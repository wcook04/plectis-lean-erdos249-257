#!/usr/bin/env python3
"""Build stale local Lean modules with bounded memory, then verify with Lake.

The optional targets may be module names or ``.lean`` paths.  With no targets,
the public root module is built.  Focused targets keep the edit/test loop from
paying for every public certificate module while preserving an ordinary Lake
build as the final authority check.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_'.]+)\s*(?:--.*)?$")


def default_jobs() -> int:
    configured = os.environ.get("LEAN_BUILD_JOBS")
    if configured:
        try:
            return max(1, int(configured))
        except ValueError:
            pass
    cpu_count = max(1, os.cpu_count() or 1)
    interactive_reserve = max(1, cpu_count // 4)
    return min(2, max(1, (cpu_count - interactive_reserve) // 2))


def module_name(source: Path, root: Path = ROOT) -> str:
    return ".".join(source.relative_to(root).with_suffix("").parts)


def discover(root: Path = ROOT) -> dict[str, Path]:
    return {
        module_name(source, root): source
        for source in root.rglob("*.lean")
        if not any(part.startswith(".") for part in source.relative_to(root).parts)
    }


def local_graph(modules: dict[str, Path]) -> dict[str, set[str]]:
    graph: dict[str, set[str]] = {}
    for name, source in modules.items():
        graph[name] = {
            match.group(1)
            for line in source.read_text(encoding="utf-8").splitlines()
            if (match := IMPORT_RE.match(line)) and match.group(1) in modules
        }
    return graph


def resolve_targets(
    targets: Iterable[str], modules: dict[str, Path], root: Path = ROOT
) -> list[str]:
    requested = list(targets) or ["Erdos249257"]
    resolved: list[str] = []
    modules_by_path = {source.resolve(): name for name, source in modules.items()}
    for target in requested:
        candidate = target.removeprefix("+")
        if candidate in modules:
            resolved.append(candidate)
            continue
        target_path = (root / candidate).resolve()
        if target_path.suffix == ".lean" and target_path in modules_by_path:
            resolved.append(modules_by_path[target_path])
            continue
        raise ValueError(f"unknown local Lean target: {target}")
    return resolved


def reachable(roots: Iterable[str], graph: dict[str, set[str]]) -> set[str]:
    result: set[str] = set()
    stack = list(roots)
    while stack:
        item = stack.pop()
        if item not in result:
            result.add(item)
            stack.extend(graph[item])
    return result


def waves(selected: set[str], graph: dict[str, set[str]]) -> list[list[str]]:
    pending = set(selected)
    done: set[str] = set()
    result: list[list[str]] = []
    while pending:
        ready = sorted(name for name in pending if (graph[name] & selected) <= done)
        if not ready:
            raise RuntimeError("cycle in local Lean import graph")
        result.append(ready)
        done.update(ready)
        pending.difference_update(ready)
    return result


def olean(name: str, root: Path = ROOT) -> Path:
    return root / ".lake" / "build" / "lib" / "lean" / Path(*name.split(".")).with_suffix(".olean")


def stale(
    name: str,
    modules: dict[str, Path],
    graph: dict[str, set[str]],
    root: Path = ROOT,
) -> bool:
    output = olean(name, root)
    if not output.is_file():
        return True
    timestamp = output.stat().st_mtime_ns
    if modules[name].stat().st_mtime_ns > timestamp:
        return True
    if any(
        not olean(dep, root).is_file() or olean(dep, root).stat().st_mtime_ns > timestamp
        for dep in graph[name]
    ):
        return True
    return any(
        config.is_file() and config.stat().st_mtime_ns > timestamp
        for config in (
            root / "lakefile.toml",
            root / "lakefile.lean",
            root / "lake-manifest.json",
            root / "lean-toolchain",
        )
    )


def build_one(name: str, root: Path = ROOT) -> tuple[str, int, float]:
    started = time.monotonic()
    result = subprocess.run(["lake", "build", f"+{name}"], cwd=root, check=False)
    return name, result.returncode, time.monotonic() - started


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="*", help="local module name or .lean path; defaults to Erdos249257")
    parser.add_argument("--jobs", type=int, default=default_jobs())
    parser.add_argument("--plan", action="store_true")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be at least 1")

    modules = discover()
    graph = local_graph(modules)
    try:
        target_modules = resolve_targets(args.targets, modules)
    except ValueError as error:
        parser.error(str(error))
    build_waves = waves(reachable(target_modules, graph), graph)
    pending = [[name for name in wave if stale(name, modules, graph)] for wave in build_waves]
    pending = [wave for wave in pending if wave]
    print(
        f"lean-fast-build: targets={','.join(target_modules)}; "
        f"{sum(map(len, pending))} stale/missing module(s), jobs={args.jobs}"
    )
    if args.plan:
        for index, wave in enumerate(pending, 1):
            print(f"wave {index}: {' '.join(wave)}")
        return 0

    for wave in pending:
        current = [name for name in wave if stale(name, modules, graph)]
        with ThreadPoolExecutor(max_workers=args.jobs) as executor:
            futures = [executor.submit(build_one, name) for name in current]
            failed = []
            for future in as_completed(futures):
                name, code, duration = future.result()
                print(f"lean-fast-build: {name} -> {code} ({duration:.1f}s)")
                if code:
                    failed.append(name)
            if failed:
                raise RuntimeError("module prebuild failed: " + ", ".join(sorted(failed)))

    print("lean-fast-build: final Lake authority check")
    final_targets = [] if not args.targets else [f"+{name}" for name in target_modules]
    return subprocess.run(["lake", "build", *final_targets], cwd=ROOT, check=False).returncode


if __name__ == "__main__":
    sys.exit(main())
