#!/usr/bin/env python3
"""Build stale local Lean modules with bounded memory, then verify with Lake."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import os
from pathlib import Path
import re
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_'.]+)\s*(?:--.*)?$")


def module_name(source: Path) -> str:
    return ".".join(source.relative_to(ROOT).with_suffix("").parts)


def discover() -> dict[str, Path]:
    return {
        module_name(source): source
        for source in ROOT.rglob("*.lean")
        if not any(part.startswith(".") for part in source.relative_to(ROOT).parts)
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


def reachable(root: str, graph: dict[str, set[str]]) -> set[str]:
    result: set[str] = set()
    stack = [root]
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


def olean(name: str) -> Path:
    return ROOT / ".lake" / "build" / "lib" / "lean" / Path(*name.split(".")).with_suffix(".olean")


def stale(name: str, modules: dict[str, Path], graph: dict[str, set[str]]) -> bool:
    output = olean(name)
    if not output.is_file():
        return True
    timestamp = output.stat().st_mtime_ns
    if modules[name].stat().st_mtime_ns > timestamp:
        return True
    return any(not olean(dep).is_file() or olean(dep).stat().st_mtime_ns > timestamp for dep in graph[name])


def build_one(name: str) -> tuple[str, int, float]:
    started = time.monotonic()
    result = subprocess.run(["lake", "build", f"+{name}"], cwd=ROOT, check=False)
    return name, result.returncode, time.monotonic() - started


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=int(os.environ.get("LEAN_BUILD_JOBS", "2")))
    parser.add_argument("--plan", action="store_true")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be at least 1")

    modules = discover()
    graph = local_graph(modules)
    build_waves = waves(reachable("Erdos249257", graph), graph)
    pending = [[name for name in wave if stale(name, modules, graph)] for wave in build_waves]
    pending = [wave for wave in pending if wave]
    print(f"lean-fast-build: {sum(map(len, pending))} stale/missing module(s), jobs={args.jobs}")
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
    return subprocess.run(["lake", "build"], cwd=ROOT, check=False).returncode


if __name__ == "__main__":
    sys.exit(main())
