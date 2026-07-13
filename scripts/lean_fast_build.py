#!/usr/bin/env python3
"""Build stale local Lean modules with bounded memory, then verify with Lake.

The optional targets may be module names or ``.lean`` paths.  With no targets,
the public root module is built.  Focused targets keep the edit/test loop from
paying for every public certificate module while preserving an ordinary Lake
build as the final authority check.  ``--changed-from`` derives those focused
targets from Git, including untracked Lean files.
"""

from __future__ import annotations

import argparse
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
    modules: dict[str, Path] = {}
    for directory, dirnames, filenames in os.walk(root):
        # Prune .lake and other hidden trees before traversal; filtering after
        # Path.rglob still pays to enumerate the complete dependency cache.
        dirnames[:] = [name for name in dirnames if not name.startswith(".")]
        directory_path = Path(directory)
        module_prefix = directory_path.relative_to(root).parts
        for filename in filenames:
            if not filename.endswith(".lean") or filename.startswith("_"):
                continue
            source = directory_path / filename
            module = ".".join((*module_prefix, filename[:-5]))
            modules[module] = source
    return modules


def code_without_comments(line: str, block_depth: int) -> tuple[str, int]:
    """Remove nested Lean comments from one header line."""

    code: list[str] = []
    index = 0
    while index < len(line):
        if block_depth:
            if line.startswith("/-", index):
                block_depth += 1
                index += 2
            elif line.startswith("-/", index):
                block_depth -= 1
                index += 2
            else:
                index += 1
        elif line.startswith("--", index):
            break
        elif line.startswith("/-", index):
            block_depth = 1
            index += 2
        else:
            code.append(line[index])
            index += 1
    return "".join(code), block_depth


def local_imports(source: Path, modules: dict[str, Path]) -> set[str]:
    """Read only the Lean header, where import commands are legal."""

    imports: set[str] = set()
    block_depth = 0
    with source.open(encoding="utf-8") as lines:
        for raw_line in lines:
            code, block_depth = code_without_comments(raw_line, block_depth)
            stripped = code.strip()
            if not stripped or stripped == "prelude":
                continue
            match = IMPORT_RE.match(stripped)
            if match:
                if match.group(1) in modules:
                    imports.add(match.group(1))
                continue
            break
    return imports


def local_graph(modules: dict[str, Path]) -> dict[str, set[str]]:
    return {name: local_imports(source, modules) for name, source in modules.items()}


def reachable_graph(
    roots: Iterable[str], modules: dict[str, Path]
) -> dict[str, set[str]]:
    """Parse only the local import cone reachable from ``roots``."""

    graph: dict[str, set[str]] = {}
    pending = list(roots)
    while pending:
        module = pending.pop()
        if module in graph:
            continue
        imports = local_imports(modules[module], modules)
        graph[module] = imports
        pending.extend(imports - graph.keys())
    return graph


def resolve_targets(
    targets: Iterable[str], modules: dict[str, Path], root: Path = ROOT
) -> list[str]:
    requested = list(targets) or ["Erdos249257"]
    resolved: list[str] = []
    for target in requested:
        candidate = target.removeprefix("+")
        if candidate in modules:
            resolved.append(candidate)
            continue
        target_path = (root / candidate).resolve()
        if target_path.suffix == ".lean":
            try:
                path_module = module_name(target_path, root.resolve())
            except ValueError:
                path_module = None
            if path_module in modules and modules[path_module].resolve() == target_path:
                resolved.append(path_module)
                continue
        raise ValueError(f"unknown local Lean target: {target}")
    return resolved


def changed_lean_paths(base: str, root: Path = ROOT) -> set[Path]:
    """Return tracked or untracked Lean paths changed relative to ``base``."""

    commands = (
        ["git", "diff", "--name-only", "--diff-filter=ACMR", base, "--", "*.lean"],
        ["git", "ls-files", "--others", "--exclude-standard", "--", "*.lean"],
    )
    changed_paths: set[Path] = set()
    for command in commands:
        completed = subprocess.run(
            command,
            cwd=root,
            capture_output=True,
            text=True,
            check=False,
        )
        if completed.returncode:
            detail = completed.stderr.strip() or f"exit {completed.returncode}"
            raise RuntimeError(f"cannot resolve changed Lean targets: {detail}")
        changed_paths.update(
            (root / line).resolve()
            for line in completed.stdout.splitlines()
            if line.strip()
        )
    return changed_paths


def changed_targets_from_paths(
    changed_paths: Iterable[Path], modules: dict[str, Path], root: Path = ROOT
) -> list[str]:
    resolved_root = root.resolve()
    changed: set[str] = set()
    for path in changed_paths:
        resolved_path = path.resolve()
        try:
            name = module_name(resolved_path, resolved_root)
        except ValueError:
            continue
        if name in modules and modules[name].resolve() == resolved_path:
            changed.add(name)
    return sorted(changed)


def changed_targets(
    base: str, modules: dict[str, Path], root: Path = ROOT
) -> list[str]:
    """Return changed local Lean modules relative to ``base``."""

    return changed_targets_from_paths(changed_lean_paths(base, root), modules, root)


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


def file_mtime_ns(path: Path) -> int | None:
    try:
        return path.stat().st_mtime_ns
    except FileNotFoundError:
        return None


def project_config_mtime_ns(root: Path = ROOT) -> int | None:
    mtimes = [
        mtime
        for name in ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain")
        if (mtime := file_mtime_ns(root / name)) is not None
    ]
    return max(mtimes, default=None)


def olean_mtime_ns(
    name: str,
    root: Path = ROOT,
    cache: dict[str, int | None] | None = None,
) -> int | None:
    if cache is not None and name in cache:
        return cache[name]
    mtime = file_mtime_ns(olean(name, root))
    if cache is not None:
        cache[name] = mtime
    return mtime


def stale(
    name: str,
    modules: dict[str, Path],
    graph: dict[str, set[str]],
    root: Path = ROOT,
    *,
    cached_olean_mtimes: dict[str, int | None] | None = None,
    cached_config_mtime_ns: int | None = None,
) -> bool:
    timestamp = olean_mtime_ns(name, root, cached_olean_mtimes)
    if timestamp is None:
        return True
    if modules[name].stat().st_mtime_ns > timestamp:
        return True
    for dependency in graph[name]:
        dependency_timestamp = olean_mtime_ns(
            dependency, root, cached_olean_mtimes
        )
        if dependency_timestamp is None or dependency_timestamp > timestamp:
            return True
    config_timestamp = (
        cached_config_mtime_ns
        if cached_olean_mtimes is not None
        else project_config_mtime_ns(root)
    )
    return config_timestamp is not None and config_timestamp > timestamp


def build_one(name: str, root: Path = ROOT) -> tuple[str, int, float]:
    started = time.monotonic()
    result = subprocess.run(["lake", "build", f"+{name}"], cwd=root, check=False)
    return name, result.returncode, time.monotonic() - started


def build_batch(
    names: Iterable[str],
    root: Path = ROOT,
) -> tuple[list[str], int, float]:
    """Build one bounded target batch through a single Lake invocation."""

    batch = list(names)
    started = time.monotonic()
    result = subprocess.run(
        ["lake", "build", *(f"+{name}" for name in batch)],
        cwd=root,
        check=False,
    )
    return batch, result.returncode, time.monotonic() - started


def build_wave(names: Iterable[str], jobs: int, root: Path = ROOT) -> list[str]:
    """Build one wave in bounded Lake batches, isolating failures individually."""

    modules = list(names)
    failed: list[str] = []
    for start in range(0, len(modules), jobs):
        batch = modules[start : start + jobs]
        built, code, duration = build_batch(batch, root)
        print(
            f"lean-fast-build: {','.join(built)} -> {code} "
            f"({duration:.1f}s, batch={len(built)})"
        )
        if not code:
            continue
        print("lean-fast-build: batch failed; isolating targets")
        for name in batch:
            isolated_name, isolated_code, isolated_duration = build_one(name, root)
            print(
                f"lean-fast-build: {isolated_name} -> {isolated_code} "
                f"({isolated_duration:.1f}s, isolated)"
            )
            if isolated_code:
                failed.append(isolated_name)
    return failed


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="*", help="local module name or .lean path; defaults to Erdos249257")
    parser.add_argument(
        "--changed-from",
        nargs="?",
        const="HEAD",
        metavar="REF",
        help="build changed Lean modules relative to REF (default: HEAD), plus untracked Lean files",
    )
    parser.add_argument("--jobs", type=int, default=default_jobs())
    parser.add_argument("--plan", action="store_true")
    args = parser.parse_args(argv)
    if args.jobs < 1:
        parser.error("--jobs must be at least 1")

    root = ROOT
    try:
        if args.changed_from is not None:
            if args.targets:
                parser.error("positional targets and --changed-from are mutually exclusive")
            changed_paths = changed_lean_paths(args.changed_from, root)
            if not changed_paths:
                print(f"lean-fast-build: no changed Lean modules relative to {args.changed_from}")
                return 0
            modules = discover(root)
            target_modules = changed_targets_from_paths(changed_paths, modules, root)
            if not target_modules:
                print(f"lean-fast-build: no changed local Lean modules relative to {args.changed_from}")
                return 0
        else:
            modules = discover(root)
            target_modules = resolve_targets(args.targets, modules, root)
    except (RuntimeError, ValueError) as error:
        parser.error(str(error))
    graph = reachable_graph(target_modules, modules)
    build_waves = waves(reachable(target_modules, graph), graph)
    output_mtimes: dict[str, int | None] = {}
    config_mtime = project_config_mtime_ns(root)
    pending = [
        [
            name
            for name in wave
            if stale(
                name,
                modules,
                graph,
                root,
                cached_olean_mtimes=output_mtimes,
                cached_config_mtime_ns=config_mtime,
            )
        ]
        for wave in build_waves
    ]
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
        current = [name for name in wave if stale(name, modules, graph, root)]
        failed = build_wave(current, args.jobs, root)
        if failed:
            raise RuntimeError("module prebuild failed: " + ", ".join(sorted(failed)))

    print("lean-fast-build: final Lake authority check")
    focused = bool(args.targets) or args.changed_from is not None
    final_targets = [f"+{name}" for name in target_modules] if focused else []
    return subprocess.run(["lake", "build", *final_targets], cwd=root, check=False).returncode


if __name__ == "__main__":
    sys.exit(main())
