#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Run the release gate against a clean committed Git snapshot.

This wrapper is for shared or intentionally dirty worktrees.  It resolves one
commit, creates a disposable local clone, and runs scripts/check_release.py
there.  Uncommitted files in the caller's checkout are never copied into the
validation snapshot.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
SCHEMA = "erdos249257-clean-ref-release-receipt/1"
TAIL_BYTES = 16_000
DIRTY_PATH_LIMIT = 120


class SnapshotError(RuntimeError):
    """Raised when the requested clean snapshot cannot be prepared."""


def run(
    argv: list[str],
    *,
    cwd: Path,
    timeout: int | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        argv,
        cwd=cwd,
        capture_output=True,
        text=True,
        check=False,
        timeout=timeout,
    )


def resolve_commit(ref: str) -> str:
    completed = run(["git", "rev-parse", "--verify", f"{ref}^{{commit}}"], cwd=ROOT)
    if completed.returncode != 0:
        raise SnapshotError(
            completed.stderr.strip() or f"could not resolve commit ref {ref!r}"
        )
    commit = completed.stdout.strip()
    if re.fullmatch(r"[0-9a-f]{40}", commit) is None:
        raise SnapshotError(f"resolved ref is not a full commit id: {commit!r}")
    return commit


def dirty_paths() -> list[str]:
    completed = run(
        ["git", "status", "--short", "--untracked-files=all"],
        cwd=ROOT,
    )
    if completed.returncode != 0:
        return []
    return [line[3:] for line in completed.stdout.splitlines() if line]


def bounded_tail(text: str | bytes) -> str:
    encoded = (
        text
        if isinstance(text, bytes)
        else text.encode("utf-8", errors="replace")
    )
    return encoded[-TAIL_BYTES:].decode("utf-8", errors="replace")


def parse_release_summary(stdout: str) -> dict[str, Any]:
    match = re.search(
        r"all ([0-9,]+) checks passed for release ([^\s]+)",
        stdout,
    )
    if match:
        return {
            "reported_check_count": int(match.group(1).replace(",", "")),
            "reported_release": match.group(2),
        }
    failed = re.search(r"([0-9,]+) checks", stdout)
    return {
        "reported_check_count": (
            int(failed.group(1).replace(",", "")) if failed else None
        ),
        "reported_release": None,
    }


def prepare_clone(commit: str, parent: Path) -> Path:
    clone = parent / "repo"
    cloned = run(
        [
            "git",
            "clone",
            "--local",
            "--no-hardlinks",
            "--no-checkout",
            "--quiet",
            str(ROOT),
            str(clone),
        ],
        cwd=ROOT,
    )
    if cloned.returncode != 0:
        raise SnapshotError(cloned.stderr.strip() or "local clone failed")
    checked_out = run(
        ["git", "checkout", "--detach", "--quiet", commit],
        cwd=clone,
    )
    if checked_out.returncode != 0:
        raise SnapshotError(
            checked_out.stderr.strip() or f"could not check out {commit}"
        )
    if not (clone / "scripts" / "check_release.py").is_file():
        raise SnapshotError("snapshot does not contain scripts/check_release.py")
    return clone


def receipt_base(ref: str, commit: str, caller_dirty_paths: list[str]) -> dict[str, Any]:
    dirty_path_count = len(caller_dirty_paths)
    return {
        "schema": SCHEMA,
        "requested_ref": ref,
        "resolved_commit": commit,
        "snapshot_posture": "clean_committed_clone_excludes_caller_worktree_changes",
        "source_repository": str(ROOT),
        "caller_worktree_dirty_path_count": dirty_path_count,
        "caller_worktree_dirty_paths": caller_dirty_paths[:DIRTY_PATH_LIMIT],
        "caller_worktree_dirty_path_limit": DIRTY_PATH_LIMIT,
        "caller_worktree_dirty_paths_truncated": dirty_path_count > DIRTY_PATH_LIMIT,
        "release_command": ["python3", "scripts/check_release.py"],
    }


def validate_ref(
    ref: str,
    *,
    timeout_seconds: int,
    probe_only: bool,
) -> tuple[dict[str, Any], int]:
    commit = resolve_commit(ref)
    caller_dirty_paths = dirty_paths()
    started_at = datetime.now(timezone.utc).isoformat()
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="plectis-clean-release-") as temp:
        clone = prepare_clone(commit, Path(temp))
        checked_out = run(["git", "rev-parse", "HEAD"], cwd=clone)
        if checked_out.stdout.strip() != commit:
            raise SnapshotError("disposable clone resolved a different commit")
        if probe_only:
            elapsed = round(time.monotonic() - started, 3)
            return (
                {
                    **receipt_base(ref, commit, caller_dirty_paths),
                    "mode": "probe_only",
                    "status": "clean_snapshot_prepared",
                    "started_at": started_at,
                    "completed_at": datetime.now(timezone.utc).isoformat(),
                    "wall_time_seconds": elapsed,
                    "gate_exit_code": None,
                },
                0,
            )
        try:
            completed = run(
                ["python3", "scripts/check_release.py"],
                cwd=clone,
                timeout=timeout_seconds,
            )
            elapsed = round(time.monotonic() - started, 3)
            summary = parse_release_summary(completed.stdout)
            return (
                {
                    **receipt_base(ref, commit, caller_dirty_paths),
                    "mode": "release_gate",
                    "status": (
                        "passed" if completed.returncode == 0 else "failed"
                    ),
                    "started_at": started_at,
                    "completed_at": datetime.now(timezone.utc).isoformat(),
                    "wall_time_seconds": elapsed,
                    "gate_exit_code": completed.returncode,
                    **summary,
                    "stdout_tail": bounded_tail(completed.stdout),
                    "stderr_tail": bounded_tail(completed.stderr),
                },
                completed.returncode,
            )
        except subprocess.TimeoutExpired as error:
            elapsed = round(time.monotonic() - started, 3)
            return (
                {
                    **receipt_base(ref, commit, caller_dirty_paths),
                    "mode": "release_gate",
                    "status": "timeout",
                    "started_at": started_at,
                    "completed_at": datetime.now(timezone.utc).isoformat(),
                    "wall_time_seconds": elapsed,
                    "gate_exit_code": None,
                    "timeout_seconds": timeout_seconds,
                    "reported_check_count": None,
                    "reported_release": None,
                    "stdout_tail": bounded_tail(error.stdout or ""),
                    "stderr_tail": bounded_tail(error.stderr or ""),
                },
                124,
            )


def write_receipt(path: Path, receipt: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(receipt, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def render_text(receipt: dict[str, Any]) -> str:
    header = (
        f"check_release_ref: {receipt['status']} "
        f"ref={receipt['requested_ref']} "
        f"commit={receipt['resolved_commit'][:12]} "
        f"caller_dirty_paths={receipt['caller_worktree_dirty_path_count']}"
    )
    if receipt["mode"] == "probe_only":
        return header
    body = receipt.get("stdout_tail", "").rstrip()
    error = receipt.get("stderr_tail", "").rstrip()
    return "\n".join(part for part in (header, body, error) if part)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ref", default="HEAD")
    parser.add_argument("--timeout-seconds", type=int, default=900)
    parser.add_argument("--probe-only", action="store_true")
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args()
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")
    try:
        receipt, exit_code = validate_ref(
            args.ref,
            timeout_seconds=args.timeout_seconds,
            probe_only=args.probe_only,
        )
    except (SnapshotError, OSError, subprocess.SubprocessError) as error:
        print(f"check_release_ref: {error}")
        return 2
    if args.receipt is not None:
        write_receipt(args.receipt, receipt)
    if args.format == "json":
        print(json.dumps(receipt, ensure_ascii=False, indent=2))
    else:
        print(render_text(receipt))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
