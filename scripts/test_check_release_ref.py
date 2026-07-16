#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression contract for clean committed-snapshot release validation."""

from __future__ import annotations

import subprocess
import tempfile
from pathlib import Path

import check_release_ref


TIMEOUT_SECONDS = 1


def git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def commit_path(root: Path, path: str, message: str) -> str:
    git(root, "add", "--", path)
    git(root, "commit", "-qm", message)
    return git(root, "rev-parse", "HEAD")


def gate_source(*, exit_code: int, summary: str) -> str:
    return (
        "#!/usr/bin/env python3\n"
        f"print({summary!r})\n"
        f"raise SystemExit({exit_code})\n"
    )


def root_closure_source(*, exit_code: int) -> str:
    return (
        "#!/usr/bin/env python3\n"
        "print('test_root_import_closure: synthetic root census')\n"
        f"raise SystemExit({exit_code})\n"
    )


def main() -> int:
    original_root = check_release_ref.ROOT
    try:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            git(root, "init", "-q")
            git(root, "config", "user.email", "release-ref-test@example.invalid")
            git(root, "config", "user.name", "Clean ref release test")
            (root / "scripts").mkdir()
            (root / "caller.txt").write_text("committed\n", encoding="utf-8")
            (root / "scripts" / "check_release.py").write_text(
                gate_source(
                    exit_code=0,
                    summary="check_release: all 17 checks passed for release v-test",
                ),
                encoding="utf-8",
            )
            (root / "scripts" / "test_root_import_closure.py").write_text(
                root_closure_source(exit_code=0),
                encoding="utf-8",
            )
            git(root, "add", ".")
            git(root, "commit", "-qm", "passing release snapshot")
            passing_commit = git(root, "rev-parse", "HEAD")

            (root / "caller.txt").write_text(
                "uncommitted caller edit\n", encoding="utf-8"
            )
            (root / "untracked.txt").write_text(
                "uncommitted caller file\n", encoding="utf-8"
            )
            check_release_ref.ROOT = root

            probe, probe_exit = check_release_ref.validate_ref(
                passing_commit,
                timeout_seconds=30,
                probe_only=True,
            )
            assert probe_exit == 0
            assert probe["status"] == "clean_snapshot_prepared"
            assert probe["resolved_commit"] == passing_commit
            assert set(probe["caller_worktree_dirty_paths"]) == {
                "caller.txt",
                "untracked.txt",
            }
            assert not probe["caller_worktree_dirty_paths_truncated"]

            many_dirty_paths = [
                f"untracked-{index:03d}.txt"
                for index in range(check_release_ref.DIRTY_PATH_LIMIT + 5)
            ]
            bounded_receipt = check_release_ref.receipt_base(
                "HEAD",
                passing_commit,
                many_dirty_paths,
            )
            assert bounded_receipt["caller_worktree_dirty_path_count"] == len(
                many_dirty_paths
            )
            assert len(bounded_receipt["caller_worktree_dirty_paths"]) == (
                check_release_ref.DIRTY_PATH_LIMIT
            )
            assert bounded_receipt["caller_worktree_dirty_paths_truncated"]

            passed, passed_exit = check_release_ref.validate_ref(
                passing_commit,
                timeout_seconds=30,
                probe_only=False,
            )
            assert passed_exit == 0
            assert passed["status"] == "passed"
            assert passed["reported_check_count"] == 17
            assert passed["reported_release"] == "v-test"
            assert "uncommitted caller edit" not in passed["stdout_tail"]
            assert passed["release_commands"] == [
                ["python3", "scripts/check_release.py"],
                ["python3", "scripts/test_root_import_closure.py"],
            ]
            assert [row["exit_code"] for row in passed["gate_results"]] == [0, 0]

            (root / "scripts" / "test_root_import_closure.py").write_text(
                root_closure_source(exit_code=9),
                encoding="utf-8",
            )
            root_failure_commit = commit_path(
                root,
                "scripts/test_root_import_closure.py",
                "failing root closure snapshot",
            )
            root_failed, root_failed_exit = check_release_ref.validate_ref(
                root_failure_commit,
                timeout_seconds=30,
                probe_only=False,
            )
            assert root_failed_exit == 9
            assert root_failed["status"] == "failed"
            assert [row["exit_code"] for row in root_failed["gate_results"]] == [0, 9]
            assert "synthetic root census" in root_failed["stdout_tail"]

            (root / "scripts" / "test_root_import_closure.py").write_text(
                root_closure_source(exit_code=0),
                encoding="utf-8",
            )
            commit_path(
                root,
                "scripts/test_root_import_closure.py",
                "restore passing root closure",
            )

            (root / "scripts" / "check_release.py").write_text(
                gate_source(
                    exit_code=7,
                    summary="check_release: 2 failure(s) across 17 checks",
                ),
                encoding="utf-8",
            )
            failing_commit = commit_path(
                root,
                "scripts/check_release.py",
                "failing release snapshot",
            )

            old_again, old_again_exit = check_release_ref.validate_ref(
                passing_commit,
                timeout_seconds=30,
                probe_only=False,
            )
            assert old_again_exit == 0
            assert old_again["resolved_commit"] == passing_commit
            assert old_again["status"] == "passed"

            failed, failed_exit = check_release_ref.validate_ref(
                failing_commit,
                timeout_seconds=30,
                probe_only=False,
            )
            assert failed_exit == 7
            assert failed["status"] == "failed"
            assert failed["resolved_commit"] == failing_commit
            assert failed["reported_check_count"] == 17
            assert failed["reported_release"] is None

            (root / "scripts" / "check_release.py").write_text(
                "import time\n"
                "print('release gate started', flush=True)\n"
                f"time.sleep({TIMEOUT_SECONDS + 2})\n",
                encoding="utf-8",
            )
            timeout_commit = commit_path(
                root,
                "scripts/check_release.py",
                "timed-out release snapshot",
            )
            timed_out, timeout_exit = check_release_ref.validate_ref(
                timeout_commit,
                timeout_seconds=TIMEOUT_SECONDS,
                probe_only=False,
            )
            assert timeout_exit == 124
            assert timed_out["status"] == "timeout"
            assert timed_out["resolved_commit"] == timeout_commit
            assert timed_out["timeout_seconds"] == TIMEOUT_SECONDS
            assert timed_out["timed_out_command"] == [
                "python3",
                "scripts/check_release.py",
            ]
            assert "release gate started" in timed_out["stdout_tail"]

            try:
                check_release_ref.resolve_commit("missing-ref")
            except check_release_ref.SnapshotError:
                pass
            else:
                raise AssertionError("missing ref was accepted")
    finally:
        check_release_ref.ROOT = original_root

    print(
        "test_check_release_ref: caller dirt excluded, exact commits selected, "
        "dirty paths bounded, root disk census enforced, failing gate exit "
        "preserved, and timeout receipt serialized"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
