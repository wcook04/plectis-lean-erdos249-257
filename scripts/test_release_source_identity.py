#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression test for immutable-ref source resolution in the release gate."""

from __future__ import annotations

import subprocess
import tempfile
from pathlib import Path

import check_release


def git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def commit(root: Path, message: str) -> str:
    git(root, "add", ".")
    git(root, "commit", "-qm", message)
    return git(root, "rev-parse", "HEAD")


def main() -> int:
    """A later worktree file must not satisfy a historical source reference."""
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        git(root, "init", "-q")
        git(root, "config", "user.email", "release-test@example.invalid")
        git(root, "config", "user.name", "Release source identity test")
        (root / "Erdos249257").mkdir()
        (root / "Erdos249257" / "Stable.lean").write_text(
            "theorem stable : True := True.intro\n", encoding="utf-8"
        )
        old_ref = commit(root, "old formal source")
        (root / "Erdos249257" / "PostRef.lean").write_text(
            "theorem postRefOnly : True := True.intro\n", encoding="utf-8"
        )
        new_ref = commit(root, "new worktree source")

        original_root = check_release.ROOT
        check_release.ROOT = root
        try:
            cache: dict[tuple[str, str | None], list[str] | None] = {}
            assert check_release.module_lines(cache, "Erdos249257/PostRef.lean", old_ref) is None
            new_lines = check_release.module_lines(cache, "Erdos249257/PostRef.lean", new_ref)
            assert new_lines is not None
            assert check_release.name_at_line(new_lines, "postRefOnly", 1)
            matches_old, old_detail = check_release.formal_source_matches_current_lean_tree(old_ref)
            assert not matches_old
            assert "differ from formal-source checkpoint" in old_detail
            matches_new, new_detail = check_release.formal_source_matches_current_lean_tree(new_ref)
            assert matches_new
            assert new_detail == ""
            (root / "Erdos249257" / "Untracked.lean").write_text(
                "theorem untracked : True := True.intro\n", encoding="utf-8"
            )
            matches_with_untracked, untracked_detail = (
                check_release.formal_source_matches_current_lean_tree(new_ref)
            )
            assert not matches_with_untracked
            assert "Untracked.lean" in untracked_detail
        finally:
            check_release.ROOT = original_root

    print("test_release_source_identity: pinned source cannot masquerade as a later Lean tree")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
