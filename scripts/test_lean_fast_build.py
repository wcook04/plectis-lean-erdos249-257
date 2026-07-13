#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression tests for the public bounded Lean build planner."""

from __future__ import annotations

import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import lean_fast_build as fast


class LeanFastBuildTests(unittest.TestCase):
    def test_automatic_worker_default_is_memory_bounded(self) -> None:
        with mock.patch.dict(os.environ, {}, clear=True), mock.patch.object(
            fast.os, "cpu_count", return_value=64
        ):
            self.assertEqual(fast.default_jobs(), 2)

    def test_reachable_and_waves_limit_focused_target(self) -> None:
        graph = {
            "Root": {"Left", "Right"},
            "Left": {"Shared"},
            "Right": set(),
            "Shared": set(),
        }
        selected = fast.reachable(["Left"], graph)
        self.assertEqual(selected, {"Left", "Shared"})
        self.assertEqual(fast.waves(selected, graph), [["Shared"], ["Left"]])

    def test_discovery_ignores_ephemeral_underscore_modules(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Pkg" / "Leaf.lean"
            source.parent.mkdir()
            source.write_text("-- source\n", encoding="utf-8")
            (root / "_axcheck.lean").write_text("#check True\n", encoding="utf-8")

            self.assertEqual(set(fast.discover(root)), {"Pkg.Leaf"})

    def test_resolve_targets_accepts_module_and_path(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Pkg" / "Leaf.lean"
            source.parent.mkdir()
            source.write_text("-- test\n", encoding="utf-8")
            modules = {"Pkg.Leaf": source}
            self.assertEqual(fast.resolve_targets(["Pkg.Leaf"], modules, root), ["Pkg.Leaf"])
            self.assertEqual(fast.resolve_targets(["Pkg/Leaf.lean"], modules, root), ["Pkg.Leaf"])
            with self.assertRaisesRegex(ValueError, "unknown local Lean target"):
                fast.resolve_targets(["Pkg.Missing"], modules, root)

    def test_changed_targets_combines_tracked_and_untracked_modules(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tracked = root / "Pkg" / "Tracked.lean"
            untracked = root / "Pkg" / "Untracked.lean"
            tracked.parent.mkdir()
            tracked.write_text("-- tracked\n", encoding="utf-8")
            untracked.write_text("-- untracked\n", encoding="utf-8")
            modules = {"Pkg.Tracked": tracked, "Pkg.Untracked": untracked}
            results = [
                fast.subprocess.CompletedProcess([], 0, "Pkg/Tracked.lean\nREADME.md\n", ""),
                fast.subprocess.CompletedProcess([], 0, "Pkg/Untracked.lean\n", ""),
            ]
            with mock.patch.object(fast.subprocess, "run", side_effect=results) as run:
                self.assertEqual(
                    fast.changed_targets("HEAD~1", modules, root),
                    ["Pkg.Tracked", "Pkg.Untracked"],
                )
            self.assertEqual(run.call_count, 2)
            self.assertIn("HEAD~1", run.call_args_list[0].args[0])

    def test_changed_targets_reports_git_failure(self) -> None:
        failed = fast.subprocess.CompletedProcess([], 128, "", "bad revision")
        with mock.patch.object(fast.subprocess, "run", return_value=failed):
            with self.assertRaisesRegex(RuntimeError, "bad revision"):
                fast.changed_targets("missing", {})

    def test_config_change_makes_module_stale(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Pkg" / "Leaf.lean"
            output = root / ".lake" / "build" / "lib" / "lean" / "Pkg" / "Leaf.olean"
            source.parent.mkdir()
            output.parent.mkdir(parents=True)
            source.write_text("-- source\n", encoding="utf-8")
            output.write_text("olean\n", encoding="utf-8")
            os.utime(source, ns=(1_000_000_000, 1_000_000_000))
            os.utime(output, ns=(2_000_000_000, 2_000_000_000))
            modules = {"Pkg.Leaf": source}
            graph = {"Pkg.Leaf": set()}
            self.assertFalse(fast.stale("Pkg.Leaf", modules, graph, root))

            config = root / "lean-toolchain"
            config.write_text("leanprover/lean4:test\n", encoding="utf-8")
            os.utime(config, ns=(3_000_000_000, 3_000_000_000))
            self.assertTrue(fast.stale("Pkg.Leaf", modules, graph, root))

    def test_cycle_is_rejected(self) -> None:
        graph = {"A": {"B"}, "B": {"A"}}
        with self.assertRaisesRegex(RuntimeError, "cycle"):
            fast.waves({"A", "B"}, graph)

    def test_focused_main_uses_focused_final_lake_authority(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Pkg" / "Leaf.lean"
            output = root / ".lake" / "build" / "lib" / "lean" / "Pkg" / "Leaf.olean"
            source.parent.mkdir()
            output.parent.mkdir(parents=True)
            source.write_text("-- source\n", encoding="utf-8")
            output.write_text("olean\n", encoding="utf-8")
            os.utime(source, ns=(1_000_000_000, 1_000_000_000))
            os.utime(output, ns=(2_000_000_000, 2_000_000_000))
            completed = fast.subprocess.CompletedProcess([], 0, "", "")
            with mock.patch.object(fast, "ROOT", root), mock.patch.object(
                fast.subprocess, "run", return_value=completed
            ) as run:
                self.assertEqual(fast.main(["Pkg/Leaf.lean"]), 0)

            self.assertEqual(run.call_count, 1)
            self.assertEqual(run.call_args.args[0], ["lake", "build", "+Pkg.Leaf"])
            self.assertEqual(run.call_args.kwargs["cwd"], root)


if __name__ == "__main__":
    unittest.main()
