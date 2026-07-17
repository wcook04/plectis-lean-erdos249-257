#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial fixtures for the newcomer architecture guide."""

from __future__ import annotations

import check_architecture_guide as checker


def assert_rejected(text: str, label: str) -> None:
    try:
        checker.validate_guide(text)
    except AssertionError:
        return
    raise AssertionError(f"architecture-guide mutation escaped: {label}")


def main() -> int:
    guide = checker.GUIDE.read_text(encoding="utf-8")
    readme = checker.README.read_text(encoding="utf-8")
    agents = checker.AGENTS.read_text(encoding="utf-8")

    checker.validate_guide(guide)
    checker.validate_entry_links(readme, agents)
    checks = 2

    mutations = (
        (
            guide.replace("Both mathematical problems remain open", ""),
            "open-problem boundary removed",
        ),
        (
            guide.replace("Lean decides whether a formal proof", "Software decides"),
            "formal-check decision blurred",
        ),
        (
            guide.replace("A mathematician decides whether the public wording", ""),
            "human semantic review removed",
        ),
        (
            guide.replace("does not prove that every important sentence was selected", ""),
            "coverage ceiling removed",
        ),
        (
            guide.replace("## A complete example", "## Internal record"),
            "worked-example section removed",
        ),
        (guide + "\nM8 achieved 9/10.\n", "evaluation shorthand introduced"),
    )
    for mutated, label in mutations:
        assert_rejected(mutated, label)
        checks += 1

    try:
        checker.validate_entry_links(
            readme.replace(
                "[architecture and repository guide](ARCHITECTURE.md)",
                "architecture notes",
            ),
            agents,
        )
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("README architecture entry-link deletion escaped")

    print(f"architecture guide tests: {checks} checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
