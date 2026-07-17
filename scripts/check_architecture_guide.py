#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check that the newcomer architecture guide stays concrete and jargon-free."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
GUIDE = ROOT / "ARCHITECTURE.md"
README = ROOT / "README.md"
AGENTS = ROOT / "AGENTS.md"
MAX_GUIDE_BYTES = 18_000

SECTION_ORDER = (
    "## What this repository is",
    "## The architecture in one page",
    "## Which file is authoritative for what",
    "## Repository map",
    "## A complete example",
    "## What happens when a change is made",
    "## How the checks run",
    "## What the checks do not prove",
    "## Where to start",
)

REQUIRED_ANCHOR_GROUPS = {
    "purpose_and_boundary": (
        "Both mathematical problems remain open",
        "does not claim a solution to either problem",
        "self-contained public release",
    ),
    "three_decisions": (
        "Lean decides whether a formal proof",
        "A mathematician decides whether the public wording",
        "The release program decides whether the files",
    ),
    "authority_owners": (
        "Erdos249257.lean",
        "docs/claims.json",
        "docs/methodology.json",
        "scripts/check_release.py",
        ".github/workflows/lean.yml",
    ),
    "worked_example": (
        "certified_kill_instances",
        "verified finite instance",
        "beyond every fixed limit",
    ),
    "validation_split": (
        "lake build",
        "python3 scripts/check_release.py",
        "does not run Lean",
    ),
    "guarantee_ceiling": (
        "does not mean that a program understood every sentence",
        "does not prove that every important sentence was selected",
    ),
}

REQUIRED_PATHS = (
    "Erdos249257.lean",
    "docs/claims.json",
    "docs/methodology.json",
    "docs/publication_contract.json",
    "docs/publication_evidence.json",
    "docs/ORIENTATION.md",
    "docs/SOURCE_MAP.md",
    "scripts/check_release.py",
    "scripts/check_cold_clone_comprehension.py",
    ".github/workflows/lean.yml",
    "paper/erdos249-257-main-paper.tex",
)

# These labels belong to the evaluation history or to private agent doctrine.
# A first-principles repository guide has no reason to make a cold reader decode
# them. The full words Type A and Type B are included because they are private
# role labels in the parent workflow, not part of this public Lean project.
BANNED_SHORTHAND = (
    re.compile(r"\bM(?:10|[1-9])\b"),
    re.compile(r"\b9/10\b"),
    re.compile(r"\b5,207\b"),
    re.compile(r"\bMRS\b"),
    re.compile(r"\bquantifier\b", re.IGNORECASE),
    re.compile(r"\bType A\b", re.IGNORECASE),
    re.compile(r"\bType B\b", re.IGNORECASE),
    re.compile(r"\bAccess Skeleton\b", re.IGNORECASE),
    re.compile(r"\bVinum\b", re.IGNORECASE),
)


def normalise(text: str) -> str:
    return " ".join(text.split())


def validate_guide(text: str) -> None:
    size = len(text.encode("utf-8"))
    assert size <= MAX_GUIDE_BYTES, (
        f"ARCHITECTURE.md is {size} bytes (budget {MAX_GUIDE_BYTES})"
    )

    positions = [text.find(heading) for heading in SECTION_ORDER]
    assert all(position >= 0 for position in positions), (
        f"architecture guide lost section sequence {SECTION_ORDER}"
    )
    assert positions == sorted(positions), "architecture guide sections are out of order"

    compact = normalise(text)
    for group_id, anchors in REQUIRED_ANCHOR_GROUPS.items():
        for anchor in anchors:
            assert normalise(anchor).casefold() in compact.casefold(), (
                f"architecture guide lost {group_id} anchor {anchor!r}"
            )

    for pattern in BANNED_SHORTHAND:
        assert not pattern.search(text), (
            f"architecture guide exposes private or evaluation shorthand {pattern.pattern!r}"
        )

    for rel in REQUIRED_PATHS:
        assert (ROOT / rel).exists(), f"architecture guide names missing path {rel}"
        assert rel in text, f"architecture guide no longer routes through {rel}"

    for target in re.findall(r"\[[^\]]+\]\(([^)]+)\)", text):
        if target.startswith(("http://", "https://", "#")):
            continue
        path = target.split("#", 1)[0]
        assert (ROOT / path).exists(), f"architecture guide has broken local link {target}"


def validate_entry_links(readme: str, agents: str) -> None:
    readme_prefix = readme.encode("utf-8")[:2_000].decode("utf-8", errors="ignore")
    assert "[architecture and repository guide](ARCHITECTURE.md)" in readme_prefix
    assert "It assumes no Lean or project history" in normalise(readme_prefix)
    assert "ARCHITECTURE.md" in agents
    assert "plain-language human guide" in agents


def main() -> int:
    validate_guide(GUIDE.read_text(encoding="utf-8"))
    validate_entry_links(
        README.read_text(encoding="utf-8"),
        AGENTS.read_text(encoding="utf-8"),
    )
    print("architecture guide: first-principles structure and entry links verified")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
