#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Cold-clone comprehension diagnostic.

Availability, not correctness. From a fresh clone, can a human reader (using the
prose surfaces) and an agent (using the machine surfaces) each recover the same
seven distinctions the release is built to keep straight? The canonical answers
are derived from docs/claims.json and docs/methodology.json, so this check
follows the registry rather than a hand-maintained answer key.

A failure means a projection or route dropped a distinction, not that any
mathematics is wrong. A pass certifies availability, not mathematical
correctness. This is a diagnostic, not a release gate: it is not run by
scripts/check_release.py and never blocks a build.

Stdlib only; run from the repository root:
  python3 scripts/check_cold_clone_comprehension.py
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent

# Human reader: the text-available prose surfaces. The paper is the third human
# surface named in the design, but it ships as a compiled PDF, so it is excluded
# from this text probe rather than silently assumed to carry the tokens.
HUMAN_SURFACES = ["README.md", "METHODOLOGY.md", "SCOPE.md"]
# Agent reader: the structured machine surfaces.
MACHINE_SURFACES = [
    "docs/claims.json",
    "docs/methodology.json",
    "docs/corpus_descriptor.json",
    "docs/declaration_atlas.json",
]


def read(rel: str) -> str:
    path = ROOT / rel
    return path.read_text(encoding="utf-8") if path.is_file() else ""


def claim_by_id(claims: dict[str, Any], claim_id: str) -> dict[str, Any]:
    return next((c for c in claims["claims"] if c["id"] == claim_id), {})


def first_decl_name(claim: dict[str, Any]) -> str | None:
    decls = claim.get("declarations") or []
    return decls[0]["name"] if decls else None


def build_questions(claims: dict[str, Any], methodology: dict[str, Any]) -> list[dict[str, Any]]:
    """Derive each question's recoverable tokens from the live registry.

    machine_all: every token must appear in the machine bundle (structured data
    should carry each id). human_any: at least one token must appear in the human
    bundle (prose need only surface the distinction once).
    """
    remaining_ids = [row["id"] for row in claims["remaining_open_propositions"]]
    required_review = [
        row["id"] for row in methodology["change_classes"] if row.get("human_review") == "required"
    ]
    reduction = claim_by_id(claims, "certificate_reduction")
    ladder = claim_by_id(claims, "mersenne_lambert_ladder")
    support = claim_by_id(claims, "support_families")
    finite = claim_by_id(claims, "certified_kill_instances")

    return [
        {
            "id": "q1_proved_about_249",
            "question": "What is proved about Erdős #249?",
            "machine_all": ["certificate_reduction", "denominator_exclusion"],
            "human_any": [n for n in (first_decl_name(reduction),) if n] + ["denominator"],
        },
        {
            "id": "q2_what_remains_open",
            "question": "What proposition still remains open?",
            "machine_all": remaining_ids,
            "human_any": remaining_ids,
        },
        {
            "id": "q3_finite_does_not_settle",
            "question": "Why do the finite certificates not settle it?",
            "machine_all": ["verified finite instance", "remaining_open.unbounded_certificate_supply"],
            "human_any": ["verified finite instance", "unbounded"],
        },
        {
            "id": "q4_257_proved_vs_universal",
            "question": "Which #257 statements are proved, and which universal statement remains open?",
            "machine_all": ["support_families", "universal_257", "remaining_open.universal_257_all_infinite_supports"],
            "human_any": [n for n in (first_decl_name(support),) if n] + ["universal"],
        },
        {
            "id": "q5_representation_transport",
            "question": "Which representation changes have checked transport?",
            "machine_all": ["mersenne_lambert_ladder"],
            "human_any": [n for n in (first_decl_name(ladder),) if n] + ["Mersenne"],
        },
        {
            "id": "q6_proof_authority",
            "question": "What is proof authority?",
            "machine_all": ["Lean source checked by the pinned Lean kernel"],
            "human_any": ["proof authority", "Lean kernel"],
        },
        {
            "id": "q7_which_changes_need_review",
            "question": "Which classes of repository change require mathematical review?",
            "machine_all": required_review,
            "human_any": ["required"],
        },
    ]


def probe(tokens: list[str], bundle: str, mode: str) -> tuple[bool, list[str]]:
    present = [t for t in tokens if t and t in bundle]
    missing = [t for t in tokens if t and t not in bundle]
    if mode == "all":
        return (not missing, missing)
    return (bool(present), missing if not present else [])


def main() -> int:
    claims = json.loads(read("docs/claims.json"))
    methodology = json.loads(read("docs/methodology.json"))
    human_bundle = "\n".join(read(s) for s in HUMAN_SURFACES)
    machine_bundle = "\n".join(read(s) for s in MACHINE_SURFACES)

    questions = build_questions(claims, methodology)
    failures: list[str] = []

    print("Cold-clone comprehension diagnostic (availability, not correctness)")
    print(f"  human surfaces  : {', '.join(HUMAN_SURFACES)} (paper PDF excluded from text probe)")
    print(f"  machine surfaces: {', '.join(MACHINE_SURFACES)}")
    print()

    for q in questions:
        machine_ok, machine_missing = probe(q["machine_all"], machine_bundle, "all")
        human_ok, _ = probe(q["human_any"], human_bundle, "any")
        mark = "PASS" if (machine_ok and human_ok) else "FAIL"
        print(f"  [{mark}] {q['id']}: {q['question']}")
        if not machine_ok:
            failures.append(f"{q['id']}: machine surfaces missing {machine_missing}")
            print(f"         machine bundle missing: {machine_missing}")
        if not human_ok:
            failures.append(f"{q['id']}: human surfaces recover none of {q['human_any']}")
            print(f"         human bundle recovered none of: {q['human_any']}")

    print()
    if failures:
        print(f"cold-clone comprehension: {len(failures)} surface gap(s)")
        for f in failures:
            print(f"  GAP {f}")
        return 1
    print(f"cold-clone comprehension: all {len(questions)} distinctions recoverable from both audiences")
    return 0


if __name__ == "__main__":
    sys.exit(main())
