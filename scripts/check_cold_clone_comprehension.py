#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Cold-clone comprehension diagnostic.

Availability, not correctness. From a fresh clone, can a human reader (using the
prose surfaces) and an agent (using the machine surfaces) each recover the same
core distinctions the release is built to keep straight? The canonical answers
are derived from docs/claims.json and docs/methodology.json, so this check
follows the registry rather than a hand-maintained answer key. Human evidence is
grouped by meaning: every semantic group must have an anchor, so a generic word
such as "universal" or "required" cannot make a question pass by itself.

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
HUMAN_SURFACES = ["README.md", "METHODOLOGY.md", "SCOPE.md", "docs/ORIENTATION.md"]
# Agent reader: the structured machine surfaces.
MACHINE_SURFACES = [
    "docs/claims.json",
    "docs/methodology.json",
    "docs/corpus_descriptor.json",
    "docs/declaration_atlas.json",
    "docs/orientation.json",
]


def read(rel: str) -> str:
    path = ROOT / rel
    return path.read_text(encoding="utf-8") if path.is_file() else ""


def claim_by_id(claims: dict[str, Any], claim_id: str) -> dict[str, Any]:
    return next((c for c in claims["claims"] if c["id"] == claim_id), {})


def first_decl_name(claim: dict[str, Any]) -> str | None:
    decls = claim.get("declarations") or []
    return decls[0]["name"] if decls else None


def build_questions(
    claims: dict[str, Any], methodology: dict[str, Any], orientation: dict[str, Any]
) -> list[dict[str, Any]]:
    """Derive each question's recoverable tokens from the live registry.

    machine_all: every token must appear in the machine bundle (structured data
    should carry each id). human_groups: every semantic group must contribute at
    least one token to the human bundle. Alternatives within a group allow prose
    and declaration-oriented routes to express the same distinction differently.
    """
    remaining = claims["remaining_open_propositions"]
    remaining_ids = [row["id"] for row in remaining]
    required_review = [
        row for row in methodology["change_classes"] if row.get("human_review") == "required"
    ]
    reduction = claim_by_id(claims, "certificate_reduction")
    exclusion = claim_by_id(claims, "denominator_exclusion")
    ladder = claim_by_id(claims, "mersenne_lambert_ladder")
    support = claim_by_id(claims, "support_families")
    finite = claim_by_id(claims, "certified_kill_instances")

    return [
        {
            "id": "q1_proved_about_249",
            "question": "What is proved about Erdős #249?",
            "machine_all": [
                reduction["id"],
                reduction["status"],
                exclusion["id"],
                exclusion["status"],
            ],
            "human_groups": [
                [exclusion["label"], first_decl_name(exclusion), "7.96 × 10³⁴"],
                [reduction["label"], first_decl_name(reduction), "unbounded certificate supply"],
                ["does not solve either open problem", "does not prove the irrationality"],
            ],
        },
        {
            "id": "q2_what_remains_open",
            "question": "Which three propositions remain open?",
            "machine_all": remaining_ids,
            "human_groups": [[row["id"], row["statement"]] for row in remaining],
        },
        {
            "id": "q3_finite_does_not_settle",
            "question": "Why do the finite certificates not settle it?",
            "machine_all": [
                finite["status"],
                finite["bounded_domain"],
                "remaining_open.unbounded_certificate_supply",
            ],
            "human_groups": [
                [finite["status"]],
                ["fixed bounds", "bounded region", "through t = 8"],
                ["unbounded certificate supply", "remaining_open.unbounded_certificate_supply"],
            ],
        },
        {
            "id": "q4_257_proved_vs_universal",
            "question": "Which #257 statements are proved, and which universal statement remains open?",
            "machine_all": [
                support["id"],
                support["status"],
                "universal_257",
                "remaining_open.universal_257_all_infinite_supports",
            ],
            "human_groups": [
                [support["label"], first_decl_name(support)],
                [
                    "universal Erdős #257",
                    "universal #257",
                    "remaining_open.universal_257_all_infinite_supports",
                ],
                ["not the universal statement", "does not prove the universal"],
            ],
        },
        {
            "id": "q5_representation_transport",
            "question": "Which representation changes have checked transport?",
            "machine_all": [ladder["id"], *[row["name"] for row in ladder["declarations"]]],
            "human_groups": [
                [ladder["label"], first_decl_name(ladder)],
                ["Mersenne–Lambert", "Mersenne--Lambert", "Möbius-square lens"],
                ["kernel-checked", "Lean declaration"],
            ],
        },
        {
            "id": "q6_proof_authority",
            "question": "What is proof authority?",
            "machine_all": ["Lean source checked by the pinned Lean kernel"],
            "human_groups": [
                ["proof authority"],
                ["Lean kernel", "pinned Lean kernel"],
                ["Provider or model output is not proof authority", "provider output"],
            ],
        },
        {
            "id": "q7_which_changes_need_review",
            "question": "Which classes of repository change require mathematical review?",
            "machine_all": [row["id"] for row in required_review],
            "human_groups": [[row["summary"]] for row in required_review],
        },
        {
            "id": "q8_scale_and_drilldown",
            "question": "How large is the checked corpus, and where does a reader drill down?",
            "machine_all": [
                orientation["schema"],
                str(orientation["scale"]["module_count"]),
                str(orientation["scale"]["declaration_count"]),
                "principal_claims",
                "drilldowns",
            ],
            "human_groups": [
                ["Corpus orientation"],
                [f"{orientation['scale']['module_count']:,}"],
                [f"{orientation['scale']['declaration_count']:,}"],
                ["Exact open boundary"],
                ["Principal claim routes"],
            ],
        },
        {
            "id": "q9_external_registration",
            "question": "How does an external system register and expand the corpus, including its authored papers?",
            "machine_all": [
                "erdos249257-corpus-descriptor/3",
                "principal_declaration_handles",
                "module_topology",
                "migration_from_v2",
                "expected_content_digest",
                "human_exposition",
                "technical_companion",
                "paper_source_sigils",
                "source_content_digest",
                "rendered_content_digest",
                "authored_editorial_surface_not_Lean_proof_authority",
            ],
            "human_groups": [
                ["External corpus registration"],
                ["erdos249257-corpus-descriptor/3"],
                ["below 64 KB"],
                ["digest-bound expansion files"],
                ["both authored papers"],
                ["paper-to-Lean source-sigil crosswalk"],
                ["remain distinct from Lean proof authority"],
            ],
        },
    ]


def probe(tokens: list[str], bundle: str, mode: str) -> tuple[bool, list[str]]:
    present = [t for t in tokens if t and t in bundle]
    missing = [t for t in tokens if t and t not in bundle]
    if mode == "all":
        return (not missing, missing)
    return (bool(present), missing if not present else [])


def probe_groups(
    groups: list[list[str | None]], bundle: str
) -> tuple[bool, list[list[str]]]:
    """Require at least one non-empty anchor from every semantic group."""
    missing: list[list[str]] = []
    for group in groups:
        anchors = [token for token in group if token]
        if not any(token in bundle for token in anchors):
            missing.append(anchors)
    return (not missing, missing)


def main() -> int:
    claims = json.loads(read("docs/claims.json"))
    methodology = json.loads(read("docs/methodology.json"))
    orientation = json.loads(read("docs/orientation.json"))
    human_bundle = "\n".join(read(s) for s in HUMAN_SURFACES)
    machine_bundle = "\n".join(read(s) for s in MACHINE_SURFACES)

    questions = build_questions(claims, methodology, orientation)
    failures: list[str] = []

    print("Cold-clone comprehension diagnostic (availability, not correctness)")
    print(f"  human surfaces  : {', '.join(HUMAN_SURFACES)} (paper PDF excluded from text probe)")
    print(f"  machine surfaces: {', '.join(MACHINE_SURFACES)}")
    print()

    for q in questions:
        machine_ok, machine_missing = probe(q["machine_all"], machine_bundle, "all")
        human_ok, human_missing = probe_groups(q["human_groups"], human_bundle)
        mark = "PASS" if (machine_ok and human_ok) else "FAIL"
        print(f"  [{mark}] {q['id']}: {q['question']}")
        if not machine_ok:
            failures.append(f"{q['id']}: machine surfaces missing {machine_missing}")
            print(f"         machine bundle missing: {machine_missing}")
        if not human_ok:
            failures.append(f"{q['id']}: human surfaces missing semantic groups {human_missing}")
            print(f"         human bundle missing semantic groups: {human_missing}")

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
