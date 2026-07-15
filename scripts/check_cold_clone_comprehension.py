#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Verify bounded first-contact comprehension in a fresh public checkout.

This evaluator deliberately does *not* concatenate the exhaustive claim,
methodology, or declaration owners.  A cold reader starts from the compact
human surfaces; a coding agent starts from the bounded corpus query and then
follows typed packets.  The authoritative owners remain available as explicit
expansions, but are not evidence for first-contact comprehension.

This checks navigation semantics and response budgets, not Lean proof
correctness.  The pinned Lean source checked by the kernel remains proof
authority.
"""

from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
QUERY = ROOT / "scripts" / "query_corpus.py"
HUMAN_SURFACES = ("README.md", "SCOPE.md", "docs/ORIENTATION.md")
HUMAN_SURFACE_BUDGET_BYTES = {
    "README.md": 9_000,
    "SCOPE.md": 4_000,
    "docs/ORIENTATION.md": 16_000,
}
README_FIRST_MINUTE_BUDGET_BYTES = 6_000
SUMMARY_PACKET_BUDGET_BYTES = 32_000
PACKET_BUDGET_BYTES = 16_384
PROOF_AUTHORITY = "Lean source checked by the pinned Lean kernel"
GATEWAY_PAPER = "paper/erdos249-257-exposition.tex"
GATEWAY_OPENING_BUDGET_BYTES = 7_500
CLAUDE_ENTRY_BUDGET_BYTES = 1_500
STORY_ROUTES = ("erdos257_half_story", "erdos249_certificate_story")
STORY_CLAIMS = (
    "greedy_achievement_geometry",
    "half_greedy_two_thirds_band",
    "half_membership_seam_classification",
    "fatal_gap_right_tail_classification",
    "final_middle_cell_escape",
    "last_producer_tail_escape_reduction",
    "certificate_reduction",
    "certificate_completeness",
    "first_harmonic_certificate_interface",
)


def read(rel: str) -> str:
    return (ROOT / rel).read_text(encoding="utf-8")


def encoded_bytes(value: Any) -> int:
    return len(json.dumps(value, ensure_ascii=False, sort_keys=True).encode("utf-8"))


def query_packet(*args: str, budget_bytes: int = PACKET_BUDGET_BYTES) -> dict[str, Any]:
    """Run the public CLI exactly as a cold coding agent would."""
    completed = subprocess.run(
        [sys.executable, str(QUERY), *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        raise AssertionError(completed.stdout.strip() or completed.stderr.strip())
    raw = completed.stdout.encode("utf-8")
    assert len(raw) <= budget_bytes, (
        f"query {' '.join(args) or '<summary>'} emitted {len(raw)} bytes "
        f"(budget {budget_bytes})"
    )
    return json.loads(completed.stdout)


def human_tasks(summary: dict[str, Any]) -> dict[str, list[list[str]]]:
    """Facts a reader must recover from the README's first-minute prefix.

    Each task contains conjunctions of semantic anchor groups.  Alternatives
    within one group permit harmless wording changes; satisfying one task with
    tokens scattered across three documents is deliberately impossible.
    """
    open_rows = {row["id"]: row for row in summary["remaining_open_propositions"]}
    return {
        "identity_and_public_boundary": [
            ["self-contained public"],
            ["Plectis"],
            ["not an entrypoint into any private development system"],
        ],
        "state_both_problems": [
            ["Erdős #249 asks whether"],
            ["S = ∑ φ(n)/2ⁿ"],
            ["Erdős #257 asks whether"],
            ["∑_{n∈A} 1/(2ⁿ - 1)"],
            ["every infinite", "for every infinite"],
        ],
        "distinguish_release_source_and_authority": [
            ["latest tagged release and citation anchor"],
            ["formal-source checkpoint"],
            ["not a new tagged release"],
            [PROOF_AUTHORITY],
        ],
        "recover_headline_statuses": [
            ["formalised here"],
            ["unconditional progress"],
            ["conditional reduction"],
            ["verified finite instance"],
            ["does not show that the actual orbit avoids", "does not show the actual orbit avoids"],
        ],
        "name_exact_open_frontier": [
            [open_rows["remaining_open.erdos_249_irrationality"]["statement"],
             "Prove that `S = ∑ φ(n)/2ⁿ` is irrational"],
            [open_rows["remaining_open.unbounded_certificate_supply"]["statement"],
             "Produce the unbounded certificate supply"],
            [open_rows["remaining_open.universal_257_all_infinite_supports"]["statement"],
             "Prove irrationality of `∑_{n∈A} 1/(2ⁿ - 1)` for every infinite"],
        ],
        "choose_a_next_read": [
            ["Exposition PDF"],
            ["AGENTS.md"],
            ["docs/orientation.json"],
            ["docs/SOURCE_MAP.md"],
        ],
    }


def first_bytes(text: str, limit: int) -> str:
    return text.encode("utf-8")[:limit].decode("utf-8", errors="ignore")


def normalized(text: str) -> str:
    return " ".join(text.split())


def contains_any(text: str, alternatives: list[str]) -> bool:
    compact = normalized(text)
    return any(normalized(token) in compact for token in alternatives)


def validate_human_first_contact(
    summary: dict[str, Any], surfaces: dict[str, str]
) -> None:
    assert set(surfaces) == set(HUMAN_SURFACES)
    for path, budget in HUMAN_SURFACE_BUDGET_BYTES.items():
        size = len(surfaces[path].encode("utf-8"))
        assert size <= budget, f"{path} is {size} bytes (budget {budget})"

    readme_prefix = first_bytes(surfaces["README.md"], README_FIRST_MINUTE_BUDGET_BYTES)
    section_order = (
        "## The two problems",
        "## What the formal source establishes",
        "## What remains open",
        "## Read or run it",
    )
    positions = [readme_prefix.find(heading) for heading in section_order]
    assert all(position >= 0 for position in positions), (
        f"README first-minute prefix lost section sequence {section_order}"
    )
    assert positions == sorted(positions), "README first-minute sections are out of order"

    for task_id, requirements in human_tasks(summary).items():
        for alternatives in requirements:
            assert contains_any(readme_prefix, alternatives), (
                f"README first-minute task {task_id!r} lost semantic anchor group "
                f"{alternatives}"
            )

    scope = surfaces["SCOPE.md"]
    assert contains_any(scope, ["does not prove"])
    assert contains_any(scope, ["formal-source checkpoint"])
    orientation = surfaces["docs/ORIENTATION.md"]
    for status in (
        "formalised here",
        "unconditional progress",
        "conditional reduction",
        "verified finite instance",
    ):
        assert contains_any(orientation, [summary["status_taxonomy"][status]])
    for row in summary["remaining_open_propositions"]:
        assert row["id"] in orientation and contains_any(orientation, [row["statement"]])


def validate_gateway_opening(paper: str) -> None:
    """Check that the authored introduction works without source inventory."""
    start = paper.index(r"\section{Introduction}")
    end = paper.index(r"\section{The Mersenne--Lambert ladder}")
    opening = paper[start:end]
    size = len(opening.encode("utf-8"))
    assert size <= GATEWAY_OPENING_BUDGET_BYTES, (
        f"gateway introduction is {size} bytes (budget {GATEWAY_OPENING_BUDGET_BYTES})"
    )
    requirements = {
        "both_problem_statements": [
            [r"Erd\H{o}s~\#249 asks whether"],
            [r"Erd\H{o}s~\#257 asks whether"],
        ],
        "status_table": [
            ["problem & checked here & exact open edge"],
            [r"q>\Qzero\approx7.96\times10^{34}"],
            ["28 lcm-diagonal scales"],
        ],
        "exact_residuals": [
            ["Produce these certificates at unbounded parameters"],
            [r"middle coordinates $-2$ and $-1$"],
        ],
        "common_architecture": [
            ["exact tail and carry identities separate finite arithmetic"],
            ["not an assertion that the two open problems are equivalent"],
        ],
        "reading_map": [
            [r"\paragraph{Reading map.}"],
            [r"Section~\ref{sec:eb}"],
            [r"Section~\ref{sec:249}"],
        ],
    }
    for task_id, groups in requirements.items():
        for alternatives in groups:
            assert contains_any(opening, alternatives), (
                f"gateway opening task {task_id!r} lost {alternatives}"
            )
    for source_inventory_token in (r"\lref", r"\idn", ".lean", "module inventory"):
        assert source_inventory_token not in opening, (
            f"gateway opening exposes source-inventory token {source_inventory_token!r}"
        )


def validate_cross_agent_entry(agents: str, claude: str) -> None:
    """Keep one shared semantic core with a small Claude-native adapter."""
    assert len(claude.encode("utf-8")) <= CLAUDE_ENTRY_BUDGET_BYTES
    for token in (
        "docs/orientation.json",
        "docs/claims.json",
        "Lean source checked by the pinned Lean kernel",
        "not an entrypoint into any private development system",
    ):
        assert contains_any(agents, [token]), f"AGENTS.md lost shared invariant {token!r}"
    for token in (
        "@AGENTS.md",
        "Claude-specific deltas only",
        "docs/orientation.json",
        "not an entrypoint into any private development system",
    ):
        assert contains_any(claude, [token]), f"CLAUDE.md lost native adapter token {token!r}"
    assert "## First read" not in claude, "CLAUDE.md duplicated the shared first-read manual"


def collect_agent_packets() -> dict[str, Any]:
    """Collect only bounded query replies needed to walk the public graph."""
    summary = query_packet(budget_bytes=SUMMARY_PACKET_BUDGET_BYTES)
    packets: dict[str, Any] = {
        "summary": summary,
        "opens": {},
        "claims": {},
        "papers": {},
        "declarations": {},
        "sources": {},
        "modules": {},
        "sigil_modules": {},
        "route": query_packet("--route", "instant_orientation"),
        "story_routes": {
            route_id: query_packet("--route", route_id) for route_id in STORY_ROUTES
        },
        "story_claims": {
            claim_id: query_packet("--claim", claim_id) for claim_id in STORY_CLAIMS
        },
    }
    for row in summary["remaining_open_propositions"]:
        packets["opens"][row["id"]] = query_packet("--open", row["id"])
    for row in summary["principal_claims"]:
        claim_id = row["id"]
        claim = query_packet("--claim", claim_id)
        packets["claims"][claim_id] = claim
        paper_label = claim["claim"].get("paper_label")
        if paper_label:
            packets["papers"][paper_label] = query_packet("--paper-label", paper_label)
        for declaration in claim["claim"]["declarations"][:1]:
            key = f"{declaration['module']}:{declaration['line']}"
            packets["declarations"][key] = query_packet(
                "--declaration", declaration["name"]
            )
            packets["sources"][key] = query_packet("--source", key)
            module = query_packet("--module", declaration["module"])
            packets["modules"][declaration["module"]] = module
            sigil = module.get("paper_sigil")
            if sigil:
                packets["sigil_modules"][sigil] = query_packet("--module", sigil)
    artifact = query_packet("--artifact", "docs/orientation.json")
    packets["artifact"] = artifact
    digest = artifact["matches"][0]["content_digest"]
    packets["artifact_digest"] = query_packet("--artifact", digest)
    return packets


def validate_agent_packets(packets: dict[str, Any]) -> None:
    summary = packets["summary"]
    assert summary["kind"] == "corpus_summary"
    assert summary["authority_posture"] == "navigation_projection_not_proof_authority"
    assert summary["proof_authority"] == PROOF_AUTHORITY
    assert encoded_bytes(summary) <= SUMMARY_PACKET_BUDGET_BYTES
    assert summary["remaining_open_propositions"]

    principal = {row["id"]: row for row in summary["principal_claims"]}
    assert any(row["status"] == "conditional reduction" for row in principal.values())
    assert any(row["status"] == "verified finite instance" for row in principal.values())

    for open_id, packet in packets["opens"].items():
        proposition = packet["open_proposition"]
        assert proposition["id"] == open_id
        assert packet["authority_posture"] == "authored_open_boundary_navigation_not_proof_authority"
        assert proposition["paper_anchor"] is not None
        assert packet["open_target"]["status"] == "open"

    for claim_id, packet in packets["claims"].items():
        claim = packet["claim"]
        assert claim["id"] == claim_id
        assert claim["status"] == principal[claim_id]["status"]
        assert packet["authority_posture"] == "navigation_projection_not_proof_authority"
        if claim["status"] == "conditional reduction":
            assert claim["remaining_open_proposition_ids"]
        if claim["status"] == "verified finite instance":
            assert claim.get("bounded_domain")
        paper_label = claim.get("paper_label")
        if paper_label:
            assert paper_label in packets["papers"]
            assert packets["papers"][paper_label]["paper"]["label"] == paper_label
        for declaration in claim["declarations"][:1]:
            key = f"{declaration['module']}:{declaration['line']}"
            exact = [
                row
                for row in packets["declarations"][key]["matches"]
                if row["module"] == declaration["module"] and row["line"] == declaration["line"]
            ]
            assert len(exact) == 1
            source = packets["sources"][key]["source"]
            assert source["source_ref"] == key
            module = packets["modules"][declaration["module"]]
            assert module["module"]["path"] == declaration["module"]
            sigil = module.get("paper_sigil")
            if sigil:
                assert packets["sigil_modules"][sigil]["module"]["path"] == declaration["module"]

    artifact = packets["artifact"]["matches"]
    digest_matches = packets["artifact_digest"]["matches"]
    assert artifact and digest_matches
    assert artifact[0]["artifact_handle"] in {
        row["artifact_handle"] for row in digest_matches
    }
    assert packets["route"]["route"]["id"] == "instant_orientation"
    assert packets["route"]["proof_authority"] == PROOF_AUTHORITY
    route = packets["route"]["route"]
    assert "docs/claims.json" not in route["read"]
    assert route["query_steps"]
    assert route["authority_owners"]
    assert route["adjacent_handle_classes"]

    story_routes = packets["story_routes"]
    assert tuple(story_routes) == STORY_ROUTES
    assert [
        step.rsplit(" ", 1)[-1]
        for step in story_routes["erdos257_half_story"]["route"]["query_steps"]
    ] == list(STORY_CLAIMS[:6])
    assert story_routes["erdos249_certificate_story"]["route"]["query_steps"][-1].endswith(
        "remaining_open.unbounded_certificate_supply"
    )

    story_claims = packets["story_claims"]
    singleton_band = story_claims["half_greedy_two_thirds_band"]
    assert ("builds_on", "greedy_achievement_geometry") in {
        (row["relation"], row["neighbour"]["id"])
        for row in singleton_band["argument_neighbourhood"]["outgoing"]
    }
    assert (
        "no theorem here says that the actual greedy orbit for 1/2 avoids the band"
        in singleton_band["claim"]["statement"]
    )
    half_membership = story_claims["half_membership_seam_classification"]
    assert {
        (row["relation"], row["neighbour"]["id"])
        for row in half_membership["argument_neighbourhood"]["outgoing"]
    } >= {
        ("builds_on", "greedy_achievement_geometry"),
        ("builds_on", "fatal_gap_right_tail_classification"),
    }
    last_producer = story_claims["last_producer_tail_escape_reduction"]
    assert ("eliminates_case", "final_middle_cell_escape") in {
        (row["relation"], row["neighbour"]["id"])
        for row in last_producer["argument_neighbourhood"]["incoming"]
    }
    assert ("builds_on", "fatal_gap_right_tail_classification") in {
        (row["relation"], row["neighbour"]["id"])
        for row in last_producer["argument_neighbourhood"]["outgoing"]
    }
    first_harmonic = story_claims["first_harmonic_certificate_interface"]
    assert {
        row["neighbour"]["id"]
        for row in first_harmonic["argument_neighbourhood"]["outgoing"]
        if row["relation"] == "builds_on"
    } >= {"certificate_reduction", "certificate_completeness"}


def main() -> int:
    packets = collect_agent_packets()
    summary = packets["summary"]
    human_surfaces = {path: read(path) for path in HUMAN_SURFACES}
    validate_human_first_contact(summary, human_surfaces)
    validate_gateway_opening(read(GATEWAY_PAPER))
    validate_cross_agent_entry(read("AGENTS.md"), read("CLAUDE.md"))
    validate_agent_packets(packets)
    query_count = (
        1
        + len(packets["opens"])
        + len(packets["claims"])
        + len(packets["papers"])
        + len(packets["declarations"])
        + len(packets["sources"])
        + len(packets["modules"])
        + len(packets["sigil_modules"])
        + len(packets["story_routes"])
        + len(packets["story_claims"])
        + 3
    )
    print(
        "cold-clone comprehension: bounded human first contact and "
        f"{query_count} typed query packets verified"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
