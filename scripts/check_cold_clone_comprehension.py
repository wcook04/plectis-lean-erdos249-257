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
HUMAN_FIRST_CONTACT_BUDGET_BYTES = 32_000
PACKET_BUDGET_BYTES = 16_384
PROOF_AUTHORITY = "Lean source checked by the pinned Lean kernel"


def read(rel: str) -> str:
    return (ROOT / rel).read_text(encoding="utf-8")


def encoded_bytes(value: Any) -> int:
    return len(json.dumps(value, ensure_ascii=False, sort_keys=True).encode("utf-8"))


def query_packet(*args: str) -> dict[str, Any]:
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
    assert len(raw) <= PACKET_BUDGET_BYTES, (
        f"query {' '.join(args) or '<summary>'} emitted {len(raw)} bytes "
        f"(budget {PACKET_BUDGET_BYTES})"
    )
    return json.loads(completed.stdout)


def human_requirements(summary: dict[str, Any]) -> list[list[str]]:
    conditional = next(
        row for row in summary["principal_claims"] if row["status"] == "conditional reduction"
    )
    finite = next(
        row for row in summary["principal_claims"] if row["status"] == "verified finite instance"
    )
    requirements = [
        ["Corpus orientation"],
        ["proof authority"],
        ["Lean kernel", "pinned Lean kernel"],
        ["does not prove the irrationality", "does not solve either open problem"],
        [conditional["statement"], "unbounded certificate supply"],
        [finite["statement"], "verified finite instance"],
    ]
    requirements.extend(
        [[row["id"], row["statement"]] for row in summary["remaining_open_propositions"]]
    )
    return requirements


def validate_human_first_contact(summary: dict[str, Any], bundle: str) -> None:
    assert len(bundle.encode("utf-8")) <= HUMAN_FIRST_CONTACT_BUDGET_BYTES
    for alternatives in human_requirements(summary):
        assert any(token in bundle for token in alternatives), (
            f"human first contact lost semantic anchor group {alternatives}"
        )


def collect_agent_packets() -> dict[str, Any]:
    """Collect only bounded query replies needed to walk the public graph."""
    summary = query_packet()
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
    assert encoded_bytes(summary) <= PACKET_BUDGET_BYTES
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


def main() -> int:
    packets = collect_agent_packets()
    summary = packets["summary"]
    human_bundle = "\n".join(read(path) for path in HUMAN_SURFACES)
    validate_human_first_contact(summary, human_bundle)
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
        + 3
    )
    print(
        "cold-clone comprehension: bounded human first contact and "
        f"{query_count} typed query packets verified"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
