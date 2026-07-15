#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial tests for bounded cold-clone comprehension."""

from __future__ import annotations

import copy

import check_cold_clone_comprehension as diagnostic


def assert_rejected(packets: dict, label: str) -> None:
    try:
        diagnostic.validate_agent_packets(packets)
    except AssertionError:
        return
    raise AssertionError(f"semantic mutation escaped: {label}")


def assert_human_rejected(summary: dict, surfaces: dict[str, str], label: str) -> None:
    try:
        diagnostic.validate_human_first_contact(summary, surfaces)
    except AssertionError:
        return
    raise AssertionError(f"human first-contact mutation escaped: {label}")


def main() -> int:
    packets = diagnostic.collect_agent_packets()
    summary = packets["summary"]
    human_surfaces = {
        path: diagnostic.read(path) for path in diagnostic.HUMAN_SURFACES
    }
    diagnostic.validate_human_first_contact(summary, human_surfaces)
    gateway_paper = diagnostic.read(diagnostic.GATEWAY_PAPER)
    diagnostic.validate_gateway_opening(gateway_paper)
    agents = diagnostic.read("AGENTS.md")
    claude = diagnostic.read("CLAUDE.md")
    diagnostic.validate_cross_agent_entry(agents, claude)
    diagnostic.validate_agent_packets(packets)

    checks = 2
    for task_id, requirements in diagnostic.human_tasks(summary).items():
        for alternatives in requirements:
            mutated = copy.deepcopy(human_surfaces)
            mutated["README.md"] = diagnostic.normalized(mutated["README.md"])
            for token in alternatives:
                mutated["README.md"] = mutated["README.md"].replace(
                    diagnostic.normalized(token), ""
                )
            assert_human_rejected(summary, mutated, f"{task_id}: {alternatives}")
            checks += 1

    mutated = copy.deepcopy(human_surfaces)
    mutated["README.md"] = mutated["README.md"].replace(
        "## What remains open", "## Deferred questions"
    )
    assert_human_rejected(summary, mutated, "first-minute section contract")
    checks += 1

    mutated_paper = gateway_paper.replace(
        "Produce these certificates at unbounded parameters", ""
    )
    try:
        diagnostic.validate_gateway_opening(mutated_paper)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("gateway exact-open-edge deletion escaped")

    mutated_paper = gateway_paper.replace(
        r"\paragraph{Reading map.}", r"\paragraph{Reading map.}\lref{Fake.lean}{1}{fake}"
    )
    try:
        diagnostic.validate_gateway_opening(mutated_paper)
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("gateway source-inventory leak escaped")

    try:
        diagnostic.validate_cross_agent_entry(agents, claude.replace("@AGENTS.md", ""))
    except AssertionError:
        checks += 1
    else:
        raise AssertionError("Claude shared-instruction import deletion escaped")

    mutated = copy.deepcopy(packets)
    mutated["summary"]["proof_authority"] = "unverified"
    assert_rejected(mutated, "proof authority")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["summary"]["remaining_open_propositions"] = []
    assert_rejected(mutated, "open boundary")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["story_routes"]["erdos257_half_story"]["route"]["query_steps"].pop()
    assert_rejected(mutated, "#257 story route")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["story_claims"]["half_greedy_two_thirds_band"]["claim"]["statement"] = (
        "The actual greedy orbit for 1/2 avoids the band."
    )
    assert_rejected(mutated, "#257 singleton-band orbit boundary")
    checks += 1

    mutated = copy.deepcopy(packets)
    last_producer = mutated["story_claims"]["last_producer_tail_escape_reduction"]
    last_producer["argument_neighbourhood"]["incoming"] = [
        row
        for row in last_producer["argument_neighbourhood"]["incoming"]
        if row["relation"] != "eliminates_case"
    ]
    assert_rejected(mutated, "#257 eliminated-case edge")
    checks += 1

    mutated = copy.deepcopy(packets)
    first_harmonic = mutated["story_claims"]["first_harmonic_certificate_interface"]
    first_harmonic["argument_neighbourhood"]["outgoing"] = [
        row
        for row in first_harmonic["argument_neighbourhood"]["outgoing"]
        if row["neighbour"]["id"] != "certificate_completeness"
    ]
    assert_rejected(mutated, "#249 completeness-consumer edge")
    checks += 1

    conditional = next(
        claim_id for claim_id, packet in packets["claims"].items()
        if packet["claim"]["status"] == "conditional reduction"
    )
    mutated = copy.deepcopy(packets)
    mutated["claims"][conditional]["claim"]["remaining_open_proposition_ids"] = []
    assert_rejected(mutated, "conditional-open link")
    checks += 1

    finite = next(
        claim_id for claim_id, packet in packets["claims"].items()
        if packet["claim"]["status"] == "verified finite instance"
    )
    mutated = copy.deepcopy(packets)
    mutated["claims"][finite]["claim"].pop("bounded_domain", None)
    assert_rejected(mutated, "finite bound")
    checks += 1

    source_key = next(iter(packets["sources"]))
    mutated = copy.deepcopy(packets)
    mutated["sources"][source_key]["source"]["source_ref"] = "wrong.lean:1"
    assert_rejected(mutated, "source coordinate")
    checks += 1

    print(
        "test_cold_clone_comprehension: bounded baseline passed; "
        f"{checks - 2} semantic mutations were rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
