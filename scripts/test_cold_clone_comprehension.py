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


def main() -> int:
    packets = diagnostic.collect_agent_packets()
    summary = packets["summary"]
    human_bundle = "\n".join(diagnostic.read(path) for path in diagnostic.HUMAN_SURFACES)
    diagnostic.validate_human_first_contact(summary, human_bundle)
    diagnostic.validate_agent_packets(packets)

    checks = 2
    for alternatives in diagnostic.human_requirements(summary):
        mutated = human_bundle
        for token in alternatives:
            mutated = mutated.replace(token, "")
        try:
            diagnostic.validate_human_first_contact(summary, mutated)
        except AssertionError:
            checks += 1
        else:
            raise AssertionError(f"human semantic-anchor deletion escaped: {alternatives}")

    mutated = copy.deepcopy(packets)
    mutated["summary"]["proof_authority"] = "unverified"
    assert_rejected(mutated, "proof authority")
    checks += 1

    mutated = copy.deepcopy(packets)
    mutated["summary"]["remaining_open_propositions"] = []
    assert_rejected(mutated, "open boundary")
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
