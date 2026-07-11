#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial checks for the cold-clone comprehension diagnostic."""

from __future__ import annotations

import json

import check_cold_clone_comprehension as diagnostic


def without_tokens(bundle: str, tokens: list[str | None]) -> str:
    for token in tokens:
        if token:
            bundle = bundle.replace(token, "")
    return bundle


def main() -> int:
    claims = json.loads(diagnostic.read("docs/claims.json"))
    methodology = json.loads(diagnostic.read("docs/methodology.json"))
    questions = diagnostic.build_questions(claims, methodology)
    human_bundle = "\n".join(diagnostic.read(path) for path in diagnostic.HUMAN_SURFACES)
    machine_bundle = "\n".join(diagnostic.read(path) for path in diagnostic.MACHINE_SURFACES)

    checks = 0
    for question in questions:
        machine_ok, _ = diagnostic.probe(question["machine_all"], machine_bundle, "all")
        human_ok, _ = diagnostic.probe_groups(question["human_groups"], human_bundle)
        assert machine_ok and human_ok, f"baseline failed for {question['id']}"
        checks += 1

        for token in question["machine_all"]:
            mutated = without_tokens(machine_bundle, [token])
            mutation_ok, _ = diagnostic.probe(question["machine_all"], mutated, "all")
            assert not mutation_ok, f"machine-token deletion escaped for {question['id']}: {token}"
            checks += 1

        for group in question["human_groups"]:
            mutated = without_tokens(human_bundle, group)
            mutation_ok, _ = diagnostic.probe_groups(question["human_groups"], mutated)
            assert not mutation_ok, f"human semantic-group deletion escaped for {question['id']}: {group}"
            checks += 1

    mutation_count = checks - len(questions)
    print(
        "test_cold_clone_comprehension: baseline passed; "
        f"all {mutation_count} semantic-anchor deletions were rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
