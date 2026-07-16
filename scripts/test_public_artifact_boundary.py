#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep public navigation from treating unpublished work as corpus authority."""

from __future__ import annotations

import json
import subprocess
import sys
from copy import deepcopy
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
QUERY = ROOT / "scripts" / "query_corpus.py"


def read(rel: str) -> str:
    return (ROOT / rel).read_text(encoding="utf-8")


def summary_packet() -> dict[str, object]:
    completed = subprocess.run(
        [sys.executable, str(QUERY)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return json.loads(completed.stdout)


def boundary_errors(
    agents: str,
    scope: str,
    readme: str,
    claims: dict[str, object],
    methodology: dict[str, object],
    summary: dict[str, object],
) -> list[str]:
    """Return every missing public-proof boundary required at first contact."""
    errors: list[str] = []
    for phrase in (
        "not an entrypoint into any private development system",
        "Work only from the files\nin this repository",
        "never infer unpublished results or private machinery",
    ):
        if phrase not in agents:
            errors.append(f"agent entry lost public-boundary phrase: {phrase}")
    for phrase in (
        "Unreleased work, private repositories",
        "not part of\nthe public proof artefact",
    ):
        if phrase not in scope:
            errors.append(f"scope lost public-boundary phrase: {phrase}")
    if "do not infer results from private or unreleased work" not in readme:
        errors.append("README lost private-or-unreleased inference boundary")

    non_claims = {row["id"] for row in claims["non_claims"]}
    required_non_claims = {
        "not_private_root_equivalence",
        "not_hidden_proof_body_authority",
        "not_provider_proof_authority",
    }
    missing_non_claims = sorted(required_non_claims - non_claims)
    if missing_non_claims:
        errors.append(f"claim registry lost public-boundary non-claims: {missing_non_claims}")

    anti_principles = {row["id"]: row["statement"] for row in methodology["anti_principles"]}
    private_work_rule = anti_principles.get(
        "anti_principle.do_not_treat_graph_model_or_private_work_as_proof", ""
    )
    if "private proof sketch is not public proof authority" not in private_work_rule:
        errors.append("methodology lost private-proof authority boundary")

    projected_non_claims = {row["id"] for row in summary["non_claims"]}
    missing_projected = sorted(required_non_claims - projected_non_claims)
    if missing_projected:
        errors.append(f"bounded query lost public-boundary non-claims: {missing_projected}")
    return errors


def prior_art_errors(prior_art: str) -> list[str]:
    """Keep bibliography navigation subordinate to exact claim evidence."""
    required = (
        "python3 scripts/query_corpus.py --route trace_prior_art",
        "python3 scripts/query_corpus.py --claim <claim_id>",
        "remaining-open links",
        "is an evidence statement, not a novelty",
        "Failure to identify a matching source is\nnot evidence of novelty",
        "Lean source checked by the pinned Lean kernel remains\nproof authority",
    )
    return [
        f"prior-art map lost claim-faithful comparison boundary: {phrase}"
        for phrase in required
        if phrase not in prior_art
    ]


def related_problem_errors(related: str) -> list[str]:
    """Reject collapse between catalogue status and local mathematical effect."""
    required = (
        "external catalogue status and the local release status are separate facts",
        "--open remaining_open.erdos_249_irrationality",
        "--open remaining_open.universal_257_all_infinite_supports",
        "--claim prime_support_irrationality",
        "--claim sigma_transcendence",
        "The first two packets are `open`; the latter two are `cited only`",
        "records an `advances_open_target` edge",
        "untouched analogy",
    )
    return [
        f"related-problem map lost typed relation boundary: {phrase}"
        for phrase in required
        if phrase not in related
    ]


def main() -> int:
    """Assert that every first-contact surface preserves the public membrane."""
    agents = read("AGENTS.md")
    scope = read("SCOPE.md")
    readme = read("README.md")
    claims = json.loads(read("docs/claims.json"))
    methodology = json.loads(read("docs/methodology.json"))
    prior_art = read("docs/PRIOR_ART.md")
    related = read("docs/RELATED_PROBLEMS.md")
    summary = summary_packet()
    assert not boundary_errors(agents, scope, readme, claims, methodology, summary)
    assert not prior_art_errors(prior_art)
    assert not related_problem_errors(related)

    missing_agent_rule = agents.replace(
        "never infer unpublished results or private machinery", "", 1
    )
    assert any(
        "agent entry lost public-boundary phrase" in error
        for error in boundary_errors(
            missing_agent_rule, scope, readme, claims, methodology, summary
        )
    )
    missing_projection = deepcopy(summary)
    missing_projection["non_claims"] = [
        row for row in summary["non_claims"] if row["id"] != "not_hidden_proof_body_authority"
    ]
    assert any(
        "bounded query lost public-boundary non-claims" in error
        for error in boundary_errors(
            agents, scope, readme, claims, methodology, missing_projection
        )
    )
    novelty_from_absence = prior_art.replace(
        "Failure to identify a matching source is\nnot evidence of novelty.",
        "Failure to identify a matching source establishes novelty.",
        1,
    )
    assert any(
        "prior-art map lost claim-faithful comparison boundary" in error
        for error in prior_art_errors(novelty_from_absence)
    )
    missing_claim_route = prior_art.replace(
        "python3 scripts/query_corpus.py --claim <claim_id>", "", 1
    )
    assert any(
        "prior-art map lost claim-faithful comparison boundary" in error
        for error in prior_art_errors(missing_claim_route)
    )
    collapsed_relation = related.replace(
        "The first two packets are `open`; the latter two are `cited only`.",
        "Every related solved problem is progress on the open targets.",
        1,
    )
    assert any(
        "related-problem map lost typed relation boundary" in error
        for error in related_problem_errors(collapsed_relation)
    )
    missing_open_handle = related.replace(
        "--open remaining_open.universal_257_all_infinite_supports", "", 1
    )
    assert any(
        "related-problem map lost typed relation boundary" in error
        for error in related_problem_errors(missing_open_handle)
    )

    print(
        "test_public_artifact_boundary: first-contact surfaces reject "
        "private or unpublished proof authority and novelty inference; "
        "6 negative fixtures rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
