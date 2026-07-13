#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep public navigation from treating unpublished work as corpus authority."""

from __future__ import annotations

import json
import subprocess
import sys
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


def main() -> int:
    """Assert that every first-contact surface preserves the public membrane."""
    agents = read("AGENTS.md")
    assert "not an entrypoint into any private development system" in agents
    assert "Work only from the files\nin this repository" in agents
    assert "never infer unpublished results or private machinery" in agents

    scope = read("SCOPE.md")
    assert "Unreleased work, private repositories" in scope
    assert "not part of\nthe public proof artefact" in scope

    readme = read("README.md")
    assert "do not infer results from private or unreleased work" in readme

    claims = json.loads(read("docs/claims.json"))
    non_claims = {row["id"] for row in claims["non_claims"]}
    assert {
        "not_private_root_equivalence",
        "not_hidden_proof_body_authority",
        "not_provider_proof_authority",
    } <= non_claims

    methodology = json.loads(read("docs/methodology.json"))
    anti_principles = {row["id"]: row["statement"] for row in methodology["anti_principles"]}
    assert "anti_principle.do_not_treat_graph_model_or_private_work_as_proof" in anti_principles
    assert "private proof sketch is not public proof authority" in anti_principles[
        "anti_principle.do_not_treat_graph_model_or_private_work_as_proof"
    ]

    summary = summary_packet()
    projected_non_claims = {row["id"] for row in summary["non_claims"]}
    assert non_claims <= projected_non_claims
    assert "not_private_root_equivalence" in projected_non_claims
    assert "not_hidden_proof_body_authority" in projected_non_claims

    print(
        "test_public_artifact_boundary: first-contact surfaces reject "
        "private or unpublished proof authority"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
