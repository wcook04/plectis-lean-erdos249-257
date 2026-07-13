#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused tests for the bounded public corpus query surface."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "query_corpus.py"


def query(*args: str) -> dict[str, object]:
    completed = subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return json.loads(completed.stdout)


def run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )


def main() -> int:
    summary = query()
    assert summary["kind"] == "corpus_summary"
    assert summary["scale"]["module_count"] == 539

    claim = query("--claim", "denominator_exclusion")
    assert claim["claim"]["status"] == "unconditional progress"
    assert claim["remaining_open_propositions"][0]["id"] == "remaining_open.erdos_249_irrationality"

    declaration = query(
        "--declaration",
        "tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053",
    )
    assert declaration["match_count"] == 1
    assert declaration["matches"][0]["claim_ids"] == ["denominator_exclusion"]

    module_run = run("--module", "Erdos249257/CertificateKernel.lean")
    assert module_run.returncode == 0
    assert len(module_run.stdout.encode("utf-8")) <= 64_000
    module = json.loads(module_run.stdout)
    assert module["module"]["declaration_count"] > 400
    assert any(row["id"] == "eb_full_support" for row in module["attached_claims"])
    assert len(module["declaration_preview"]) == 20
    assert module["declaration_preview_receipt"]["omitted"] > 0
    assert "declaration_kind" in module["declaration_preview"][0]

    search = query("--search", " denominator_exclusion ", "--limit", "5")
    assert search["match_count"] >= 1
    assert search["results"][0]["kind"] == "claim"
    assert search["results"][0]["id"] == "denominator_exclusion"
    assert len(search["results"]) <= 5

    declaration_search = query("--search", "totientTail", "--limit", "1")
    assert declaration_search["results"][0]["kind"] == "declaration"
    assert declaration_search["results"][0]["declaration_kind"] in {
        "abbrev", "class", "def", "example", "instance", "lemma", "structure", "theorem"
    }

    route = query("--route", "instant_orientation")
    assert route["route"]["read"][0] == "docs/orientation.json"

    unknown = run("--claim", "does_not_exist")
    assert unknown.returncode == 2
    assert "unknown claim id" in unknown.stderr

    invalid_limit = run("--search", "totient", "--limit", "101")
    assert invalid_limit.returncode == 2
    assert "--limit must be between 1 and 100" in invalid_limit.stderr

    print("test_query_corpus: bounded summary, typed lookup, search, ranking, and error paths passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
