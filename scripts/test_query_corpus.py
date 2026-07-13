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
    assert claim["argument_neighbourhood"]["outgoing"][0]["neighbour"]["id"] == "erdos_249"
    assert "partial progress" in claim["argument_neighbourhood"]["outgoing"][0]["relation_meaning"]

    reduction = query("--claim", "certificate_reduction")
    incoming_ids = {
        row["neighbour"]["id"] for row in reduction["argument_neighbourhood"]["incoming"]
    }
    assert "certificate_completeness" in incoming_ids
    assert "first_harmonic_certificate_interface" in incoming_ids
    assert reduction["argument_neighbourhood"]["outgoing"][0]["neighbour"]["status"] == "open"

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
    assert module["module"]["role"] == "Assembled theorem kernel and headline interfaces"
    neighbourhood = module["dependency_neighbourhood"]
    assert neighbourhood["receipt"]["imports_total"] == 10
    assert neighbourhood["receipt"]["importers_total"] == 7
    assert len(neighbourhood["importers"]) == 7
    assert neighbourhood["receipt"]["importers_omitted"] == 0

    certificate_hub = query("--module", "Erdos249257.DiagonalPincerCertificates")
    hub_neighbourhood = certificate_hub["dependency_neighbourhood"]
    assert hub_neighbourhood["receipt"]["importers_total"] == 481
    assert len(hub_neighbourhood["importers"]) == 20
    assert hub_neighbourhood["receipt"]["importers_omitted"] == 461

    root = query("--module", "Erdos249257.lean", "--limit", "3")
    assert root["module"]["role"] == "Supported package root import"
    assert root["dependency_neighbourhood"]["receipt"]["importers_total"] == 0
    assert root["dependency_neighbourhood"]["receipt"]["imports_total"] > 3

    leaf = query("--module", "Erdos249257.GeneratedCertificates.b10_L6_A11", "--limit", "3")
    assert leaf["module"]["role"] == "Generated finite certificate shard"
    assert leaf["dependency_neighbourhood"]["imports"][0]["id"] == "Erdos249257.CertificateKernel"
    assert any(
        row["id"] == "Erdos249257.GeneratedCertificates"
        for row in leaf["dependency_neighbourhood"]["importers"]
    )

    aliases = json.loads((ROOT / "paper" / "module-aliases.json").read_text(encoding="utf-8"))
    assert aliases["alias_count"] == len(aliases["aliases"])
    assert len({row["sigil"] for row in aliases["aliases"]}) == aliases["alias_count"]
    for row in aliases["aliases"]:
        resolved = query("--module", row["sigil"], "--limit", "1")
        assert resolved["module"]["path"] == row["path"]
        assert resolved["paper_sigil"] == row["sigil"]

    sigil_search = query("--search", "CerKer", "--limit", "1")
    assert sigil_search["results"][0]["kind"] == "module"
    assert sigil_search["results"][0]["path"] == "Erdos249257/CertificateKernel.lean"

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

    print("test_query_corpus: bounded lookup, sigil round trips, search, ranking, and errors passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
