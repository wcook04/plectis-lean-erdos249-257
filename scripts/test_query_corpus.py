#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused tests for the bounded public corpus query surface."""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

from query_corpus import (
    artifact_inventory,
    artifact_packet,
    claim_packet,
    declaration_packet,
    load,
    open_proposition_packet,
    paper_anchor_inventory,
    paper_anchor_packet,
    route_packet,
    source_coordinate_packet,
)

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
    assert reduction["paper"]["source_ref"] == "paper/erdos249-257-exposition.tex:568"

    claims_document = json.loads((ROOT / "docs" / "claims.json").read_text(encoding="utf-8"))
    labelled_claims = [row for row in claims_document["claims"] if row.get("paper_label")]
    for row in labelled_claims:
        packet = query("--claim", row["id"])
        paper = packet["paper"]
        source_line = (ROOT / paper["source"]).read_text(encoding="utf-8").splitlines()[paper["line"] - 1]
        assert re.search(rf"\\label\{{{re.escape(row['paper_label'])}\}}", source_line)
    companion = query("--claim", "transport_curvature_reductions")
    assert companion["paper"]["source"] == "paper/erdos249-transport-curvature.tex"
    assert companion["paper"]["rendered"] == "erdos249-transport-curvature.pdf"
    assert query("--claim", "erdos_249")["paper"] is None

    paper_label = query("--paper-label", "res:farey")
    assert paper_label["kind"] == "paper_label"
    assert paper_label["paper"]["source_ref"] == "paper/erdos249-257-exposition.tex:457"
    assert paper_label["attached_claims"][0]["id"] == "denominator_exclusion"
    assert paper_label["anchor_class"] == "registered_claim_anchor"
    assert any(
        row["source_ref"] == "Erdos249257/CertificateKernel.lean:18055"
        for row in paper_label["source_links"]
    )
    shared_paper_label = query("--paper-label", "res:full")
    assert shared_paper_label["attachment_receipt"]["claim_count"] == 2
    assert {row["id"] for row in shared_paper_label["attached_claims"]} == {
        "eb_constant",
        "eb_full_support",
    }
    companion_paper_label = query("--paper-label", "sec:curvature")
    assert companion_paper_label["paper"]["source"] == (
        "paper/erdos249-transport-curvature.tex"
    )
    local_result = query("--paper-anchor", "res:lift")
    assert local_result["anchor_class"] == "authored_formal_anchor_without_registered_claim"
    assert local_result["attachment_receipt"]["claim_count"] == 0
    assert local_result["source_links"][0]["declaration"] == (
        "tsum_primWeight_div_two_pow_sub_one_eq_totient_series"
    )
    unlabelled_result = query("--paper-anchor", "paper/erdos249-257-exposition.tex:227")
    assert unlabelled_result["paper"]["label"] is None
    assert unlabelled_result["anchor_class"] == (
        "authored_formal_anchor_without_registered_claim"
    )
    assert unlabelled_result["source_links"][0]["declaration"] == (
        "tsum_moebius_div_two_pow_sub_one_eq_half"
    )
    navigation_anchor = query("--paper-anchor", "sec:intro")
    assert navigation_anchor["anchor_class"] == "section_navigation_anchor"
    assert query("--paper-anchor", "app:index")["anchor_neighbourhood"]["next"] is None
    assert query("--paper-anchor", "sec:scope")["anchor_neighbourhood"]["previous"] is None
    unknown_paper_label = run("--paper-label", "prop:not-a-real-label")
    assert unknown_paper_label.returncode == 2
    assert "unknown paper label" in unknown_paper_label.stderr

    open_expectations = {
        "remaining_open.erdos_249_irrationality": ("erdos_249", 1),
        "remaining_open.unbounded_certificate_supply": ("erdos_249", 6),
        "remaining_open.universal_257_all_infinite_supports": ("universal_257", 5),
    }
    for open_id, (target, advancing_count) in open_expectations.items():
        open_packet = query("--open", open_id)
        assert open_packet["kind"] == "open_proposition"
        assert open_packet["status"] == "open"
        assert open_packet["open_target"]["id"] == target
        assert len(open_packet["advancing_claims"]) == advancing_count
        assert open_packet["paper_anchor"]["anchor_class"] == (
            "remaining_open_proposition_anchor"
        )
        reverse_open = query(
            "--paper-anchor", open_packet["paper_anchor"]["canonical_handle"]
        )
        assert [row["id"] for row in reverse_open["attached_open_propositions"]] == [
            open_id
        ]

    open_search = query("--search", "remaining_open.unbounded_certificate_supply", "--limit", "1")
    assert open_search["results"][0]["kind"] == "open_proposition"
    assert open_search["results"][0]["id"] == "remaining_open.unbounded_certificate_supply"

    declaration = query(
        "--declaration",
        "tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053",
    )
    assert declaration["match_count"] == 1
    assert declaration["matches"][0]["claim_ids"] == ["denominator_exclusion"]
    assert declaration["matches"][0]["source_ref"] == "Erdos249257/CertificateKernel.lean:18056"
    assert declaration["matches"][0]["source_url"].startswith(
        "https://github.com/wcook04/plectis-lean-erdos249-257/blob/v0.6.0/"
    )
    assert declaration["matches"][0]["attached_claims"][0]["paper"]["label"] == "res:farey"
    assert declaration["matches"][0]["paper_anchors"][0]["canonical_handle"] == "res:farey"

    reduction_declaration = query(
        "--declaration", "irrational_totient_series_of_certificate_supply"
    )["matches"][0]
    assert reduction_declaration["source_ref"] == (
        "Erdos249257/TotientTailPeriodKiller.lean:394"
    )
    assert reduction_declaration["paper_sigil"] == "TotTaiPerKil"
    assert reduction_declaration["module_role"] == "Tail-period certificate reduction"
    assert reduction_declaration["attached_claims"][0]["paper"]["source_ref"] == (
        "paper/erdos249-257-exposition.tex:568"
    )

    unlinked = query("--declaration", "totientTail_pos")["matches"][0]
    assert unlinked["attached_claims"] == []

    local_declaration = query(
        "--declaration", "tsum_primWeight_div_two_pow_sub_one_eq_totient_series"
    )["matches"][0]
    assert local_declaration["attached_claims"] == []
    assert local_declaration["paper_anchors"][0]["canonical_handle"] == "res:lift"

    source_coordinate = query(
        "--source", "Erdos249257/CertificateKernel.lean:18055"
    )
    assert source_coordinate["kind"] == "source_coordinate"
    assert source_coordinate["source"]["source_url"].endswith(
        "/Erdos249257/CertificateKernel.lean#L18055"
    )
    source_declaration = source_coordinate["nearby_declarations"][0]
    assert source_declaration["name"] == (
        "tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053"
    )
    assert source_declaration["attached_claims"][0]["id"] == "denominator_exclusion"
    assert source_declaration["paper_anchors"][0]["canonical_handle"] == "res:farey"
    nondeclaration_source = query("--source", "Erdos249257/CertificateKernel.lean:1")
    assert nondeclaration_source["source"]["line"] == 1
    assert nondeclaration_source["coordinate_receipt"]["line_exists"] is True
    assert nondeclaration_source["coordinate_receipt"]["nearest_after"] is not None

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

    anchor_search = query("--search", "positive lift", "--limit", "5")
    assert any(
        row["kind"] == "paper_anchor" and row["canonical_handle"] == "res:lift"
        for row in anchor_search["results"]
    )

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

    unknown_open = run("--open", "remaining_open.does_not_exist")
    assert unknown_open.returncode == 2
    assert "unknown remaining-open proposition id" in unknown_open.stderr

    unknown_source = run("--source", "Erdos249257/NotAModule.lean:1")
    assert unknown_source.returncode == 2
    assert "unknown Lean source module" in unknown_source.stderr

    invalid_source_line = run("--source", "Erdos249257/CertificateKernel.lean:999999")
    assert invalid_source_line.returncode == 2
    assert "exceeds" in invalid_source_line.stderr

    source_link_count = 0
    for anchor in paper_anchor_inventory():
        for link in anchor["source_links"]:
            source_link_count += 1
            packet = source_coordinate_packet(link["source_ref"], 20)
            assert packet["coordinate_receipt"]["line_exists"] is True
            names = {row["name"] for row in packet["nearby_declarations"]}
            if link["declaration"]:
                assert link["declaration"] in names
            reverse_anchors = {
                paper_anchor["canonical_handle"]
                for row in packet["nearby_declarations"]
                for paper_anchor in row["paper_anchors"]
            }
            assert anchor["canonical_handle"] in reverse_anchors
    assert source_link_count > 100

    descriptor = json.loads(
        (ROOT / "docs" / "corpus_descriptor.json").read_text(encoding="utf-8")
    )
    claims_identity = descriptor["identity"]["content"]["claims_document"]
    claims_artifact = query("--artifact", "docs/claims.json")
    assert claims_artifact["matches"][0]["artifact_id"] == "claims_document"
    assert claims_artifact["matches"][0]["content_digest"] == claims_identity["content_digest"]
    claims_by_digest = query("--artifact", claims_identity["content_digest"])
    assert claims_by_digest["matches"][0]["artifact_handle"] == "docs/claims.json"
    machine_paper_artifact = query(
        "--artifact", "docs/claims.json::machine_readable_paper"
    )
    assert machine_paper_artifact["matches"][0]["artifact_kind"] == "json_fragment"
    exposition_artifact = query("--artifact", "erdos249-257-exposition.pdf")
    assert exposition_artifact["matches"][0]["artifact_kind"] == (
        "authored_paper_rendered"
    )
    artifact_search = query("--search", claims_identity["content_digest"], "--limit", "1")
    assert artifact_search["results"][0]["kind"] == "artifact"

    unknown_artifact = run("--artifact", "sha256:" + "0" * 64)
    assert unknown_artifact.returncode == 2
    assert "unknown registered artifact" in unknown_artifact.stderr

    # Exhaustive populated-owner closure matrix. These assertions are derived
    # from the current owners, so corpus growth creates a failing orphan instead
    # of requiring a hand-maintained count or specimen list.
    closure_checks = 0
    for claim_row in claims_document["claims"]:
        claim_view = claim_packet(claim_row["id"])
        closure_checks += 1
        assert claim_view["claim"]["id"] == claim_row["id"]
        if claim_row.get("paper_label"):
            paper_view = paper_anchor_packet(claim_row["paper_label"])
            closure_checks += 1
            assert claim_row["id"] in {
                row["id"] for row in paper_view["attached_claims"]
            }
        for declaration_row in claim_row["declarations"]:
            declaration_view = declaration_packet(declaration_row["name"], 100)
            closure_checks += 1
            exact_rows = [
                row
                for row in declaration_view["matches"]
                if row["module"] == declaration_row["module"]
                and row["line"] == declaration_row["line"]
            ]
            assert len(exact_rows) == 1
            assert claim_row["id"] in exact_rows[0]["claim_ids"]

    for open_row in claims_document["remaining_open_propositions"]:
        open_view = open_proposition_packet(open_row["id"])
        closure_checks += 1
        assert open_view["paper_anchor"] is not None
        assert open_view["paper_anchor"]["anchor_class"] == (
            "remaining_open_proposition_anchor"
        )

    for anchor_row in paper_anchor_inventory():
        anchor_view = paper_anchor_packet(anchor_row["canonical_handle"])
        closure_checks += 1
        assert anchor_view["anchor_class"] == anchor_row["anchor_class"]

    for artifact_row in artifact_inventory():
        for handle in (artifact_row["artifact_handle"], artifact_row["content_digest"]):
            artifact_view = artifact_packet(handle)
            closure_checks += 1
            assert artifact_row["artifact_handle"] in {
                row["artifact_handle"] for row in artifact_view["matches"]
            }

    orientation_document = load("docs/orientation.json")
    for route_row in orientation_document["reading_routes"]:
        route_view = route_packet(route_row["id"])
        closure_checks += 1
        assert route_view["route"]["id"] == route_row["id"]

    assert closure_checks > 150

    invalid_limit = run("--search", "totient", "--limit", "101")
    assert invalid_limit.returncode == 2
    assert "--limit must be between 1 and 100" in invalid_limit.stderr

    print(
        "test_query_corpus: bounded lookup and exhaustive populated-owner closure "
        f"passed ({closure_checks} closure checks)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
