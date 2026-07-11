#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Pure validation and Markdown rendering for the public methodology contract."""

from __future__ import annotations

import json
import re
from copy import deepcopy
from typing import Any


IMPLEMENTED_GUARDS = {
    "release.methodology_schema_and_references",
    "release.claim_transition_requirements",
    "release.methodology_projection_matches_source",
    "release.methodology_routes_exist",
    "release.proof_trust",
}

REMAINING_OPEN_EFFECTS = {
    "proves",
    "narrows",
    "decomposes",
    "re_expresses",
    "constrains",
}


def _rule_rows(methodology: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        *methodology.get("method_axioms", []),
        *methodology.get("principles", []),
        *methodology.get("anti_principles", []),
        *methodology.get("transition_contracts", []),
    ]


def validate_contract(claims: dict[str, Any], methodology: dict[str, Any]) -> list[str]:
    """Return every structural contract error without mutating either input."""
    errors: list[str] = []

    if methodology.get("schema") != "erdos249257-methodology/1":
        errors.append("unsupported methodology schema")
    if claims.get("schema") != "erdos249257-claims/3":
        errors.append("claims must use erdos249257-claims/3")

    evidence_classes = set(methodology.get("evidence_classes", {}))
    mathematical_objects = {
        row.get("id") for row in methodology.get("ontology", {}).get("mathematical_objects", [])
    }
    repository_objects = {
        row.get("id") for row in methodology.get("ontology", {}).get("repository_objects", [])
    }
    object_ids = mathematical_objects | repository_objects
    change_types = set(methodology.get("change_types", []))
    claim_statuses = set(claims.get("status_taxonomy", {}))
    argument_relations = set(
        claims.get("machine_readable_paper", {})
        .get("argument_graph", {})
        .get("edge_semantics", {})
    )

    rules = _rule_rows(methodology)
    rule_ids = [row.get("id") for row in rules]
    if any(not isinstance(rule_id, str) or not rule_id for rule_id in rule_ids):
        errors.append("every methodology rule and transition needs a non-empty id")
    if len(rule_ids) != len(set(rule_ids)):
        errors.append("methodology rule and transition ids must be unique")

    for row in rules:
        rule_id = row.get("id", "<missing>")
        for field in ("title", "checked_by"):
            if not row.get(field):
                errors.append(f"{rule_id}: missing {field}")
        if rule_id.startswith(("method_axiom.", "principle.", "anti_principle.")):
            for field in ("statement", "evidence_classes", "applies_to", "scope_limit"):
                if not row.get(field):
                    errors.append(f"{rule_id}: missing {field}")
            unknown_evidence = set(row.get("evidence_classes", [])) - evidence_classes
            if unknown_evidence:
                errors.append(f"{rule_id}: unknown evidence classes {sorted(unknown_evidence)}")
            for reference in row.get("applies_to", []):
                kind, separator, value = str(reference).partition(":")
                if not separator:
                    errors.append(f"{rule_id}: malformed applies_to reference {reference!r}")
                elif kind == "object" and value not in object_ids:
                    errors.append(f"{rule_id}: unknown object {value!r}")
                elif kind == "change_type" and value not in change_types:
                    errors.append(f"{rule_id}: unknown change type {value!r}")
                elif kind == "claim_status" and value not in claim_statuses:
                    errors.append(f"{rule_id}: unknown claim status {value!r}")
                elif kind == "argument_relation" and value not in argument_relations:
                    errors.append(f"{rule_id}: unknown argument relation {value!r}")
                elif kind not in {"object", "change_type", "claim_status", "argument_relation"}:
                    errors.append(f"{rule_id}: unknown applies_to reference kind {kind!r}")
        elif rule_id.startswith("transition."):
            for field in ("trigger", "required_evidence_classes", "requirements"):
                if not row.get(field):
                    errors.append(f"{rule_id}: missing {field}")
            unknown_evidence = set(row.get("required_evidence_classes", [])) - evidence_classes
            if unknown_evidence:
                errors.append(f"{rule_id}: unknown evidence classes {sorted(unknown_evidence)}")
        else:
            errors.append(f"{rule_id}: id must use a literal methodology prefix")

        unknown_guards = set(row.get("checked_by", [])) - IMPLEMENTED_GUARDS
        if unknown_guards:
            errors.append(f"{rule_id}: unknown validation guards {sorted(unknown_guards)}")

    guards = methodology.get("validation_guards", [])
    guard_ids = [guard.get("id") for guard in guards]
    if set(guard_ids) != IMPLEMENTED_GUARDS or len(guard_ids) != len(set(guard_ids)):
        errors.append("validation_guards must name each implemented release guard exactly once")
    reverse_bindings = {
        guard_id: sorted(
            row.get("id") for row in rules if guard_id in set(row.get("checked_by", []))
        )
        for guard_id in IMPLEMENTED_GUARDS
    }
    for guard in guards:
        guard_id = guard.get("id")
        if not guard.get("description"):
            errors.append(f"{guard_id}: validation guard needs a description")
        if sorted(guard.get("serves", [])) != reverse_bindings.get(guard_id, []):
            errors.append(f"{guard_id}: serves must exactly reverse the rule checked_by bindings")

    claims_by_id = {claim.get("id"): claim for claim in claims.get("claims", [])}
    remaining_rows = claims.get("remaining_open_propositions", [])
    remaining_ids = [row.get("id") for row in remaining_rows]
    if len(remaining_ids) != len(set(remaining_ids)):
        errors.append("remaining_open_proposition ids must be unique")
    remaining_by_id = {row.get("id"): row for row in remaining_rows}
    for row in remaining_rows:
        row_id = row.get("id", "<missing>")
        target = claims_by_id.get(row.get("open_target_claim"))
        if target is None or target.get("status") != "open":
            errors.append(f"{row_id}: open_target_claim must name an open claim")
        if not row.get("statement"):
            errors.append(f"{row_id}: missing statement")

    for claim in claims.get("claims", []):
        claim_id = claim.get("id", "<missing>")
        remaining = claim.get("remaining_open_proposition_ids", [])
        unknown = set(remaining) - set(remaining_ids)
        if unknown:
            errors.append(f"{claim_id}: unknown remaining open propositions {sorted(unknown)}")
        if claim.get("status") == "conditional reduction" and not remaining:
            errors.append(f"{claim_id}: conditional reduction must name a remaining open proposition")
        bounded_domain = claim.get("bounded_domain")
        if claim.get("status") == "verified finite instance" and not bounded_domain:
            errors.append(f"{claim_id}: verified finite instance must state bounded_domain")
        if bounded_domain and claim.get("status") != "verified finite instance":
            errors.append(f"{claim_id}: bounded_domain is only valid for verified finite instance")

    edges = (
        claims.get("machine_readable_paper", {})
        .get("argument_graph", {})
        .get("edges", [])
    )
    for edge in edges:
        if edge.get("relation") != "advances_open_target":
            continue
        source = edge.get("from", "<missing>")
        target_id = edge.get("to")
        target = claims_by_id.get(target_id)
        effect = edge.get("remaining_open_effect")
        if target is None or target.get("status") != "open":
            errors.append(f"argument edge {source}->{target_id}: target must be an open claim")
        if not isinstance(effect, dict):
            errors.append(f"argument edge {source}->{target_id}: missing remaining_open_effect")
            continue
        remaining_id = effect.get("remaining_open_proposition_id")
        remaining_row = remaining_by_id.get(remaining_id)
        if remaining_row is None:
            errors.append(f"argument edge {source}->{target_id}: unknown remaining open proposition")
        elif remaining_row.get("open_target_claim") != target_id:
            errors.append(f"argument edge {source}->{target_id}: remaining open proposition belongs to another target")
        if effect.get("operation") not in REMAINING_OPEN_EFFECTS:
            errors.append(f"argument edge {source}->{target_id}: invalid remaining-open operation")
        if not effect.get("statement"):
            errors.append(f"argument edge {source}->{target_id}: remaining-open effect needs a statement")

    return errors


def render_markdown(methodology: dict[str, Any]) -> str:
    """Render the conventional root document from the machine-readable owner."""
    lines = [
        "<!-- SPDX-FileCopyrightText: 2026 Will Cook -->",
        "<!-- SPDX-License-Identifier: Apache-2.0 -->",
        "<!-- Generated by scripts/build_methodology.py from docs/methodology.json. Do not edit directly. -->",
        "",
        f"# {methodology['title']}",
        "",
        methodology["scope"],
        "",
        "## Short form",
        "",
    ]
    lines.extend(f"- {statement}" for statement in methodology["human_capsule"])

    lines.extend(["", "## Evidence classes", ""])
    for evidence_id, evidence in methodology["evidence_classes"].items():
        lines.extend(
            [
                f"### `{evidence_id}`",
                "",
                f"Decides: {evidence['decides']}",
                "",
                f"Does not decide: {evidence['does_not_decide']}",
                "",
            ]
        )

    lines.extend(["## Mathematical and repository objects", ""])
    for heading, key in (
        ("Mathematical objects", "mathematical_objects"),
        ("Repository objects", "repository_objects"),
    ):
        lines.extend([f"### {heading}", "", "| Identifier | Literal meaning |", "|---|---|"])
        for row in methodology["ontology"][key]:
            lines.append(f"| `{row['id']}` | {row['definition']} |")
        lines.append("")

    def cycle(title: str, key: str) -> None:
        lines.extend([f"### {title}", "", " → ".join(f"`{item}`" for item in methodology[key]), ""])

    lines.extend(["## Ordered cycles", ""])
    cycle("Mathematical research cycle", "mathematical_research_cycle")
    cycle("Public claim cycle", "public_claim_cycle")

    def rule_table(title: str, key: str, include_scope_limit: bool = False) -> None:
        if include_scope_limit:
            lines.extend([f"## {title}", "", "| Identifier and literal name | Rule | What it does not establish |", "|---|---|---|"])
        else:
            lines.extend([f"## {title}", "", "| Identifier and literal name | Rule |", "|---|---|"])
        for row in methodology[key]:
            if include_scope_limit:
                lines.append(
                    f"| `{row['id']}` — {row['title']} | {row['statement']} | {row['scope_limit']} |"
                )
            else:
                lines.append(f"| `{row['id']}` — {row['title']} | {row['statement']} |")
        lines.append("")

    rule_table("Method axioms", "method_axioms", include_scope_limit=True)
    rule_table("Principles", "principles")
    rule_table("Anti-principles", "anti_principles")
    lines.extend(
        [
            "The machine-readable source retains the evidence class, applicability bindings, validation guards, and scope limit for every rule.",
            "",
        ]
    )

    lines.extend(["## Claim-transition requirements", ""])
    for transition in methodology["transition_contracts"]:
        lines.extend(
            [
                f"### `{transition['id']}` — {transition['title']}",
                "",
                f"Trigger: {transition['trigger']}",
                "",
                "Required evidence: " + ", ".join(f"`{item}`" for item in transition["required_evidence_classes"]),
                "",
            ]
        )
        lines.extend(f"- {requirement}" for requirement in transition["requirements"])
        lines.append("")

    lines.extend(
        [
            "## Authority and maintenance",
            "",
            "Lean source checked by the pinned Lean kernel remains proof authority. `docs/claims.json` remains the owner of release identity, claim status, remaining open propositions, and argument relationships. `docs/methodology.json` owns the rules on this page. The authored paper remains the owner of mathematical exposition.",
            "",
            "`METHODOLOGY.md` is generated from `docs/methodology.json`; run `python3 scripts/build_methodology.py` after changing the source. `python3 scripts/check_release.py` checks the source schema, typed claim-transition requirements, exact Markdown projection, descriptor registration, and entry routes.",
            "",
        ]
    )
    return "\n".join(lines)


def mutation_fixture_errors(claims: dict[str, Any], methodology: dict[str, Any]) -> dict[str, list[str]]:
    """Return validator results for the four public failure shapes used by tests."""
    fixtures: dict[str, tuple[dict[str, Any], dict[str, Any]]] = {}

    missing_remaining = deepcopy(claims)
    conditional = next(row for row in missing_remaining["claims"] if row["status"] == "conditional reduction")
    conditional.pop("remaining_open_proposition_ids", None)
    fixtures["conditional_reduction_without_remaining_open_proposition"] = (missing_remaining, methodology)

    finite_promoted = deepcopy(claims)
    finite = next(row for row in finite_promoted["claims"] if row["status"] == "verified finite instance")
    finite["status"] = "open"
    fixtures["finite_result_changed_to_open_status"] = (finite_promoted, methodology)

    edge_without_effect = deepcopy(claims)
    edge = next(
        row
        for row in edge_without_effect["machine_readable_paper"]["argument_graph"]["edges"]
        if row["relation"] == "advances_open_target"
    )
    edge.pop("remaining_open_effect", None)
    fixtures["open_target_edge_without_stated_effect"] = (edge_without_effect, methodology)

    unknown_guard = deepcopy(methodology)
    unknown_guard["method_axioms"][0]["checked_by"] = ["release.not_implemented"]
    fixtures["methodology_rule_without_implemented_guard"] = (claims, unknown_guard)

    return {
        fixture_id: validate_contract(fixture_claims, fixture_methodology)
        for fixture_id, (fixture_claims, fixture_methodology) in fixtures.items()
    }
