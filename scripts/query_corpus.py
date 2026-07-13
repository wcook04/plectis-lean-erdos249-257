#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Query the public mathematical corpus without loading its exhaustive files.

This is a read-only navigation projection. It does not elaborate Lean and does
not acquire proof authority. Run from any directory; output is JSON by default.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent


def load(rel: str) -> dict[str, Any]:
    return json.loads((ROOT / rel).read_text(encoding="utf-8"))


def claim_packet(claim_id: str) -> dict[str, Any]:
    claims = load("docs/claims.json")
    claim = next((row for row in claims["claims"] if row["id"] == claim_id), None)
    if claim is None:
        raise KeyError(f"unknown claim id: {claim_id}")
    edges = claims["machine_readable_paper"]["argument_graph"]["edges"]
    open_ids = set(claim.get("remaining_open_proposition_ids", []))
    return {
        "kind": "claim",
        "authority_posture": "navigation_projection_not_proof_authority",
        "claim": claim,
        "incoming_edges": [row for row in edges if row["to"] == claim_id],
        "outgoing_edges": [row for row in edges if row["from"] == claim_id],
        "remaining_open_propositions": [
            row for row in claims["remaining_open_propositions"] if row["id"] in open_ids
        ],
        "paper": {
            "source": claims["machine_readable_paper"]["paper"]["source"],
            "rendered": claims["machine_readable_paper"]["paper"]["rendered"],
            "label": claim.get("paper_label"),
        },
        "validation": "python3 scripts/check_release.py",
    }


def declaration_packet(name: str) -> dict[str, Any]:
    atlas = load("docs/declaration_atlas.json")
    matches = [row for row in atlas["declarations"] if row["name"] == name]
    if not matches:
        raise KeyError(f"unknown declaration name: {name}")
    return {
        "kind": "declaration",
        "authority_posture": "atlas_navigation_projection_not_proof_authority",
        "matches": matches,
        "match_count": len(matches),
        "validation": "python3 scripts/build_declaration_atlas.py --check",
    }


def module_packet(handle: str) -> dict[str, Any]:
    atlas = load("docs/declaration_atlas.json")
    claims = load("docs/claims.json")
    normalized = handle.replace(".", "/") + ".lean" if "/" not in handle else handle
    normalized = normalized.removeprefix("./")
    module = next(
        (
            row
            for row in atlas["modules"]
            if handle in (row["id"], row["path"]) or normalized == row["path"]
        ),
        None,
    )
    if module is None:
        raise KeyError(f"unknown module handle: {handle}")
    declarations = [
        row for row in atlas["declarations"] if row["module"] == module["path"]
    ]
    attached_claim_ids = sorted(
        {
            claim_id
            for row in declarations
            for claim_id in row.get("claim_ids", [])
        }
    )
    claim_rows = [row for row in claims["claims"] if row["id"] in attached_claim_ids]
    return {
        "kind": "module",
        "authority_posture": "atlas_navigation_projection_not_proof_authority",
        "module": module,
        "attached_claims": claim_rows,
        "declarations": declarations,
        "validation": "python3 scripts/build_declaration_atlas.py --check",
    }


def route_packet(route_id: str) -> dict[str, Any]:
    orientation = load("docs/orientation.json")
    route = next((row for row in orientation["reading_routes"] if row["id"] == route_id), None)
    if route is None:
        raise KeyError(f"unknown route id: {route_id}")
    return {
        "kind": "reading_route",
        "authority_posture": orientation["authority_posture"],
        "route": route,
        "proof_authority": orientation["proof_authority"],
    }


def summary_packet() -> dict[str, Any]:
    orientation = load("docs/orientation.json")
    return {
        "kind": "corpus_summary",
        **orientation,
    }


def render_card(packet: dict[str, Any]) -> str:
    kind = packet["kind"]
    if kind == "claim":
        claim = packet["claim"]
        decls = ", ".join(row["name"] for row in claim["declarations"]) or "none"
        return f"claim {claim['id']} | {claim['status']} | paper={claim.get('paper_label')} | declarations={decls}"
    if kind == "declaration":
        return "\n".join(
            f"declaration {row['name']} | {row['kind']} | {row['module']}:{row['line']} | claims={','.join(row['claim_ids']) or 'none'}"
            for row in packet["matches"]
        )
    if kind == "module":
        module = packet["module"]
        return (
            f"module {module['id']} | {module['path']} | declarations={module['declaration_count']} "
            f"| imports={len(module['imports'])} | claims={len(packet['attached_claims'])}"
        )
    if kind == "reading_route":
        route = packet["route"]
        return f"route {route['id']} | {route['intent']} | {' -> '.join(route['read'])}"
    scale = packet["scale"]
    return (
        f"corpus {packet['release']['tag']} | modules={scale['module_count']} "
        f"| declarations={scale['declaration_count']} | principal_claims={len(packet['principal_claims'])} "
        f"| open={len(packet['remaining_open_propositions'])}"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--claim", metavar="ID")
    group.add_argument("--declaration", metavar="NAME")
    group.add_argument("--module", metavar="PATH_OR_ID")
    group.add_argument("--route", metavar="ID")
    parser.add_argument("--format", choices=("json", "card"), default="json")
    args = parser.parse_args()
    try:
        if args.claim:
            packet = claim_packet(args.claim)
        elif args.declaration:
            packet = declaration_packet(args.declaration)
        elif args.module:
            packet = module_packet(args.module)
        elif args.route:
            packet = route_packet(args.route)
        else:
            packet = summary_packet()
    except (KeyError, json.JSONDecodeError, OSError) as exc:
        print(f"query_corpus: {exc}", file=sys.stderr)
        return 2
    if args.format == "card":
        print(render_card(packet))
    else:
        print(json.dumps(packet, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
