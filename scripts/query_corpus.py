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
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_LIMIT = 20
MAX_LIMIT = 100
OUTPUT_BUDGET_BYTES = 64_000


def load(rel: str) -> dict[str, Any]:
    return json.loads((ROOT / rel).read_text(encoding="utf-8"))


def compact_claim(claim: dict[str, Any]) -> dict[str, Any]:
    return {
        "id": claim["id"],
        "label": claim["label"],
        "status": claim["status"],
        "paper_label": claim.get("paper_label"),
    }


def paper_label_index() -> dict[str, dict[str, Any]]:
    index: dict[str, dict[str, Any]] = {}
    for path in sorted((ROOT / "paper").glob("erdos*.tex")):
        relative = str(path.relative_to(ROOT))
        for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            for label in re.findall(r"\\label\{([^}]+)\}", line):
                if label in index:
                    raise ValueError(
                        f"duplicate paper label {label!r}: "
                        f"{index[label]['source_ref']} and {relative}:{line_number}"
                    )
                index[label] = {
                    "label": label,
                    "source": relative,
                    "line": line_number,
                    "source_ref": f"{relative}:{line_number}",
                    "rendered": f"{path.stem}.pdf",
                }
    return index


def paper_coordinate(label: str | None, index: dict[str, dict[str, Any]]) -> dict[str, Any] | None:
    if label is None:
        return None
    coordinate = index.get(label)
    if coordinate is None:
        raise ValueError(f"unknown paper label: {label}")
    return coordinate


def claim_packet(claim_id: str) -> dict[str, Any]:
    claims = load("docs/claims.json")
    claim_index = {row["id"]: row for row in claims["claims"]}
    claim = claim_index.get(claim_id)
    if claim is None:
        raise KeyError(f"unknown claim id: {claim_id}")
    graph = claims["machine_readable_paper"]["argument_graph"]
    label_index = paper_label_index()
    edges = graph["edges"]
    incoming = [row for row in edges if row["to"] == claim_id]
    outgoing = [row for row in edges if row["from"] == claim_id]

    def resolved_edge(edge: dict[str, Any], neighbour_key: str) -> dict[str, Any]:
        row = {
            "relation": edge["relation"],
            "relation_meaning": graph["edge_semantics"][edge["relation"]],
            "neighbour": compact_claim(claim_index[edge[neighbour_key]]),
        }
        if "remaining_open_effect" in edge:
            row["remaining_open_effect"] = edge["remaining_open_effect"]
        return row

    open_ids = set(claim.get("remaining_open_proposition_ids", []))
    return {
        "kind": "claim",
        "authority_posture": "navigation_projection_not_proof_authority",
        "claim": claim,
        "incoming_edges": incoming,
        "outgoing_edges": outgoing,
        "argument_neighbourhood": {
            "incoming": [resolved_edge(row, "from") for row in incoming],
            "outgoing": [resolved_edge(row, "to") for row in outgoing],
            "exhaustive": "docs/claims.json::machine_readable_paper.argument_graph",
            "follow": "python3 scripts/query_corpus.py --claim <neighbour_id>",
        },
        "remaining_open_propositions": [
            row for row in claims["remaining_open_propositions"] if row["id"] in open_ids
        ],
        "paper": paper_coordinate(claim.get("paper_label"), label_index),
        "validation": "python3 scripts/check_release.py",
    }


def open_proposition_packet(open_id: str) -> dict[str, Any]:
    claims = load("docs/claims.json")
    proposition = next(
        (row for row in claims["remaining_open_propositions"] if row["id"] == open_id), None
    )
    if proposition is None:
        raise KeyError(f"unknown remaining-open proposition id: {open_id}")
    claim_index = {row["id"]: row for row in claims["claims"]}
    linked_claims = [
        compact_claim(row)
        for row in claims["claims"]
        if open_id in row.get("remaining_open_proposition_ids", [])
        and row["id"] != proposition["open_target_claim"]
    ]
    advancing_claims = []
    for edge in claims["machine_readable_paper"]["argument_graph"]["edges"]:
        effect = edge.get("remaining_open_effect")
        if not effect or effect.get("remaining_open_proposition_id") != open_id:
            continue
        advancing_claims.append(
            {
                "claim": compact_claim(claim_index[edge["from"]]),
                "relation": edge["relation"],
                "operation": effect["operation"],
                "effect": effect["statement"],
            }
        )
    return {
        "kind": "open_proposition",
        "authority_posture": "authored_open_boundary_navigation_not_proof_authority",
        "open_proposition": proposition,
        "status": "open",
        "open_target": compact_claim(claim_index[proposition["open_target_claim"]]),
        "linked_claims": linked_claims,
        "advancing_claims": advancing_claims,
        "follow": "python3 scripts/query_corpus.py --claim <claim_id>",
        "source": "docs/claims.json::remaining_open_propositions",
        "validation": "python3 scripts/check_release.py",
    }


def declaration_packet(name: str, limit: int) -> dict[str, Any]:
    atlas = load("docs/declaration_atlas.json")
    claims = load("docs/claims.json")
    aliases = load("paper/module-aliases.json")["aliases"]
    matches = [row for row in atlas["declarations"] if row["name"] == name]
    if not matches:
        raise KeyError(f"unknown declaration name: {name}")
    claim_index = {row["id"]: row for row in claims["claims"]}
    roles = module_roles(claims)
    label_index = paper_label_index()
    sigil_by_path = {row["path"]: row["sigil"] for row in aliases}
    repository = claims["release"]["repository"].rstrip("/")
    tag = claims["release"]["tag"]
    decorated = []
    for match in matches[:limit]:
        attached_claims = []
        for claim_id in match.get("claim_ids", []):
            claim = claim_index[claim_id]
            attached_claims.append(
                {
                    **compact_claim(claim),
                    "paper": paper_coordinate(claim.get("paper_label"), label_index),
                }
            )
        decorated.append(
            {
                **match,
                "source_ref": f"{match['module']}:{match['line']}",
                "source_url": f"{repository}/blob/{tag}/{match['module']}#L{match['line']}",
                "paper_sigil": sigil_by_path.get(match["module"]),
                "module_role": roles.get(
                    match["module"].removesuffix(".lean").replace("/", "."),
                    "Unclassified module",
                ),
                "attached_claims": attached_claims,
            }
        )
    return {
        "kind": "declaration",
        "authority_posture": "atlas_navigation_projection_not_proof_authority",
        "matches": decorated,
        "match_count": len(matches),
        "omitted_match_count": max(0, len(matches) - limit),
        "follow": {
            "claim": "python3 scripts/query_corpus.py --claim <claim_id>",
            "module": "python3 scripts/query_corpus.py --module <module_or_sigil>",
        },
        "validation": "python3 scripts/build_declaration_atlas.py --check",
    }


def compact_declaration(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "name": row["name"],
        "declaration_kind": row["kind"],
        "module": row["module"],
        "line": row["line"],
        "source_ref": f"{row['module']}:{row['line']}",
        "claim_ids": row.get("claim_ids", []),
        "generated_certificate": bool(row.get("generated_certificate")),
    }


def module_roles(claims: dict[str, Any]) -> dict[str, str]:
    nodes = claims["machine_readable_paper"]["module_graph"]["nodes"]
    roles = {row["id"]: row["role"] for row in nodes}
    roles["Erdos249257"] = "Supported package root import"
    return roles


def compact_module(row: dict[str, Any], roles: dict[str, str]) -> dict[str, Any]:
    return {
        "id": row["id"],
        "path": row["path"],
        "role": roles.get(row["id"], "Unclassified module"),
        "declaration_count": row["declaration_count"],
    }


def module_packet(handle: str, limit: int) -> dict[str, Any]:
    atlas = load("docs/declaration_atlas.json")
    claims = load("docs/claims.json")
    aliases = load("paper/module-aliases.json")["aliases"]
    alias = next((row for row in aliases if row["sigil"].casefold() == handle.casefold()), None)
    if alias is not None:
        handle = alias["path"]
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
    roles = module_roles(claims)
    module_view = {**module, "role": roles.get(module["id"], "Unclassified module")}
    imported_rows = [row for row in atlas["modules"] if row["id"] in module["imports"]]
    importer_rows = [row for row in atlas["modules"] if module["id"] in row["imports"]]
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
    claim_rows = [compact_claim(row) for row in claims["claims"] if row["id"] in attached_claim_ids]
    return {
        "kind": "module",
        "authority_posture": "atlas_navigation_projection_not_proof_authority",
        "module": module_view,
        "paper_sigil": next(
            (row["sigil"] for row in aliases if row["path"] == module["path"]), None
        ),
        "attached_claims": claim_rows,
        "declaration_preview": [compact_declaration(row) for row in declarations[:limit]],
        "declaration_preview_receipt": {
            "total": len(declarations),
            "emitted": min(len(declarations), limit),
            "omitted": max(0, len(declarations) - limit),
            "expand": f"python3 scripts/query_corpus.py --search {module['path']} --limit {MAX_LIMIT}",
            "exhaustive": "docs/declaration_atlas.json",
        },
        "dependency_neighbourhood": {
            "imports": [compact_module(row, roles) for row in imported_rows[:limit]],
            "importers": [compact_module(row, roles) for row in importer_rows[:limit]],
            "receipt": {
                "imports_total": len(imported_rows),
                "imports_emitted": min(len(imported_rows), limit),
                "imports_omitted": max(0, len(imported_rows) - limit),
                "importers_total": len(importer_rows),
                "importers_emitted": min(len(importer_rows), limit),
                "importers_omitted": max(0, len(importer_rows) - limit),
                "exhaustive": "docs/claims.json::machine_readable_paper.module_graph",
            },
        },
        "validation": "python3 scripts/build_declaration_atlas.py --check",
    }


def search_rank(query: str, primary: str, haystack: str) -> int | None:
    needle = query.casefold()
    key = primary.casefold()
    body = haystack.casefold()
    if needle == key:
        return 0
    if key.startswith(needle):
        return 1
    if needle in key:
        return 2
    if needle in body:
        return 3
    return None


def search_packet(query: str, limit: int) -> dict[str, Any]:
    query = query.strip()
    if not query:
        raise ValueError("search query must not be empty")
    claims = load("docs/claims.json")
    atlas = load("docs/declaration_atlas.json")
    orientation = load("docs/orientation.json")
    aliases = load("paper/module-aliases.json")["aliases"]
    sigil_by_path = {row["path"]: row["sigil"] for row in aliases}
    roles = module_roles(claims)
    ranked: list[tuple[int, str, dict[str, Any]]] = []

    for proposition in claims["remaining_open_propositions"]:
        rank = search_rank(
            query,
            proposition["id"],
            proposition["statement"] + " " + proposition["open_target_claim"],
        )
        if rank is not None:
            ranked.append(
                (
                    rank,
                    f"open_proposition:{proposition['id']}",
                    {"kind": "open_proposition", **proposition},
                )
            )

    for claim in claims["claims"]:
        rank = search_rank(
            query,
            claim["id"],
            " ".join(
                str(value)
                for value in (claim["label"], claim["statement"], claim["status"], claim.get("paper_label"))
                if value
            ),
        )
        if rank is not None:
            ranked.append((rank, f"claim:{claim['id']}", {"kind": "claim", **compact_claim(claim)}))

    for row in atlas["declarations"]:
        rank = search_rank(
            query,
            row["name"],
            " ".join(str(value) for value in (row["signature"], row.get("docstring"), row["module"]) if value),
        )
        if rank is not None:
            result = {"kind": "declaration", **compact_declaration(row)}
            if row.get("signature"):
                result["signature_excerpt"] = str(row["signature"])[:240]
            ranked.append((rank, f"declaration:{row['module']}:{row['line']}:{row['name']}", result))

    for row in atlas["modules"]:
        sigil = sigil_by_path.get(row["path"])
        ranks = [search_rank(query, row["id"], row["path"])]
        if sigil:
            ranks.append(search_rank(query, sigil, row["id"] + " " + row["path"]))
        rank = min((value for value in ranks if value is not None), default=None)
        if rank is not None:
            ranked.append(
                (
                    rank,
                    f"module:{row['id']}",
                    {
                        "kind": "module",
                        "id": row["id"],
                        "path": row["path"],
                        "paper_sigil": sigil,
                        "role": roles.get(row["id"], "Unclassified module"),
                        "declaration_count": row["declaration_count"],
                        "import_count": len(row["imports"]),
                    },
                )
            )

    for row in orientation["reading_routes"]:
        rank = search_rank(query, row["id"], row["intent"] + " " + " ".join(row["read"]))
        if rank is not None:
            ranked.append((rank, f"route:{row['id']}", {"kind": "reading_route", **row}))

    ranked.sort(key=lambda item: (item[0], item[1]))
    results = [item[2] for item in ranked]
    return {
        "kind": "search",
        "authority_posture": "navigation_projection_not_proof_authority",
        "query": query,
        "match_count": len(results),
        "results": results[:limit],
        "omitted_match_count": max(0, len(results) - limit),
        "limit": limit,
        "next": "Use the typed handle with --claim, --open, --declaration, --module, or --route.",
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
        neighbourhood = packet["argument_neighbourhood"]
        return (
            f"claim {claim['id']} | {claim['status']} | paper={claim.get('paper_label')} "
            f"| incoming={len(neighbourhood['incoming'])} | outgoing={len(neighbourhood['outgoing'])} "
            f"| declarations={decls}"
        )
    if kind == "declaration":
        return "\n".join(
            f"declaration {row['name']} | {row['kind']} | {row['module']}:{row['line']} | claims={','.join(row['claim_ids']) or 'none'}"
            for row in packet["matches"]
        )
    if kind == "open_proposition":
        proposition = packet["open_proposition"]
        return (
            f"open {proposition['id']} | target={packet['open_target']['id']} "
            f"| linked_claims={len(packet['linked_claims'])} "
            f"| advancing_claims={len(packet['advancing_claims'])}"
        )
    if kind == "module":
        module = packet["module"]
        dependency = packet["dependency_neighbourhood"]["receipt"]
        return (
            f"module {module['id']} | {module['path']} | declarations={module['declaration_count']} "
            f"| imports={dependency['imports_total']} | importers={dependency['importers_total']} "
            f"| claims={len(packet['attached_claims'])} | paper_sigil={packet.get('paper_sigil') or 'none'} "
            f"| role={module['role']}"
        )
    if kind == "search":
        rows = [
            f"search {packet['query']!r} | matches={packet['match_count']} | emitted={len(packet['results'])}"
        ]
        for result in packet["results"]:
            handle = result.get("id") or result.get("name")
            rows.append(f"{result['kind']} | {handle}")
        return "\n".join(rows)
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
    group.add_argument("--open", metavar="ID")
    group.add_argument("--declaration", metavar="NAME")
    group.add_argument("--module", metavar="PATH_OR_ID")
    group.add_argument("--route", metavar="ID")
    group.add_argument("--search", metavar="TEXT")
    parser.add_argument("--limit", type=int, default=DEFAULT_LIMIT)
    parser.add_argument("--format", choices=("json", "card"), default="json")
    args = parser.parse_args()
    if not 1 <= args.limit <= MAX_LIMIT:
        parser.error(f"--limit must be between 1 and {MAX_LIMIT}")
    try:
        if args.claim:
            packet = claim_packet(args.claim)
        elif args.open:
            packet = open_proposition_packet(args.open)
        elif args.declaration:
            packet = declaration_packet(args.declaration, args.limit)
        elif args.module:
            packet = module_packet(args.module, args.limit)
        elif args.route:
            packet = route_packet(args.route)
        elif args.search:
            packet = search_packet(args.search, args.limit)
        else:
            packet = summary_packet()
    except (KeyError, ValueError, json.JSONDecodeError, OSError) as exc:
        print(f"query_corpus: {exc}", file=sys.stderr)
        return 2
    if args.format == "card":
        print(render_card(packet))
    else:
        encoded = json.dumps(packet, ensure_ascii=False, indent=2) + "\n"
        if len(encoded.encode("utf-8")) > OUTPUT_BUDGET_BYTES:
            print(
                f"query_corpus: response exceeds {OUTPUT_BUDGET_BYTES} bytes; lower --limit or use --format card",
                file=sys.stderr,
            )
            return 2
        print(encoded, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
