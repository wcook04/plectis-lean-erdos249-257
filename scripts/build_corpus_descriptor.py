#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build the public corpus descriptor and bounded orientation projections.

The descriptor is a self-describing navigation root for external agents.  It
keeps the proof-bearing release identity distinct from the later navigation
snapshot, carries content digests for the machine-readable paper, methodology
contract, and exhaustive atlas, and embeds only compact navigation data.  It
does not duplicate the full declaration atlas or acquire proof authority.

The companion orientation JSON and Markdown are deliberately small first-read
surfaces. They expose scale, the proved/open boundary, principal claims, and
typed drilldowns without asking a cold reader to load the exhaustive graphs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / "docs" / "corpus_descriptor.json"
ORIENTATION_JSON = ROOT / "docs" / "orientation.json"
ORIENTATION_MARKDOWN = ROOT / "docs" / "ORIENTATION.md"
README_PATH = ROOT / "README.md"
CLAIMS_PATH = ROOT / "docs" / "claims.json"
ATLAS_PATH = ROOT / "docs" / "declaration_atlas.json"
METHODOLOGY_PATH = ROOT / "docs" / "methodology.json"
README_SCALE_BEGIN = "<!-- BEGIN generated_corpus_at_a_glance -->"
README_SCALE_END = "<!-- END generated_corpus_at_a_glance -->"


def canonical_digest(value: Any) -> str:
    encoded = json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def file_digest(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str, check: bool = True) -> str:
    completed = subprocess.run(
        ["git", *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if check and completed.returncode != 0:
        raise RuntimeError(completed.stderr.strip() or f"git {' '.join(args)} failed")
    return completed.stdout.strip() if completed.returncode == 0 else ""


def is_ancestor(ancestor: str, descendant: str) -> bool:
    return (
        subprocess.run(
            ["git", "merge-base", "--is-ancestor", ancestor, descendant],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        ).returncode
        == 0
    )


def build_orientation(claims: dict[str, Any], atlas: dict[str, Any]) -> dict[str, Any]:
    """Project a bounded first-read capsule from the exhaustive owners."""
    principal_claims = []
    for claim in claims["claims"]:
        if not claim.get("readme_headline"):
            continue
        row = {
            "id": claim["id"],
            "status": claim["status"],
            "statement": claim["statement"],
            "paper_label": claim.get("paper_label"),
            "declarations": [
                {
                    "name": declaration["name"],
                    "module": declaration["module"],
                    "line": declaration["line"],
                }
                for declaration in claim["declarations"]
            ],
        }
        if claim.get("remaining_open_proposition_ids"):
            row["remaining_open_proposition_ids"] = claim["remaining_open_proposition_ids"]
        principal_claims.append(row)

    machine_paper = claims["machine_readable_paper"]
    return {
        "schema": "erdos249257-orientation/1",
        "artifact_role": "bounded_first_read_navigation_projection",
        "authority_posture": "navigation_projection_not_proof_authority",
        "proof_authority": "Lean source checked by the pinned Lean kernel",
        "release": {
            "version": claims["release"]["version"],
            "tag": claims["release"]["tag"],
            "lean_toolchain": claims["release"]["lean_toolchain"],
        },
        "scale": atlas["summary"],
        "status_taxonomy": claims["status_taxonomy"],
        "remaining_open_propositions": claims["remaining_open_propositions"],
        "non_claims": claims["non_claims"],
        "principal_claims": principal_claims,
        "reading_routes": machine_paper["entrypoints"],
        "drilldowns": {
            "exact_claims_and_argument_graph": "docs/claims.json",
            "machine_readable_paper": "docs/claims.json::machine_readable_paper",
            "exhaustive_declarations": "docs/declaration_atlas.json",
            "mathematical_methodology": "docs/methodology.json",
            "human_exposition": "erdos249-257-exposition.pdf",
            "technical_companion": "erdos249-transport-curvature.pdf",
            "paper_source_sigils": "paper/module-aliases.json",
            "source_by_question": "docs/SOURCE_MAP.md",
            "development_chronology": "docs/WAVE_INDEX.md",
            "supported_root_import": "Erdos249257.lean",
        },
        "checks": {
            "release": "python3 scripts/check_release.py",
            "cold_clone_comprehension": "python3 scripts/check_cold_clone_comprehension.py",
            "orientation_freshness": "python3 scripts/build_corpus_descriptor.py --check",
        },
        "queries": {
            "summary": "python3 scripts/query_corpus.py --format card",
            "claim": "python3 scripts/query_corpus.py --claim <claim_id>",
            "declaration": "python3 scripts/query_corpus.py --declaration <Lean_name>",
            "module": "python3 scripts/query_corpus.py --module <path_or_id_or_paper_sigil>",
            "reading_route": "python3 scripts/query_corpus.py --route <route_id>",
            "search": "python3 scripts/query_corpus.py --search <text> [--limit 1..100]",
        },
        "external_registration": {
            "path": "docs/corpus_descriptor.json",
            "schema": "erdos249257-corpus-descriptor/3",
            "maximum_bytes": 64_000,
            "inline": ["release_identity", "content_digests", "principal_claim_handles", "root_module_topology"],
            "expands_to": ["docs/claims.json", "docs/declaration_atlas.json", "docs/methodology.json"],
        },
    }


def render_orientation_markdown(orientation: dict[str, Any]) -> str:
    scale = orientation["scale"]
    lines = [
        "<!--",
        "SPDX-FileCopyrightText: 2026 Will Cook",
        "SPDX-License-Identifier: Apache-2.0",
        "",
        "Generated by scripts/build_corpus_descriptor.py. Do not edit by hand.",
        "-->",
        "",
        "# Corpus orientation",
        "",
        "This is the bounded first-read map for the public release. It is a navigation",
        "projection, not proof authority. The published Lean source checked by the pinned",
        "Lean kernel remains proof authority.",
        "",
        "## Scale",
        "",
        "| Surface | Count |",
        "|---|---:|",
        f"| Lean modules | {scale['module_count']:,} |",
        f"| Lean declarations | {scale['declaration_count']:,} |",
        f"| Theorem-like declarations | {scale['theorem_like_count']:,} |",
        f"| Generated certificate declarations | {scale['generated_certificate_declaration_count']:,} |",
        f"| Principal claim links | {scale['principal_claim_link_count']:,} |",
        "",
        "The exhaustive declaration and import index is",
        "[`docs/declaration_atlas.json`](declaration_atlas.json). Generated certificate",
        "shards are counted as formal source, not as separate mathematical claims.",
        "",
        "## Exact open boundary",
        "",
    ]
    for row in orientation["remaining_open_propositions"]:
        lines.append(f"- `{row['id']}` — {row['statement']}")
    lines.extend(["", "## Principal claim routes", ""])
    lines.extend(
        [
            "| Claim | Status | Paper | First Lean anchor |",
            "|---|---|---|---|",
        ]
    )
    for claim in orientation["principal_claims"]:
        first = claim["declarations"][0]
        anchor = f"`{first['name']}` in `{first['module']}:{first['line']}`"
        lines.append(
            f"| `{claim['id']}` | {claim['status']} | `{claim['paper_label']}` | {anchor} |"
        )
    lines.extend(
        [
            "",
            "Each row is only an entry handle. Read the claim statement and every attached",
            "declaration in [`docs/claims.json`](claims.json), then follow the paper label into",
            "the authored exposition. A conditional reduction or finite instance does not",
            "settle the open proposition attached to it.",
            "",
            "## Read by intent",
            "",
        ]
    )
    for route in orientation["reading_routes"]:
        paths = " → ".join(f"`{path}`" for path in route["read"])
        lines.append(f"- **{route['intent']}** (`{route['id']}`): {paths}")
    lines.extend(
        [
            "",
            "## Drill down",
            "",
            "- Exact statuses, statements, paper anchors, declarations, and argument edges:",
            "  [`docs/claims.json`](claims.json)",
            "- Source routes by mathematical question: [`docs/SOURCE_MAP.md`](SOURCE_MAP.md)",
            "- Development chronology: [`docs/WAVE_INDEX.md`](WAVE_INDEX.md)",
            "- Human mathematical account: [`erdos249-257-exposition.pdf`](../erdos249-257-exposition.pdf)",
            "- Transport and curvature companion: [`erdos249-transport-curvature.pdf`](../erdos249-transport-curvature.pdf)",
            "- Machine form of this page: [`docs/orientation.json`](orientation.json)",
            "",
            "## External corpus registration",
            "",
            "[`docs/corpus_descriptor.json`](corpus_descriptor.json) uses schema",
            "`erdos249257-corpus-descriptor/3`. The release gate keeps it below 64 KB.",
            "It carries release identities, content digests, principal claim and declaration",
            "handles, and the root module topology. Complete claims, module imports,",
            "declaration prose, and methodology remain in their digest-bound expansion files.",
            "",
            "## Query one handle",
            "",
            "The read-only query helper returns bounded JSON by default:",
            "",
            "```sh",
            "python3 scripts/query_corpus.py --format card",
            "python3 scripts/query_corpus.py --claim denominator_exclusion",
            "python3 scripts/query_corpus.py --declaration irrational_erdosSum_full_support",
            "python3 scripts/query_corpus.py --module Erdos249257/CertificateKernel.lean",
            "python3 scripts/query_corpus.py --module CerKer",
            "python3 scripts/query_corpus.py --route instant_orientation",
            "python3 scripts/query_corpus.py --search totient --limit 10",
            "```",
            "",
        ]
    )
    return "\n".join(lines)


def render_readme_scale_strip(orientation: dict[str, Any]) -> str:
    scale = orientation["scale"]
    return "\n".join(
        [
            README_SCALE_BEGIN,
            "<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->",
            "## Corpus at a glance",
            "",
            "| Checked surface | Scale |",
            "|---|---:|",
            f"| Lean modules | {scale['module_count']:,} |",
            f"| Lean declarations | {scale['declaration_count']:,} |",
            f"| Theorem-like declarations | {scale['theorem_like_count']:,} |",
            f"| Generated certificate declarations | {scale['generated_certificate_declaration_count']:,} |",
            f"| Principal claim-to-Lean links | {scale['principal_claim_link_count']:,} |",
            f"| Exact remaining open propositions | {len(orientation['remaining_open_propositions']):,} |",
            "",
            "These are generated navigation counts, not a claim that every declaration is a",
            "separate mathematical result. Start with the bounded",
            "[`docs/ORIENTATION.md`](docs/ORIENTATION.md), then drill into one exact handle",
            "with `python3 scripts/query_corpus.py`.",
            README_SCALE_END,
        ]
    )


def replace_readme_scale_strip(readme: str, replacement: str) -> str:
    start = readme.find(README_SCALE_BEGIN)
    end = readme.find(README_SCALE_END)
    if start < 0 or end < 0 or end < start:
        raise ValueError("README corpus-at-a-glance generated-region markers are missing")
    end += len(README_SCALE_END)
    return readme[:start] + replacement + readme[end:]


def build() -> dict[str, Any]:
    claims = json.loads(CLAIMS_PATH.read_text(encoding="utf-8"))
    atlas = json.loads(ATLAS_PATH.read_text(encoding="utf-8"))
    methodology = json.loads(METHODOLOGY_PATH.read_text(encoding="utf-8"))
    machine_paper = claims["machine_readable_paper"]
    release = claims["release"]

    formal_tag = str(release["tag"])
    formal_commit = git("rev-parse", f"{formal_tag}^{{commit}}")
    navigation_commit = git(
        "log",
        "-1",
        "--format=%H",
        "--",
        "docs/claims.json",
        "docs/declaration_atlas.json",
        "docs/methodology.json",
    )
    local_main = git("rev-parse", "--verify", "main", check=False)
    publication_state = (
        "main_history_snapshot"
        if local_main and is_ancestor(navigation_commit, local_main)
        else "detached_navigation_snapshot"
    )

    orientation = build_orientation(claims, atlas)
    root_module = next(row for row in atlas["modules"] if row["path"] == "Erdos249257.lean")
    principal_declaration_handles = [
        {"claim_id": claim["id"], **declaration}
        for claim in orientation["principal_claims"]
        for declaration in claim["declarations"]
    ]

    repository = str(release["repository"])
    return {
        "schema": "erdos249257-corpus-descriptor/3",
        "artifact_role": "self_describing_external_mathematical_corpus_root",
        "corpus_id": "plectis_lean_erdos249_257_public",
        "authority_posture": {
            "proof": "Lean source checked by the pinned Lean kernel",
            "authored_argument": "docs/claims.json::machine_readable_paper.argument_graph",
            "navigation": "generated projections and this descriptor; not proof authority",
            "semantic_bridge": "approximate correspondence only; never a proof edge",
            "methodology": "docs/methodology.json defines mathematical methodology and claim-transition requirements; it is not proof authority or claim-status authority",
        },
        "identity": {
            "formal_source": {
                "tag": formal_tag,
                "resolved_commit": formal_commit,
                "lean_toolchain": release["lean_toolchain"],
                "authority_role": "proof_bearing_release_anchor",
            },
            "navigation_snapshot": {
                "commit": navigation_commit,
                "authority_role": "machine_readable_navigation_anchor",
                "publication_state": publication_state,
                "published_ref": "main" if publication_state == "main_history_snapshot" else None,
                "repository_resolution": f"{repository}/tree/{navigation_commit}",
            },
            "content": {
                "machine_readable_paper": {
                    "path": "docs/claims.json::machine_readable_paper",
                    "content_digest": canonical_digest(machine_paper),
                },
                "claims_document": {
                    "path": "docs/claims.json",
                    "content_digest": file_digest(CLAIMS_PATH),
                },
                "declaration_atlas": {
                    "path": "docs/declaration_atlas.json",
                    "content_digest": file_digest(ATLAS_PATH),
                    "source_input_fingerprint": atlas["source_fingerprint"],
                },
                "methodology_contract": {
                    "path": "docs/methodology.json",
                    "content_digest": file_digest(METHODOLOGY_PATH),
                },
                "bounded_orientation": {
                    "path": "docs/orientation.json",
                    "content_digest": canonical_digest(orientation),
                },
            },
        },
        "schemas": {
            "claims": claims["schema"],
            "machine_readable_paper": machine_paper["schema"],
            "declaration_atlas": atlas["schema"],
            "methodology": methodology["schema"],
        },
        "capabilities": {
            "global_argument_graph": True,
            "module_import_graph": True,
            "principal_claim_declaration_links": True,
            "high_salience_signatures": True,
            "exhaustive_declaration_lookup": "attached_atlas",
            "declaration_level_proof_dependencies": False,
            "typed_remaining_open_propositions": True,
            "claim_transition_requirements": True,
            "human_mathematical_review_is_machine_decidable": False,
        },
        "retrieval_modes": {
            "global": {
                "source": "docs/orientation.json and compact_graph",
                "supports": ["proved_open_boundary", "principal_claim_routes", "release_scale", "root_module_topology"],
            },
            "concept": {
                "source": "scripts/query_corpus.py then attached claims or atlas",
                "supports": ["name", "signature", "docstring", "bounded_module_neighbourhood"],
            },
            "premise_chain": {
                "source": "docs/claims.json::machine_readable_paper.argument_graph and module_graph",
                "boundary": "The public atlas does not claim elaborator-derived declaration dependencies or accessibility annotations.",
            },
        },
        "summary": atlas["summary"],
        "compact_graph": {
            "status_taxonomy": claims["status_taxonomy"],
            "principal_claims": orientation["principal_claims"],
            "non_claims": claims["non_claims"],
            "remaining_open_propositions": claims["remaining_open_propositions"],
            "module_topology": {
                "root": machine_paper["module_graph"]["root"],
                "node_count": len(machine_paper["module_graph"]["nodes"]),
                "root_imports": root_module["imports"],
                "full_graph": "docs/claims.json::machine_readable_paper.module_graph",
            },
            "argument_graph": machine_paper["argument_graph"],
            "methodology_capsule": {
                "path": "docs/methodology.json",
                "human_projection": "METHODOLOGY.md",
                "artifact_role": methodology["artifact_role"],
                "human_capsule": methodology["human_capsule"],
                "method_axiom_ids": [row["id"] for row in methodology["method_axioms"]],
                "transition_contract_ids": [row["id"] for row in methodology["transition_contracts"]],
                "change_classes": methodology["change_classes"],
                "full_contract": "docs/methodology.json",
            },
            "principal_declaration_handles": principal_declaration_handles,
        },
        "expansion": {
            "machine_readable_paper": {
                "path": "docs/claims.json::machine_readable_paper",
                "expected_content_digest": canonical_digest(machine_paper),
                "contains": ["all_claims", "authored_argument_graph", "complete_module_import_graph"],
                "query": "python3 scripts/query_corpus.py --claim <claim_id>",
            },
            "exhaustive_declaration_atlas": {
                "path": "docs/declaration_atlas.json",
                "expected_content_digest": file_digest(ATLAS_PATH),
                "expected_source_input_fingerprint": atlas["source_fingerprint"],
                "availability": "optional_attached_corpus",
                "check": "python3 scripts/build_declaration_atlas.py --check",
            },
            "methodology_contract": {
                "path": "docs/methodology.json",
                "expected_content_digest": file_digest(METHODOLOGY_PATH),
                "human_projection": "METHODOLOGY.md",
                "check": "python3 scripts/build_methodology.py --check",
            },
        },
        "migration_from_v2": {
            "reason": "Version 2 embedded exhaustive graphs and full declaration prose in a surface described as compact.",
            "field_replacements": {
                "compact_graph.claims": "compact_graph.principal_claims; expand through docs/claims.json or query_corpus.py",
                "compact_graph.module_graph": "compact_graph.module_topology; expand through docs/claims.json::machine_readable_paper.module_graph",
                "compact_graph.high_salience_declarations": "compact_graph.principal_declaration_handles; expand through docs/declaration_atlas.json or query_corpus.py",
                "compact_graph.methodology_capsule extended fields": "docs/methodology.json",
            },
        },
        "checks": {
            "descriptor": "python3 scripts/build_corpus_descriptor.py --check",
            "methodology": "python3 scripts/build_methodology.py --check",
            "methodology_mutations": "python3 scripts/test_methodology_contract.py",
            "release": "python3 scripts/check_release.py",
        },
    }


def render() -> str:
    return json.dumps(build(), ensure_ascii=False, indent=2) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the descriptor is stale")
    args = parser.parse_args()
    claims = json.loads(CLAIMS_PATH.read_text(encoding="utf-8"))
    atlas = json.loads(ATLAS_PATH.read_text(encoding="utf-8"))
    orientation = build_orientation(claims, atlas)
    expected = render()
    expected_orientation_json = json.dumps(orientation, ensure_ascii=False, indent=2) + "\n"
    expected_orientation_markdown = render_orientation_markdown(orientation)
    actual_readme = README_PATH.read_text(encoding="utf-8")
    expected_readme = replace_readme_scale_strip(
        actual_readme, render_readme_scale_strip(orientation)
    )
    if args.check:
        actual = OUTPUT.read_text(encoding="utf-8") if OUTPUT.is_file() else ""
        actual_orientation_json = (
            ORIENTATION_JSON.read_text(encoding="utf-8") if ORIENTATION_JSON.is_file() else ""
        )
        actual_orientation_markdown = (
            ORIENTATION_MARKDOWN.read_text(encoding="utf-8")
            if ORIENTATION_MARKDOWN.is_file()
            else ""
        )
        if (
            actual != expected
            or actual_orientation_json != expected_orientation_json
            or actual_orientation_markdown != expected_orientation_markdown
            or actual_readme != expected_readme
        ):
            print(
                "corpus descriptor, orientation, or README scale projection is stale; "
                "run python3 scripts/build_corpus_descriptor.py"
            )
            return 1
        descriptor = json.loads(actual)
        print(
            "corpus descriptor and orientation current: "
            f"formal={descriptor['identity']['formal_source']['resolved_commit'][:8]} "
            f"navigation={descriptor['identity']['navigation_snapshot']['commit'][:8]}"
        )
        return 0
    OUTPUT.write_text(expected, encoding="utf-8")
    ORIENTATION_JSON.write_text(expected_orientation_json, encoding="utf-8")
    ORIENTATION_MARKDOWN.write_text(expected_orientation_markdown, encoding="utf-8")
    README_PATH.write_text(expected_readme, encoding="utf-8")
    print(
        "wrote "
        f"{OUTPUT.relative_to(ROOT)}, {ORIENTATION_JSON.relative_to(ROOT)}, and "
        f"{ORIENTATION_MARKDOWN.relative_to(ROOT)}, and {README_PATH.relative_to(ROOT)}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
