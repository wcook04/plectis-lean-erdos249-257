#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build the compact, dual-anchored public mathematical-corpus descriptor.

The descriptor is a self-describing navigation root for external agents.  It
keeps the proof-bearing release identity distinct from the later navigation
snapshot, carries content digests for the machine-readable paper and exhaustive
atlas, and embeds only the compact claim/module graph.  It does not duplicate
the full declaration atlas or acquire proof authority.
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
CLAIMS_PATH = ROOT / "docs" / "claims.json"
ATLAS_PATH = ROOT / "docs" / "declaration_atlas.json"


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


def build() -> dict[str, Any]:
    claims = json.loads(CLAIMS_PATH.read_text(encoding="utf-8"))
    atlas = json.loads(ATLAS_PATH.read_text(encoding="utf-8"))
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
    )
    origin_main = git("rev-parse", "--verify", "origin/main", check=False)
    publication_state = (
        "published_origin_main"
        if origin_main and is_ancestor(navigation_commit, origin_main)
        else "navigation_snapshot_unpublished"
    )

    atlas_by_declaration = {
        (str(row["module"]), str(row["name"])): row
        for row in atlas["declarations"]
    }
    compact_claims: list[dict[str, Any]] = []
    high_salience_declarations: list[dict[str, Any]] = []
    for claim in claims["claims"]:
        declaration_rows: list[dict[str, Any]] = []
        for declaration in claim["declarations"]:
            key = (str(declaration["module"]), str(declaration["name"]))
            atlas_row = atlas_by_declaration.get(key, {})
            row = {
                "name": declaration["name"],
                "module": declaration["module"],
                "line": declaration["line"],
                "kind": atlas_row.get("kind"),
                "signature": atlas_row.get("signature"),
                "docstring": atlas_row.get("docstring"),
            }
            declaration_rows.append(row)
            high_salience_declarations.append({"claim_id": claim["id"], **row})
        compact_claims.append(
            {
                "id": claim["id"],
                "label": claim["label"],
                "status": claim["status"],
                "statement": claim["statement"],
                "paper_label": claim.get("paper_label"),
                "readme_headline": bool(claim.get("readme_headline")),
                "declarations": declaration_rows,
            }
        )

    repository = str(release["repository"])
    return {
        "schema": "erdos249257-corpus-descriptor/1",
        "artifact_role": "self_describing_external_mathematical_corpus_root",
        "corpus_id": "plectis_lean_erdos249_257_public",
        "authority_posture": {
            "proof": "Lean source checked by the pinned Lean kernel",
            "authored_argument": "docs/claims.json::machine_readable_paper.argument_graph",
            "navigation": "generated projections and this descriptor; not proof authority",
            "semantic_bridge": "approximate correspondence only; never a proof edge",
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
                "published_ref": "origin/main" if publication_state == "published_origin_main" else None,
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
            },
        },
        "schemas": {
            "claims": claims["schema"],
            "machine_readable_paper": machine_paper["schema"],
            "declaration_atlas": atlas["schema"],
        },
        "capabilities": {
            "global_argument_graph": True,
            "module_import_graph": True,
            "principal_claim_declaration_links": True,
            "high_salience_signatures": True,
            "exhaustive_declaration_lookup": "attached_atlas",
            "declaration_level_proof_dependencies": False,
        },
        "retrieval_modes": {
            "global": {
                "source": "compact_graph",
                "supports": ["proved_open_boundary", "principal_argument_routes", "module_topology"],
            },
            "concept": {
                "source": "compact_graph.high_salience_declarations_then_attached_atlas",
                "supports": ["name", "signature", "docstring", "bounded_module_neighbourhood"],
            },
            "premise_chain": {
                "source": "authored_argument_edges_and_module_imports",
                "boundary": "The public atlas does not claim elaborator-derived declaration dependencies or accessibility annotations.",
            },
        },
        "summary": atlas["summary"],
        "compact_graph": {
            "status_taxonomy": claims["status_taxonomy"],
            "claims": compact_claims,
            "non_claims": claims["non_claims"],
            "module_graph": machine_paper["module_graph"],
            "argument_graph": machine_paper["argument_graph"],
            "high_salience_declarations": high_salience_declarations,
        },
        "expansion": {
            "exhaustive_declaration_atlas": {
                "path": "docs/declaration_atlas.json",
                "expected_content_digest": file_digest(ATLAS_PATH),
                "expected_source_input_fingerprint": atlas["source_fingerprint"],
                "availability": "optional_attached_corpus",
                "check": "python3 scripts/build_declaration_atlas.py --check",
            }
        },
        "checks": {
            "descriptor": "python3 scripts/build_corpus_descriptor.py --check",
            "release": "python3 scripts/check_release.py",
        },
    }


def render() -> str:
    return json.dumps(build(), ensure_ascii=False, indent=2) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the descriptor is stale")
    args = parser.parse_args()
    expected = render()
    if args.check:
        actual = OUTPUT.read_text(encoding="utf-8") if OUTPUT.is_file() else ""
        if actual != expected:
            print("corpus descriptor is stale; run python3 scripts/build_corpus_descriptor.py")
            return 1
        descriptor = json.loads(actual)
        print(
            "corpus descriptor current: "
            f"formal={descriptor['identity']['formal_source']['resolved_commit'][:8]} "
            f"navigation={descriptor['identity']['navigation_snapshot']['commit'][:8]}"
        )
        return 0
    OUTPUT.write_text(expected, encoding="utf-8")
    print(f"wrote {OUTPUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
