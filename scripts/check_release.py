#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Cross-surface release checker.

The single owner of release identity and claim status is docs/claims.json.
This script verifies that every other public surface agrees with it:

  1. claims.json is well formed, every claim status is in the taxonomy, typed
     remaining-open propositions resolve, and the machine-readable paper graph
     resolves to real public files and claim ids.
  2. Release identity: lakefile.toml, CITATION.cff, and the paper's pinned
     artefact reference all state the same version/tag.
  3. Every claimed Lean declaration exists in the stated module at the
     stated line.
  4. Every paper source link (\\lref / \\lrefx / \\lloc) resolves: the file
     exists and the named declaration appears at the stated line.
  5. SCOPE.md lists exactly the machine identifiers in claims.json.
  6. README.md carries the headline declarations, states the release tag,
     uses only taxonomy statuses in its status table, and contains none of
     the banned drift phrases.
  7. Licensing: every licence named in REUSE.toml or an SPDX header has its
     text under LICENSES/.
  8. AGENTS.md routes agent harnesses through the public machine-readable paper
     without weakening the proof or open-problem boundary.
  9. Proof-trust guard: no sorry/admit/native_decide/axiom in the Lean
     sources.
 10. The methodology source, generated root projection, claim-transition
     requirements, descriptor capsule, and entry routes agree.

Stdlib only; run from the repository root:  python3 scripts/check_release.py
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

from methodology_contract import mutation_fixture_errors, render_markdown, validate_contract

ROOT = Path(__file__).resolve().parent.parent
ERRORS: list[str] = []
CHECKS = 0

LINE_WINDOW = 3  # declaration name must appear within this many lines of the stated line

README_BANNED_PHRASES = [
    "Ramanujan Machine Challenge",
    "publication status",
    "ai_workflow` is a private",
]


def fail(msg: str) -> None:
    ERRORS.append(msg)


def check(ok: bool, msg: str) -> None:
    global CHECKS
    CHECKS += 1
    if not ok:
        fail(msg)


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def module_lines(cache: dict[str, list[str]], rel: str) -> list[str] | None:
    if rel not in cache:
        p = ROOT / rel
        cache[rel] = read(p).splitlines() if p.is_file() else None
    return cache[rel]


def name_at_line(lines: list[str], name: str, line: int) -> bool:
    lo = max(0, line - 1 - LINE_WINDOW)
    hi = min(len(lines), line - 1 + LINE_WINDOW + 1)
    return any(name in lines[i] for i in range(lo, hi))


def internal_imports(path: Path) -> list[str]:
    """Return direct Erdos249257 imports in source order."""
    return re.findall(r"^import (Erdos249257(?:\.[A-Za-z0-9_]+)+)\s*$", read(path), re.M)


def lean_code_without_comments_and_strings(text: str) -> str:
    """Remove nested Lean comments and strings while preserving newlines."""
    out: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(text):
        if block_depth:
            if text.startswith("/-", index):
                block_depth += 1
                out.extend("  ")
                index += 2
            elif text.startswith("-/", index):
                block_depth -= 1
                out.extend("  ")
                index += 2
            else:
                out.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif in_string:
            if text[index] == "\\" and index + 1 < len(text):
                out.extend("  ")
                index += 2
            elif text[index] == '"':
                in_string = False
                out.append(" ")
                index += 1
            else:
                out.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif text.startswith("--", index):
            end = text.find("\n", index)
            if end < 0:
                out.extend(" " * (len(text) - index))
                break
            out.extend(" " * (end - index))
            index = end
        elif text.startswith("/-", index):
            block_depth = 1
            out.extend("  ")
            index += 2
        elif text[index] == '"':
            in_string = True
            out.append(" ")
            index += 1
        else:
            out.append(text[index])
            index += 1
    return "".join(out)


def main() -> int:
    cache: dict[str, list[str]] = {}

    # --- 1. claims.json ---------------------------------------------------
    claims_path = ROOT / "docs" / "claims.json"
    data = json.loads(read(claims_path))
    check(data.get("schema") == "erdos249257-claims/3",
          "docs/claims.json must use schema erdos249257-claims/3")
    taxonomy = set(data["status_taxonomy"])
    release = data["release"]
    version, tag = release["version"], release["tag"]
    check(tag == f"v{version}", f"release tag {tag} does not match version {version}")
    claim_ids = [claim["id"] for claim in data["claims"]]
    check(len(claim_ids) == len(set(claim_ids)), "docs/claims.json contains duplicate claim ids")
    claim_id_set = set(claim_ids)
    for claim in data["claims"]:
        check(claim["status"] in taxonomy,
              f"claim {claim['id']}: status {claim['status']!r} not in taxonomy")
        if claim["status"] in ("cited only", "open"):
            check(not claim["declarations"],
                  f"claim {claim['id']}: {claim['status']!r} claims must not carry declarations")
        else:
            check(bool(claim["declarations"]),
                  f"claim {claim['id']}: formal claim carries no declaration")

    machine_paper = data["machine_readable_paper"]
    check(machine_paper.get("schema") == "erdos249257-machine-readable-paper/1",
          "machine_readable_paper has an unsupported schema")
    for route in machine_paper["entrypoints"]:
        check(bool(route.get("id")) and bool(route.get("intent")) and bool(route.get("read")),
              "every machine-readable-paper entrypoint needs id, intent, and read paths")
        for rel in route.get("read", []):
            check((ROOT / rel).is_file(), f"machine-readable-paper entrypoint path does not exist: {rel}")

    module_nodes = machine_paper["module_graph"]["nodes"]
    module_ids = [node["id"] for node in module_nodes]
    check(len(module_ids) == len(set(module_ids)), "machine-readable module graph contains duplicate ids")
    module_id_set = set(module_ids)
    module_paths = {node["path"] for node in module_nodes}
    for node in module_nodes:
        path = ROOT / node["path"]
        check(path.is_file(), f"machine-readable module path does not exist: {node['path']}")
        unknown_imports = set(node["imports"]) - module_id_set
        check(not unknown_imports,
              f"module {node['id']} has unknown internal imports: {sorted(unknown_imports)}")
        if path.is_file():
            observed = internal_imports(path)
            check(observed == node["imports"],
                  f"module {node['id']} imports drifted: registry={node['imports']} source={observed}")
    root_path = ROOT / machine_paper["module_graph"]["root"]
    check(root_path.is_file(), "machine-readable module graph root does not exist")
    if root_path.is_file():
        root_imports = internal_imports(root_path)
        unknown_root_imports = set(root_imports) - module_id_set
        check(not unknown_root_imports,
              f"Erdos249257.lean has imports missing from the machine-readable module graph: {sorted(unknown_root_imports)}")
        imports_by_id = {node["id"]: node["imports"] for node in module_nodes}
        reachable = set(root_imports)
        frontier = list(root_imports)
        while frontier:
            current = frontier.pop()
            for dependency in imports_by_id.get(current, []):
                if dependency not in reachable:
                    reachable.add(dependency)
                    frontier.append(dependency)
        check(reachable == module_id_set,
              f"machine-readable module graph has nodes unreachable from Erdos249257.lean: {sorted(module_id_set - reachable)}")

    edge_types = set(machine_paper["argument_graph"]["edge_semantics"])
    for edge in machine_paper["argument_graph"]["edges"]:
        check(edge.get("from") in claim_id_set,
              f"argument edge has unknown source claim: {edge.get('from')}")
        check(edge.get("to") in claim_id_set,
              f"argument edge has unknown target claim: {edge.get('to')}")
        check(edge.get("relation") in edge_types,
              f"argument edge has unknown relation: {edge.get('relation')}")
    for claim in data["claims"]:
        for decl in claim["declarations"]:
            check(decl["module"] in module_paths,
                  f"claim {claim['id']}: declaration module missing from machine-readable module graph: {decl['module']}")
    for projection in machine_paper.get("projections", []):
        check((ROOT / projection["path"]).is_file(),
              f"machine-readable paper projection does not exist: {projection['path']}")

    # --- methodology source and typed claim transitions -------------------
    methodology_path = ROOT / "docs" / "methodology.json"
    methodology = json.loads(read(methodology_path))
    methodology_errors = validate_contract(data, methodology)
    check(not methodology_errors,
          "methodology contract invalid: " + "; ".join(methodology_errors))

    methodology_projection = ROOT / "METHODOLOGY.md"
    expected_methodology_projection = render_markdown(methodology, data)
    check(methodology_projection.is_file(), "METHODOLOGY.md is missing")
    if methodology_projection.is_file():
        check(read(methodology_projection) == expected_methodology_projection,
              "METHODOLOGY.md does not exactly match docs/methodology.json")

    for fixture_id, fixture_errors in mutation_fixture_errors(data, methodology).items():
        check(bool(fixture_errors),
              f"methodology mutation fixture escaped validation: {fixture_id}")

    # --- 2. release identity ----------------------------------------------
    lakefile = read(ROOT / "lakefile.toml")
    m = re.search(r'^version\s*=\s*"([^"]+)"', lakefile, re.M)
    check(m is not None and m.group(1) == version,
          f"lakefile.toml version {m.group(1) if m else '<missing>'} != claims.json {version}")

    cff = read(ROOT / "CITATION.cff")
    check(re.search(r"^type: software\s*$", cff, re.M) is not None,
          "CITATION.cff: top-level type must be exactly 'software' (CFF 1.2.0)")
    check(re.search(rf'^version: "?{re.escape(version)}"?\s*$', cff, re.M) is not None,
          f"CITATION.cff: version does not state {version}")
    check(re.search(rf"""^date-released: ["']?{re.escape(release['date'])}["']?\s*$""", cff, re.M) is not None,
          f"CITATION.cff: date-released does not state {release['date']}")
    check("Erdős" in cff, "CITATION.cff: title/keywords should use Unicode 'Erdős'")

    toolchain = read(ROOT / "lean-toolchain").strip()
    check(toolchain == release["lean_toolchain"],
          f"lean-toolchain {toolchain} != claims.json {release['lean_toolchain']}")

    paper = read(ROOT / "paper" / "erdos249-257-exposition.tex")
    m = re.search(r"\\newcommand\{\\commit\}\{([^}]+)\}", paper)
    check(m is not None and m.group(1) == tag,
          f"paper \\commit pin {m.group(1) if m else '<missing>'} != release tag {tag}")
    check("blob/main" not in paper,
          "paper links a floating branch (blob/main); pin every link to the release tag")
    for claim in data["claims"]:
        label = claim.get("paper_label")
        if label:
            check(re.search(rf"\\label\{{{re.escape(label)}\}}", paper) is not None,
                  f"claim {claim['id']}: paper label {label!r} does not exist")
    index_label = machine_paper["paper"]["principal_declaration_index_label"]
    check(re.search(rf"\\label\{{{re.escape(index_label)}\}}", paper) is not None,
          f"machine-readable paper index label {index_label!r} does not exist")

    # --- 3. claimed declarations -------------------------------------------
    for claim in data["claims"]:
        for decl in claim["declarations"]:
            lines = module_lines(cache, decl["module"])
            if lines is None:
                fail(f"claim {claim['id']}: module {decl['module']} not found")
                continue
            check(name_at_line(lines, decl["name"], decl["line"]),
                  f"claim {claim['id']}: {decl['name']} not at "
                  f"{decl['module']}:{decl['line']} (±{LINE_WINDOW})")

    # --- 4. paper source links ----------------------------------------------
    for macro, fname, line_s, name in re.findall(
            r"\\(lref|lrefx|lloc)\{([^}]+)\}\{(\d+)\}(?:\{([^}]*)\})?", paper):
        rel = f"Erdos249257/{fname}"
        lines = module_lines(cache, rel)
        if lines is None:
            fail(f"paper \\{macro}: file {rel} not found")
            continue
        line = int(line_s)
        check(line <= len(lines), f"paper \\{macro}: {rel}:{line} beyond end of file")
        if macro in ("lref", "lrefx") and name and line <= len(lines):
            check(name_at_line(lines, name, line),
                  f"paper \\{macro}: {name} not at {rel}:{line} (±{LINE_WINDOW})")

    # --- 5. SCOPE.md ----------------------------------------------------------
    scope = read(ROOT / "SCOPE.md")
    declared = {nc["id"] for nc in data["non_claims"]}
    listed = set(re.findall(r"`(not_[a-z0-9_]+)`", scope))
    check(declared == listed,
          f"SCOPE.md identifiers {sorted(listed)} != claims.json {sorted(declared)}")
    check("does not prove" in scope,
          "SCOPE.md must state the open boundary in plain language")

    # --- 6. README ------------------------------------------------------------
    readme = read(ROOT / "README.md")
    for claim in data["claims"]:
        if claim.get("readme_headline"):
            first = claim["declarations"][0]["name"] if claim["declarations"] else None
            if first:
                check(first in readme,
                      f"README missing headline declaration {first} ({claim['id']})")
    check(tag in readme, f"README does not state the release tag {tag}")
    check("does not solve" in readme, "README must state the open boundary in plain language")
    check("METHODOLOGY.md" in readme and "docs/methodology.json" in readme,
          "README must route to the human and machine-readable methodology")
    leaked_identifier = re.search(r"method_axiom\.|anti_principle\.|principle\.[a-z_]|transition\.[a-z_]", readme)
    check(leaked_identifier is None,
          f"README leaks a methodology machine identifier: {leaked_identifier.group(0) if leaked_identifier else ''}")
    for phrase in README_BANNED_PHRASES:
        check(phrase not in readme, f"README contains banned drift phrase: {phrase!r}")
    for status in re.findall(r"\|\s*\*\*([a-z][a-z ]+)\*\*\s*\|", readme):
        check(status in taxonomy,
              f"README status table uses {status!r}, which is not in the taxonomy")

    # --- 7. licensing -----------------------------------------------------------
    import os

    # REUSE-IgnoreStart — the strings below are scanner patterns, not licence tags.
    reuse = read(ROOT / "REUSE.toml")
    spdx_ids = set(re.findall(r'SPDX-License-Identifier\s*=\s*"([^"]+)"', reuse))
    for dirpath, dirnames, filenames in os.walk(ROOT):
        dirnames[:] = [d for d in dirnames if d not in (".lake", ".git", "LICENSES")]
        for fname in filenames:
            path = Path(dirpath) / fname
            try:
                head = path.read_text(encoding="utf-8", errors="ignore")[:2000]
            except OSError:
                continue
            spdx_ids.update(re.findall(r"SPDX-License-Identifier: ([A-Za-z0-9.\-]+)", head))
    # REUSE-IgnoreEnd
    for lic in sorted(spdx_ids):
        check((ROOT / "LICENSES" / f"{lic}.txt").is_file(),
              f"licence {lic} is used but LICENSES/{lic}.txt is missing")

    # --- 8. agent entry ------------------------------------------------------------
    agents = read(ROOT / "AGENTS.md")
    for required in (
        "docs/claims.json",
        "docs/corpus_descriptor.json",
        "docs/methodology.json",
        "METHODOLOGY.md",
        "SCOPE.md",
        "Erdos249257.lean",
        "scripts/check_release.py",
    ):
        check(required in agents, f"AGENTS.md does not route through {required}")
    check("remain open" in agents, "AGENTS.md must preserve the open-problem boundary")
    check("proof authority" in agents, "AGENTS.md must state the proof-authority boundary")

    methodology_check = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "build_methodology.py"), "--check"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(methodology_check.returncode == 0,
          f"methodology projection drift: {methodology_check.stdout.strip() or methodology_check.stderr.strip()}")

    module_graph_check = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "build_module_graph.py"), "--check"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(module_graph_check.returncode == 0,
          f"module graph drift: {module_graph_check.stdout.strip() or module_graph_check.stderr.strip()}")

    atlas_check = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "build_declaration_atlas.py"), "--check"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(atlas_check.returncode == 0,
          f"declaration atlas drift: {atlas_check.stdout.strip() or atlas_check.stderr.strip()}")

    coordinate_check = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "refresh_source_coordinates.py"), "--check"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(coordinate_check.returncode == 0,
          f"source-coordinate drift: {coordinate_check.stdout.strip() or coordinate_check.stderr.strip()}")

    corpus_check = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "build_corpus_descriptor.py"), "--check"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(corpus_check.returncode == 0,
          f"corpus descriptor drift: {corpus_check.stdout.strip() or corpus_check.stderr.strip()}")

    descriptor = json.loads(read(ROOT / "docs" / "corpus_descriptor.json"))
    check(descriptor.get("schema") == "erdos249257-corpus-descriptor/2",
          "corpus descriptor must use schema erdos249257-corpus-descriptor/2")
    methodology_content = descriptor.get("identity", {}).get("content", {}).get("methodology_contract", {})
    check(methodology_content.get("path") == "docs/methodology.json",
          "corpus descriptor does not register docs/methodology.json")
    check(descriptor.get("schemas", {}).get("methodology") == methodology.get("schema"),
          "corpus descriptor methodology schema does not match docs/methodology.json")
    methodology_capsule = descriptor.get("compact_graph", {}).get("methodology_capsule", {})
    check(methodology_capsule.get("human_capsule") == methodology.get("human_capsule"),
          "corpus descriptor methodology capsule drifted from docs/methodology.json")
    check(methodology_capsule.get("change_classes") == methodology.get("change_classes"),
          "corpus descriptor methodology capsule does not carry the change-class matrix")

    # --- 9. proof-trust guard ------------------------------------------------------
    # Covers the library, its root, and the downstream examples: everything
    # shipped as Lean source obeys the same no-sorry/no-axiom contract.
    trust_re = re.compile(r"^\s*(sorry\b|admit\b|axiom\s)|native_decide", re.M)
    example_sources = sorted((ROOT / "examples").rglob("*.lean")) if (ROOT / "examples").is_dir() else []
    for lean in sorted((ROOT / "Erdos249257").rglob("*.lean")) + [ROOT / "Erdos249257.lean"] + example_sources:
        m = trust_re.search(lean_code_without_comments_and_strings(read(lean)))
        check(m is None,
              f"proof-trust violation in {lean.relative_to(ROOT)}: {m.group(0).strip() if m else ''}")

    # --- report ---------------------------------------------------------------------
    if ERRORS:
        print(f"check_release: {len(ERRORS)} failure(s) across {CHECKS} checks")
        for err in ERRORS:
            print(f"  FAIL {err}")
        return 1
    print(f"check_release: all {CHECKS} checks passed for release {tag}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
