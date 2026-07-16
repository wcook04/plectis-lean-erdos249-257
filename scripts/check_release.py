#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Cross-surface release checker.

The single owner of release identity and claim status is docs/claims.json.
This script verifies that every other public surface agrees with it:

  1. claims.json is well formed, every claim status is in the taxonomy, typed
     remaining-open propositions resolve, and the machine-readable paper graph
     resolves to real public files and claim ids.
  2. Release identity: lakefile.toml and CITATION.cff state the last tagged
     release, while the main exposition pin agrees with the exact committed
     formal-source checkpoint named in the registry.
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
  9. Proof-trust guard: no sorry/admit/axiom or native evaluator in the
     Lean sources.
 10. The methodology source, generated root projection, claim-transition
     requirements, descriptor capsule, and entry routes agree.
Stdlib only; run from the repository root:  python3 scripts/check_release.py
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

from methodology_contract import mutation_fixture_errors, render_markdown, validate_contract
from query_corpus import paper_anchor_inventory

ROOT = Path(__file__).resolve().parent.parent
ERRORS: list[str] = []
CHECKS = 0

LINE_WINDOW = 3  # declaration name must appear within this many lines of the stated line
MAX_ROUTE_FIRST_CONTACT_BYTES = 48_000

README_BANNED_PHRASES = [
    "Ramanujan Machine Challenge",
    "publication status",
    "ai_workflow` is a private",
]

PROOF_TRUST_RE = re.compile(
    r"^\s*(?:sorry\b|admit\b|axiom\s)"
    r"|native_decide"
    r"|\bdecide[^\n]*(?:\+native\b|native\s*:=\s*true\b)",
    re.M,
)


def fail(msg: str) -> None:
    ERRORS.append(msg)


def check(ok: bool, msg: str) -> None:
    global CHECKS
    CHECKS += 1
    if not ok:
        fail(msg)


def file_digest(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def module_lines(
    cache: dict[tuple[str, str | None], list[str] | None],
    rel: str,
    source_ref: str | None = None,
) -> list[str] | None:
    """Read a module from the worktree or from the exact pinned Git tree."""
    key = (rel, source_ref)
    if key not in cache:
        if source_ref is None:
            path = ROOT / rel
            cache[key] = read(path).splitlines() if path.is_file() else None
        else:
            completed = subprocess.run(
                ["git", "show", f"{source_ref}:{rel}"],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            cache[key] = completed.stdout.splitlines() if completed.returncode == 0 else None
    return cache[key]


def formal_source_matches_current_lean_tree(formal_ref: str) -> tuple[bool, str]:
    """Whether the current public proof sources are exactly ``formal_ref``.

    The source checkpoint owns the declarations named by the claim registry.
    Checking a declaration only with ``git show <formal_ref>:...`` is necessary,
    but it is not sufficient when a later Lean edit is present in the worktree:
    that would verify an older source while presenting the current tree.  The
    public root and library directory are the supported proof surface; papers,
    generated navigation, and release metadata may legitimately advance after
    that checkpoint.
    """
    proof_paths = ("Erdos249257.lean", "Erdos249257")
    comparison = subprocess.run(
        ["git", "diff", "--quiet", formal_ref, "--", *proof_paths],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if comparison.returncode not in (0, 1):
        return False, comparison.stderr.strip() or "could not compare formal source to worktree"
    untracked = subprocess.run(
        ["git", "ls-files", "--others", "--exclude-standard", "--", *proof_paths],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if untracked.returncode != 0:
        return False, untracked.stderr.strip() or "could not inspect untracked Lean sources"
    extras = [line for line in untracked.stdout.splitlines() if line.endswith(".lean")]
    if comparison.returncode == 0 and not extras:
        return True, ""
    detail = "current public Lean sources differ from formal-source checkpoint"
    if extras:
        detail += "; untracked Lean source(s): " + ", ".join(extras)
    return False, detail


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


def proof_trust_violation(text: str) -> str | None:
    """Return the first executable proof-trust violation, if any."""
    # Most source files contain none of the four candidate words.  Avoid the
    # character-by-character comment/string pass for that overwhelmingly
    # common case; candidate-bearing files still receive the exact scan.
    if PROOF_TRUST_RE.search(text) is None:
        return None
    match = PROOF_TRUST_RE.search(lean_code_without_comments_and_strings(text))
    return match.group(0).strip() if match else None


def check_proof_trust() -> None:
    """Run the cheap proof-trust gate before any expensive release checks."""
    # Pin the lexical boundary: prose and strings are harmless, executable
    # native reduction is not.  These fixtures keep future scanner edits from
    # silently weakening or over-broadening the release contract.
    check(proof_trust_violation("theorem bad : True := by native_decide\n") == "native_decide",
          "proof-trust scanner must reject executable native reduction")
    check(proof_trust_violation("theorem bad : True := by decide +native\n") == "decide +native",
          "proof-trust scanner must reject the native decide alias")
    check(proof_trust_violation(
        "theorem bad : True := by decide (config := { native := true })\n"
    ) == "decide (config := { native := true",
          "proof-trust scanner must reject native evaluation through configuration")
    check(proof_trust_violation("/- native_decide -/\ntheorem ok : True := by trivial\n") is None,
          "proof-trust scanner must ignore comments")
    check(proof_trust_violation('def label := "native_decide"\n') is None,
          "proof-trust scanner must ignore strings")
    example_sources = sorted((ROOT / "examples").rglob("*.lean")) if (ROOT / "examples").is_dir() else []
    lean_sources = (
        sorted((ROOT / "Erdos249257").rglob("*.lean"))
        + [ROOT / "Erdos249257.lean"]
        + example_sources
    )
    for lean in lean_sources:
        violation = proof_trust_violation(read(lean))
        check(violation is None,
              f"proof-trust violation in {lean.relative_to(ROOT)}: {violation or ''}")


def main() -> int:
    cache: dict[tuple[str, str | None], list[str] | None] = {}

    # Fail fast on the cheapest high-severity invariant.  In particular, do
    # not spend the corpus-query budget before rejecting untrusted proof code.
    check_proof_trust()
    if ERRORS:
        print(f"check_release: {len(ERRORS)} proof-trust failure(s) across {CHECKS} checks")
        for err in ERRORS:
            print(f"  FAIL {err}")
        return 1

    # --- 1. claims.json ---------------------------------------------------
    claims_path = ROOT / "docs" / "claims.json"
    data = json.loads(read(claims_path))
    check(data.get("schema") == "erdos249257-claims/3",
          "docs/claims.json must use schema erdos249257-claims/3")
    taxonomy = set(data["status_taxonomy"])
    release = data["release"]
    version, tag = release["version"], release["tag"]
    check(tag == f"v{version}", f"release tag {tag} does not match version {version}")
    formal_source = release.get("formal_source")
    check(isinstance(formal_source, dict), "release must name a formal_source checkpoint")
    formal_ref = formal_source.get("ref") if isinstance(formal_source, dict) else None
    check(isinstance(formal_ref, str) and re.fullmatch(r"[0-9a-f]{40}", formal_ref or "") is not None,
          "release.formal_source.ref must be a full lowercase Git commit id")
    if isinstance(formal_source, dict):
        check(formal_source.get("ref_kind") == "commit",
              "release.formal_source.ref_kind must be 'commit'")
        check(formal_source.get("publication_state") in {
            "committed_checkpoint_pending_remote_publication",
            "published_committed_checkpoint",
        }, "release.formal_source has an unsupported publication_state")
        check(formal_source.get("relationship_to_last_tag") in {
            "at_last_tag", "post_tag_checkpoint",
        }, "release.formal_source has an unsupported relationship_to_last_tag")
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
    exhaustive_route_reads = {"docs/claims.json", "docs/declaration_atlas.json", "docs/methodology.json"}
    for route in machine_paper["entrypoints"]:
        check(bool(route.get("id")) and bool(route.get("intent")) and bool(route.get("read")),
              "every machine-readable-paper entrypoint needs id, intent, and read paths")
        check(bool(route.get("query_steps")) and bool(route.get("authority_owners"))
              and bool(route.get("adjacent_handle_classes")),
              f"route {route.get('id')!r} lacks bounded query, authority-owner, or adjacent-handle data")
        check(not (set(route.get("read", [])) & exhaustive_route_reads),
              f"route {route.get('id')!r} sends first contact to an exhaustive owner")
        first_contact_bytes = 0
        for rel in route.get("read", []):
            path = ROOT / rel
            check(path.is_file(), f"machine-readable-paper entrypoint path does not exist: {rel}")
            if path.is_file():
                first_contact_bytes += path.stat().st_size
        check(first_contact_bytes <= MAX_ROUTE_FIRST_CONTACT_BYTES,
              f"route {route.get('id')!r} first-contact bundle is {first_contact_bytes} bytes "
              f"(budget {MAX_ROUTE_FIRST_CONTACT_BYTES})")
        for owner in route.get("authority_owners", []):
            rel = str(owner).split("::", 1)[0]
            check((ROOT / rel).is_file(),
                  f"route {route.get('id')!r} authority owner does not exist: {rel}")
        for step in route.get("query_steps", []):
            check(step.startswith("python3 scripts/query_corpus.py --"),
                  f"route {route.get('id')!r} query step is not a typed corpus query: {step}")

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

    main_paper_row = machine_paper["paper"]
    paper_rows = [main_paper_row, *main_paper_row.get("companion_sources", [])]
    paper_sources = [(row["source"], read(ROOT / row["source"])) for row in paper_rows]
    paper = paper_sources[0][1]
    all_paper = "\n".join(text for _path, text in paper_sources)
    check(subprocess.run(["git", "rev-parse", "--verify", f"{formal_ref}^{{commit}}"], cwd=ROOT,
                         capture_output=True, text=True, check=False).returncode == 0,
          f"release.formal_source.ref {formal_ref!r} does not resolve to a local commit")
    formal_tree_matches, formal_tree_detail = formal_source_matches_current_lean_tree(formal_ref)
    check(formal_tree_matches,
          formal_tree_detail or "current public Lean sources differ from formal-source checkpoint")
    for paper_path, paper_text in paper_sources:
        m = re.search(r"\\newcommand\{\\commit\}\{([^}]+)\}", paper_text)
        expected_pin = formal_ref
        check(m is not None and m.group(1) == expected_pin,
              f"{paper_path} \\commit pin {m.group(1) if m else '<missing>'} != expected {expected_pin}")
        if paper_path == main_paper_row["source"]:
            check(paper_text.count("blob/main") == 1 and "\\newcommand{\\rootbase}" in paper_text,
                  f"{paper_path} may use blob/main only for the explicit \\rref root-navigation base")
        else:
            check("blob/main" not in paper_text,
                  f"{paper_path} links a floating branch (blob/main)")
    for claim in data["claims"]:
        label = claim.get("paper_label")
        if label:
            check(re.search(rf"\\label\{{{re.escape(label)}\}}", all_paper) is not None,
                  f"claim {claim['id']}: paper label {label!r} does not exist")
    paper_anchors = paper_anchor_inventory()
    anchor_labels = [row["label"] for row in paper_anchors if row["label"]]
    check(len(anchor_labels) == len(set(anchor_labels)),
          "authored papers contain duplicate semantic-anchor labels")
    check(all(row.get("anchor_class") for row in paper_anchors),
          "every authored paper semantic anchor must have an explicit classification")
    check(all(
        row["anchor_class"] in {
            "registered_claim_anchor",
            "remaining_open_proposition_anchor",
            "authored_formal_anchor_without_registered_claim",
            "section_navigation_anchor",
        }
        for row in paper_anchors
    ), "authored paper semantic anchor has an unsupported classification")
    claim_ids_by_label: dict[str, set[str]] = {}
    for claim in data["claims"]:
        if claim.get("paper_label"):
            claim_ids_by_label.setdefault(claim["paper_label"], set()).add(claim["id"])
    for anchor in paper_anchors:
        observed_claim_ids = {row["id"] for row in anchor["attached_claims"]}
        expected_claim_ids = claim_ids_by_label.get(anchor["label"], set())
        check(observed_claim_ids == expected_claim_ids,
              f"paper anchor {anchor['canonical_handle']}: attached claim set drifted")
        observed_open_ids = {row["id"] for row in anchor["attached_open_propositions"]}
        expected_open_ids = {
            row["id"]
            for row in data["remaining_open_propositions"]
            if row.get("paper_anchor")
            and row["paper_anchor"]["source"] == anchor["paper"]["source"]
            and row["paper_anchor"]["environment"] == anchor["environment"]
            and row["paper_anchor"]["title"] == anchor["title"]
        }
        check(observed_open_ids == expected_open_ids,
              f"paper anchor {anchor['canonical_handle']}: open proposition set drifted")
        if anchor["environment"] == "problem":
            check(anchor["anchor_class"] == "remaining_open_proposition_anchor",
                  f"problem paper anchor {anchor['canonical_handle']} is not typed as remaining open")
        if anchor["anchor_kind"] == "formal_environment":
            check(anchor["anchor_class"] != "section_navigation_anchor",
                  f"formal paper anchor {anchor['canonical_handle']} classified as navigation-only")
    routed_open_ids = {
        row["id"]
        for anchor in paper_anchors
        for row in anchor["attached_open_propositions"]
    }
    check(routed_open_ids == {row["id"] for row in data["remaining_open_propositions"]},
          "every remaining-open proposition must resolve to exactly one authored problem anchor")
    index_label = machine_paper["paper"]["principal_declaration_index_label"]
    check(re.search(rf"\\label\{{{re.escape(index_label)}\}}", paper) is not None,
          f"machine-readable paper index label {index_label!r} does not exist")

    # --- 3. claimed declarations -------------------------------------------
    for claim in data["claims"]:
        for decl in claim["declarations"]:
            lines = module_lines(cache, decl["module"], formal_ref)
            if lines is None:
                fail(f"claim {claim['id']}: module {decl['module']} not found")
                continue
            check(name_at_line(lines, decl["name"], decl["line"]),
                  f"claim {claim['id']}: {decl['name']} not at "
                  f"{decl['module']}:{decl['line']} (±{LINE_WINDOW})")

    # --- 4. paper source links ----------------------------------------------
    for paper_path, paper_text in paper_sources:
        source_ref = formal_ref
        for macro, fname, line_s, name in re.findall(
                r"\\(lref|lrefx|lloc)\{([^}]+)\}\{(\d+)\}(?:\{([^}]*)\})?", paper_text):
            rel = f"Erdos249257/{fname}"
            lines = module_lines(cache, rel, source_ref)
            if lines is None:
                fail(f"{paper_path} \\{macro}: file {rel} not found at {source_ref}")
                continue
            line = int(line_s)
            check(line <= len(lines), f"{paper_path} \\{macro}: {rel}:{line} beyond end of file")
            if macro in ("lref", "lrefx") and name and line <= len(lines):
                check(name_at_line(lines, name, line),
                      f"{paper_path} \\{macro}: {name} not at {rel}:{line} (±{LINE_WINDOW})")

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
    check(tag in readme, f"README does not state the release tag {tag}")
    check("does not solve" in readme, "README must state the open boundary in plain language")
    check("METHODOLOGY.md" in readme and "SOURCE_MAP.md" in readme,
          "README must route readers to the methodology and source map")
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
        "docs/orientation.json",
        "docs/ORIENTATION.md",
        "docs/claims.json",
        "docs/corpus_descriptor.json",
        "docs/methodology.json",
        "METHODOLOGY.md",
        "SCOPE.md",
        "Erdos249257.lean",
        "scripts/check_release.py",
        "scripts/query_corpus.py",
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

    paper_alias_check = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "build_paper_module_aliases.py"), "--check"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(paper_alias_check.returncode == 0,
          f"paper module alias drift: {paper_alias_check.stdout.strip() or paper_alias_check.stderr.strip()}")
    boundary = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "check_rendered_paper_boundary.py"),
            "--source-only",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(
        boundary.returncode == 0,
        "human-facing paper boundary failed: "
        f"{boundary.stdout.strip() or boundary.stderr.strip()}",
    )

    descriptor = json.loads(read(ROOT / "docs" / "corpus_descriptor.json"))
    check(descriptor.get("schema") == "erdos249257-corpus-descriptor/3",
          "corpus descriptor must use schema erdos249257-corpus-descriptor/3")
    descriptor_path = ROOT / "docs" / "corpus_descriptor.json"
    check(len(descriptor_path.read_bytes()) <= 64_000,
          "corpus descriptor exceeds the 64 KB registration-envelope budget")
    compact_graph = descriptor.get("compact_graph", {})
    check("module_graph" not in compact_graph and "high_salience_declarations" not in compact_graph,
          "corpus descriptor re-embedded an exhaustive graph removed in schema 3")
    module_topology = compact_graph.get("module_topology", {})
    check(module_topology.get("node_count") == len(machine_paper["module_graph"]["nodes"]),
          "corpus descriptor module count drifted from the machine-readable paper")
    check(module_topology.get("full_graph") == "docs/claims.json::machine_readable_paper.module_graph",
          "corpus descriptor does not route to the complete module graph")
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
    descriptor_content = descriptor.get("identity", {}).get("content", {})
    paper_aliases = json.loads(read(ROOT / "paper" / "module-aliases.json"))
    paper_artifacts = {
        "human_exposition": (
            "paper/erdos249-257-exposition.tex",
            "erdos249-257-exposition.pdf",
        ),
        "technical_companion": (
            "paper/erdos249-transport-curvature.tex",
            "erdos249-transport-curvature.pdf",
        ),
    }
    for content_id, (source_path, rendered_path) in paper_artifacts.items():
        content = descriptor_content.get(content_id, {})
        check(content.get("source_path") == source_path,
              f"corpus descriptor {content_id} source path is missing or incorrect")
        check(content.get("rendered_path") == rendered_path,
              f"corpus descriptor {content_id} rendered path is missing or incorrect")
        check(content.get("source_content_digest") == file_digest(ROOT / source_path),
              f"corpus descriptor {content_id} source digest drifted")
        check(content.get("rendered_content_digest") == file_digest(ROOT / rendered_path),
              f"corpus descriptor {content_id} rendered digest drifted")
        check(content.get("authority_posture") == "authored_editorial_surface_not_Lean_proof_authority",
              f"corpus descriptor {content_id} does not preserve the proof-authority boundary")
    sigils = descriptor_content.get("paper_source_sigils", {})
    check(sigils.get("path") == "paper/module-aliases.json",
          "corpus descriptor does not register the paper source-sigil crosswalk")
    check(sigils.get("content_digest") == file_digest(ROOT / "paper" / "module-aliases.json"),
          "corpus descriptor paper source-sigil digest drifted")
    check(descriptor.get("schemas", {}).get("paper_module_aliases") == paper_aliases.get("schema"),
          "corpus descriptor paper source-sigil schema drifted")

    orientation_path = ROOT / "docs" / "orientation.json"
    orientation = json.loads(read(orientation_path))
    declaration_atlas = json.loads(read(ROOT / "docs" / "declaration_atlas.json"))
    check(orientation.get("schema") == "erdos249257-orientation/1",
          "orientation projection must use schema erdos249257-orientation/1")
    check(orientation.get("scale") == declaration_atlas.get("summary"),
          "orientation scale drifted from the declaration atlas")
    expected_principal_ids = [
        claim["id"] for claim in data["claims"] if claim.get("readme_headline")
    ]
    actual_principal_ids = [
        claim.get("id") for claim in orientation.get("principal_claims", [])
    ]
    check(actual_principal_ids == expected_principal_ids,
          "orientation principal claims drifted from README-headline claims")
    check(len(orientation_path.read_bytes()) <= 32_000,
          "orientation JSON exceeds the 32 KB bounded first-read budget")
    for target in orientation.get("drilldowns", {}).values():
        rel = str(target).split("::", 1)[0]
        check((ROOT / rel).is_file(), f"orientation drilldown path does not exist: {rel}")
    query_check = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "test_query_corpus.py")],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(query_check.returncode == 0,
          f"corpus query surface failed: {query_check.stdout.strip() or query_check.stderr.strip()}")
    # The adversarial program starts by running the complete baseline against
    # one collected packet set, then mutates that same set.  Running the
    # standalone diagnostic here as well would repeat every bounded query.
    # Keep the diagnostic as a user-facing command, but execute the combined
    # baseline-plus-adversarial program once in the release gate.
    cold_clone_adversarial = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "test_cold_clone_comprehension.py")],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    check(cold_clone_adversarial.returncode == 0,
          "bounded cold-clone baseline/adversarial check failed: "
          f"{cold_clone_adversarial.stdout.strip() or cold_clone_adversarial.stderr.strip()}")

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
