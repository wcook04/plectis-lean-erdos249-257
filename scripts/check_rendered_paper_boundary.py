#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep implementation coordinates out of the human-facing papers.

The authored TeX deliberately retains exact Lean coordinates inside hyperlink
arguments so release tooling can validate them.  The printed papers should
show only a quiet source mark, never theorem identifiers, module names, source
paths, registry paths, or commit hashes.

Run from the repository root:

    python3 scripts/check_rendered_paper_boundary.py

The full check extracts text from both PDFs with ``pdftotext``.  The
``--source-only`` mode checks the TeX rendering contract without requiring
Poppler and is suitable for the stdlib-only release gate.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPERS = (
    (
        ROOT / "paper" / "erdos249-257-exposition.tex",
        ROOT / "erdos249-257-exposition.pdf",
    ),
    (
        ROOT / "paper" / "erdos249-transport-curvature.tex",
        ROOT / "erdos249-transport-curvature.pdf",
    ),
)
ALIASES = ROOT / "paper" / "module-aliases.json"

LINK_MACRO_RE = re.compile(
    r"""\\(?:lref|lrefx)\{[^{}]*\}\{[^{}]*\}\{[^{}]*\}
        |\\lloc\{[^{}]*\}\{[^{}]*\}""",
    re.X,
)
COMMENT_RE = re.compile(r"(?<!\\)%.*$")
HIDDEN_RE = re.compile(r"\\iffalse.*?\\fi", re.S)
NEWCOMMAND_RE = re.compile(r"^\s*\\newcommand.*$", re.M)
LEAN_IDENTIFIER_RE = re.compile(
    r"\b[A-Za-z][A-Za-z0-9]*(?:_[A-Za-z0-9]+)+\b"
)
VISIBLE_PATH_RE = re.compile(
    r"\b[A-Za-z0-9_./-]+\.(?:lean|json|py|md)\b",
    re.I,
)
COMMIT_RE = re.compile(r"\b[0-9a-f]{40}\b", re.I)


def visible_tex(text: str) -> str:
    """Approximate the material that can contribute visible prose."""
    text = "\n".join(COMMENT_RE.sub("", line) for line in text.splitlines())
    text = HIDDEN_RE.sub("", text)
    text = LINK_MACRO_RE.sub("", text)
    return NEWCOMMAND_RE.sub("", text)


def source_errors(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    visible = visible_tex(text)
    errors: list[str] = []

    if r"\newcommand{\sourceglyph}" not in text:
        errors.append("missing the quiet source-glyph definition")
    for macro in ("lref", "lrefx", "lloc"):
        definitions = re.findall(
            rf"\\newcommand\{{\\{macro}\}}.*$", text, flags=re.M
        )
        if definitions and any(r"\sourceglyph" not in row for row in definitions):
            errors.append(f"\\{macro} renders something other than the source glyph")
    if r"\modulesigil" in "\n".join(
        re.findall(r"\\newcommand\{\\(?:lref|lrefx|lloc)\}.*$", text, flags=re.M)
    ):
        errors.append("a paper link macro still prints a module sigil")
    if r"\idn{" in visible:
        errors.append("visible TeX still prints a Lean identifier")
    if r"\rref{" in visible:
        errors.append("visible TeX still prints a repository path")

    for pattern, label in (
        (VISIBLE_PATH_RE, "implementation path"),
        (COMMIT_RE, "full commit hash"),
    ):
        match = pattern.search(visible)
        if match:
            errors.append(f"visible TeX contains {label}: {match.group(0)!r}")
    return [f"{path.relative_to(ROOT)}: {error}" for error in errors]


def rendered_text(pdf: Path, pdftotext: str) -> str:
    completed = subprocess.run(
        [pdftotext, str(pdf), "-"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or "pdftotext failed"
        raise RuntimeError(f"{pdf.relative_to(ROOT)}: {detail}")
    return completed.stdout


def rendered_errors(pdf: Path, text: str, aliases: dict[str, object]) -> list[str]:
    errors: list[str] = []
    compact = re.sub(r"\s+", " ", text)

    fixed_terms = (
        "docs/claims.json",
        "scripts/check_release.py",
        "METHODOLOGY.md",
        "lake-manifest.json",
        "native_decide",
        "Erdos249257/",
    )
    for term in fixed_terms:
        if term.lower() in compact.lower():
            errors.append(f"prints internal term {term!r}")

    for match in VISIBLE_PATH_RE.finditer(compact):
        errors.append(f"prints implementation path {match.group(0)!r}")
    for match in COMMIT_RE.finditer(compact):
        errors.append(f"prints full commit hash {match.group(0)!r}")
    for match in LEAN_IDENTIFIER_RE.finditer(compact):
        errors.append(f"prints Lean-style identifier {match.group(0)!r}")

    alias_rows = aliases.get("aliases", [])
    if isinstance(alias_rows, list):
        for row in alias_rows:
            if not isinstance(row, dict):
                continue
            sigil = row.get("sigil")
            module = row.get("module")
            terms = []
            if isinstance(sigil, str) and len(sigil) >= 6:
                terms.append(sigil)
            if isinstance(module, str):
                stem = module.rsplit("/", 1)[-1].removesuffix(".lean")
                if len(stem) >= 8:
                    terms.append(stem)
            for term in terms:
                if re.search(rf"\b{re.escape(term)}\b", compact):
                    errors.append(f"prints source-module name or sigil {term!r}")

    return [f"{pdf.relative_to(ROOT)}: {error}" for error in sorted(set(errors))]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--source-only",
        action="store_true",
        help="check only the TeX rendering contract; do not inspect PDFs",
    )
    args = parser.parse_args()

    errors = [error for tex, _pdf in PAPERS for error in source_errors(tex)]
    if not args.source_only:
        pdftotext = shutil.which("pdftotext")
        if pdftotext is None:
            errors.append("pdftotext is required for the rendered-paper check")
        else:
            aliases = json.loads(ALIASES.read_text(encoding="utf-8"))
            for _tex, pdf in PAPERS:
                if not pdf.is_file():
                    errors.append(f"{pdf.relative_to(ROOT)}: rendered paper is missing")
                    continue
                try:
                    text = rendered_text(pdf, pdftotext)
                except RuntimeError as error:
                    errors.append(str(error))
                    continue
                errors.extend(rendered_errors(pdf, text, aliases))

    if errors:
        print(f"check_rendered_paper_boundary: {len(errors)} failure(s)")
        for error in errors:
            print(f"  FAIL {error}")
        return 1

    mode = "source contract" if args.source_only else "source contract and rendered PDFs"
    print(f"check_rendered_paper_boundary: {mode} passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
