#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep implementation coordinates exact but visually subordinate in the papers.

The authored TeX deliberately retains exact Lean coordinates inside hyperlink
arguments so release tooling can validate them.  A source link must print
ordinary mathematical words, not an indistinguishable glyph or a raw Lean
identifier.  Module names, source paths, registry paths, commit hashes, and
unlinked Lean identifiers remain outside the rendered narrative.

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
        ROOT / "paper" / "erdos249-257-main-paper.tex",
        ROOT / "erdos249-257-main-paper.pdf",
    ),
)
ARCHITECTURE_PAPERS = (
    ROOT / "claim-faithful-publication-systems-paper.pdf",
)
ALIASES = ROOT / "paper" / "module-aliases.json"
FIRST_MINUTE_CONTRACT = {
    "erdos249-257-main-paper.pdf": {
        (1, 1): (
            "q > q0",
            "full support in every base",
            "would refute the universal statement",
            "neither problem is settled",
            "an unbounded certificate supply",
            "cofinal terminal zeros",
        ),
        (2, 2): (
            "an exact certificate normal form",
            "the exact half-value counterexample spine",
            "a finite normalised support cannot have value 1/2",
            "no unbounded supply is proved",
        ),
    },
    "claim-faithful-publication-systems-paper.pdf": {
        (1, 2): (
            "this document explains how one public mathematics repository is organised",
            "both problems remain open",
            "the repository addresses this gap with five visible parts",
            "the architecture in one picture",
            "docs/claims.json",
            "scripts/check_release.py",
            ".github/workflows/lean.yml",
            "lean checks the formal proofs",
        ),
    },
}

LINK_MACRO_RE = re.compile(
    r"""\\lword\{[^{}]*\}\{[^{}]*\}\{[^{}]*\}\{[^{}]*\}
        |\\(?:lref|lrefx)\{[^{}]*\}\{[^{}]*\}\{[^{}]*\}
        |\\lloc\{[^{}]*\}\{[^{}]*\}""",
    re.X,
)
COMMENT_RE = re.compile(r"(?<!\\)%.*$")
HIDDEN_RE = re.compile(r"\\iffalse.*?\\fi", re.S)
NEWCOMMAND_RE = re.compile(r"^\s*\\newcommand.*$", re.M)
VISIBLE_PATH_RE = re.compile(
    r"\b[A-Za-z0-9_./-]+\.(?:lean|json|py|md)\b",
    re.I,
)
COMMIT_RE = re.compile(r"\b[0-9a-f]{40}\b", re.I)
LEAN_IDENTIFIER_RE = re.compile(r"\b[A-Za-z][A-Za-z0-9]*_[A-Za-z0-9_]{8,}\b")


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

    if r"\newcommand{\sourceglyph}" in text:
        errors.append("obsolete source-glyph definition is still present")
    gateway = path.name == "erdos249-257-main-paper.tex"
    for macro in ("lref", "lrefx"):
        definitions = re.findall(
            rf"\\newcommand\{{\\{macro}\}}.*$", text, flags=re.M
        )
        if gateway:
            if definitions and any(r"\leanlabel{#3}" not in row for row in definitions):
                errors.append(
                    f"\\{macro} does not print its theorem-specific declaration label"
                )
        elif definitions and any("{Lean proof}" not in row for row in definitions):
            errors.append(f"\\{macro} does not print the textual fallback 'Lean proof'")
    if gateway and r"\newcommand{\leanlabel}" not in text:
        errors.append(r"\leanlabel is missing from the gateway paper")
    lword_definitions = re.findall(r"\\newcommand\{\\lword\}.*$", text, flags=re.M)
    if lword_definitions and any("{#4}" not in row for row in lword_definitions):
        errors.append(r"\lword does not print its semantic label")
    lloc_definitions = re.findall(r"\\newcommand\{\\lloc\}.*$", text, flags=re.M)
    if lloc_definitions and any("{Lean source}" not in row for row in lloc_definitions):
        errors.append(r"\lloc does not print a distinguishable textual source link")
    if r"\modulesigil" in "\n".join(
        re.findall(
            r"\\newcommand\{\\(?:lref|lrefx|lword|lloc)\}.*$",
            text,
            flags=re.M,
        )
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


def rendered_pages(pdf: Path, pdftotext: str, first: int, last: int) -> str:
    completed = subprocess.run(
        [pdftotext, "-f", str(first), "-l", str(last), str(pdf), "-"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or "pdftotext failed"
        raise RuntimeError(
            f"{pdf.relative_to(ROOT)} pages {first}-{last}: {detail}"
        )
    return completed.stdout


def semantic_text(text: str) -> str:
    replacements = {
        "ﬁ": "fi",
        "ﬂ": "fl",
        "ﬀ": "ff",
        "ﬃ": "ffi",
        "ﬄ": "ffl",
        "−": "-",
        "–": "-",
        "—": "-",
    }
    for source, target in replacements.items():
        text = text.replace(source, target)
    return re.sub(r"\s+", " ", text).lower()


def first_minute_errors(pdf: Path, pdftotext: str) -> list[str]:
    errors: list[str] = []
    contract = FIRST_MINUTE_CONTRACT.get(pdf.name, {})
    for (first, last), anchors in contract.items():
        try:
            text = semantic_text(rendered_pages(pdf, pdftotext, first, last))
        except RuntimeError as error:
            errors.append(str(error))
            continue
        for anchor in anchors:
            if anchor not in text:
                errors.append(
                    f"{pdf.relative_to(ROOT)} pages {first}-{last}: "
                    f"missing first-minute anchor {anchor!r}"
                )
    return errors


def rendered_errors(
    pdf: Path,
    text: str,
    aliases: dict[str, object],
) -> list[str]:
    errors: list[str] = []
    compact = re.sub(r"_\s+(?=[a-z0-9])", "_", text)
    compact = re.sub(r"(?<=[a-z0-9])\s+_", "_", compact)
    compact = re.sub(r"\s+", " ", compact)

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
        errors.append(f"prints raw Lean identifier {match.group(0)!r}")
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


def architecture_rendered_errors(pdf: Path, text: str) -> list[str]:
    """Reject a rebuilt architecture paper that regresses to private scorekeeping."""
    compact = semantic_text(text)
    errors: list[str] = []
    banned = (
        re.compile(r"\bm(?:10|[1-9])\b"),
        re.compile(r"\b9/10\b"),
        re.compile(r"\b5,207\b"),
        re.compile(r"\bunbounded quantifier\b"),
    )
    for pattern in banned:
        if pattern.search(compact):
            errors.append(
                f"prints private or score-like shorthand {pattern.pattern!r}"
            )
    if len(re.findall(r"\bsentence\b", compact)) > 4:
        errors.append("has regressed to a sentence-centred case study")
    return [f"{pdf.relative_to(ROOT)}: {error}" for error in errors]


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
            for tex, pdf in PAPERS:
                if not pdf.is_file():
                    errors.append(f"{pdf.relative_to(ROOT)}: rendered paper is missing")
                    continue
                try:
                    text = rendered_text(pdf, pdftotext)
                except RuntimeError as error:
                    errors.append(str(error))
                    continue
                errors.extend(rendered_errors(pdf, text, aliases))
                errors.extend(first_minute_errors(pdf, pdftotext))
            for pdf in ARCHITECTURE_PAPERS:
                if not pdf.is_file():
                    errors.append(f"{pdf.relative_to(ROOT)}: rendered paper is missing")
                    continue
                try:
                    text = rendered_text(pdf, pdftotext)
                except RuntimeError as error:
                    errors.append(str(error))
                    continue
                errors.extend(architecture_rendered_errors(pdf, text))
                errors.extend(first_minute_errors(pdf, pdftotext))

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
