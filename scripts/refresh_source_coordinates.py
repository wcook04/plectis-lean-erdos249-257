#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Refresh claim and paper source lines from the declaration atlas.

Declaration names and module paths remain authored.  This script updates only
their line coordinates after a checked Lean-source change.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CLAIMS = ROOT / "docs" / "claims.json"
ATLAS = ROOT / "docs" / "declaration_atlas.json"
PAPER = ROOT / "paper" / "erdos249-257-exposition.tex"
LINK_RE = re.compile(r"\\(lrefx?)\{([^}]+)\}\{\d+\}\{([^}]+)\}")


def declaration_lines() -> dict[tuple[str, str], int]:
    atlas = json.loads(ATLAS.read_text(encoding="utf-8"))
    rows: dict[tuple[str, str], list[int]] = {}
    for decl in atlas["declarations"]:
        rows.setdefault((decl["module"], decl["name"]), []).append(decl["line"])
    duplicate = {key: values for key, values in rows.items() if len(values) != 1}
    if duplicate:
        raise RuntimeError(f"ambiguous declaration coordinates: {duplicate}")
    return {key: values[0] for key, values in rows.items()}


def render() -> tuple[str, str]:
    lines = declaration_lines()
    claims = json.loads(CLAIMS.read_text(encoding="utf-8"))
    for claim in claims["claims"]:
        for decl in claim["declarations"]:
            key = (decl["module"], decl["name"])
            if key not in lines:
                raise RuntimeError(f"claim declaration absent from atlas: {key}")
            decl["line"] = lines[key]

    paper = PAPER.read_text(encoding="utf-8")

    def replace(match: re.Match[str]) -> str:
        macro, filename, name = match.groups()
        key = (f"Erdos249257/{filename}", name)
        if key not in lines:
            raise RuntimeError(f"paper declaration absent from atlas: {key}")
        return f"\\{macro}{{{filename}}}{{{lines[key]}}}{{{name}}}"

    paper = LINK_RE.sub(replace, paper)
    return json.dumps(claims, ensure_ascii=False, indent=2) + "\n", paper


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    claims, paper = render()
    if args.check:
        stale = []
        if CLAIMS.read_text(encoding="utf-8") != claims:
            stale.append("docs/claims.json")
        if PAPER.read_text(encoding="utf-8") != paper:
            stale.append("paper/erdos249-257-exposition.tex")
        if stale:
            print("source coordinates are stale: " + ", ".join(stale))
            return 1
        print("source coordinates current")
        return 0
    CLAIMS.write_text(claims, encoding="utf-8")
    PAPER.write_text(paper, encoding="utf-8")
    print("refreshed claim and paper source coordinates")
    return 0


if __name__ == "__main__":
    sys.exit(main())
