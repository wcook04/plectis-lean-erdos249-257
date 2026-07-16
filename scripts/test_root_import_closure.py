#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Verify that the supported root import reaches every public Lean module."""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
IMPORT_RE = re.compile(r"^import (Erdos249257(?:\.[A-Za-z0-9_]+)+)\s*$", re.M)


def closure_errors(nodes: list[dict[str, object]], root_imports: list[str]) -> list[str]:
    """Return identity, missing-edge, and orphan errors for a public import graph."""
    module_ids = [str(node["id"]) for node in nodes]
    duplicate_ids = sorted(
        module_id for module_id in set(module_ids) if module_ids.count(module_id) > 1
    )
    errors = [
        f"machine-readable module graph contains duplicate id: {module_id}"
        for module_id in duplicate_ids
    ]
    imports_by_id = {str(node["id"]): list(node["imports"]) for node in nodes}
    for importer, imports in [("Erdos249257", root_imports), *imports_by_id.items()]:
        for imported in imports:
            if imported not in imports_by_id:
                errors.append(f"{importer} imports unknown public module {imported}")

    reachable: set[str] = set()
    pending = list(root_imports)
    while pending:
        module = pending.pop()
        if module in reachable or module not in imports_by_id:
            continue
        reachable.add(module)
        pending.extend(imports_by_id[module])
    for module in sorted(set(imports_by_id) - reachable):
        errors.append(f"public module is outside supported root-import closure: {module}")
    return errors


def check_fixtures() -> None:
    connected = [
        {"id": "Erdos249257.A", "imports": ["Erdos249257.B"]},
        {"id": "Erdos249257.B", "imports": []},
    ]
    assert closure_errors(connected, ["Erdos249257.A"]) == []

    orphaned = [*connected, {"id": "Erdos249257.Orphan", "imports": []}]
    assert closure_errors(orphaned, ["Erdos249257.A"]) == [
        "public module is outside supported root-import closure: Erdos249257.Orphan"
    ]

    missing = [{"id": "Erdos249257.A", "imports": ["Erdos249257.Missing"]}]
    assert closure_errors(missing, ["Erdos249257.A"]) == [
        "Erdos249257.A imports unknown public module Erdos249257.Missing"
    ]

    duplicate = [
        {"id": "Erdos249257.A", "imports": []},
        {"id": "Erdos249257.A", "imports": []},
    ]
    assert closure_errors(duplicate, ["Erdos249257.A"]) == [
        "machine-readable module graph contains duplicate id: Erdos249257.A"
    ]


def main() -> int:
    check_fixtures()
    claims = json.loads((ROOT / "docs" / "claims.json").read_text(encoding="utf-8"))
    graph = claims["machine_readable_paper"]["module_graph"]
    assert graph["root"] == "Erdos249257.lean"
    root_imports = IMPORT_RE.findall((ROOT / graph["root"]).read_text(encoding="utf-8"))
    errors = closure_errors(graph["nodes"], root_imports)
    assert not errors, "\n".join(errors)
    print(
        "test_root_import_closure: supported root reaches "
        f"all {len(graph['nodes'])} public Lean modules"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
