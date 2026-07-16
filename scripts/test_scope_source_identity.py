#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the human scope boundary aligned with the formal-source contract."""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent


def scope_open_route_errors(scope: str, open_ids: set[str]) -> list[str]:
    """Require every registered open proposition to remain directly queryable."""
    errors: list[str] = []
    for open_id in sorted(open_ids):
        if f"`{open_id}`" not in scope:
            errors.append(f"SCOPE.md lost exact open identifier {open_id}")
        command = f"python3 scripts/query_corpus.py --open {open_id}"
        if command not in scope:
            errors.append(f"SCOPE.md lost bounded open query {command}")
    for phrase in (
        "Finite instances, conditional reductions, cited neighbours, and named",
        "do not discharge these propositions",
        "required by `docs/methodology.json`",
    ):
        if phrase not in scope:
            errors.append(f"SCOPE.md lost open-transition boundary: {phrase}")
    return errors


def main() -> int:
    claims = json.loads((ROOT / "docs" / "claims.json").read_text(encoding="utf-8"))
    formal_source = claims["release"]["formal_source"]
    open_ids = {row["id"] for row in claims["remaining_open_propositions"]}
    scope = (ROOT / "SCOPE.md").read_text(encoding="utf-8")

    assert re.fullmatch(r"[0-9a-f]{40}", formal_source["ref"])
    assert formal_source["ref_kind"] == "commit"
    assert formal_source["relationship_to_last_tag"] in {"at_last_tag", "post_tag_checkpoint"}
    assert "immutable\nformal-source checkpoint" in scope
    assert "citation and release identity" in scope
    assert "not a substitute for an exact proof-source identity" in scope
    assert "until it is included in a new tagged\nrelease" not in scope
    assert not scope_open_route_errors(scope, open_ids)

    missing_open = scope.replace(
        "python3 scripts/query_corpus.py --open "
        "remaining_open.universal_257_all_infinite_supports",
        "",
        1,
    )
    assert any(
        "lost bounded open query" in error
        for error in scope_open_route_errors(missing_open, open_ids)
    )
    weakened_transition = scope.replace(
        "do not discharge these propositions",
        "are enough to discharge these propositions",
        1,
    )
    assert any(
        "lost open-transition boundary" in error
        for error in scope_open_route_errors(weakened_transition, open_ids)
    )

    print(
        "test_scope_source_identity: scope separates release identity, proof "
        "checkpoint, and 3 exact open propositions; 2 negative fixtures rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
