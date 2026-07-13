#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the human scope boundary aligned with the formal-source contract."""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    claims = json.loads((ROOT / "docs" / "claims.json").read_text(encoding="utf-8"))
    formal_source = claims["release"]["formal_source"]
    scope = (ROOT / "SCOPE.md").read_text(encoding="utf-8")

    assert re.fullmatch(r"[0-9a-f]{40}", formal_source["ref"])
    assert formal_source["ref_kind"] == "commit"
    assert formal_source["relationship_to_last_tag"] in {"at_last_tag", "post_tag_checkpoint"}
    assert "immutable\nformal-source checkpoint" in scope
    assert "citation and release identity" in scope
    assert "not a substitute for an exact proof-source identity" in scope
    assert "until it is included in a new tagged\nrelease" not in scope

    print("test_scope_source_identity: scope separates release tag and formal-source checkpoint")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
