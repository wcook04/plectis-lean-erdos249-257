#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check publication-artifact coverage, identity, routing, and evidence limits."""

from __future__ import annotations

import argparse
from pathlib import Path

from publication_contract import RepositoryReader, validate_publication_contract


ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--git-ref",
        help="validate a committed Git ref, or ':' for the staged index",
    )
    args = parser.parse_args()
    errors = validate_publication_contract(RepositoryReader(ROOT, args.git_ref))
    if errors:
        print(f"check_publication_contract: {len(errors)} failure(s)")
        for error in errors:
            print(f"  FAIL {error}")
        return 1
    target = args.git_ref or "worktree"
    print(f"check_publication_contract: publication contract verified at {target}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
