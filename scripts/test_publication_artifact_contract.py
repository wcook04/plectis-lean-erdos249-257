#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial fixtures for the publication-artifact contract."""

from __future__ import annotations

import argparse
from pathlib import Path

from publication_contract import (
    RepositoryReader,
    mutation_fixture_failures,
    validate_publication_contract,
)


ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--git-ref",
        help="test a committed Git ref, or ':' for the staged index",
    )
    args = parser.parse_args()
    reader = RepositoryReader(ROOT, args.git_ref)
    baseline_errors = validate_publication_contract(reader)
    fixture_failures = mutation_fixture_failures(reader) if not baseline_errors else []
    if baseline_errors or fixture_failures:
        print(
            "test_publication_artifact_contract: "
            f"{len(baseline_errors)} baseline failure(s), "
            f"{len(fixture_failures)} fixture failure(s)"
        )
        for error in baseline_errors:
            print(f"  FAIL baseline: {error}")
        for fixture in fixture_failures:
            print(f"  FAIL fixture did not reject: {fixture}")
        return 1
    print(
        "test_publication_artifact_contract: baseline and 7 known-bad "
        "publication mutations verified"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
