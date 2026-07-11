#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial fixtures for methodology claim-transition checks."""

from __future__ import annotations

import json
import sys
from pathlib import Path

from methodology_contract import mutation_fixture_errors, validate_contract


ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    claims = json.loads((ROOT / "docs" / "claims.json").read_text(encoding="utf-8"))
    methodology = json.loads((ROOT / "docs" / "methodology.json").read_text(encoding="utf-8"))

    baseline_errors = validate_contract(claims, methodology)
    if baseline_errors:
        print("test_methodology_contract: baseline contract is invalid")
        for error in baseline_errors:
            print(f"  FAIL {error}")
        return 1

    failures = []
    for fixture_id, errors in mutation_fixture_errors(claims, methodology).items():
        if not errors:
            failures.append(fixture_id)
    if failures:
        print("test_methodology_contract: mutations escaped validation: " + ", ".join(failures))
        return 1

    print("test_methodology_contract: baseline passed; all 4 invalid mutations were rejected")
    return 0


if __name__ == "__main__":
    sys.exit(main())
