#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the downstream consumer example explicit about its open boundary."""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent


def contract_errors(example: str, readme: str) -> list[str]:
    """Return missing public-interface and claim-ceiling obligations."""
    errors: list[str] = []
    example_requirements = {
        "supported root import": "import Erdos249257",
        "proved headline consumer": "theorem downstream_base_three_irrational",
        "conditional consumer": "theorem downstream_conditional_rational_shell_bound",
        "explicit analytic hypothesis": "(hupper : (whole : ℝ) - (pfx : ℝ) ≤",
        "conditional library adapter":
            "prefixDenominator_shell_power_bound_of_rational_difference",
        "universal claim ceiling":
            "this does not prove the universal\nErdős #257 statement",
    }
    for label, token in example_requirements.items():
        if token not in example:
            errors.append(f"downstream example lost {label}")

    readme_requirements = {
        "consumer route": "[`examples/Examples.lean`](examples/Examples.lean)",
        "conditional interface description":
            "conditional rational shell-pressure\ninterface",
        "explicit-hypothesis boundary": "leaving its analytic hypothesis explicit",
        "universal claim ceiling":
            "does\nnot prove the still-open universal Erdős #257 statement",
    }
    for label, token in readme_requirements.items():
        if token not in readme:
            errors.append(f"README lost downstream {label}")
    return errors


def main() -> int:
    example = (ROOT / "examples" / "Examples.lean").read_text(encoding="utf-8")
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    assert not contract_errors(example, readme)

    implicit_hypothesis = example.replace(
        "(hupper : (whole : ℝ) - (pfx : ℝ) ≤",
        "(upperBound : (whole : ℝ) - (pfx : ℝ) ≤",
        1,
    )
    assert any(
        "explicit analytic hypothesis" in error
        for error in contract_errors(implicit_hypothesis, readme)
    )

    overstated_readme = readme.replace(
        "does\nnot prove the still-open universal Erdős #257 statement",
        "proves the universal Erdős #257 statement",
        1,
    )
    assert any(
        "universal claim ceiling" in error
        for error in contract_errors(example, overstated_readme)
    )

    print(
        "test_downstream_example_contract: proved and conditional consumers "
        "retain an explicit open boundary; 2 negative fixtures rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
