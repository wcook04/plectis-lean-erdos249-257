#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the public Lean toolchain and dependency lock mutually consistent."""

from __future__ import annotations

import copy
import json
import re
import tomllib
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
LEAN_TOOLCHAIN_RE = re.compile(r"leanprover/lean4:(v[0-9]+\.[0-9]+\.[0-9]+)")
COMMIT_RE = re.compile(r"[0-9a-f]{40}")
MATHLIB_URL = "https://github.com/leanprover-community/mathlib4"


def encode_manifest(manifest: dict[str, Any]) -> str:
    return json.dumps(manifest, ensure_ascii=False)


def dependency_lock_errors(
    toolchain_text: str,
    lakefile_text: str,
    manifest_text: str,
) -> list[str]:
    """Return proof-environment identity and pinning failures."""
    errors: list[str] = []
    toolchain = toolchain_text.strip()
    toolchain_match = LEAN_TOOLCHAIN_RE.fullmatch(toolchain)
    if toolchain_match is None:
        errors.append("lean-toolchain lost the exact Lean release identity")
        lean_release = None
    else:
        lean_release = toolchain_match.group(1)

    try:
        lakefile = tomllib.loads(lakefile_text)
    except tomllib.TOMLDecodeError:
        errors.append("lakefile.toml is not valid TOML")
        return errors
    try:
        manifest = json.loads(manifest_text)
    except json.JSONDecodeError:
        errors.append("lake-manifest.json is not valid JSON")
        return errors

    if manifest.get("name") != lakefile.get("name"):
        errors.append("Lake project name drifted between lakefile and manifest")

    mathlib_requirements = [
        row
        for row in lakefile.get("require", [])
        if row.get("name") == "mathlib"
    ]
    if len(mathlib_requirements) != 1:
        errors.append("lakefile must declare exactly one direct Mathlib requirement")
        expected_mathlib_input = None
    else:
        requirement = mathlib_requirements[0]
        expected_mathlib_input = requirement.get("rev")
        if requirement.get("scope") != "leanprover-community":
            errors.append("Mathlib requirement lost its leanprover-community scope")
        if expected_mathlib_input != lean_release:
            errors.append("Mathlib input revision drifted from the Lean toolchain")

    packages = manifest.get("packages")
    if not isinstance(packages, list) or not packages:
        errors.append("lake-manifest.json lost its pinned package list")
        return errors

    names = [row.get("name") for row in packages]
    if any(not isinstance(name, str) or not name for name in names):
        errors.append("manifest package lost its nonempty name")
    if len(names) != len(set(names)):
        errors.append("manifest package names are not unique")

    for row in packages:
        name = row.get("name", "<unnamed>")
        if row.get("type") != "git":
            errors.append(f"manifest package {name} is not a Git dependency")
        if COMMIT_RE.fullmatch(str(row.get("rev", ""))) is None:
            errors.append(f"manifest package {name} lacks a full commit revision")
        if not str(row.get("url", "")).startswith("https://"):
            errors.append(f"manifest package {name} lacks an HTTPS source URL")

    mathlib_packages = [row for row in packages if row.get("name") == "mathlib"]
    if len(mathlib_packages) != 1:
        errors.append("manifest must contain exactly one Mathlib package")
    else:
        mathlib = mathlib_packages[0]
        if mathlib.get("inherited") is not False:
            errors.append("Mathlib manifest package must remain a direct dependency")
        if mathlib.get("scope") != "leanprover-community":
            errors.append("Mathlib manifest package lost its canonical scope")
        if mathlib.get("url") != MATHLIB_URL:
            errors.append("Mathlib manifest package lost its canonical source URL")
        if mathlib.get("inputRev") != expected_mathlib_input:
            errors.append("Mathlib manifest input revision drifted from lakefile")
    return errors


def main() -> int:
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8")
    lakefile = (ROOT / "lakefile.toml").read_text(encoding="utf-8")
    manifest = (ROOT / "lake-manifest.json").read_text(encoding="utf-8")
    assert not dependency_lock_errors(toolchain, lakefile, manifest)

    lake_rev_drift = lakefile.replace('rev = "v4.29.1"', 'rev = "v4.29.0"', 1)
    assert any(
        "drifted from the Lean toolchain" in error
        for error in dependency_lock_errors(toolchain, lake_rev_drift, manifest)
    )

    manifest_data = json.loads(manifest)
    input_drift = copy.deepcopy(manifest_data)
    input_drift["packages"][0]["inputRev"] = "v4.29.0"
    assert any(
        "input revision drifted from lakefile" in error
        for error in dependency_lock_errors(
            toolchain, lakefile, encode_manifest(input_drift)
        )
    )

    inherited_mathlib = copy.deepcopy(manifest_data)
    inherited_mathlib["packages"][0]["inherited"] = True
    assert any(
        "direct dependency" in error
        for error in dependency_lock_errors(
            toolchain, lakefile, encode_manifest(inherited_mathlib)
        )
    )

    shortened_revision = copy.deepcopy(manifest_data)
    shortened_revision["packages"][-1]["rev"] = "7802da01"
    assert any(
        "full commit revision" in error
        for error in dependency_lock_errors(
            toolchain, lakefile, encode_manifest(shortened_revision)
        )
    )

    duplicate_package = copy.deepcopy(manifest_data)
    duplicate_package["packages"].append(copy.deepcopy(manifest_data["packages"][0]))
    assert any(
        "names are not unique" in error
        for error in dependency_lock_errors(
            toolchain, lakefile, encode_manifest(duplicate_package)
        )
    )

    project_name_drift = copy.deepcopy(manifest_data)
    project_name_drift["name"] = "different-project"
    assert any(
        "project name drifted" in error
        for error in dependency_lock_errors(
            toolchain, lakefile, encode_manifest(project_name_drift)
        )
    )

    print(
        "test_dependency_lock_contract: Lean, direct Mathlib input, and "
        f"{len(manifest_data['packages'])} exact package revisions agree; "
        "6 negative fixtures rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
