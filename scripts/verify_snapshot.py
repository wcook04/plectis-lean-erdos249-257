#!/usr/bin/env python3
"""Verify a generated Plectis Lean/Lake snapshot without the private workspace."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Mapping, Sequence


SCHEMA = "plectis_lean_snapshot_verifier_v0"
SUBJECT_EXCLUDED = {"snapshot/RELEASE_NOTES.md", "snapshot/RELEASE_PROVENANCE.json"}
APACHE_PHRASES = (
    "Apache License",
    "Version 2.0, January 2004",
    "TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION",
    "END OF TERMS AND CONDITIONS",
)
REQUIRED_NON_CLAIMS = (
    "not_erdos_257_solution",
    "not_erdos_249_solution",
    "not_publication_authority",
    "not_private_root_equivalence",
)
REQUIRED_CLAIM_FAMILIES = (
    "lean_kernel_model",
    "lake_package_build",
    "mathlib_dependency",
    "erdos_borwein_lambert_series",
    "local_lean_snapshot_identity",
    "problem_numbering_249_257_if_publicly_cited",
)


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _tree_file_rows(root: Path, excluded: set[str] | None = None) -> list[dict[str, Any]]:
    excluded = excluded or set()
    rows: list[dict[str, Any]] = []
    for path in sorted(root.rglob("*")):
        if not path.is_file():
            continue
        rel = path.relative_to(root).as_posix()
        if (
            rel == ".git"
            or rel.startswith(".git/")
            or rel.startswith(".lake/")
            or rel.startswith(".cursor/")
            or rel in excluded
        ):
            continue
        stat = path.stat()
        rows.append({"path": rel, "bytes": stat.st_size, "sha256": _sha256(path)})
    return rows


def _tree_sha256(rows: Sequence[Mapping[str, Any]]) -> str:
    digest = hashlib.sha256()
    for row in rows:
        digest.update(str(row.get("path") or "").encode("utf-8"))
        digest.update(b"\0")
        digest.update(str(row.get("sha256") or "").encode("utf-8"))
        digest.update(b"\0")
        digest.update(str(row.get("bytes") or 0).encode("utf-8"))
        digest.update(b"\n")
    return digest.hexdigest()


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_json_with_comment_header(path: Path) -> dict[str, Any]:
    lines = [line for line in path.read_text(encoding="utf-8").splitlines() if not line.lstrip().startswith("#")]
    return json.loads("\n".join(lines))


def _decode_scalar(value: str) -> str:
    value = value.strip()
    if value.startswith('"') and value.endswith('"'):
        try:
            return str(json.loads(value))
        except json.JSONDecodeError:
            return value.strip('"')
    return value


def _parse_generated_cff(path: Path) -> dict[str, Any]:
    top: dict[str, str] = {}
    titles: list[str] = []
    in_references = False
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if stripped == "references:":
            in_references = True
            continue
        if in_references:
            match = re.match(r"title:\s*(.+)$", stripped)
            if match:
                titles.append(_decode_scalar(match.group(1)))
            continue
        match = re.match(r"([A-Za-z0-9_-]+):\s*(.*)$", stripped)
        if match:
            top[match.group(1)] = _decode_scalar(match.group(2))
    return {"top": top, "reference_titles": titles}


def _json_body_keys(value: Any, prefix: str = "") -> list[str]:
    keys: list[str] = []
    if isinstance(value, dict):
        for key, child in value.items():
            key_text = str(key)
            if key_text in {"stdout", "stderr", "stdout_body", "stderr_body"}:
                keys.append(prefix + key_text)
            keys.extend(_json_body_keys(child, prefix + key_text + "."))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            keys.extend(_json_body_keys(child, prefix + str(index) + "."))
    return keys


def _private_text_findings(root: Path) -> list[dict[str, str]]:
    patterns = {
        "absolute_user_path": "/" + "Users/",
        "ai_workflow_root_path": "src/" + "ai_workflow",
        "private_key_block": "BEGIN " + "PRIVATE KEY",
    }
    findings: list[dict[str, str]] = []
    for path in sorted(root.rglob("*")):
        if not path.is_file():
            continue
        rel = path.relative_to(root).as_posix()
        if rel.startswith(".git/") or rel.startswith(".lake/") or rel.startswith(".cursor/"):
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        for kind, needle in patterns.items():
            if needle in text:
                findings.append({"path": rel, "kind": kind})
    return findings


def verify(root: Path) -> dict[str, Any]:
    failures: list[dict[str, Any]] = []
    blockers: list[dict[str, Any]] = []

    required_files = [
        "CITATION.cff",
        "snapshot/REFERENCES.yaml",
        "snapshot/CLAIM_TO_REFERENCE_MAP.json",
        "snapshot/PUBLIC_API_CONTRACT.json",
        "PlectisSnapshot.lean",
        "PlectisSnapshot/PublicAPI.lean",
        "snapshot/NON_CLAIMS.md",
        "snapshot/PUBLIC_SNAPSHOT_MANIFEST.json",
        "snapshot/PLECTIS_INTEGRATION.json",
        "snapshot/RELEASE_PROVENANCE.json",
        "snapshot/RELEASE_NOTES.md",
        "LICENSE",
        "LICENSES/Apache-2.0.txt",
        "REUSE.toml",
        ".github/workflows/release-gate.yml",
    ]
    for rel in required_files:
        if not (root / rel).is_file():
            failures.append({"kind": "missing_required_file", "path": rel})

    cff: dict[str, Any] = {"top": {}, "reference_titles": []}
    try:
        cff = _parse_generated_cff(root / "CITATION.cff")
        for key in ("cff-version", "type", "message", "title", "license"):
            if key not in cff["top"]:
                failures.append({"kind": "citation_missing_key", "key": key})
        if cff["top"].get("type") != "software-code":
            failures.append({"kind": "citation_type_not_software_code"})
        forbidden_public_keys = [key for key in ("repository-code", "version", "commit", "date-released") if key in cff["top"]]
        if forbidden_public_keys:
            failures.append({"kind": "citation_public_fields_present_before_public_tag", "keys": forbidden_public_keys})
        placeholder_titles = [title for title in cff["reference_titles"] if "placeholder" in title.lower()]
        if placeholder_titles:
            blockers.append({"kind": "citation_placeholders_unresolved", "titles": placeholder_titles})
    except Exception as exc:  # noqa: BLE001 - standalone verifier should report, not crash.
        failures.append({"kind": "citation_parse_error", "error": str(exc)})

    references: dict[str, Any] = {}
    try:
        references = _load_json_with_comment_header(root / "snapshot" / "REFERENCES.yaml")
    except Exception as exc:  # noqa: BLE001
        failures.append({"kind": "references_parse_error", "error": str(exc)})

    try:
        claim_map = _load_json(root / "snapshot" / "CLAIM_TO_REFERENCE_MAP.json")
        families = claim_map.get("claim_families") or {}
        for family in REQUIRED_CLAIM_FAMILIES:
            row = families.get(family) or {}
            if row.get("status") != "pass":
                blockers.append({"kind": "claim_family_unresolved", "claim_family": family, "blockers": row.get("blockers") or []})
    except Exception as exc:  # noqa: BLE001
        failures.append({"kind": "claim_reference_map_parse_error", "error": str(exc)})

    try:
        non_claims = (root / "snapshot" / "NON_CLAIMS.md").read_text(encoding="utf-8")
        missing = [item for item in REQUIRED_NON_CLAIMS if item not in non_claims]
        if missing:
            failures.append({"kind": "non_claims_missing", "missing": missing})
    except FileNotFoundError:
        pass

    try:
        public_manifest = _load_json(root / "snapshot" / "PUBLIC_SNAPSHOT_MANIFEST.json")
        integration = _load_json(root / "snapshot" / "PLECTIS_INTEGRATION.json")
        if public_manifest.get("parent_component") != (integration.get("plectis_integration") or {}).get("parent_component"):
            failures.append({"kind": "public_manifest_parent_component_mismatch"})
        public_tag = (public_manifest.get("standalone_repo") or {}).get("public_tag")
        public_commit = (public_manifest.get("standalone_repo") or {}).get("public_commit")
        notes = (root / "snapshot" / "RELEASE_NOTES.md").read_text(encoding="utf-8")
        if not public_tag and "Publication status: blocked" not in notes:
            failures.append({"kind": "release_notes_not_blocked_without_public_tag"})
        if public_tag or public_commit:
            blockers.append({"kind": "public_fields_present_in_local_candidate", "public_tag": public_tag, "public_commit": public_commit})
    except Exception as exc:  # noqa: BLE001
        failures.append({"kind": "public_manifest_or_integration_error", "error": str(exc)})

    try:
        contract = _load_json(root / "snapshot" / "PUBLIC_API_CONTRACT.json")
        if contract.get("schema") != "plectis_lean_public_api_contract_v0":
            failures.append({"kind": "public_api_contract_schema_mismatch", "schema": contract.get("schema")})
        if contract.get("plectis_consumption_mode") != "pointer_only_until_public_tag":
            failures.append({"kind": "public_api_contract_consumption_mode_not_pointer_only"})
        for rel in contract.get("adapter_files") or []:
            if not (root / str(rel)).is_file():
                failures.append({"kind": "public_api_contract_adapter_missing", "path": str(rel)})
        public_manifest_contract = public_manifest.get("public_api_contract") or {}
        if public_manifest_contract.get("schema") != contract.get("schema"):
            failures.append({"kind": "public_manifest_contract_schema_mismatch"})
        adapter_text = (root / "PlectisSnapshot" / "PublicAPI.lean").read_text(encoding="utf-8")
        if "namespace PlectisSnapshot" not in adapter_text or "def publicApiContractSchema" not in adapter_text:
            failures.append({"kind": "public_api_adapter_missing_stable_metadata"})
    except Exception as exc:  # noqa: BLE001
        failures.append({"kind": "public_api_contract_error", "error": str(exc)})

    try:
        provenance = _load_json(root / "snapshot" / "RELEASE_PROVENANCE.json")
        rows = _tree_file_rows(root, SUBJECT_EXCLUDED)
        digest = _tree_sha256(rows)
        subject_digest = ((provenance.get("subject") or [{}])[0].get("digest") or {}).get("sha256")
        if subject_digest != digest:
            failures.append({"kind": "provenance_subject_digest_mismatch", "expected": subject_digest, "actual": digest})
        deps = {
            row.get("uri")
            for row in ((provenance.get("predicate") or {}).get("buildDefinition") or {}).get("resolvedDependencies") or []
        }
        for uri in ("source_files_sha256", "lake-manifest.json", "lean-toolchain"):
            if uri not in deps:
                failures.append({"kind": "provenance_dependency_missing", "uri": uri})
    except Exception as exc:  # noqa: BLE001
        failures.append({"kind": "provenance_parse_error", "error": str(exc)})

    try:
        license_text = (root / "LICENSE").read_text(encoding="utf-8")
        license_copy = (root / "LICENSES" / "Apache-2.0.txt").read_text(encoding="utf-8")
        for phrase in APACHE_PHRASES:
            if phrase not in license_text or phrase not in license_copy:
                failures.append({"kind": "apache_license_phrase_missing", "phrase": phrase})
    except FileNotFoundError:
        pass

    try:
        reuse = (root / "REUSE.toml").read_text(encoding="utf-8")
        if "SPDX-License-Identifier" not in reuse or "Apache-2.0" not in reuse:
            failures.append({"kind": "reuse_toml_missing_spdx_license"})
    except FileNotFoundError:
        pass

    try:
        workflow = (root / ".github" / "workflows" / "release-gate.yml").read_text(encoding="utf-8")
        pins = re.findall(r"uses: [^@\s]+@([0-9a-f]{40})", workflow)
        if len(pins) != 2:
            failures.append({"kind": "release_gate_workflow_not_full_sha_pinned", "pin_count": len(pins)})
    except FileNotFoundError:
        pass

    private_findings = _private_text_findings(root)
    if private_findings:
        failures.append({"kind": "private_text_findings", "findings": private_findings})

    json_body_findings: list[dict[str, Any]] = []
    for path in sorted(root.rglob("*.json")):
        if ".git" in path.parts or ".lake" in path.parts or ".cursor" in path.parts:
            continue
        try:
            keys = _json_body_keys(_load_json(path))
        except Exception:
            continue
        if keys:
            json_body_findings.append({"path": path.relative_to(root).as_posix(), "keys": keys})
    if json_body_findings:
        failures.append({"kind": "stdout_stderr_body_keys_present", "findings": json_body_findings})

    structural_status = "pass" if not failures else "failed"
    status = "failed" if failures else "blocked" if blockers else "pass"
    return {
        "schema": SCHEMA,
        "status": status,
        "structural_status": structural_status,
        "publication_ready_boolean": status == "pass",
        "blockers": blockers,
        "failures": failures,
        "citation_reference_titles": cff.get("reference_titles") or [],
        "references_schema": references.get("schema"),
        "subject_digest_recomputed": not any(row.get("kind") == "provenance_subject_digest_mismatch" for row in failures),
        "subject_excluded_files": sorted(SUBJECT_EXCLUDED),
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=".")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--allow-blocked", action="store_true")
    args = parser.parse_args(argv)
    result = verify(Path(args.root).resolve())
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print("status:", result["status"])
        print("structural_status:", result["structural_status"])
        print("blockers:", len(result["blockers"]))
        print("failures:", len(result["failures"]))
    if result["status"] == "pass":
        return 0
    if args.allow_blocked and result["structural_status"] == "pass":
        return 0
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
