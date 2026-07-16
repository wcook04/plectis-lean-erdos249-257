#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Validation helpers for the public publication-artifact contract."""

from __future__ import annotations

import copy
import hashlib
import json
import re
import subprocess
import tomllib
from pathlib import Path
from typing import Any


CONTRACT_PATH = "docs/publication_contract.json"
CLAIMS_PATH = "docs/claims.json"
MAKEFILE_PATH = "paper/Makefile"
REUSE_PATH = "REUSE.toml"
SCHEMA = "erdos249257-publication-contract/1"
REQUIRED_ARTIFACT_FIELDS = {
    "id",
    "title",
    "artifact_class",
    "source_path",
    "source_content_digest",
    "rendered_path",
    "rendered_content_digest",
    "authority_posture",
    "claim_scope",
    "architecture_ref",
    "entry_route_id",
    "validation",
}


class RepositoryReader:
    """Read either the worktree or one committed/staged Git snapshot."""

    def __init__(self, root: Path, git_ref: str | None = None) -> None:
        self.root = root
        self.git_ref = git_ref

    def _git_spec(self, relative: str) -> str:
        return f":{relative}" if self.git_ref == ":" else f"{self.git_ref}:{relative}"

    def read_bytes(self, relative: str) -> bytes:
        if self.git_ref is None:
            return (self.root / relative).read_bytes()
        completed = subprocess.run(
            ["git", "show", self._git_spec(relative)],
            cwd=self.root,
            capture_output=True,
            check=False,
        )
        if completed.returncode != 0:
            detail = completed.stderr.decode("utf-8", errors="replace").strip()
            raise FileNotFoundError(detail or relative)
        return completed.stdout

    def read_text(self, relative: str) -> str:
        return self.read_bytes(relative).decode("utf-8")

    def exists(self, relative: str) -> bool:
        try:
            self.read_bytes(relative)
        except (FileNotFoundError, OSError, UnicodeError):
            return False
        return True

    def git_object_exists(self, object_name: str) -> bool:
        return (
            subprocess.run(
                ["git", "cat-file", "-e", f"{object_name}^{{commit}}"],
                cwd=self.root,
                capture_output=True,
                check=False,
            ).returncode
            == 0
        )


def sha256(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def load_json(reader: RepositoryReader, relative: str) -> dict[str, Any]:
    return json.loads(reader.read_text(relative))


def makefile_papers(text: str) -> set[str]:
    logical = text.replace("\\\n", " ")
    match = re.search(r"(?m)^PAPERS\s*=\s*(.+)$", logical)
    if not match:
        return set()
    return {token for token in match.group(1).split() if token}


def reuse_manuscript_pdfs(data: dict[str, Any]) -> set[str]:
    paths: set[str] = set()
    for annotation in data.get("annotations", []):
        if annotation.get("SPDX-License-Identifier") != "CC-BY-4.0":
            continue
        raw_paths = annotation.get("path", [])
        if isinstance(raw_paths, str):
            raw_paths = [raw_paths]
        for path in raw_paths:
            if (
                isinstance(path, str)
                and path.endswith(".pdf")
                and "/" not in path
                and "*" not in path
            ):
                paths.add(path)
    return paths


def all_entrypoints(
    claims: dict[str, Any], contract: dict[str, Any]
) -> list[dict[str, Any]]:
    return [
        *claims["machine_readable_paper"]["entrypoints"],
        *contract.get("entrypoints", []),
    ]


def validate_publication_contract(
    reader: RepositoryReader,
    *,
    contract_override: dict[str, Any] | None = None,
    claims_override: dict[str, Any] | None = None,
) -> list[str]:
    errors: list[str] = []

    try:
        contract = contract_override or load_json(reader, CONTRACT_PATH)
    except (FileNotFoundError, json.JSONDecodeError, UnicodeError) as error:
        return [f"{CONTRACT_PATH}: {error}"]
    try:
        claims = claims_override or load_json(reader, CLAIMS_PATH)
    except (FileNotFoundError, json.JSONDecodeError, UnicodeError) as error:
        return [f"{CLAIMS_PATH}: {error}"]

    if contract.get("schema") != SCHEMA:
        errors.append(f"{CONTRACT_PATH} must use schema {SCHEMA}")
    if contract.get("authority_posture") != (
        "publication_metadata_and_evidence_boundary_not_Lean_proof_authority"
    ):
        errors.append("publication contract authority posture drifted")

    artifacts = contract.get("artifacts")
    if not isinstance(artifacts, list) or not artifacts:
        return [*errors, "publication contract must contain artifacts"]

    artifact_ids = [row.get("id") for row in artifacts]
    source_paths = [row.get("source_path") for row in artifacts]
    rendered_paths = [row.get("rendered_path") for row in artifacts]
    if len(artifact_ids) != len(set(artifact_ids)):
        errors.append("publication contract contains duplicate artifact ids")
    if len(source_paths) != len(set(source_paths)):
        errors.append("publication contract contains duplicate source paths")
    if len(rendered_paths) != len(set(rendered_paths)):
        errors.append("publication contract contains duplicate rendered paths")

    route_ids = {
        row.get("id") for row in all_entrypoints(claims, contract) if row.get("id")
    }
    for artifact in artifacts:
        artifact_id = artifact.get("id", "<unknown>")
        missing = REQUIRED_ARTIFACT_FIELDS - set(artifact)
        if missing:
            errors.append(
                f"publication artifact {artifact_id!r} lacks fields: {sorted(missing)}"
            )
            continue
        source = artifact["source_path"]
        rendered = artifact["rendered_path"]
        if not source.startswith("paper/") or not source.endswith(".tex"):
            errors.append(
                f"publication artifact {artifact_id!r} has invalid source path {source!r}"
            )
        if "/" in rendered or not rendered.endswith(".pdf"):
            errors.append(
                f"publication artifact {artifact_id!r} has invalid rendered path {rendered!r}"
            )
        for relative, digest_field in (
            (source, "source_content_digest"),
            (rendered, "rendered_content_digest"),
        ):
            if not reader.exists(relative):
                errors.append(
                    f"publication artifact {artifact_id!r} path does not exist: {relative}"
                )
                continue
            actual = sha256(reader.read_bytes(relative))
            if artifact[digest_field] != actual:
                errors.append(
                    f"publication artifact {artifact_id!r} {digest_field} drifted: "
                    f"expected {artifact[digest_field]}, actual {actual}"
                )
        if "not_Lean_proof_authority" not in artifact["authority_posture"]:
            errors.append(
                f"publication artifact {artifact_id!r} lost its Lean proof-authority boundary"
            )
        if artifact["entry_route_id"] not in route_ids:
            errors.append(
                f"publication artifact {artifact_id!r} names unknown entry route "
                f"{artifact['entry_route_id']!r}"
            )
        if not artifact["validation"] or not all(
            isinstance(command, str) and command.startswith("python3 scripts/")
            for command in artifact["validation"]
        ):
            errors.append(
                f"publication artifact {artifact_id!r} lacks repository validation commands"
            )

    try:
        built = makefile_papers(reader.read_text(MAKEFILE_PATH))
    except (FileNotFoundError, UnicodeError) as error:
        errors.append(f"{MAKEFILE_PATH}: {error}")
        built = set()
    registered_bases = {Path(path).stem for path in source_paths if isinstance(path, str)}
    if built != registered_bases:
        errors.append(
            "publication build coverage drifted: "
            f"missing_from_contract={sorted(built - registered_bases)}, "
            f"not_built={sorted(registered_bases - built)}"
        )

    try:
        reuse = tomllib.loads(reader.read_text(REUSE_PATH))
        licensed_pdfs = reuse_manuscript_pdfs(reuse)
    except (FileNotFoundError, UnicodeError, tomllib.TOMLDecodeError) as error:
        errors.append(f"{REUSE_PATH}: {error}")
        licensed_pdfs = set()
    registered_pdfs = {path for path in rendered_paths if isinstance(path, str)}
    if licensed_pdfs != registered_pdfs:
        errors.append(
            "publication licence coverage drifted: "
            f"missing_from_contract={sorted(licensed_pdfs - registered_pdfs)}, "
            f"not_CC_BY_licensed={sorted(registered_pdfs - licensed_pdfs)}"
        )

    contract_routes = contract.get("entrypoints", [])
    contract_route_ids = [row.get("id") for row in contract_routes]
    if len(contract_route_ids) != len(set(contract_route_ids)):
        errors.append("publication contract contains duplicate entry route ids")
    for route in contract_routes:
        route_id = route.get("id", "<unknown>")
        for field in (
            "id",
            "title",
            "intent",
            "read",
            "query_steps",
            "authority_owners",
            "adjacent_handle_classes",
        ):
            if not route.get(field):
                errors.append(
                    f"publication entry route {route_id!r} lacks required field {field!r}"
                )
        for relative in route.get("read", []):
            if not reader.exists(relative):
                errors.append(
                    f"publication entry route {route_id!r} read path is missing: {relative}"
                )
        for command in route.get("query_steps", []):
            if not command.startswith("python3 scripts/query_corpus.py --"):
                errors.append(
                    f"publication entry route {route_id!r} has an untyped query step: "
                    f"{command}"
                )

    architecture = claims["machine_readable_paper"]["publication_assembly"][
        "publication_architecture"
    ]
    by_class: dict[str, set[str]] = {}
    for artifact in artifacts:
        by_class.setdefault(artifact["artifact_class"], set()).add(
            artifact["source_path"]
        )
    if by_class.get("mathematical_gateway", set()) != {
        architecture["canonical_gateway"]["source"]
    }:
        errors.append("publication gateway drifted from docs/claims.json")
    retained_sources = {
        row["source"] for row in architecture.get("retained_companions", [])
    }
    if by_class.get("mathematical_companion", set()) != retained_sources:
        errors.append("publication mathematical companions drifted from docs/claims.json")
    systems_sources = {
        row["source"] for row in architecture.get("systems_case_studies", [])
    }
    if by_class.get("systems_case_study", set()) != systems_sources:
        errors.append("publication systems case studies drifted from docs/claims.json")

    rejected_ids = set(contract.get("rejected_artifact_ids", []))
    registered_ids = set(artifact_ids)
    overlap = rejected_ids & registered_ids
    if overlap:
        errors.append(
            f"publication artifacts are both registered and rejected: {sorted(overlap)}"
        )
    claims_rejected = {
        row.get("id") for row in architecture.get("rejected_companions", [])
    }
    if "system_or_methodology_paper" in claims_rejected and systems_sources:
        errors.append(
            "docs/claims.json still rejects a system or methodology paper while "
            "a systems case study is shipped"
        )

    systems_artifacts = [
        row for row in artifacts if row.get("artifact_class") == "systems_case_study"
    ]
    for artifact in systems_artifacts:
        evidence = artifact.get("evidence_boundary")
        if not isinstance(evidence, dict):
            errors.append(
                f"systems artifact {artifact['id']!r} lacks an evidence_boundary"
            )
            continue
        checkpoint = evidence.get("evaluation_checkpoint", "")
        if not isinstance(checkpoint, str) or not re.fullmatch(
            r"[0-9a-f]{40}", checkpoint
        ):
            errors.append(
                f"systems artifact {artifact['id']!r} has an invalid evaluation checkpoint"
            )
        elif not reader.git_object_exists(checkpoint):
            errors.append(
                f"systems artifact {artifact['id']!r} evaluation checkpoint is absent: "
                f"{checkpoint}"
            )
        if evidence.get("authored_mutation_count") != 10:
            errors.append("systems evidence must preserve the ten-mutation study size")
        if evidence.get("rejected_mutation_count") != 9:
            errors.append("systems evidence must preserve the nine rejected mutations")
        if evidence.get("escaped_mutation_id") != "M8":
            errors.append("systems evidence must preserve M8 as the escaped mutation")
        if evidence.get("post_repair_full_mutation_rerun") is not False:
            errors.append(
                "systems evidence must not claim a complete post-repair mutation rerun"
            )
        if "ten-of-ten" not in str(evidence.get("forbidden_inference", "")):
            errors.append(
                "systems evidence must explicitly forbid a post-repair ten-of-ten claim"
            )

    return errors


def mutation_fixture_failures(reader: RepositoryReader) -> list[str]:
    """Return fixture names whose known-bad mutation was not rejected."""
    contract = load_json(reader, CONTRACT_PATH)
    failures: list[str] = []

    missing = copy.deepcopy(contract)
    missing["artifacts"] = [
        row for row in missing["artifacts"] if row["id"] != "systems_case_study"
    ]
    if not validate_publication_contract(reader, contract_override=missing):
        failures.append("unregistered_built_systems_paper")

    duplicate = copy.deepcopy(contract)
    duplicate["artifacts"].append(copy.deepcopy(duplicate["artifacts"][0]))
    duplicate["artifacts"][-1]["id"] = "duplicate_gateway"
    if not validate_publication_contract(reader, contract_override=duplicate):
        failures.append("duplicate_publication_source")

    drift = copy.deepcopy(contract)
    drift["artifacts"][0]["source_content_digest"] = "sha256:" + "0" * 64
    if not validate_publication_contract(reader, contract_override=drift):
        failures.append("publication_digest_drift")

    rejected = copy.deepcopy(contract)
    rejected["rejected_artifact_ids"].append("systems_case_study")
    if not validate_publication_contract(reader, contract_override=rejected):
        failures.append("registered_and_rejected_artifact")

    inflated = copy.deepcopy(contract)
    systems = next(
        row for row in inflated["artifacts"] if row["id"] == "systems_case_study"
    )
    systems["evidence_boundary"]["post_repair_full_mutation_rerun"] = True
    if not validate_publication_contract(reader, contract_override=inflated):
        failures.append("post_repair_ten_of_ten_inflation")

    return failures
