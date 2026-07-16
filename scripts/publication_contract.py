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
EVIDENCE_PATH = "docs/publication_evidence.json"
MUTATION_MANIFEST_PATH = "experiments/publication_mutations.json"
MUTATION_HARNESS_PATH = "scripts/run_publication_mutations.py"
CLAIMS_PATH = "docs/claims.json"
MAKEFILE_PATH = "paper/Makefile"
REUSE_PATH = "REUSE.toml"
SCHEMA = "erdos249257-publication-contract/1"
EVIDENCE_SCHEMA = "erdos249257-publication-evidence/1"
MUTATION_MANIFEST_SCHEMA = "erdos249257-publication-mutation-operators/1"
EXPECTED_INVARIANT_FAMILIES = (
    "proof_trust",
    "registry_structure",
    "source_coordinates",
    "paper_anchoring",
    "boundary_language",
    "projection_freshness",
    "byte_budgets",
)
EXPECTED_MUTATION_MATRIX = {
    "M1": ("rejected", "projection_freshness", (), 139.4),
    "M2": ("rejected", "boundary_language", (), 171.5),
    "M3": (
        "rejected",
        "source_coordinates",
        ("projection_freshness",),
        239.1,
    ),
    "M4": (
        "rejected",
        "source_coordinates",
        ("projection_freshness",),
        192.2,
    ),
    "M5": (
        "rejected",
        "registry_structure",
        ("source_coordinates", "projection_freshness"),
        121.4,
    ),
    "M6": ("rejected", "projection_freshness", (), 184.8),
    "M7": ("rejected", "proof_trust", (), 4.7),
    "M8": ("escaped", None, (), 176.0),
    "M9": (
        "rejected",
        "paper_anchoring",
        ("source_coordinates", "projection_freshness"),
        122.8,
    ),
    "M10": ("rejected", "byte_budgets", ("projection_freshness",), 210.5),
}
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

    def __init__(
        self,
        root: Path,
        git_ref: str | None = None,
        byte_overrides: dict[str, bytes] | None = None,
    ) -> None:
        self.root = root
        self.git_ref = git_ref
        self.byte_overrides = byte_overrides or {}

    def _git_spec(self, relative: str) -> str:
        return f":{relative}" if self.git_ref == ":" else f"{self.git_ref}:{relative}"

    def read_bytes(self, relative: str) -> bytes:
        if relative in self.byte_overrides:
            return self.byte_overrides[relative]
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


def normalize_latex_evidence(text: str) -> str:
    """Flatten stable prose anchors without pretending to parse all of TeX."""
    normalized = text.replace("{,}", ",").replace("~", " ").replace("$", "")
    for _ in range(3):
        normalized = re.sub(
            r"\\(?:emph|texttt)\{([^{}]*)\}",
            r"\1",
            normalized,
        )
    normalized = normalized.replace("{", "").replace("}", "")
    return re.sub(r"\s+", " ", normalized).strip().lower()


def validate_systems_evidence_source(
    artifact: dict[str, Any],
    source_text: str,
) -> list[str]:
    """Bind structured experiment metadata to load-bearing manuscript prose."""
    errors: list[str] = []
    evidence = artifact["evidence_boundary"]
    normalized = normalize_latex_evidence(source_text)
    checkpoint_prefix = evidence["evaluation_checkpoint"][:7]
    release_check_count = evidence["release_check_count_at_evaluation"]
    escaped_mutation = evidence["escaped_mutation_id"].lower()

    required_patterns = {
        "evaluation checkpoint": (
            rf"evaluation checkpoint .{{0,80}}{re.escape(checkpoint_prefix)}"
        ),
        "release-check baseline": (
            rf"{release_check_count:,} release checks pass"
        ),
        "observed mutation ratio": (
            r"reports .{0,20}9/10 for the ten authored mutations"
        ),
        "escaped mutation identity": (
            rf"mutation {re.escape(escaped_mutation)} survived"
        ),
        "post-repair baseline scope": (
            r"repaired checker passes the intact baseline and rejects the same corruption"
        ),
        "post-repair rerun limitation": (
            r"we did not rerun the other nine mutations against the extended invariant family"
        ),
        "post-repair ratio limitation": (
            r"no post-repair detection ratio is reported"
        ),
    }
    for label, pattern in required_patterns.items():
        if not re.search(pattern, normalized):
            errors.append(
                f"systems artifact {artifact['id']!r} source lost its "
                f"{label} evidence anchor"
            )
    return errors


def validate_mutation_evidence_receipt(
    receipt: dict[str, Any],
    artifact: dict[str, Any],
    reader: RepositoryReader,
) -> list[str]:
    """Validate the immutable reported mutation matrix and its claim ceiling."""
    errors: list[str] = []
    if receipt.get("schema") != EVIDENCE_SCHEMA:
        errors.append(f"{EVIDENCE_PATH} must use schema {EVIDENCE_SCHEMA}")
    if receipt.get("record_kind") != (
        "structured_transcription_of_reported_historical_runs"
    ):
        errors.append("publication evidence record kind drifted")
    if receipt.get("authority_posture") != (
        "historical_systems_evidence_not_Lean_proof_authority_and_not_a_fresh_rerun"
    ):
        errors.append("publication evidence authority posture drifted")
    if receipt.get("publication_artifact_id") != artifact["id"]:
        errors.append("publication evidence points at the wrong artifact")

    source = receipt.get("source", {})
    if source.get("manuscript") != artifact["source_path"]:
        errors.append("publication evidence manuscript path drifted")
    if source.get("contract") != CONTRACT_PATH:
        errors.append("publication evidence lost its contract owner")

    provenance = receipt.get("provenance", {})
    raw_logs = provenance.get("raw_run_logs_registered")
    operators = provenance.get("executable_mutation_operators_registered")
    if raw_logs is not False:
        paths = provenance.get("raw_run_log_paths", [])
        if not paths or any(not reader.exists(path) for path in paths):
            errors.append(
                "publication evidence may claim registered raw logs only when "
                "all raw_run_log_paths exist"
            )
    if operators is not False:
        manifest = provenance.get("mutation_operator_manifest")
        if not isinstance(manifest, str) or not reader.exists(manifest):
            errors.append(
                "publication evidence may claim executable mutation operators "
                "only with an existing mutation_operator_manifest"
            )
    if provenance.get("reconstructed_executable_mutation_operators_registered") is not True:
        errors.append(
            "publication evidence must register the deterministic mutation reconstruction"
        )
    reconstruction_manifest = provenance.get("reconstruction_manifest")
    reconstruction_harness = provenance.get("reconstruction_harness")
    if reconstruction_manifest != MUTATION_MANIFEST_PATH:
        errors.append("publication evidence reconstruction manifest path drifted")
    if reconstruction_harness != MUTATION_HARNESS_PATH:
        errors.append("publication evidence reconstruction harness path drifted")
    for relative, digest_field in (
        (MUTATION_MANIFEST_PATH, "reconstruction_manifest_digest"),
        (MUTATION_HARNESS_PATH, "reconstruction_harness_digest"),
    ):
        if not reader.exists(relative):
            errors.append(f"publication evidence reconstruction path is missing: {relative}")
            continue
        actual = sha256(reader.read_bytes(relative))
        if provenance.get(digest_field) != actual:
            errors.append(
                f"publication evidence {digest_field} drifted: "
                f"expected {provenance.get(digest_field)}, actual {actual}"
            )
    try:
        reconstruction = load_json(reader, MUTATION_MANIFEST_PATH)
    except (FileNotFoundError, json.JSONDecodeError, UnicodeError) as error:
        errors.append(f"{MUTATION_MANIFEST_PATH}: {error}")
        reconstruction = {}
    if reconstruction.get("schema") != MUTATION_MANIFEST_SCHEMA:
        errors.append(
            f"{MUTATION_MANIFEST_PATH} must use schema {MUTATION_MANIFEST_SCHEMA}"
        )
    if reconstruction.get("experiment_kind") != (
        "deterministic_reconstruction_not_exact_historical_replay"
    ):
        errors.append("publication mutation manifest lost its reconstruction boundary")
    if reconstruction.get("checkpoint") != artifact["evidence_boundary"][
        "evaluation_checkpoint"
    ]:
        errors.append("publication mutation manifest checkpoint drifted")
    if reconstruction.get("historical_evidence") != EVIDENCE_PATH:
        errors.append("publication mutation manifest lost its historical evidence owner")
    reconstructed_rows = reconstruction.get("operators", [])
    reconstructed_ids = [
        row.get("id") for row in reconstructed_rows if isinstance(row, dict)
    ]
    if reconstructed_ids != list(EXPECTED_MUTATION_MATRIX):
        errors.append("publication mutation manifest must register M1 through M10")
    exact_target_ids = {
        row.get("id")
        for row in reconstructed_rows
        if isinstance(row, dict) and row.get("exact_original_target_registered") is True
    }
    if exact_target_ids != {"M6", "M8", "M10"}:
        errors.append("publication mutation exact-target provenance drifted")
    if provenance.get("operator_verification") != (
        "python3 scripts/run_publication_mutations.py --verify-operators"
    ):
        errors.append("publication evidence operator-verification route drifted")
    claim_ceiling = str(provenance.get("claim_ceiling", "")).lower()
    for phrase in (
        "not a fresh rerun",
        "does not reconstruct missing raw run logs",
        "does not treat deterministic replacement targets as the exact original edits",
    ):
        if phrase not in claim_ceiling:
            errors.append(
                f"publication evidence provenance lost claim ceiling phrase: {phrase}"
            )

    evaluation = receipt.get("evaluation", {})
    contract_evidence = artifact["evidence_boundary"]
    if evaluation.get("checkpoint") != contract_evidence["evaluation_checkpoint"]:
        errors.append("publication evidence checkpoint drifted from the contract")
    baseline = evaluation.get("baseline", {})
    if baseline.get("release_check_count") != contract_evidence[
        "release_check_count_at_evaluation"
    ]:
        errors.append("publication evidence release-check baseline drifted")
    if baseline.get("wall_time_seconds") != 144.5:
        errors.append("publication evidence baseline timing drifted")
    if baseline.get("result") != "all_checks_passed":
        errors.append("publication evidence baseline result drifted")
    if baseline.get("negative_fixture_count") != 69:
        errors.append("publication evidence negative-fixture count drifted")

    protocol = evaluation.get("protocol", {})
    expected_protocol = {
        "worktree_posture": "isolated_worktree_pinned_at_evaluation_checkpoint",
        "application_mode": "one_mutation_at_a_time",
        "tree_restored_between_runs": True,
        "full_release_gate_run_after_each_mutation": True,
        "mutation_author_relationship": "mutations_authored_by_checker_author",
    }
    for field, expected in expected_protocol.items():
        if protocol.get(field) != expected:
            errors.append(f"publication evidence protocol field drifted: {field}")

    families = evaluation.get("invariant_families", [])
    family_ids = [row.get("id") for row in families if isinstance(row, dict)]
    if tuple(family_ids) != EXPECTED_INVARIANT_FAMILIES:
        errors.append("publication evidence invariant-family order or coverage drifted")

    mutations = evaluation.get("mutations", [])
    mutation_ids = [
        row.get("id") for row in mutations if isinstance(row, dict)
    ]
    if mutation_ids != list(EXPECTED_MUTATION_MATRIX):
        errors.append("publication evidence mutation ids or order drifted")
    mutations_by_id = {
        row.get("id"): row for row in mutations if isinstance(row, dict)
    }
    for mutation_id, expected in EXPECTED_MUTATION_MATRIX.items():
        row = mutations_by_id.get(mutation_id)
        if row is None:
            continue
        actual = (
            row.get("outcome"),
            row.get("first_detector"),
            tuple(row.get("additional_detectors", [])),
            row.get("wall_time_seconds"),
        )
        if actual != expected:
            errors.append(
                f"publication evidence matrix row drifted: {mutation_id}; "
                f"expected={expected}, actual={actual}"
            )
        detectors = [
            row.get("first_detector"),
            *row.get("additional_detectors", []),
        ]
        if any(
            detector is not None and detector not in EXPECTED_INVARIANT_FAMILIES
            for detector in detectors
        ):
            errors.append(
                f"publication evidence matrix row names an unknown detector: "
                f"{mutation_id}"
            )
        if not isinstance(row.get("description"), str) or not row["description"]:
            errors.append(
                f"publication evidence matrix row lacks a description: {mutation_id}"
            )

    m7 = mutations_by_id.get("M7", {})
    if m7.get("checks_before_rejection") != 639:
        errors.append("publication evidence M7 early-rejection count drifted")
    m8 = mutations_by_id.get("M8", {})
    if m8.get("gate_result") != "all_checks_passed":
        errors.append("publication evidence must preserve the M8 green-gate escape")

    rejected_ids = [
        row.get("id") for row in mutations if row.get("outcome") == "rejected"
    ]
    escaped_ids = [
        row.get("id") for row in mutations if row.get("outcome") == "escaped"
    ]
    summary = evaluation.get("summary", {})
    if summary.get("authored_mutation_count") != len(mutations):
        errors.append("publication evidence authored-mutation summary is not derived")
    if summary.get("rejected_mutation_count") != len(rejected_ids):
        errors.append("publication evidence rejected-mutation summary is not derived")
    if summary.get("escaped_mutation_ids") != escaped_ids:
        errors.append("publication evidence escaped-mutation summary is not derived")
    if summary.get("observed_detection_ratio") != "9/10":
        errors.append("publication evidence observed detection ratio drifted")
    if summary.get("coverage_depth_posture") != (
        "one_deep_coverage_not_family_depth"
    ):
        errors.append("publication evidence lost its one-deep coverage ceiling")

    post_repair = receipt.get("post_repair", {})
    if post_repair.get("intact_baseline_rechecked") is not True:
        errors.append("publication evidence lost the post-repair baseline recheck")
    if post_repair.get("rerun_mutation_ids") != ["M8"]:
        errors.append("publication evidence must preserve M8 as the only rerun mutation")
    if post_repair.get("other_original_mutations_rerun") is not False:
        errors.append("publication evidence must not claim the other mutations were rerun")
    if post_repair.get("post_repair_detection_ratio") is not None:
        errors.append("publication evidence must not report a post-repair ratio")
    if "no post-repair ten-of-ten" not in str(
        post_repair.get("claim_ceiling", "")
    ).lower():
        errors.append("publication evidence lost the post-repair ten-of-ten ceiling")

    threats = receipt.get("threats_to_validity", [])
    if not isinstance(threats, list) or len(threats) < 5:
        errors.append("publication evidence threats-to-validity record is incomplete")
    return errors


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
    evidence_override: dict[str, Any] | None = None,
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
        if evidence.get("release_check_count_at_evaluation") != 5207:
            errors.append(
                "systems evidence must preserve the 5,207-check evaluation baseline"
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
        try:
            source_text = reader.read_text(artifact["source_path"])
        except (FileNotFoundError, UnicodeError) as error:
            errors.append(
                f"systems artifact {artifact['id']!r} evidence source is unreadable: "
                f"{error}"
            )
        else:
            errors.extend(validate_systems_evidence_source(artifact, source_text))
        evidence_path = artifact.get("evidence_receipt_path")
        evidence_digest = artifact.get("evidence_receipt_digest")
        if evidence_path != EVIDENCE_PATH:
            errors.append(
                f"systems artifact {artifact['id']!r} must register {EVIDENCE_PATH}"
            )
            continue
        if not isinstance(evidence_digest, str):
            errors.append(
                f"systems artifact {artifact['id']!r} lacks an evidence receipt digest"
            )
            continue
        try:
            receipt_bytes = reader.read_bytes(evidence_path)
            receipt = evidence_override or json.loads(receipt_bytes)
        except (FileNotFoundError, json.JSONDecodeError, UnicodeError) as error:
            errors.append(f"{EVIDENCE_PATH}: {error}")
            continue
        actual_digest = sha256(receipt_bytes)
        if evidence_digest != actual_digest:
            errors.append(
                f"systems artifact {artifact['id']!r} evidence receipt digest drifted: "
                f"expected {evidence_digest}, actual {actual_digest}"
            )
        errors.extend(validate_mutation_evidence_receipt(receipt, artifact, reader))

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

    checkpoint_drift = copy.deepcopy(contract)
    systems = next(
        row
        for row in checkpoint_drift["artifacts"]
        if row["id"] == "systems_case_study"
    )
    systems["evidence_boundary"]["evaluation_checkpoint"] = (
        "a16aa24af5236b6508a34b8a4c4b41fdcf620a98"
    )
    if not validate_publication_contract(reader, contract_override=checkpoint_drift):
        failures.append("evaluation_checkpoint_source_drift")

    source_inflation = copy.deepcopy(contract)
    systems = next(
        row
        for row in source_inflation["artifacts"]
        if row["id"] == "systems_case_study"
    )
    source_path = systems["source_path"]
    original_source = reader.read_text(source_path)
    limited_sentence = (
        "We did\nnot rerun the other nine mutations against the extended invariant family, "
        "so\nno post-repair detection ratio is reported; the claim is only that this\n"
        "corruption is now caught."
    )
    inflated_sentence = (
        "We reran all ten mutations against the extended invariant family, so a\n"
        "post-repair ten-of-ten detection ratio is reported."
    )
    if limited_sentence not in original_source:
        failures.append("post_repair_source_fixture_anchor_missing")
    else:
        mutated_source = original_source.replace(
            limited_sentence,
            inflated_sentence,
            1,
        )
        systems["source_content_digest"] = sha256(mutated_source.encode("utf-8"))
        overlay_reader = RepositoryReader(
            reader.root,
            reader.git_ref,
            {source_path: mutated_source.encode("utf-8")},
        )
        if not validate_publication_contract(
            overlay_reader,
            contract_override=source_inflation,
        ):
            failures.append("source_and_digest_ten_of_ten_inflation")

    evidence = load_json(reader, EVIDENCE_PATH)

    matrix_inflation = copy.deepcopy(evidence)
    m8 = next(
        row
        for row in matrix_inflation["evaluation"]["mutations"]
        if row["id"] == "M8"
    )
    m8["outcome"] = "rejected"
    m8["first_detector"] = "boundary_language"
    matrix_inflation["evaluation"]["summary"]["rejected_mutation_count"] = 10
    matrix_inflation["evaluation"]["summary"]["escaped_mutation_ids"] = []
    matrix_inflation["evaluation"]["summary"]["observed_detection_ratio"] = "10/10"
    if not validate_publication_contract(
        reader,
        evidence_override=matrix_inflation,
    ):
        failures.append("historical_matrix_ten_of_ten_inflation")

    detector_drift = copy.deepcopy(evidence)
    m3 = next(
        row
        for row in detector_drift["evaluation"]["mutations"]
        if row["id"] == "M3"
    )
    m3["first_detector"] = "byte_budgets"
    if not validate_publication_contract(
        reader,
        evidence_override=detector_drift,
    ):
        failures.append("historical_matrix_detector_drift")

    provenance_inflation = copy.deepcopy(evidence)
    provenance_inflation["provenance"]["raw_run_logs_registered"] = True
    if not validate_publication_contract(
        reader,
        evidence_override=provenance_inflation,
    ):
        failures.append("unbacked_raw_run_log_claim")

    return failures
