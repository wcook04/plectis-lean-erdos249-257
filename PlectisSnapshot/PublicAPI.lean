/-
SPDX-FileCopyrightText: 2026 Will Cook
SPDX-License-Identifier: Apache-2.0

Generated public API adapter for the Plectis Lean snapshot.
It exposes stable metadata strings for consumers while the private frontier moves.
-/
import Erdos249257
import Erdos249257.CertificateKernel
import Erdos249257.GeneratedCertificates

namespace PlectisSnapshot

def publicApiContractSchema : String := "plectis_lean_public_api_contract_v0"
def publicApiContractVersion : String := "0.1.0-pre"
def sourceSnapshotSHA256 : String := "c93b6622f144513f9b014e9cc4fbb44dafb4abdd6e791a40b020466c7fbbee57"
def sourceFileCount : Nat := 19
def plectisConsumptionMode : String := "pointer_only_until_public_tag"

def exposedDeclarationFamilies : List String :=
[
  "certificate_kernel",
  "generated_certificate_aggregate",
  "selected_certificate_shards",
  "target_runner_declarations",
  "non_claim_ids",
  "receipt_schema_ids",
]

def nonClaimIds : List String :=
[
  "not_erdos_257_solution",
  "not_erdos_249_solution",
  "not_publication_authority",
  "not_private_root_equivalence",
  "not_provider_proof_authority",
  "not_hidden_proof_body_authority",
]

end PlectisSnapshot
