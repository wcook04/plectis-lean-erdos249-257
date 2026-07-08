/-
SPDX-FileCopyrightText: 2026 Will Cook
SPDX-License-Identifier: Apache-2.0

Generated public API adapter for the Plectis Lean snapshot.
It exposes stable metadata strings for consumers while the private frontier moves.
-/
import Erdos257PeriodNoncollapse
import Erdos257PeriodNoncollapse.CertificateKernel
import Erdos257PeriodNoncollapse.GeneratedCertificates

namespace PlectisSnapshot

def publicApiContractSchema : String := "plectis_lean_public_api_contract_v0"
def publicApiContractVersion : String := "0.1.0-pre"
def sourceSnapshotSHA256 : String := "184c8e24fd40b098df2f4a6feb3f7e81ec7d02943b7045989adf6d5dc6df78e6"
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
