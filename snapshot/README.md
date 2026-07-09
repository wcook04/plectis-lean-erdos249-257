<!--
SPDX-FileCopyrightText: 2026 Will Cook
SPDX-License-Identifier: Apache-2.0
-->

# Snapshot contract

This directory contains the Plectis export contract for the standalone Lean
snapshot. These files are machine-readable provenance, non-claim, publication,
reference, and consumer-contract surfaces. They are not Lean proof authority.

Proof authority lives in `../Erdos249257.lean` and `../Erdos249257/`, checked by
Lean/Lake. The stable adapter for Plectis consumers lives in
`../PlectisSnapshot.lean` and `../PlectisSnapshot/PublicAPI.lean`.

Start here:
- `PUBLIC_SNAPSHOT_MANIFEST.json` — snapshot manifest and publication gates
- `PUBLIC_API_CONTRACT.json` — stable consumer contract
- `PLECTIS_INTEGRATION.json` — parent Plectis integration pointer
- `NON_CLAIMS.md` and `RELEASE_BOUNDARY.md` — what this snapshot does not claim
- `RELEASE_PROVENANCE.json` — subject-tree provenance
- `CLAIM_TO_REFERENCE_MAP.json` and `REFERENCES.yaml` — claim/reference map
