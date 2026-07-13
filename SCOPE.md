<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Scope of this release

This release does not prove the irrationality of the Erdős #249 totient
constant, and does not prove the universal form of Erdős #257. Its claims
apply only to the source and dependencies identified by the immutable
formal-source checkpoint in [`docs/claims.json`](docs/claims.json). The last
release tag remains the citation and release identity; it can differ from that
checkpoint.

Mathematical proof authority is Lean source at that declared checkpoint after
checking by the pinned Lean kernel. Unreleased work, private repositories,
generated prose, provider output, and hidden proof sketches are not part of
the public proof artefact. Work later than the declared checkpoint is out of
scope even if it checks locally; a later tagged release is a separate citation
and release action, not a substitute for an exact proof-source identity.

## Machine identifiers

These identifiers are the machine-readable form of the scope statement above.
They are declared once in [`docs/claims.json`](docs/claims.json) and
cross-checked against this file by `scripts/check_release.py`, which fails
when any public surface drifts from them.

| Identifier | Public meaning |
|---|---|
| `not_erdos_249_solution` | The release does not settle Erdős #249 |
| `not_erdos_257_solution` | The release does not settle the universal Erdős #257 |
| `not_publication_authority` | The release is not itself a peer-reviewed publication record |
| `not_private_root_equivalence` | The release is not asserted to be equivalent to any private development |
| `not_provider_proof_authority` | Provider or model output is not proof authority; the Lean kernel check is |
| `not_hidden_proof_body_authority` | No unpublished proof sketch or hidden artefact carries proof authority |
