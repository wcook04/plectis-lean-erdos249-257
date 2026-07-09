<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Snapshot Notes

Publication status: blocked until a clean build receipt and public tag/hash exist.

Snapshot name: `Erdos #249/#257 Lean Snapshot`
Public package: `erdos249257` (Lake) / `Erdos249257` (Lean root import)
Tagged release: `v0.2.0` (ships the Erdos249257 rename with contract files at repository root)
HEAD candidate: unreleased after `v0.2.0` (`v0.2.1` candidate; not tagged)
Public tag for HEAD: `pending`
Public commit for HEAD: `pending`

## Breaking change (v0.2.0)

The public Lean import path changed:

- was: `import Erdos257PeriodNoncollapse`
- now: `import Erdos249257`

There is no compatibility shim. Consumers on the old import path should pin the
`v0.1.0` tag.

The `v0.2.0` tag renames the Lake package, Lean root module, source directory,
outer project namespaces, Plectis adapter imports, paper macro/path references,
and provenance digests. Topic namespaces such as `GapFareyBound` are preserved.
Mathematical claims are unchanged. On that tag, Plectis export-contract files
still live at the repository root.

## Unreleased after v0.2.0 (`v0.2.1` candidate)

HEAD after `v0.2.0` moves the Plectis export-contract layer behind one named
boundary. This is not the `v0.2.0` tag.

- contract / provenance / non-claim / reference files moved into `snapshot/`
- standalone verifier and public contract refs updated to `snapshot/...` paths
- provenance subject digest recomputed for the new layout
- mathematical claims and Lean proof sources unchanged
- no new public tag yet; promotion still requires the publication gates below

Selected source files: `19`

This generated note is intentionally not a publication announcement. It records the local export candidate and the gates still required before public promotion.

Required before promotion:

- clean standalone Lake build receipt
- public repository URL
- public tag
- public commit hash
- Plectis import pointer update
