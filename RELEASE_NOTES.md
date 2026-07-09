<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Snapshot Notes

Publication status: blocked until a clean build receipt and public tag/hash exist.

Snapshot name: `Erdos #249/#257 Lean Snapshot`
Public package: `erdos249257` (Lake) / `Erdos249257` (Lean root import)
Release candidate: `v0.2.0`
Public tag: `pending`
Public commit: `pending`

## Breaking change (v0.2.0)

The public Lean import path changed:

- was: `import Erdos257PeriodNoncollapse`
- now: `import Erdos249257`

There is no compatibility shim. Consumers on the old import path should pin the
`v0.1.0` tag.

This release renames the Lake package, Lean root module, source directory,
outer project namespaces, Plectis adapter imports, public API contract paths,
snapshot manifest paths, paper macro/path references, and provenance digests.
Topic namespaces such as `GapFareyBound` are preserved. Mathematical claims are
unchanged.

Selected source files: `19`

This generated note is intentionally not a publication announcement. It records the local export candidate and the gates still required before public promotion.

Required before promotion:

- clean standalone Lake build receipt
- public repository URL
- public tag
- public commit hash
- Plectis import pointer update
