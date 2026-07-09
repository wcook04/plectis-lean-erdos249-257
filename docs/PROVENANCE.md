<!--
SPDX-FileCopyrightText: 2026 Will Cook
SPDX-License-Identifier: Apache-2.0
-->

# Provenance notes

The public Lean package is now `Erdos249257` (Lake package `erdos249257`).

Some provenance records retain `formal_math/erdos257_period_noncollapse` as the
**legacy private export-source root** for the v0.1.x / v0.2.0 lineage. That path
is historical provenance for the private lane; it is **not** the public Lean
import path.

Fields such as `source_root` / `release_selected_source` may therefore still
show the old private path, annotated with
`source_root_role: legacy_private_export_source_root` (or the matching
`release_selected_source_role`) and an explanatory note.
