<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Agent entry

This is an ordinary public Lean project and a pinned scholarly artefact. It is
not an entrypoint into any private development system. Work only from the files
in this repository, and never infer unpublished results or private machinery.

## First read

1. Read `docs/claims.json`. Its `machine_readable_paper` object is the compact
   map from open problems and paper claims to Lean declarations, module imports,
   argument relationships, validation, and explicit non-claims.
2. Read `SCOPE.md` before describing what the project proves. Erdős #249 and
   the universal form of #257 remain open.
3. For one claim, follow its `paper_label` into
   `paper/erdos249-257-exposition.tex`, then follow its `declarations` to the
   named Lean source coordinates.
4. Use `docs/declaration_atlas.json` when you need the exhaustive mathematical
   scale: every declaration, signature excerpt, module, import edge, generated
   certificate marker, and principal-claim link. It is a generated navigation
   projection; drill back to Lean before trusting a statement.
5. Use `Erdos249257.lean` for the supported root import and exact package
   topology. Use `docs/SOURCE_MAP.md` for intention-based routes and
   `docs/WAVE_INDEX.md` for mathematical chronology.

## Authority and change order

- Lean source checked by the pinned Lean kernel is proof authority.
- `docs/claims.json` owns release identity, status taxonomy, declaration
  coordinates, and the machine-readable navigation graph.
- The paper is authored mathematical exposition. Do not generate or rewrite its
  prose mechanically from the registry.
- README, scope, source maps, and other summaries must not exceed the status in
  the claim registry.
- Provider or model output is never proof authority.

When a theorem statement or public claim changes, update Lean first, then the
claim registry, then every affected human projection. A proof-body-only change
does not automatically authorize stronger prose. New mathematics requires
explicit review of the open-problem boundary and the paper-facing claim.

## Validation

Run the focused public-surface gate after documentation or registry changes:

```sh
python3 scripts/check_release.py
```

Run the full proof authority check after Lean changes:

```sh
lake build
```

The release checker validates claim status, declaration coordinates, paper
anchors, the machine-readable module and argument graphs, the exhaustive
declaration atlas, scope, metadata, licensing, and proof-trust guards. Do not
add `sorry`, `admit`, `axiom`, or `native_decide`; finite computations use
kernel-checked `decide`.
