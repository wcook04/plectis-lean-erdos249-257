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
2. Read `docs/methodology.json` for the literal mathematical methodology,
   evidence classes, remaining-open requirements, and claim-transition rules.
   `METHODOLOGY.md` is its generated human projection.
3. Read `docs/corpus_descriptor.json` when another agent or system needs to
   register this repository as a mathematical corpus. It separates the pinned
   proof-source tag from the later navigation snapshot and content digests, and
   carries a compact methodology capsule.
4. Read `SCOPE.md` before describing what the project proves. Erdős #249 and
   the universal form of #257 remain open.
5. For one claim, follow its `paper_label` into
   `paper/erdos249-257-exposition.tex`, then follow its `declarations` to the
   named Lean source coordinates.
6. Use `docs/declaration_atlas.json` when you need the exhaustive mathematical
   scale: every declaration, signature excerpt, module, import edge, generated
   certificate marker, and principal-claim link. It is a generated navigation
   projection; drill back to Lean before trusting a statement.
7. Use `Erdos249257.lean` for the supported root import and exact package
   topology. Use `docs/SOURCE_MAP.md` for intention-based routes and
   `docs/WAVE_INDEX.md` for mathematical chronology.

## Authority and change order

- Lean source checked by the pinned Lean kernel is proof authority.
- `docs/claims.json` owns release identity, status taxonomy, declaration
  coordinates, typed remaining-open propositions, and the machine-readable
  navigation graph.
- `docs/methodology.json` owns mathematical methodology and claim-transition
  requirements. It is not proof authority and does not own claim status.
- `docs/corpus_descriptor.json` is a generated, compact registration envelope;
  it does not replace the claim registry, exhaustive atlas, or Lean authority.
- The paper is authored mathematical exposition. Do not generate or rewrite its
  prose mechanically from the registry.
- README, scope, source maps, and other summaries must not exceed the status in
  the claim registry.
- Provider or model output is never proof authority.

Before updating a public claim, classify whether the change affects only a
proof body or changes a proposition, assumptions, representation, finite
range, claim status, exposition, or projection. Update Lean first, then review
assumptions and intended meaning, then update the claim registry, authored
exposition, and generated projections in that order. A proof-body-only change
does not automatically authorize stronger prose. New mathematics requires
explicit human mathematical review of the paper-facing statement and the
remaining-open boundary.

## Validation

Run the focused public-surface gate after documentation or registry changes:

```sh
python3 scripts/check_release.py
python3 scripts/test_methodology_contract.py
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
