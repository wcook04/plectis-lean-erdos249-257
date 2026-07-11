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
2. Read `docs/methodology.json` before changing a public claim. It defines
   the evidence responsibilities, change classes, required reviews, and local
   claim, guard, and negative-fixture references for each rule.
   `METHODOLOGY.md` is the shorter human projection.
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

Before updating a public claim, classify the change against the
`change_classes` matrix in `docs/methodology.json`: each class states its
minimum evidence, whether human mathematical review is required, and the
effects the change must not have. The update order stays fixed: Lean source
first, then assumption and meaning review, then the claim registry, then
authored exposition, then generated projections.

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

A separate diagnostic checks that a cold clone stays readable:

```sh
python3 scripts/check_cold_clone_comprehension.py
python3 scripts/test_cold_clone_comprehension.py
```

It derives the proved/open distinctions from the claim registry and confirms
both the prose surfaces and the machine surfaces still let a reader recover
them. It measures availability, not mathematical correctness, and is not part
of the release gate; a failure means a projection or route dropped a
distinction and should be repaired.
The companion adversarial test removes each machine token and each grouped
human semantic anchor in turn; every such mutation must make the diagnostic
fail, so generic vocabulary cannot masquerade as comprehension.
