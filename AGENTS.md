<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Agent entry

This is an ordinary public Lean project and a pinned scholarly artefact. It is
not an entrypoint into any private development system. Work only from the files
in this repository, and never infer unpublished results or private machinery.

## First read

1. Read `docs/orientation.json`. It is the bounded first-read capsule: release
   scale, exact open propositions, principal claim routes, and typed drilldowns.
   Its human projection is `docs/ORIENTATION.md`. Both are generated navigation,
   not proof authority.
2. Drill into `docs/claims.json` only for the selected claim or route. Its
   `machine_readable_paper` object owns the complete map from paper claims to
   Lean declarations, module imports, argument relationships, validation, and
   explicit non-claims. Do not load its exhaustive module graph merely to orient.
3. Read `docs/methodology.json` before changing a public claim. It defines
   the evidence responsibilities, change classes, required reviews, and local
   claim, guard, and negative-fixture references for each rule.
   `METHODOLOGY.md` is the shorter human projection.
4. Read `docs/corpus_descriptor.json` when another agent or system needs to
   register this repository as a mathematical corpus. It separates the pinned
   proof-source tag from the later navigation snapshot and content digests, and
   carries bounded principal handles plus digest-bound expansion routes for both
   authored papers and the paper-to-Lean source-sigil crosswalk. These authored
   surfaces remain distinct from Lean proof authority. The release gate keeps
   this registration envelope below 64 KB.
5. Read `SCOPE.md` before describing what the project proves. Erdős #249 and
   the universal form of #257 remain open.
6. For one claim, follow its `paper_label` into
   `paper/erdos249-257-exposition.tex`, then follow its `declarations` to the
   named Lean source coordinates.
7. Use `docs/declaration_atlas.json` when you need the exhaustive mathematical
   scale: every declaration, signature excerpt, module, import edge, generated
   certificate marker, and principal-claim link. It is a generated navigation
   projection; drill back to Lean before trusting a statement.
8. Use `Erdos249257.lean` for the supported root import and exact package
   topology. Use `docs/SOURCE_MAP.md` for intention-based routes and
   `docs/WAVE_INDEX.md` for mathematical chronology.

For a bounded lookup, use `python3 scripts/query_corpus.py --claim <id>`,
`--paper-label <TeX_label>`, `--paper-anchor <TeX_label_or_source_ref>`,
`--open <remaining_open.id>`, `--declaration <Lean_name>`,
`--source <module.lean:line>`, `--module <path_or_id>`, or `--route <id>`. Use
`--artifact <registered_path_or_sha256>` for a descriptor-registered artefact
or content identity. Use
`--connections <module_or_declaration> --query "<task>"` after selecting a
Lean module or declaration. It returns the source-current public projection of
the shared Lean connection-card contract: directional imports, named consumer
declarations, bounded prerequisite interfaces, source digests, and the exact
refresh route. This is equivalent in navigation grammar to private claim-local
cards, but it is public-only and carries no private claim, unpublished-source,
or proof authority. Consume it before introducing a parallel public result or
changing claim prose.
Use
`--search <text> --limit <1..100>` when the typed handle is not yet known.
JSON responses are capped at 64 KB; exhaustive data remains in the routed owner.
Visible paper sigils resolve directly (`--module CerKer`); their generated
crosswalk is `paper/module-aliases.json`.
Visible TeX labels resolve in reverse (`--paper-label res:farey`) to
their exact paper coordinate and every attached claim.
Every theorem-like or section anchor in either authored paper is classified by
`--paper-anchor`; unlabeled formal results keep their exact TeX source coordinate
as the handle instead of receiving a fabricated label or claim identity. These
packets also expose exact paper-to-Lean source links and adjacent paper handles.
Module packets carry the authored role plus bounded imports, reverse importers,
attached claims, and declaration previews; use their receipts before expanding.
Claim packets carry a resolved local argument neighbourhood; follow adjacent
claim IDs with another `--claim` query instead of loading the complete graph.
The `paper` object is an exact TeX source coordinate and may point to either
paper; do not assume every label lives in the principal exposition.
Each exact ID in `remaining_open_propositions` is directly queryable with
`--open`; do not substitute a finite or conditional progress claim for it.
Declaration packets provide the pinned source URL, module role/sigil, attached
claims, and both claim-owned and local-result paper coordinates; declarations
with neither relation say so explicitly.
Exact Lean coordinates are handles too: `--source Erdos249257/CertificateKernel.lean:18055`
returns the pinned line, its module identity, declarations within the release
checker tolerance, and their claim and paper-anchor routes. A source line with
no nearby declaration remains an honest module/line handle with bounded nearest
declarations; it is not silently promoted to a theorem.
Descriptor-registered source papers, PDFs, JSON owners, JSON fragments, and
their `sha256:` identities round-trip through `--artifact`. The packet preserves
one-to-many digest cardinality and routes into the owning claim, declaration,
paper-anchor, module, methodology, or orientation surface without embedding it.
The helper reads the registry and atlas; it is navigation, not proof authority.

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
python3 scripts/build_module_graph.py --check
python3 scripts/refresh_source_coordinates.py --check
python3 scripts/build_corpus_descriptor.py --check
python3 scripts/test_query_corpus.py
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

After adding, removing, or rewiring Lean modules, run
`python3 scripts/build_module_graph.py` before the other projections.  It
derives paths and imports from source while preserving authored module roles;
it does not author claims or paper prose.
After declaration lines move, rebuild the declaration atlas and run
`python3 scripts/refresh_source_coordinates.py`; it changes coordinates only,
never declaration names or mathematical prose.

A separate diagnostic checks that a cold clone stays readable:

```sh
python3 scripts/check_cold_clone_comprehension.py
python3 scripts/test_cold_clone_comprehension.py
```

It proves the first-contact boundary through a compact human bundle and the
same bounded public query packets a cold coding agent would follow; it does
not concatenate the claim registry, methodology, or declaration atlas as
evidence. It checks navigation semantics and response budgets, not Lean proof
correctness, and runs in the release gate. A failure means a projection, route,
or typed handle dropped a distinction and should be repaired.
The companion adversarial test removes human semantic anchors and mutates proof
authority, open-boundary, finite-bound, source-coordinate, and graph-link
facts; every mutation must make the evaluator fail.
