<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Contributing

This repository is a pinned scholarly artefact, so contributions work a
little differently from an ordinary software project: the mathematics, the
paper, and the metadata are released together as one citable object, and
substantial changes land only as a new tagged release with refreshed claim
and citation metadata.

## What is welcome

- **Error reports.** A wrong or misstated result, a Lean build failure, a
  broken source/paper link, or an exposition mistake. Use the issue forms;
  each one asks for exactly the evidence that makes the report checkable.
- **Corrections.** Fixes to prose, citations, or documentation that do not
  change any mathematical claim.
- **Strengthenings.** New formalised results are best proposed in an issue
  first, since they change the claim registry and therefore the release.

## The rules that keep the release trustworthy

- `docs/claims.json` is the single owner of release identity and claim
  status. Never edit a status table, the scope statement, or citation
  metadata directly without updating the registry; `scripts/check_release.py`
  fails when any surface drifts from it.
- Do not weaken the open-problem boundary. The release states plainly that
  Erdős #249 and the universal #257 remain open; wording that blurs that is a
  defect, not an improvement.
- No `sorry`, `admit`, new `axiom`, or `native_decide` anywhere in the Lean
  sources, including `examples/`.
- The paper pins every source link to the release tag. Changes that move
  declaration line numbers require regenerating those pins as part of a new
  release, not as a drive-by edit.

## Local checks

```sh
lake exe cache get                 # fetch the prebuilt Mathlib cache
lake build                         # elaborate and kernel-check the library
lake build Examples                # build the downstream consumer example
python3 scripts/check_release.py   # cross-surface release checks
```

CI runs the build and the release-surface checks (including `cffconvert` and
`reuse lint`) on every push.
