<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Erdős Problems 249 and 257 in Lean 4

Formalised results, certificate reductions, and open questions.

[**Plectis website**](https://wcook04.github.io/plectis/) ·
[Plectis source](https://github.com/wcook04/plectis) ·
[**Exposition PDF**](erdos249-257-exposition.pdf) ·
[Release v0.6.0](https://github.com/wcook04/plectis-lean-erdos249-257/releases/tag/v0.6.0) ·
[![Lean CI](https://github.com/wcook04/plectis-lean-erdos249-257/actions/workflows/lean.yml/badge.svg)](https://github.com/wcook04/plectis-lean-erdos249-257/actions/workflows/lean.yml)

This is the standalone Lean 4 development behind the Erdős #249/#257 example on
Plectis. It contains machine-checked results around two open irrationality
problems. **This release does not solve Erdős #249 or the universal form of
Erdős #257.**

## Read this first

1. [Open Plectis](https://wcook04.github.io/plectis/) for the plain account of
   where this project sits and what the public claim is.
2. [Read the exposition PDF](erdos249-257-exposition.pdf) for the mathematics in
   ordinary notation. It is the canonical human-readable account; this README
   is only a route into it.
3. Follow the links in the paper to the Lean source. Source checked by the
   pinned Lean kernel is proof authority.
4. Use [`docs/claims.json`](docs/claims.json) for the exact release status,
   declaration coordinates, argument map, and explicit non-claims.

For a bounded view of the whole public corpus before drilling down, use the
generated [corpus orientation](docs/ORIENTATION.md), or
[`docs/orientation.json`](docs/orientation.json) from an agent. It shows the
release scale, exact open boundary, principal claim routes, and the next
authoritative surface for each kind of question.

For one bounded lookup, run `python3 scripts/query_corpus.py --claim <id>`,
`--declaration <Lean_name>`, `--module <path_or_id>`, or `--route <id>`.

The Plectis site is an introduction, not a proof certificate. The exposition
explains the mathematics. The checked Lean source establishes the formal
statements.

The source tree is large enough that opening modules at random is not a useful
reading strategy. For source inspection, use Claude Code, Codex, Cursor, or
another coding harness that can read the repository and run its local checks.
The harness should follow the maintained routes below and trace one claim at a
time; its explanation is not proof authority.

## What this release establishes

- **Erdős-Borwein and named #257 support cases.** For every integer base
  `b ≥ 2`, the full-support series `∑ 1/(bⁿ - 1)` is irrational. The development
  also treats several named infinite supports, including factorials, powers of
  two, multiples, pairwise-coprime supports, and eventually periodic supports.
- **An unconditional exclusion for #249.** If the totient constant
  `S = ∑ φ(n)/2ⁿ` is rational, its denominator is greater than
  `79 639 646 646 701 375 323 355 774 875 831 053`, approximately
  `7.96 × 10³⁴`. This is not a proof that `S` is irrational.
- **An exact finite-certificate reduction for #249.** Irrationality follows from
  certified non-integrality witnesses at unbounded parameters. The existence of
  that unbounded certificate supply remains open. The release verifies 22
  explicit lcm-diagonal scales through `t = 43`; a verified finite instance does
  not change the unbounded quantifier.
- **Necessary conditions for rational support values.** The formal development
  records carry-orbit, reciprocal-mass, unbounded-state, achievement-set, and
  sublogarithmic divisor-coverage constraints. These do not prove the universal
  #257 statement.

The [exposition](erdos249-257-exposition.pdf) states each result with its
hypotheses and proof status. The
[transport and curvature companion](erdos249-transport-curvature.pdf) gives the
separate technical account of the affine transport and fixed-precision
boundary.

## What remains open

- Prove that `S = ∑ φ(n)/2ⁿ` is irrational without placing a bound on a possible
  rational denominator.
- Produce the unbounded certificate supply required by the exact #249
  reduction.
- Prove irrationality of `∑_{n∈A} 1/(2ⁿ - 1)` for every infinite
  `A ⊆ ℕ`, rather than only the named support families formalised here.

[`SCOPE.md`](SCOPE.md) is the short boundary statement. The paper gives the full
mathematical boundary.

## Find the right source

- **Mathematics:** [`erdos249-257-exposition.pdf`](erdos249-257-exposition.pdf)
  and its [LaTeX source](paper/erdos249-257-exposition.tex).
- **Exact claim status:** [`docs/claims.json`](docs/claims.json).
- **Bounded corpus map:** [`docs/ORIENTATION.md`](docs/ORIENTATION.md) and
  [`docs/orientation.json`](docs/orientation.json).
- **External corpus registration:**
  [`docs/corpus_descriptor.json`](docs/corpus_descriptor.json), a bounded
  envelope with digest-bound expansion paths.
- **Method:** [`METHODOLOGY.md`](METHODOLOGY.md), generated from
  [`docs/methodology.json`](docs/methodology.json).
- **Lean routes by question:** [`docs/SOURCE_MAP.md`](docs/SOURCE_MAP.md).
- **Complete declaration index:** Appendix B of the exposition and
  [`docs/declaration_atlas.json`](docs/declaration_atlas.json).
- **Development chronology:** [`docs/WAVE_INDEX.md`](docs/WAVE_INDEX.md).
- **Prior art:** [`docs/PRIOR_ART.md`](docs/PRIOR_ART.md).
- **Agent entry:** [`AGENTS.md`](AGENTS.md).

Long Lean identifiers are kept out of the main reading path. The source map and
declaration atlas are the maintained indexes.

## Read it with a coding agent

Clone the repository, open it in Claude Code, Codex, Cursor, or another coding
harness with filesystem and terminal access, and give it a mathematical
question rather than asking it to summarise every file. A useful starting
prompt is:

```text
Read AGENTS.md and docs/orientation.json first. Then select one claim and read
its row in docs/claims.json, SCOPE.md, and the exposition PDF.
For the claim or question I give you, trace its paper anchor, status, Lean
declaration, source module, and direct dependencies. State separately what is
proved, what is conditional, what is verified only at finite parameters, and
what remains open. Cite exact repository paths. Run scripts/check_release.py
before reporting, and do not infer results from private or unreleased work.
```

Then ask it to trace one item, for example the denominator exclusion, the
finite-certificate reduction, one named #257 support family, or the
sublogarithmic zero-window theorem. The maintained claim and source maps make
those bounded walks possible; a whole-repository summary usually hides the
distinction between a theorem, a reduction, and a finite certificate.

## How the repository fits together

The published package has one supported root import,
[`Erdos249257.lean`](Erdos249257.lean). Beneath it, the source is organised into
four reader-facing layers:

- **Assembled kernel.** [`CertificateKernel.lean`](Erdos249257/CertificateKernel.lean)
  contains the common series machinery, the full-support Erdős-Borwein theorem,
  named support-family interfaces, and the unconditional #249 denominator
  exclusion.
- **The #249 reduction spine.** The period-killer, lcm-diagonal, cone, diagonal
  pincer, fresh-loss, and transport modules turn the open irrationality problem
  into exact certificate or avoidance obligations. Finite certificate modules
  verify explicit parameters; they do not supply the unbounded family that the
  reduction requires.
- **The #257 carry trunk.** The tail-orbit, achievement-set, Boolean-Möbius
  carry, reciprocal-mass, and divisor-coverage modules describe what a rational
  support value would force. They give exact criteria and necessary conditions,
  not the universal #257 theorem.
- **The reading and audit layer.** The exposition gives the authored
  mathematical account. [`docs/claims.json`](docs/claims.json) binds statuses,
  paper anchors, declarations, modules, and argument edges. The
  [`source map`](docs/SOURCE_MAP.md) gives grouped routes, while the generated
  [`declaration atlas`](docs/declaration_atlas.json) covers every public
  declaration. `scripts/check_release.py` checks that these surfaces still
  agree with the source and the stated open boundary.

[`docs/SOURCE_MAP.md`](docs/SOURCE_MAP.md) gives the exact module order within
each band. [`docs/WAVE_INDEX.md`](docs/WAVE_INDEX.md) gives the development
chronology; it is not the recommended first reading order.

<details>
<summary>Principal Lean declaration anchors</summary>

These names are included for source search and automated release checks. The
paper and source map explain what they say.

- `irrational_erdosSum_full_support`
- `irrational_erdosBorwein_series`
- `erdos257_family_factorial_instance`
- `tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053`
- `irrational_totient_series_of_certificate_supply`
- `exists_certifiedKill_iff_tail_diff_notMem_int`
- `certifiedKill_all_small`
- `diagonal_int_iff_foreignDiagonalDefect_hits_fullTarget`
- `supportCoeffZeroWindow_length_le_eps_logb_add`

</details>

## Build and verify

The project uses `leanprover/lean4:v4.29.1` with Mathlib pinned by
[`lake-manifest.json`](lake-manifest.json).

```sh
lake exe cache get
lake build
```

On a memory-constrained machine:

```sh
python3 scripts/lean_fast_build.py --jobs 2
```

Check the public release surfaces separately:

```sh
python3 scripts/check_release.py
python3 scripts/test_methodology_contract.py
```

There is no `sorry`, `admit`, project-defined `axiom`, or `native_decide` in the
checked source. Finite computations use `decide`, whose proof terms are checked
by the Lean kernel.

## Use as a Lean package

Import the supported root:

```lean
import Erdos249257
```

[`examples/Examples.lean`](examples/Examples.lean) is the minimal downstream
consumer. It imports the package root and derives the base-3 instance of the
full-support theorem.

## Citation and licence

Cite release `v0.6.0` using [`CITATION.cff`](CITATION.cff). For the mathematics,
cite the exposition included in the release.

Code, scripts, and documentation are Apache-2.0. The manuscript layer, including
the paper source and rendered PDFs, is CC-BY-4.0. The complete licence map is in
[`REUSE.toml`](REUSE.toml).

Errors and corrections are welcome through the repository issue forms.
[`CONTRIBUTING.md`](CONTRIBUTING.md) explains the release-pinning rule and local
checks; [`SECURITY.md`](SECURITY.md) gives the private reporting route.
