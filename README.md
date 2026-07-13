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

The Plectis site is an introduction, not a proof certificate. The exposition
explains the mathematics. The checked Lean source establishes the formal
statements.

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
