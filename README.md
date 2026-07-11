<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Erdős #249/#257: a Lean 4 formalisation

Machine-checked results around two Erdős irrationality problems. **This release does not solve either open problem**; it formalises irrationality for named support families, an unconditional denominator exclusion, exact certificate reductions, and rationality-forced carry constraints — and it states its own boundary precisely.

[![Lean CI](https://github.com/wcook04/plectis-lean-erdos249-257/actions/workflows/lean.yml/badge.svg)](https://github.com/wcook04/plectis-lean-erdos249-257/actions/workflows/lean.yml)

Erdős #249 asks whether the totient constant `S = ∑_{n≥1} φ(n)/2ⁿ` is irrational. Erdős #257 asks whether `∑_{n∈A} 1/(2ⁿ − 1)` is irrational for every infinite `A ⊆ ℕ`. This Lean 4 (Mathlib) development verifies the irrationality of the Erdős–Borwein series `∑ 1/(bⁿ − 1)` for every integer base `b ≥ 2` and for several structured infinite supports; proves unconditionally that `S ≠ p/q` for every denominator `q` up to about `7.96 × 10³⁴`; and reduces the irrationality of `S`, exactly, to an unbounded supply of finite decidable certificates. A binary-carry layer then pins down what a rational value of either series would force: tempered carry orbits, reciprocal-mass lower bounds, unbounded carry states, and sublogarithmic zero windows in divisor coverage.

Everything needed to build and check the release is in this repository. There is no `sorry`, no `admit`, and no additional axiom; finite computations use `decide`, whose proof terms are checked by the Lean kernel (`native_decide` is never used). Toolchain `leanprover/lean4:v4.29.1`; Mathlib pinned by [`lake-manifest.json`](lake-manifest.json).

## What is proved, reduced, and open

Statuses use the release taxonomy declared once in [`docs/claims.json`](docs/claims.json); `scripts/check_release.py` fails the build if this table drifts from it.

| Result | Status | Lean declaration |
|---|---|---|
| `∑ 1/(bⁿ − 1)` irrational for every base `b ≥ 2` (Erdős, 1948) | **formalised here** | `irrational_erdosSum_full_support` |
| The Erdős–Borwein constant `E` is irrational | **formalised here** | `irrational_erdosBorwein_series` |
| Named infinite-support families: factorial, powers of two, multiples, pairwise-coprime, eventually periodic | **formalised here** | `erdos257_family_factorial_instance`, `erdos257_family_two_pow_instance`, `irrational_erdosSupportSeries_pairwise_coprime` |
| `S ≠ p/q` for every `q ≤ 7.96 × 10³⁴` | **unconditional progress** | `tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053` |
| Unbounded certificate supply ⟹ `S` irrational (period ⟹ lcm-diagonal ⟹ cone) | **conditional reduction** | `irrational_totient_series_of_certificate_supply`, `irrational_totient_series_of_lcm_diagonal_certificate_supply` |
| A certificate exists ⟺ the tail difference is non-integral | **proved here** | `exists_certifiedKill_iff_tail_diff_notMem_int` |
| Initial certified-kill segment and generated certificate shards | **verified finite instance** | `certifiedKill_all_small`, `certifiedKill_periodLcm_diagonal_upto_six` |
| Rationality forces sublogarithmic divisor-coverage zero windows | **proved here** | `supportCoeffZeroWindow_length_le_eps_logb_add` |
| Transcendence of `∑ σ(m)/2^m` (Nesterenko); prime-support irrationality (Tao–Teräväinen) | **cited only** | — |
| Erdős #249; the universal Erdős #257 | **open** | — |

The conditional reduction is exact: producing the unbounded certificate supply is the untouched analytic core of #249, and the proved support families are not the universal #257 statement. The scope statement lives in [`SCOPE.md`](SCOPE.md).

## Start here

- **Machine-readable paper and agent map** — [`docs/claims.json`](docs/claims.json): the single checked map of claim status, paper anchors, principal Lean declarations, module dependencies, argument relationships, and explicit non-claims. The generated [`docs/declaration_atlas.json`](docs/declaration_atlas.json) exposes every public Lean declaration and import edge so the full mathematical scale is queryable at once. Agent harnesses should begin with [`AGENTS.md`](AGENTS.md).
- **The paper** — [`erdos249-257-exposition.pdf`](erdos249-257-exposition.pdf): the full argument in ordinary notation, no Lean required. Every formal statement links to the exact declaration at the pinned release. Source and build in [`paper/`](paper/).
- **Module reference and chronology** — [`docs/WAVE_INDEX.md`](docs/WAVE_INDEX.md): what each module establishes, in development order.
- **Declaration routes** — [`docs/SOURCE_MAP.md`](docs/SOURCE_MAP.md): intention-based routes to the principal declarations.
- **Neighbouring problems** — [`docs/RELATED_PROBLEMS.md`](docs/RELATED_PROBLEMS.md): where this sits among Erdős #249/#257/#1049/#69/#250/#258.
- **Scope** — [`SCOPE.md`](SCOPE.md): what this release deliberately does not claim.

## Build and verify

```sh
lake exe cache get   # fetch the prebuilt Mathlib cache
lake build           # elaborate and kernel-check the whole package
```

On memory-constrained machines, use the bounded build wrapper instead:

```sh
python3 scripts/lean_fast_build.py --jobs 2
```

Lake 5 can start every ready local module at once; this wrapper prebuilds stale
modules in dependency order with at most two Lean processes, then runs the
ordinary `lake build` authority check. Set `--jobs` higher only after measuring
memory headroom.

The build is heavy (thousands of `decide`-discharged certificates); continuous integration runs it on every push. The release surfaces are checked separately:

```sh
python3 scripts/check_release.py   # claim registry, paper links, metadata, scope, licences
```

The checker verifies that the paper's source links resolve to the named declarations at the stated lines, that README/paper/`CITATION.cff`/`SCOPE.md` agree with the claim registry, that no Lean source uses `sorry`/`admit`/`axiom`/`native_decide` (the downstream examples included), and that every licence in use has its text under `LICENSES/`.

## Headline Lean interface

The supported entry point is the root import:

```lean
import Erdos249257
```

| Declaration | Statement | Module |
|---|---|---|
| `irrational_erdosSum_full_support` | `∑ 1/(bⁿ − 1)` irrational, all `b ≥ 2` | [`CertificateKernel`](Erdos249257/CertificateKernel.lean) |
| `tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053` | the denominator exclusion for `S` | [`CertificateKernel`](Erdos249257/CertificateKernel.lean) |
| `totient_series_eq_half_add_moebius_mersenne_square` | the Möbius-square lens `S = 1/2 + ∑ μ(d)/(2^d−1)²` | [`CertificateKernel`](Erdos249257/CertificateKernel.lean) |
| `irrational_totient_series_of_lcm_diagonal_certificate_supply` | the one-parameter #249 reduction | [`LcmDiagonalReduction`](Erdos249257/LcmDiagonalReduction.lean) |
| `binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit` | rationality ⟺ tempered carry orbit | [`GenericTailOrbitRigidity`](Erdos249257/GenericTailOrbitRigidity.lean) |
| `supportCoeffZeroWindow_length_le_eps_logb_add` | sublogarithmic zero windows from rationality | [`SublogDivisorCoverage`](Erdos249257/SublogDivisorCoverage.lean) |

The exhaustive declaration map, with one row per principal statement, is Appendix B of the paper.

A minimal downstream consumer lives in [`examples/Examples.lean`](examples/Examples.lean): it imports the package root exactly as an external project would and re-derives a corollary (the base-3 instance of the headline theorem) through this interface. CI builds it with `lake build Examples` on every push, so the package is proven externally usable, not merely internally buildable.

## Citation, licence, and support

Cite the tagged release `v0.4.0` using [`CITATION.cff`](CITATION.cff); for the mathematics, cite the exposition included in the release. Code, scripts, and documentation are licensed Apache-2.0; the manuscript layer (paper source, rendered PDF, banner) is CC-BY-4.0; the map is [`REUSE.toml`](REUSE.toml) with licence texts under [`LICENSES/`](LICENSES/).

This release is a pinned scholarly artefact. Error reports are welcome through the GitHub issue forms (mathematical discrepancy, build failure, broken link, exposition correction); [`CONTRIBUTING.md`](CONTRIBUTING.md) explains the release-pinning rule and the local checks, and [`SECURITY.md`](SECURITY.md) the private reporting route. Substantial changes land only as a new tagged release with refreshed claim and citation metadata.

---

*Project context.* This formalisation is one lane of a broader programme; the adjacent public claim-testing surface is [Plectis](https://github.com/wcook04/plectis). None of that tooling is proof authority here: the proof authority is the Lean source in this repository, checked by the Lean kernel.
