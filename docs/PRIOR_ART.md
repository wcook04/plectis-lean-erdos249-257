<!--
SPDX-FileCopyrightText: 2026 Will Cook
SPDX-License-Identifier: Apache-2.0
-->

# Prior art and attribution map

This is a reading map for the mathematical sources cited in the exposition. It
records relationship, not proof authority: only the pinned Lean source
establishes what this release proves. A citation never widens a release claim,
and a source listed as *context* is not an imported argument or a claim of
mathematical priority. Formalisation/software dependencies are recorded in
[CITATION.cff](../CITATION.cff); the Erdős Problems catalogue supplies
numbering and status context rather than mathematical priority.

The [exposition](../paper/erdos249-257-exposition.tex) is the complete
mathematics bibliography. [CITATION.cff](../CITATION.cff) is intentionally
selected release/software citation metadata: it supplies the recommended
citation for this version and selected foundational or software references,
not a duplicate bibliography. This map explains why the principal sources are
credited.

| Source | Relationship to this release | Boundary |
|---|---|---|
| P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial Number Theory* (1980); P. Erdős, *On the irrationality of certain series: problems and results* (1988) | Original published formulations for the #249 and #257 problem setting. | They formulate open problems; they are not proofs of either universal statement. |
| P. Erdős, *On arithmetical properties of Lambert series* (1948) | Full-support Erdős--Borwein irrationality formalised here. | The formalisation is a checked rendering, not a priority claim. |
| P. Erdős, *On the irrationality of certain series* (1968) | Pairwise-coprime support condition. | Only that classical family is attributed to this source; it does not settle universal #257. |
| P. B. Borwein, *On the irrationality of certain series* (1992) | Broader irrationality theorem containing the relevant Mersenne--Lambert specialisation. | Context for the full-support family, not a proof route for the new #249 reductions. |
| T. M. Apostol, *Introduction to Analytic Number Theory* (1976); M. Merca, [*The Lambert series factorization theorem* (2017)](https://doi.org/10.1007/s11139-016-9856-3); M. Merca and M. D. Schmidt, [*Generating Special Arithmetic Functions by Lambert Series Factorizations* (2019)](https://doi.org/10.55016/ojs/cdm.v14i1.62425) | Apostol supplies the classical Dirichlet/Möbius background; Merca gives the modern factorisation theorem and Merca--Schmidt its synthesis/unification treatment. | The release uses classical transforms and claims a Lean-checked composition, not new Möbius inversion, Lambert identities, or the cited factorisation theorems. |
| Y. V. Nesterenko, [*Modular functions and transcendence questions* (1996)](https://doi.org/10.1070/SM1996v187n09ABEH000158) | Direct source for the cited-only transcendence of the divisor-sum ladder rung \(L(\mathrm{Id})=\sum_{m\geq1}\sigma(m)/2^m\). | This positions one ladder row only; no part of its modular-transcendence proof is formalised here. |
| S. Kakeya, *On the Set of Partial Sums of an Infinite Series* (1914); V. Kovač and T. Tao, [*On several irrationality problems for Ahmes series* (2025)](https://doi.org/10.1007/s10474-025-01528-0) | Kakeya's strict-tail criterion is the general subsum-set source; Kovač--Tao give the direct fixed-base Lambert-subseries instance. | The executable greedy interface and finite certificates are not presented as a priority claim. |
| J. Farey, *On a Curious Property of Vulgar Fractions* (1816) | Historical source for the Farey/mediant language used by the finite denominator-exclusion frames. | The explicit Farey windows and denominator bound are Lean-checked arguments of this release, not historical results. |
| F. Luca and Y. Tachiya, *Irrationality of Lambert series associated with a periodic sequence* (2014) | Context for periodic-coefficient Lambert-series literature. | The repository's named support families are stated only as its own formalised framework. |
| T. Tao and J. Teräväinen, [*Quantitative correlations and some problems on prime factors of consecutive integers* (arXiv v2, 2026)](https://arxiv.org/abs/2512.01739v2) | Direct source for the cited-only irrationality of the prime-support series, through its \(\sum_n\omega(n)/2^n\) formulation and this release's separately formalised identity bridge. | It settles that one support family, not universal #257; its quantitative correlation proof is not formalised here. |
| H. Wang and J. M. Grau Ribas, *Positive dyadic density for rational weighted binary expansions* (2026) | Direct antecedent for the rationality-forced integral carry recurrence in a weighted-binary special case. | The public paper calls its generic carry criterion a formalisation/abstraction; converse and rigidity remain deliberately non-priority language. |
| R. Crandall, *The googol-th bit of the Erdős--Borwein constant* (2012); J. M. Campbell, *On the binary digits of the Erdős--Borwein constant* (2026) | Adjacent work on binary digits of the full-support constant. | Neither result is formalised or used by this release. |

## Audit rule for new sources

Add a public citation only when the source can be tied to a named statement,
method, or historical formulation in the release. Before describing a source as
an antecedent of a local theorem family, record the exact statement comparison:
assumptions, conclusion, specialisation map, proof mechanism, and the remaining
delta. Otherwise, retain it as private research context rather than turning a
bibliographic lead into a public priority claim.
