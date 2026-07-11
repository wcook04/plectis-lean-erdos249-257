-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import Erdos249257

/-!
# Minimal downstream consumer

This module is not part of the `Erdos249257` library. It imports the package
root exactly as an external project would (`import Erdos249257`) and derives a
small corollary through the advertised public interface, so the release is
demonstrably usable from outside, not merely internally buildable. CI builds
it with `lake build Examples`.

The same proof-trust rules apply here as in the library: no `sorry`, no
`admit`, no new axioms (`scripts/check_release.py` scans this directory too).
-/

open Erdos249257

/-- Downstream instance of the headline theorem: the base-3 series
`∑ 1/(3ⁿ − 1)` is irrational, obtained by specialising
`irrational_erdosSum_full_support` exactly as a consumer project would. -/
theorem downstream_base_three_irrational :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((3 : ℝ) ^ (k + 1) - 1)) := by
  have h := irrational_erdosSum_full_support 3 (by norm_num)
  have hcast : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
  rwa [hcast] at h

/-- The release's own base-2 headline, reached through the public root
import: the Erdős–Borwein constant is irrational. -/
example : Irrational (∑' k : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (k + 1) - 1)) :=
  irrational_erdosBorwein_series
