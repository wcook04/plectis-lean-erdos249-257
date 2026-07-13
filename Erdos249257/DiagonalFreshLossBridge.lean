import Erdos249257.DiagonalPincerDecomposition
import Erdos249257.LcmConeNonflat

/-!
# Diagonal fresh-loss bridge

This module connects the operational binary window at the two LCM vertices
`[1, 2]` to the constitutional full-target pincer.  The certificate itself is
the existing one-sided cone certificate; the point of this file is the direct
consumer theorem

`diagonalFreshLossProjectionCert t L ->
  not ForeignDiagonalDefectHitsFullTarget t`.

The bridge is denominator-free.  It does not claim an avoidance supply and it
does not identify the foreign defect with a fresh-prime loss series.  That
analytic representation remains a separate theorem-development lane.  What is
proved here is that the exact `[1, 2]` binary projection is already the right
finite consumer for the full reduced target.  The adjacent-suffix route is
further reduced to centrality of one canonical depth at arbitrarily large LCM
heights (or just at strict LCM jumps); the guard-bit width is automatic.
-/

namespace Erdos249257.DiagonalFreshLossBridge

open TotientTailPeriodKiller
open DiagonalPincerDecomposition

/-- The exact two-vertex operational projection at the LCM height `H_t`.

For this menu, the two rows of `coneNonflatCert` are precisely the asymmetric
safe-interval test on the residue of
`windowNumerator (2 * H_t) L - windowNumerator H_t L`. -/
def diagonalFreshLossProjectionCert (t L : ℕ) : Prop :=
  coneNonflatCert (periodLcm t) L [1, 2]

instance (t L : ℕ) : Decidable (diagonalFreshLossProjectionCert t L) :=
  inferInstanceAs (Decidable (coneNonflatCert (periodLcm t) L [1, 2]))

/-- The signed depth-`L` binary window residue on the diagonal pair. -/
def diagonalWindowResidue (t L : ℕ) : ℤ :=
  ((windowNumerator (2 * periodLcm t) L : ℤ) -
    (windowNumerator (periodLcm t) L : ℤ)) % 2 ^ L

/-- The explicit asymmetric safe interval for the diagonal residue.  This is
the denominator-free form of the finite full-target certificate. -/
def diagonalFreshLossResidueCert (t L : ℕ) : Prop :=
  (periodLcm t + L + 2 : ℤ) < diagonalWindowResidue t L ∧
    diagonalWindowResidue t L < 2 ^ L - (2 * periodLcm t + L + 2)

instance (t L : ℕ) : Decidable (diagonalFreshLossResidueCert t L) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- On the two-vertex menu, the generic cone certificate is exactly the
asymmetric residue-safe interval.  This pins the operational shape used by
the diagnostic probe to a kernel theorem rather than a comment-level analogy. -/
theorem diagonalFreshLossResidueCert_iff_projectionCert (t L : ℕ) :
    diagonalFreshLossResidueCert t L ↔
      diagonalFreshLossProjectionCert t L := by
  let H := periodLcm t
  let P1 : ℤ := windowNumerator H L
  let P2 : ℤ := windowNumerator (2 * H) L
  let W : ℤ := P2 - P1
  let M : ℤ := 2 ^ L
  have hMpos : 0 < M := by simp [M]
  constructor
  · intro hres
    have hleft : (H + L + 2 : ℤ) < W % M := by
      simpa [diagonalFreshLossResidueCert, diagonalWindowResidue, H, P1, P2, W, M]
        using hres.1
    have hright : W % M < M - (2 * H + L + 2) := by
      simpa [diagonalFreshLossResidueCert, diagonalWindowResidue, H, P1, P2, W, M]
        using hres.2
    have hWpos : 0 < W % M := by omega
    have hMnotDvdW : ¬M ∣ W := by
      intro hdvd
      rw [Int.emod_eq_zero_of_dvd hdvd] at hWpos
      omega
    intro qi hqi
    simp at hqi
    rcases hqi with rfl | rfl
    · refine ⟨2, by simp, ?_⟩
      have hneg : (2 * H + L + 2 : ℤ) < (P1 - P2) % M := by
        rw [show P1 - P2 = -W by simp [W], Int.neg_emod,
          if_neg hMnotDvdW]
        rw [Int.natAbs_of_nonneg hMpos.le]
        omega
      simpa [H, P1, P2, M] using hneg
    · refine ⟨1, by simp, ?_⟩
      simpa [H, P1, P2, W, M] using hleft
  · intro hcert
    have hrow2 := hcert 2 (by simp)
    obtain ⟨qj, hqj, hgap2⟩ := hrow2
    simp at hqj
    have hleft : (H + L + 2 : ℤ) < W % M := by
      rcases hqj with rfl | rfl
      · simpa [W] using hgap2
      · exfalso
        have : (2 * H + L + 2 : ℤ) < 0 := by
          simpa [H, P2, M] using hgap2
        omega
    have hWpos : 0 < W % M := by omega
    have hMnotDvdW : ¬M ∣ W := by
      intro hdvd
      rw [Int.emod_eq_zero_of_dvd hdvd] at hWpos
      omega
    have hrow1 := hcert 1 (by simp)
    obtain ⟨qj, hqj, hgap1⟩ := hrow1
    simp at hqj
    have hright : W % M < M - (2 * H + L + 2) := by
      rcases hqj with rfl | rfl
      · exfalso
        have : (H + L + 2 : ℤ) < 0 := by
          simpa [H, P1, M] using hgap1
        omega
      · have hgap1' : (2 * H + L + 2 : ℤ) < (P1 - P2) % M := by
          simpa [H, P1, P2, M] using hgap1
        rw [show P1 - P2 = -W by simp [W], Int.neg_emod,
          if_neg hMnotDvdW] at hgap1'
        rw [Int.natAbs_of_nonneg hMpos.le] at hgap1'
        omega
    constructor
    · simpa [diagonalFreshLossResidueCert, diagonalWindowResidue, H, P1, P2, W, M]
        using hleft
    · simpa [diagonalFreshLossResidueCert, diagonalWindowResidue, H, P1, P2, W, M]
        using hright

/-- A firing exact `[1, 2]` projection misses the complete reduced pincer
target.  Only the largest one-sided floor is needed; the `q = 1` floor follows
from it.

This is the proof-bearing composition seam between the cone/window owner and
the complement-free pincer owner. -/
theorem foreignDiagonalDefect_misses_fullTarget_of_projectionCert
    {t L : ℕ}
    (hfloor : (2 * periodLcm t + L + 2 : ℤ) < 2 ^ L)
    (hcert : diagonalFreshLossProjectionCert t L) :
    ¬ForeignDiagonalDefectHitsFullTarget t := by
  have hfloorAll : ∀ q ∈ ([1, 2] : List ℕ),
      (q * periodLcm t + L + 2 : ℤ) < 2 ^ L := by
    intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · omega
    · exact hfloor
  have hdiag :
      diagonalTailDifference t ∉ Set.range ((↑) : ℤ → ℝ) := by
    intro hint
    obtain ⟨qi, hqi, qj, hqj, hnon⟩ :=
      exists_nonintegral_pair_of_coneNonflatCert
        (H := periodLcm t) (L := L) (Q := [1, 2])
        (by simp) hfloorAll hcert
    simp at hqi hqj
    apply hnon
    rcases hqi with rfl | rfl <;> rcases hqj with rfl | rfl
    · exact ⟨0, by simp⟩
    · simpa [diagonalTailDifference, two_mul] using hint
    · obtain ⟨k, hk⟩ := hint
      refine ⟨-k, ?_⟩
      simp only [Int.cast_neg]
      simpa [diagonalTailDifference, two_mul] using congrArg Neg.neg hk
    · exact ⟨0, by simp⟩
  exact
    (diagonal_not_int_iff_foreignDiagonalDefect_misses_fullTarget t).mp hdiag

/-- The explicit asymmetric residue certificate alone is a complete finite
consumer: its right-hand inequality already implies the largest one-sided
floor required by the generic cone soundness theorem. -/
theorem foreignDiagonalDefect_misses_fullTarget_of_residueCert
    {t L : ℕ} (hcert : diagonalFreshLossResidueCert t L) :
    ¬ForeignDiagonalDefectHitsFullTarget t := by
  have hresNonneg : (0 : ℤ) ≤ diagonalWindowResidue t L := by
    apply Int.emod_nonneg
    positivity
  have hfloor : (2 * periodLcm t + L + 2 : ℤ) < 2 ^ L := by
    have hright := hcert.2
    omega
  exact foreignDiagonalDefect_misses_fullTarget_of_projectionCert hfloor
    ((diagonalFreshLossResidueCert_iff_projectionCert t L).mp hcert)

/-- The exact unresolved operational supply exposed by this bridge. -/
def DiagonalFreshLossProjectionSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ, diagonalFreshLossResidueCert t L

/-- Unbounded exact `[1, 2]` projection certificates feed the full-target
avoidance consumer and therefore prove irrationality of the totient series. -/
theorem irrational_totientSeries_of_diagonalFreshLossProjectionSupply
    (hsupply : DiagonalFreshLossProjectionSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totientSeries_of_full_target_avoidance_supply
  intro t₀
  obtain ⟨t, ht, L, hcert⟩ := hsupply t₀
  exact ⟨t, ht, foreignDiagonalDefect_misses_fullTarget_of_residueCert hcert⟩

/-! ## Sliding-suffix projection

The last `m` binary places of the depth-`(J + m)` diagonal window do not
depend on its first `J` offsets: the window numerator splits as
`P_{J+m}(M) = 2^m * P_J(M) + P_m(M + J)`, so the depth-`(J + m)` residue
reduces modulo `2^m` to the residue of a translated depth-`m` window.  A
central residue in those `m` suffix bits already excludes both edge bands of
the full window.  The cut remains operationally useful for finding finite
certificates, but the exact endpoint identities below show that it is not an
independent arithmetic averaging variable: it reads successive digits of one
dyadic orbit. -/

/-- Prefix–suffix split of the window numerator: the depth-`(J + m)` window
is `2^m` times its depth-`J` prefix plus the depth-`m` window at the
translated base `M + J`. -/
theorem windowNumerator_prefix_suffix (M J m : ℕ) :
    windowNumerator M (J + m)
      = 2 ^ m * windowNumerator M J + windowNumerator (M + J) m := by
  induction m with
  | zero => simp [windowNumerator]
  | succ m ih =>
    have h1 : J + (m + 1) = (J + m) + 1 := by omega
    have h2 : M + J + 1 + m = M + 1 + (J + m) := by omega
    rw [h1, windowNumerator_succ, ih, windowNumerator_succ, h2]
    ring

/-- The signed diagonal window increment `φ(2·H_t+s) − φ(H_t+s)` at offset
`s`. -/
def diagonalWindowIncrement (t s : ℕ) : ℤ :=
  (Nat.totient (2 * periodLcm t + s) : ℤ) -
    (Nat.totient (periodLcm t + s) : ℤ)

/-- The depth-`m` binary residue of the diagonal window suffix that starts
after the cut `J`: the last `m` bits of the depth-`(J + m)` diagonal window,
computed from the translated windows alone. -/
def diagonalSuffixResidue (t J m : ℕ) : ℤ :=
  ((windowNumerator (2 * periodLcm t + J) m : ℤ) -
    (windowNumerator (periodLcm t + J) m : ℤ)) % 2 ^ m

/-- The suffix residue is the dyadically weighted sum of the signed window
increments strictly after the cut — the operational shape used by the
sliding-suffix probe. -/
theorem diagonalSuffixResidue_eq_increment_sum (t J m : ℕ) :
    diagonalSuffixResidue t J m
      = (∑ r ∈ Finset.range m,
          diagonalWindowIncrement t (J + 1 + r) * 2 ^ (m - 1 - r)) % 2 ^ m := by
  unfold diagonalSuffixResidue diagonalWindowIncrement windowNumerator
  push_cast
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  have h1 : 2 * periodLcm t + J + 1 + r = 2 * periodLcm t + (J + 1 + r) := by
    omega
  have h2 : periodLcm t + J + 1 + r = periodLcm t + (J + 1 + r) := by omega
  rw [h1, h2]
  ring

/-- Low-bit projection: the depth-`(J + m)` diagonal residue reduces modulo
`2^m` to the sliding-suffix residue at cut `J`.  The `J`-bit prefix vanishes;
no estimate of it is required. -/
theorem diagonalWindowResidue_mod_suffix (t J m : ℕ) :
    diagonalWindowResidue t (J + m) % 2 ^ m = diagonalSuffixResidue t J m := by
  have hdvd : ((2 : ℤ) ^ m) ∣ 2 ^ (J + m) :=
    pow_dvd_pow 2 (Nat.le_add_left m J)
  have hsplit :
      ((windowNumerator (2 * periodLcm t) (J + m) : ℤ) -
          (windowNumerator (periodLcm t) (J + m) : ℤ))
        = ((windowNumerator (2 * periodLcm t + J) m : ℤ) -
              (windowNumerator (periodLcm t + J) m : ℤ))
          + 2 ^ m * ((windowNumerator (2 * periodLcm t) J : ℤ) -
              (windowNumerator (periodLcm t) J : ℤ)) := by
    rw [windowNumerator_prefix_suffix (2 * periodLcm t) J m,
      windowNumerator_prefix_suffix (periodLcm t) J m]
    push_cast
    ring
  unfold diagonalWindowResidue diagonalSuffixResidue
  rw [Int.emod_emod_of_dvd _ hdvd, hsplit, Int.add_mul_emod_self_left]

/-- **Sliding-suffix transference.**  A central residue in the last `m` bits
of the depth-`(J + m)` diagonal window already implies the full asymmetric
safe-interval certificate at depth `J + m`: both excluded edge bands of the
full window reduce into the corresponding edge bands of the suffix
modulus. -/
theorem diagonalFreshLossResidueCert_of_suffix_central {t J m : ℕ}
    (hleft : (periodLcm t + (J + m) + 2 : ℤ) < diagonalSuffixResidue t J m)
    (hright : diagonalSuffixResidue t J m
        < 2 ^ m - (2 * periodLcm t + (J + m) + 2)) :
    diagonalFreshLossResidueCert t (J + m) := by
  have hmod := diagonalWindowResidue_mod_suffix t J m
  have hM2pos : (0 : ℤ) < 2 ^ m := by positivity
  have hRlo : (0 : ℤ) ≤ diagonalWindowResidue t (J + m) := by
    unfold diagonalWindowResidue
    exact Int.emod_nonneg _ (by positivity)
  have hRhi : diagonalWindowResidue t (J + m) < 2 ^ (J + m) := by
    unfold diagonalWindowResidue
    exact Int.emod_lt_of_pos _ (by positivity)
  have hdvd : ((2 : ℤ) ^ m) ∣ 2 ^ (J + m) :=
    pow_dvd_pow 2 (Nat.le_add_left m J)
  unfold diagonalFreshLossResidueCert
  constructor
  · -- a left-band full residue would be its own suffix residue
    by_contra hnot
    have hRle : diagonalWindowResidue t (J + m) ≤ periodLcm t + (J + m) + 2 :=
      not_lt.mp hnot
    have hσlt : diagonalSuffixResidue t J m < 2 ^ m := by
      rw [← hmod]
      exact Int.emod_lt_of_pos _ hM2pos
    have hRltM2 : diagonalWindowResidue t (J + m) < 2 ^ m := by omega
    have hRfix : diagonalWindowResidue t (J + m) % 2 ^ m
        = diagonalWindowResidue t (J + m) := Int.emod_eq_of_lt hRlo hRltM2
    omega
  · -- a right-band full residue reappears in the suffix top band
    by_contra hnot
    have hRge : 2 ^ (J + m) - (2 * periodLcm t + (J + m) + 2)
        ≤ diagonalWindowResidue t (J + m) := not_lt.mp hnot
    have hσnn : (0 : ℤ) ≤ diagonalSuffixResidue t J m := by
      rw [← hmod]
      exact Int.emod_nonneg _ (by positivity)
    have hband : (2 * periodLcm t + (J + m) + 2 : ℤ) < 2 ^ m := by omega
    have hσeq : diagonalSuffixResidue t J m
        = 2 ^ m - (2 ^ (J + m) - diagonalWindowResidue t (J + m)) := by
      set k : ℤ := 2 ^ (J + m) - diagonalWindowResidue t (J + m) with hk
      have hkpos : (0 : ℤ) < k := by omega
      have hklt : k < 2 ^ m := by omega
      have h1 : diagonalWindowResidue t (J + m) = 2 ^ (J + m) - k := by omega
      have h2 : ((2 : ℤ) ^ (J + m) - k) % 2 ^ m = ((2 : ℤ) ^ m - k) % 2 ^ m := by
        obtain ⟨c, hc⟩ := hdvd
        rw [hc,
          show (2 ^ m * c - k : ℤ) = (2 ^ m - k) + 2 ^ m * (c - 1) by ring,
          Int.add_mul_emod_self_left]
      have h3 : ((2 : ℤ) ^ m - k) % 2 ^ m = 2 ^ m - k :=
        Int.emod_eq_of_lt (by omega) (by omega)
      rw [← hmod, h1, h2, h3]
    omega

/-! ## Adjacent-suffix separation

Two adjacent cuts already contain the finite geometry needed by the
sliding-suffix consumer.  Their difference is represented in the canonical
interval `[0, 2^m)`, so a residue outside the sum of the two edge widths
forces at least one suffix into its central interval.  This is an integer-only
replacement for averaging a larger family of complex phases. -/

/-- The canonical modular displacement from the suffix at cut `J` to the
suffix at cut `J + 1`. -/
def diagonalAdjacentSuffixResidue (t J m : ℕ) : ℤ :=
  (diagonalSuffixResidue t (J + 1) m -
    diagonalSuffixResidue t J m) % 2 ^ m

/-- Sliding the cut once doubles the retained suffix and appends the next
diagonal increment. -/
theorem diagonalSuffixResidue_succ_cut (t J m : ℕ) :
    diagonalSuffixResidue t (J + 1) m =
      (2 * diagonalSuffixResidue t J m +
        diagonalWindowIncrement t (J + m + 1)) % 2 ^ m := by
  let H := periodLcm t
  let P := 2 * H + J
  let Q := H + J
  let M : ℤ := 2 ^ m
  let A : ℤ := windowNumerator P m
  let B : ℤ := windowNumerator Q m
  let A' : ℤ := windowNumerator (P + 1) m
  let B' : ℤ := windowNumerator (Q + 1) m
  let E : ℤ := Nat.totient (P + m + 1)
  let F : ℤ := Nat.totient (Q + m + 1)
  let U : ℤ := Nat.totient (P + 1)
  let V : ℤ := Nat.totient (Q + 1)
  have hshift (N : ℕ) :
      windowNumerator (N + 1) m + 2 ^ m * Nat.totient (N + 1) =
        windowNumerator N (m + 1) := by
    rw [show m + 1 = 1 + m by omega, windowNumerator_prefix_suffix N 1 m]
    simp [windowNumerator, Nat.add_comm, Nat.add_left_comm]
  have hA : A' + M * U = 2 * A + E := by
    have hNat := (calc
      windowNumerator (P + 1) m + 2 ^ m * Nat.totient (P + 1) =
          windowNumerator P (m + 1) := hshift P
      _ = 2 * windowNumerator P m + Nat.totient (P + m + 1) := by
        rw [windowNumerator_succ]
        congr 2 <;> omega)
    simpa [A', M, U, A, E] using congrArg (fun n : ℕ => (n : ℤ)) hNat
  have hB : B' + M * V = 2 * B + F := by
    have hNat := (calc
      windowNumerator (Q + 1) m + 2 ^ m * Nat.totient (Q + 1) =
          windowNumerator Q (m + 1) := hshift Q
      _ = 2 * windowNumerator Q m + Nat.totient (Q + m + 1) := by
        rw [windowNumerator_succ]
        congr 2 <;> omega)
    simpa [B', M, V, B, F] using congrArg (fun n : ℕ => (n : ℤ)) hNat
  have hAmod : A' ≡ 2 * A + E [ZMOD M] := by
    rw [Int.modEq_iff_dvd]
    use U
    linarith
  have hBmod : B' ≡ 2 * B + F [ZMOD M] := by
    rw [Int.modEq_iff_dvd]
    use V
    linarith
  have hraw : A' - B' ≡ 2 * (A - B) + (E - F) [ZMOD M] := by
    convert hAmod.sub hBmod using 1 <;> ring
  have hreduced :
      2 * ((A - B) % M) + (E - F) ≡
        2 * (A - B) + (E - F) [ZMOD M] :=
    ((Int.mod_modEq (A - B) M).mul_left 2).add (Int.ModEq.refl _)
  have hEq : (A' - B') % M =
      (2 * ((A - B) % M) + (E - F)) % M :=
    Int.ModEq.eq (hraw.trans hreduced.symm)
  simpa [diagonalSuffixResidue, diagonalWindowIncrement, A', B', M, A, B,
    E, F, P, Q, H, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hEq

/-- The adjacent displacement is the terminal-corrected suffix residue. -/
theorem diagonalAdjacentSuffixResidue_eq_terminal_corrected (t J m : ℕ) :
    diagonalAdjacentSuffixResidue t J m =
      (diagonalSuffixResidue t J m +
        diagonalWindowIncrement t (J + m + 1)) % 2 ^ m := by
  have hfix : diagonalSuffixResidue t J m % 2 ^ m =
      diagonalSuffixResidue t J m := by
    unfold diagonalSuffixResidue
    rw [Int.emod_emod]
  unfold diagonalAdjacentSuffixResidue
  rw [diagonalSuffixResidue_succ_cut]
  apply Int.ModEq.eq
  have h := (Int.mod_modEq
    (2 * diagonalSuffixResidue t J m +
      diagonalWindowIncrement t (J + m + 1)) (2 ^ m)).sub
        (Int.ModEq.refl (diagonalSuffixResidue t J m))
  convert h using 1 <;> ring

/-- Sharp adjacent-gap geometry.  The constant is exactly the sum of the
right edge width at cut `J` and the left edge width at cut `J + 1` (equally,
the other cross-edge sum). -/
theorem diagonalFreshLossResidueCert_or_of_adjacent_suffix_gap_sharp
    {t J m : ℕ}
    (hgap :
      let B : ℤ := 3 * periodLcm t + 2 * (J + m) + 5
      B < diagonalAdjacentSuffixResidue t J m ∧
        diagonalAdjacentSuffixResidue t J m < 2 ^ m - B) :
    diagonalFreshLossResidueCert t (J + m) ∨
      diagonalFreshLossResidueCert t (J + 1 + m) := by
  let H : ℤ := periodLcm t
  let M : ℤ := 2 ^ m
  let x : ℤ := diagonalSuffixResidue t J m
  let y : ℤ := diagonalSuffixResidue t (J + 1) m
  let d : ℤ := diagonalAdjacentSuffixResidue t J m
  let A0 : ℤ := H + (J + m) + 2
  let C0 : ℤ := 2 * H + (J + m) + 2
  let A1 : ℤ := H + (J + 1 + m) + 2
  let C1 : ℤ := 2 * H + (J + 1 + m) + 2
  let B : ℤ := 3 * H + 2 * (J + m) + 5
  have hgap' : B < d ∧ d < M - B := by
    simpa [B, d, M, H] using hgap
  have hMpos : 0 < M := by simp [M]
  have hx0 : 0 ≤ x := by
    unfold x diagonalSuffixResidue
    exact Int.emod_nonneg _ hMpos.ne'
  have hxM : x < M := by
    unfold x diagonalSuffixResidue
    exact Int.emod_lt_of_pos _ hMpos
  have hy0 : 0 ≤ y := by
    unfold y diagonalSuffixResidue
    exact Int.emod_nonneg _ hMpos.ne'
  have hyM : y < M := by
    unfold y diagonalSuffixResidue
    exact Int.emod_lt_of_pos _ hMpos
  have hd : d = (y - x) % M := by rfl
  have hd_of_le (hxy : x ≤ y) : d = y - x := by
    rw [hd, Int.emod_eq_of_lt] <;> omega
  have hd_of_gt (hyx : y < x) : d = M + y - x := by
    rw [hd, show y - x = (M + y - x) - M by ring,
      Int.sub_emod_right, Int.emod_eq_of_lt] <;> omega
  by_cases hxCentral : A0 < x ∧ x < M - C0
  · left
    apply diagonalFreshLossResidueCert_of_suffix_central
    · simpa [A0, x, H] using hxCentral.1
    · simpa [C0, x, M, H] using hxCentral.2
  by_cases hyCentral : A1 < y ∧ y < M - C1
  · right
    apply diagonalFreshLossResidueCert_of_suffix_central
    · simpa [A1, y, H, Nat.add_assoc] using hyCentral.1
    · simpa [C1, y, M, H, Nat.add_assoc] using hyCentral.2
  exfalso
  have hxEdge : x ≤ A0 ∨ M - C0 ≤ x := by omega
  have hyEdge : y ≤ A1 ∨ M - C1 ≤ y := by omega
  rcases hxEdge with hxlo | hxhi <;> rcases hyEdge with hylo | hyhi
  · by_cases hxy : x ≤ y
    · rw [hd_of_le hxy] at hgap'
      omega
    · rw [hd_of_gt (by omega)] at hgap'
      omega
  · have hxy : x ≤ y := by omega
    rw [hd_of_le hxy] at hgap'
    omega
  · have hyx : y < x := by omega
    rw [hd_of_gt hyx] at hgap'
    omega
  · by_cases hxy : x ≤ y
    · rw [hd_of_le hxy] at hgap'
      omega
    · rw [hd_of_gt (by omega)] at hgap'
      omega

/-- If the modular displacement between adjacent suffixes exceeds the sum of
their two edge widths in both directions, then at least one suffix gives a
full-depth fresh-loss certificate. -/
theorem diagonalFreshLossResidueCert_or_of_adjacent_suffix_gap
    {t J m : ℕ}
    (hgap :
      let B : ℤ := 3 * periodLcm t + 2 * (J + m + 3)
      B < diagonalAdjacentSuffixResidue t J m ∧
        diagonalAdjacentSuffixResidue t J m < 2 ^ m - B) :
    diagonalFreshLossResidueCert t (J + m) ∨
      diagonalFreshLossResidueCert t (J + 1 + m) := by
  apply diagonalFreshLossResidueCert_or_of_adjacent_suffix_gap_sharp
  dsimp only at hgap ⊢
  omega

/-- A fixed `1/32` circular gap dominates the adjacent edge budget. -/
theorem diagonalFreshLossResidueCert_or_of_adjacent_dyadic_gap
    {t J m : ℕ}
    (hm : 5 ≤ m)
    (hwidth :
      32 * (3 * periodLcm t + 2 * (J + m + 3) : ℤ) < 2 ^ m)
    (hlo : 2 ^ (m - 5) ≤ diagonalAdjacentSuffixResidue t J m)
    (hhi : diagonalAdjacentSuffixResidue t J m
      ≤ 2 ^ m - 2 ^ (m - 5)) :
    diagonalFreshLossResidueCert t (J + m) ∨
      diagonalFreshLossResidueCert t (J + 1 + m) := by
  apply diagonalFreshLossResidueCert_or_of_adjacent_suffix_gap
  dsimp only
  have hpow : (2 : ℤ) ^ m = 32 * 2 ^ (m - 5) := by
    calc
      (2 : ℤ) ^ m = 2 ^ ((m - 5) + 5) := by rw [Nat.sub_add_cancel hm]
      _ = 32 * 2 ^ (m - 5) := by rw [pow_add]; norm_num; ring
  rw [hpow] at hwidth
  constructor <;> omega

/-- The canonical adjacent-suffix depth: ten guard bits beyond the binary
scale of the LCM height.  At this depth the analytic width budget is automatic;
the only remaining arithmetic input is centrality of the adjacent residue. -/
def canonicalAdjacentSuffixDepth (t : ℕ) : ℕ :=
  Nat.log2 (periodLcm t) + 10

/-- From `t ≥ 3`, the canonical depth has enough guard bits and its fixed
`1/32` central band dominates the whole adjacent-suffix edge budget. -/
theorem canonicalAdjacentSuffixDepth_width {t : ℕ} (ht : 3 ≤ t) :
    5 ≤ canonicalAdjacentSuffixDepth t ∧
      32 * (3 * periodLcm t +
        2 * (canonicalAdjacentSuffixDepth t + 3) : ℤ) <
        2 ^ canonicalAdjacentSuffixDepth t := by
  let H := periodLcm t
  let m := canonicalAdjacentSuffixDepth t
  have hH : 3 ≤ H := by
    exact ht.trans (le_periodLcm t)
  have hlog_le : Nat.log2 H ≤ H := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_le_self 2 H
  have hHpow : H < 2 ^ (Nat.log2 H + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two H
  have hm : m = Nat.log2 H + 10 := by
    simp [m, canonicalAdjacentSuffixDepth, H]
  have hbudget : 3 * H + 2 * (m + 3) < 16 * H := by
    omega
  have hscaled : 32 * (3 * H + 2 * (m + 3)) < 512 * H := by
    omega
  have hpow_eq : 512 * 2 ^ (Nat.log2 H + 1) = 2 ^ m := by
    rw [hm, show Nat.log2 H + 10 = (Nat.log2 H + 1) + 9 by omega,
      pow_add]
    norm_num
    ring
  have hwidthNat : 32 * (3 * H + 2 * (m + 3)) < 2 ^ m := by
    calc
      32 * (3 * H + 2 * (m + 3)) < 512 * H := hscaled
      _ < 512 * 2 ^ (Nat.log2 H + 1) :=
        (Nat.mul_lt_mul_left (a := 512) (by norm_num)).2 hHpow
      _ = 2 ^ m := hpow_eq
  constructor
  · change 5 ≤ m
    rw [hm]
    omega
  · change 32 * (3 * (H : ℤ) + 2 * (m + 3)) < 2 ^ m
    exact_mod_cast hwidthNat

/-- The unresolved arithmetic input after the adjacent finite reduction.  It
uses the fixed first pair of cuts, so sliding is no longer an artificial
waiting parameter. -/
def DiagonalAdjacentSuffixGapSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ m : ℕ,
    5 ≤ m ∧
      32 * (3 * periodLcm t + 2 * (m + 3) : ℤ) < 2 ^ m ∧
      2 ^ (m - 5) ≤ diagonalAdjacentSuffixResidue t 0 m ∧
      diagonalAdjacentSuffixResidue t 0 m ≤ 2 ^ m - 2 ^ (m - 5)

/-- The canonical producer throat after removing the automatic width budget.
Only centrality of one exact modular observable at arbitrarily large LCM
heights remains. -/
def CanonicalAdjacentSuffixCentralSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, max 3 t₀ ≤ t ∧
    2 ^ (canonicalAdjacentSuffixDepth t - 5) ≤
        diagonalAdjacentSuffixResidue t 0 (canonicalAdjacentSuffixDepth t) ∧
      diagonalAdjacentSuffixResidue t 0 (canonicalAdjacentSuffixDepth t) ≤
        2 ^ canonicalAdjacentSuffixDepth t -
          2 ^ (canonicalAdjacentSuffixDepth t - 5)

/-- The prime-power-jump-aligned producer throat.  Repeated LCM heights carry
no new arithmetic state, so it is enough to establish canonical centrality at
arbitrarily large strict jumps. -/
def CanonicalAdjacentSuffixJumpCentralSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, max 3 t₀ ≤ t ∧
    periodLcm t < periodLcm (t + 1) ∧
      2 ^ (canonicalAdjacentSuffixDepth t - 5) ≤
          diagonalAdjacentSuffixResidue t 0 (canonicalAdjacentSuffixDepth t) ∧
        diagonalAdjacentSuffixResidue t 0 (canonicalAdjacentSuffixDepth t) ≤
          2 ^ canonicalAdjacentSuffixDepth t -
            2 ^ (canonicalAdjacentSuffixDepth t - 5)

/-- Signed distance of the canonical adjacent residue from the nearer edge of
the fixed central band.  Nonnegative slack is exactly the two-sided
centrality condition; this scalar is the proof-oriented cocycle to study at
strict LCM jumps. -/
def canonicalAdjacentSuffixCentralSlack (t : ℕ) : ℤ :=
  let m := canonicalAdjacentSuffixDepth t
  let d := diagonalAdjacentSuffixResidue t 0 m
  min (d - 2 ^ (m - 5)) ((2 ^ m - 2 ^ (m - 5)) - d)

/-- The two central-band inequalities collapse to one exact integer sign. -/
theorem canonicalAdjacentSuffixCentral_iff_slack_nonneg (t : ℕ) :
    (2 ^ (canonicalAdjacentSuffixDepth t - 5) ≤
          diagonalAdjacentSuffixResidue t 0 (canonicalAdjacentSuffixDepth t) ∧
        diagonalAdjacentSuffixResidue t 0 (canonicalAdjacentSuffixDepth t) ≤
          2 ^ canonicalAdjacentSuffixDepth t -
            2 ^ (canonicalAdjacentSuffixDepth t - 5)) ↔
      0 ≤ canonicalAdjacentSuffixCentralSlack t := by
  simp [canonicalAdjacentSuffixCentralSlack]

/-- Scalar strict-jump producer.  This is equivalent to the original
two-sided producer but exposes a single integer observable for recurrence,
congruence, and exact-computation arguments. -/
def CanonicalAdjacentSuffixJumpSlackSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, max 3 t₀ ≤ t ∧
    periodLcm t < periodLcm (t + 1) ∧
      0 ≤ canonicalAdjacentSuffixCentralSlack t

theorem canonicalAdjacentSuffixJumpCentralSupply_iff_slackSupply :
    CanonicalAdjacentSuffixJumpCentralSupply ↔
      CanonicalAdjacentSuffixJumpSlackSupply := by
  constructor
  · intro hsupply t₀
    obtain ⟨t, ht, hjump, hlo, hhi⟩ := hsupply t₀
    exact ⟨t, ht, hjump,
      (canonicalAdjacentSuffixCentral_iff_slack_nonneg t).1 ⟨hlo, hhi⟩⟩
  · intro hsupply t₀
    obtain ⟨t, ht, hjump, hslack⟩ := hsupply t₀
    obtain ⟨hlo, hhi⟩ :=
      (canonicalAdjacentSuffixCentral_iff_slack_nonneg t).2 hslack
    exact ⟨t, ht, hjump, hlo, hhi⟩

/-- Restricting the producer to strict LCM jumps still supplies the canonical
centrality interface. -/
theorem canonicalAdjacentSuffixCentralSupply_of_jump
    (hsupply : CanonicalAdjacentSuffixJumpCentralSupply) :
    CanonicalAdjacentSuffixCentralSupply := by
  intro t₀
  obtain ⟨t, ht, _hjump, hlo, hhi⟩ := hsupply t₀
  exact ⟨t, ht, hlo, hhi⟩

/-- Canonical centrality supplies the existing adjacent-gap interface; the
guard-bit and width obligations are discharged uniformly. -/
theorem diagonalAdjacentSuffixGapSupply_of_canonical
    (hsupply : CanonicalAdjacentSuffixCentralSupply) :
    DiagonalAdjacentSuffixGapSupply := by
  intro t₀
  obtain ⟨t, ht, hlo, hhi⟩ := hsupply t₀
  have ht3 : 3 ≤ t := (le_max_left 3 t₀).trans ht
  have ht₀ : t₀ ≤ t := (le_max_right 3 t₀).trans ht
  obtain ⟨hm, hwidth⟩ := canonicalAdjacentSuffixDepth_width ht3
  exact ⟨t, ht₀, canonicalAdjacentSuffixDepth t, hm, hwidth, hlo, hhi⟩

/- The fixed adjacent-gap supply feeds the existing diagonal projection
supply. -/
set_option maxHeartbeats 800000 in
theorem diagonalFreshLossProjectionSupply_of_adjacentSuffixGapSupply
    (hsupply : DiagonalAdjacentSuffixGapSupply) :
    DiagonalFreshLossProjectionSupply := by
  intro t₀
  obtain ⟨t, ht, m, hm, hwidth, hlo, hhi⟩ := hsupply t₀
  rcases diagonalFreshLossResidueCert_or_of_adjacent_dyadic_gap
      hm (by simpa using hwidth) hlo hhi with hcert | hcert
  · exact ⟨t, ht, m, by simpa using hcert⟩
  · exact ⟨t, ht, 1 + m, by simpa using hcert⟩

/-- The adjacent integer-gap interface is already sufficient for the global
irrationality consumer. -/
theorem irrational_totientSeries_of_diagonalAdjacentSuffixGapSupply
    (hsupply : DiagonalAdjacentSuffixGapSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact irrational_totientSeries_of_diagonalFreshLossProjectionSupply
    (diagonalFreshLossProjectionSupply_of_adjacentSuffixGapSupply hsupply)

/-- Canonical adjacent-suffix centrality is sufficient for Erdős #249's
irrationality target through the already-landed adjacent-gap consumer. -/
theorem irrational_totientSeries_of_canonicalAdjacentSuffixCentralSupply
    (hsupply : CanonicalAdjacentSuffixCentralSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact irrational_totientSeries_of_diagonalAdjacentSuffixGapSupply
    (diagonalAdjacentSuffixGapSupply_of_canonical hsupply)

/-- Centrality at arbitrarily large strict LCM jumps already closes the
irrationality consumer. -/
theorem irrational_totientSeries_of_canonicalAdjacentSuffixJumpCentralSupply
    (hsupply : CanonicalAdjacentSuffixJumpCentralSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact irrational_totientSeries_of_canonicalAdjacentSuffixCentralSupply
    (canonicalAdjacentSuffixCentralSupply_of_jump hsupply)

/-- Nonnegative canonical slack at arbitrarily large strict LCM jumps closes
the same irrationality consumer. -/
theorem irrational_totientSeries_of_canonicalAdjacentSuffixJumpSlackSupply
    (hsupply : CanonicalAdjacentSuffixJumpSlackSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totientSeries_of_canonicalAdjacentSuffixJumpCentralSupply
  exact (canonicalAdjacentSuffixJumpCentralSupply_iff_slackSupply).2 hsupply

/-! ## Kernel-checked composition fixture -/

set_option maxRecDepth 100000 in
/-- At `t = 7`, depth `13` gives the exact diagonal projection and its floor.
This is a bridge fixture, not evidence for an unbounded supply. -/
theorem diagonalFreshLossProjectionCell_seven :
    (2 * periodLcm 7 + 13 + 2 : ℤ) < 2 ^ 13 ∧
      diagonalFreshLossProjectionCert 7 13 := by
  decide

set_option maxRecDepth 100000 in
theorem diagonalFreshLossResidueCell_seven :
    diagonalFreshLossResidueCert 7 13 := by
  decide

/-- The existing `t = 7` full-target miss can be recovered through the new
operational composition seam. -/
theorem foreignDiagonalDefect_misses_fullTarget_seven_via_projection :
    ¬ForeignDiagonalDefectHitsFullTarget 7 := by
  exact foreignDiagonalDefect_misses_fullTarget_of_residueCert
    diagonalFreshLossResidueCell_seven

set_option maxRecDepth 100000 in
/-- At `t = 7`, the cut `J = 1` with suffix length `m = 12` is centrally
placed: the last twelve bits alone recover the landed `(7, 13)` projection.
A bridge fixture, not evidence for an unbounded supply. -/
theorem diagonalSuffixCell_seven :
    (periodLcm 7 + (1 + 12) + 2 : ℤ) < diagonalSuffixResidue 7 1 12 ∧
      diagonalSuffixResidue 7 1 12
        < 2 ^ 12 - (2 * periodLcm 7 + (1 + 12) + 2) := by
  decide

/-- The `t = 7` full-target miss re-derived from suffix bits only, through
the sliding-suffix transference theorem. -/
theorem foreignDiagonalDefect_misses_fullTarget_seven_via_suffix :
    ¬ForeignDiagonalDefectHitsFullTarget 7 :=
  foreignDiagonalDefect_misses_fullTarget_of_residueCert
    (diagonalFreshLossResidueCert_of_suffix_central
      diagonalSuffixCell_seven.1 diagonalSuffixCell_seven.2)

#print axioms foreignDiagonalDefect_misses_fullTarget_of_projectionCert
#print axioms foreignDiagonalDefect_misses_fullTarget_of_residueCert
#print axioms diagonalFreshLossResidueCert_iff_projectionCert
#print axioms irrational_totientSeries_of_diagonalFreshLossProjectionSupply
#print axioms diagonalFreshLossProjectionCell_seven
#print axioms foreignDiagonalDefect_misses_fullTarget_seven_via_projection
#print axioms windowNumerator_prefix_suffix
#print axioms diagonalSuffixResidue_eq_increment_sum
#print axioms diagonalWindowResidue_mod_suffix
#print axioms diagonalFreshLossResidueCert_of_suffix_central
#print axioms diagonalAdjacentSuffixResidue_eq_terminal_corrected
#print axioms diagonalFreshLossResidueCert_or_of_adjacent_suffix_gap_sharp
#print axioms diagonalFreshLossResidueCert_or_of_adjacent_suffix_gap
#print axioms diagonalFreshLossResidueCert_or_of_adjacent_dyadic_gap
#print axioms diagonalFreshLossProjectionSupply_of_adjacentSuffixGapSupply
#print axioms irrational_totientSeries_of_diagonalAdjacentSuffixGapSupply
#print axioms irrational_totientSeries_of_canonicalAdjacentSuffixCentralSupply
#print axioms irrational_totientSeries_of_canonicalAdjacentSuffixJumpCentralSupply
#print axioms irrational_totientSeries_of_canonicalAdjacentSuffixJumpSlackSupply
#print axioms foreignDiagonalDefect_misses_fullTarget_seven_via_suffix

end Erdos249257.DiagonalFreshLossBridge
