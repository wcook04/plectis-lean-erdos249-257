import Erdos249257.GreedyAchievementSet
import Erdos249257.RationalSupportCarrySkeleton

/-!
# Dyadic prefix compression

This module owns the corrected transport from a reduced finite Mersenne prefix to the residual
support fraction and its wrap-ratio bound.
The reusable core is stated for an arbitrary finite positive fragment, not
only for an initial segment.

No novelty or priority claim is made for the statements in this file.  Nothing here proves or
refutes the universal Erdős #257 problem.
-/

namespace Erdos249257

open Set

/-! ## Pure reduced-denominator transport -/

/-- Integer residual numerator.  This is the algebraically natural core:
unlike the interface natural specialization below, it needs no ordering
hypothesis on the subtraction. -/
def dyadicResidualIntNumerator (p r : ℤ) (c D : ℕ) : ℤ :=
  p * (D : ℤ) - ((2 ^ c : ℕ) : ℤ) * r

/-- Integer displayed residual normalized by `Rat.divInt`. -/
def dyadicResidualIntRat (p r : ℤ) (c D : ℕ) : ℚ :=
  Rat.divInt (dyadicResidualIntNumerator p r c D) (((2 ^ c * D : ℕ) : ℤ))

/-- The decisive congruence argument in `ℤ`: adding the multiple `pD` to
`-2^c r` preserves coprimality with the odd modulus `D`. -/
theorem dyadicResidualIntNumerator_coprime_oddDenominator
    (p r : ℤ) (c D : ℕ) (hDodd : Odd D)
    (hrD : r.natAbs.Coprime D) :
    (dyadicResidualIntNumerator p r c D).natAbs.Coprime D := by
  have hpowDnat : Nat.Coprime (2 ^ c) D :=
    (Nat.coprime_two_left.mpr hDodd).pow_left c
  have hpowDint : IsCoprime (((2 ^ c : ℕ) : ℤ)) (D : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hpowDnat
  have hrDint : IsCoprime r (D : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hrD
  have hprod : IsCoprime (((2 ^ c : ℕ) : ℤ) * r) (D : ℤ) :=
    hpowDint.mul_left hrDint
  have hadd := hprod.neg_left.add_mul_left_left p
  rw [Int.isCoprime_iff_nat_coprime] at hadd
  simpa only [dyadicResidualIntNumerator, sub_eq_add_neg, mul_comm, add_comm]
    using hadd

/-- Integer form of the exact denominator sandwich.  It works for positive,
zero, or negative displayed residual numerators once coprimality with `D` is
known. -/
theorem dyadicResidualInt_denominator_sandwich
    (p r : ℤ) (c D : ℕ) (hDpos : 0 < D)
    (hND : (dyadicResidualIntNumerator p r c D).natAbs.Coprime D) :
    D ∣ (dyadicResidualIntRat p r c D).den ∧
      (dyadicResidualIntRat p r c D).den ∣ 2 ^ c * D := by
  let N : ℤ := dyadicResidualIntNumerator p r c D
  let P : ℕ := 2 ^ c
  let B : ℕ := P * D
  let g : ℕ := ((B : ℤ)).gcd N
  have hPpos : 0 < P := by simp [P]
  have hBpos : 0 < B := Nat.mul_pos hPpos hDpos
  have hBne : (B : ℤ) ≠ 0 := by exact_mod_cast hBpos.ne'
  have hden : (dyadicResidualIntRat p r c D).den = B / g := by
    rw [dyadicResidualIntRat, Rat.den_divInt, if_neg hBne]
    simp only [Int.natAbs_natCast]
    rfl
  have hgB : g ∣ B := Int.gcd_dvd_natAbs_left (B : ℤ) N
  have hgN : g ∣ N.natAbs := Int.gcd_dvd_natAbs_right (B : ℤ) N
  have hgD : g.Coprime D := hND.coprime_dvd_left (by simpa [N] using hgN)
  have hgP : g ∣ P := (hgD.dvd_mul_right).mp (by simpa [B] using hgB)
  change D ∣ (dyadicResidualIntRat p r c D).den ∧
    (dyadicResidualIntRat p r c D).den ∣ B
  rw [hden]
  constructor
  · refine ⟨P / g, ?_⟩
    simpa [B, Nat.mul_comm] using (Nat.mul_div_assoc D hgP)
  · exact Nat.div_dvd_of_dvd hgB

/-- Numerator left after subtracting a reduced finite prefix `r / D` from a
dyadic rational `p / 2^c`.  The transport theorem below assumes the
subtraction is nonnegative, so natural subtraction is exact. -/
def dyadicResidualNumerator (p r c D : ℕ) : ℕ :=
  p * D - 2 ^ c * r

/-- The displayed residual rational before its remaining power-of-two
cancellation is normalized by `Rat`. -/
def dyadicResidualRat (p r c D : ℕ) : ℚ :=
  (dyadicResidualNumerator p r c D : ℚ) / (2 ^ c * D : ℕ)

/-- Subtracting a reduced odd-denominator fraction from a dyadic fraction
cannot cancel any factor of the odd denominator. -/
theorem dyadicResidualNumerator_coprime_oddDenominator
    (p r c D : ℕ) (hDodd : Odd D) (hrD : r.Coprime D)
    (hle : 2 ^ c * r ≤ p * D) :
    (dyadicResidualNumerator p r c D).Coprime D := by
  let N := dyadicResidualNumerator p r c D
  have hpow : (2 ^ c).Coprime D :=
    (Nat.coprime_two_left.mpr hDodd).pow_left c
  have hscaled : (2 ^ c * r).Coprime D := hpow.mul_left hrD
  show Nat.gcd N D = 1
  have hgN : Nat.gcd N D ∣ N := Nat.gcd_dvd_left N D
  have hgD : Nat.gcd N D ∣ D := Nat.gcd_dvd_right N D
  have hgPD : Nat.gcd N D ∣ p * D := dvd_mul_of_dvd_right hgD p
  have hgscaled : Nat.gcd N D ∣ 2 ^ c * r := by
    have hsub := Nat.dvd_sub hgPD hgN
    simpa [N, dyadicResidualNumerator, Nat.sub_sub_self hle] using hsub
  exact Nat.eq_one_of_dvd_coprimes hscaled hgscaled hgD

/-- Exact denominator sandwich.  If `Q` is the normalized denominator of the
residual, then `D ∣ Q ∣ 2^c D`.  This is the division-free statement that the
odd part inherited from the finite prefix is exactly `D`. -/
theorem dyadicResidual_denominator_sandwich
    (p r c D : ℕ) (hDpos : 0 < D) (hDodd : Odd D)
    (hrD : r.Coprime D) (hle : 2 ^ c * r ≤ p * D) :
    D ∣ (dyadicResidualRat p r c D).den ∧
      (dyadicResidualRat p r c D).den ∣ 2 ^ c * D := by
  let N := dyadicResidualNumerator p r c D
  let P := 2 ^ c
  let T := P * D
  let g := Nat.gcd N T
  have hTpos : 0 < T := mul_pos (pow_pos (by omega) c) hDpos
  have hden : (dyadicResidualRat p r c D).den = T / g := by
    simpa [dyadicResidualRat, N, P, T, g] using
      den_natCast_div_natCast N T hTpos.ne'
  have hND : N.Coprime D := by
    simpa [N] using
      dyadicResidualNumerator_coprime_oddDenominator p r c D hDodd hrD hle
  have hgN : g ∣ N := by
    exact Nat.gcd_dvd_left N T
  have hgT : g ∣ T := by
    exact Nat.gcd_dvd_right N T
  have hgD : g.Coprime D := Nat.Coprime.coprime_dvd_left hgN hND
  have hgP : g ∣ P := by
    exact (hgD.dvd_mul_right).mp (by simpa [T] using hgT)
  rw [hden]
  constructor
  · refine ⟨P / g, ?_⟩
    rw [show T = D * P by simp [T, mul_comm], Nat.mul_div_assoc D hgP]
  · exact ⟨g, by simpa [T] using (Nat.div_mul_cancel hgT).symm⟩

/-! ## Existing finite-denominator and support-series bridges -/

/-- At base two, the actual reduced denominator of every positive finite
Erdős fragment is odd. -/
theorem finiteErdosSum_den_odd
    (F : Finset ℕ) (h0 : 0 ∉ F) :
    Odd (finiteErdosSum F 2).den := by
  exact Nat.coprime_two_left.mp
    (coprime_base_den_finiteErdosSum F 2 h0 (by omega))

/-- The existing finite noncollapse theorem rewritten in the T9 order API:
the order of two modulo the actual reduced denominator is `lcm F`. -/
theorem oddDoublingOrder_finiteErdosSum_den_eq_lcm
    (F : Finset ℕ) (hF : F.Nonempty) (h0 : 0 ∉ F) :
    oddDoublingOrder (finiteErdosSum F 2).den
        (finiteErdosSum_den_odd F h0) = F.lcm id := by
  simpa [oddDoublingOrder] using
    finite_period_noncollapse_rat_den F 2 hF h0 (by omega)

/-- A finite support series is the real cast of the audited rational
`finiteErdosSum`. -/
theorem erdosSupportSeries_finset_eq_cast_finiteErdosSum (F : Finset ℕ) :
    erdosSupportSeries 2 (↑F : Set ℕ) = ((finiteErdosSum F 2 : ℚ) : ℝ) := by
  calc
    erdosSupportSeries 2 (↑F : Set ℕ)
        = ∑ a ∈ F, mersenneWeight a := by
            unfold erdosSupportSeries
            rw [tsum_eq_sum (s := F)]
            · exact Finset.sum_congr rfl fun a ha => by
                simp [mersenneWeight, ha]
            · intro a ha
              simp [ha]
    _ = ((∑ a ∈ F, mersenneWeightRat a : ℚ) : ℝ) := by
          push_cast
          simp only [cast_mersenneWeightRat]
    _ = ((finiteErdosSum F 2 : ℚ) : ℝ) := by
          congr 1

/-- Removing a finite fragment from a support subtracts exactly its audited
finite rational sum.  No ordering or prefix hypothesis is used. -/
theorem erdosSupportSeries_diff_finset
    (A : Set ℕ) (F : Finset ℕ) (hFA : (↑F : Set ℕ) ⊆ A) :
    erdosSupportSeries 2 (A \ (↑F : Set ℕ)) =
      erdosSupportSeries 2 A - ((finiteErdosSum F 2 : ℚ) : ℝ) := by
  let fA : ℕ → ℝ := fun a =>
    Set.indicator A (fun a => (1 : ℝ) / ((2 : ℝ) ^ a - 1)) a
  let fF : ℕ → ℝ := fun a =>
    Set.indicator (↑F : Set ℕ) (fun a => (1 : ℝ) / ((2 : ℝ) ^ a - 1)) a
  have hsA : Summable fA := by
    simpa [fA] using summable_erdosSupport_indicator 2 A (by omega)
  have hsF : Summable fF := by
    simpa [fF] using
      summable_erdosSupport_indicator 2 (↑F : Set ℕ) (by omega)
  calc
    erdosSupportSeries 2 (A \ (↑F : Set ℕ))
        = ∑' a : ℕ, (fA a - fF a) := by
            unfold erdosSupportSeries
            apply tsum_congr
            intro a
            by_cases haF : a ∈ F
            · have haA : a ∈ A := hFA (by simpa using haF)
              simp [fA, fF, haF, haA]
            · by_cases haA : a ∈ A
              · simp [fA, fF, haF, haA]
              · simp [fA, fF, haF, haA]
    _ = (∑' a : ℕ, fA a) - ∑' a : ℕ, fF a := hsA.tsum_sub hsF
    _ = erdosSupportSeries 2 A - erdosSupportSeries 2 (↑F : Set ℕ) := by
          rfl
    _ = erdosSupportSeries 2 A - ((finiteErdosSum F 2 : ℚ) : ℝ) := by
          rw [erdosSupportSeries_finset_eq_cast_finiteErdosSum]

/-- Algebraic composition of the support-difference bridge with displayed
dyadic and reduced-prefix fractions. -/
theorem finiteFragment_residual_value
    (A : Set ℕ) (F : Finset ℕ) (p r c D : ℕ)
    (hFA : (↑F : Set ℕ) ⊆ A)
    (hwhole : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ))
    (hprefix : finiteErdosSum F 2 = (r : ℚ) / (D : ℚ))
    (hDpos : 0 < D) (hle : 2 ^ c * r ≤ p * D) :
    erdosSupportSeries 2 (A \ (↑F : Set ℕ)) =
      (dyadicResidualNumerator p r c D : ℝ) /
        ((2 ^ c * D : ℕ) : ℝ) := by
  have hprefixR : ((finiteErdosSum F 2 : ℚ) : ℝ) =
      (r : ℝ) / (D : ℝ) := by
    simpa using congrArg (fun q : ℚ => (q : ℝ)) hprefix
  rw [erdosSupportSeries_diff_finset A F hFA, hwhole, hprefixR]
  unfold dyadicResidualNumerator
  rw [Nat.cast_sub hle]
  push_cast
  field_simp

/-! ## Certificate transport into the T9 wrap-ratio theorem -/

/-- The proof-bearing T12 product.  It records the no-odd-cancellation
transport, exact residual value, exact finite period, and the T9 analytic
conclusion in one reusable certificate. -/
structure DyadicPrefixCompressionCertificate
    (A : Set ℕ) (F : Finset ℕ) (p r c D : ℕ) : Prop where
  oddDenominator : Odd D
  numeratorPositive : 0 < dyadicResidualNumerator p r c D
  numeratorCoprime : (dyadicResidualNumerator p r c D).Coprime D
  denominatorSandwich :
    D ∣ (dyadicResidualRat p r c D).den ∧
      (dyadicResidualRat p r c D).den ∣ 2 ^ c * D
  residualValue :
    erdosSupportSeries 2 (A \ (↑F : Set ℕ)) =
      (dyadicResidualNumerator p r c D : ℝ) /
        ((2 ^ c * D : ℕ) : ℝ)
  orderEq : oddDoublingOrder D oddDenominator = F.lcm id
  wrapBound :
    ReciprocalMassDivergesOrAtLeast (A \ (↑F : Set ℕ))
      ((doublingWrapCount (dyadicResidualNumerator p r c D) D (F.lcm id) : ℝ) /
        ((F.lcm id : ℕ) : ℝ))

/-- Generic finite-fragment T12 transport.  The prefix certificate names the
actual reduced denominator and numerator; the existing noncollapse theorem
supplies the exact order, while T9 supplies the analytic disjunction. -/
theorem finiteFragment_dyadicPrefixCompression
    (A : Set ℕ) (F : Finset ℕ) (p r c D : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hFA : (↑F : Set ℕ) ⊆ A)
    (hwhole : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ))
    (hprefix : finiteErdosSum F 2 = (r : ℚ) / (D : ℚ))
    (hDactual : D = (finiteErdosSum F 2).den)
    (hrD : r.Coprime D) (hDgtOne : 1 < D)
    (hle : 2 ^ c * r ≤ p * D)
    (hNpos : 0 < dyadicResidualNumerator p r c D)
    (hResidual : ∃ a : ℕ, 0 < a ∧ a ∈ A \ (↑F : Set ℕ)) :
    DyadicPrefixCompressionCertificate A F p r c D := by
  have hDodd : Odd D := by
    rw [hDactual]
    exact finiteErdosSum_den_odd F h0
  have hNcop : (dyadicResidualNumerator p r c D).Coprime D :=
    dyadicResidualNumerator_coprime_oddDenominator p r c D hDodd hrD hle
  have hsandwich := dyadicResidual_denominator_sandwich
    p r c D (by omega) hDodd hrD hle
  have hresidualValue := finiteFragment_residual_value
    A F p r c D hFA hwhole hprefix (by omega) hle
  have horder : oddDoublingOrder D hDodd = F.lcm id := by
    subst D
    exact oddDoublingOrder_finiteErdosSum_den_eq_lcm F hF h0
  have hwrap :=
    support_fraction_oddOrder_wrapRatio_reciprocalMassDivergesOrAtLeast
      (A \ (↑F : Set ℕ)) hResidual
      ((dyadicResidualNumerator p r c D : ℕ) : ℤ) c hDgtOne hDodd
      (by simpa using hresidualValue)
  refine
    { oddDenominator := hDodd
      numeratorPositive := hNpos
      numeratorCoprime := hNcop
      denominatorSandwich := hsandwich
      residualValue := hresidualValue
      orderEq := horder
      wrapBound := ?_ }
  simpa [horder] using hwrap

/-! ## Finite fixtures -/

/-- Exact arithmetic, reduced odd denominator, order and wrap count for the
`{2,3}` finite fragment. -/
theorem two_three_dyadicPrefix_fixture :
    finiteErdosSum ({2, 3} : Finset ℕ) 2 = (10 : ℚ) / 21 ∧
      (finiteErdosSum ({2, 3} : Finset ℕ) 2).den = 21 ∧
      oddDoublingOrder 21 (by decide : Odd 21) = 6 ∧
      doublingWrapCount 1 21 6 = 2 ∧
      dyadicResidualRat 1 10 1 21 = (1 : ℚ) / 42 := by
  have horder := oddDoublingOrder_finiteErdosSum_den_eq_lcm
    ({2, 3} : Finset ℕ) (by simp) (by simp)
  norm_num [finiteErdosSum] at horder
  refine ⟨by norm_num [finiteErdosSum], by norm_num [finiteErdosSum], ?_, ?_, ?_⟩
  · simpa using horder
  · norm_num [doublingWrapCount, doublingWrapDigit, doublingResidue,
      Finset.sum_range_succ]
  · norm_num [dyadicResidualRat, dyadicResidualNumerator]

/-- Exact arithmetic, reduced odd denominator, order and wrap count for the
five-term finite fragment. -/
theorem five_term_dyadicPrefix_fixture :
    finiteErdosSum ({2, 3, 6, 7, 14} : Finset ℕ) 2 =
        (172021 : ℚ) / 344043 ∧
      (finiteErdosSum ({2, 3, 6, 7, 14} : Finset ℕ) 2).den = 344043 ∧
      oddDoublingOrder 344043 (by decide : Odd 344043) = 42 ∧
      doublingWrapCount 1 344043 42 = 13 ∧
      dyadicResidualRat 1 172021 1 344043 = (1 : ℚ) / 688086 := by
  have horder := oddDoublingOrder_finiteErdosSum_den_eq_lcm
    ({2, 3, 6, 7, 14} : Finset ℕ) (by simp) (by simp)
  norm_num [finiteErdosSum] at horder
  refine ⟨by norm_num [finiteErdosSum], by norm_num [finiteErdosSum], ?_, ?_, ?_⟩
  · simpa using horder
  · norm_num [doublingWrapCount, doublingWrapDigit, doublingResidue,
      Finset.sum_range_succ]
  · norm_num [dyadicResidualRat, dyadicResidualNumerator]

/-- Conditional wrapper for `F={2,3}`.  Any support of dyadic value
`1/2` containing this fragment and a positive residual witness inherits the
exact lower bound `1/3` (or divergent reciprocal mass). -/
theorem two_three_residual_reciprocalMassDivergesOrAtLeast
    (A : Set ℕ) (hFA : (↑({2, 3} : Finset ℕ) : Set ℕ) ⊆ A)
    (hwhole : erdosSupportSeries 2 A = (1 : ℝ) / 2)
    (hResidual : ∃ a : ℕ, 0 < a ∧ a ∈ A \ (↑({2, 3} : Finset ℕ) : Set ℕ)) :
    ReciprocalMassDivergesOrAtLeast
      (A \ (↑({2, 3} : Finset ℕ) : Set ℕ)) (1 / 3 : ℝ) := by
  have hcert := finiteFragment_dyadicPrefixCompression
    A ({2, 3} : Finset ℕ) 1 10 1 21
    (by simp) (by simp) hFA
    (by simpa using hwhole)
    (by norm_num [finiteErdosSum])
    (by norm_num [finiteErdosSum])
    (by decide) (by omega) (by norm_num) (by norm_num [dyadicResidualNumerator])
    hResidual
  have hbound := hcert.wrapBound
  have hwrap : doublingWrapCount 1 21 6 = 2 :=
    two_three_dyadicPrefix_fixture.2.2.2.1
  norm_num [dyadicResidualNumerator] at hbound
  rw [show GCDMonoid.lcm 2 3 = 6 by decide] at hbound
  rw [hwrap] at hbound
  norm_num at hbound
  simpa using hbound

/-- Conditional wrapper for `F={2,3,6,7,14}` with the exact
`13/42` residual wrap ratio. -/
theorem five_term_residual_reciprocalMassDivergesOrAtLeast
    (A : Set ℕ)
    (hFA : (↑({2, 3, 6, 7, 14} : Finset ℕ) : Set ℕ) ⊆ A)
    (hwhole : erdosSupportSeries 2 A = (1 : ℝ) / 2)
    (hResidual : ∃ a : ℕ, 0 < a ∧
      a ∈ A \ (↑({2, 3, 6, 7, 14} : Finset ℕ) : Set ℕ)) :
    ReciprocalMassDivergesOrAtLeast
      (A \ (↑({2, 3, 6, 7, 14} : Finset ℕ) : Set ℕ)) (13 / 42 : ℝ) := by
  have hcert := finiteFragment_dyadicPrefixCompression
    A ({2, 3, 6, 7, 14} : Finset ℕ) 1 172021 1 344043
    (by simp) (by simp) hFA
    (by simpa using hwhole)
    (by norm_num [finiteErdosSum])
    (by norm_num [finiteErdosSum])
    (by decide) (by omega) (by norm_num) (by norm_num [dyadicResidualNumerator])
    hResidual
  have hbound := hcert.wrapBound
  have hwrap : doublingWrapCount 1 344043 42 = 13 :=
    five_term_dyadicPrefix_fixture.2.2.2.1
  norm_num [dyadicResidualNumerator] at hbound
  rw [show GCDMonoid.lcm 2
      (GCDMonoid.lcm 3
        (GCDMonoid.lcm 6 (GCDMonoid.lcm 7 14))) = 42 by decide] at hbound
  rw [hwrap] at hbound
  norm_num at hbound
  simpa using hbound

end Erdos249257
