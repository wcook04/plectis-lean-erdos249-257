import Erdos249257.SuffixCylinderStage51
import Erdos249257.SuffixCylinderGlobalProducer
import Erdos249257.TerminalOnlyCofinal

/-!
# Suffix-cylinder stages feed the terminal-only half consumer

The suffix-cylinder construction carries substantially more information than
the terminal-only compactness-free consumer needs.  This module records the
lossy projection explicitly: one selected representative already gives a
normalized terminal strip witness.  At a feedback row the same conclusion
survives both outputs of the total feedback theorem, because a localized
one-hole seam always realizes at least one of carries `3` and `4`.
-/

namespace Erdos249257.SuffixCylinderTerminalOnlyBridge

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.SuffixCylinderThreshold
open Erdos249257.SuffixCylinderGlobalProducer
open Erdos249257.SuffixCylinderStage51

/-- Every all-prefix reachable terminal state is, after forgetting its
history, a terminal-only strip witness. -/
theorem halfTerminalOnlyStripWitness_of_halfTerminalReachable
    {N k : ℕ} (hreach : HalfTerminalReachable N k) :
    HalfTerminalOnlyStripWitness N := by
  obtain ⟨a, ha, _hterminal⟩ := hreach
  refine ⟨a, ha.1, ha.2.1, ?_⟩
  by_cases hN : N = 0
  · subst N
    simp [integerHalfCarry_zero, halfStripBound]
  · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    have hstrip := ha.2.2 N hNpos le_rfl
    have hnonnegZ :
        (0 : ℤ) ≤ integerHalfCarry (wordSupport a) (N - 1) := by
      omega
    have hnonnegR :
        (0 : ℝ) ≤ (integerHalfCarry (wordSupport a) (N - 1) : ℝ) := by
      exact_mod_cast hnonnegZ
    rw [abs_of_nonneg hnonnegR]
    exact_mod_cast hstrip.2

/-- A nonempty selected window contains a terminal-only witness: choose its
representative with terminal carry `1`. -/
theorem SelectedHalfWindow.halfTerminalOnlyStripWitness
    {N R : ℕ} (W : SelectedHalfWindow N R) (hR : 1 ≤ R) :
    HalfTerminalOnlyStripWitness N := by
  apply halfTerminalOnlyStripWitness_of_halfTerminalReachable
  exact ⟨W.word 1 (by omega) hR,
    W.admissible 1 (by omega) hR,
    W.terminal 1 (by omega) hR⟩

/-- Forgetting the endpoint and cylinder data of a full cylinder stage leaves
a terminal-only witness at the same depth. -/
theorem CylinderStage.halfTerminalOnlyStripWitness
    {K N : ℕ} (S : CylinderStage K N) :
    HalfTerminalOnlyStripWitness N := by
  apply
    Erdos249257.SuffixCylinderTerminalOnlyBridge.SelectedHalfWindow.halfTerminalOnlyStripWitness
      S.window
  unfold halfStripBound
  omega

/-- A realized localized seam still gives a terminal-only witness.  The seam
can delete at most one carry, so one of `3` and `4` survives. -/
theorem halfTerminalOnlyStripWitness_of_protectedEvenSeamRealizedAt
    {N : ℕ} {delta c : ℤ}
    (hrealize : ProtectedEvenSeamRealizedAt N delta c) :
    HalfTerminalOnlyStripWitness N := by
  let k : ℕ := if 2 * delta - c = 3 then 4 else 3
  have hk3 : 3 ≤ k := by
    simp only [k]
    split_ifs <;> omega
  have hk27 : k ≤ 27 := by
    simp only [k]
    split_ifs <;> omega
  have hnotHole : (k : ℤ) ≠ 2 * delta - c := by
    simp only [k]
    split_ifs <;> omega
  have hseam : EvenSeamReachable delta c k :=
    (evenSeamReachable_iff delta c k).2 hnotHole
  exact halfTerminalOnlyStripWitness_of_halfTerminalReachable
    (hrealize k hk3 hk27 hseam)

/-- **Feedback-row terminal consumer.**  At an exact half-divisor horizon,
the total suffix-cylinder feedback theorem produces a terminal-only witness
at the next row in both cases: either the full cylinder advances, or its
localized one-hole seam supplies a surviving terminal state. -/
theorem CylinderStage.halfTerminalOnlyStripWitness_after_feedback
    {K N : ℕ} (S : CylinderStage K N)
    (hN : 1 ≤ N) (hK1N : K + 1 ≤ N)
    (hrow : N + 1 = 2 * (K + 1))
    (h27 : 27 ≤ halfStripBound (N + 1)) :
    HalfTerminalOnlyStripWitness (N + 1) := by
  rcases
      Erdos249257.SuffixCylinderGlobalProducer.CylinderStage.feedbackStep_or_protectedSeam
        S hN hK1N hrow h27 with
    hstage | hseam
  · rcases hstage with ⟨S'⟩
    exact
      Erdos249257.SuffixCylinderTerminalOnlyBridge.CylinderStage.halfTerminalOnlyStripWitness
        S'
  · obtain ⟨delta, c, hrealize⟩ := hseam
    exact halfTerminalOnlyStripWitness_of_protectedEvenSeamRealizedAt hrealize

/-- The certified depth-51 cylinder already yields a concrete normalized
terminal strip witness. -/
theorem fullCylinderStage51_halfTerminalOnlyStripWitness :
    HalfTerminalOnlyStripWitness 51 :=
  Erdos249257.SuffixCylinderTerminalOnlyBridge.CylinderStage.halfTerminalOnlyStripWitness
    fullCylinderStage51

/-- The explicitly promoted second-feedback successor gives the next
concrete terminal strip witness as well. -/
theorem fullCylinderStage52_halfTerminalOnlyStripWitness :
    HalfTerminalOnlyStripWitness 52 :=
  Erdos249257.SuffixCylinderTerminalOnlyBridge.CylinderStage.halfTerminalOnlyStripWitness
    fullCylinderStage52

/-- Cofinal full-cylinder stages imply the strictly weaker terminal-only
cofinal producer expected by the closed achievement-set consumer. -/
theorem cofinalTerminalOnlyStrip_of_cofinalCylinderStages
    (hstages : ∀ N : ℕ, ∃ M K : ℕ,
      max N 1 ≤ M ∧ Nonempty (CylinderStage K M)) :
    HalfCarryCofinalTerminalOnlyStrip := by
  intro N
  obtain ⟨M, K, hNM, hstage⟩ := hstages N
  rcases hstage with ⟨S⟩
  exact ⟨M, hNM,
    Erdos249257.SuffixCylinderTerminalOnlyBridge.CylinderStage.halfTerminalOnlyStripWitness
      S⟩

/-- Direct end-to-end consumer: cofinal suffix-cylinder stages produce an
infinite support whose Mersenne support series is the rational value `1/2`. -/
theorem exists_infinite_support_half_of_cofinalCylinderStages
    (hstages : ∀ N : ℕ, ∃ M K : ℕ,
      max N 1 ≤ M ∧ Nonempty (CylinderStage K M)) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 :=
  exists_infinite_support_half_of_cofinalTerminalOnlyStrip
    (cofinalTerminalOnlyStrip_of_cofinalCylinderStages hstages)

#print axioms halfTerminalOnlyStripWitness_of_halfTerminalReachable
#print axioms SelectedHalfWindow.halfTerminalOnlyStripWitness
#print axioms CylinderStage.halfTerminalOnlyStripWitness
#print axioms halfTerminalOnlyStripWitness_of_protectedEvenSeamRealizedAt
#print axioms CylinderStage.halfTerminalOnlyStripWitness_after_feedback
#print axioms fullCylinderStage51_halfTerminalOnlyStripWitness
#print axioms fullCylinderStage52_halfTerminalOnlyStripWitness
#print axioms cofinalTerminalOnlyStrip_of_cofinalCylinderStages
#print axioms exists_infinite_support_half_of_cofinalCylinderStages

end Erdos249257.SuffixCylinderTerminalOnlyBridge
