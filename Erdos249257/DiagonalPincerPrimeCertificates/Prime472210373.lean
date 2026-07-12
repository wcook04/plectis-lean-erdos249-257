import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_472210373 : Nat.Prime 472210373 := by
  apply lucas_primality 472210373 (2 : ZMod 472210373)
  ·
      have fermat_0 : (2 : ZMod 472210373) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 472210373) ^ 3 = 8 := by
        calc
          (2 : ZMod 472210373) ^ 3 = (2 : ZMod 472210373) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 1 * (2 : ZMod 472210373) ^ 1) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 472210373) ^ 7 = 128 := by
        calc
          (2 : ZMod 472210373) ^ 7 = (2 : ZMod 472210373) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 3 * (2 : ZMod 472210373) ^ 3) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 472210373) ^ 14 = 16384 := by
        calc
          (2 : ZMod 472210373) ^ 14 = (2 : ZMod 472210373) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 7 * (2 : ZMod 472210373) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 472210373) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 472210373) ^ 28 = (2 : ZMod 472210373) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 14 * (2 : ZMod 472210373) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 472210373) ^ 56 = 47467823 := by
        calc
          (2 : ZMod 472210373) ^ 56 = (2 : ZMod 472210373) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 28 * (2 : ZMod 472210373) ^ 28 := by rw [pow_add]
          _ = 47467823 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 472210373) ^ 112 = 398866632 := by
        calc
          (2 : ZMod 472210373) ^ 112 = (2 : ZMod 472210373) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 56 * (2 : ZMod 472210373) ^ 56 := by rw [pow_add]
          _ = 398866632 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 472210373) ^ 225 = 349032051 := by
        calc
          (2 : ZMod 472210373) ^ 225 = (2 : ZMod 472210373) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 112 * (2 : ZMod 472210373) ^ 112) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 349032051 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 472210373) ^ 450 = 106919861 := by
        calc
          (2 : ZMod 472210373) ^ 450 = (2 : ZMod 472210373) ^ (225 + 225) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 225 * (2 : ZMod 472210373) ^ 225 := by rw [pow_add]
          _ = 106919861 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 472210373) ^ 900 = 64760936 := by
        calc
          (2 : ZMod 472210373) ^ 900 = (2 : ZMod 472210373) ^ (450 + 450) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 450 * (2 : ZMod 472210373) ^ 450 := by rw [pow_add]
          _ = 64760936 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 472210373) ^ 1801 = 281936425 := by
        calc
          (2 : ZMod 472210373) ^ 1801 = (2 : ZMod 472210373) ^ (900 + 900 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 900 * (2 : ZMod 472210373) ^ 900) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 281936425 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 472210373) ^ 3602 = 68060007 := by
        calc
          (2 : ZMod 472210373) ^ 3602 = (2 : ZMod 472210373) ^ (1801 + 1801) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 1801 * (2 : ZMod 472210373) ^ 1801 := by rw [pow_add]
          _ = 68060007 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 472210373) ^ 7205 = 270856615 := by
        calc
          (2 : ZMod 472210373) ^ 7205 = (2 : ZMod 472210373) ^ (3602 + 3602 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 3602 * (2 : ZMod 472210373) ^ 3602) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 270856615 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 472210373) ^ 14410 = 163153574 := by
        calc
          (2 : ZMod 472210373) ^ 14410 = (2 : ZMod 472210373) ^ (7205 + 7205) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 7205 * (2 : ZMod 472210373) ^ 7205 := by rw [pow_add]
          _ = 163153574 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 472210373) ^ 28821 = 384415198 := by
        calc
          (2 : ZMod 472210373) ^ 28821 = (2 : ZMod 472210373) ^ (14410 + 14410 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 14410 * (2 : ZMod 472210373) ^ 14410) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 384415198 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 472210373) ^ 57642 = 365150684 := by
        calc
          (2 : ZMod 472210373) ^ 57642 = (2 : ZMod 472210373) ^ (28821 + 28821) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 28821 * (2 : ZMod 472210373) ^ 28821 := by rw [pow_add]
          _ = 365150684 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 472210373) ^ 115285 = 407248620 := by
        calc
          (2 : ZMod 472210373) ^ 115285 = (2 : ZMod 472210373) ^ (57642 + 57642 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 57642 * (2 : ZMod 472210373) ^ 57642) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 407248620 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 472210373) ^ 230571 = 465115669 := by
        calc
          (2 : ZMod 472210373) ^ 230571 = (2 : ZMod 472210373) ^ (115285 + 115285 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 115285 * (2 : ZMod 472210373) ^ 115285) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 465115669 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 472210373) ^ 461142 = 32348054 := by
        calc
          (2 : ZMod 472210373) ^ 461142 = (2 : ZMod 472210373) ^ (230571 + 230571) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 230571 * (2 : ZMod 472210373) ^ 230571 := by rw [pow_add]
          _ = 32348054 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 472210373) ^ 922285 = 265392148 := by
        calc
          (2 : ZMod 472210373) ^ 922285 = (2 : ZMod 472210373) ^ (461142 + 461142 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 461142 * (2 : ZMod 472210373) ^ 461142) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 265392148 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 472210373) ^ 1844571 = 9930529 := by
        calc
          (2 : ZMod 472210373) ^ 1844571 = (2 : ZMod 472210373) ^ (922285 + 922285 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 922285 * (2 : ZMod 472210373) ^ 922285) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 9930529 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 472210373) ^ 3689143 = 344896907 := by
        calc
          (2 : ZMod 472210373) ^ 3689143 = (2 : ZMod 472210373) ^ (1844571 + 1844571 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 1844571 * (2 : ZMod 472210373) ^ 1844571) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 344896907 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 472210373) ^ 7378287 = 120532263 := by
        calc
          (2 : ZMod 472210373) ^ 7378287 = (2 : ZMod 472210373) ^ (3689143 + 3689143 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 3689143 * (2 : ZMod 472210373) ^ 3689143) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 120532263 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 472210373) ^ 14756574 = 199341677 := by
        calc
          (2 : ZMod 472210373) ^ 14756574 = (2 : ZMod 472210373) ^ (7378287 + 7378287) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 7378287 * (2 : ZMod 472210373) ^ 7378287 := by rw [pow_add]
          _ = 199341677 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 472210373) ^ 29513148 = 177417500 := by
        calc
          (2 : ZMod 472210373) ^ 29513148 = (2 : ZMod 472210373) ^ (14756574 + 14756574) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 14756574 * (2 : ZMod 472210373) ^ 14756574 := by rw [pow_add]
          _ = 177417500 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 472210373) ^ 59026296 = 49883568 := by
        calc
          (2 : ZMod 472210373) ^ 59026296 = (2 : ZMod 472210373) ^ (29513148 + 29513148) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 29513148 * (2 : ZMod 472210373) ^ 29513148 := by rw [pow_add]
          _ = 49883568 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 472210373) ^ 118052593 = 372443236 := by
        calc
          (2 : ZMod 472210373) ^ 118052593 = (2 : ZMod 472210373) ^ (59026296 + 59026296 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 59026296 * (2 : ZMod 472210373) ^ 59026296) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 372443236 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 472210373) ^ 236105186 = 472210372 := by
        calc
          (2 : ZMod 472210373) ^ 236105186 = (2 : ZMod 472210373) ^ (118052593 + 118052593) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 118052593 * (2 : ZMod 472210373) ^ 118052593 := by rw [pow_add]
          _ = 472210372 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 472210373) ^ 472210372 = 1 := by
        calc
          (2 : ZMod 472210373) ^ 472210372 = (2 : ZMod 472210373) ^ (236105186 + 236105186) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 236105186 * (2 : ZMod 472210373) ^ 236105186 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (67, 1), (1031, 1), (1709, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (67, 1), (1031, 1), (1709, 1)] : List FactorBlock).map factorBlockValue).prod = 472210373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 472210373) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 472210373) ^ 3 = 8 := by
        calc
          (2 : ZMod 472210373) ^ 3 = (2 : ZMod 472210373) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 1 * (2 : ZMod 472210373) ^ 1) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 472210373) ^ 7 = 128 := by
        calc
          (2 : ZMod 472210373) ^ 7 = (2 : ZMod 472210373) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 3 * (2 : ZMod 472210373) ^ 3) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 472210373) ^ 14 = 16384 := by
        calc
          (2 : ZMod 472210373) ^ 14 = (2 : ZMod 472210373) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 7 * (2 : ZMod 472210373) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 472210373) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 472210373) ^ 28 = (2 : ZMod 472210373) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 14 * (2 : ZMod 472210373) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 472210373) ^ 56 = 47467823 := by
        calc
          (2 : ZMod 472210373) ^ 56 = (2 : ZMod 472210373) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 28 * (2 : ZMod 472210373) ^ 28 := by rw [pow_add]
          _ = 47467823 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 472210373) ^ 112 = 398866632 := by
        calc
          (2 : ZMod 472210373) ^ 112 = (2 : ZMod 472210373) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 56 * (2 : ZMod 472210373) ^ 56 := by rw [pow_add]
          _ = 398866632 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 472210373) ^ 225 = 349032051 := by
        calc
          (2 : ZMod 472210373) ^ 225 = (2 : ZMod 472210373) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 112 * (2 : ZMod 472210373) ^ 112) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 349032051 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 472210373) ^ 450 = 106919861 := by
        calc
          (2 : ZMod 472210373) ^ 450 = (2 : ZMod 472210373) ^ (225 + 225) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 225 * (2 : ZMod 472210373) ^ 225 := by rw [pow_add]
          _ = 106919861 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 472210373) ^ 900 = 64760936 := by
        calc
          (2 : ZMod 472210373) ^ 900 = (2 : ZMod 472210373) ^ (450 + 450) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 450 * (2 : ZMod 472210373) ^ 450 := by rw [pow_add]
          _ = 64760936 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 472210373) ^ 1801 = 281936425 := by
        calc
          (2 : ZMod 472210373) ^ 1801 = (2 : ZMod 472210373) ^ (900 + 900 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 900 * (2 : ZMod 472210373) ^ 900) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 281936425 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 472210373) ^ 3602 = 68060007 := by
        calc
          (2 : ZMod 472210373) ^ 3602 = (2 : ZMod 472210373) ^ (1801 + 1801) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 1801 * (2 : ZMod 472210373) ^ 1801 := by rw [pow_add]
          _ = 68060007 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 472210373) ^ 7205 = 270856615 := by
        calc
          (2 : ZMod 472210373) ^ 7205 = (2 : ZMod 472210373) ^ (3602 + 3602 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 3602 * (2 : ZMod 472210373) ^ 3602) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 270856615 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 472210373) ^ 14410 = 163153574 := by
        calc
          (2 : ZMod 472210373) ^ 14410 = (2 : ZMod 472210373) ^ (7205 + 7205) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 7205 * (2 : ZMod 472210373) ^ 7205 := by rw [pow_add]
          _ = 163153574 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 472210373) ^ 28821 = 384415198 := by
        calc
          (2 : ZMod 472210373) ^ 28821 = (2 : ZMod 472210373) ^ (14410 + 14410 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 14410 * (2 : ZMod 472210373) ^ 14410) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 384415198 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 472210373) ^ 57642 = 365150684 := by
        calc
          (2 : ZMod 472210373) ^ 57642 = (2 : ZMod 472210373) ^ (28821 + 28821) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 28821 * (2 : ZMod 472210373) ^ 28821 := by rw [pow_add]
          _ = 365150684 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 472210373) ^ 115285 = 407248620 := by
        calc
          (2 : ZMod 472210373) ^ 115285 = (2 : ZMod 472210373) ^ (57642 + 57642 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 57642 * (2 : ZMod 472210373) ^ 57642) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 407248620 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 472210373) ^ 230571 = 465115669 := by
        calc
          (2 : ZMod 472210373) ^ 230571 = (2 : ZMod 472210373) ^ (115285 + 115285 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 115285 * (2 : ZMod 472210373) ^ 115285) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 465115669 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 472210373) ^ 461142 = 32348054 := by
        calc
          (2 : ZMod 472210373) ^ 461142 = (2 : ZMod 472210373) ^ (230571 + 230571) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 230571 * (2 : ZMod 472210373) ^ 230571 := by rw [pow_add]
          _ = 32348054 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 472210373) ^ 922285 = 265392148 := by
        calc
          (2 : ZMod 472210373) ^ 922285 = (2 : ZMod 472210373) ^ (461142 + 461142 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 461142 * (2 : ZMod 472210373) ^ 461142) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 265392148 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 472210373) ^ 1844571 = 9930529 := by
        calc
          (2 : ZMod 472210373) ^ 1844571 = (2 : ZMod 472210373) ^ (922285 + 922285 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 922285 * (2 : ZMod 472210373) ^ 922285) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 9930529 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 472210373) ^ 3689143 = 344896907 := by
        calc
          (2 : ZMod 472210373) ^ 3689143 = (2 : ZMod 472210373) ^ (1844571 + 1844571 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 1844571 * (2 : ZMod 472210373) ^ 1844571) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 344896907 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 472210373) ^ 7378287 = 120532263 := by
        calc
          (2 : ZMod 472210373) ^ 7378287 = (2 : ZMod 472210373) ^ (3689143 + 3689143 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 3689143 * (2 : ZMod 472210373) ^ 3689143) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 120532263 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 472210373) ^ 14756574 = 199341677 := by
        calc
          (2 : ZMod 472210373) ^ 14756574 = (2 : ZMod 472210373) ^ (7378287 + 7378287) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 7378287 * (2 : ZMod 472210373) ^ 7378287 := by rw [pow_add]
          _ = 199341677 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 472210373) ^ 29513148 = 177417500 := by
        calc
          (2 : ZMod 472210373) ^ 29513148 = (2 : ZMod 472210373) ^ (14756574 + 14756574) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 14756574 * (2 : ZMod 472210373) ^ 14756574 := by rw [pow_add]
          _ = 177417500 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 472210373) ^ 59026296 = 49883568 := by
        calc
          (2 : ZMod 472210373) ^ 59026296 = (2 : ZMod 472210373) ^ (29513148 + 29513148) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 29513148 * (2 : ZMod 472210373) ^ 29513148 := by rw [pow_add]
          _ = 49883568 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 472210373) ^ 118052593 = 372443236 := by
        calc
          (2 : ZMod 472210373) ^ 118052593 = (2 : ZMod 472210373) ^ (59026296 + 59026296 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 59026296 * (2 : ZMod 472210373) ^ 59026296) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 372443236 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 472210373) ^ 236105186 = 472210372 := by
        calc
          (2 : ZMod 472210373) ^ 236105186 = (2 : ZMod 472210373) ^ (118052593 + 118052593) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 118052593 * (2 : ZMod 472210373) ^ 118052593 := by rw [pow_add]
          _ = 472210372 := by rw [factor_0_26]; decide
      change (2 : ZMod 472210373) ^ 236105186 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (2 : ZMod 472210373) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 472210373) ^ 3 = 8 := by
        calc
          (2 : ZMod 472210373) ^ 3 = (2 : ZMod 472210373) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 1 * (2 : ZMod 472210373) ^ 1) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 472210373) ^ 6 = 64 := by
        calc
          (2 : ZMod 472210373) ^ 6 = (2 : ZMod 472210373) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 3 * (2 : ZMod 472210373) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 472210373) ^ 13 = 8192 := by
        calc
          (2 : ZMod 472210373) ^ 13 = (2 : ZMod 472210373) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 6 * (2 : ZMod 472210373) ^ 6) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 472210373) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 472210373) ^ 26 = (2 : ZMod 472210373) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 13 * (2 : ZMod 472210373) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 472210373) ^ 53 = 301064961 := by
        calc
          (2 : ZMod 472210373) ^ 53 = (2 : ZMod 472210373) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 26 * (2 : ZMod 472210373) ^ 26) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 301064961 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 472210373) ^ 107 = 366622362 := by
        calc
          (2 : ZMod 472210373) ^ 107 = (2 : ZMod 472210373) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 53 * (2 : ZMod 472210373) ^ 53) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 366622362 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 472210373) ^ 215 = 373405492 := by
        calc
          (2 : ZMod 472210373) ^ 215 = (2 : ZMod 472210373) ^ (107 + 107 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 107 * (2 : ZMod 472210373) ^ 107) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 373405492 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 472210373) ^ 430 = 450629976 := by
        calc
          (2 : ZMod 472210373) ^ 430 = (2 : ZMod 472210373) ^ (215 + 215) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 215 * (2 : ZMod 472210373) ^ 215 := by rw [pow_add]
          _ = 450629976 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 472210373) ^ 860 = 304199716 := by
        calc
          (2 : ZMod 472210373) ^ 860 = (2 : ZMod 472210373) ^ (430 + 430) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 430 * (2 : ZMod 472210373) ^ 430 := by rw [pow_add]
          _ = 304199716 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 472210373) ^ 1720 = 266414380 := by
        calc
          (2 : ZMod 472210373) ^ 1720 = (2 : ZMod 472210373) ^ (860 + 860) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 860 * (2 : ZMod 472210373) ^ 860 := by rw [pow_add]
          _ = 266414380 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 472210373) ^ 3441 = 121873124 := by
        calc
          (2 : ZMod 472210373) ^ 3441 = (2 : ZMod 472210373) ^ (1720 + 1720 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 1720 * (2 : ZMod 472210373) ^ 1720) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 121873124 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 472210373) ^ 6882 = 285016524 := by
        calc
          (2 : ZMod 472210373) ^ 6882 = (2 : ZMod 472210373) ^ (3441 + 3441) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 3441 * (2 : ZMod 472210373) ^ 3441 := by rw [pow_add]
          _ = 285016524 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 472210373) ^ 13765 = 30696982 := by
        calc
          (2 : ZMod 472210373) ^ 13765 = (2 : ZMod 472210373) ^ (6882 + 6882 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 6882 * (2 : ZMod 472210373) ^ 6882) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 30696982 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 472210373) ^ 27530 = 404800110 := by
        calc
          (2 : ZMod 472210373) ^ 27530 = (2 : ZMod 472210373) ^ (13765 + 13765) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 13765 * (2 : ZMod 472210373) ^ 13765 := by rw [pow_add]
          _ = 404800110 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 472210373) ^ 55061 = 196530747 := by
        calc
          (2 : ZMod 472210373) ^ 55061 = (2 : ZMod 472210373) ^ (27530 + 27530 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 27530 * (2 : ZMod 472210373) ^ 27530) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 196530747 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 472210373) ^ 110123 = 302454685 := by
        calc
          (2 : ZMod 472210373) ^ 110123 = (2 : ZMod 472210373) ^ (55061 + 55061 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 55061 * (2 : ZMod 472210373) ^ 55061) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 302454685 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 472210373) ^ 220247 = 43234950 := by
        calc
          (2 : ZMod 472210373) ^ 220247 = (2 : ZMod 472210373) ^ (110123 + 110123 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 110123 * (2 : ZMod 472210373) ^ 110123) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 43234950 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 472210373) ^ 440494 = 84829318 := by
        calc
          (2 : ZMod 472210373) ^ 440494 = (2 : ZMod 472210373) ^ (220247 + 220247) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 220247 * (2 : ZMod 472210373) ^ 220247 := by rw [pow_add]
          _ = 84829318 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 472210373) ^ 880989 = 53027367 := by
        calc
          (2 : ZMod 472210373) ^ 880989 = (2 : ZMod 472210373) ^ (440494 + 440494 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 440494 * (2 : ZMod 472210373) ^ 440494) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 53027367 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 472210373) ^ 1761979 = 170561061 := by
        calc
          (2 : ZMod 472210373) ^ 1761979 = (2 : ZMod 472210373) ^ (880989 + 880989 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 880989 * (2 : ZMod 472210373) ^ 880989) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 170561061 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 472210373) ^ 3523958 = 181382073 := by
        calc
          (2 : ZMod 472210373) ^ 3523958 = (2 : ZMod 472210373) ^ (1761979 + 1761979) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 1761979 * (2 : ZMod 472210373) ^ 1761979 := by rw [pow_add]
          _ = 181382073 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 472210373) ^ 7047916 = 149575324 := by
        calc
          (2 : ZMod 472210373) ^ 7047916 = (2 : ZMod 472210373) ^ (3523958 + 3523958) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 3523958 * (2 : ZMod 472210373) ^ 3523958 := by rw [pow_add]
          _ = 149575324 := by rw [factor_1_21]; decide
      change (2 : ZMod 472210373) ^ 7047916 ≠ 1
      rw [factor_1_22]
      decide
    ·
      have factor_2_0 : (2 : ZMod 472210373) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 472210373) ^ 3 = 8 := by
        calc
          (2 : ZMod 472210373) ^ 3 = (2 : ZMod 472210373) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 1 * (2 : ZMod 472210373) ^ 1) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 472210373) ^ 6 = 64 := by
        calc
          (2 : ZMod 472210373) ^ 6 = (2 : ZMod 472210373) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 3 * (2 : ZMod 472210373) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 472210373) ^ 13 = 8192 := by
        calc
          (2 : ZMod 472210373) ^ 13 = (2 : ZMod 472210373) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 6 * (2 : ZMod 472210373) ^ 6) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 472210373) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 472210373) ^ 27 = (2 : ZMod 472210373) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 13 * (2 : ZMod 472210373) ^ 13) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 472210373) ^ 55 = 259839098 := by
        calc
          (2 : ZMod 472210373) ^ 55 = (2 : ZMod 472210373) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 27 * (2 : ZMod 472210373) ^ 27) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 259839098 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 472210373) ^ 111 = 199433316 := by
        calc
          (2 : ZMod 472210373) ^ 111 = (2 : ZMod 472210373) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 55 * (2 : ZMod 472210373) ^ 55) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 199433316 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 472210373) ^ 223 = 205310606 := by
        calc
          (2 : ZMod 472210373) ^ 223 = (2 : ZMod 472210373) ^ (111 + 111 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 111 * (2 : ZMod 472210373) ^ 111) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 205310606 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 472210373) ^ 447 = 426549059 := by
        calc
          (2 : ZMod 472210373) ^ 447 = (2 : ZMod 472210373) ^ (223 + 223 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 223 * (2 : ZMod 472210373) ^ 223) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 426549059 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 472210373) ^ 894 = 414195966 := by
        calc
          (2 : ZMod 472210373) ^ 894 = (2 : ZMod 472210373) ^ (447 + 447) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 447 * (2 : ZMod 472210373) ^ 447 := by rw [pow_add]
          _ = 414195966 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 472210373) ^ 1789 = 27160980 := by
        calc
          (2 : ZMod 472210373) ^ 1789 = (2 : ZMod 472210373) ^ (894 + 894 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 894 * (2 : ZMod 472210373) ^ 894) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 27160980 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 472210373) ^ 3578 = 151764809 := by
        calc
          (2 : ZMod 472210373) ^ 3578 = (2 : ZMod 472210373) ^ (1789 + 1789) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 1789 * (2 : ZMod 472210373) ^ 1789 := by rw [pow_add]
          _ = 151764809 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 472210373) ^ 7156 = 14629458 := by
        calc
          (2 : ZMod 472210373) ^ 7156 = (2 : ZMod 472210373) ^ (3578 + 3578) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 3578 * (2 : ZMod 472210373) ^ 3578 := by rw [pow_add]
          _ = 14629458 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 472210373) ^ 14312 = 189598228 := by
        calc
          (2 : ZMod 472210373) ^ 14312 = (2 : ZMod 472210373) ^ (7156 + 7156) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 7156 * (2 : ZMod 472210373) ^ 7156 := by rw [pow_add]
          _ = 189598228 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 472210373) ^ 28625 = 50432103 := by
        calc
          (2 : ZMod 472210373) ^ 28625 = (2 : ZMod 472210373) ^ (14312 + 14312 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 14312 * (2 : ZMod 472210373) ^ 14312) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 50432103 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 472210373) ^ 57251 = 336095826 := by
        calc
          (2 : ZMod 472210373) ^ 57251 = (2 : ZMod 472210373) ^ (28625 + 28625 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 28625 * (2 : ZMod 472210373) ^ 28625) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 336095826 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 472210373) ^ 114503 = 340507132 := by
        calc
          (2 : ZMod 472210373) ^ 114503 = (2 : ZMod 472210373) ^ (57251 + 57251 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 57251 * (2 : ZMod 472210373) ^ 57251) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 340507132 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 472210373) ^ 229006 = 392823749 := by
        calc
          (2 : ZMod 472210373) ^ 229006 = (2 : ZMod 472210373) ^ (114503 + 114503) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 114503 * (2 : ZMod 472210373) ^ 114503 := by rw [pow_add]
          _ = 392823749 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 472210373) ^ 458012 = 268307618 := by
        calc
          (2 : ZMod 472210373) ^ 458012 = (2 : ZMod 472210373) ^ (229006 + 229006) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 229006 * (2 : ZMod 472210373) ^ 229006 := by rw [pow_add]
          _ = 268307618 := by rw [factor_2_17]; decide
      change (2 : ZMod 472210373) ^ 458012 ≠ 1
      rw [factor_2_18]
      decide
    ·
      have factor_3_0 : (2 : ZMod 472210373) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 472210373) ^ 2 = 4 := by
        calc
          (2 : ZMod 472210373) ^ 2 = (2 : ZMod 472210373) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 1 * (2 : ZMod 472210373) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 472210373) ^ 4 = 16 := by
        calc
          (2 : ZMod 472210373) ^ 4 = (2 : ZMod 472210373) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 2 * (2 : ZMod 472210373) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 472210373) ^ 8 = 256 := by
        calc
          (2 : ZMod 472210373) ^ 8 = (2 : ZMod 472210373) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 4 * (2 : ZMod 472210373) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 472210373) ^ 16 = 65536 := by
        calc
          (2 : ZMod 472210373) ^ 16 = (2 : ZMod 472210373) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 8 * (2 : ZMod 472210373) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 472210373) ^ 33 = 90147878 := by
        calc
          (2 : ZMod 472210373) ^ 33 = (2 : ZMod 472210373) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 16 * (2 : ZMod 472210373) ^ 16) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 90147878 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 472210373) ^ 67 = 410975039 := by
        calc
          (2 : ZMod 472210373) ^ 67 = (2 : ZMod 472210373) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 33 * (2 : ZMod 472210373) ^ 33) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 410975039 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 472210373) ^ 134 = 223343316 := by
        calc
          (2 : ZMod 472210373) ^ 134 = (2 : ZMod 472210373) ^ (67 + 67) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 67 * (2 : ZMod 472210373) ^ 67 := by rw [pow_add]
          _ = 223343316 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 472210373) ^ 269 = 198127327 := by
        calc
          (2 : ZMod 472210373) ^ 269 = (2 : ZMod 472210373) ^ (134 + 134 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 134 * (2 : ZMod 472210373) ^ 134) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 198127327 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 472210373) ^ 539 = 439398878 := by
        calc
          (2 : ZMod 472210373) ^ 539 = (2 : ZMod 472210373) ^ (269 + 269 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 269 * (2 : ZMod 472210373) ^ 269) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 439398878 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 472210373) ^ 1079 = 243992039 := by
        calc
          (2 : ZMod 472210373) ^ 1079 = (2 : ZMod 472210373) ^ (539 + 539 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 539 * (2 : ZMod 472210373) ^ 539) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 243992039 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 472210373) ^ 2158 = 412920738 := by
        calc
          (2 : ZMod 472210373) ^ 2158 = (2 : ZMod 472210373) ^ (1079 + 1079) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 1079 * (2 : ZMod 472210373) ^ 1079 := by rw [pow_add]
          _ = 412920738 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 472210373) ^ 4317 = 26672149 := by
        calc
          (2 : ZMod 472210373) ^ 4317 = (2 : ZMod 472210373) ^ (2158 + 2158 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 2158 * (2 : ZMod 472210373) ^ 2158) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 26672149 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 472210373) ^ 8634 = 189149154 := by
        calc
          (2 : ZMod 472210373) ^ 8634 = (2 : ZMod 472210373) ^ (4317 + 4317) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 4317 * (2 : ZMod 472210373) ^ 4317 := by rw [pow_add]
          _ = 189149154 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 472210373) ^ 17269 = 227495680 := by
        calc
          (2 : ZMod 472210373) ^ 17269 = (2 : ZMod 472210373) ^ (8634 + 8634 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 8634 * (2 : ZMod 472210373) ^ 8634) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 227495680 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 472210373) ^ 34538 = 149660766 := by
        calc
          (2 : ZMod 472210373) ^ 34538 = (2 : ZMod 472210373) ^ (17269 + 17269) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 17269 * (2 : ZMod 472210373) ^ 17269 := by rw [pow_add]
          _ = 149660766 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 472210373) ^ 69077 = 347231178 := by
        calc
          (2 : ZMod 472210373) ^ 69077 = (2 : ZMod 472210373) ^ (34538 + 34538 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = ((2 : ZMod 472210373) ^ 34538 * (2 : ZMod 472210373) ^ 34538) * (2 : ZMod 472210373) := by rw [pow_succ, pow_add]
          _ = 347231178 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 472210373) ^ 138154 = 382025002 := by
        calc
          (2 : ZMod 472210373) ^ 138154 = (2 : ZMod 472210373) ^ (69077 + 69077) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 69077 * (2 : ZMod 472210373) ^ 69077 := by rw [pow_add]
          _ = 382025002 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 472210373) ^ 276308 = 95766476 := by
        calc
          (2 : ZMod 472210373) ^ 276308 = (2 : ZMod 472210373) ^ (138154 + 138154) :=
            congrArg (fun n : ℕ => (2 : ZMod 472210373) ^ n) (by norm_num)
          _ = (2 : ZMod 472210373) ^ 138154 * (2 : ZMod 472210373) ^ 138154 := by rw [pow_add]
          _ = 95766476 := by rw [factor_3_17]; decide
      change (2 : ZMod 472210373) ^ 276308 ≠ 1
      rw [factor_3_18]
      decide

#print axioms prime_lucas_472210373

end TotientTailPeriodKiller
end Erdos249257
