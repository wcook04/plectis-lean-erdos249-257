import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_440869801 : Nat.Prime 440869801 := by
  apply lucas_primality 440869801 (13 : ZMod 440869801)
  ·
      have fermat_0 : (13 : ZMod 440869801) ^ 1 = 13 := by norm_num
      have fermat_1 : (13 : ZMod 440869801) ^ 3 = 2197 := by
        calc
          (13 : ZMod 440869801) ^ 3 = (13 : ZMod 440869801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 1 * (13 : ZMod 440869801) ^ 1) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [fermat_0]; decide
      have fermat_2 : (13 : ZMod 440869801) ^ 6 = 4826809 := by
        calc
          (13 : ZMod 440869801) ^ 6 = (13 : ZMod 440869801) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 3 * (13 : ZMod 440869801) ^ 3 := by rw [pow_add]
          _ = 4826809 := by rw [fermat_1]; decide
      have fermat_3 : (13 : ZMod 440869801) ^ 13 = 198524059 := by
        calc
          (13 : ZMod 440869801) ^ 13 = (13 : ZMod 440869801) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 6 * (13 : ZMod 440869801) ^ 6) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 198524059 := by rw [fermat_2]; decide
      have fermat_4 : (13 : ZMod 440869801) ^ 26 = 136091523 := by
        calc
          (13 : ZMod 440869801) ^ 26 = (13 : ZMod 440869801) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 13 * (13 : ZMod 440869801) ^ 13 := by rw [pow_add]
          _ = 136091523 := by rw [fermat_3]; decide
      have fermat_5 : (13 : ZMod 440869801) ^ 52 = 207252415 := by
        calc
          (13 : ZMod 440869801) ^ 52 = (13 : ZMod 440869801) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 26 * (13 : ZMod 440869801) ^ 26 := by rw [pow_add]
          _ = 207252415 := by rw [fermat_4]; decide
      have fermat_6 : (13 : ZMod 440869801) ^ 105 = 372161966 := by
        calc
          (13 : ZMod 440869801) ^ 105 = (13 : ZMod 440869801) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 52 * (13 : ZMod 440869801) ^ 52) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 372161966 := by rw [fermat_5]; decide
      have fermat_7 : (13 : ZMod 440869801) ^ 210 = 214358778 := by
        calc
          (13 : ZMod 440869801) ^ 210 = (13 : ZMod 440869801) ^ (105 + 105) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 105 * (13 : ZMod 440869801) ^ 105 := by rw [pow_add]
          _ = 214358778 := by rw [fermat_6]; decide
      have fermat_8 : (13 : ZMod 440869801) ^ 420 = 276412015 := by
        calc
          (13 : ZMod 440869801) ^ 420 = (13 : ZMod 440869801) ^ (210 + 210) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 210 * (13 : ZMod 440869801) ^ 210 := by rw [pow_add]
          _ = 276412015 := by rw [fermat_7]; decide
      have fermat_9 : (13 : ZMod 440869801) ^ 840 = 95640862 := by
        calc
          (13 : ZMod 440869801) ^ 840 = (13 : ZMod 440869801) ^ (420 + 420) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 420 * (13 : ZMod 440869801) ^ 420 := by rw [pow_add]
          _ = 95640862 := by rw [fermat_8]; decide
      have fermat_10 : (13 : ZMod 440869801) ^ 1681 = 247491541 := by
        calc
          (13 : ZMod 440869801) ^ 1681 = (13 : ZMod 440869801) ^ (840 + 840 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 840 * (13 : ZMod 440869801) ^ 840) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 247491541 := by rw [fermat_9]; decide
      have fermat_11 : (13 : ZMod 440869801) ^ 3363 = 332632248 := by
        calc
          (13 : ZMod 440869801) ^ 3363 = (13 : ZMod 440869801) ^ (1681 + 1681 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 1681 * (13 : ZMod 440869801) ^ 1681) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 332632248 := by rw [fermat_10]; decide
      have fermat_12 : (13 : ZMod 440869801) ^ 6727 = 293802547 := by
        calc
          (13 : ZMod 440869801) ^ 6727 = (13 : ZMod 440869801) ^ (3363 + 3363 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 3363 * (13 : ZMod 440869801) ^ 3363) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 293802547 := by rw [fermat_11]; decide
      have fermat_13 : (13 : ZMod 440869801) ^ 13454 = 144807186 := by
        calc
          (13 : ZMod 440869801) ^ 13454 = (13 : ZMod 440869801) ^ (6727 + 6727) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 6727 * (13 : ZMod 440869801) ^ 6727 := by rw [pow_add]
          _ = 144807186 := by rw [fermat_12]; decide
      have fermat_14 : (13 : ZMod 440869801) ^ 26908 = 352259327 := by
        calc
          (13 : ZMod 440869801) ^ 26908 = (13 : ZMod 440869801) ^ (13454 + 13454) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 13454 * (13 : ZMod 440869801) ^ 13454 := by rw [pow_add]
          _ = 352259327 := by rw [fermat_13]; decide
      have fermat_15 : (13 : ZMod 440869801) ^ 53817 = 392770202 := by
        calc
          (13 : ZMod 440869801) ^ 53817 = (13 : ZMod 440869801) ^ (26908 + 26908 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 26908 * (13 : ZMod 440869801) ^ 26908) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 392770202 := by rw [fermat_14]; decide
      have fermat_16 : (13 : ZMod 440869801) ^ 107634 = 11851658 := by
        calc
          (13 : ZMod 440869801) ^ 107634 = (13 : ZMod 440869801) ^ (53817 + 53817) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 53817 * (13 : ZMod 440869801) ^ 53817 := by rw [pow_add]
          _ = 11851658 := by rw [fermat_15]; decide
      have fermat_17 : (13 : ZMod 440869801) ^ 215268 = 237880563 := by
        calc
          (13 : ZMod 440869801) ^ 215268 = (13 : ZMod 440869801) ^ (107634 + 107634) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 107634 * (13 : ZMod 440869801) ^ 107634 := by rw [pow_add]
          _ = 237880563 := by rw [fermat_16]; decide
      have fermat_18 : (13 : ZMod 440869801) ^ 430536 = 89684514 := by
        calc
          (13 : ZMod 440869801) ^ 430536 = (13 : ZMod 440869801) ^ (215268 + 215268) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 215268 * (13 : ZMod 440869801) ^ 215268 := by rw [pow_add]
          _ = 89684514 := by rw [fermat_17]; decide
      have fermat_19 : (13 : ZMod 440869801) ^ 861073 = 126797889 := by
        calc
          (13 : ZMod 440869801) ^ 861073 = (13 : ZMod 440869801) ^ (430536 + 430536 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 430536 * (13 : ZMod 440869801) ^ 430536) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 126797889 := by rw [fermat_18]; decide
      have fermat_20 : (13 : ZMod 440869801) ^ 1722147 = 155398064 := by
        calc
          (13 : ZMod 440869801) ^ 1722147 = (13 : ZMod 440869801) ^ (861073 + 861073 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 861073 * (13 : ZMod 440869801) ^ 861073) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 155398064 := by rw [fermat_19]; decide
      have fermat_21 : (13 : ZMod 440869801) ^ 3444295 = 429580957 := by
        calc
          (13 : ZMod 440869801) ^ 3444295 = (13 : ZMod 440869801) ^ (1722147 + 1722147 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 1722147 * (13 : ZMod 440869801) ^ 1722147) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 429580957 := by rw [fermat_20]; decide
      have fermat_22 : (13 : ZMod 440869801) ^ 6888590 = 174179276 := by
        calc
          (13 : ZMod 440869801) ^ 6888590 = (13 : ZMod 440869801) ^ (3444295 + 3444295) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 3444295 * (13 : ZMod 440869801) ^ 3444295 := by rw [pow_add]
          _ = 174179276 := by rw [fermat_21]; decide
      have fermat_23 : (13 : ZMod 440869801) ^ 13777181 = 439752726 := by
        calc
          (13 : ZMod 440869801) ^ 13777181 = (13 : ZMod 440869801) ^ (6888590 + 6888590 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 6888590 * (13 : ZMod 440869801) ^ 6888590) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 439752726 := by rw [fermat_22]; decide
      have fermat_24 : (13 : ZMod 440869801) ^ 27554362 = 195018795 := by
        calc
          (13 : ZMod 440869801) ^ 27554362 = (13 : ZMod 440869801) ^ (13777181 + 13777181) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 13777181 * (13 : ZMod 440869801) ^ 13777181 := by rw [pow_add]
          _ = 195018795 := by rw [fermat_23]; decide
      have fermat_25 : (13 : ZMod 440869801) ^ 55108725 = 62811372 := by
        calc
          (13 : ZMod 440869801) ^ 55108725 = (13 : ZMod 440869801) ^ (27554362 + 27554362 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 27554362 * (13 : ZMod 440869801) ^ 27554362) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 62811372 := by rw [fermat_24]; decide
      have fermat_26 : (13 : ZMod 440869801) ^ 110217450 = 432979156 := by
        calc
          (13 : ZMod 440869801) ^ 110217450 = (13 : ZMod 440869801) ^ (55108725 + 55108725) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 55108725 * (13 : ZMod 440869801) ^ 55108725 := by rw [pow_add]
          _ = 432979156 := by rw [fermat_25]; decide
      have fermat_27 : (13 : ZMod 440869801) ^ 220434900 = 440869800 := by
        calc
          (13 : ZMod 440869801) ^ 220434900 = (13 : ZMod 440869801) ^ (110217450 + 110217450) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 110217450 * (13 : ZMod 440869801) ^ 110217450 := by rw [pow_add]
          _ = 440869800 := by rw [fermat_26]; decide
      have fermat_28 : (13 : ZMod 440869801) ^ 440869800 = 1 := by
        calc
          (13 : ZMod 440869801) ^ 440869800 = (13 : ZMod 440869801) ^ (220434900 + 220434900) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 220434900 * (13 : ZMod 440869801) ^ 220434900 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 2), (7, 1), (37, 1), (2837, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 2), (7, 1), (37, 1), (2837, 1)] : List FactorBlock).map factorBlockValue).prod = 440869801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (13 : ZMod 440869801) ^ 1 = 13 := by norm_num
      have factor_0_1 : (13 : ZMod 440869801) ^ 3 = 2197 := by
        calc
          (13 : ZMod 440869801) ^ 3 = (13 : ZMod 440869801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 1 * (13 : ZMod 440869801) ^ 1) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_0_0]; decide
      have factor_0_2 : (13 : ZMod 440869801) ^ 6 = 4826809 := by
        calc
          (13 : ZMod 440869801) ^ 6 = (13 : ZMod 440869801) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 3 * (13 : ZMod 440869801) ^ 3 := by rw [pow_add]
          _ = 4826809 := by rw [factor_0_1]; decide
      have factor_0_3 : (13 : ZMod 440869801) ^ 13 = 198524059 := by
        calc
          (13 : ZMod 440869801) ^ 13 = (13 : ZMod 440869801) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 6 * (13 : ZMod 440869801) ^ 6) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 198524059 := by rw [factor_0_2]; decide
      have factor_0_4 : (13 : ZMod 440869801) ^ 26 = 136091523 := by
        calc
          (13 : ZMod 440869801) ^ 26 = (13 : ZMod 440869801) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 13 * (13 : ZMod 440869801) ^ 13 := by rw [pow_add]
          _ = 136091523 := by rw [factor_0_3]; decide
      have factor_0_5 : (13 : ZMod 440869801) ^ 52 = 207252415 := by
        calc
          (13 : ZMod 440869801) ^ 52 = (13 : ZMod 440869801) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 26 * (13 : ZMod 440869801) ^ 26 := by rw [pow_add]
          _ = 207252415 := by rw [factor_0_4]; decide
      have factor_0_6 : (13 : ZMod 440869801) ^ 105 = 372161966 := by
        calc
          (13 : ZMod 440869801) ^ 105 = (13 : ZMod 440869801) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 52 * (13 : ZMod 440869801) ^ 52) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 372161966 := by rw [factor_0_5]; decide
      have factor_0_7 : (13 : ZMod 440869801) ^ 210 = 214358778 := by
        calc
          (13 : ZMod 440869801) ^ 210 = (13 : ZMod 440869801) ^ (105 + 105) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 105 * (13 : ZMod 440869801) ^ 105 := by rw [pow_add]
          _ = 214358778 := by rw [factor_0_6]; decide
      have factor_0_8 : (13 : ZMod 440869801) ^ 420 = 276412015 := by
        calc
          (13 : ZMod 440869801) ^ 420 = (13 : ZMod 440869801) ^ (210 + 210) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 210 * (13 : ZMod 440869801) ^ 210 := by rw [pow_add]
          _ = 276412015 := by rw [factor_0_7]; decide
      have factor_0_9 : (13 : ZMod 440869801) ^ 840 = 95640862 := by
        calc
          (13 : ZMod 440869801) ^ 840 = (13 : ZMod 440869801) ^ (420 + 420) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 420 * (13 : ZMod 440869801) ^ 420 := by rw [pow_add]
          _ = 95640862 := by rw [factor_0_8]; decide
      have factor_0_10 : (13 : ZMod 440869801) ^ 1681 = 247491541 := by
        calc
          (13 : ZMod 440869801) ^ 1681 = (13 : ZMod 440869801) ^ (840 + 840 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 840 * (13 : ZMod 440869801) ^ 840) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 247491541 := by rw [factor_0_9]; decide
      have factor_0_11 : (13 : ZMod 440869801) ^ 3363 = 332632248 := by
        calc
          (13 : ZMod 440869801) ^ 3363 = (13 : ZMod 440869801) ^ (1681 + 1681 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 1681 * (13 : ZMod 440869801) ^ 1681) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 332632248 := by rw [factor_0_10]; decide
      have factor_0_12 : (13 : ZMod 440869801) ^ 6727 = 293802547 := by
        calc
          (13 : ZMod 440869801) ^ 6727 = (13 : ZMod 440869801) ^ (3363 + 3363 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 3363 * (13 : ZMod 440869801) ^ 3363) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 293802547 := by rw [factor_0_11]; decide
      have factor_0_13 : (13 : ZMod 440869801) ^ 13454 = 144807186 := by
        calc
          (13 : ZMod 440869801) ^ 13454 = (13 : ZMod 440869801) ^ (6727 + 6727) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 6727 * (13 : ZMod 440869801) ^ 6727 := by rw [pow_add]
          _ = 144807186 := by rw [factor_0_12]; decide
      have factor_0_14 : (13 : ZMod 440869801) ^ 26908 = 352259327 := by
        calc
          (13 : ZMod 440869801) ^ 26908 = (13 : ZMod 440869801) ^ (13454 + 13454) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 13454 * (13 : ZMod 440869801) ^ 13454 := by rw [pow_add]
          _ = 352259327 := by rw [factor_0_13]; decide
      have factor_0_15 : (13 : ZMod 440869801) ^ 53817 = 392770202 := by
        calc
          (13 : ZMod 440869801) ^ 53817 = (13 : ZMod 440869801) ^ (26908 + 26908 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 26908 * (13 : ZMod 440869801) ^ 26908) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 392770202 := by rw [factor_0_14]; decide
      have factor_0_16 : (13 : ZMod 440869801) ^ 107634 = 11851658 := by
        calc
          (13 : ZMod 440869801) ^ 107634 = (13 : ZMod 440869801) ^ (53817 + 53817) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 53817 * (13 : ZMod 440869801) ^ 53817 := by rw [pow_add]
          _ = 11851658 := by rw [factor_0_15]; decide
      have factor_0_17 : (13 : ZMod 440869801) ^ 215268 = 237880563 := by
        calc
          (13 : ZMod 440869801) ^ 215268 = (13 : ZMod 440869801) ^ (107634 + 107634) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 107634 * (13 : ZMod 440869801) ^ 107634 := by rw [pow_add]
          _ = 237880563 := by rw [factor_0_16]; decide
      have factor_0_18 : (13 : ZMod 440869801) ^ 430536 = 89684514 := by
        calc
          (13 : ZMod 440869801) ^ 430536 = (13 : ZMod 440869801) ^ (215268 + 215268) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 215268 * (13 : ZMod 440869801) ^ 215268 := by rw [pow_add]
          _ = 89684514 := by rw [factor_0_17]; decide
      have factor_0_19 : (13 : ZMod 440869801) ^ 861073 = 126797889 := by
        calc
          (13 : ZMod 440869801) ^ 861073 = (13 : ZMod 440869801) ^ (430536 + 430536 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 430536 * (13 : ZMod 440869801) ^ 430536) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 126797889 := by rw [factor_0_18]; decide
      have factor_0_20 : (13 : ZMod 440869801) ^ 1722147 = 155398064 := by
        calc
          (13 : ZMod 440869801) ^ 1722147 = (13 : ZMod 440869801) ^ (861073 + 861073 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 861073 * (13 : ZMod 440869801) ^ 861073) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 155398064 := by rw [factor_0_19]; decide
      have factor_0_21 : (13 : ZMod 440869801) ^ 3444295 = 429580957 := by
        calc
          (13 : ZMod 440869801) ^ 3444295 = (13 : ZMod 440869801) ^ (1722147 + 1722147 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 1722147 * (13 : ZMod 440869801) ^ 1722147) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 429580957 := by rw [factor_0_20]; decide
      have factor_0_22 : (13 : ZMod 440869801) ^ 6888590 = 174179276 := by
        calc
          (13 : ZMod 440869801) ^ 6888590 = (13 : ZMod 440869801) ^ (3444295 + 3444295) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 3444295 * (13 : ZMod 440869801) ^ 3444295 := by rw [pow_add]
          _ = 174179276 := by rw [factor_0_21]; decide
      have factor_0_23 : (13 : ZMod 440869801) ^ 13777181 = 439752726 := by
        calc
          (13 : ZMod 440869801) ^ 13777181 = (13 : ZMod 440869801) ^ (6888590 + 6888590 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 6888590 * (13 : ZMod 440869801) ^ 6888590) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 439752726 := by rw [factor_0_22]; decide
      have factor_0_24 : (13 : ZMod 440869801) ^ 27554362 = 195018795 := by
        calc
          (13 : ZMod 440869801) ^ 27554362 = (13 : ZMod 440869801) ^ (13777181 + 13777181) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 13777181 * (13 : ZMod 440869801) ^ 13777181 := by rw [pow_add]
          _ = 195018795 := by rw [factor_0_23]; decide
      have factor_0_25 : (13 : ZMod 440869801) ^ 55108725 = 62811372 := by
        calc
          (13 : ZMod 440869801) ^ 55108725 = (13 : ZMod 440869801) ^ (27554362 + 27554362 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 27554362 * (13 : ZMod 440869801) ^ 27554362) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 62811372 := by rw [factor_0_24]; decide
      have factor_0_26 : (13 : ZMod 440869801) ^ 110217450 = 432979156 := by
        calc
          (13 : ZMod 440869801) ^ 110217450 = (13 : ZMod 440869801) ^ (55108725 + 55108725) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 55108725 * (13 : ZMod 440869801) ^ 55108725 := by rw [pow_add]
          _ = 432979156 := by rw [factor_0_25]; decide
      have factor_0_27 : (13 : ZMod 440869801) ^ 220434900 = 440869800 := by
        calc
          (13 : ZMod 440869801) ^ 220434900 = (13 : ZMod 440869801) ^ (110217450 + 110217450) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 110217450 * (13 : ZMod 440869801) ^ 110217450 := by rw [pow_add]
          _ = 440869800 := by rw [factor_0_26]; decide
      change (13 : ZMod 440869801) ^ 220434900 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (13 : ZMod 440869801) ^ 1 = 13 := by norm_num
      have factor_1_1 : (13 : ZMod 440869801) ^ 2 = 169 := by
        calc
          (13 : ZMod 440869801) ^ 2 = (13 : ZMod 440869801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 1 * (13 : ZMod 440869801) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_1_0]; decide
      have factor_1_2 : (13 : ZMod 440869801) ^ 4 = 28561 := by
        calc
          (13 : ZMod 440869801) ^ 4 = (13 : ZMod 440869801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 2 * (13 : ZMod 440869801) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_1_1]; decide
      have factor_1_3 : (13 : ZMod 440869801) ^ 8 = 374860920 := by
        calc
          (13 : ZMod 440869801) ^ 8 = (13 : ZMod 440869801) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 4 * (13 : ZMod 440869801) ^ 4 := by rw [pow_add]
          _ = 374860920 := by rw [factor_1_2]; decide
      have factor_1_4 : (13 : ZMod 440869801) ^ 17 = 19138438 := by
        calc
          (13 : ZMod 440869801) ^ 17 = (13 : ZMod 440869801) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 8 * (13 : ZMod 440869801) ^ 8) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 19138438 := by rw [factor_1_3]; decide
      have factor_1_5 : (13 : ZMod 440869801) ^ 35 = 307107820 := by
        calc
          (13 : ZMod 440869801) ^ 35 = (13 : ZMod 440869801) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 17 * (13 : ZMod 440869801) ^ 17) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 307107820 := by rw [factor_1_4]; decide
      have factor_1_6 : (13 : ZMod 440869801) ^ 70 = 62473744 := by
        calc
          (13 : ZMod 440869801) ^ 70 = (13 : ZMod 440869801) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 35 * (13 : ZMod 440869801) ^ 35 := by rw [pow_add]
          _ = 62473744 := by rw [factor_1_5]; decide
      have factor_1_7 : (13 : ZMod 440869801) ^ 140 = 363761054 := by
        calc
          (13 : ZMod 440869801) ^ 140 = (13 : ZMod 440869801) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 70 * (13 : ZMod 440869801) ^ 70 := by rw [pow_add]
          _ = 363761054 := by rw [factor_1_6]; decide
      have factor_1_8 : (13 : ZMod 440869801) ^ 280 = 35349181 := by
        calc
          (13 : ZMod 440869801) ^ 280 = (13 : ZMod 440869801) ^ (140 + 140) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 140 * (13 : ZMod 440869801) ^ 140 := by rw [pow_add]
          _ = 35349181 := by rw [factor_1_7]; decide
      have factor_1_9 : (13 : ZMod 440869801) ^ 560 = 266479645 := by
        calc
          (13 : ZMod 440869801) ^ 560 = (13 : ZMod 440869801) ^ (280 + 280) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 280 * (13 : ZMod 440869801) ^ 280 := by rw [pow_add]
          _ = 266479645 := by rw [factor_1_8]; decide
      have factor_1_10 : (13 : ZMod 440869801) ^ 1121 = 415835913 := by
        calc
          (13 : ZMod 440869801) ^ 1121 = (13 : ZMod 440869801) ^ (560 + 560 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 560 * (13 : ZMod 440869801) ^ 560) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 415835913 := by rw [factor_1_9]; decide
      have factor_1_11 : (13 : ZMod 440869801) ^ 2242 = 8014646 := by
        calc
          (13 : ZMod 440869801) ^ 2242 = (13 : ZMod 440869801) ^ (1121 + 1121) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 1121 * (13 : ZMod 440869801) ^ 1121 := by rw [pow_add]
          _ = 8014646 := by rw [factor_1_10]; decide
      have factor_1_12 : (13 : ZMod 440869801) ^ 4484 = 261369417 := by
        calc
          (13 : ZMod 440869801) ^ 4484 = (13 : ZMod 440869801) ^ (2242 + 2242) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 2242 * (13 : ZMod 440869801) ^ 2242 := by rw [pow_add]
          _ = 261369417 := by rw [factor_1_11]; decide
      have factor_1_13 : (13 : ZMod 440869801) ^ 8969 = 327029277 := by
        calc
          (13 : ZMod 440869801) ^ 8969 = (13 : ZMod 440869801) ^ (4484 + 4484 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 4484 * (13 : ZMod 440869801) ^ 4484) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 327029277 := by rw [factor_1_12]; decide
      have factor_1_14 : (13 : ZMod 440869801) ^ 17939 = 335137728 := by
        calc
          (13 : ZMod 440869801) ^ 17939 = (13 : ZMod 440869801) ^ (8969 + 8969 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 8969 * (13 : ZMod 440869801) ^ 8969) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 335137728 := by rw [factor_1_13]; decide
      have factor_1_15 : (13 : ZMod 440869801) ^ 35878 = 369891422 := by
        calc
          (13 : ZMod 440869801) ^ 35878 = (13 : ZMod 440869801) ^ (17939 + 17939) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 17939 * (13 : ZMod 440869801) ^ 17939 := by rw [pow_add]
          _ = 369891422 := by rw [factor_1_14]; decide
      have factor_1_16 : (13 : ZMod 440869801) ^ 71756 = 411120590 := by
        calc
          (13 : ZMod 440869801) ^ 71756 = (13 : ZMod 440869801) ^ (35878 + 35878) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 35878 * (13 : ZMod 440869801) ^ 35878 := by rw [pow_add]
          _ = 411120590 := by rw [factor_1_15]; decide
      have factor_1_17 : (13 : ZMod 440869801) ^ 143512 = 290501091 := by
        calc
          (13 : ZMod 440869801) ^ 143512 = (13 : ZMod 440869801) ^ (71756 + 71756) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 71756 * (13 : ZMod 440869801) ^ 71756 := by rw [pow_add]
          _ = 290501091 := by rw [factor_1_16]; decide
      have factor_1_18 : (13 : ZMod 440869801) ^ 287024 = 100643619 := by
        calc
          (13 : ZMod 440869801) ^ 287024 = (13 : ZMod 440869801) ^ (143512 + 143512) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 143512 * (13 : ZMod 440869801) ^ 143512 := by rw [pow_add]
          _ = 100643619 := by rw [factor_1_17]; decide
      have factor_1_19 : (13 : ZMod 440869801) ^ 574049 = 378283742 := by
        calc
          (13 : ZMod 440869801) ^ 574049 = (13 : ZMod 440869801) ^ (287024 + 287024 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 287024 * (13 : ZMod 440869801) ^ 287024) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 378283742 := by rw [factor_1_18]; decide
      have factor_1_20 : (13 : ZMod 440869801) ^ 1148098 = 343675139 := by
        calc
          (13 : ZMod 440869801) ^ 1148098 = (13 : ZMod 440869801) ^ (574049 + 574049) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 574049 * (13 : ZMod 440869801) ^ 574049 := by rw [pow_add]
          _ = 343675139 := by rw [factor_1_19]; decide
      have factor_1_21 : (13 : ZMod 440869801) ^ 2296196 = 293375798 := by
        calc
          (13 : ZMod 440869801) ^ 2296196 = (13 : ZMod 440869801) ^ (1148098 + 1148098) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 1148098 * (13 : ZMod 440869801) ^ 1148098 := by rw [pow_add]
          _ = 293375798 := by rw [factor_1_20]; decide
      have factor_1_22 : (13 : ZMod 440869801) ^ 4592393 = 218842177 := by
        calc
          (13 : ZMod 440869801) ^ 4592393 = (13 : ZMod 440869801) ^ (2296196 + 2296196 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 2296196 * (13 : ZMod 440869801) ^ 2296196) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 218842177 := by rw [factor_1_21]; decide
      have factor_1_23 : (13 : ZMod 440869801) ^ 9184787 = 373714828 := by
        calc
          (13 : ZMod 440869801) ^ 9184787 = (13 : ZMod 440869801) ^ (4592393 + 4592393 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 4592393 * (13 : ZMod 440869801) ^ 4592393) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 373714828 := by rw [factor_1_22]; decide
      have factor_1_24 : (13 : ZMod 440869801) ^ 18369575 = 358913950 := by
        calc
          (13 : ZMod 440869801) ^ 18369575 = (13 : ZMod 440869801) ^ (9184787 + 9184787 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 9184787 * (13 : ZMod 440869801) ^ 9184787) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 358913950 := by rw [factor_1_23]; decide
      have factor_1_25 : (13 : ZMod 440869801) ^ 36739150 = 318318752 := by
        calc
          (13 : ZMod 440869801) ^ 36739150 = (13 : ZMod 440869801) ^ (18369575 + 18369575) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 18369575 * (13 : ZMod 440869801) ^ 18369575 := by rw [pow_add]
          _ = 318318752 := by rw [factor_1_24]; decide
      have factor_1_26 : (13 : ZMod 440869801) ^ 73478300 = 355304400 := by
        calc
          (13 : ZMod 440869801) ^ 73478300 = (13 : ZMod 440869801) ^ (36739150 + 36739150) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 36739150 * (13 : ZMod 440869801) ^ 36739150 := by rw [pow_add]
          _ = 355304400 := by rw [factor_1_25]; decide
      have factor_1_27 : (13 : ZMod 440869801) ^ 146956600 = 355304399 := by
        calc
          (13 : ZMod 440869801) ^ 146956600 = (13 : ZMod 440869801) ^ (73478300 + 73478300) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 73478300 * (13 : ZMod 440869801) ^ 73478300 := by rw [pow_add]
          _ = 355304399 := by rw [factor_1_26]; decide
      change (13 : ZMod 440869801) ^ 146956600 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (13 : ZMod 440869801) ^ 1 = 13 := by norm_num
      have factor_2_1 : (13 : ZMod 440869801) ^ 2 = 169 := by
        calc
          (13 : ZMod 440869801) ^ 2 = (13 : ZMod 440869801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 1 * (13 : ZMod 440869801) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_2_0]; decide
      have factor_2_2 : (13 : ZMod 440869801) ^ 5 = 371293 := by
        calc
          (13 : ZMod 440869801) ^ 5 = (13 : ZMod 440869801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 2 * (13 : ZMod 440869801) ^ 2) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 371293 := by rw [factor_2_1]; decide
      have factor_2_3 : (13 : ZMod 440869801) ^ 10 = 307113937 := by
        calc
          (13 : ZMod 440869801) ^ 10 = (13 : ZMod 440869801) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 5 * (13 : ZMod 440869801) ^ 5 := by rw [pow_add]
          _ = 307113937 := by rw [factor_2_2]; decide
      have factor_2_4 : (13 : ZMod 440869801) ^ 21 = 375244279 := by
        calc
          (13 : ZMod 440869801) ^ 21 = (13 : ZMod 440869801) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 10 * (13 : ZMod 440869801) ^ 10) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 375244279 := by rw [factor_2_3]; decide
      have factor_2_5 : (13 : ZMod 440869801) ^ 42 = 184056620 := by
        calc
          (13 : ZMod 440869801) ^ 42 = (13 : ZMod 440869801) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 21 * (13 : ZMod 440869801) ^ 21 := by rw [pow_add]
          _ = 184056620 := by rw [factor_2_4]; decide
      have factor_2_6 : (13 : ZMod 440869801) ^ 84 = 20246684 := by
        calc
          (13 : ZMod 440869801) ^ 84 = (13 : ZMod 440869801) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 42 * (13 : ZMod 440869801) ^ 42 := by rw [pow_add]
          _ = 20246684 := by rw [factor_2_5]; decide
      have factor_2_7 : (13 : ZMod 440869801) ^ 168 = 418109240 := by
        calc
          (13 : ZMod 440869801) ^ 168 = (13 : ZMod 440869801) ^ (84 + 84) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 84 * (13 : ZMod 440869801) ^ 84 := by rw [pow_add]
          _ = 418109240 := by rw [factor_2_6]; decide
      have factor_2_8 : (13 : ZMod 440869801) ^ 336 = 399979074 := by
        calc
          (13 : ZMod 440869801) ^ 336 = (13 : ZMod 440869801) ^ (168 + 168) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 168 * (13 : ZMod 440869801) ^ 168 := by rw [pow_add]
          _ = 399979074 := by rw [factor_2_7]; decide
      have factor_2_9 : (13 : ZMod 440869801) ^ 672 = 370789710 := by
        calc
          (13 : ZMod 440869801) ^ 672 = (13 : ZMod 440869801) ^ (336 + 336) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 336 * (13 : ZMod 440869801) ^ 336 := by rw [pow_add]
          _ = 370789710 := by rw [factor_2_8]; decide
      have factor_2_10 : (13 : ZMod 440869801) ^ 1345 = 115144330 := by
        calc
          (13 : ZMod 440869801) ^ 1345 = (13 : ZMod 440869801) ^ (672 + 672 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 672 * (13 : ZMod 440869801) ^ 672) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 115144330 := by rw [factor_2_9]; decide
      have factor_2_11 : (13 : ZMod 440869801) ^ 2690 = 45708438 := by
        calc
          (13 : ZMod 440869801) ^ 2690 = (13 : ZMod 440869801) ^ (1345 + 1345) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 1345 * (13 : ZMod 440869801) ^ 1345 := by rw [pow_add]
          _ = 45708438 := by rw [factor_2_10]; decide
      have factor_2_12 : (13 : ZMod 440869801) ^ 5381 = 57569582 := by
        calc
          (13 : ZMod 440869801) ^ 5381 = (13 : ZMod 440869801) ^ (2690 + 2690 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 2690 * (13 : ZMod 440869801) ^ 2690) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 57569582 := by rw [factor_2_11]; decide
      have factor_2_13 : (13 : ZMod 440869801) ^ 10763 = 11549780 := by
        calc
          (13 : ZMod 440869801) ^ 10763 = (13 : ZMod 440869801) ^ (5381 + 5381 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 5381 * (13 : ZMod 440869801) ^ 5381) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 11549780 := by rw [factor_2_12]; decide
      have factor_2_14 : (13 : ZMod 440869801) ^ 21526 = 356271223 := by
        calc
          (13 : ZMod 440869801) ^ 21526 = (13 : ZMod 440869801) ^ (10763 + 10763) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 10763 * (13 : ZMod 440869801) ^ 10763 := by rw [pow_add]
          _ = 356271223 := by rw [factor_2_13]; decide
      have factor_2_15 : (13 : ZMod 440869801) ^ 43053 = 20520638 := by
        calc
          (13 : ZMod 440869801) ^ 43053 = (13 : ZMod 440869801) ^ (21526 + 21526 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 21526 * (13 : ZMod 440869801) ^ 21526) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 20520638 := by rw [factor_2_14]; decide
      have factor_2_16 : (13 : ZMod 440869801) ^ 86107 = 401613229 := by
        calc
          (13 : ZMod 440869801) ^ 86107 = (13 : ZMod 440869801) ^ (43053 + 43053 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 43053 * (13 : ZMod 440869801) ^ 43053) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 401613229 := by rw [factor_2_15]; decide
      have factor_2_17 : (13 : ZMod 440869801) ^ 172214 = 421003644 := by
        calc
          (13 : ZMod 440869801) ^ 172214 = (13 : ZMod 440869801) ^ (86107 + 86107) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 86107 * (13 : ZMod 440869801) ^ 86107 := by rw [pow_add]
          _ = 421003644 := by rw [factor_2_16]; decide
      have factor_2_18 : (13 : ZMod 440869801) ^ 344429 = 308710310 := by
        calc
          (13 : ZMod 440869801) ^ 344429 = (13 : ZMod 440869801) ^ (172214 + 172214 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 172214 * (13 : ZMod 440869801) ^ 172214) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 308710310 := by rw [factor_2_17]; decide
      have factor_2_19 : (13 : ZMod 440869801) ^ 688859 = 48814587 := by
        calc
          (13 : ZMod 440869801) ^ 688859 = (13 : ZMod 440869801) ^ (344429 + 344429 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 344429 * (13 : ZMod 440869801) ^ 344429) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 48814587 := by rw [factor_2_18]; decide
      have factor_2_20 : (13 : ZMod 440869801) ^ 1377718 = 103508654 := by
        calc
          (13 : ZMod 440869801) ^ 1377718 = (13 : ZMod 440869801) ^ (688859 + 688859) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 688859 * (13 : ZMod 440869801) ^ 688859 := by rw [pow_add]
          _ = 103508654 := by rw [factor_2_19]; decide
      have factor_2_21 : (13 : ZMod 440869801) ^ 2755436 = 182890263 := by
        calc
          (13 : ZMod 440869801) ^ 2755436 = (13 : ZMod 440869801) ^ (1377718 + 1377718) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 1377718 * (13 : ZMod 440869801) ^ 1377718 := by rw [pow_add]
          _ = 182890263 := by rw [factor_2_20]; decide
      have factor_2_22 : (13 : ZMod 440869801) ^ 5510872 = 67004641 := by
        calc
          (13 : ZMod 440869801) ^ 5510872 = (13 : ZMod 440869801) ^ (2755436 + 2755436) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 2755436 * (13 : ZMod 440869801) ^ 2755436 := by rw [pow_add]
          _ = 67004641 := by rw [factor_2_21]; decide
      have factor_2_23 : (13 : ZMod 440869801) ^ 11021745 = 198942437 := by
        calc
          (13 : ZMod 440869801) ^ 11021745 = (13 : ZMod 440869801) ^ (5510872 + 5510872 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 5510872 * (13 : ZMod 440869801) ^ 5510872) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 198942437 := by rw [factor_2_22]; decide
      have factor_2_24 : (13 : ZMod 440869801) ^ 22043490 = 134385622 := by
        calc
          (13 : ZMod 440869801) ^ 22043490 = (13 : ZMod 440869801) ^ (11021745 + 11021745) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 11021745 * (13 : ZMod 440869801) ^ 11021745 := by rw [pow_add]
          _ = 134385622 := by rw [factor_2_23]; decide
      have factor_2_25 : (13 : ZMod 440869801) ^ 44086980 = 254929554 := by
        calc
          (13 : ZMod 440869801) ^ 44086980 = (13 : ZMod 440869801) ^ (22043490 + 22043490) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 22043490 * (13 : ZMod 440869801) ^ 22043490 := by rw [pow_add]
          _ = 254929554 := by rw [factor_2_24]; decide
      have factor_2_26 : (13 : ZMod 440869801) ^ 88173960 = 310026473 := by
        calc
          (13 : ZMod 440869801) ^ 88173960 = (13 : ZMod 440869801) ^ (44086980 + 44086980) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 44086980 * (13 : ZMod 440869801) ^ 44086980 := by rw [pow_add]
          _ = 310026473 := by rw [factor_2_25]; decide
      change (13 : ZMod 440869801) ^ 88173960 ≠ 1
      rw [factor_2_26]
      decide
    ·
      have factor_3_0 : (13 : ZMod 440869801) ^ 1 = 13 := by norm_num
      have factor_3_1 : (13 : ZMod 440869801) ^ 3 = 2197 := by
        calc
          (13 : ZMod 440869801) ^ 3 = (13 : ZMod 440869801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 1 * (13 : ZMod 440869801) ^ 1) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_3_0]; decide
      have factor_3_2 : (13 : ZMod 440869801) ^ 7 = 62748517 := by
        calc
          (13 : ZMod 440869801) ^ 7 = (13 : ZMod 440869801) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 3 * (13 : ZMod 440869801) ^ 3) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 62748517 := by rw [factor_3_1]; decide
      have factor_3_3 : (13 : ZMod 440869801) ^ 15 = 44461095 := by
        calc
          (13 : ZMod 440869801) ^ 15 = (13 : ZMod 440869801) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 7 * (13 : ZMod 440869801) ^ 7) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 44461095 := by rw [factor_3_2]; decide
      have factor_3_4 : (13 : ZMod 440869801) ^ 30 = 201822787 := by
        calc
          (13 : ZMod 440869801) ^ 30 = (13 : ZMod 440869801) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 15 * (13 : ZMod 440869801) ^ 15 := by rw [pow_add]
          _ = 201822787 := by rw [factor_3_3]; decide
      have factor_3_5 : (13 : ZMod 440869801) ^ 60 = 298672289 := by
        calc
          (13 : ZMod 440869801) ^ 60 = (13 : ZMod 440869801) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 30 * (13 : ZMod 440869801) ^ 30 := by rw [pow_add]
          _ = 298672289 := by rw [factor_3_4]; decide
      have factor_3_6 : (13 : ZMod 440869801) ^ 120 = 68492163 := by
        calc
          (13 : ZMod 440869801) ^ 120 = (13 : ZMod 440869801) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 60 * (13 : ZMod 440869801) ^ 60 := by rw [pow_add]
          _ = 68492163 := by rw [factor_3_5]; decide
      have factor_3_7 : (13 : ZMod 440869801) ^ 240 = 315693640 := by
        calc
          (13 : ZMod 440869801) ^ 240 = (13 : ZMod 440869801) ^ (120 + 120) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 120 * (13 : ZMod 440869801) ^ 120 := by rw [pow_add]
          _ = 315693640 := by rw [factor_3_6]; decide
      have factor_3_8 : (13 : ZMod 440869801) ^ 480 = 413989855 := by
        calc
          (13 : ZMod 440869801) ^ 480 = (13 : ZMod 440869801) ^ (240 + 240) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 240 * (13 : ZMod 440869801) ^ 240 := by rw [pow_add]
          _ = 413989855 := by rw [factor_3_7]; decide
      have factor_3_9 : (13 : ZMod 440869801) ^ 961 = 238813304 := by
        calc
          (13 : ZMod 440869801) ^ 961 = (13 : ZMod 440869801) ^ (480 + 480 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 480 * (13 : ZMod 440869801) ^ 480) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 238813304 := by rw [factor_3_8]; decide
      have factor_3_10 : (13 : ZMod 440869801) ^ 1922 = 260872028 := by
        calc
          (13 : ZMod 440869801) ^ 1922 = (13 : ZMod 440869801) ^ (961 + 961) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 961 * (13 : ZMod 440869801) ^ 961 := by rw [pow_add]
          _ = 260872028 := by rw [factor_3_9]; decide
      have factor_3_11 : (13 : ZMod 440869801) ^ 3844 = 207903463 := by
        calc
          (13 : ZMod 440869801) ^ 3844 = (13 : ZMod 440869801) ^ (1922 + 1922) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 1922 * (13 : ZMod 440869801) ^ 1922 := by rw [pow_add]
          _ = 207903463 := by rw [factor_3_10]; decide
      have factor_3_12 : (13 : ZMod 440869801) ^ 7688 = 315092159 := by
        calc
          (13 : ZMod 440869801) ^ 7688 = (13 : ZMod 440869801) ^ (3844 + 3844) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 3844 * (13 : ZMod 440869801) ^ 3844 := by rw [pow_add]
          _ = 315092159 := by rw [factor_3_11]; decide
      have factor_3_13 : (13 : ZMod 440869801) ^ 15376 = 237645320 := by
        calc
          (13 : ZMod 440869801) ^ 15376 = (13 : ZMod 440869801) ^ (7688 + 7688) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 7688 * (13 : ZMod 440869801) ^ 7688 := by rw [pow_add]
          _ = 237645320 := by rw [factor_3_12]; decide
      have factor_3_14 : (13 : ZMod 440869801) ^ 30752 = 53346680 := by
        calc
          (13 : ZMod 440869801) ^ 30752 = (13 : ZMod 440869801) ^ (15376 + 15376) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 15376 * (13 : ZMod 440869801) ^ 15376 := by rw [pow_add]
          _ = 53346680 := by rw [factor_3_13]; decide
      have factor_3_15 : (13 : ZMod 440869801) ^ 61505 = 223481217 := by
        calc
          (13 : ZMod 440869801) ^ 61505 = (13 : ZMod 440869801) ^ (30752 + 30752 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 30752 * (13 : ZMod 440869801) ^ 30752) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 223481217 := by rw [factor_3_14]; decide
      have factor_3_16 : (13 : ZMod 440869801) ^ 123010 = 65559473 := by
        calc
          (13 : ZMod 440869801) ^ 123010 = (13 : ZMod 440869801) ^ (61505 + 61505) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 61505 * (13 : ZMod 440869801) ^ 61505 := by rw [pow_add]
          _ = 65559473 := by rw [factor_3_15]; decide
      have factor_3_17 : (13 : ZMod 440869801) ^ 246021 = 368511536 := by
        calc
          (13 : ZMod 440869801) ^ 246021 = (13 : ZMod 440869801) ^ (123010 + 123010 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 123010 * (13 : ZMod 440869801) ^ 123010) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 368511536 := by rw [factor_3_16]; decide
      have factor_3_18 : (13 : ZMod 440869801) ^ 492042 = 338900942 := by
        calc
          (13 : ZMod 440869801) ^ 492042 = (13 : ZMod 440869801) ^ (246021 + 246021) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 246021 * (13 : ZMod 440869801) ^ 246021 := by rw [pow_add]
          _ = 338900942 := by rw [factor_3_17]; decide
      have factor_3_19 : (13 : ZMod 440869801) ^ 984084 = 234536685 := by
        calc
          (13 : ZMod 440869801) ^ 984084 = (13 : ZMod 440869801) ^ (492042 + 492042) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 492042 * (13 : ZMod 440869801) ^ 492042 := by rw [pow_add]
          _ = 234536685 := by rw [factor_3_18]; decide
      have factor_3_20 : (13 : ZMod 440869801) ^ 1968168 = 160818527 := by
        calc
          (13 : ZMod 440869801) ^ 1968168 = (13 : ZMod 440869801) ^ (984084 + 984084) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 984084 * (13 : ZMod 440869801) ^ 984084 := by rw [pow_add]
          _ = 160818527 := by rw [factor_3_19]; decide
      have factor_3_21 : (13 : ZMod 440869801) ^ 3936337 = 373437598 := by
        calc
          (13 : ZMod 440869801) ^ 3936337 = (13 : ZMod 440869801) ^ (1968168 + 1968168 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 1968168 * (13 : ZMod 440869801) ^ 1968168) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 373437598 := by rw [factor_3_20]; decide
      have factor_3_22 : (13 : ZMod 440869801) ^ 7872675 = 68108776 := by
        calc
          (13 : ZMod 440869801) ^ 7872675 = (13 : ZMod 440869801) ^ (3936337 + 3936337 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 3936337 * (13 : ZMod 440869801) ^ 3936337) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 68108776 := by rw [factor_3_21]; decide
      have factor_3_23 : (13 : ZMod 440869801) ^ 15745350 = 215154037 := by
        calc
          (13 : ZMod 440869801) ^ 15745350 = (13 : ZMod 440869801) ^ (7872675 + 7872675) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 7872675 * (13 : ZMod 440869801) ^ 7872675 := by rw [pow_add]
          _ = 215154037 := by rw [factor_3_22]; decide
      have factor_3_24 : (13 : ZMod 440869801) ^ 31490700 = 189825927 := by
        calc
          (13 : ZMod 440869801) ^ 31490700 = (13 : ZMod 440869801) ^ (15745350 + 15745350) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 15745350 * (13 : ZMod 440869801) ^ 15745350 := by rw [pow_add]
          _ = 189825927 := by rw [factor_3_23]; decide
      have factor_3_25 : (13 : ZMod 440869801) ^ 62981400 = 422218515 := by
        calc
          (13 : ZMod 440869801) ^ 62981400 = (13 : ZMod 440869801) ^ (31490700 + 31490700) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 31490700 * (13 : ZMod 440869801) ^ 31490700 := by rw [pow_add]
          _ = 422218515 := by rw [factor_3_24]; decide
      change (13 : ZMod 440869801) ^ 62981400 ≠ 1
      rw [factor_3_25]
      decide
    ·
      have factor_4_0 : (13 : ZMod 440869801) ^ 1 = 13 := by norm_num
      have factor_4_1 : (13 : ZMod 440869801) ^ 2 = 169 := by
        calc
          (13 : ZMod 440869801) ^ 2 = (13 : ZMod 440869801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 1 * (13 : ZMod 440869801) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_4_0]; decide
      have factor_4_2 : (13 : ZMod 440869801) ^ 5 = 371293 := by
        calc
          (13 : ZMod 440869801) ^ 5 = (13 : ZMod 440869801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 2 * (13 : ZMod 440869801) ^ 2) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 371293 := by rw [factor_4_1]; decide
      have factor_4_3 : (13 : ZMod 440869801) ^ 11 = 24652972 := by
        calc
          (13 : ZMod 440869801) ^ 11 = (13 : ZMod 440869801) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 5 * (13 : ZMod 440869801) ^ 5) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 24652972 := by rw [factor_4_2]; decide
      have factor_4_4 : (13 : ZMod 440869801) ^ 22 = 28607816 := by
        calc
          (13 : ZMod 440869801) ^ 22 = (13 : ZMod 440869801) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 11 * (13 : ZMod 440869801) ^ 11 := by rw [pow_add]
          _ = 28607816 := by rw [factor_4_3]; decide
      have factor_4_5 : (13 : ZMod 440869801) ^ 45 = 94786623 := by
        calc
          (13 : ZMod 440869801) ^ 45 = (13 : ZMod 440869801) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 22 * (13 : ZMod 440869801) ^ 22) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 94786623 := by rw [factor_4_4]; decide
      have factor_4_6 : (13 : ZMod 440869801) ^ 90 = 149503288 := by
        calc
          (13 : ZMod 440869801) ^ 90 = (13 : ZMod 440869801) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 45 * (13 : ZMod 440869801) ^ 45 := by rw [pow_add]
          _ = 149503288 := by rw [factor_4_5]; decide
      have factor_4_7 : (13 : ZMod 440869801) ^ 181 = 163461802 := by
        calc
          (13 : ZMod 440869801) ^ 181 = (13 : ZMod 440869801) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 90 * (13 : ZMod 440869801) ^ 90) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 163461802 := by rw [factor_4_6]; decide
      have factor_4_8 : (13 : ZMod 440869801) ^ 363 = 276775294 := by
        calc
          (13 : ZMod 440869801) ^ 363 = (13 : ZMod 440869801) ^ (181 + 181 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 181 * (13 : ZMod 440869801) ^ 181) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 276775294 := by rw [factor_4_7]; decide
      have factor_4_9 : (13 : ZMod 440869801) ^ 727 = 233762567 := by
        calc
          (13 : ZMod 440869801) ^ 727 = (13 : ZMod 440869801) ^ (363 + 363 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 363 * (13 : ZMod 440869801) ^ 363) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 233762567 := by rw [factor_4_8]; decide
      have factor_4_10 : (13 : ZMod 440869801) ^ 1454 = 141294872 := by
        calc
          (13 : ZMod 440869801) ^ 1454 = (13 : ZMod 440869801) ^ (727 + 727) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 727 * (13 : ZMod 440869801) ^ 727 := by rw [pow_add]
          _ = 141294872 := by rw [factor_4_9]; decide
      have factor_4_11 : (13 : ZMod 440869801) ^ 2909 = 235471754 := by
        calc
          (13 : ZMod 440869801) ^ 2909 = (13 : ZMod 440869801) ^ (1454 + 1454 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 1454 * (13 : ZMod 440869801) ^ 1454) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 235471754 := by rw [factor_4_10]; decide
      have factor_4_12 : (13 : ZMod 440869801) ^ 5818 = 162473147 := by
        calc
          (13 : ZMod 440869801) ^ 5818 = (13 : ZMod 440869801) ^ (2909 + 2909) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 2909 * (13 : ZMod 440869801) ^ 2909 := by rw [pow_add]
          _ = 162473147 := by rw [factor_4_11]; decide
      have factor_4_13 : (13 : ZMod 440869801) ^ 11636 = 205319002 := by
        calc
          (13 : ZMod 440869801) ^ 11636 = (13 : ZMod 440869801) ^ (5818 + 5818) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 5818 * (13 : ZMod 440869801) ^ 5818 := by rw [pow_add]
          _ = 205319002 := by rw [factor_4_12]; decide
      have factor_4_14 : (13 : ZMod 440869801) ^ 23272 = 244610781 := by
        calc
          (13 : ZMod 440869801) ^ 23272 = (13 : ZMod 440869801) ^ (11636 + 11636) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 11636 * (13 : ZMod 440869801) ^ 11636 := by rw [pow_add]
          _ = 244610781 := by rw [factor_4_13]; decide
      have factor_4_15 : (13 : ZMod 440869801) ^ 46544 = 89062503 := by
        calc
          (13 : ZMod 440869801) ^ 46544 = (13 : ZMod 440869801) ^ (23272 + 23272) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 23272 * (13 : ZMod 440869801) ^ 23272 := by rw [pow_add]
          _ = 89062503 := by rw [factor_4_14]; decide
      have factor_4_16 : (13 : ZMod 440869801) ^ 93089 = 194298918 := by
        calc
          (13 : ZMod 440869801) ^ 93089 = (13 : ZMod 440869801) ^ (46544 + 46544 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 46544 * (13 : ZMod 440869801) ^ 46544) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 194298918 := by rw [factor_4_15]; decide
      have factor_4_17 : (13 : ZMod 440869801) ^ 186178 = 70046043 := by
        calc
          (13 : ZMod 440869801) ^ 186178 = (13 : ZMod 440869801) ^ (93089 + 93089) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 93089 * (13 : ZMod 440869801) ^ 93089 := by rw [pow_add]
          _ = 70046043 := by rw [factor_4_16]; decide
      have factor_4_18 : (13 : ZMod 440869801) ^ 372356 = 188972431 := by
        calc
          (13 : ZMod 440869801) ^ 372356 = (13 : ZMod 440869801) ^ (186178 + 186178) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 186178 * (13 : ZMod 440869801) ^ 186178 := by rw [pow_add]
          _ = 188972431 := by rw [factor_4_17]; decide
      have factor_4_19 : (13 : ZMod 440869801) ^ 744712 = 149156476 := by
        calc
          (13 : ZMod 440869801) ^ 744712 = (13 : ZMod 440869801) ^ (372356 + 372356) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 372356 * (13 : ZMod 440869801) ^ 372356 := by rw [pow_add]
          _ = 149156476 := by rw [factor_4_18]; decide
      have factor_4_20 : (13 : ZMod 440869801) ^ 1489425 = 277876263 := by
        calc
          (13 : ZMod 440869801) ^ 1489425 = (13 : ZMod 440869801) ^ (744712 + 744712 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 744712 * (13 : ZMod 440869801) ^ 744712) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 277876263 := by rw [factor_4_19]; decide
      have factor_4_21 : (13 : ZMod 440869801) ^ 2978850 = 305803065 := by
        calc
          (13 : ZMod 440869801) ^ 2978850 = (13 : ZMod 440869801) ^ (1489425 + 1489425) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 1489425 * (13 : ZMod 440869801) ^ 1489425 := by rw [pow_add]
          _ = 305803065 := by rw [factor_4_20]; decide
      have factor_4_22 : (13 : ZMod 440869801) ^ 5957700 = 102317280 := by
        calc
          (13 : ZMod 440869801) ^ 5957700 = (13 : ZMod 440869801) ^ (2978850 + 2978850) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 2978850 * (13 : ZMod 440869801) ^ 2978850 := by rw [pow_add]
          _ = 102317280 := by rw [factor_4_21]; decide
      have factor_4_23 : (13 : ZMod 440869801) ^ 11915400 = 267741356 := by
        calc
          (13 : ZMod 440869801) ^ 11915400 = (13 : ZMod 440869801) ^ (5957700 + 5957700) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 5957700 * (13 : ZMod 440869801) ^ 5957700 := by rw [pow_add]
          _ = 267741356 := by rw [factor_4_22]; decide
      change (13 : ZMod 440869801) ^ 11915400 ≠ 1
      rw [factor_4_23]
      decide
    ·
      have factor_5_0 : (13 : ZMod 440869801) ^ 1 = 13 := by norm_num
      have factor_5_1 : (13 : ZMod 440869801) ^ 2 = 169 := by
        calc
          (13 : ZMod 440869801) ^ 2 = (13 : ZMod 440869801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 1 * (13 : ZMod 440869801) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_5_0]; decide
      have factor_5_2 : (13 : ZMod 440869801) ^ 4 = 28561 := by
        calc
          (13 : ZMod 440869801) ^ 4 = (13 : ZMod 440869801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 2 * (13 : ZMod 440869801) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_5_1]; decide
      have factor_5_3 : (13 : ZMod 440869801) ^ 9 = 23624149 := by
        calc
          (13 : ZMod 440869801) ^ 9 = (13 : ZMod 440869801) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 4 * (13 : ZMod 440869801) ^ 4) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 23624149 := by rw [factor_5_2]; decide
      have factor_5_4 : (13 : ZMod 440869801) ^ 18 = 248799694 := by
        calc
          (13 : ZMod 440869801) ^ 18 = (13 : ZMod 440869801) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 9 * (13 : ZMod 440869801) ^ 9 := by rw [pow_add]
          _ = 248799694 := by rw [factor_5_3]; decide
      have factor_5_5 : (13 : ZMod 440869801) ^ 37 = 319454863 := by
        calc
          (13 : ZMod 440869801) ^ 37 = (13 : ZMod 440869801) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 18 * (13 : ZMod 440869801) ^ 18) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 319454863 := by rw [factor_5_4]; decide
      have factor_5_6 : (13 : ZMod 440869801) ^ 75 = 140121178 := by
        calc
          (13 : ZMod 440869801) ^ 75 = (13 : ZMod 440869801) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 37 * (13 : ZMod 440869801) ^ 37) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 140121178 := by rw [factor_5_5]; decide
      have factor_5_7 : (13 : ZMod 440869801) ^ 151 = 261997756 := by
        calc
          (13 : ZMod 440869801) ^ 151 = (13 : ZMod 440869801) ^ (75 + 75 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 75 * (13 : ZMod 440869801) ^ 75) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 261997756 := by rw [factor_5_6]; decide
      have factor_5_8 : (13 : ZMod 440869801) ^ 303 = 301908375 := by
        calc
          (13 : ZMod 440869801) ^ 303 = (13 : ZMod 440869801) ^ (151 + 151 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 151 * (13 : ZMod 440869801) ^ 151) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 301908375 := by rw [factor_5_7]; decide
      have factor_5_9 : (13 : ZMod 440869801) ^ 607 = 145435062 := by
        calc
          (13 : ZMod 440869801) ^ 607 = (13 : ZMod 440869801) ^ (303 + 303 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 303 * (13 : ZMod 440869801) ^ 303) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 145435062 := by rw [factor_5_8]; decide
      have factor_5_10 : (13 : ZMod 440869801) ^ 1214 = 316502419 := by
        calc
          (13 : ZMod 440869801) ^ 1214 = (13 : ZMod 440869801) ^ (607 + 607) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 607 * (13 : ZMod 440869801) ^ 607 := by rw [pow_add]
          _ = 316502419 := by rw [factor_5_9]; decide
      have factor_5_11 : (13 : ZMod 440869801) ^ 2428 = 182155847 := by
        calc
          (13 : ZMod 440869801) ^ 2428 = (13 : ZMod 440869801) ^ (1214 + 1214) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 1214 * (13 : ZMod 440869801) ^ 1214 := by rw [pow_add]
          _ = 182155847 := by rw [factor_5_10]; decide
      have factor_5_12 : (13 : ZMod 440869801) ^ 4856 = 375159588 := by
        calc
          (13 : ZMod 440869801) ^ 4856 = (13 : ZMod 440869801) ^ (2428 + 2428) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 2428 * (13 : ZMod 440869801) ^ 2428 := by rw [pow_add]
          _ = 375159588 := by rw [factor_5_11]; decide
      have factor_5_13 : (13 : ZMod 440869801) ^ 9712 = 434580076 := by
        calc
          (13 : ZMod 440869801) ^ 9712 = (13 : ZMod 440869801) ^ (4856 + 4856) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 4856 * (13 : ZMod 440869801) ^ 4856 := by rw [pow_add]
          _ = 434580076 := by rw [factor_5_12]; decide
      have factor_5_14 : (13 : ZMod 440869801) ^ 19425 = 37652794 := by
        calc
          (13 : ZMod 440869801) ^ 19425 = (13 : ZMod 440869801) ^ (9712 + 9712 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = ((13 : ZMod 440869801) ^ 9712 * (13 : ZMod 440869801) ^ 9712) * (13 : ZMod 440869801) := by rw [pow_succ, pow_add]
          _ = 37652794 := by rw [factor_5_13]; decide
      have factor_5_15 : (13 : ZMod 440869801) ^ 38850 = 102133273 := by
        calc
          (13 : ZMod 440869801) ^ 38850 = (13 : ZMod 440869801) ^ (19425 + 19425) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 19425 * (13 : ZMod 440869801) ^ 19425 := by rw [pow_add]
          _ = 102133273 := by rw [factor_5_14]; decide
      have factor_5_16 : (13 : ZMod 440869801) ^ 77700 = 236694417 := by
        calc
          (13 : ZMod 440869801) ^ 77700 = (13 : ZMod 440869801) ^ (38850 + 38850) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 38850 * (13 : ZMod 440869801) ^ 38850 := by rw [pow_add]
          _ = 236694417 := by rw [factor_5_15]; decide
      have factor_5_17 : (13 : ZMod 440869801) ^ 155400 = 222598463 := by
        calc
          (13 : ZMod 440869801) ^ 155400 = (13 : ZMod 440869801) ^ (77700 + 77700) :=
            congrArg (fun n : ℕ => (13 : ZMod 440869801) ^ n) (by norm_num)
          _ = (13 : ZMod 440869801) ^ 77700 * (13 : ZMod 440869801) ^ 77700 := by rw [pow_add]
          _ = 222598463 := by rw [factor_5_16]; decide
      change (13 : ZMod 440869801) ^ 155400 ≠ 1
      rw [factor_5_17]
      decide

#print axioms prime_lucas_440869801

end TotientTailPeriodKiller
end Erdos249257
