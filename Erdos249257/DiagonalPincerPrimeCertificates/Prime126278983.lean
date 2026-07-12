import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=27 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_126278983 : Nat.Prime 126278983 := by
  apply lucas_primality 126278983 (3 : ZMod 126278983)
  ·
      have fermat_0 : (3 : ZMod 126278983) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 126278983) ^ 3 = 27 := by
        calc
          (3 : ZMod 126278983) ^ 3 = (3 : ZMod 126278983) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 1 * (3 : ZMod 126278983) ^ 1) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 126278983) ^ 7 = 2187 := by
        calc
          (3 : ZMod 126278983) ^ 7 = (3 : ZMod 126278983) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 3 * (3 : ZMod 126278983) ^ 3) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 126278983) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 126278983) ^ 15 = (3 : ZMod 126278983) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 7 * (3 : ZMod 126278983) ^ 7) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 126278983) ^ 30 = 69378231 := by
        calc
          (3 : ZMod 126278983) ^ 30 = (3 : ZMod 126278983) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 15 * (3 : ZMod 126278983) ^ 15 := by rw [pow_add]
          _ = 69378231 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 126278983) ^ 60 = 67699363 := by
        calc
          (3 : ZMod 126278983) ^ 60 = (3 : ZMod 126278983) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 30 * (3 : ZMod 126278983) ^ 30 := by rw [pow_add]
          _ = 67699363 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 126278983) ^ 120 = 119999376 := by
        calc
          (3 : ZMod 126278983) ^ 120 = (3 : ZMod 126278983) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 60 * (3 : ZMod 126278983) ^ 60 := by rw [pow_add]
          _ = 119999376 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 126278983) ^ 240 = 73495073 := by
        calc
          (3 : ZMod 126278983) ^ 240 = (3 : ZMod 126278983) ^ (120 + 120) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 120 * (3 : ZMod 126278983) ^ 120 := by rw [pow_add]
          _ = 73495073 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 126278983) ^ 481 = 27115663 := by
        calc
          (3 : ZMod 126278983) ^ 481 = (3 : ZMod 126278983) ^ (240 + 240 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 240 * (3 : ZMod 126278983) ^ 240) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 27115663 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 126278983) ^ 963 = 35631122 := by
        calc
          (3 : ZMod 126278983) ^ 963 = (3 : ZMod 126278983) ^ (481 + 481 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 481 * (3 : ZMod 126278983) ^ 481) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 35631122 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 126278983) ^ 1926 = 34758566 := by
        calc
          (3 : ZMod 126278983) ^ 1926 = (3 : ZMod 126278983) ^ (963 + 963) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 963 * (3 : ZMod 126278983) ^ 963 := by rw [pow_add]
          _ = 34758566 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 126278983) ^ 3853 = 91537989 := by
        calc
          (3 : ZMod 126278983) ^ 3853 = (3 : ZMod 126278983) ^ (1926 + 1926 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 1926 * (3 : ZMod 126278983) ^ 1926) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 91537989 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 126278983) ^ 7707 = 84866808 := by
        calc
          (3 : ZMod 126278983) ^ 7707 = (3 : ZMod 126278983) ^ (3853 + 3853 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 3853 * (3 : ZMod 126278983) ^ 3853) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 84866808 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 126278983) ^ 15414 = 14973038 := by
        calc
          (3 : ZMod 126278983) ^ 15414 = (3 : ZMod 126278983) ^ (7707 + 7707) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 7707 * (3 : ZMod 126278983) ^ 7707 := by rw [pow_add]
          _ = 14973038 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 126278983) ^ 30829 = 99260168 := by
        calc
          (3 : ZMod 126278983) ^ 30829 = (3 : ZMod 126278983) ^ (15414 + 15414 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 15414 * (3 : ZMod 126278983) ^ 15414) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 99260168 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 126278983) ^ 61659 = 14024689 := by
        calc
          (3 : ZMod 126278983) ^ 61659 = (3 : ZMod 126278983) ^ (30829 + 30829 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 30829 * (3 : ZMod 126278983) ^ 30829) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 14024689 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 126278983) ^ 123319 = 30551661 := by
        calc
          (3 : ZMod 126278983) ^ 123319 = (3 : ZMod 126278983) ^ (61659 + 61659 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 61659 * (3 : ZMod 126278983) ^ 61659) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 30551661 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 126278983) ^ 246638 = 6558155 := by
        calc
          (3 : ZMod 126278983) ^ 246638 = (3 : ZMod 126278983) ^ (123319 + 123319) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 123319 * (3 : ZMod 126278983) ^ 123319 := by rw [pow_add]
          _ = 6558155 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 126278983) ^ 493277 = 114552165 := by
        calc
          (3 : ZMod 126278983) ^ 493277 = (3 : ZMod 126278983) ^ (246638 + 246638 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 246638 * (3 : ZMod 126278983) ^ 246638) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 114552165 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 126278983) ^ 986554 = 69081175 := by
        calc
          (3 : ZMod 126278983) ^ 986554 = (3 : ZMod 126278983) ^ (493277 + 493277) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 493277 * (3 : ZMod 126278983) ^ 493277 := by rw [pow_add]
          _ = 69081175 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 126278983) ^ 1973109 = 88714739 := by
        calc
          (3 : ZMod 126278983) ^ 1973109 = (3 : ZMod 126278983) ^ (986554 + 986554 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 986554 * (3 : ZMod 126278983) ^ 986554) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 88714739 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 126278983) ^ 3946218 = 6619718 := by
        calc
          (3 : ZMod 126278983) ^ 3946218 = (3 : ZMod 126278983) ^ (1973109 + 1973109) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 1973109 * (3 : ZMod 126278983) ^ 1973109 := by rw [pow_add]
          _ = 6619718 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 126278983) ^ 7892436 = 91392762 := by
        calc
          (3 : ZMod 126278983) ^ 7892436 = (3 : ZMod 126278983) ^ (3946218 + 3946218) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 3946218 * (3 : ZMod 126278983) ^ 3946218 := by rw [pow_add]
          _ = 91392762 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 126278983) ^ 15784872 = 116556999 := by
        calc
          (3 : ZMod 126278983) ^ 15784872 = (3 : ZMod 126278983) ^ (7892436 + 7892436) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 7892436 * (3 : ZMod 126278983) ^ 7892436 := by rw [pow_add]
          _ = 116556999 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 126278983) ^ 31569745 = 49333112 := by
        calc
          (3 : ZMod 126278983) ^ 31569745 = (3 : ZMod 126278983) ^ (15784872 + 15784872 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 15784872 * (3 : ZMod 126278983) ^ 15784872) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 49333112 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 126278983) ^ 63139491 = 126278982 := by
        calc
          (3 : ZMod 126278983) ^ 63139491 = (3 : ZMod 126278983) ^ (31569745 + 31569745 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 31569745 * (3 : ZMod 126278983) ^ 31569745) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 126278982 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 126278983) ^ 126278982 = 1 := by
        calc
          (3 : ZMod 126278983) ^ 126278982 = (3 : ZMod 126278983) ^ (63139491 + 63139491) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 63139491 * (3 : ZMod 126278983) ^ 63139491 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7015499, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7015499, 1)] : List FactorBlock).map factorBlockValue).prod = 126278983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 126278983) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 126278983) ^ 3 = 27 := by
        calc
          (3 : ZMod 126278983) ^ 3 = (3 : ZMod 126278983) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 1 * (3 : ZMod 126278983) ^ 1) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 126278983) ^ 7 = 2187 := by
        calc
          (3 : ZMod 126278983) ^ 7 = (3 : ZMod 126278983) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 3 * (3 : ZMod 126278983) ^ 3) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 126278983) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 126278983) ^ 15 = (3 : ZMod 126278983) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 7 * (3 : ZMod 126278983) ^ 7) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 126278983) ^ 30 = 69378231 := by
        calc
          (3 : ZMod 126278983) ^ 30 = (3 : ZMod 126278983) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 15 * (3 : ZMod 126278983) ^ 15 := by rw [pow_add]
          _ = 69378231 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 126278983) ^ 60 = 67699363 := by
        calc
          (3 : ZMod 126278983) ^ 60 = (3 : ZMod 126278983) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 30 * (3 : ZMod 126278983) ^ 30 := by rw [pow_add]
          _ = 67699363 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 126278983) ^ 120 = 119999376 := by
        calc
          (3 : ZMod 126278983) ^ 120 = (3 : ZMod 126278983) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 60 * (3 : ZMod 126278983) ^ 60 := by rw [pow_add]
          _ = 119999376 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 126278983) ^ 240 = 73495073 := by
        calc
          (3 : ZMod 126278983) ^ 240 = (3 : ZMod 126278983) ^ (120 + 120) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 120 * (3 : ZMod 126278983) ^ 120 := by rw [pow_add]
          _ = 73495073 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 126278983) ^ 481 = 27115663 := by
        calc
          (3 : ZMod 126278983) ^ 481 = (3 : ZMod 126278983) ^ (240 + 240 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 240 * (3 : ZMod 126278983) ^ 240) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 27115663 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 126278983) ^ 963 = 35631122 := by
        calc
          (3 : ZMod 126278983) ^ 963 = (3 : ZMod 126278983) ^ (481 + 481 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 481 * (3 : ZMod 126278983) ^ 481) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 35631122 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 126278983) ^ 1926 = 34758566 := by
        calc
          (3 : ZMod 126278983) ^ 1926 = (3 : ZMod 126278983) ^ (963 + 963) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 963 * (3 : ZMod 126278983) ^ 963 := by rw [pow_add]
          _ = 34758566 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 126278983) ^ 3853 = 91537989 := by
        calc
          (3 : ZMod 126278983) ^ 3853 = (3 : ZMod 126278983) ^ (1926 + 1926 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 1926 * (3 : ZMod 126278983) ^ 1926) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 91537989 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 126278983) ^ 7707 = 84866808 := by
        calc
          (3 : ZMod 126278983) ^ 7707 = (3 : ZMod 126278983) ^ (3853 + 3853 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 3853 * (3 : ZMod 126278983) ^ 3853) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 84866808 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 126278983) ^ 15414 = 14973038 := by
        calc
          (3 : ZMod 126278983) ^ 15414 = (3 : ZMod 126278983) ^ (7707 + 7707) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 7707 * (3 : ZMod 126278983) ^ 7707 := by rw [pow_add]
          _ = 14973038 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 126278983) ^ 30829 = 99260168 := by
        calc
          (3 : ZMod 126278983) ^ 30829 = (3 : ZMod 126278983) ^ (15414 + 15414 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 15414 * (3 : ZMod 126278983) ^ 15414) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 99260168 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 126278983) ^ 61659 = 14024689 := by
        calc
          (3 : ZMod 126278983) ^ 61659 = (3 : ZMod 126278983) ^ (30829 + 30829 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 30829 * (3 : ZMod 126278983) ^ 30829) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 14024689 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 126278983) ^ 123319 = 30551661 := by
        calc
          (3 : ZMod 126278983) ^ 123319 = (3 : ZMod 126278983) ^ (61659 + 61659 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 61659 * (3 : ZMod 126278983) ^ 61659) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 30551661 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 126278983) ^ 246638 = 6558155 := by
        calc
          (3 : ZMod 126278983) ^ 246638 = (3 : ZMod 126278983) ^ (123319 + 123319) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 123319 * (3 : ZMod 126278983) ^ 123319 := by rw [pow_add]
          _ = 6558155 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 126278983) ^ 493277 = 114552165 := by
        calc
          (3 : ZMod 126278983) ^ 493277 = (3 : ZMod 126278983) ^ (246638 + 246638 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 246638 * (3 : ZMod 126278983) ^ 246638) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 114552165 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 126278983) ^ 986554 = 69081175 := by
        calc
          (3 : ZMod 126278983) ^ 986554 = (3 : ZMod 126278983) ^ (493277 + 493277) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 493277 * (3 : ZMod 126278983) ^ 493277 := by rw [pow_add]
          _ = 69081175 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 126278983) ^ 1973109 = 88714739 := by
        calc
          (3 : ZMod 126278983) ^ 1973109 = (3 : ZMod 126278983) ^ (986554 + 986554 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 986554 * (3 : ZMod 126278983) ^ 986554) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 88714739 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 126278983) ^ 3946218 = 6619718 := by
        calc
          (3 : ZMod 126278983) ^ 3946218 = (3 : ZMod 126278983) ^ (1973109 + 1973109) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 1973109 * (3 : ZMod 126278983) ^ 1973109 := by rw [pow_add]
          _ = 6619718 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 126278983) ^ 7892436 = 91392762 := by
        calc
          (3 : ZMod 126278983) ^ 7892436 = (3 : ZMod 126278983) ^ (3946218 + 3946218) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 3946218 * (3 : ZMod 126278983) ^ 3946218 := by rw [pow_add]
          _ = 91392762 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 126278983) ^ 15784872 = 116556999 := by
        calc
          (3 : ZMod 126278983) ^ 15784872 = (3 : ZMod 126278983) ^ (7892436 + 7892436) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 7892436 * (3 : ZMod 126278983) ^ 7892436 := by rw [pow_add]
          _ = 116556999 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 126278983) ^ 31569745 = 49333112 := by
        calc
          (3 : ZMod 126278983) ^ 31569745 = (3 : ZMod 126278983) ^ (15784872 + 15784872 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 15784872 * (3 : ZMod 126278983) ^ 15784872) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 49333112 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 126278983) ^ 63139491 = 126278982 := by
        calc
          (3 : ZMod 126278983) ^ 63139491 = (3 : ZMod 126278983) ^ (31569745 + 31569745 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 31569745 * (3 : ZMod 126278983) ^ 31569745) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 126278982 := by rw [factor_0_24]; decide
      change (3 : ZMod 126278983) ^ 63139491 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (3 : ZMod 126278983) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 126278983) ^ 2 = 9 := by
        calc
          (3 : ZMod 126278983) ^ 2 = (3 : ZMod 126278983) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 1 * (3 : ZMod 126278983) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 126278983) ^ 5 = 243 := by
        calc
          (3 : ZMod 126278983) ^ 5 = (3 : ZMod 126278983) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 2 * (3 : ZMod 126278983) ^ 2) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 126278983) ^ 10 = 59049 := by
        calc
          (3 : ZMod 126278983) ^ 10 = (3 : ZMod 126278983) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 5 * (3 : ZMod 126278983) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 126278983) ^ 20 = 77251860 := by
        calc
          (3 : ZMod 126278983) ^ 20 = (3 : ZMod 126278983) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 10 * (3 : ZMod 126278983) ^ 10 := by rw [pow_add]
          _ = 77251860 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 126278983) ^ 40 = 98674816 := by
        calc
          (3 : ZMod 126278983) ^ 40 = (3 : ZMod 126278983) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 20 * (3 : ZMod 126278983) ^ 20 := by rw [pow_add]
          _ = 98674816 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 126278983) ^ 80 = 48403932 := by
        calc
          (3 : ZMod 126278983) ^ 80 = (3 : ZMod 126278983) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 40 * (3 : ZMod 126278983) ^ 40 := by rw [pow_add]
          _ = 48403932 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 126278983) ^ 160 = 34079286 := by
        calc
          (3 : ZMod 126278983) ^ 160 = (3 : ZMod 126278983) ^ (80 + 80) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 80 * (3 : ZMod 126278983) ^ 80 := by rw [pow_add]
          _ = 34079286 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 126278983) ^ 321 = 107295383 := by
        calc
          (3 : ZMod 126278983) ^ 321 = (3 : ZMod 126278983) ^ (160 + 160 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 160 * (3 : ZMod 126278983) ^ 160) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 107295383 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 126278983) ^ 642 = 86810872 := by
        calc
          (3 : ZMod 126278983) ^ 642 = (3 : ZMod 126278983) ^ (321 + 321) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 321 * (3 : ZMod 126278983) ^ 321 := by rw [pow_add]
          _ = 86810872 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 126278983) ^ 1284 = 90891150 := by
        calc
          (3 : ZMod 126278983) ^ 1284 = (3 : ZMod 126278983) ^ (642 + 642) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 642 * (3 : ZMod 126278983) ^ 642 := by rw [pow_add]
          _ = 90891150 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 126278983) ^ 2569 = 78193638 := by
        calc
          (3 : ZMod 126278983) ^ 2569 = (3 : ZMod 126278983) ^ (1284 + 1284 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 1284 * (3 : ZMod 126278983) ^ 1284) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 78193638 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 126278983) ^ 5138 = 23898360 := by
        calc
          (3 : ZMod 126278983) ^ 5138 = (3 : ZMod 126278983) ^ (2569 + 2569) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 2569 * (3 : ZMod 126278983) ^ 2569 := by rw [pow_add]
          _ = 23898360 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 126278983) ^ 10276 = 57072792 := by
        calc
          (3 : ZMod 126278983) ^ 10276 = (3 : ZMod 126278983) ^ (5138 + 5138) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 5138 * (3 : ZMod 126278983) ^ 5138 := by rw [pow_add]
          _ = 57072792 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 126278983) ^ 20553 = 68813428 := by
        calc
          (3 : ZMod 126278983) ^ 20553 = (3 : ZMod 126278983) ^ (10276 + 10276 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 10276 * (3 : ZMod 126278983) ^ 10276) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 68813428 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 126278983) ^ 41106 = 23049758 := by
        calc
          (3 : ZMod 126278983) ^ 41106 = (3 : ZMod 126278983) ^ (20553 + 20553) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 20553 * (3 : ZMod 126278983) ^ 20553 := by rw [pow_add]
          _ = 23049758 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 126278983) ^ 82212 = 51704358 := by
        calc
          (3 : ZMod 126278983) ^ 82212 = (3 : ZMod 126278983) ^ (41106 + 41106) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 41106 * (3 : ZMod 126278983) ^ 41106 := by rw [pow_add]
          _ = 51704358 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 126278983) ^ 164425 = 5718374 := by
        calc
          (3 : ZMod 126278983) ^ 164425 = (3 : ZMod 126278983) ^ (82212 + 82212 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 82212 * (3 : ZMod 126278983) ^ 82212) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 5718374 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 126278983) ^ 328851 = 80784010 := by
        calc
          (3 : ZMod 126278983) ^ 328851 = (3 : ZMod 126278983) ^ (164425 + 164425 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 164425 * (3 : ZMod 126278983) ^ 164425) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 80784010 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 126278983) ^ 657703 = 54355504 := by
        calc
          (3 : ZMod 126278983) ^ 657703 = (3 : ZMod 126278983) ^ (328851 + 328851 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 328851 * (3 : ZMod 126278983) ^ 328851) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 54355504 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 126278983) ^ 1315406 = 115172157 := by
        calc
          (3 : ZMod 126278983) ^ 1315406 = (3 : ZMod 126278983) ^ (657703 + 657703) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 657703 * (3 : ZMod 126278983) ^ 657703 := by rw [pow_add]
          _ = 115172157 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 126278983) ^ 2630812 = 24138525 := by
        calc
          (3 : ZMod 126278983) ^ 2630812 = (3 : ZMod 126278983) ^ (1315406 + 1315406) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 1315406 * (3 : ZMod 126278983) ^ 1315406 := by rw [pow_add]
          _ = 24138525 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 126278983) ^ 5261624 = 113950920 := by
        calc
          (3 : ZMod 126278983) ^ 5261624 = (3 : ZMod 126278983) ^ (2630812 + 2630812) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 2630812 * (3 : ZMod 126278983) ^ 2630812 := by rw [pow_add]
          _ = 113950920 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 126278983) ^ 10523248 = 87806047 := by
        calc
          (3 : ZMod 126278983) ^ 10523248 = (3 : ZMod 126278983) ^ (5261624 + 5261624) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 5261624 * (3 : ZMod 126278983) ^ 5261624 := by rw [pow_add]
          _ = 87806047 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 126278983) ^ 21046497 = 115418807 := by
        calc
          (3 : ZMod 126278983) ^ 21046497 = (3 : ZMod 126278983) ^ (10523248 + 10523248 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 10523248 * (3 : ZMod 126278983) ^ 10523248) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 115418807 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 126278983) ^ 42092994 = 115418806 := by
        calc
          (3 : ZMod 126278983) ^ 42092994 = (3 : ZMod 126278983) ^ (21046497 + 21046497) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 21046497 * (3 : ZMod 126278983) ^ 21046497 := by rw [pow_add]
          _ = 115418806 := by rw [factor_1_24]; decide
      change (3 : ZMod 126278983) ^ 42092994 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (3 : ZMod 126278983) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 126278983) ^ 2 = 9 := by
        calc
          (3 : ZMod 126278983) ^ 2 = (3 : ZMod 126278983) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 1 * (3 : ZMod 126278983) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 126278983) ^ 4 = 81 := by
        calc
          (3 : ZMod 126278983) ^ 4 = (3 : ZMod 126278983) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 2 * (3 : ZMod 126278983) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 126278983) ^ 9 = 19683 := by
        calc
          (3 : ZMod 126278983) ^ 9 = (3 : ZMod 126278983) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = ((3 : ZMod 126278983) ^ 4 * (3 : ZMod 126278983) ^ 4) * (3 : ZMod 126278983) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 126278983) ^ 18 = 8583540 := by
        calc
          (3 : ZMod 126278983) ^ 18 = (3 : ZMod 126278983) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 126278983) ^ n) (by norm_num)
          _ = (3 : ZMod 126278983) ^ 9 * (3 : ZMod 126278983) ^ 9 := by rw [pow_add]
          _ = 8583540 := by rw [factor_2_3]; decide
      change (3 : ZMod 126278983) ^ 18 ≠ 1
      rw [factor_2_4]
      decide

#print axioms prime_lucas_126278983

end TotientTailPeriodKiller
end Erdos249257
