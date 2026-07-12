import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_356495017 : Nat.Prime 356495017 := by
  apply lucas_primality 356495017 (5 : ZMod 356495017)
  ·
      have fermat_0 : (5 : ZMod 356495017) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 356495017) ^ 2 = 25 := by
        calc
          (5 : ZMod 356495017) ^ 2 = (5 : ZMod 356495017) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 1 * (5 : ZMod 356495017) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 356495017) ^ 5 = 3125 := by
        calc
          (5 : ZMod 356495017) ^ 5 = (5 : ZMod 356495017) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 2 * (5 : ZMod 356495017) ^ 2) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 356495017) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 356495017) ^ 10 = (5 : ZMod 356495017) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 5 * (5 : ZMod 356495017) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 356495017) ^ 21 = 118314435 := by
        calc
          (5 : ZMod 356495017) ^ 21 = (5 : ZMod 356495017) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 10 * (5 : ZMod 356495017) ^ 10) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 118314435 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 356495017) ^ 42 = 4754014 := by
        calc
          (5 : ZMod 356495017) ^ 42 = (5 : ZMod 356495017) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 21 * (5 : ZMod 356495017) ^ 21 := by rw [pow_add]
          _ = 4754014 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 356495017) ^ 84 = 291014464 := by
        calc
          (5 : ZMod 356495017) ^ 84 = (5 : ZMod 356495017) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 42 * (5 : ZMod 356495017) ^ 42 := by rw [pow_add]
          _ = 291014464 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 356495017) ^ 169 = 5726320 := by
        calc
          (5 : ZMod 356495017) ^ 169 = (5 : ZMod 356495017) ^ (84 + 84 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 84 * (5 : ZMod 356495017) ^ 84) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 5726320 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 356495017) ^ 339 = 219413632 := by
        calc
          (5 : ZMod 356495017) ^ 339 = (5 : ZMod 356495017) ^ (169 + 169 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 169 * (5 : ZMod 356495017) ^ 169) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 219413632 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 356495017) ^ 679 = 102952937 := by
        calc
          (5 : ZMod 356495017) ^ 679 = (5 : ZMod 356495017) ^ (339 + 339 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 339 * (5 : ZMod 356495017) ^ 339) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 102952937 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 356495017) ^ 1359 = 147725474 := by
        calc
          (5 : ZMod 356495017) ^ 1359 = (5 : ZMod 356495017) ^ (679 + 679 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 679 * (5 : ZMod 356495017) ^ 679) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 147725474 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 356495017) ^ 2719 = 56474772 := by
        calc
          (5 : ZMod 356495017) ^ 2719 = (5 : ZMod 356495017) ^ (1359 + 1359 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 1359 * (5 : ZMod 356495017) ^ 1359) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 56474772 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 356495017) ^ 5439 = 99008323 := by
        calc
          (5 : ZMod 356495017) ^ 5439 = (5 : ZMod 356495017) ^ (2719 + 2719 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 2719 * (5 : ZMod 356495017) ^ 2719) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 99008323 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 356495017) ^ 10879 = 82421723 := by
        calc
          (5 : ZMod 356495017) ^ 10879 = (5 : ZMod 356495017) ^ (5439 + 5439 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 5439 * (5 : ZMod 356495017) ^ 5439) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 82421723 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 356495017) ^ 21758 = 254433106 := by
        calc
          (5 : ZMod 356495017) ^ 21758 = (5 : ZMod 356495017) ^ (10879 + 10879) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 10879 * (5 : ZMod 356495017) ^ 10879 := by rw [pow_add]
          _ = 254433106 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 356495017) ^ 43517 = 31625543 := by
        calc
          (5 : ZMod 356495017) ^ 43517 = (5 : ZMod 356495017) ^ (21758 + 21758 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 21758 * (5 : ZMod 356495017) ^ 21758) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 31625543 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 356495017) ^ 87034 = 36745006 := by
        calc
          (5 : ZMod 356495017) ^ 87034 = (5 : ZMod 356495017) ^ (43517 + 43517) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 43517 * (5 : ZMod 356495017) ^ 43517 := by rw [pow_add]
          _ = 36745006 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 356495017) ^ 174069 = 177704701 := by
        calc
          (5 : ZMod 356495017) ^ 174069 = (5 : ZMod 356495017) ^ (87034 + 87034 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 87034 * (5 : ZMod 356495017) ^ 87034) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 177704701 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 356495017) ^ 348139 = 73376283 := by
        calc
          (5 : ZMod 356495017) ^ 348139 = (5 : ZMod 356495017) ^ (174069 + 174069 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 174069 * (5 : ZMod 356495017) ^ 174069) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 73376283 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 356495017) ^ 696279 = 231656034 := by
        calc
          (5 : ZMod 356495017) ^ 696279 = (5 : ZMod 356495017) ^ (348139 + 348139 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 348139 * (5 : ZMod 356495017) ^ 348139) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 231656034 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 356495017) ^ 1392558 = 226591069 := by
        calc
          (5 : ZMod 356495017) ^ 1392558 = (5 : ZMod 356495017) ^ (696279 + 696279) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 696279 * (5 : ZMod 356495017) ^ 696279 := by rw [pow_add]
          _ = 226591069 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 356495017) ^ 2785117 = 293001495 := by
        calc
          (5 : ZMod 356495017) ^ 2785117 = (5 : ZMod 356495017) ^ (1392558 + 1392558 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 1392558 * (5 : ZMod 356495017) ^ 1392558) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 293001495 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 356495017) ^ 5570234 = 227764831 := by
        calc
          (5 : ZMod 356495017) ^ 5570234 = (5 : ZMod 356495017) ^ (2785117 + 2785117) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 2785117 * (5 : ZMod 356495017) ^ 2785117 := by rw [pow_add]
          _ = 227764831 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 356495017) ^ 11140469 = 202563079 := by
        calc
          (5 : ZMod 356495017) ^ 11140469 = (5 : ZMod 356495017) ^ (5570234 + 5570234 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 5570234 * (5 : ZMod 356495017) ^ 5570234) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 202563079 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 356495017) ^ 22280938 = 250417233 := by
        calc
          (5 : ZMod 356495017) ^ 22280938 = (5 : ZMod 356495017) ^ (11140469 + 11140469) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 11140469 * (5 : ZMod 356495017) ^ 11140469 := by rw [pow_add]
          _ = 250417233 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 356495017) ^ 44561877 = 289427421 := by
        calc
          (5 : ZMod 356495017) ^ 44561877 = (5 : ZMod 356495017) ^ (22280938 + 22280938 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 22280938 * (5 : ZMod 356495017) ^ 22280938) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 289427421 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 356495017) ^ 89123754 = 103032362 := by
        calc
          (5 : ZMod 356495017) ^ 89123754 = (5 : ZMod 356495017) ^ (44561877 + 44561877) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 44561877 * (5 : ZMod 356495017) ^ 44561877 := by rw [pow_add]
          _ = 103032362 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 356495017) ^ 178247508 = 356495016 := by
        calc
          (5 : ZMod 356495017) ^ 178247508 = (5 : ZMod 356495017) ^ (89123754 + 89123754) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 89123754 * (5 : ZMod 356495017) ^ 89123754 := by rw [pow_add]
          _ = 356495016 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 356495017) ^ 356495016 = 1 := by
        calc
          (5 : ZMod 356495017) ^ 356495016 = (5 : ZMod 356495017) ^ (178247508 + 178247508) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 178247508 * (5 : ZMod 356495017) ^ 178247508 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (131, 1), (149, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (131, 1), (149, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod = 356495017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 356495017) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 356495017) ^ 2 = 25 := by
        calc
          (5 : ZMod 356495017) ^ 2 = (5 : ZMod 356495017) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 1 * (5 : ZMod 356495017) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 356495017) ^ 5 = 3125 := by
        calc
          (5 : ZMod 356495017) ^ 5 = (5 : ZMod 356495017) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 2 * (5 : ZMod 356495017) ^ 2) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 356495017) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 356495017) ^ 10 = (5 : ZMod 356495017) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 5 * (5 : ZMod 356495017) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 356495017) ^ 21 = 118314435 := by
        calc
          (5 : ZMod 356495017) ^ 21 = (5 : ZMod 356495017) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 10 * (5 : ZMod 356495017) ^ 10) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 118314435 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 356495017) ^ 42 = 4754014 := by
        calc
          (5 : ZMod 356495017) ^ 42 = (5 : ZMod 356495017) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 21 * (5 : ZMod 356495017) ^ 21 := by rw [pow_add]
          _ = 4754014 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 356495017) ^ 84 = 291014464 := by
        calc
          (5 : ZMod 356495017) ^ 84 = (5 : ZMod 356495017) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 42 * (5 : ZMod 356495017) ^ 42 := by rw [pow_add]
          _ = 291014464 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 356495017) ^ 169 = 5726320 := by
        calc
          (5 : ZMod 356495017) ^ 169 = (5 : ZMod 356495017) ^ (84 + 84 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 84 * (5 : ZMod 356495017) ^ 84) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 5726320 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 356495017) ^ 339 = 219413632 := by
        calc
          (5 : ZMod 356495017) ^ 339 = (5 : ZMod 356495017) ^ (169 + 169 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 169 * (5 : ZMod 356495017) ^ 169) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 219413632 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 356495017) ^ 679 = 102952937 := by
        calc
          (5 : ZMod 356495017) ^ 679 = (5 : ZMod 356495017) ^ (339 + 339 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 339 * (5 : ZMod 356495017) ^ 339) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 102952937 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 356495017) ^ 1359 = 147725474 := by
        calc
          (5 : ZMod 356495017) ^ 1359 = (5 : ZMod 356495017) ^ (679 + 679 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 679 * (5 : ZMod 356495017) ^ 679) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 147725474 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 356495017) ^ 2719 = 56474772 := by
        calc
          (5 : ZMod 356495017) ^ 2719 = (5 : ZMod 356495017) ^ (1359 + 1359 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 1359 * (5 : ZMod 356495017) ^ 1359) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 56474772 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 356495017) ^ 5439 = 99008323 := by
        calc
          (5 : ZMod 356495017) ^ 5439 = (5 : ZMod 356495017) ^ (2719 + 2719 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 2719 * (5 : ZMod 356495017) ^ 2719) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 99008323 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 356495017) ^ 10879 = 82421723 := by
        calc
          (5 : ZMod 356495017) ^ 10879 = (5 : ZMod 356495017) ^ (5439 + 5439 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 5439 * (5 : ZMod 356495017) ^ 5439) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 82421723 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 356495017) ^ 21758 = 254433106 := by
        calc
          (5 : ZMod 356495017) ^ 21758 = (5 : ZMod 356495017) ^ (10879 + 10879) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 10879 * (5 : ZMod 356495017) ^ 10879 := by rw [pow_add]
          _ = 254433106 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 356495017) ^ 43517 = 31625543 := by
        calc
          (5 : ZMod 356495017) ^ 43517 = (5 : ZMod 356495017) ^ (21758 + 21758 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 21758 * (5 : ZMod 356495017) ^ 21758) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 31625543 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 356495017) ^ 87034 = 36745006 := by
        calc
          (5 : ZMod 356495017) ^ 87034 = (5 : ZMod 356495017) ^ (43517 + 43517) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 43517 * (5 : ZMod 356495017) ^ 43517 := by rw [pow_add]
          _ = 36745006 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 356495017) ^ 174069 = 177704701 := by
        calc
          (5 : ZMod 356495017) ^ 174069 = (5 : ZMod 356495017) ^ (87034 + 87034 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 87034 * (5 : ZMod 356495017) ^ 87034) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 177704701 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 356495017) ^ 348139 = 73376283 := by
        calc
          (5 : ZMod 356495017) ^ 348139 = (5 : ZMod 356495017) ^ (174069 + 174069 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 174069 * (5 : ZMod 356495017) ^ 174069) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 73376283 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 356495017) ^ 696279 = 231656034 := by
        calc
          (5 : ZMod 356495017) ^ 696279 = (5 : ZMod 356495017) ^ (348139 + 348139 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 348139 * (5 : ZMod 356495017) ^ 348139) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 231656034 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 356495017) ^ 1392558 = 226591069 := by
        calc
          (5 : ZMod 356495017) ^ 1392558 = (5 : ZMod 356495017) ^ (696279 + 696279) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 696279 * (5 : ZMod 356495017) ^ 696279 := by rw [pow_add]
          _ = 226591069 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 356495017) ^ 2785117 = 293001495 := by
        calc
          (5 : ZMod 356495017) ^ 2785117 = (5 : ZMod 356495017) ^ (1392558 + 1392558 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 1392558 * (5 : ZMod 356495017) ^ 1392558) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 293001495 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 356495017) ^ 5570234 = 227764831 := by
        calc
          (5 : ZMod 356495017) ^ 5570234 = (5 : ZMod 356495017) ^ (2785117 + 2785117) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 2785117 * (5 : ZMod 356495017) ^ 2785117 := by rw [pow_add]
          _ = 227764831 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 356495017) ^ 11140469 = 202563079 := by
        calc
          (5 : ZMod 356495017) ^ 11140469 = (5 : ZMod 356495017) ^ (5570234 + 5570234 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 5570234 * (5 : ZMod 356495017) ^ 5570234) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 202563079 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 356495017) ^ 22280938 = 250417233 := by
        calc
          (5 : ZMod 356495017) ^ 22280938 = (5 : ZMod 356495017) ^ (11140469 + 11140469) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 11140469 * (5 : ZMod 356495017) ^ 11140469 := by rw [pow_add]
          _ = 250417233 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 356495017) ^ 44561877 = 289427421 := by
        calc
          (5 : ZMod 356495017) ^ 44561877 = (5 : ZMod 356495017) ^ (22280938 + 22280938 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 22280938 * (5 : ZMod 356495017) ^ 22280938) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 289427421 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 356495017) ^ 89123754 = 103032362 := by
        calc
          (5 : ZMod 356495017) ^ 89123754 = (5 : ZMod 356495017) ^ (44561877 + 44561877) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 44561877 * (5 : ZMod 356495017) ^ 44561877 := by rw [pow_add]
          _ = 103032362 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 356495017) ^ 178247508 = 356495016 := by
        calc
          (5 : ZMod 356495017) ^ 178247508 = (5 : ZMod 356495017) ^ (89123754 + 89123754) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 89123754 * (5 : ZMod 356495017) ^ 89123754 := by rw [pow_add]
          _ = 356495016 := by rw [factor_0_26]; decide
      change (5 : ZMod 356495017) ^ 178247508 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (5 : ZMod 356495017) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 356495017) ^ 3 = 125 := by
        calc
          (5 : ZMod 356495017) ^ 3 = (5 : ZMod 356495017) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 1 * (5 : ZMod 356495017) ^ 1) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 356495017) ^ 7 = 78125 := by
        calc
          (5 : ZMod 356495017) ^ 7 = (5 : ZMod 356495017) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 3 * (5 : ZMod 356495017) ^ 3) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 356495017) ^ 14 = 43100336 := by
        calc
          (5 : ZMod 356495017) ^ 14 = (5 : ZMod 356495017) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 7 * (5 : ZMod 356495017) ^ 7 := by rw [pow_add]
          _ = 43100336 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 356495017) ^ 28 = 112433599 := by
        calc
          (5 : ZMod 356495017) ^ 28 = (5 : ZMod 356495017) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 14 * (5 : ZMod 356495017) ^ 14 := by rw [pow_add]
          _ = 112433599 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 356495017) ^ 56 = 168282767 := by
        calc
          (5 : ZMod 356495017) ^ 56 = (5 : ZMod 356495017) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 28 * (5 : ZMod 356495017) ^ 28 := by rw [pow_add]
          _ = 168282767 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 356495017) ^ 113 = 4864950 := by
        calc
          (5 : ZMod 356495017) ^ 113 = (5 : ZMod 356495017) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 56 * (5 : ZMod 356495017) ^ 56) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 4864950 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 356495017) ^ 226 = 34323870 := by
        calc
          (5 : ZMod 356495017) ^ 226 = (5 : ZMod 356495017) ^ (113 + 113) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 113 * (5 : ZMod 356495017) ^ 113 := by rw [pow_add]
          _ = 34323870 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 356495017) ^ 453 = 17810478 := by
        calc
          (5 : ZMod 356495017) ^ 453 = (5 : ZMod 356495017) ^ (226 + 226 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 226 * (5 : ZMod 356495017) ^ 226) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 17810478 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 356495017) ^ 906 = 295511714 := by
        calc
          (5 : ZMod 356495017) ^ 906 = (5 : ZMod 356495017) ^ (453 + 453) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 453 * (5 : ZMod 356495017) ^ 453 := by rw [pow_add]
          _ = 295511714 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 356495017) ^ 1813 = 131232328 := by
        calc
          (5 : ZMod 356495017) ^ 1813 = (5 : ZMod 356495017) ^ (906 + 906 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 906 * (5 : ZMod 356495017) ^ 906) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 131232328 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 356495017) ^ 3626 = 75631295 := by
        calc
          (5 : ZMod 356495017) ^ 3626 = (5 : ZMod 356495017) ^ (1813 + 1813) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 1813 * (5 : ZMod 356495017) ^ 1813 := by rw [pow_add]
          _ = 75631295 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 356495017) ^ 7252 = 114930820 := by
        calc
          (5 : ZMod 356495017) ^ 7252 = (5 : ZMod 356495017) ^ (3626 + 3626) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 3626 * (5 : ZMod 356495017) ^ 3626 := by rw [pow_add]
          _ = 114930820 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 356495017) ^ 14505 = 117714778 := by
        calc
          (5 : ZMod 356495017) ^ 14505 = (5 : ZMod 356495017) ^ (7252 + 7252 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 7252 * (5 : ZMod 356495017) ^ 7252) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 117714778 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 356495017) ^ 29011 = 67552286 := by
        calc
          (5 : ZMod 356495017) ^ 29011 = (5 : ZMod 356495017) ^ (14505 + 14505 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 14505 * (5 : ZMod 356495017) ^ 14505) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 67552286 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 356495017) ^ 58023 = 79367228 := by
        calc
          (5 : ZMod 356495017) ^ 58023 = (5 : ZMod 356495017) ^ (29011 + 29011 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 29011 * (5 : ZMod 356495017) ^ 29011) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 79367228 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 356495017) ^ 116046 = 86974237 := by
        calc
          (5 : ZMod 356495017) ^ 116046 = (5 : ZMod 356495017) ^ (58023 + 58023) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 58023 * (5 : ZMod 356495017) ^ 58023 := by rw [pow_add]
          _ = 86974237 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 356495017) ^ 232093 = 64048894 := by
        calc
          (5 : ZMod 356495017) ^ 232093 = (5 : ZMod 356495017) ^ (116046 + 116046 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 116046 * (5 : ZMod 356495017) ^ 116046) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 64048894 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 356495017) ^ 464186 = 293515785 := by
        calc
          (5 : ZMod 356495017) ^ 464186 = (5 : ZMod 356495017) ^ (232093 + 232093) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 232093 * (5 : ZMod 356495017) ^ 232093 := by rw [pow_add]
          _ = 293515785 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 356495017) ^ 928372 = 140446872 := by
        calc
          (5 : ZMod 356495017) ^ 928372 = (5 : ZMod 356495017) ^ (464186 + 464186) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 464186 * (5 : ZMod 356495017) ^ 464186 := by rw [pow_add]
          _ = 140446872 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 356495017) ^ 1856744 = 32827709 := by
        calc
          (5 : ZMod 356495017) ^ 1856744 = (5 : ZMod 356495017) ^ (928372 + 928372) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 928372 * (5 : ZMod 356495017) ^ 928372 := by rw [pow_add]
          _ = 32827709 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 356495017) ^ 3713489 = 329669610 := by
        calc
          (5 : ZMod 356495017) ^ 3713489 = (5 : ZMod 356495017) ^ (1856744 + 1856744 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 1856744 * (5 : ZMod 356495017) ^ 1856744) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 329669610 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 356495017) ^ 7426979 = 72711631 := by
        calc
          (5 : ZMod 356495017) ^ 7426979 = (5 : ZMod 356495017) ^ (3713489 + 3713489 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 3713489 * (5 : ZMod 356495017) ^ 3713489) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 72711631 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 356495017) ^ 14853959 = 215042623 := by
        calc
          (5 : ZMod 356495017) ^ 14853959 = (5 : ZMod 356495017) ^ (7426979 + 7426979 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 7426979 * (5 : ZMod 356495017) ^ 7426979) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 215042623 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 356495017) ^ 29707918 = 341647555 := by
        calc
          (5 : ZMod 356495017) ^ 29707918 = (5 : ZMod 356495017) ^ (14853959 + 14853959) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 14853959 * (5 : ZMod 356495017) ^ 14853959 := by rw [pow_add]
          _ = 341647555 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 356495017) ^ 59415836 = 234694103 := by
        calc
          (5 : ZMod 356495017) ^ 59415836 = (5 : ZMod 356495017) ^ (29707918 + 29707918) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 29707918 * (5 : ZMod 356495017) ^ 29707918 := by rw [pow_add]
          _ = 234694103 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 356495017) ^ 118831672 = 234694102 := by
        calc
          (5 : ZMod 356495017) ^ 118831672 = (5 : ZMod 356495017) ^ (59415836 + 59415836) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 59415836 * (5 : ZMod 356495017) ^ 59415836 := by rw [pow_add]
          _ = 234694102 := by rw [factor_1_25]; decide
      change (5 : ZMod 356495017) ^ 118831672 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (5 : ZMod 356495017) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 356495017) ^ 2 = 25 := by
        calc
          (5 : ZMod 356495017) ^ 2 = (5 : ZMod 356495017) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 1 * (5 : ZMod 356495017) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 356495017) ^ 5 = 3125 := by
        calc
          (5 : ZMod 356495017) ^ 5 = (5 : ZMod 356495017) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 2 * (5 : ZMod 356495017) ^ 2) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 356495017) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 356495017) ^ 10 = (5 : ZMod 356495017) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 5 * (5 : ZMod 356495017) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 356495017) ^ 20 = 23662887 := by
        calc
          (5 : ZMod 356495017) ^ 20 = (5 : ZMod 356495017) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 10 * (5 : ZMod 356495017) ^ 10 := by rw [pow_add]
          _ = 23662887 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 356495017) ^ 41 = 214847813 := by
        calc
          (5 : ZMod 356495017) ^ 41 = (5 : ZMod 356495017) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 20 * (5 : ZMod 356495017) ^ 20) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 214847813 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 356495017) ^ 83 = 272099903 := by
        calc
          (5 : ZMod 356495017) ^ 83 = (5 : ZMod 356495017) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 41 * (5 : ZMod 356495017) ^ 41) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 272099903 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 356495017) ^ 166 = 114124216 := by
        calc
          (5 : ZMod 356495017) ^ 166 = (5 : ZMod 356495017) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 83 * (5 : ZMod 356495017) ^ 83 := by rw [pow_add]
          _ = 114124216 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 356495017) ^ 332 = 137599618 := by
        calc
          (5 : ZMod 356495017) ^ 332 = (5 : ZMod 356495017) ^ (166 + 166) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 166 * (5 : ZMod 356495017) ^ 166 := by rw [pow_add]
          _ = 137599618 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 356495017) ^ 664 = 249231183 := by
        calc
          (5 : ZMod 356495017) ^ 664 = (5 : ZMod 356495017) ^ (332 + 332) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 332 * (5 : ZMod 356495017) ^ 332 := by rw [pow_add]
          _ = 249231183 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 356495017) ^ 1328 = 280356097 := by
        calc
          (5 : ZMod 356495017) ^ 1328 = (5 : ZMod 356495017) ^ (664 + 664) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 664 * (5 : ZMod 356495017) ^ 664 := by rw [pow_add]
          _ = 280356097 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 356495017) ^ 2657 = 235001557 := by
        calc
          (5 : ZMod 356495017) ^ 2657 = (5 : ZMod 356495017) ^ (1328 + 1328 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 1328 * (5 : ZMod 356495017) ^ 1328) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 235001557 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 356495017) ^ 5315 = 222356672 := by
        calc
          (5 : ZMod 356495017) ^ 5315 = (5 : ZMod 356495017) ^ (2657 + 2657 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 2657 * (5 : ZMod 356495017) ^ 2657) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 222356672 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 356495017) ^ 10630 = 315916268 := by
        calc
          (5 : ZMod 356495017) ^ 10630 = (5 : ZMod 356495017) ^ (5315 + 5315) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 5315 * (5 : ZMod 356495017) ^ 5315 := by rw [pow_add]
          _ = 315916268 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 356495017) ^ 21260 = 72662749 := by
        calc
          (5 : ZMod 356495017) ^ 21260 = (5 : ZMod 356495017) ^ (10630 + 10630) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 10630 * (5 : ZMod 356495017) ^ 10630 := by rw [pow_add]
          _ = 72662749 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 356495017) ^ 42520 = 295533246 := by
        calc
          (5 : ZMod 356495017) ^ 42520 = (5 : ZMod 356495017) ^ (21260 + 21260) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 21260 * (5 : ZMod 356495017) ^ 21260 := by rw [pow_add]
          _ = 295533246 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 356495017) ^ 85041 = 166556547 := by
        calc
          (5 : ZMod 356495017) ^ 85041 = (5 : ZMod 356495017) ^ (42520 + 42520 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 42520 * (5 : ZMod 356495017) ^ 42520) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 166556547 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 356495017) ^ 170083 = 66645048 := by
        calc
          (5 : ZMod 356495017) ^ 170083 = (5 : ZMod 356495017) ^ (85041 + 85041 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 85041 * (5 : ZMod 356495017) ^ 85041) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 66645048 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 356495017) ^ 340167 = 305463679 := by
        calc
          (5 : ZMod 356495017) ^ 340167 = (5 : ZMod 356495017) ^ (170083 + 170083 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 170083 * (5 : ZMod 356495017) ^ 170083) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 305463679 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 356495017) ^ 680334 = 289400193 := by
        calc
          (5 : ZMod 356495017) ^ 680334 = (5 : ZMod 356495017) ^ (340167 + 340167) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 340167 * (5 : ZMod 356495017) ^ 340167 := by rw [pow_add]
          _ = 289400193 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 356495017) ^ 1360668 = 72964923 := by
        calc
          (5 : ZMod 356495017) ^ 1360668 = (5 : ZMod 356495017) ^ (680334 + 680334) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 680334 * (5 : ZMod 356495017) ^ 680334 := by rw [pow_add]
          _ = 72964923 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 356495017) ^ 2721336 = 159783728 := by
        calc
          (5 : ZMod 356495017) ^ 2721336 = (5 : ZMod 356495017) ^ (1360668 + 1360668) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 1360668 * (5 : ZMod 356495017) ^ 1360668 := by rw [pow_add]
          _ = 159783728 := by rw [factor_2_20]; decide
      change (5 : ZMod 356495017) ^ 2721336 ≠ 1
      rw [factor_2_21]
      decide
    ·
      have factor_3_0 : (5 : ZMod 356495017) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 356495017) ^ 2 = 25 := by
        calc
          (5 : ZMod 356495017) ^ 2 = (5 : ZMod 356495017) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 1 * (5 : ZMod 356495017) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 356495017) ^ 4 = 625 := by
        calc
          (5 : ZMod 356495017) ^ 4 = (5 : ZMod 356495017) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 2 * (5 : ZMod 356495017) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 356495017) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 356495017) ^ 9 = (5 : ZMod 356495017) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 4 * (5 : ZMod 356495017) ^ 4) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 356495017) ^ 18 = 200583725 := by
        calc
          (5 : ZMod 356495017) ^ 18 = (5 : ZMod 356495017) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 9 * (5 : ZMod 356495017) ^ 9 := by rw [pow_add]
          _ = 200583725 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 356495017) ^ 36 = 258000026 := by
        calc
          (5 : ZMod 356495017) ^ 36 = (5 : ZMod 356495017) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 18 * (5 : ZMod 356495017) ^ 18 := by rw [pow_add]
          _ = 258000026 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 356495017) ^ 73 = 19853905 := by
        calc
          (5 : ZMod 356495017) ^ 73 = (5 : ZMod 356495017) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 36 * (5 : ZMod 356495017) ^ 36) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 19853905 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 356495017) ^ 146 = 290462091 := by
        calc
          (5 : ZMod 356495017) ^ 146 = (5 : ZMod 356495017) ^ (73 + 73) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 73 * (5 : ZMod 356495017) ^ 73 := by rw [pow_add]
          _ = 290462091 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 356495017) ^ 292 = 80486773 := by
        calc
          (5 : ZMod 356495017) ^ 292 = (5 : ZMod 356495017) ^ (146 + 146) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 146 * (5 : ZMod 356495017) ^ 146 := by rw [pow_add]
          _ = 80486773 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 356495017) ^ 584 = 127534629 := by
        calc
          (5 : ZMod 356495017) ^ 584 = (5 : ZMod 356495017) ^ (292 + 292) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 292 * (5 : ZMod 356495017) ^ 292 := by rw [pow_add]
          _ = 127534629 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 356495017) ^ 1168 = 8492811 := by
        calc
          (5 : ZMod 356495017) ^ 1168 = (5 : ZMod 356495017) ^ (584 + 584) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 584 * (5 : ZMod 356495017) ^ 584 := by rw [pow_add]
          _ = 8492811 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 356495017) ^ 2336 = 340862213 := by
        calc
          (5 : ZMod 356495017) ^ 2336 = (5 : ZMod 356495017) ^ (1168 + 1168) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 1168 * (5 : ZMod 356495017) ^ 1168 := by rw [pow_add]
          _ = 340862213 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 356495017) ^ 4673 = 127747863 := by
        calc
          (5 : ZMod 356495017) ^ 4673 = (5 : ZMod 356495017) ^ (2336 + 2336 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 2336 * (5 : ZMod 356495017) ^ 2336) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 127747863 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 356495017) ^ 9346 = 265266141 := by
        calc
          (5 : ZMod 356495017) ^ 9346 = (5 : ZMod 356495017) ^ (4673 + 4673) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 4673 * (5 : ZMod 356495017) ^ 4673 := by rw [pow_add]
          _ = 265266141 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 356495017) ^ 18692 = 103992566 := by
        calc
          (5 : ZMod 356495017) ^ 18692 = (5 : ZMod 356495017) ^ (9346 + 9346) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 9346 * (5 : ZMod 356495017) ^ 9346 := by rw [pow_add]
          _ = 103992566 := by rw [factor_3_13]; decide
      have factor_3_15 : (5 : ZMod 356495017) ^ 37384 = 264545907 := by
        calc
          (5 : ZMod 356495017) ^ 37384 = (5 : ZMod 356495017) ^ (18692 + 18692) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 18692 * (5 : ZMod 356495017) ^ 18692 := by rw [pow_add]
          _ = 264545907 := by rw [factor_3_14]; decide
      have factor_3_16 : (5 : ZMod 356495017) ^ 74768 = 154659964 := by
        calc
          (5 : ZMod 356495017) ^ 74768 = (5 : ZMod 356495017) ^ (37384 + 37384) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 37384 * (5 : ZMod 356495017) ^ 37384 := by rw [pow_add]
          _ = 154659964 := by rw [factor_3_15]; decide
      have factor_3_17 : (5 : ZMod 356495017) ^ 149536 = 18749285 := by
        calc
          (5 : ZMod 356495017) ^ 149536 = (5 : ZMod 356495017) ^ (74768 + 74768) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 74768 * (5 : ZMod 356495017) ^ 74768 := by rw [pow_add]
          _ = 18749285 := by rw [factor_3_16]; decide
      have factor_3_18 : (5 : ZMod 356495017) ^ 299073 = 78953594 := by
        calc
          (5 : ZMod 356495017) ^ 299073 = (5 : ZMod 356495017) ^ (149536 + 149536 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 149536 * (5 : ZMod 356495017) ^ 149536) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 78953594 := by rw [factor_3_17]; decide
      have factor_3_19 : (5 : ZMod 356495017) ^ 598146 = 277224938 := by
        calc
          (5 : ZMod 356495017) ^ 598146 = (5 : ZMod 356495017) ^ (299073 + 299073) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 299073 * (5 : ZMod 356495017) ^ 299073 := by rw [pow_add]
          _ = 277224938 := by rw [factor_3_18]; decide
      have factor_3_20 : (5 : ZMod 356495017) ^ 1196292 = 267316421 := by
        calc
          (5 : ZMod 356495017) ^ 1196292 = (5 : ZMod 356495017) ^ (598146 + 598146) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 598146 * (5 : ZMod 356495017) ^ 598146 := by rw [pow_add]
          _ = 267316421 := by rw [factor_3_19]; decide
      have factor_3_21 : (5 : ZMod 356495017) ^ 2392584 = 311623977 := by
        calc
          (5 : ZMod 356495017) ^ 2392584 = (5 : ZMod 356495017) ^ (1196292 + 1196292) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 1196292 * (5 : ZMod 356495017) ^ 1196292 := by rw [pow_add]
          _ = 311623977 := by rw [factor_3_20]; decide
      change (5 : ZMod 356495017) ^ 2392584 ≠ 1
      rw [factor_3_21]
      decide
    ·
      have factor_4_0 : (5 : ZMod 356495017) ^ 1 = 5 := by norm_num
      have factor_4_1 : (5 : ZMod 356495017) ^ 3 = 125 := by
        calc
          (5 : ZMod 356495017) ^ 3 = (5 : ZMod 356495017) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 1 * (5 : ZMod 356495017) ^ 1) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_4_0]; decide
      have factor_4_2 : (5 : ZMod 356495017) ^ 7 = 78125 := by
        calc
          (5 : ZMod 356495017) ^ 7 = (5 : ZMod 356495017) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 3 * (5 : ZMod 356495017) ^ 3) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_4_1]; decide
      have factor_4_3 : (5 : ZMod 356495017) ^ 14 = 43100336 := by
        calc
          (5 : ZMod 356495017) ^ 14 = (5 : ZMod 356495017) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 7 * (5 : ZMod 356495017) ^ 7 := by rw [pow_add]
          _ = 43100336 := by rw [factor_4_2]; decide
      have factor_4_4 : (5 : ZMod 356495017) ^ 28 = 112433599 := by
        calc
          (5 : ZMod 356495017) ^ 28 = (5 : ZMod 356495017) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 14 * (5 : ZMod 356495017) ^ 14 := by rw [pow_add]
          _ = 112433599 := by rw [factor_4_3]; decide
      have factor_4_5 : (5 : ZMod 356495017) ^ 57 = 128423801 := by
        calc
          (5 : ZMod 356495017) ^ 57 = (5 : ZMod 356495017) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 28 * (5 : ZMod 356495017) ^ 28) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 128423801 := by rw [factor_4_4]; decide
      have factor_4_6 : (5 : ZMod 356495017) ^ 114 = 24324750 := by
        calc
          (5 : ZMod 356495017) ^ 114 = (5 : ZMod 356495017) ^ (57 + 57) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 57 * (5 : ZMod 356495017) ^ 57 := by rw [pow_add]
          _ = 24324750 := by rw [factor_4_5]; decide
      have factor_4_7 : (5 : ZMod 356495017) ^ 228 = 145106716 := by
        calc
          (5 : ZMod 356495017) ^ 228 = (5 : ZMod 356495017) ^ (114 + 114) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 114 * (5 : ZMod 356495017) ^ 114 := by rw [pow_add]
          _ = 145106716 := by rw [factor_4_6]; decide
      have factor_4_8 : (5 : ZMod 356495017) ^ 457 = 80203223 := by
        calc
          (5 : ZMod 356495017) ^ 457 = (5 : ZMod 356495017) ^ (228 + 228 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 228 * (5 : ZMod 356495017) ^ 228) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 80203223 := by rw [factor_4_7]; decide
      have factor_4_9 : (5 : ZMod 356495017) ^ 914 = 107291599 := by
        calc
          (5 : ZMod 356495017) ^ 914 = (5 : ZMod 356495017) ^ (457 + 457) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 457 * (5 : ZMod 356495017) ^ 457 := by rw [pow_add]
          _ = 107291599 := by rw [factor_4_8]; decide
      have factor_4_10 : (5 : ZMod 356495017) ^ 1829 = 118621275 := by
        calc
          (5 : ZMod 356495017) ^ 1829 = (5 : ZMod 356495017) ^ (914 + 914 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 914 * (5 : ZMod 356495017) ^ 914) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 118621275 := by rw [factor_4_9]; decide
      have factor_4_11 : (5 : ZMod 356495017) ^ 3659 = 229057714 := by
        calc
          (5 : ZMod 356495017) ^ 3659 = (5 : ZMod 356495017) ^ (1829 + 1829 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 1829 * (5 : ZMod 356495017) ^ 1829) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 229057714 := by rw [factor_4_10]; decide
      have factor_4_12 : (5 : ZMod 356495017) ^ 7319 = 72376694 := by
        calc
          (5 : ZMod 356495017) ^ 7319 = (5 : ZMod 356495017) ^ (3659 + 3659 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 3659 * (5 : ZMod 356495017) ^ 3659) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 72376694 := by rw [factor_4_11]; decide
      have factor_4_13 : (5 : ZMod 356495017) ^ 14639 = 351711739 := by
        calc
          (5 : ZMod 356495017) ^ 14639 = (5 : ZMod 356495017) ^ (7319 + 7319 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 7319 * (5 : ZMod 356495017) ^ 7319) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 351711739 := by rw [factor_4_12]; decide
      have factor_4_14 : (5 : ZMod 356495017) ^ 29278 = 254729241 := by
        calc
          (5 : ZMod 356495017) ^ 29278 = (5 : ZMod 356495017) ^ (14639 + 14639) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 14639 * (5 : ZMod 356495017) ^ 14639 := by rw [pow_add]
          _ = 254729241 := by rw [factor_4_13]; decide
      have factor_4_15 : (5 : ZMod 356495017) ^ 58557 = 92153729 := by
        calc
          (5 : ZMod 356495017) ^ 58557 = (5 : ZMod 356495017) ^ (29278 + 29278 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = ((5 : ZMod 356495017) ^ 29278 * (5 : ZMod 356495017) ^ 29278) * (5 : ZMod 356495017) := by rw [pow_succ, pow_add]
          _ = 92153729 := by rw [factor_4_14]; decide
      have factor_4_16 : (5 : ZMod 356495017) ^ 117114 = 265026915 := by
        calc
          (5 : ZMod 356495017) ^ 117114 = (5 : ZMod 356495017) ^ (58557 + 58557) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 58557 * (5 : ZMod 356495017) ^ 58557 := by rw [pow_add]
          _ = 265026915 := by rw [factor_4_15]; decide
      have factor_4_17 : (5 : ZMod 356495017) ^ 234228 = 38662411 := by
        calc
          (5 : ZMod 356495017) ^ 234228 = (5 : ZMod 356495017) ^ (117114 + 117114) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 117114 * (5 : ZMod 356495017) ^ 117114 := by rw [pow_add]
          _ = 38662411 := by rw [factor_4_16]; decide
      have factor_4_18 : (5 : ZMod 356495017) ^ 468456 = 200527006 := by
        calc
          (5 : ZMod 356495017) ^ 468456 = (5 : ZMod 356495017) ^ (234228 + 234228) :=
            congrArg (fun n : ℕ => (5 : ZMod 356495017) ^ n) (by norm_num)
          _ = (5 : ZMod 356495017) ^ 234228 * (5 : ZMod 356495017) ^ 234228 := by rw [pow_add]
          _ = 200527006 := by rw [factor_4_17]; decide
      change (5 : ZMod 356495017) ^ 468456 ≠ 1
      rw [factor_4_18]
      decide

#print axioms prime_lucas_356495017

end TotientTailPeriodKiller
end Erdos249257
