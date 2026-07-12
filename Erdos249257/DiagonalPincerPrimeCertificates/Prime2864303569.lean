import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2864303569 : Nat.Prime 2864303569 := by
  apply lucas_primality 2864303569 (11 : ZMod 2864303569)
  ·
      have fermat_0 : (11 : ZMod 2864303569) ^ 1 = 11 := by norm_num
      have fermat_1 : (11 : ZMod 2864303569) ^ 2 = 121 := by
        calc
          (11 : ZMod 2864303569) ^ 2 = (11 : ZMod 2864303569) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 1 * (11 : ZMod 2864303569) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [fermat_0]; decide
      have fermat_2 : (11 : ZMod 2864303569) ^ 5 = 161051 := by
        calc
          (11 : ZMod 2864303569) ^ 5 = (11 : ZMod 2864303569) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 2 * (11 : ZMod 2864303569) ^ 2) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 161051 := by rw [fermat_1]; decide
      have fermat_3 : (11 : ZMod 2864303569) ^ 10 = 158692480 := by
        calc
          (11 : ZMod 2864303569) ^ 10 = (11 : ZMod 2864303569) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 5 * (11 : ZMod 2864303569) ^ 5 := by rw [pow_add]
          _ = 158692480 := by rw [fermat_2]; decide
      have fermat_4 : (11 : ZMod 2864303569) ^ 21 = 1869483199 := by
        calc
          (11 : ZMod 2864303569) ^ 21 = (11 : ZMod 2864303569) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 10 * (11 : ZMod 2864303569) ^ 10) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1869483199 := by rw [fermat_3]; decide
      have fermat_5 : (11 : ZMod 2864303569) ^ 42 = 1625783445 := by
        calc
          (11 : ZMod 2864303569) ^ 42 = (11 : ZMod 2864303569) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 21 * (11 : ZMod 2864303569) ^ 21 := by rw [pow_add]
          _ = 1625783445 := by rw [fermat_4]; decide
      have fermat_6 : (11 : ZMod 2864303569) ^ 85 = 514567392 := by
        calc
          (11 : ZMod 2864303569) ^ 85 = (11 : ZMod 2864303569) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 42 * (11 : ZMod 2864303569) ^ 42) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 514567392 := by rw [fermat_5]; decide
      have fermat_7 : (11 : ZMod 2864303569) ^ 170 = 1977413813 := by
        calc
          (11 : ZMod 2864303569) ^ 170 = (11 : ZMod 2864303569) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 85 * (11 : ZMod 2864303569) ^ 85 := by rw [pow_add]
          _ = 1977413813 := by rw [fermat_6]; decide
      have fermat_8 : (11 : ZMod 2864303569) ^ 341 = 2014406947 := by
        calc
          (11 : ZMod 2864303569) ^ 341 = (11 : ZMod 2864303569) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 170 * (11 : ZMod 2864303569) ^ 170) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2014406947 := by rw [fermat_7]; decide
      have fermat_9 : (11 : ZMod 2864303569) ^ 682 = 716165868 := by
        calc
          (11 : ZMod 2864303569) ^ 682 = (11 : ZMod 2864303569) ^ (341 + 341) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 341 * (11 : ZMod 2864303569) ^ 341 := by rw [pow_add]
          _ = 716165868 := by rw [fermat_8]; decide
      have fermat_10 : (11 : ZMod 2864303569) ^ 1365 = 1153675695 := by
        calc
          (11 : ZMod 2864303569) ^ 1365 = (11 : ZMod 2864303569) ^ (682 + 682 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 682 * (11 : ZMod 2864303569) ^ 682) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1153675695 := by rw [fermat_9]; decide
      have fermat_11 : (11 : ZMod 2864303569) ^ 2731 = 1462784971 := by
        calc
          (11 : ZMod 2864303569) ^ 2731 = (11 : ZMod 2864303569) ^ (1365 + 1365 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 1365 * (11 : ZMod 2864303569) ^ 1365) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1462784971 := by rw [fermat_10]; decide
      have fermat_12 : (11 : ZMod 2864303569) ^ 5463 = 2659677384 := by
        calc
          (11 : ZMod 2864303569) ^ 5463 = (11 : ZMod 2864303569) ^ (2731 + 2731 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 2731 * (11 : ZMod 2864303569) ^ 2731) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2659677384 := by rw [fermat_11]; decide
      have fermat_13 : (11 : ZMod 2864303569) ^ 10926 = 2306763483 := by
        calc
          (11 : ZMod 2864303569) ^ 10926 = (11 : ZMod 2864303569) ^ (5463 + 5463) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 5463 * (11 : ZMod 2864303569) ^ 5463 := by rw [pow_add]
          _ = 2306763483 := by rw [fermat_12]; decide
      have fermat_14 : (11 : ZMod 2864303569) ^ 21852 = 2384771574 := by
        calc
          (11 : ZMod 2864303569) ^ 21852 = (11 : ZMod 2864303569) ^ (10926 + 10926) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 10926 * (11 : ZMod 2864303569) ^ 10926 := by rw [pow_add]
          _ = 2384771574 := by rw [fermat_13]; decide
      have fermat_15 : (11 : ZMod 2864303569) ^ 43705 = 1677414298 := by
        calc
          (11 : ZMod 2864303569) ^ 43705 = (11 : ZMod 2864303569) ^ (21852 + 21852 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 21852 * (11 : ZMod 2864303569) ^ 21852) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1677414298 := by rw [fermat_14]; decide
      have fermat_16 : (11 : ZMod 2864303569) ^ 87411 = 2067910698 := by
        calc
          (11 : ZMod 2864303569) ^ 87411 = (11 : ZMod 2864303569) ^ (43705 + 43705 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 43705 * (11 : ZMod 2864303569) ^ 43705) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2067910698 := by rw [fermat_15]; decide
      have fermat_17 : (11 : ZMod 2864303569) ^ 174823 = 2426129184 := by
        calc
          (11 : ZMod 2864303569) ^ 174823 = (11 : ZMod 2864303569) ^ (87411 + 87411 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 87411 * (11 : ZMod 2864303569) ^ 87411) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2426129184 := by rw [fermat_16]; decide
      have fermat_18 : (11 : ZMod 2864303569) ^ 349646 = 2852917505 := by
        calc
          (11 : ZMod 2864303569) ^ 349646 = (11 : ZMod 2864303569) ^ (174823 + 174823) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 174823 * (11 : ZMod 2864303569) ^ 174823 := by rw [pow_add]
          _ = 2852917505 := by rw [fermat_17]; decide
      have fermat_19 : (11 : ZMod 2864303569) ^ 699292 = 1209575587 := by
        calc
          (11 : ZMod 2864303569) ^ 699292 = (11 : ZMod 2864303569) ^ (349646 + 349646) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 349646 * (11 : ZMod 2864303569) ^ 349646 := by rw [pow_add]
          _ = 1209575587 := by rw [fermat_18]; decide
      have fermat_20 : (11 : ZMod 2864303569) ^ 1398585 = 1514249640 := by
        calc
          (11 : ZMod 2864303569) ^ 1398585 = (11 : ZMod 2864303569) ^ (699292 + 699292 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 699292 * (11 : ZMod 2864303569) ^ 699292) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1514249640 := by rw [fermat_19]; decide
      have fermat_21 : (11 : ZMod 2864303569) ^ 2797171 = 1284518425 := by
        calc
          (11 : ZMod 2864303569) ^ 2797171 = (11 : ZMod 2864303569) ^ (1398585 + 1398585 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 1398585 * (11 : ZMod 2864303569) ^ 1398585) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1284518425 := by rw [fermat_20]; decide
      have fermat_22 : (11 : ZMod 2864303569) ^ 5594342 = 2321963869 := by
        calc
          (11 : ZMod 2864303569) ^ 5594342 = (11 : ZMod 2864303569) ^ (2797171 + 2797171) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 2797171 * (11 : ZMod 2864303569) ^ 2797171 := by rw [pow_add]
          _ = 2321963869 := by rw [fermat_21]; decide
      have fermat_23 : (11 : ZMod 2864303569) ^ 11188685 = 2840573602 := by
        calc
          (11 : ZMod 2864303569) ^ 11188685 = (11 : ZMod 2864303569) ^ (5594342 + 5594342 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 5594342 * (11 : ZMod 2864303569) ^ 5594342) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2840573602 := by rw [fermat_22]; decide
      have fermat_24 : (11 : ZMod 2864303569) ^ 22377371 = 2074462477 := by
        calc
          (11 : ZMod 2864303569) ^ 22377371 = (11 : ZMod 2864303569) ^ (11188685 + 11188685 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 11188685 * (11 : ZMod 2864303569) ^ 11188685) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2074462477 := by rw [fermat_23]; decide
      have fermat_25 : (11 : ZMod 2864303569) ^ 44754743 = 491378847 := by
        calc
          (11 : ZMod 2864303569) ^ 44754743 = (11 : ZMod 2864303569) ^ (22377371 + 22377371 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 22377371 * (11 : ZMod 2864303569) ^ 22377371) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 491378847 := by rw [fermat_24]; decide
      have fermat_26 : (11 : ZMod 2864303569) ^ 89509486 = 2324146518 := by
        calc
          (11 : ZMod 2864303569) ^ 89509486 = (11 : ZMod 2864303569) ^ (44754743 + 44754743) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 44754743 * (11 : ZMod 2864303569) ^ 44754743 := by rw [pow_add]
          _ = 2324146518 := by rw [fermat_25]; decide
      have fermat_27 : (11 : ZMod 2864303569) ^ 179018973 = 1986980099 := by
        calc
          (11 : ZMod 2864303569) ^ 179018973 = (11 : ZMod 2864303569) ^ (89509486 + 89509486 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 89509486 * (11 : ZMod 2864303569) ^ 89509486) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1986980099 := by rw [fermat_26]; decide
      have fermat_28 : (11 : ZMod 2864303569) ^ 358037946 = 2488947304 := by
        calc
          (11 : ZMod 2864303569) ^ 358037946 = (11 : ZMod 2864303569) ^ (179018973 + 179018973) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 179018973 * (11 : ZMod 2864303569) ^ 179018973 := by rw [pow_add]
          _ = 2488947304 := by rw [fermat_27]; decide
      have fermat_29 : (11 : ZMod 2864303569) ^ 716075892 = 32887879 := by
        calc
          (11 : ZMod 2864303569) ^ 716075892 = (11 : ZMod 2864303569) ^ (358037946 + 358037946) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 358037946 * (11 : ZMod 2864303569) ^ 358037946 := by rw [pow_add]
          _ = 32887879 := by rw [fermat_28]; decide
      have fermat_30 : (11 : ZMod 2864303569) ^ 1432151784 = 2864303568 := by
        calc
          (11 : ZMod 2864303569) ^ 1432151784 = (11 : ZMod 2864303569) ^ (716075892 + 716075892) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 716075892 * (11 : ZMod 2864303569) ^ 716075892 := by rw [pow_add]
          _ = 2864303568 := by rw [fermat_29]; decide
      have fermat_31 : (11 : ZMod 2864303569) ^ 2864303568 = 1 := by
        calc
          (11 : ZMod 2864303569) ^ 2864303568 = (11 : ZMod 2864303569) ^ (1432151784 + 1432151784) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 1432151784 * (11 : ZMod 2864303569) ^ 1432151784 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (7, 1), (251, 1), (11321, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (7, 1), (251, 1), (11321, 1)] : List FactorBlock).map factorBlockValue).prod = 2864303569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (11 : ZMod 2864303569) ^ 1 = 11 := by norm_num
      have factor_0_1 : (11 : ZMod 2864303569) ^ 2 = 121 := by
        calc
          (11 : ZMod 2864303569) ^ 2 = (11 : ZMod 2864303569) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 1 * (11 : ZMod 2864303569) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_0_0]; decide
      have factor_0_2 : (11 : ZMod 2864303569) ^ 5 = 161051 := by
        calc
          (11 : ZMod 2864303569) ^ 5 = (11 : ZMod 2864303569) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 2 * (11 : ZMod 2864303569) ^ 2) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 161051 := by rw [factor_0_1]; decide
      have factor_0_3 : (11 : ZMod 2864303569) ^ 10 = 158692480 := by
        calc
          (11 : ZMod 2864303569) ^ 10 = (11 : ZMod 2864303569) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 5 * (11 : ZMod 2864303569) ^ 5 := by rw [pow_add]
          _ = 158692480 := by rw [factor_0_2]; decide
      have factor_0_4 : (11 : ZMod 2864303569) ^ 21 = 1869483199 := by
        calc
          (11 : ZMod 2864303569) ^ 21 = (11 : ZMod 2864303569) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 10 * (11 : ZMod 2864303569) ^ 10) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1869483199 := by rw [factor_0_3]; decide
      have factor_0_5 : (11 : ZMod 2864303569) ^ 42 = 1625783445 := by
        calc
          (11 : ZMod 2864303569) ^ 42 = (11 : ZMod 2864303569) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 21 * (11 : ZMod 2864303569) ^ 21 := by rw [pow_add]
          _ = 1625783445 := by rw [factor_0_4]; decide
      have factor_0_6 : (11 : ZMod 2864303569) ^ 85 = 514567392 := by
        calc
          (11 : ZMod 2864303569) ^ 85 = (11 : ZMod 2864303569) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 42 * (11 : ZMod 2864303569) ^ 42) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 514567392 := by rw [factor_0_5]; decide
      have factor_0_7 : (11 : ZMod 2864303569) ^ 170 = 1977413813 := by
        calc
          (11 : ZMod 2864303569) ^ 170 = (11 : ZMod 2864303569) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 85 * (11 : ZMod 2864303569) ^ 85 := by rw [pow_add]
          _ = 1977413813 := by rw [factor_0_6]; decide
      have factor_0_8 : (11 : ZMod 2864303569) ^ 341 = 2014406947 := by
        calc
          (11 : ZMod 2864303569) ^ 341 = (11 : ZMod 2864303569) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 170 * (11 : ZMod 2864303569) ^ 170) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2014406947 := by rw [factor_0_7]; decide
      have factor_0_9 : (11 : ZMod 2864303569) ^ 682 = 716165868 := by
        calc
          (11 : ZMod 2864303569) ^ 682 = (11 : ZMod 2864303569) ^ (341 + 341) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 341 * (11 : ZMod 2864303569) ^ 341 := by rw [pow_add]
          _ = 716165868 := by rw [factor_0_8]; decide
      have factor_0_10 : (11 : ZMod 2864303569) ^ 1365 = 1153675695 := by
        calc
          (11 : ZMod 2864303569) ^ 1365 = (11 : ZMod 2864303569) ^ (682 + 682 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 682 * (11 : ZMod 2864303569) ^ 682) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1153675695 := by rw [factor_0_9]; decide
      have factor_0_11 : (11 : ZMod 2864303569) ^ 2731 = 1462784971 := by
        calc
          (11 : ZMod 2864303569) ^ 2731 = (11 : ZMod 2864303569) ^ (1365 + 1365 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 1365 * (11 : ZMod 2864303569) ^ 1365) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1462784971 := by rw [factor_0_10]; decide
      have factor_0_12 : (11 : ZMod 2864303569) ^ 5463 = 2659677384 := by
        calc
          (11 : ZMod 2864303569) ^ 5463 = (11 : ZMod 2864303569) ^ (2731 + 2731 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 2731 * (11 : ZMod 2864303569) ^ 2731) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2659677384 := by rw [factor_0_11]; decide
      have factor_0_13 : (11 : ZMod 2864303569) ^ 10926 = 2306763483 := by
        calc
          (11 : ZMod 2864303569) ^ 10926 = (11 : ZMod 2864303569) ^ (5463 + 5463) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 5463 * (11 : ZMod 2864303569) ^ 5463 := by rw [pow_add]
          _ = 2306763483 := by rw [factor_0_12]; decide
      have factor_0_14 : (11 : ZMod 2864303569) ^ 21852 = 2384771574 := by
        calc
          (11 : ZMod 2864303569) ^ 21852 = (11 : ZMod 2864303569) ^ (10926 + 10926) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 10926 * (11 : ZMod 2864303569) ^ 10926 := by rw [pow_add]
          _ = 2384771574 := by rw [factor_0_13]; decide
      have factor_0_15 : (11 : ZMod 2864303569) ^ 43705 = 1677414298 := by
        calc
          (11 : ZMod 2864303569) ^ 43705 = (11 : ZMod 2864303569) ^ (21852 + 21852 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 21852 * (11 : ZMod 2864303569) ^ 21852) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1677414298 := by rw [factor_0_14]; decide
      have factor_0_16 : (11 : ZMod 2864303569) ^ 87411 = 2067910698 := by
        calc
          (11 : ZMod 2864303569) ^ 87411 = (11 : ZMod 2864303569) ^ (43705 + 43705 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 43705 * (11 : ZMod 2864303569) ^ 43705) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2067910698 := by rw [factor_0_15]; decide
      have factor_0_17 : (11 : ZMod 2864303569) ^ 174823 = 2426129184 := by
        calc
          (11 : ZMod 2864303569) ^ 174823 = (11 : ZMod 2864303569) ^ (87411 + 87411 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 87411 * (11 : ZMod 2864303569) ^ 87411) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2426129184 := by rw [factor_0_16]; decide
      have factor_0_18 : (11 : ZMod 2864303569) ^ 349646 = 2852917505 := by
        calc
          (11 : ZMod 2864303569) ^ 349646 = (11 : ZMod 2864303569) ^ (174823 + 174823) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 174823 * (11 : ZMod 2864303569) ^ 174823 := by rw [pow_add]
          _ = 2852917505 := by rw [factor_0_17]; decide
      have factor_0_19 : (11 : ZMod 2864303569) ^ 699292 = 1209575587 := by
        calc
          (11 : ZMod 2864303569) ^ 699292 = (11 : ZMod 2864303569) ^ (349646 + 349646) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 349646 * (11 : ZMod 2864303569) ^ 349646 := by rw [pow_add]
          _ = 1209575587 := by rw [factor_0_18]; decide
      have factor_0_20 : (11 : ZMod 2864303569) ^ 1398585 = 1514249640 := by
        calc
          (11 : ZMod 2864303569) ^ 1398585 = (11 : ZMod 2864303569) ^ (699292 + 699292 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 699292 * (11 : ZMod 2864303569) ^ 699292) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1514249640 := by rw [factor_0_19]; decide
      have factor_0_21 : (11 : ZMod 2864303569) ^ 2797171 = 1284518425 := by
        calc
          (11 : ZMod 2864303569) ^ 2797171 = (11 : ZMod 2864303569) ^ (1398585 + 1398585 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 1398585 * (11 : ZMod 2864303569) ^ 1398585) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1284518425 := by rw [factor_0_20]; decide
      have factor_0_22 : (11 : ZMod 2864303569) ^ 5594342 = 2321963869 := by
        calc
          (11 : ZMod 2864303569) ^ 5594342 = (11 : ZMod 2864303569) ^ (2797171 + 2797171) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 2797171 * (11 : ZMod 2864303569) ^ 2797171 := by rw [pow_add]
          _ = 2321963869 := by rw [factor_0_21]; decide
      have factor_0_23 : (11 : ZMod 2864303569) ^ 11188685 = 2840573602 := by
        calc
          (11 : ZMod 2864303569) ^ 11188685 = (11 : ZMod 2864303569) ^ (5594342 + 5594342 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 5594342 * (11 : ZMod 2864303569) ^ 5594342) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2840573602 := by rw [factor_0_22]; decide
      have factor_0_24 : (11 : ZMod 2864303569) ^ 22377371 = 2074462477 := by
        calc
          (11 : ZMod 2864303569) ^ 22377371 = (11 : ZMod 2864303569) ^ (11188685 + 11188685 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 11188685 * (11 : ZMod 2864303569) ^ 11188685) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2074462477 := by rw [factor_0_23]; decide
      have factor_0_25 : (11 : ZMod 2864303569) ^ 44754743 = 491378847 := by
        calc
          (11 : ZMod 2864303569) ^ 44754743 = (11 : ZMod 2864303569) ^ (22377371 + 22377371 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 22377371 * (11 : ZMod 2864303569) ^ 22377371) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 491378847 := by rw [factor_0_24]; decide
      have factor_0_26 : (11 : ZMod 2864303569) ^ 89509486 = 2324146518 := by
        calc
          (11 : ZMod 2864303569) ^ 89509486 = (11 : ZMod 2864303569) ^ (44754743 + 44754743) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 44754743 * (11 : ZMod 2864303569) ^ 44754743 := by rw [pow_add]
          _ = 2324146518 := by rw [factor_0_25]; decide
      have factor_0_27 : (11 : ZMod 2864303569) ^ 179018973 = 1986980099 := by
        calc
          (11 : ZMod 2864303569) ^ 179018973 = (11 : ZMod 2864303569) ^ (89509486 + 89509486 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 89509486 * (11 : ZMod 2864303569) ^ 89509486) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1986980099 := by rw [factor_0_26]; decide
      have factor_0_28 : (11 : ZMod 2864303569) ^ 358037946 = 2488947304 := by
        calc
          (11 : ZMod 2864303569) ^ 358037946 = (11 : ZMod 2864303569) ^ (179018973 + 179018973) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 179018973 * (11 : ZMod 2864303569) ^ 179018973 := by rw [pow_add]
          _ = 2488947304 := by rw [factor_0_27]; decide
      have factor_0_29 : (11 : ZMod 2864303569) ^ 716075892 = 32887879 := by
        calc
          (11 : ZMod 2864303569) ^ 716075892 = (11 : ZMod 2864303569) ^ (358037946 + 358037946) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 358037946 * (11 : ZMod 2864303569) ^ 358037946 := by rw [pow_add]
          _ = 32887879 := by rw [factor_0_28]; decide
      have factor_0_30 : (11 : ZMod 2864303569) ^ 1432151784 = 2864303568 := by
        calc
          (11 : ZMod 2864303569) ^ 1432151784 = (11 : ZMod 2864303569) ^ (716075892 + 716075892) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 716075892 * (11 : ZMod 2864303569) ^ 716075892 := by rw [pow_add]
          _ = 2864303568 := by rw [factor_0_29]; decide
      change (11 : ZMod 2864303569) ^ 1432151784 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (11 : ZMod 2864303569) ^ 1 = 11 := by norm_num
      have factor_1_1 : (11 : ZMod 2864303569) ^ 3 = 1331 := by
        calc
          (11 : ZMod 2864303569) ^ 3 = (11 : ZMod 2864303569) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 1 * (11 : ZMod 2864303569) ^ 1) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1331 := by rw [factor_1_0]; decide
      have factor_1_2 : (11 : ZMod 2864303569) ^ 7 = 19487171 := by
        calc
          (11 : ZMod 2864303569) ^ 7 = (11 : ZMod 2864303569) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 3 * (11 : ZMod 2864303569) ^ 3) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 19487171 := by rw [factor_1_1]; decide
      have factor_1_3 : (11 : ZMod 2864303569) ^ 14 = 466405221 := by
        calc
          (11 : ZMod 2864303569) ^ 14 = (11 : ZMod 2864303569) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 7 * (11 : ZMod 2864303569) ^ 7 := by rw [pow_add]
          _ = 466405221 := by rw [factor_1_2]; decide
      have factor_1_4 : (11 : ZMod 2864303569) ^ 28 = 2037303910 := by
        calc
          (11 : ZMod 2864303569) ^ 28 = (11 : ZMod 2864303569) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 14 * (11 : ZMod 2864303569) ^ 14 := by rw [pow_add]
          _ = 2037303910 := by rw [factor_1_3]; decide
      have factor_1_5 : (11 : ZMod 2864303569) ^ 56 = 421019970 := by
        calc
          (11 : ZMod 2864303569) ^ 56 = (11 : ZMod 2864303569) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 28 * (11 : ZMod 2864303569) ^ 28 := by rw [pow_add]
          _ = 421019970 := by rw [factor_1_4]; decide
      have factor_1_6 : (11 : ZMod 2864303569) ^ 113 = 78366383 := by
        calc
          (11 : ZMod 2864303569) ^ 113 = (11 : ZMod 2864303569) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 56 * (11 : ZMod 2864303569) ^ 56) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 78366383 := by rw [factor_1_5]; decide
      have factor_1_7 : (11 : ZMod 2864303569) ^ 227 = 2614378515 := by
        calc
          (11 : ZMod 2864303569) ^ 227 = (11 : ZMod 2864303569) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 113 * (11 : ZMod 2864303569) ^ 113) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2614378515 := by rw [factor_1_6]; decide
      have factor_1_8 : (11 : ZMod 2864303569) ^ 455 = 1862210988 := by
        calc
          (11 : ZMod 2864303569) ^ 455 = (11 : ZMod 2864303569) ^ (227 + 227 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 227 * (11 : ZMod 2864303569) ^ 227) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1862210988 := by rw [factor_1_7]; decide
      have factor_1_9 : (11 : ZMod 2864303569) ^ 910 = 688115210 := by
        calc
          (11 : ZMod 2864303569) ^ 910 = (11 : ZMod 2864303569) ^ (455 + 455) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 455 * (11 : ZMod 2864303569) ^ 455 := by rw [pow_add]
          _ = 688115210 := by rw [factor_1_8]; decide
      have factor_1_10 : (11 : ZMod 2864303569) ^ 1821 = 1673055105 := by
        calc
          (11 : ZMod 2864303569) ^ 1821 = (11 : ZMod 2864303569) ^ (910 + 910 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 910 * (11 : ZMod 2864303569) ^ 910) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1673055105 := by rw [factor_1_9]; decide
      have factor_1_11 : (11 : ZMod 2864303569) ^ 3642 = 1188502181 := by
        calc
          (11 : ZMod 2864303569) ^ 3642 = (11 : ZMod 2864303569) ^ (1821 + 1821) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 1821 * (11 : ZMod 2864303569) ^ 1821 := by rw [pow_add]
          _ = 1188502181 := by rw [factor_1_10]; decide
      have factor_1_12 : (11 : ZMod 2864303569) ^ 7284 = 2444072670 := by
        calc
          (11 : ZMod 2864303569) ^ 7284 = (11 : ZMod 2864303569) ^ (3642 + 3642) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 3642 * (11 : ZMod 2864303569) ^ 3642 := by rw [pow_add]
          _ = 2444072670 := by rw [factor_1_11]; decide
      have factor_1_13 : (11 : ZMod 2864303569) ^ 14568 = 642220705 := by
        calc
          (11 : ZMod 2864303569) ^ 14568 = (11 : ZMod 2864303569) ^ (7284 + 7284) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 7284 * (11 : ZMod 2864303569) ^ 7284 := by rw [pow_add]
          _ = 642220705 := by rw [factor_1_12]; decide
      have factor_1_14 : (11 : ZMod 2864303569) ^ 29137 = 497981315 := by
        calc
          (11 : ZMod 2864303569) ^ 29137 = (11 : ZMod 2864303569) ^ (14568 + 14568 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 14568 * (11 : ZMod 2864303569) ^ 14568) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 497981315 := by rw [factor_1_13]; decide
      have factor_1_15 : (11 : ZMod 2864303569) ^ 58274 = 2122604125 := by
        calc
          (11 : ZMod 2864303569) ^ 58274 = (11 : ZMod 2864303569) ^ (29137 + 29137) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 29137 * (11 : ZMod 2864303569) ^ 29137 := by rw [pow_add]
          _ = 2122604125 := by rw [factor_1_14]; decide
      have factor_1_16 : (11 : ZMod 2864303569) ^ 116548 = 1968269068 := by
        calc
          (11 : ZMod 2864303569) ^ 116548 = (11 : ZMod 2864303569) ^ (58274 + 58274) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 58274 * (11 : ZMod 2864303569) ^ 58274 := by rw [pow_add]
          _ = 1968269068 := by rw [factor_1_15]; decide
      have factor_1_17 : (11 : ZMod 2864303569) ^ 233097 = 1686774546 := by
        calc
          (11 : ZMod 2864303569) ^ 233097 = (11 : ZMod 2864303569) ^ (116548 + 116548 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 116548 * (11 : ZMod 2864303569) ^ 116548) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1686774546 := by rw [factor_1_16]; decide
      have factor_1_18 : (11 : ZMod 2864303569) ^ 466195 = 632080646 := by
        calc
          (11 : ZMod 2864303569) ^ 466195 = (11 : ZMod 2864303569) ^ (233097 + 233097 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 233097 * (11 : ZMod 2864303569) ^ 233097) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 632080646 := by rw [factor_1_17]; decide
      have factor_1_19 : (11 : ZMod 2864303569) ^ 932390 = 470507523 := by
        calc
          (11 : ZMod 2864303569) ^ 932390 = (11 : ZMod 2864303569) ^ (466195 + 466195) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 466195 * (11 : ZMod 2864303569) ^ 466195 := by rw [pow_add]
          _ = 470507523 := by rw [factor_1_18]; decide
      have factor_1_20 : (11 : ZMod 2864303569) ^ 1864780 = 945135120 := by
        calc
          (11 : ZMod 2864303569) ^ 1864780 = (11 : ZMod 2864303569) ^ (932390 + 932390) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 932390 * (11 : ZMod 2864303569) ^ 932390 := by rw [pow_add]
          _ = 945135120 := by rw [factor_1_19]; decide
      have factor_1_21 : (11 : ZMod 2864303569) ^ 3729561 = 1945831943 := by
        calc
          (11 : ZMod 2864303569) ^ 3729561 = (11 : ZMod 2864303569) ^ (1864780 + 1864780 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 1864780 * (11 : ZMod 2864303569) ^ 1864780) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1945831943 := by rw [factor_1_20]; decide
      have factor_1_22 : (11 : ZMod 2864303569) ^ 7459123 = 832735826 := by
        calc
          (11 : ZMod 2864303569) ^ 7459123 = (11 : ZMod 2864303569) ^ (3729561 + 3729561 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 3729561 * (11 : ZMod 2864303569) ^ 3729561) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 832735826 := by rw [factor_1_21]; decide
      have factor_1_23 : (11 : ZMod 2864303569) ^ 14918247 = 2573374223 := by
        calc
          (11 : ZMod 2864303569) ^ 14918247 = (11 : ZMod 2864303569) ^ (7459123 + 7459123 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 7459123 * (11 : ZMod 2864303569) ^ 7459123) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2573374223 := by rw [factor_1_22]; decide
      have factor_1_24 : (11 : ZMod 2864303569) ^ 29836495 = 770037207 := by
        calc
          (11 : ZMod 2864303569) ^ 29836495 = (11 : ZMod 2864303569) ^ (14918247 + 14918247 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 14918247 * (11 : ZMod 2864303569) ^ 14918247) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 770037207 := by rw [factor_1_23]; decide
      have factor_1_25 : (11 : ZMod 2864303569) ^ 59672991 = 373456238 := by
        calc
          (11 : ZMod 2864303569) ^ 59672991 = (11 : ZMod 2864303569) ^ (29836495 + 29836495 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 29836495 * (11 : ZMod 2864303569) ^ 29836495) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 373456238 := by rw [factor_1_24]; decide
      have factor_1_26 : (11 : ZMod 2864303569) ^ 119345982 = 1520954685 := by
        calc
          (11 : ZMod 2864303569) ^ 119345982 = (11 : ZMod 2864303569) ^ (59672991 + 59672991) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 59672991 * (11 : ZMod 2864303569) ^ 59672991 := by rw [pow_add]
          _ = 1520954685 := by rw [factor_1_25]; decide
      have factor_1_27 : (11 : ZMod 2864303569) ^ 238691964 = 2528126881 := by
        calc
          (11 : ZMod 2864303569) ^ 238691964 = (11 : ZMod 2864303569) ^ (119345982 + 119345982) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 119345982 * (11 : ZMod 2864303569) ^ 119345982 := by rw [pow_add]
          _ = 2528126881 := by rw [factor_1_26]; decide
      have factor_1_28 : (11 : ZMod 2864303569) ^ 477383928 = 1931186024 := by
        calc
          (11 : ZMod 2864303569) ^ 477383928 = (11 : ZMod 2864303569) ^ (238691964 + 238691964) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 238691964 * (11 : ZMod 2864303569) ^ 238691964 := by rw [pow_add]
          _ = 1931186024 := by rw [factor_1_27]; decide
      have factor_1_29 : (11 : ZMod 2864303569) ^ 954767856 = 1931186023 := by
        calc
          (11 : ZMod 2864303569) ^ 954767856 = (11 : ZMod 2864303569) ^ (477383928 + 477383928) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 477383928 * (11 : ZMod 2864303569) ^ 477383928 := by rw [pow_add]
          _ = 1931186023 := by rw [factor_1_28]; decide
      change (11 : ZMod 2864303569) ^ 954767856 ≠ 1
      rw [factor_1_29]
      decide
    ·
      have factor_2_0 : (11 : ZMod 2864303569) ^ 1 = 11 := by norm_num
      have factor_2_1 : (11 : ZMod 2864303569) ^ 3 = 1331 := by
        calc
          (11 : ZMod 2864303569) ^ 3 = (11 : ZMod 2864303569) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 1 * (11 : ZMod 2864303569) ^ 1) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1331 := by rw [factor_2_0]; decide
      have factor_2_2 : (11 : ZMod 2864303569) ^ 6 = 1771561 := by
        calc
          (11 : ZMod 2864303569) ^ 6 = (11 : ZMod 2864303569) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 3 * (11 : ZMod 2864303569) ^ 3 := by rw [pow_add]
          _ = 1771561 := by rw [factor_2_1]; decide
      have factor_2_3 : (11 : ZMod 2864303569) ^ 12 = 2015968666 := by
        calc
          (11 : ZMod 2864303569) ^ 12 = (11 : ZMod 2864303569) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 6 * (11 : ZMod 2864303569) ^ 6 := by rw [pow_add]
          _ = 2015968666 := by rw [factor_2_2]; decide
      have factor_2_4 : (11 : ZMod 2864303569) ^ 24 = 2066639977 := by
        calc
          (11 : ZMod 2864303569) ^ 24 = (11 : ZMod 2864303569) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 12 * (11 : ZMod 2864303569) ^ 12 := by rw [pow_add]
          _ = 2066639977 := by rw [factor_2_3]; decide
      have factor_2_5 : (11 : ZMod 2864303569) ^ 48 = 2734835385 := by
        calc
          (11 : ZMod 2864303569) ^ 48 = (11 : ZMod 2864303569) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 24 * (11 : ZMod 2864303569) ^ 24 := by rw [pow_add]
          _ = 2734835385 := by rw [factor_2_4]; decide
      have factor_2_6 : (11 : ZMod 2864303569) ^ 97 = 2235615833 := by
        calc
          (11 : ZMod 2864303569) ^ 97 = (11 : ZMod 2864303569) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 48 * (11 : ZMod 2864303569) ^ 48) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2235615833 := by rw [factor_2_5]; decide
      have factor_2_7 : (11 : ZMod 2864303569) ^ 195 = 1686962963 := by
        calc
          (11 : ZMod 2864303569) ^ 195 = (11 : ZMod 2864303569) ^ (97 + 97 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 97 * (11 : ZMod 2864303569) ^ 97) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1686962963 := by rw [factor_2_6]; decide
      have factor_2_8 : (11 : ZMod 2864303569) ^ 390 = 916016565 := by
        calc
          (11 : ZMod 2864303569) ^ 390 = (11 : ZMod 2864303569) ^ (195 + 195) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 195 * (11 : ZMod 2864303569) ^ 195 := by rw [pow_add]
          _ = 916016565 := by rw [factor_2_7]; decide
      have factor_2_9 : (11 : ZMod 2864303569) ^ 780 = 2422536000 := by
        calc
          (11 : ZMod 2864303569) ^ 780 = (11 : ZMod 2864303569) ^ (390 + 390) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 390 * (11 : ZMod 2864303569) ^ 390 := by rw [pow_add]
          _ = 2422536000 := by rw [factor_2_8]; decide
      have factor_2_10 : (11 : ZMod 2864303569) ^ 1560 = 336675563 := by
        calc
          (11 : ZMod 2864303569) ^ 1560 = (11 : ZMod 2864303569) ^ (780 + 780) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 780 * (11 : ZMod 2864303569) ^ 780 := by rw [pow_add]
          _ = 336675563 := by rw [factor_2_9]; decide
      have factor_2_11 : (11 : ZMod 2864303569) ^ 3121 = 2617535101 := by
        calc
          (11 : ZMod 2864303569) ^ 3121 = (11 : ZMod 2864303569) ^ (1560 + 1560 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 1560 * (11 : ZMod 2864303569) ^ 1560) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2617535101 := by rw [factor_2_10]; decide
      have factor_2_12 : (11 : ZMod 2864303569) ^ 6243 = 757714802 := by
        calc
          (11 : ZMod 2864303569) ^ 6243 = (11 : ZMod 2864303569) ^ (3121 + 3121 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 3121 * (11 : ZMod 2864303569) ^ 3121) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 757714802 := by rw [factor_2_11]; decide
      have factor_2_13 : (11 : ZMod 2864303569) ^ 12487 = 24584739 := by
        calc
          (11 : ZMod 2864303569) ^ 12487 = (11 : ZMod 2864303569) ^ (6243 + 6243 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 6243 * (11 : ZMod 2864303569) ^ 6243) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 24584739 := by rw [factor_2_12]; decide
      have factor_2_14 : (11 : ZMod 2864303569) ^ 24974 = 1238389155 := by
        calc
          (11 : ZMod 2864303569) ^ 24974 = (11 : ZMod 2864303569) ^ (12487 + 12487) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 12487 * (11 : ZMod 2864303569) ^ 12487 := by rw [pow_add]
          _ = 1238389155 := by rw [factor_2_13]; decide
      have factor_2_15 : (11 : ZMod 2864303569) ^ 49949 = 2627495559 := by
        calc
          (11 : ZMod 2864303569) ^ 49949 = (11 : ZMod 2864303569) ^ (24974 + 24974 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 24974 * (11 : ZMod 2864303569) ^ 24974) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2627495559 := by rw [factor_2_14]; decide
      have factor_2_16 : (11 : ZMod 2864303569) ^ 99898 = 2300510833 := by
        calc
          (11 : ZMod 2864303569) ^ 99898 = (11 : ZMod 2864303569) ^ (49949 + 49949) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 49949 * (11 : ZMod 2864303569) ^ 49949 := by rw [pow_add]
          _ = 2300510833 := by rw [factor_2_15]; decide
      have factor_2_17 : (11 : ZMod 2864303569) ^ 199797 = 718622561 := by
        calc
          (11 : ZMod 2864303569) ^ 199797 = (11 : ZMod 2864303569) ^ (99898 + 99898 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 99898 * (11 : ZMod 2864303569) ^ 99898) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 718622561 := by rw [factor_2_16]; decide
      have factor_2_18 : (11 : ZMod 2864303569) ^ 399595 = 1857198059 := by
        calc
          (11 : ZMod 2864303569) ^ 399595 = (11 : ZMod 2864303569) ^ (199797 + 199797 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 199797 * (11 : ZMod 2864303569) ^ 199797) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1857198059 := by rw [factor_2_17]; decide
      have factor_2_19 : (11 : ZMod 2864303569) ^ 799191 = 2851972993 := by
        calc
          (11 : ZMod 2864303569) ^ 799191 = (11 : ZMod 2864303569) ^ (399595 + 399595 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 399595 * (11 : ZMod 2864303569) ^ 399595) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2851972993 := by rw [factor_2_18]; decide
      have factor_2_20 : (11 : ZMod 2864303569) ^ 1598383 = 1566863298 := by
        calc
          (11 : ZMod 2864303569) ^ 1598383 = (11 : ZMod 2864303569) ^ (799191 + 799191 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 799191 * (11 : ZMod 2864303569) ^ 799191) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1566863298 := by rw [factor_2_19]; decide
      have factor_2_21 : (11 : ZMod 2864303569) ^ 3196767 = 1070413310 := by
        calc
          (11 : ZMod 2864303569) ^ 3196767 = (11 : ZMod 2864303569) ^ (1598383 + 1598383 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 1598383 * (11 : ZMod 2864303569) ^ 1598383) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1070413310 := by rw [factor_2_20]; decide
      have factor_2_22 : (11 : ZMod 2864303569) ^ 6393534 = 2852477563 := by
        calc
          (11 : ZMod 2864303569) ^ 6393534 = (11 : ZMod 2864303569) ^ (3196767 + 3196767) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 3196767 * (11 : ZMod 2864303569) ^ 3196767 := by rw [pow_add]
          _ = 2852477563 := by rw [factor_2_21]; decide
      have factor_2_23 : (11 : ZMod 2864303569) ^ 12787069 = 1200247479 := by
        calc
          (11 : ZMod 2864303569) ^ 12787069 = (11 : ZMod 2864303569) ^ (6393534 + 6393534 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 6393534 * (11 : ZMod 2864303569) ^ 6393534) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1200247479 := by rw [factor_2_22]; decide
      have factor_2_24 : (11 : ZMod 2864303569) ^ 25574139 = 1538236616 := by
        calc
          (11 : ZMod 2864303569) ^ 25574139 = (11 : ZMod 2864303569) ^ (12787069 + 12787069 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 12787069 * (11 : ZMod 2864303569) ^ 12787069) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1538236616 := by rw [factor_2_23]; decide
      have factor_2_25 : (11 : ZMod 2864303569) ^ 51148278 = 1684831619 := by
        calc
          (11 : ZMod 2864303569) ^ 51148278 = (11 : ZMod 2864303569) ^ (25574139 + 25574139) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 25574139 * (11 : ZMod 2864303569) ^ 25574139 := by rw [pow_add]
          _ = 1684831619 := by rw [factor_2_24]; decide
      have factor_2_26 : (11 : ZMod 2864303569) ^ 102296556 = 1354255856 := by
        calc
          (11 : ZMod 2864303569) ^ 102296556 = (11 : ZMod 2864303569) ^ (51148278 + 51148278) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 51148278 * (11 : ZMod 2864303569) ^ 51148278 := by rw [pow_add]
          _ = 1354255856 := by rw [factor_2_25]; decide
      have factor_2_27 : (11 : ZMod 2864303569) ^ 204593112 = 2772892361 := by
        calc
          (11 : ZMod 2864303569) ^ 204593112 = (11 : ZMod 2864303569) ^ (102296556 + 102296556) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 102296556 * (11 : ZMod 2864303569) ^ 102296556 := by rw [pow_add]
          _ = 2772892361 := by rw [factor_2_26]; decide
      have factor_2_28 : (11 : ZMod 2864303569) ^ 409186224 = 1924907685 := by
        calc
          (11 : ZMod 2864303569) ^ 409186224 = (11 : ZMod 2864303569) ^ (204593112 + 204593112) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 204593112 * (11 : ZMod 2864303569) ^ 204593112 := by rw [pow_add]
          _ = 1924907685 := by rw [factor_2_27]; decide
      change (11 : ZMod 2864303569) ^ 409186224 ≠ 1
      rw [factor_2_28]
      decide
    ·
      have factor_3_0 : (11 : ZMod 2864303569) ^ 1 = 11 := by norm_num
      have factor_3_1 : (11 : ZMod 2864303569) ^ 2 = 121 := by
        calc
          (11 : ZMod 2864303569) ^ 2 = (11 : ZMod 2864303569) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 1 * (11 : ZMod 2864303569) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_3_0]; decide
      have factor_3_2 : (11 : ZMod 2864303569) ^ 5 = 161051 := by
        calc
          (11 : ZMod 2864303569) ^ 5 = (11 : ZMod 2864303569) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 2 * (11 : ZMod 2864303569) ^ 2) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 161051 := by rw [factor_3_1]; decide
      have factor_3_3 : (11 : ZMod 2864303569) ^ 10 = 158692480 := by
        calc
          (11 : ZMod 2864303569) ^ 10 = (11 : ZMod 2864303569) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 5 * (11 : ZMod 2864303569) ^ 5 := by rw [pow_add]
          _ = 158692480 := by rw [factor_3_2]; decide
      have factor_3_4 : (11 : ZMod 2864303569) ^ 21 = 1869483199 := by
        calc
          (11 : ZMod 2864303569) ^ 21 = (11 : ZMod 2864303569) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 10 * (11 : ZMod 2864303569) ^ 10) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1869483199 := by rw [factor_3_3]; decide
      have factor_3_5 : (11 : ZMod 2864303569) ^ 43 = 697796481 := by
        calc
          (11 : ZMod 2864303569) ^ 43 = (11 : ZMod 2864303569) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 21 * (11 : ZMod 2864303569) ^ 21) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 697796481 := by rw [factor_3_4]; decide
      have factor_3_6 : (11 : ZMod 2864303569) ^ 87 = 2112279483 := by
        calc
          (11 : ZMod 2864303569) ^ 87 = (11 : ZMod 2864303569) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 43 * (11 : ZMod 2864303569) ^ 43) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2112279483 := by rw [factor_3_5]; decide
      have factor_3_7 : (11 : ZMod 2864303569) ^ 174 = 1799464250 := by
        calc
          (11 : ZMod 2864303569) ^ 174 = (11 : ZMod 2864303569) ^ (87 + 87) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 87 * (11 : ZMod 2864303569) ^ 87 := by rw [pow_add]
          _ = 1799464250 := by rw [factor_3_6]; decide
      have factor_3_8 : (11 : ZMod 2864303569) ^ 348 = 1270667491 := by
        calc
          (11 : ZMod 2864303569) ^ 348 = (11 : ZMod 2864303569) ^ (174 + 174) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 174 * (11 : ZMod 2864303569) ^ 174 := by rw [pow_add]
          _ = 1270667491 := by rw [factor_3_7]; decide
      have factor_3_9 : (11 : ZMod 2864303569) ^ 696 = 964049864 := by
        calc
          (11 : ZMod 2864303569) ^ 696 = (11 : ZMod 2864303569) ^ (348 + 348) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 348 * (11 : ZMod 2864303569) ^ 348 := by rw [pow_add]
          _ = 964049864 := by rw [factor_3_8]; decide
      have factor_3_10 : (11 : ZMod 2864303569) ^ 1393 = 1480713425 := by
        calc
          (11 : ZMod 2864303569) ^ 1393 = (11 : ZMod 2864303569) ^ (696 + 696 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 696 * (11 : ZMod 2864303569) ^ 696) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1480713425 := by rw [factor_3_9]; decide
      have factor_3_11 : (11 : ZMod 2864303569) ^ 2786 = 2390456975 := by
        calc
          (11 : ZMod 2864303569) ^ 2786 = (11 : ZMod 2864303569) ^ (1393 + 1393) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 1393 * (11 : ZMod 2864303569) ^ 1393 := by rw [pow_add]
          _ = 2390456975 := by rw [factor_3_10]; decide
      have factor_3_12 : (11 : ZMod 2864303569) ^ 5572 = 420685431 := by
        calc
          (11 : ZMod 2864303569) ^ 5572 = (11 : ZMod 2864303569) ^ (2786 + 2786) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 2786 * (11 : ZMod 2864303569) ^ 2786 := by rw [pow_add]
          _ = 420685431 := by rw [factor_3_11]; decide
      have factor_3_13 : (11 : ZMod 2864303569) ^ 11144 = 2762370198 := by
        calc
          (11 : ZMod 2864303569) ^ 11144 = (11 : ZMod 2864303569) ^ (5572 + 5572) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 5572 * (11 : ZMod 2864303569) ^ 5572 := by rw [pow_add]
          _ = 2762370198 := by rw [factor_3_12]; decide
      have factor_3_14 : (11 : ZMod 2864303569) ^ 22288 = 1983090553 := by
        calc
          (11 : ZMod 2864303569) ^ 22288 = (11 : ZMod 2864303569) ^ (11144 + 11144) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 11144 * (11 : ZMod 2864303569) ^ 11144 := by rw [pow_add]
          _ = 1983090553 := by rw [factor_3_13]; decide
      have factor_3_15 : (11 : ZMod 2864303569) ^ 44576 = 2814311333 := by
        calc
          (11 : ZMod 2864303569) ^ 44576 = (11 : ZMod 2864303569) ^ (22288 + 22288) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 22288 * (11 : ZMod 2864303569) ^ 22288 := by rw [pow_add]
          _ = 2814311333 := by rw [factor_3_14]; decide
      have factor_3_16 : (11 : ZMod 2864303569) ^ 89152 = 1359880867 := by
        calc
          (11 : ZMod 2864303569) ^ 89152 = (11 : ZMod 2864303569) ^ (44576 + 44576) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 44576 * (11 : ZMod 2864303569) ^ 44576 := by rw [pow_add]
          _ = 1359880867 := by rw [factor_3_15]; decide
      have factor_3_17 : (11 : ZMod 2864303569) ^ 178305 = 1776017378 := by
        calc
          (11 : ZMod 2864303569) ^ 178305 = (11 : ZMod 2864303569) ^ (89152 + 89152 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 89152 * (11 : ZMod 2864303569) ^ 89152) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1776017378 := by rw [factor_3_16]; decide
      have factor_3_18 : (11 : ZMod 2864303569) ^ 356611 = 600800934 := by
        calc
          (11 : ZMod 2864303569) ^ 356611 = (11 : ZMod 2864303569) ^ (178305 + 178305 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 178305 * (11 : ZMod 2864303569) ^ 178305) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 600800934 := by rw [factor_3_17]; decide
      have factor_3_19 : (11 : ZMod 2864303569) ^ 713223 = 2033300966 := by
        calc
          (11 : ZMod 2864303569) ^ 713223 = (11 : ZMod 2864303569) ^ (356611 + 356611 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 356611 * (11 : ZMod 2864303569) ^ 356611) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2033300966 := by rw [factor_3_18]; decide
      have factor_3_20 : (11 : ZMod 2864303569) ^ 1426446 = 1370735122 := by
        calc
          (11 : ZMod 2864303569) ^ 1426446 = (11 : ZMod 2864303569) ^ (713223 + 713223) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 713223 * (11 : ZMod 2864303569) ^ 713223 := by rw [pow_add]
          _ = 1370735122 := by rw [factor_3_19]; decide
      have factor_3_21 : (11 : ZMod 2864303569) ^ 2852892 = 1482243345 := by
        calc
          (11 : ZMod 2864303569) ^ 2852892 = (11 : ZMod 2864303569) ^ (1426446 + 1426446) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 1426446 * (11 : ZMod 2864303569) ^ 1426446 := by rw [pow_add]
          _ = 1482243345 := by rw [factor_3_20]; decide
      have factor_3_22 : (11 : ZMod 2864303569) ^ 5705784 = 2283466009 := by
        calc
          (11 : ZMod 2864303569) ^ 5705784 = (11 : ZMod 2864303569) ^ (2852892 + 2852892) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 2852892 * (11 : ZMod 2864303569) ^ 2852892 := by rw [pow_add]
          _ = 2283466009 := by rw [factor_3_21]; decide
      have factor_3_23 : (11 : ZMod 2864303569) ^ 11411568 = 258945976 := by
        calc
          (11 : ZMod 2864303569) ^ 11411568 = (11 : ZMod 2864303569) ^ (5705784 + 5705784) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 5705784 * (11 : ZMod 2864303569) ^ 5705784 := by rw [pow_add]
          _ = 258945976 := by rw [factor_3_22]; decide
      change (11 : ZMod 2864303569) ^ 11411568 ≠ 1
      rw [factor_3_23]
      decide
    ·
      have factor_4_0 : (11 : ZMod 2864303569) ^ 1 = 11 := by norm_num
      have factor_4_1 : (11 : ZMod 2864303569) ^ 3 = 1331 := by
        calc
          (11 : ZMod 2864303569) ^ 3 = (11 : ZMod 2864303569) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 1 * (11 : ZMod 2864303569) ^ 1) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1331 := by rw [factor_4_0]; decide
      have factor_4_2 : (11 : ZMod 2864303569) ^ 7 = 19487171 := by
        calc
          (11 : ZMod 2864303569) ^ 7 = (11 : ZMod 2864303569) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 3 * (11 : ZMod 2864303569) ^ 3) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 19487171 := by rw [factor_4_1]; decide
      have factor_4_3 : (11 : ZMod 2864303569) ^ 15 = 2266153862 := by
        calc
          (11 : ZMod 2864303569) ^ 15 = (11 : ZMod 2864303569) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 7 * (11 : ZMod 2864303569) ^ 7) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2266153862 := by rw [factor_4_2]; decide
      have factor_4_4 : (11 : ZMod 2864303569) ^ 30 = 183666176 := by
        calc
          (11 : ZMod 2864303569) ^ 30 = (11 : ZMod 2864303569) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 15 * (11 : ZMod 2864303569) ^ 15 := by rw [pow_add]
          _ = 183666176 := by rw [factor_4_3]; decide
      have factor_4_5 : (11 : ZMod 2864303569) ^ 61 = 1893103102 := by
        calc
          (11 : ZMod 2864303569) ^ 61 = (11 : ZMod 2864303569) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 30 * (11 : ZMod 2864303569) ^ 30) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 1893103102 := by rw [factor_4_4]; decide
      have factor_4_6 : (11 : ZMod 2864303569) ^ 123 = 2631515572 := by
        calc
          (11 : ZMod 2864303569) ^ 123 = (11 : ZMod 2864303569) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 61 * (11 : ZMod 2864303569) ^ 61) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2631515572 := by rw [factor_4_5]; decide
      have factor_4_7 : (11 : ZMod 2864303569) ^ 247 = 2045225689 := by
        calc
          (11 : ZMod 2864303569) ^ 247 = (11 : ZMod 2864303569) ^ (123 + 123 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 123 * (11 : ZMod 2864303569) ^ 123) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2045225689 := by rw [factor_4_6]; decide
      have factor_4_8 : (11 : ZMod 2864303569) ^ 494 = 238820487 := by
        calc
          (11 : ZMod 2864303569) ^ 494 = (11 : ZMod 2864303569) ^ (247 + 247) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 247 * (11 : ZMod 2864303569) ^ 247 := by rw [pow_add]
          _ = 238820487 := by rw [factor_4_7]; decide
      have factor_4_9 : (11 : ZMod 2864303569) ^ 988 = 744579482 := by
        calc
          (11 : ZMod 2864303569) ^ 988 = (11 : ZMod 2864303569) ^ (494 + 494) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 494 * (11 : ZMod 2864303569) ^ 494 := by rw [pow_add]
          _ = 744579482 := by rw [factor_4_8]; decide
      have factor_4_10 : (11 : ZMod 2864303569) ^ 1976 = 470877620 := by
        calc
          (11 : ZMod 2864303569) ^ 1976 = (11 : ZMod 2864303569) ^ (988 + 988) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 988 * (11 : ZMod 2864303569) ^ 988 := by rw [pow_add]
          _ = 470877620 := by rw [factor_4_9]; decide
      have factor_4_11 : (11 : ZMod 2864303569) ^ 3953 = 2753907625 := by
        calc
          (11 : ZMod 2864303569) ^ 3953 = (11 : ZMod 2864303569) ^ (1976 + 1976 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 1976 * (11 : ZMod 2864303569) ^ 1976) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2753907625 := by rw [factor_4_10]; decide
      have factor_4_12 : (11 : ZMod 2864303569) ^ 7906 = 2210591554 := by
        calc
          (11 : ZMod 2864303569) ^ 7906 = (11 : ZMod 2864303569) ^ (3953 + 3953) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 3953 * (11 : ZMod 2864303569) ^ 3953 := by rw [pow_add]
          _ = 2210591554 := by rw [factor_4_11]; decide
      have factor_4_13 : (11 : ZMod 2864303569) ^ 15813 = 2180864714 := by
        calc
          (11 : ZMod 2864303569) ^ 15813 = (11 : ZMod 2864303569) ^ (7906 + 7906 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = ((11 : ZMod 2864303569) ^ 7906 * (11 : ZMod 2864303569) ^ 7906) * (11 : ZMod 2864303569) := by rw [pow_succ, pow_add]
          _ = 2180864714 := by rw [factor_4_12]; decide
      have factor_4_14 : (11 : ZMod 2864303569) ^ 31626 = 242350979 := by
        calc
          (11 : ZMod 2864303569) ^ 31626 = (11 : ZMod 2864303569) ^ (15813 + 15813) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 15813 * (11 : ZMod 2864303569) ^ 15813 := by rw [pow_add]
          _ = 242350979 := by rw [factor_4_13]; decide
      have factor_4_15 : (11 : ZMod 2864303569) ^ 63252 = 138003958 := by
        calc
          (11 : ZMod 2864303569) ^ 63252 = (11 : ZMod 2864303569) ^ (31626 + 31626) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 31626 * (11 : ZMod 2864303569) ^ 31626 := by rw [pow_add]
          _ = 138003958 := by rw [factor_4_14]; decide
      have factor_4_16 : (11 : ZMod 2864303569) ^ 126504 = 5563622 := by
        calc
          (11 : ZMod 2864303569) ^ 126504 = (11 : ZMod 2864303569) ^ (63252 + 63252) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 63252 * (11 : ZMod 2864303569) ^ 63252 := by rw [pow_add]
          _ = 5563622 := by rw [factor_4_15]; decide
      have factor_4_17 : (11 : ZMod 2864303569) ^ 253008 = 2225392270 := by
        calc
          (11 : ZMod 2864303569) ^ 253008 = (11 : ZMod 2864303569) ^ (126504 + 126504) :=
            congrArg (fun n : ℕ => (11 : ZMod 2864303569) ^ n) (by norm_num)
          _ = (11 : ZMod 2864303569) ^ 126504 * (11 : ZMod 2864303569) ^ 126504 := by rw [pow_add]
          _ = 2225392270 := by rw [factor_4_16]; decide
      change (11 : ZMod 2864303569) ^ 253008 ≠ 1
      rw [factor_4_17]
      decide

#print axioms prime_lucas_2864303569

end TotientTailPeriodKiller
end Erdos249257
