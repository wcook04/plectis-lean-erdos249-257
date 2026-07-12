import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=32 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_777012787 : Nat.Prime 777012787 := by
  apply lucas_primality 777012787 (2 : ZMod 777012787)
  ·
      have fermat_0 : (2 : ZMod 777012787) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 777012787) ^ 2 = 4 := by
        calc
          (2 : ZMod 777012787) ^ 2 = (2 : ZMod 777012787) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 1 * (2 : ZMod 777012787) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 777012787) ^ 5 = 32 := by
        calc
          (2 : ZMod 777012787) ^ 5 = (2 : ZMod 777012787) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 2 * (2 : ZMod 777012787) ^ 2) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 777012787) ^ 11 = 2048 := by
        calc
          (2 : ZMod 777012787) ^ 11 = (2 : ZMod 777012787) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 5 * (2 : ZMod 777012787) ^ 5) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 777012787) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 777012787) ^ 23 = (2 : ZMod 777012787) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 11 * (2 : ZMod 777012787) ^ 11) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 777012787) ^ 46 = 135148583 := by
        calc
          (2 : ZMod 777012787) ^ 46 = (2 : ZMod 777012787) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 23 * (2 : ZMod 777012787) ^ 23 := by rw [pow_add]
          _ = 135148583 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 777012787) ^ 92 = 137548412 := by
        calc
          (2 : ZMod 777012787) ^ 92 = (2 : ZMod 777012787) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 46 * (2 : ZMod 777012787) ^ 46 := by rw [pow_add]
          _ = 137548412 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 777012787) ^ 185 = 190445005 := by
        calc
          (2 : ZMod 777012787) ^ 185 = (2 : ZMod 777012787) ^ (92 + 92 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 92 * (2 : ZMod 777012787) ^ 92) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 190445005 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 777012787) ^ 370 = 400564696 := by
        calc
          (2 : ZMod 777012787) ^ 370 = (2 : ZMod 777012787) ^ (185 + 185) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 185 * (2 : ZMod 777012787) ^ 185 := by rw [pow_add]
          _ = 400564696 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 777012787) ^ 741 = 124193999 := by
        calc
          (2 : ZMod 777012787) ^ 741 = (2 : ZMod 777012787) ^ (370 + 370 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 370 * (2 : ZMod 777012787) ^ 370) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 124193999 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 777012787) ^ 1482 = 337335050 := by
        calc
          (2 : ZMod 777012787) ^ 1482 = (2 : ZMod 777012787) ^ (741 + 741) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 741 * (2 : ZMod 777012787) ^ 741 := by rw [pow_add]
          _ = 337335050 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 777012787) ^ 2964 = 693105734 := by
        calc
          (2 : ZMod 777012787) ^ 2964 = (2 : ZMod 777012787) ^ (1482 + 1482) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 1482 * (2 : ZMod 777012787) ^ 1482 := by rw [pow_add]
          _ = 693105734 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 777012787) ^ 5928 = 340107007 := by
        calc
          (2 : ZMod 777012787) ^ 5928 = (2 : ZMod 777012787) ^ (2964 + 2964) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 2964 * (2 : ZMod 777012787) ^ 2964 := by rw [pow_add]
          _ = 340107007 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 777012787) ^ 11856 = 731208542 := by
        calc
          (2 : ZMod 777012787) ^ 11856 = (2 : ZMod 777012787) ^ (5928 + 5928) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 5928 * (2 : ZMod 777012787) ^ 5928 := by rw [pow_add]
          _ = 731208542 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 777012787) ^ 23712 = 316572798 := by
        calc
          (2 : ZMod 777012787) ^ 23712 = (2 : ZMod 777012787) ^ (11856 + 11856) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 11856 * (2 : ZMod 777012787) ^ 11856 := by rw [pow_add]
          _ = 316572798 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 777012787) ^ 47425 = 588023738 := by
        calc
          (2 : ZMod 777012787) ^ 47425 = (2 : ZMod 777012787) ^ (23712 + 23712 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 23712 * (2 : ZMod 777012787) ^ 23712) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 588023738 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 777012787) ^ 94850 = 110314758 := by
        calc
          (2 : ZMod 777012787) ^ 94850 = (2 : ZMod 777012787) ^ (47425 + 47425) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 47425 * (2 : ZMod 777012787) ^ 47425 := by rw [pow_add]
          _ = 110314758 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 777012787) ^ 189700 = 4363942 := by
        calc
          (2 : ZMod 777012787) ^ 189700 = (2 : ZMod 777012787) ^ (94850 + 94850) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 94850 * (2 : ZMod 777012787) ^ 94850 := by rw [pow_add]
          _ = 4363942 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 777012787) ^ 379400 = 183382781 := by
        calc
          (2 : ZMod 777012787) ^ 379400 = (2 : ZMod 777012787) ^ (189700 + 189700) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 189700 * (2 : ZMod 777012787) ^ 189700 := by rw [pow_add]
          _ = 183382781 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 777012787) ^ 758801 = 38558703 := by
        calc
          (2 : ZMod 777012787) ^ 758801 = (2 : ZMod 777012787) ^ (379400 + 379400 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 379400 * (2 : ZMod 777012787) ^ 379400) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 38558703 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 777012787) ^ 1517603 = 27565266 := by
        calc
          (2 : ZMod 777012787) ^ 1517603 = (2 : ZMod 777012787) ^ (758801 + 758801 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 758801 * (2 : ZMod 777012787) ^ 758801) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 27565266 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 777012787) ^ 3035206 = 754205095 := by
        calc
          (2 : ZMod 777012787) ^ 3035206 = (2 : ZMod 777012787) ^ (1517603 + 1517603) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 1517603 * (2 : ZMod 777012787) ^ 1517603 := by rw [pow_add]
          _ = 754205095 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 777012787) ^ 6070412 = 178790039 := by
        calc
          (2 : ZMod 777012787) ^ 6070412 = (2 : ZMod 777012787) ^ (3035206 + 3035206) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 3035206 * (2 : ZMod 777012787) ^ 3035206 := by rw [pow_add]
          _ = 178790039 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 777012787) ^ 12140824 = 122487158 := by
        calc
          (2 : ZMod 777012787) ^ 12140824 = (2 : ZMod 777012787) ^ (6070412 + 6070412) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 6070412 * (2 : ZMod 777012787) ^ 6070412 := by rw [pow_add]
          _ = 122487158 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 777012787) ^ 24281649 = 365242424 := by
        calc
          (2 : ZMod 777012787) ^ 24281649 = (2 : ZMod 777012787) ^ (12140824 + 12140824 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 12140824 * (2 : ZMod 777012787) ^ 12140824) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 365242424 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 777012787) ^ 48563299 = 286254821 := by
        calc
          (2 : ZMod 777012787) ^ 48563299 = (2 : ZMod 777012787) ^ (24281649 + 24281649 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 24281649 * (2 : ZMod 777012787) ^ 24281649) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 286254821 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 777012787) ^ 97126598 = 445753476 := by
        calc
          (2 : ZMod 777012787) ^ 97126598 = (2 : ZMod 777012787) ^ (48563299 + 48563299) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 48563299 * (2 : ZMod 777012787) ^ 48563299 := by rw [pow_add]
          _ = 445753476 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 777012787) ^ 194253196 = 60927067 := by
        calc
          (2 : ZMod 777012787) ^ 194253196 = (2 : ZMod 777012787) ^ (97126598 + 97126598) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 97126598 * (2 : ZMod 777012787) ^ 97126598 := by rw [pow_add]
          _ = 60927067 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 777012787) ^ 388506393 = 777012786 := by
        calc
          (2 : ZMod 777012787) ^ 388506393 = (2 : ZMod 777012787) ^ (194253196 + 194253196 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 194253196 * (2 : ZMod 777012787) ^ 194253196) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 777012786 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 777012787) ^ 777012786 = 1 := by
        calc
          (2 : ZMod 777012787) ^ 777012786 = (2 : ZMod 777012787) ^ (388506393 + 388506393) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 388506393 * (2 : ZMod 777012787) ^ 388506393 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (11, 1), (3924307, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (11, 1), (3924307, 1)] : List FactorBlock).map factorBlockValue).prod = 777012787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 777012787) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 777012787) ^ 2 = 4 := by
        calc
          (2 : ZMod 777012787) ^ 2 = (2 : ZMod 777012787) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 1 * (2 : ZMod 777012787) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 777012787) ^ 5 = 32 := by
        calc
          (2 : ZMod 777012787) ^ 5 = (2 : ZMod 777012787) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 2 * (2 : ZMod 777012787) ^ 2) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 777012787) ^ 11 = 2048 := by
        calc
          (2 : ZMod 777012787) ^ 11 = (2 : ZMod 777012787) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 5 * (2 : ZMod 777012787) ^ 5) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 777012787) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 777012787) ^ 23 = (2 : ZMod 777012787) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 11 * (2 : ZMod 777012787) ^ 11) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 777012787) ^ 46 = 135148583 := by
        calc
          (2 : ZMod 777012787) ^ 46 = (2 : ZMod 777012787) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 23 * (2 : ZMod 777012787) ^ 23 := by rw [pow_add]
          _ = 135148583 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 777012787) ^ 92 = 137548412 := by
        calc
          (2 : ZMod 777012787) ^ 92 = (2 : ZMod 777012787) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 46 * (2 : ZMod 777012787) ^ 46 := by rw [pow_add]
          _ = 137548412 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 777012787) ^ 185 = 190445005 := by
        calc
          (2 : ZMod 777012787) ^ 185 = (2 : ZMod 777012787) ^ (92 + 92 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 92 * (2 : ZMod 777012787) ^ 92) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 190445005 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 777012787) ^ 370 = 400564696 := by
        calc
          (2 : ZMod 777012787) ^ 370 = (2 : ZMod 777012787) ^ (185 + 185) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 185 * (2 : ZMod 777012787) ^ 185 := by rw [pow_add]
          _ = 400564696 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 777012787) ^ 741 = 124193999 := by
        calc
          (2 : ZMod 777012787) ^ 741 = (2 : ZMod 777012787) ^ (370 + 370 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 370 * (2 : ZMod 777012787) ^ 370) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 124193999 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 777012787) ^ 1482 = 337335050 := by
        calc
          (2 : ZMod 777012787) ^ 1482 = (2 : ZMod 777012787) ^ (741 + 741) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 741 * (2 : ZMod 777012787) ^ 741 := by rw [pow_add]
          _ = 337335050 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 777012787) ^ 2964 = 693105734 := by
        calc
          (2 : ZMod 777012787) ^ 2964 = (2 : ZMod 777012787) ^ (1482 + 1482) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 1482 * (2 : ZMod 777012787) ^ 1482 := by rw [pow_add]
          _ = 693105734 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 777012787) ^ 5928 = 340107007 := by
        calc
          (2 : ZMod 777012787) ^ 5928 = (2 : ZMod 777012787) ^ (2964 + 2964) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 2964 * (2 : ZMod 777012787) ^ 2964 := by rw [pow_add]
          _ = 340107007 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 777012787) ^ 11856 = 731208542 := by
        calc
          (2 : ZMod 777012787) ^ 11856 = (2 : ZMod 777012787) ^ (5928 + 5928) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 5928 * (2 : ZMod 777012787) ^ 5928 := by rw [pow_add]
          _ = 731208542 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 777012787) ^ 23712 = 316572798 := by
        calc
          (2 : ZMod 777012787) ^ 23712 = (2 : ZMod 777012787) ^ (11856 + 11856) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 11856 * (2 : ZMod 777012787) ^ 11856 := by rw [pow_add]
          _ = 316572798 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 777012787) ^ 47425 = 588023738 := by
        calc
          (2 : ZMod 777012787) ^ 47425 = (2 : ZMod 777012787) ^ (23712 + 23712 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 23712 * (2 : ZMod 777012787) ^ 23712) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 588023738 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 777012787) ^ 94850 = 110314758 := by
        calc
          (2 : ZMod 777012787) ^ 94850 = (2 : ZMod 777012787) ^ (47425 + 47425) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 47425 * (2 : ZMod 777012787) ^ 47425 := by rw [pow_add]
          _ = 110314758 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 777012787) ^ 189700 = 4363942 := by
        calc
          (2 : ZMod 777012787) ^ 189700 = (2 : ZMod 777012787) ^ (94850 + 94850) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 94850 * (2 : ZMod 777012787) ^ 94850 := by rw [pow_add]
          _ = 4363942 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 777012787) ^ 379400 = 183382781 := by
        calc
          (2 : ZMod 777012787) ^ 379400 = (2 : ZMod 777012787) ^ (189700 + 189700) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 189700 * (2 : ZMod 777012787) ^ 189700 := by rw [pow_add]
          _ = 183382781 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 777012787) ^ 758801 = 38558703 := by
        calc
          (2 : ZMod 777012787) ^ 758801 = (2 : ZMod 777012787) ^ (379400 + 379400 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 379400 * (2 : ZMod 777012787) ^ 379400) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 38558703 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 777012787) ^ 1517603 = 27565266 := by
        calc
          (2 : ZMod 777012787) ^ 1517603 = (2 : ZMod 777012787) ^ (758801 + 758801 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 758801 * (2 : ZMod 777012787) ^ 758801) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 27565266 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 777012787) ^ 3035206 = 754205095 := by
        calc
          (2 : ZMod 777012787) ^ 3035206 = (2 : ZMod 777012787) ^ (1517603 + 1517603) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 1517603 * (2 : ZMod 777012787) ^ 1517603 := by rw [pow_add]
          _ = 754205095 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 777012787) ^ 6070412 = 178790039 := by
        calc
          (2 : ZMod 777012787) ^ 6070412 = (2 : ZMod 777012787) ^ (3035206 + 3035206) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 3035206 * (2 : ZMod 777012787) ^ 3035206 := by rw [pow_add]
          _ = 178790039 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 777012787) ^ 12140824 = 122487158 := by
        calc
          (2 : ZMod 777012787) ^ 12140824 = (2 : ZMod 777012787) ^ (6070412 + 6070412) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 6070412 * (2 : ZMod 777012787) ^ 6070412 := by rw [pow_add]
          _ = 122487158 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 777012787) ^ 24281649 = 365242424 := by
        calc
          (2 : ZMod 777012787) ^ 24281649 = (2 : ZMod 777012787) ^ (12140824 + 12140824 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 12140824 * (2 : ZMod 777012787) ^ 12140824) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 365242424 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 777012787) ^ 48563299 = 286254821 := by
        calc
          (2 : ZMod 777012787) ^ 48563299 = (2 : ZMod 777012787) ^ (24281649 + 24281649 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 24281649 * (2 : ZMod 777012787) ^ 24281649) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 286254821 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 777012787) ^ 97126598 = 445753476 := by
        calc
          (2 : ZMod 777012787) ^ 97126598 = (2 : ZMod 777012787) ^ (48563299 + 48563299) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 48563299 * (2 : ZMod 777012787) ^ 48563299 := by rw [pow_add]
          _ = 445753476 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 777012787) ^ 194253196 = 60927067 := by
        calc
          (2 : ZMod 777012787) ^ 194253196 = (2 : ZMod 777012787) ^ (97126598 + 97126598) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 97126598 * (2 : ZMod 777012787) ^ 97126598 := by rw [pow_add]
          _ = 60927067 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 777012787) ^ 388506393 = 777012786 := by
        calc
          (2 : ZMod 777012787) ^ 388506393 = (2 : ZMod 777012787) ^ (194253196 + 194253196 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 194253196 * (2 : ZMod 777012787) ^ 194253196) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 777012786 := by rw [factor_0_27]; decide
      change (2 : ZMod 777012787) ^ 388506393 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (2 : ZMod 777012787) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 777012787) ^ 3 = 8 := by
        calc
          (2 : ZMod 777012787) ^ 3 = (2 : ZMod 777012787) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 1 * (2 : ZMod 777012787) ^ 1) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 777012787) ^ 7 = 128 := by
        calc
          (2 : ZMod 777012787) ^ 7 = (2 : ZMod 777012787) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 3 * (2 : ZMod 777012787) ^ 3) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 777012787) ^ 15 = 32768 := by
        calc
          (2 : ZMod 777012787) ^ 15 = (2 : ZMod 777012787) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 7 * (2 : ZMod 777012787) ^ 7) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 777012787) ^ 30 = 296729037 := by
        calc
          (2 : ZMod 777012787) ^ 30 = (2 : ZMod 777012787) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 15 * (2 : ZMod 777012787) ^ 15 := by rw [pow_add]
          _ = 296729037 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 777012787) ^ 61 = 352894631 := by
        calc
          (2 : ZMod 777012787) ^ 61 = (2 : ZMod 777012787) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 30 * (2 : ZMod 777012787) ^ 30) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 352894631 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 777012787) ^ 123 = 574742976 := by
        calc
          (2 : ZMod 777012787) ^ 123 = (2 : ZMod 777012787) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 61 * (2 : ZMod 777012787) ^ 61) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 574742976 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 777012787) ^ 247 = 15486845 := by
        calc
          (2 : ZMod 777012787) ^ 247 = (2 : ZMod 777012787) ^ (123 + 123 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 123 * (2 : ZMod 777012787) ^ 123) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 15486845 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 777012787) ^ 494 = 277065161 := by
        calc
          (2 : ZMod 777012787) ^ 494 = (2 : ZMod 777012787) ^ (247 + 247) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 247 * (2 : ZMod 777012787) ^ 247 := by rw [pow_add]
          _ = 277065161 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 777012787) ^ 988 = 49232214 := by
        calc
          (2 : ZMod 777012787) ^ 988 = (2 : ZMod 777012787) ^ (494 + 494) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 494 * (2 : ZMod 777012787) ^ 494 := by rw [pow_add]
          _ = 49232214 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 777012787) ^ 1976 = 315625144 := by
        calc
          (2 : ZMod 777012787) ^ 1976 = (2 : ZMod 777012787) ^ (988 + 988) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 988 * (2 : ZMod 777012787) ^ 988 := by rw [pow_add]
          _ = 315625144 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 777012787) ^ 3952 = 216721133 := by
        calc
          (2 : ZMod 777012787) ^ 3952 = (2 : ZMod 777012787) ^ (1976 + 1976) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 1976 * (2 : ZMod 777012787) ^ 1976 := by rw [pow_add]
          _ = 216721133 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 777012787) ^ 7904 = 288717974 := by
        calc
          (2 : ZMod 777012787) ^ 7904 = (2 : ZMod 777012787) ^ (3952 + 3952) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 3952 * (2 : ZMod 777012787) ^ 3952 := by rw [pow_add]
          _ = 288717974 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 777012787) ^ 15808 = 744066951 := by
        calc
          (2 : ZMod 777012787) ^ 15808 = (2 : ZMod 777012787) ^ (7904 + 7904) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 7904 * (2 : ZMod 777012787) ^ 7904 := by rw [pow_add]
          _ = 744066951 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 777012787) ^ 31616 = 299271708 := by
        calc
          (2 : ZMod 777012787) ^ 31616 = (2 : ZMod 777012787) ^ (15808 + 15808) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 15808 * (2 : ZMod 777012787) ^ 15808 := by rw [pow_add]
          _ = 299271708 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 777012787) ^ 63233 = 613658279 := by
        calc
          (2 : ZMod 777012787) ^ 63233 = (2 : ZMod 777012787) ^ (31616 + 31616 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 31616 * (2 : ZMod 777012787) ^ 31616) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 613658279 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 777012787) ^ 126466 = 175200 := by
        calc
          (2 : ZMod 777012787) ^ 126466 = (2 : ZMod 777012787) ^ (63233 + 63233) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 63233 * (2 : ZMod 777012787) ^ 63233 := by rw [pow_add]
          _ = 175200 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 777012787) ^ 252933 = 6069827 := by
        calc
          (2 : ZMod 777012787) ^ 252933 = (2 : ZMod 777012787) ^ (126466 + 126466 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 126466 * (2 : ZMod 777012787) ^ 126466) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 6069827 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 777012787) ^ 505867 = 700015861 := by
        calc
          (2 : ZMod 777012787) ^ 505867 = (2 : ZMod 777012787) ^ (252933 + 252933 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 252933 * (2 : ZMod 777012787) ^ 252933) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 700015861 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 777012787) ^ 1011735 = 492951435 := by
        calc
          (2 : ZMod 777012787) ^ 1011735 = (2 : ZMod 777012787) ^ (505867 + 505867 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 505867 * (2 : ZMod 777012787) ^ 505867) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 492951435 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 777012787) ^ 2023470 = 761829664 := by
        calc
          (2 : ZMod 777012787) ^ 2023470 = (2 : ZMod 777012787) ^ (1011735 + 1011735) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 1011735 * (2 : ZMod 777012787) ^ 1011735 := by rw [pow_add]
          _ = 761829664 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 777012787) ^ 4046941 = 701682429 := by
        calc
          (2 : ZMod 777012787) ^ 4046941 = (2 : ZMod 777012787) ^ (2023470 + 2023470 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 2023470 * (2 : ZMod 777012787) ^ 2023470) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 701682429 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 777012787) ^ 8093883 = 289342156 := by
        calc
          (2 : ZMod 777012787) ^ 8093883 = (2 : ZMod 777012787) ^ (4046941 + 4046941 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 4046941 * (2 : ZMod 777012787) ^ 4046941) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 289342156 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 777012787) ^ 16187766 = 260333717 := by
        calc
          (2 : ZMod 777012787) ^ 16187766 = (2 : ZMod 777012787) ^ (8093883 + 8093883) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 8093883 * (2 : ZMod 777012787) ^ 8093883 := by rw [pow_add]
          _ = 260333717 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 777012787) ^ 32375532 = 695302592 := by
        calc
          (2 : ZMod 777012787) ^ 32375532 = (2 : ZMod 777012787) ^ (16187766 + 16187766) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 16187766 * (2 : ZMod 777012787) ^ 16187766 := by rw [pow_add]
          _ = 695302592 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 777012787) ^ 64751065 = 333864307 := by
        calc
          (2 : ZMod 777012787) ^ 64751065 = (2 : ZMod 777012787) ^ (32375532 + 32375532 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 32375532 * (2 : ZMod 777012787) ^ 32375532) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 333864307 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 777012787) ^ 129502131 = 634732431 := by
        calc
          (2 : ZMod 777012787) ^ 129502131 = (2 : ZMod 777012787) ^ (64751065 + 64751065 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 64751065 * (2 : ZMod 777012787) ^ 64751065) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 634732431 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 777012787) ^ 259004262 = 634732430 := by
        calc
          (2 : ZMod 777012787) ^ 259004262 = (2 : ZMod 777012787) ^ (129502131 + 129502131) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 129502131 * (2 : ZMod 777012787) ^ 129502131 := by rw [pow_add]
          _ = 634732430 := by rw [factor_1_26]; decide
      change (2 : ZMod 777012787) ^ 259004262 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (2 : ZMod 777012787) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 777012787) ^ 2 = 4 := by
        calc
          (2 : ZMod 777012787) ^ 2 = (2 : ZMod 777012787) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 1 * (2 : ZMod 777012787) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 777012787) ^ 4 = 16 := by
        calc
          (2 : ZMod 777012787) ^ 4 = (2 : ZMod 777012787) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 2 * (2 : ZMod 777012787) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 777012787) ^ 8 = 256 := by
        calc
          (2 : ZMod 777012787) ^ 8 = (2 : ZMod 777012787) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 4 * (2 : ZMod 777012787) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 777012787) ^ 16 = 65536 := by
        calc
          (2 : ZMod 777012787) ^ 16 = (2 : ZMod 777012787) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 8 * (2 : ZMod 777012787) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 777012787) ^ 33 = 42793935 := by
        calc
          (2 : ZMod 777012787) ^ 33 = (2 : ZMod 777012787) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 16 * (2 : ZMod 777012787) ^ 16) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 42793935 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 777012787) ^ 67 = 51885561 := by
        calc
          (2 : ZMod 777012787) ^ 67 = (2 : ZMod 777012787) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 33 * (2 : ZMod 777012787) ^ 33) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 51885561 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 777012787) ^ 134 = 676255330 := by
        calc
          (2 : ZMod 777012787) ^ 134 = (2 : ZMod 777012787) ^ (67 + 67) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 67 * (2 : ZMod 777012787) ^ 67 := by rw [pow_add]
          _ = 676255330 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 777012787) ^ 269 = 597976041 := by
        calc
          (2 : ZMod 777012787) ^ 269 = (2 : ZMod 777012787) ^ (134 + 134 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 134 * (2 : ZMod 777012787) ^ 134) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 597976041 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 777012787) ^ 538 = 518377509 := by
        calc
          (2 : ZMod 777012787) ^ 538 = (2 : ZMod 777012787) ^ (269 + 269) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 269 * (2 : ZMod 777012787) ^ 269 := by rw [pow_add]
          _ = 518377509 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 777012787) ^ 1077 = 430735795 := by
        calc
          (2 : ZMod 777012787) ^ 1077 = (2 : ZMod 777012787) ^ (538 + 538 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 538 * (2 : ZMod 777012787) ^ 538) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 430735795 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 777012787) ^ 2155 = 218702611 := by
        calc
          (2 : ZMod 777012787) ^ 2155 = (2 : ZMod 777012787) ^ (1077 + 1077 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 1077 * (2 : ZMod 777012787) ^ 1077) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 218702611 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 777012787) ^ 4311 = 583302796 := by
        calc
          (2 : ZMod 777012787) ^ 4311 = (2 : ZMod 777012787) ^ (2155 + 2155 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 2155 * (2 : ZMod 777012787) ^ 2155) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 583302796 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 777012787) ^ 8622 = 50444269 := by
        calc
          (2 : ZMod 777012787) ^ 8622 = (2 : ZMod 777012787) ^ (4311 + 4311) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 4311 * (2 : ZMod 777012787) ^ 4311 := by rw [pow_add]
          _ = 50444269 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 777012787) ^ 17245 = 501094815 := by
        calc
          (2 : ZMod 777012787) ^ 17245 = (2 : ZMod 777012787) ^ (8622 + 8622 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 8622 * (2 : ZMod 777012787) ^ 8622) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 501094815 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 777012787) ^ 34490 = 431559487 := by
        calc
          (2 : ZMod 777012787) ^ 34490 = (2 : ZMod 777012787) ^ (17245 + 17245) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 17245 * (2 : ZMod 777012787) ^ 17245 := by rw [pow_add]
          _ = 431559487 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 777012787) ^ 68981 = 402647 := by
        calc
          (2 : ZMod 777012787) ^ 68981 = (2 : ZMod 777012787) ^ (34490 + 34490 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 34490 * (2 : ZMod 777012787) ^ 34490) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 402647 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 777012787) ^ 137963 = 234881039 := by
        calc
          (2 : ZMod 777012787) ^ 137963 = (2 : ZMod 777012787) ^ (68981 + 68981 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 68981 * (2 : ZMod 777012787) ^ 68981) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 234881039 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 777012787) ^ 275927 = 672131804 := by
        calc
          (2 : ZMod 777012787) ^ 275927 = (2 : ZMod 777012787) ^ (137963 + 137963 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 137963 * (2 : ZMod 777012787) ^ 137963) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 672131804 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 777012787) ^ 551855 = 288897573 := by
        calc
          (2 : ZMod 777012787) ^ 551855 = (2 : ZMod 777012787) ^ (275927 + 275927 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 275927 * (2 : ZMod 777012787) ^ 275927) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 288897573 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 777012787) ^ 1103711 = 328974894 := by
        calc
          (2 : ZMod 777012787) ^ 1103711 = (2 : ZMod 777012787) ^ (551855 + 551855 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 551855 * (2 : ZMod 777012787) ^ 551855) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 328974894 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 777012787) ^ 2207422 = 15735838 := by
        calc
          (2 : ZMod 777012787) ^ 2207422 = (2 : ZMod 777012787) ^ (1103711 + 1103711) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 1103711 * (2 : ZMod 777012787) ^ 1103711 := by rw [pow_add]
          _ = 15735838 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 777012787) ^ 4414845 = 210266103 := by
        calc
          (2 : ZMod 777012787) ^ 4414845 = (2 : ZMod 777012787) ^ (2207422 + 2207422 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 2207422 * (2 : ZMod 777012787) ^ 2207422) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 210266103 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 777012787) ^ 8829690 = 743703359 := by
        calc
          (2 : ZMod 777012787) ^ 8829690 = (2 : ZMod 777012787) ^ (4414845 + 4414845) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 4414845 * (2 : ZMod 777012787) ^ 4414845 := by rw [pow_add]
          _ = 743703359 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 777012787) ^ 17659381 = 134556483 := by
        calc
          (2 : ZMod 777012787) ^ 17659381 = (2 : ZMod 777012787) ^ (8829690 + 8829690 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 8829690 * (2 : ZMod 777012787) ^ 8829690) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 134556483 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 777012787) ^ 35318763 = 425933678 := by
        calc
          (2 : ZMod 777012787) ^ 35318763 = (2 : ZMod 777012787) ^ (17659381 + 17659381 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 17659381 * (2 : ZMod 777012787) ^ 17659381) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 425933678 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 777012787) ^ 70637526 = 58842389 := by
        calc
          (2 : ZMod 777012787) ^ 70637526 = (2 : ZMod 777012787) ^ (35318763 + 35318763) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 35318763 * (2 : ZMod 777012787) ^ 35318763 := by rw [pow_add]
          _ = 58842389 := by rw [factor_2_25]; decide
      change (2 : ZMod 777012787) ^ 70637526 ≠ 1
      rw [factor_2_26]
      decide
    ·
      have factor_3_0 : (2 : ZMod 777012787) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 777012787) ^ 3 = 8 := by
        calc
          (2 : ZMod 777012787) ^ 3 = (2 : ZMod 777012787) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 1 * (2 : ZMod 777012787) ^ 1) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 777012787) ^ 6 = 64 := by
        calc
          (2 : ZMod 777012787) ^ 6 = (2 : ZMod 777012787) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 3 * (2 : ZMod 777012787) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 777012787) ^ 12 = 4096 := by
        calc
          (2 : ZMod 777012787) ^ 12 = (2 : ZMod 777012787) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 6 * (2 : ZMod 777012787) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 777012787) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 777012787) ^ 24 = (2 : ZMod 777012787) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 12 * (2 : ZMod 777012787) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 777012787) ^ 49 = 304175877 := by
        calc
          (2 : ZMod 777012787) ^ 49 = (2 : ZMod 777012787) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 24 * (2 : ZMod 777012787) ^ 24) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 304175877 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 777012787) ^ 99 = 511915422 := by
        calc
          (2 : ZMod 777012787) ^ 99 = (2 : ZMod 777012787) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = ((2 : ZMod 777012787) ^ 49 * (2 : ZMod 777012787) ^ 49) * (2 : ZMod 777012787) := by rw [pow_succ, pow_add]
          _ = 511915422 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 777012787) ^ 198 = 660817451 := by
        calc
          (2 : ZMod 777012787) ^ 198 = (2 : ZMod 777012787) ^ (99 + 99) :=
            congrArg (fun n : ℕ => (2 : ZMod 777012787) ^ n) (by norm_num)
          _ = (2 : ZMod 777012787) ^ 99 * (2 : ZMod 777012787) ^ 99 := by rw [pow_add]
          _ = 660817451 := by rw [factor_3_6]; decide
      change (2 : ZMod 777012787) ^ 198 ≠ 1
      rw [factor_3_7]
      decide

#print axioms prime_lucas_777012787

end TotientTailPeriodKiller
end Erdos249257
