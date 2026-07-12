import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=23 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_892371481 : Nat.Prime 892371481 := by
  apply lucas_primality 892371481 (58 : ZMod 892371481)
  ·
      have fermat_0 : (58 : ZMod 892371481) ^ 1 = 58 := by norm_num
      have fermat_1 : (58 : ZMod 892371481) ^ 3 = 195112 := by
        calc
          (58 : ZMod 892371481) ^ 3 = (58 : ZMod 892371481) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 1 * (58 : ZMod 892371481) ^ 1) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 195112 := by rw [fermat_0]; decide
      have fermat_2 : (58 : ZMod 892371481) ^ 6 = 589090342 := by
        calc
          (58 : ZMod 892371481) ^ 6 = (58 : ZMod 892371481) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 3 * (58 : ZMod 892371481) ^ 3 := by rw [pow_add]
          _ = 589090342 := by rw [fermat_1]; decide
      have fermat_3 : (58 : ZMod 892371481) ^ 13 = 516633464 := by
        calc
          (58 : ZMod 892371481) ^ 13 = (58 : ZMod 892371481) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 6 * (58 : ZMod 892371481) ^ 6) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 516633464 := by rw [fermat_2]; decide
      have fermat_4 : (58 : ZMod 892371481) ^ 26 = 365489170 := by
        calc
          (58 : ZMod 892371481) ^ 26 = (58 : ZMod 892371481) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 13 * (58 : ZMod 892371481) ^ 13 := by rw [pow_add]
          _ = 365489170 := by rw [fermat_3]; decide
      have fermat_5 : (58 : ZMod 892371481) ^ 53 = 608645200 := by
        calc
          (58 : ZMod 892371481) ^ 53 = (58 : ZMod 892371481) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 26 * (58 : ZMod 892371481) ^ 26) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 608645200 := by rw [fermat_4]; decide
      have fermat_6 : (58 : ZMod 892371481) ^ 106 = 568551578 := by
        calc
          (58 : ZMod 892371481) ^ 106 = (58 : ZMod 892371481) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 53 * (58 : ZMod 892371481) ^ 53 := by rw [pow_add]
          _ = 568551578 := by rw [fermat_5]; decide
      have fermat_7 : (58 : ZMod 892371481) ^ 212 = 616952844 := by
        calc
          (58 : ZMod 892371481) ^ 212 = (58 : ZMod 892371481) ^ (106 + 106) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 106 * (58 : ZMod 892371481) ^ 106 := by rw [pow_add]
          _ = 616952844 := by rw [fermat_6]; decide
      have fermat_8 : (58 : ZMod 892371481) ^ 425 = 34643668 := by
        calc
          (58 : ZMod 892371481) ^ 425 = (58 : ZMod 892371481) ^ (212 + 212 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 212 * (58 : ZMod 892371481) ^ 212) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 34643668 := by rw [fermat_7]; decide
      have fermat_9 : (58 : ZMod 892371481) ^ 851 = 129816946 := by
        calc
          (58 : ZMod 892371481) ^ 851 = (58 : ZMod 892371481) ^ (425 + 425 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 425 * (58 : ZMod 892371481) ^ 425) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 129816946 := by rw [fermat_8]; decide
      have fermat_10 : (58 : ZMod 892371481) ^ 1702 = 480595992 := by
        calc
          (58 : ZMod 892371481) ^ 1702 = (58 : ZMod 892371481) ^ (851 + 851) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 851 * (58 : ZMod 892371481) ^ 851 := by rw [pow_add]
          _ = 480595992 := by rw [fermat_9]; decide
      have fermat_11 : (58 : ZMod 892371481) ^ 3404 = 668719988 := by
        calc
          (58 : ZMod 892371481) ^ 3404 = (58 : ZMod 892371481) ^ (1702 + 1702) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1702 * (58 : ZMod 892371481) ^ 1702 := by rw [pow_add]
          _ = 668719988 := by rw [fermat_10]; decide
      have fermat_12 : (58 : ZMod 892371481) ^ 6808 = 565956731 := by
        calc
          (58 : ZMod 892371481) ^ 6808 = (58 : ZMod 892371481) ^ (3404 + 3404) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 3404 * (58 : ZMod 892371481) ^ 3404 := by rw [pow_add]
          _ = 565956731 := by rw [fermat_11]; decide
      have fermat_13 : (58 : ZMod 892371481) ^ 13616 = 646541856 := by
        calc
          (58 : ZMod 892371481) ^ 13616 = (58 : ZMod 892371481) ^ (6808 + 6808) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 6808 * (58 : ZMod 892371481) ^ 6808 := by rw [pow_add]
          _ = 646541856 := by rw [fermat_12]; decide
      have fermat_14 : (58 : ZMod 892371481) ^ 27233 = 425986345 := by
        calc
          (58 : ZMod 892371481) ^ 27233 = (58 : ZMod 892371481) ^ (13616 + 13616 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 13616 * (58 : ZMod 892371481) ^ 13616) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 425986345 := by rw [fermat_13]; decide
      have fermat_15 : (58 : ZMod 892371481) ^ 54466 = 805072325 := by
        calc
          (58 : ZMod 892371481) ^ 54466 = (58 : ZMod 892371481) ^ (27233 + 27233) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 27233 * (58 : ZMod 892371481) ^ 27233 := by rw [pow_add]
          _ = 805072325 := by rw [fermat_14]; decide
      have fermat_16 : (58 : ZMod 892371481) ^ 108932 = 169841011 := by
        calc
          (58 : ZMod 892371481) ^ 108932 = (58 : ZMod 892371481) ^ (54466 + 54466) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 54466 * (58 : ZMod 892371481) ^ 54466 := by rw [pow_add]
          _ = 169841011 := by rw [fermat_15]; decide
      have fermat_17 : (58 : ZMod 892371481) ^ 217864 = 212916413 := by
        calc
          (58 : ZMod 892371481) ^ 217864 = (58 : ZMod 892371481) ^ (108932 + 108932) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 108932 * (58 : ZMod 892371481) ^ 108932 := by rw [pow_add]
          _ = 212916413 := by rw [fermat_16]; decide
      have fermat_18 : (58 : ZMod 892371481) ^ 435728 = 516017810 := by
        calc
          (58 : ZMod 892371481) ^ 435728 = (58 : ZMod 892371481) ^ (217864 + 217864) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 217864 * (58 : ZMod 892371481) ^ 217864 := by rw [pow_add]
          _ = 516017810 := by rw [fermat_17]; decide
      have fermat_19 : (58 : ZMod 892371481) ^ 871456 = 261740728 := by
        calc
          (58 : ZMod 892371481) ^ 871456 = (58 : ZMod 892371481) ^ (435728 + 435728) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 435728 * (58 : ZMod 892371481) ^ 435728 := by rw [pow_add]
          _ = 261740728 := by rw [fermat_18]; decide
      have fermat_20 : (58 : ZMod 892371481) ^ 1742913 = 351730860 := by
        calc
          (58 : ZMod 892371481) ^ 1742913 = (58 : ZMod 892371481) ^ (871456 + 871456 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 871456 * (58 : ZMod 892371481) ^ 871456) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 351730860 := by rw [fermat_19]; decide
      have fermat_21 : (58 : ZMod 892371481) ^ 3485826 = 297950521 := by
        calc
          (58 : ZMod 892371481) ^ 3485826 = (58 : ZMod 892371481) ^ (1742913 + 1742913) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1742913 * (58 : ZMod 892371481) ^ 1742913 := by rw [pow_add]
          _ = 297950521 := by rw [fermat_20]; decide
      have fermat_22 : (58 : ZMod 892371481) ^ 6971652 = 580552195 := by
        calc
          (58 : ZMod 892371481) ^ 6971652 = (58 : ZMod 892371481) ^ (3485826 + 3485826) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 3485826 * (58 : ZMod 892371481) ^ 3485826 := by rw [pow_add]
          _ = 580552195 := by rw [fermat_21]; decide
      have fermat_23 : (58 : ZMod 892371481) ^ 13943304 = 76508230 := by
        calc
          (58 : ZMod 892371481) ^ 13943304 = (58 : ZMod 892371481) ^ (6971652 + 6971652) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 6971652 * (58 : ZMod 892371481) ^ 6971652 := by rw [pow_add]
          _ = 76508230 := by rw [fermat_22]; decide
      have fermat_24 : (58 : ZMod 892371481) ^ 27886608 = 312856362 := by
        calc
          (58 : ZMod 892371481) ^ 27886608 = (58 : ZMod 892371481) ^ (13943304 + 13943304) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 13943304 * (58 : ZMod 892371481) ^ 13943304 := by rw [pow_add]
          _ = 312856362 := by rw [fermat_23]; decide
      have fermat_25 : (58 : ZMod 892371481) ^ 55773217 = 762309222 := by
        calc
          (58 : ZMod 892371481) ^ 55773217 = (58 : ZMod 892371481) ^ (27886608 + 27886608 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 27886608 * (58 : ZMod 892371481) ^ 27886608) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 762309222 := by rw [fermat_24]; decide
      have fermat_26 : (58 : ZMod 892371481) ^ 111546435 = 540776468 := by
        calc
          (58 : ZMod 892371481) ^ 111546435 = (58 : ZMod 892371481) ^ (55773217 + 55773217 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 55773217 * (58 : ZMod 892371481) ^ 55773217) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 540776468 := by rw [fermat_25]; decide
      have fermat_27 : (58 : ZMod 892371481) ^ 223092870 = 17808798 := by
        calc
          (58 : ZMod 892371481) ^ 223092870 = (58 : ZMod 892371481) ^ (111546435 + 111546435) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 111546435 * (58 : ZMod 892371481) ^ 111546435 := by rw [pow_add]
          _ = 17808798 := by rw [fermat_26]; decide
      have fermat_28 : (58 : ZMod 892371481) ^ 446185740 = 892371480 := by
        calc
          (58 : ZMod 892371481) ^ 446185740 = (58 : ZMod 892371481) ^ (223092870 + 223092870) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 223092870 * (58 : ZMod 892371481) ^ 223092870 := by rw [pow_add]
          _ = 892371480 := by rw [fermat_27]; decide
      have fermat_29 : (58 : ZMod 892371481) ^ 892371480 = 1 := by
        calc
          (58 : ZMod 892371481) ^ 892371480 = (58 : ZMod 892371481) ^ (446185740 + 446185740) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 446185740 * (58 : ZMod 892371481) ^ 446185740 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 892371481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (58 : ZMod 892371481) ^ 1 = 58 := by norm_num
      have factor_0_1 : (58 : ZMod 892371481) ^ 3 = 195112 := by
        calc
          (58 : ZMod 892371481) ^ 3 = (58 : ZMod 892371481) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 1 * (58 : ZMod 892371481) ^ 1) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 195112 := by rw [factor_0_0]; decide
      have factor_0_2 : (58 : ZMod 892371481) ^ 6 = 589090342 := by
        calc
          (58 : ZMod 892371481) ^ 6 = (58 : ZMod 892371481) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 3 * (58 : ZMod 892371481) ^ 3 := by rw [pow_add]
          _ = 589090342 := by rw [factor_0_1]; decide
      have factor_0_3 : (58 : ZMod 892371481) ^ 13 = 516633464 := by
        calc
          (58 : ZMod 892371481) ^ 13 = (58 : ZMod 892371481) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 6 * (58 : ZMod 892371481) ^ 6) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 516633464 := by rw [factor_0_2]; decide
      have factor_0_4 : (58 : ZMod 892371481) ^ 26 = 365489170 := by
        calc
          (58 : ZMod 892371481) ^ 26 = (58 : ZMod 892371481) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 13 * (58 : ZMod 892371481) ^ 13 := by rw [pow_add]
          _ = 365489170 := by rw [factor_0_3]; decide
      have factor_0_5 : (58 : ZMod 892371481) ^ 53 = 608645200 := by
        calc
          (58 : ZMod 892371481) ^ 53 = (58 : ZMod 892371481) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 26 * (58 : ZMod 892371481) ^ 26) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 608645200 := by rw [factor_0_4]; decide
      have factor_0_6 : (58 : ZMod 892371481) ^ 106 = 568551578 := by
        calc
          (58 : ZMod 892371481) ^ 106 = (58 : ZMod 892371481) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 53 * (58 : ZMod 892371481) ^ 53 := by rw [pow_add]
          _ = 568551578 := by rw [factor_0_5]; decide
      have factor_0_7 : (58 : ZMod 892371481) ^ 212 = 616952844 := by
        calc
          (58 : ZMod 892371481) ^ 212 = (58 : ZMod 892371481) ^ (106 + 106) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 106 * (58 : ZMod 892371481) ^ 106 := by rw [pow_add]
          _ = 616952844 := by rw [factor_0_6]; decide
      have factor_0_8 : (58 : ZMod 892371481) ^ 425 = 34643668 := by
        calc
          (58 : ZMod 892371481) ^ 425 = (58 : ZMod 892371481) ^ (212 + 212 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 212 * (58 : ZMod 892371481) ^ 212) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 34643668 := by rw [factor_0_7]; decide
      have factor_0_9 : (58 : ZMod 892371481) ^ 851 = 129816946 := by
        calc
          (58 : ZMod 892371481) ^ 851 = (58 : ZMod 892371481) ^ (425 + 425 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 425 * (58 : ZMod 892371481) ^ 425) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 129816946 := by rw [factor_0_8]; decide
      have factor_0_10 : (58 : ZMod 892371481) ^ 1702 = 480595992 := by
        calc
          (58 : ZMod 892371481) ^ 1702 = (58 : ZMod 892371481) ^ (851 + 851) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 851 * (58 : ZMod 892371481) ^ 851 := by rw [pow_add]
          _ = 480595992 := by rw [factor_0_9]; decide
      have factor_0_11 : (58 : ZMod 892371481) ^ 3404 = 668719988 := by
        calc
          (58 : ZMod 892371481) ^ 3404 = (58 : ZMod 892371481) ^ (1702 + 1702) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1702 * (58 : ZMod 892371481) ^ 1702 := by rw [pow_add]
          _ = 668719988 := by rw [factor_0_10]; decide
      have factor_0_12 : (58 : ZMod 892371481) ^ 6808 = 565956731 := by
        calc
          (58 : ZMod 892371481) ^ 6808 = (58 : ZMod 892371481) ^ (3404 + 3404) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 3404 * (58 : ZMod 892371481) ^ 3404 := by rw [pow_add]
          _ = 565956731 := by rw [factor_0_11]; decide
      have factor_0_13 : (58 : ZMod 892371481) ^ 13616 = 646541856 := by
        calc
          (58 : ZMod 892371481) ^ 13616 = (58 : ZMod 892371481) ^ (6808 + 6808) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 6808 * (58 : ZMod 892371481) ^ 6808 := by rw [pow_add]
          _ = 646541856 := by rw [factor_0_12]; decide
      have factor_0_14 : (58 : ZMod 892371481) ^ 27233 = 425986345 := by
        calc
          (58 : ZMod 892371481) ^ 27233 = (58 : ZMod 892371481) ^ (13616 + 13616 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 13616 * (58 : ZMod 892371481) ^ 13616) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 425986345 := by rw [factor_0_13]; decide
      have factor_0_15 : (58 : ZMod 892371481) ^ 54466 = 805072325 := by
        calc
          (58 : ZMod 892371481) ^ 54466 = (58 : ZMod 892371481) ^ (27233 + 27233) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 27233 * (58 : ZMod 892371481) ^ 27233 := by rw [pow_add]
          _ = 805072325 := by rw [factor_0_14]; decide
      have factor_0_16 : (58 : ZMod 892371481) ^ 108932 = 169841011 := by
        calc
          (58 : ZMod 892371481) ^ 108932 = (58 : ZMod 892371481) ^ (54466 + 54466) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 54466 * (58 : ZMod 892371481) ^ 54466 := by rw [pow_add]
          _ = 169841011 := by rw [factor_0_15]; decide
      have factor_0_17 : (58 : ZMod 892371481) ^ 217864 = 212916413 := by
        calc
          (58 : ZMod 892371481) ^ 217864 = (58 : ZMod 892371481) ^ (108932 + 108932) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 108932 * (58 : ZMod 892371481) ^ 108932 := by rw [pow_add]
          _ = 212916413 := by rw [factor_0_16]; decide
      have factor_0_18 : (58 : ZMod 892371481) ^ 435728 = 516017810 := by
        calc
          (58 : ZMod 892371481) ^ 435728 = (58 : ZMod 892371481) ^ (217864 + 217864) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 217864 * (58 : ZMod 892371481) ^ 217864 := by rw [pow_add]
          _ = 516017810 := by rw [factor_0_17]; decide
      have factor_0_19 : (58 : ZMod 892371481) ^ 871456 = 261740728 := by
        calc
          (58 : ZMod 892371481) ^ 871456 = (58 : ZMod 892371481) ^ (435728 + 435728) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 435728 * (58 : ZMod 892371481) ^ 435728 := by rw [pow_add]
          _ = 261740728 := by rw [factor_0_18]; decide
      have factor_0_20 : (58 : ZMod 892371481) ^ 1742913 = 351730860 := by
        calc
          (58 : ZMod 892371481) ^ 1742913 = (58 : ZMod 892371481) ^ (871456 + 871456 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 871456 * (58 : ZMod 892371481) ^ 871456) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 351730860 := by rw [factor_0_19]; decide
      have factor_0_21 : (58 : ZMod 892371481) ^ 3485826 = 297950521 := by
        calc
          (58 : ZMod 892371481) ^ 3485826 = (58 : ZMod 892371481) ^ (1742913 + 1742913) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1742913 * (58 : ZMod 892371481) ^ 1742913 := by rw [pow_add]
          _ = 297950521 := by rw [factor_0_20]; decide
      have factor_0_22 : (58 : ZMod 892371481) ^ 6971652 = 580552195 := by
        calc
          (58 : ZMod 892371481) ^ 6971652 = (58 : ZMod 892371481) ^ (3485826 + 3485826) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 3485826 * (58 : ZMod 892371481) ^ 3485826 := by rw [pow_add]
          _ = 580552195 := by rw [factor_0_21]; decide
      have factor_0_23 : (58 : ZMod 892371481) ^ 13943304 = 76508230 := by
        calc
          (58 : ZMod 892371481) ^ 13943304 = (58 : ZMod 892371481) ^ (6971652 + 6971652) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 6971652 * (58 : ZMod 892371481) ^ 6971652 := by rw [pow_add]
          _ = 76508230 := by rw [factor_0_22]; decide
      have factor_0_24 : (58 : ZMod 892371481) ^ 27886608 = 312856362 := by
        calc
          (58 : ZMod 892371481) ^ 27886608 = (58 : ZMod 892371481) ^ (13943304 + 13943304) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 13943304 * (58 : ZMod 892371481) ^ 13943304 := by rw [pow_add]
          _ = 312856362 := by rw [factor_0_23]; decide
      have factor_0_25 : (58 : ZMod 892371481) ^ 55773217 = 762309222 := by
        calc
          (58 : ZMod 892371481) ^ 55773217 = (58 : ZMod 892371481) ^ (27886608 + 27886608 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 27886608 * (58 : ZMod 892371481) ^ 27886608) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 762309222 := by rw [factor_0_24]; decide
      have factor_0_26 : (58 : ZMod 892371481) ^ 111546435 = 540776468 := by
        calc
          (58 : ZMod 892371481) ^ 111546435 = (58 : ZMod 892371481) ^ (55773217 + 55773217 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 55773217 * (58 : ZMod 892371481) ^ 55773217) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 540776468 := by rw [factor_0_25]; decide
      have factor_0_27 : (58 : ZMod 892371481) ^ 223092870 = 17808798 := by
        calc
          (58 : ZMod 892371481) ^ 223092870 = (58 : ZMod 892371481) ^ (111546435 + 111546435) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 111546435 * (58 : ZMod 892371481) ^ 111546435 := by rw [pow_add]
          _ = 17808798 := by rw [factor_0_26]; decide
      have factor_0_28 : (58 : ZMod 892371481) ^ 446185740 = 892371480 := by
        calc
          (58 : ZMod 892371481) ^ 446185740 = (58 : ZMod 892371481) ^ (223092870 + 223092870) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 223092870 * (58 : ZMod 892371481) ^ 223092870 := by rw [pow_add]
          _ = 892371480 := by rw [factor_0_27]; decide
      change (58 : ZMod 892371481) ^ 446185740 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (58 : ZMod 892371481) ^ 1 = 58 := by norm_num
      have factor_1_1 : (58 : ZMod 892371481) ^ 2 = 3364 := by
        calc
          (58 : ZMod 892371481) ^ 2 = (58 : ZMod 892371481) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1 * (58 : ZMod 892371481) ^ 1 := by rw [pow_add]
          _ = 3364 := by rw [factor_1_0]; decide
      have factor_1_2 : (58 : ZMod 892371481) ^ 4 = 11316496 := by
        calc
          (58 : ZMod 892371481) ^ 4 = (58 : ZMod 892371481) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 2 * (58 : ZMod 892371481) ^ 2 := by rw [pow_add]
          _ = 11316496 := by rw [factor_1_1]; decide
      have factor_1_3 : (58 : ZMod 892371481) ^ 8 = 635222668 := by
        calc
          (58 : ZMod 892371481) ^ 8 = (58 : ZMod 892371481) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 4 * (58 : ZMod 892371481) ^ 4 := by rw [pow_add]
          _ = 635222668 := by rw [factor_1_2]; decide
      have factor_1_4 : (58 : ZMod 892371481) ^ 17 = 794101443 := by
        calc
          (58 : ZMod 892371481) ^ 17 = (58 : ZMod 892371481) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 8 * (58 : ZMod 892371481) ^ 8) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 794101443 := by rw [factor_1_3]; decide
      have factor_1_5 : (58 : ZMod 892371481) ^ 35 = 184575678 := by
        calc
          (58 : ZMod 892371481) ^ 35 = (58 : ZMod 892371481) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 17 * (58 : ZMod 892371481) ^ 17) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 184575678 := by rw [factor_1_4]; decide
      have factor_1_6 : (58 : ZMod 892371481) ^ 70 = 655473116 := by
        calc
          (58 : ZMod 892371481) ^ 70 = (58 : ZMod 892371481) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 35 * (58 : ZMod 892371481) ^ 35 := by rw [pow_add]
          _ = 655473116 := by rw [factor_1_5]; decide
      have factor_1_7 : (58 : ZMod 892371481) ^ 141 = 325214310 := by
        calc
          (58 : ZMod 892371481) ^ 141 = (58 : ZMod 892371481) ^ (70 + 70 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 70 * (58 : ZMod 892371481) ^ 70) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 325214310 := by rw [factor_1_6]; decide
      have factor_1_8 : (58 : ZMod 892371481) ^ 283 = 280848435 := by
        calc
          (58 : ZMod 892371481) ^ 283 = (58 : ZMod 892371481) ^ (141 + 141 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 141 * (58 : ZMod 892371481) ^ 141) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 280848435 := by rw [factor_1_7]; decide
      have factor_1_9 : (58 : ZMod 892371481) ^ 567 = 369319991 := by
        calc
          (58 : ZMod 892371481) ^ 567 = (58 : ZMod 892371481) ^ (283 + 283 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 283 * (58 : ZMod 892371481) ^ 283) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 369319991 := by rw [factor_1_8]; decide
      have factor_1_10 : (58 : ZMod 892371481) ^ 1134 = 727834335 := by
        calc
          (58 : ZMod 892371481) ^ 1134 = (58 : ZMod 892371481) ^ (567 + 567) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 567 * (58 : ZMod 892371481) ^ 567 := by rw [pow_add]
          _ = 727834335 := by rw [factor_1_9]; decide
      have factor_1_11 : (58 : ZMod 892371481) ^ 2269 = 780944770 := by
        calc
          (58 : ZMod 892371481) ^ 2269 = (58 : ZMod 892371481) ^ (1134 + 1134 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 1134 * (58 : ZMod 892371481) ^ 1134) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 780944770 := by rw [factor_1_10]; decide
      have factor_1_12 : (58 : ZMod 892371481) ^ 4538 = 376618412 := by
        calc
          (58 : ZMod 892371481) ^ 4538 = (58 : ZMod 892371481) ^ (2269 + 2269) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 2269 * (58 : ZMod 892371481) ^ 2269 := by rw [pow_add]
          _ = 376618412 := by rw [factor_1_11]; decide
      have factor_1_13 : (58 : ZMod 892371481) ^ 9077 = 573215200 := by
        calc
          (58 : ZMod 892371481) ^ 9077 = (58 : ZMod 892371481) ^ (4538 + 4538 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 4538 * (58 : ZMod 892371481) ^ 4538) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 573215200 := by rw [factor_1_12]; decide
      have factor_1_14 : (58 : ZMod 892371481) ^ 18155 = 535547058 := by
        calc
          (58 : ZMod 892371481) ^ 18155 = (58 : ZMod 892371481) ^ (9077 + 9077 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 9077 * (58 : ZMod 892371481) ^ 9077) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 535547058 := by rw [factor_1_13]; decide
      have factor_1_15 : (58 : ZMod 892371481) ^ 36310 = 640368171 := by
        calc
          (58 : ZMod 892371481) ^ 36310 = (58 : ZMod 892371481) ^ (18155 + 18155) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 18155 * (58 : ZMod 892371481) ^ 18155 := by rw [pow_add]
          _ = 640368171 := by rw [factor_1_14]; decide
      have factor_1_16 : (58 : ZMod 892371481) ^ 72621 = 109507273 := by
        calc
          (58 : ZMod 892371481) ^ 72621 = (58 : ZMod 892371481) ^ (36310 + 36310 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 36310 * (58 : ZMod 892371481) ^ 36310) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 109507273 := by rw [factor_1_15]; decide
      have factor_1_17 : (58 : ZMod 892371481) ^ 145242 = 497952316 := by
        calc
          (58 : ZMod 892371481) ^ 145242 = (58 : ZMod 892371481) ^ (72621 + 72621) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 72621 * (58 : ZMod 892371481) ^ 72621 := by rw [pow_add]
          _ = 497952316 := by rw [factor_1_16]; decide
      have factor_1_18 : (58 : ZMod 892371481) ^ 290485 = 323431534 := by
        calc
          (58 : ZMod 892371481) ^ 290485 = (58 : ZMod 892371481) ^ (145242 + 145242 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 145242 * (58 : ZMod 892371481) ^ 145242) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 323431534 := by rw [factor_1_17]; decide
      have factor_1_19 : (58 : ZMod 892371481) ^ 580971 = 441597316 := by
        calc
          (58 : ZMod 892371481) ^ 580971 = (58 : ZMod 892371481) ^ (290485 + 290485 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 290485 * (58 : ZMod 892371481) ^ 290485) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 441597316 := by rw [factor_1_18]; decide
      have factor_1_20 : (58 : ZMod 892371481) ^ 1161942 = 588319578 := by
        calc
          (58 : ZMod 892371481) ^ 1161942 = (58 : ZMod 892371481) ^ (580971 + 580971) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 580971 * (58 : ZMod 892371481) ^ 580971 := by rw [pow_add]
          _ = 588319578 := by rw [factor_1_19]; decide
      have factor_1_21 : (58 : ZMod 892371481) ^ 2323884 = 807560632 := by
        calc
          (58 : ZMod 892371481) ^ 2323884 = (58 : ZMod 892371481) ^ (1161942 + 1161942) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1161942 * (58 : ZMod 892371481) ^ 1161942 := by rw [pow_add]
          _ = 807560632 := by rw [factor_1_20]; decide
      have factor_1_22 : (58 : ZMod 892371481) ^ 4647768 = 98933591 := by
        calc
          (58 : ZMod 892371481) ^ 4647768 = (58 : ZMod 892371481) ^ (2323884 + 2323884) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 2323884 * (58 : ZMod 892371481) ^ 2323884 := by rw [pow_add]
          _ = 98933591 := by rw [factor_1_21]; decide
      have factor_1_23 : (58 : ZMod 892371481) ^ 9295536 = 201328197 := by
        calc
          (58 : ZMod 892371481) ^ 9295536 = (58 : ZMod 892371481) ^ (4647768 + 4647768) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 4647768 * (58 : ZMod 892371481) ^ 4647768 := by rw [pow_add]
          _ = 201328197 := by rw [factor_1_22]; decide
      have factor_1_24 : (58 : ZMod 892371481) ^ 18591072 = 715532375 := by
        calc
          (58 : ZMod 892371481) ^ 18591072 = (58 : ZMod 892371481) ^ (9295536 + 9295536) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 9295536 * (58 : ZMod 892371481) ^ 9295536 := by rw [pow_add]
          _ = 715532375 := by rw [factor_1_23]; decide
      have factor_1_25 : (58 : ZMod 892371481) ^ 37182145 = 812725678 := by
        calc
          (58 : ZMod 892371481) ^ 37182145 = (58 : ZMod 892371481) ^ (18591072 + 18591072 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 18591072 * (58 : ZMod 892371481) ^ 18591072) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 812725678 := by rw [factor_1_24]; decide
      have factor_1_26 : (58 : ZMod 892371481) ^ 74364290 = 29824474 := by
        calc
          (58 : ZMod 892371481) ^ 74364290 = (58 : ZMod 892371481) ^ (37182145 + 37182145) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 37182145 * (58 : ZMod 892371481) ^ 37182145 := by rw [pow_add]
          _ = 29824474 := by rw [factor_1_25]; decide
      have factor_1_27 : (58 : ZMod 892371481) ^ 148728580 = 312174015 := by
        calc
          (58 : ZMod 892371481) ^ 148728580 = (58 : ZMod 892371481) ^ (74364290 + 74364290) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 74364290 * (58 : ZMod 892371481) ^ 74364290 := by rw [pow_add]
          _ = 312174015 := by rw [factor_1_26]; decide
      have factor_1_28 : (58 : ZMod 892371481) ^ 297457160 = 312174014 := by
        calc
          (58 : ZMod 892371481) ^ 297457160 = (58 : ZMod 892371481) ^ (148728580 + 148728580) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 148728580 * (58 : ZMod 892371481) ^ 148728580 := by rw [pow_add]
          _ = 312174014 := by rw [factor_1_27]; decide
      change (58 : ZMod 892371481) ^ 297457160 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (58 : ZMod 892371481) ^ 1 = 58 := by norm_num
      have factor_2_1 : (58 : ZMod 892371481) ^ 2 = 3364 := by
        calc
          (58 : ZMod 892371481) ^ 2 = (58 : ZMod 892371481) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1 * (58 : ZMod 892371481) ^ 1 := by rw [pow_add]
          _ = 3364 := by rw [factor_2_0]; decide
      have factor_2_2 : (58 : ZMod 892371481) ^ 5 = 656356768 := by
        calc
          (58 : ZMod 892371481) ^ 5 = (58 : ZMod 892371481) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 2 * (58 : ZMod 892371481) ^ 2) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 656356768 := by rw [factor_2_1]; decide
      have factor_2_3 : (58 : ZMod 892371481) ^ 10 = 551729638 := by
        calc
          (58 : ZMod 892371481) ^ 10 = (58 : ZMod 892371481) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 5 * (58 : ZMod 892371481) ^ 5 := by rw [pow_add]
          _ = 551729638 := by rw [factor_2_2]; decide
      have factor_2_4 : (58 : ZMod 892371481) ^ 21 = 847675352 := by
        calc
          (58 : ZMod 892371481) ^ 21 = (58 : ZMod 892371481) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 10 * (58 : ZMod 892371481) ^ 10) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 847675352 := by rw [factor_2_3]; decide
      have factor_2_5 : (58 : ZMod 892371481) ^ 42 = 836784751 := by
        calc
          (58 : ZMod 892371481) ^ 42 = (58 : ZMod 892371481) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 21 * (58 : ZMod 892371481) ^ 21 := by rw [pow_add]
          _ = 836784751 := by rw [factor_2_4]; decide
      have factor_2_6 : (58 : ZMod 892371481) ^ 85 = 195484341 := by
        calc
          (58 : ZMod 892371481) ^ 85 = (58 : ZMod 892371481) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 42 * (58 : ZMod 892371481) ^ 42) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 195484341 := by rw [factor_2_5]; decide
      have factor_2_7 : (58 : ZMod 892371481) ^ 170 = 130249485 := by
        calc
          (58 : ZMod 892371481) ^ 170 = (58 : ZMod 892371481) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 85 * (58 : ZMod 892371481) ^ 85 := by rw [pow_add]
          _ = 130249485 := by rw [factor_2_6]; decide
      have factor_2_8 : (58 : ZMod 892371481) ^ 340 = 575185365 := by
        calc
          (58 : ZMod 892371481) ^ 340 = (58 : ZMod 892371481) ^ (170 + 170) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 170 * (58 : ZMod 892371481) ^ 170 := by rw [pow_add]
          _ = 575185365 := by rw [factor_2_7]; decide
      have factor_2_9 : (58 : ZMod 892371481) ^ 680 = 569448256 := by
        calc
          (58 : ZMod 892371481) ^ 680 = (58 : ZMod 892371481) ^ (340 + 340) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 340 * (58 : ZMod 892371481) ^ 340 := by rw [pow_add]
          _ = 569448256 := by rw [factor_2_8]; decide
      have factor_2_10 : (58 : ZMod 892371481) ^ 1361 = 771137808 := by
        calc
          (58 : ZMod 892371481) ^ 1361 = (58 : ZMod 892371481) ^ (680 + 680 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 680 * (58 : ZMod 892371481) ^ 680) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 771137808 := by rw [factor_2_9]; decide
      have factor_2_11 : (58 : ZMod 892371481) ^ 2723 = 326504147 := by
        calc
          (58 : ZMod 892371481) ^ 2723 = (58 : ZMod 892371481) ^ (1361 + 1361 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 1361 * (58 : ZMod 892371481) ^ 1361) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 326504147 := by rw [factor_2_10]; decide
      have factor_2_12 : (58 : ZMod 892371481) ^ 5446 = 510976236 := by
        calc
          (58 : ZMod 892371481) ^ 5446 = (58 : ZMod 892371481) ^ (2723 + 2723) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 2723 * (58 : ZMod 892371481) ^ 2723 := by rw [pow_add]
          _ = 510976236 := by rw [factor_2_11]; decide
      have factor_2_13 : (58 : ZMod 892371481) ^ 10893 = 1594599 := by
        calc
          (58 : ZMod 892371481) ^ 10893 = (58 : ZMod 892371481) ^ (5446 + 5446 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 5446 * (58 : ZMod 892371481) ^ 5446) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 1594599 := by rw [factor_2_12]; decide
      have factor_2_14 : (58 : ZMod 892371481) ^ 21786 = 379621432 := by
        calc
          (58 : ZMod 892371481) ^ 21786 = (58 : ZMod 892371481) ^ (10893 + 10893) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 10893 * (58 : ZMod 892371481) ^ 10893 := by rw [pow_add]
          _ = 379621432 := by rw [factor_2_13]; decide
      have factor_2_15 : (58 : ZMod 892371481) ^ 43572 = 496043178 := by
        calc
          (58 : ZMod 892371481) ^ 43572 = (58 : ZMod 892371481) ^ (21786 + 21786) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 21786 * (58 : ZMod 892371481) ^ 21786 := by rw [pow_add]
          _ = 496043178 := by rw [factor_2_14]; decide
      have factor_2_16 : (58 : ZMod 892371481) ^ 87145 = 534513988 := by
        calc
          (58 : ZMod 892371481) ^ 87145 = (58 : ZMod 892371481) ^ (43572 + 43572 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 43572 * (58 : ZMod 892371481) ^ 43572) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 534513988 := by rw [factor_2_15]; decide
      have factor_2_17 : (58 : ZMod 892371481) ^ 174291 = 179543298 := by
        calc
          (58 : ZMod 892371481) ^ 174291 = (58 : ZMod 892371481) ^ (87145 + 87145 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 87145 * (58 : ZMod 892371481) ^ 87145) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 179543298 := by rw [factor_2_16]; decide
      have factor_2_18 : (58 : ZMod 892371481) ^ 348582 = 493657864 := by
        calc
          (58 : ZMod 892371481) ^ 348582 = (58 : ZMod 892371481) ^ (174291 + 174291) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 174291 * (58 : ZMod 892371481) ^ 174291 := by rw [pow_add]
          _ = 493657864 := by rw [factor_2_17]; decide
      have factor_2_19 : (58 : ZMod 892371481) ^ 697165 = 545364519 := by
        calc
          (58 : ZMod 892371481) ^ 697165 = (58 : ZMod 892371481) ^ (348582 + 348582 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 348582 * (58 : ZMod 892371481) ^ 348582) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 545364519 := by rw [factor_2_18]; decide
      have factor_2_20 : (58 : ZMod 892371481) ^ 1394330 = 198006835 := by
        calc
          (58 : ZMod 892371481) ^ 1394330 = (58 : ZMod 892371481) ^ (697165 + 697165) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 697165 * (58 : ZMod 892371481) ^ 697165 := by rw [pow_add]
          _ = 198006835 := by rw [factor_2_19]; decide
      have factor_2_21 : (58 : ZMod 892371481) ^ 2788660 = 709046496 := by
        calc
          (58 : ZMod 892371481) ^ 2788660 = (58 : ZMod 892371481) ^ (1394330 + 1394330) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1394330 * (58 : ZMod 892371481) ^ 1394330 := by rw [pow_add]
          _ = 709046496 := by rw [factor_2_20]; decide
      have factor_2_22 : (58 : ZMod 892371481) ^ 5577321 = 512723507 := by
        calc
          (58 : ZMod 892371481) ^ 5577321 = (58 : ZMod 892371481) ^ (2788660 + 2788660 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 2788660 * (58 : ZMod 892371481) ^ 2788660) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 512723507 := by rw [factor_2_21]; decide
      have factor_2_23 : (58 : ZMod 892371481) ^ 11154643 = 858668528 := by
        calc
          (58 : ZMod 892371481) ^ 11154643 = (58 : ZMod 892371481) ^ (5577321 + 5577321 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 5577321 * (58 : ZMod 892371481) ^ 5577321) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 858668528 := by rw [factor_2_22]; decide
      have factor_2_24 : (58 : ZMod 892371481) ^ 22309287 = 828501293 := by
        calc
          (58 : ZMod 892371481) ^ 22309287 = (58 : ZMod 892371481) ^ (11154643 + 11154643 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 11154643 * (58 : ZMod 892371481) ^ 11154643) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 828501293 := by rw [factor_2_23]; decide
      have factor_2_25 : (58 : ZMod 892371481) ^ 44618574 = 541339729 := by
        calc
          (58 : ZMod 892371481) ^ 44618574 = (58 : ZMod 892371481) ^ (22309287 + 22309287) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 22309287 * (58 : ZMod 892371481) ^ 22309287 := by rw [pow_add]
          _ = 541339729 := by rw [factor_2_24]; decide
      have factor_2_26 : (58 : ZMod 892371481) ^ 89237148 = 53494228 := by
        calc
          (58 : ZMod 892371481) ^ 89237148 = (58 : ZMod 892371481) ^ (44618574 + 44618574) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 44618574 * (58 : ZMod 892371481) ^ 44618574 := by rw [pow_add]
          _ = 53494228 := by rw [factor_2_25]; decide
      have factor_2_27 : (58 : ZMod 892371481) ^ 178474296 = 550446652 := by
        calc
          (58 : ZMod 892371481) ^ 178474296 = (58 : ZMod 892371481) ^ (89237148 + 89237148) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 89237148 * (58 : ZMod 892371481) ^ 89237148 := by rw [pow_add]
          _ = 550446652 := by rw [factor_2_26]; decide
      change (58 : ZMod 892371481) ^ 178474296 ≠ 1
      rw [factor_2_27]
      decide
    ·
      have factor_3_0 : (58 : ZMod 892371481) ^ 1 = 58 := by norm_num
      have factor_3_1 : (58 : ZMod 892371481) ^ 3 = 195112 := by
        calc
          (58 : ZMod 892371481) ^ 3 = (58 : ZMod 892371481) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 1 * (58 : ZMod 892371481) ^ 1) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 195112 := by rw [factor_3_0]; decide
      have factor_3_2 : (58 : ZMod 892371481) ^ 7 = 257123558 := by
        calc
          (58 : ZMod 892371481) ^ 7 = (58 : ZMod 892371481) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 3 * (58 : ZMod 892371481) ^ 3) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 257123558 := by rw [factor_3_1]; decide
      have factor_3_3 : (58 : ZMod 892371481) ^ 15 = 507699389 := by
        calc
          (58 : ZMod 892371481) ^ 15 = (58 : ZMod 892371481) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 7 * (58 : ZMod 892371481) ^ 7) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 507699389 := by rw [factor_3_2]; decide
      have factor_3_4 : (58 : ZMod 892371481) ^ 30 = 583575496 := by
        calc
          (58 : ZMod 892371481) ^ 30 = (58 : ZMod 892371481) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 15 * (58 : ZMod 892371481) ^ 15 := by rw [pow_add]
          _ = 583575496 := by rw [factor_3_3]; decide
      have factor_3_5 : (58 : ZMod 892371481) ^ 60 = 722001107 := by
        calc
          (58 : ZMod 892371481) ^ 60 = (58 : ZMod 892371481) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 30 * (58 : ZMod 892371481) ^ 30 := by rw [pow_add]
          _ = 722001107 := by rw [factor_3_4]; decide
      have factor_3_6 : (58 : ZMod 892371481) ^ 121 = 726925812 := by
        calc
          (58 : ZMod 892371481) ^ 121 = (58 : ZMod 892371481) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 60 * (58 : ZMod 892371481) ^ 60) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 726925812 := by rw [factor_3_5]; decide
      have factor_3_7 : (58 : ZMod 892371481) ^ 243 = 376851289 := by
        calc
          (58 : ZMod 892371481) ^ 243 = (58 : ZMod 892371481) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 121 * (58 : ZMod 892371481) ^ 121) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 376851289 := by rw [factor_3_6]; decide
      have factor_3_8 : (58 : ZMod 892371481) ^ 486 = 92305274 := by
        calc
          (58 : ZMod 892371481) ^ 486 = (58 : ZMod 892371481) ^ (243 + 243) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 243 * (58 : ZMod 892371481) ^ 243 := by rw [pow_add]
          _ = 92305274 := by rw [factor_3_7]; decide
      have factor_3_9 : (58 : ZMod 892371481) ^ 972 = 653232948 := by
        calc
          (58 : ZMod 892371481) ^ 972 = (58 : ZMod 892371481) ^ (486 + 486) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 486 * (58 : ZMod 892371481) ^ 486 := by rw [pow_add]
          _ = 653232948 := by rw [factor_3_8]; decide
      have factor_3_10 : (58 : ZMod 892371481) ^ 1945 = 145077526 := by
        calc
          (58 : ZMod 892371481) ^ 1945 = (58 : ZMod 892371481) ^ (972 + 972 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 972 * (58 : ZMod 892371481) ^ 972) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 145077526 := by rw [factor_3_9]; decide
      have factor_3_11 : (58 : ZMod 892371481) ^ 3890 = 521470980 := by
        calc
          (58 : ZMod 892371481) ^ 3890 = (58 : ZMod 892371481) ^ (1945 + 1945) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1945 * (58 : ZMod 892371481) ^ 1945 := by rw [pow_add]
          _ = 521470980 := by rw [factor_3_10]; decide
      have factor_3_12 : (58 : ZMod 892371481) ^ 7780 = 834909825 := by
        calc
          (58 : ZMod 892371481) ^ 7780 = (58 : ZMod 892371481) ^ (3890 + 3890) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 3890 * (58 : ZMod 892371481) ^ 3890 := by rw [pow_add]
          _ = 834909825 := by rw [factor_3_11]; decide
      have factor_3_13 : (58 : ZMod 892371481) ^ 15561 = 600785746 := by
        calc
          (58 : ZMod 892371481) ^ 15561 = (58 : ZMod 892371481) ^ (7780 + 7780 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 7780 * (58 : ZMod 892371481) ^ 7780) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 600785746 := by rw [factor_3_12]; decide
      have factor_3_14 : (58 : ZMod 892371481) ^ 31123 = 14665197 := by
        calc
          (58 : ZMod 892371481) ^ 31123 = (58 : ZMod 892371481) ^ (15561 + 15561 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 15561 * (58 : ZMod 892371481) ^ 15561) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 14665197 := by rw [factor_3_13]; decide
      have factor_3_15 : (58 : ZMod 892371481) ^ 62246 = 229527442 := by
        calc
          (58 : ZMod 892371481) ^ 62246 = (58 : ZMod 892371481) ^ (31123 + 31123) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 31123 * (58 : ZMod 892371481) ^ 31123 := by rw [pow_add]
          _ = 229527442 := by rw [factor_3_14]; decide
      have factor_3_16 : (58 : ZMod 892371481) ^ 124493 = 342207824 := by
        calc
          (58 : ZMod 892371481) ^ 124493 = (58 : ZMod 892371481) ^ (62246 + 62246 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 62246 * (58 : ZMod 892371481) ^ 62246) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 342207824 := by rw [factor_3_15]; decide
      have factor_3_17 : (58 : ZMod 892371481) ^ 248987 = 679241982 := by
        calc
          (58 : ZMod 892371481) ^ 248987 = (58 : ZMod 892371481) ^ (124493 + 124493 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 124493 * (58 : ZMod 892371481) ^ 124493) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 679241982 := by rw [factor_3_16]; decide
      have factor_3_18 : (58 : ZMod 892371481) ^ 497975 = 866844398 := by
        calc
          (58 : ZMod 892371481) ^ 497975 = (58 : ZMod 892371481) ^ (248987 + 248987 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 248987 * (58 : ZMod 892371481) ^ 248987) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 866844398 := by rw [factor_3_17]; decide
      have factor_3_19 : (58 : ZMod 892371481) ^ 995950 = 1775664 := by
        calc
          (58 : ZMod 892371481) ^ 995950 = (58 : ZMod 892371481) ^ (497975 + 497975) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 497975 * (58 : ZMod 892371481) ^ 497975 := by rw [pow_add]
          _ = 1775664 := by rw [factor_3_18]; decide
      have factor_3_20 : (58 : ZMod 892371481) ^ 1991900 = 234198523 := by
        calc
          (58 : ZMod 892371481) ^ 1991900 = (58 : ZMod 892371481) ^ (995950 + 995950) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 995950 * (58 : ZMod 892371481) ^ 995950 := by rw [pow_add]
          _ = 234198523 := by rw [factor_3_19]; decide
      have factor_3_21 : (58 : ZMod 892371481) ^ 3983801 = 277481578 := by
        calc
          (58 : ZMod 892371481) ^ 3983801 = (58 : ZMod 892371481) ^ (1991900 + 1991900 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 1991900 * (58 : ZMod 892371481) ^ 1991900) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 277481578 := by rw [factor_3_20]; decide
      have factor_3_22 : (58 : ZMod 892371481) ^ 7967602 = 775045723 := by
        calc
          (58 : ZMod 892371481) ^ 7967602 = (58 : ZMod 892371481) ^ (3983801 + 3983801) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 3983801 * (58 : ZMod 892371481) ^ 3983801 := by rw [pow_add]
          _ = 775045723 := by rw [factor_3_21]; decide
      have factor_3_23 : (58 : ZMod 892371481) ^ 15935205 = 349159354 := by
        calc
          (58 : ZMod 892371481) ^ 15935205 = (58 : ZMod 892371481) ^ (7967602 + 7967602 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 7967602 * (58 : ZMod 892371481) ^ 7967602) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 349159354 := by rw [factor_3_22]; decide
      have factor_3_24 : (58 : ZMod 892371481) ^ 31870410 = 112028000 := by
        calc
          (58 : ZMod 892371481) ^ 31870410 = (58 : ZMod 892371481) ^ (15935205 + 15935205) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 15935205 * (58 : ZMod 892371481) ^ 15935205 := by rw [pow_add]
          _ = 112028000 := by rw [factor_3_23]; decide
      have factor_3_25 : (58 : ZMod 892371481) ^ 63740820 = 431932645 := by
        calc
          (58 : ZMod 892371481) ^ 63740820 = (58 : ZMod 892371481) ^ (31870410 + 31870410) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 31870410 * (58 : ZMod 892371481) ^ 31870410 := by rw [pow_add]
          _ = 431932645 := by rw [factor_3_24]; decide
      have factor_3_26 : (58 : ZMod 892371481) ^ 127481640 = 355846638 := by
        calc
          (58 : ZMod 892371481) ^ 127481640 = (58 : ZMod 892371481) ^ (63740820 + 63740820) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 63740820 * (58 : ZMod 892371481) ^ 63740820 := by rw [pow_add]
          _ = 355846638 := by rw [factor_3_25]; decide
      change (58 : ZMod 892371481) ^ 127481640 ≠ 1
      rw [factor_3_26]
      decide
    ·
      have factor_4_0 : (58 : ZMod 892371481) ^ 1 = 58 := by norm_num
      have factor_4_1 : (58 : ZMod 892371481) ^ 2 = 3364 := by
        calc
          (58 : ZMod 892371481) ^ 2 = (58 : ZMod 892371481) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1 * (58 : ZMod 892371481) ^ 1 := by rw [pow_add]
          _ = 3364 := by rw [factor_4_0]; decide
      have factor_4_2 : (58 : ZMod 892371481) ^ 4 = 11316496 := by
        calc
          (58 : ZMod 892371481) ^ 4 = (58 : ZMod 892371481) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 2 * (58 : ZMod 892371481) ^ 2 := by rw [pow_add]
          _ = 11316496 := by rw [factor_4_1]; decide
      have factor_4_3 : (58 : ZMod 892371481) ^ 9 = 255684023 := by
        calc
          (58 : ZMod 892371481) ^ 9 = (58 : ZMod 892371481) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 4 * (58 : ZMod 892371481) ^ 4) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 255684023 := by rw [factor_4_2]; decide
      have factor_4_4 : (58 : ZMod 892371481) ^ 19 = 489411619 := by
        calc
          (58 : ZMod 892371481) ^ 19 = (58 : ZMod 892371481) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 9 * (58 : ZMod 892371481) ^ 9) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 489411619 := by rw [factor_4_3]; decide
      have factor_4_5 : (58 : ZMod 892371481) ^ 38 = 386198700 := by
        calc
          (58 : ZMod 892371481) ^ 38 = (58 : ZMod 892371481) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 19 * (58 : ZMod 892371481) ^ 19 := by rw [pow_add]
          _ = 386198700 := by rw [factor_4_4]; decide
      have factor_4_6 : (58 : ZMod 892371481) ^ 77 = 627068308 := by
        calc
          (58 : ZMod 892371481) ^ 77 = (58 : ZMod 892371481) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 38 * (58 : ZMod 892371481) ^ 38) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 627068308 := by rw [factor_4_5]; decide
      have factor_4_7 : (58 : ZMod 892371481) ^ 154 = 703508840 := by
        calc
          (58 : ZMod 892371481) ^ 154 = (58 : ZMod 892371481) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 77 * (58 : ZMod 892371481) ^ 77 := by rw [pow_add]
          _ = 703508840 := by rw [factor_4_6]; decide
      have factor_4_8 : (58 : ZMod 892371481) ^ 309 = 764433194 := by
        calc
          (58 : ZMod 892371481) ^ 309 = (58 : ZMod 892371481) ^ (154 + 154 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 154 * (58 : ZMod 892371481) ^ 154) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 764433194 := by rw [factor_4_7]; decide
      have factor_4_9 : (58 : ZMod 892371481) ^ 618 = 75658842 := by
        calc
          (58 : ZMod 892371481) ^ 618 = (58 : ZMod 892371481) ^ (309 + 309) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 309 * (58 : ZMod 892371481) ^ 309 := by rw [pow_add]
          _ = 75658842 := by rw [factor_4_8]; decide
      have factor_4_10 : (58 : ZMod 892371481) ^ 1237 = 309771625 := by
        calc
          (58 : ZMod 892371481) ^ 1237 = (58 : ZMod 892371481) ^ (618 + 618 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 618 * (58 : ZMod 892371481) ^ 618) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 309771625 := by rw [factor_4_9]; decide
      have factor_4_11 : (58 : ZMod 892371481) ^ 2475 = 497581149 := by
        calc
          (58 : ZMod 892371481) ^ 2475 = (58 : ZMod 892371481) ^ (1237 + 1237 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 1237 * (58 : ZMod 892371481) ^ 1237) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 497581149 := by rw [factor_4_10]; decide
      have factor_4_12 : (58 : ZMod 892371481) ^ 4951 = 182906843 := by
        calc
          (58 : ZMod 892371481) ^ 4951 = (58 : ZMod 892371481) ^ (2475 + 2475 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 2475 * (58 : ZMod 892371481) ^ 2475) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 182906843 := by rw [factor_4_11]; decide
      have factor_4_13 : (58 : ZMod 892371481) ^ 9902 = 92542154 := by
        calc
          (58 : ZMod 892371481) ^ 9902 = (58 : ZMod 892371481) ^ (4951 + 4951) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 4951 * (58 : ZMod 892371481) ^ 4951 := by rw [pow_add]
          _ = 92542154 := by rw [factor_4_12]; decide
      have factor_4_14 : (58 : ZMod 892371481) ^ 19805 = 738547053 := by
        calc
          (58 : ZMod 892371481) ^ 19805 = (58 : ZMod 892371481) ^ (9902 + 9902 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 9902 * (58 : ZMod 892371481) ^ 9902) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 738547053 := by rw [factor_4_13]; decide
      have factor_4_15 : (58 : ZMod 892371481) ^ 39611 = 566636762 := by
        calc
          (58 : ZMod 892371481) ^ 39611 = (58 : ZMod 892371481) ^ (19805 + 19805 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 19805 * (58 : ZMod 892371481) ^ 19805) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 566636762 := by rw [factor_4_14]; decide
      have factor_4_16 : (58 : ZMod 892371481) ^ 79223 = 875020725 := by
        calc
          (58 : ZMod 892371481) ^ 79223 = (58 : ZMod 892371481) ^ (39611 + 39611 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 39611 * (58 : ZMod 892371481) ^ 39611) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 875020725 := by rw [factor_4_15]; decide
      have factor_4_17 : (58 : ZMod 892371481) ^ 158446 = 75684338 := by
        calc
          (58 : ZMod 892371481) ^ 158446 = (58 : ZMod 892371481) ^ (79223 + 79223) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 79223 * (58 : ZMod 892371481) ^ 79223 := by rw [pow_add]
          _ = 75684338 := by rw [factor_4_16]; decide
      have factor_4_18 : (58 : ZMod 892371481) ^ 316893 = 348167951 := by
        calc
          (58 : ZMod 892371481) ^ 316893 = (58 : ZMod 892371481) ^ (158446 + 158446 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 158446 * (58 : ZMod 892371481) ^ 158446) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 348167951 := by rw [factor_4_17]; decide
      have factor_4_19 : (58 : ZMod 892371481) ^ 633786 = 409400519 := by
        calc
          (58 : ZMod 892371481) ^ 633786 = (58 : ZMod 892371481) ^ (316893 + 316893) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 316893 * (58 : ZMod 892371481) ^ 316893 := by rw [pow_add]
          _ = 409400519 := by rw [factor_4_18]; decide
      have factor_4_20 : (58 : ZMod 892371481) ^ 1267573 = 124914764 := by
        calc
          (58 : ZMod 892371481) ^ 1267573 = (58 : ZMod 892371481) ^ (633786 + 633786 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 633786 * (58 : ZMod 892371481) ^ 633786) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 124914764 := by rw [factor_4_19]; decide
      have factor_4_21 : (58 : ZMod 892371481) ^ 2535146 = 201313603 := by
        calc
          (58 : ZMod 892371481) ^ 2535146 = (58 : ZMod 892371481) ^ (1267573 + 1267573) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1267573 * (58 : ZMod 892371481) ^ 1267573 := by rw [pow_add]
          _ = 201313603 := by rw [factor_4_20]; decide
      have factor_4_22 : (58 : ZMod 892371481) ^ 5070292 = 827305560 := by
        calc
          (58 : ZMod 892371481) ^ 5070292 = (58 : ZMod 892371481) ^ (2535146 + 2535146) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 2535146 * (58 : ZMod 892371481) ^ 2535146 := by rw [pow_add]
          _ = 827305560 := by rw [factor_4_21]; decide
      have factor_4_23 : (58 : ZMod 892371481) ^ 10140585 = 241382214 := by
        calc
          (58 : ZMod 892371481) ^ 10140585 = (58 : ZMod 892371481) ^ (5070292 + 5070292 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 5070292 * (58 : ZMod 892371481) ^ 5070292) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 241382214 := by rw [factor_4_22]; decide
      have factor_4_24 : (58 : ZMod 892371481) ^ 20281170 = 389794223 := by
        calc
          (58 : ZMod 892371481) ^ 20281170 = (58 : ZMod 892371481) ^ (10140585 + 10140585) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 10140585 * (58 : ZMod 892371481) ^ 10140585 := by rw [pow_add]
          _ = 389794223 := by rw [factor_4_23]; decide
      have factor_4_25 : (58 : ZMod 892371481) ^ 40562340 = 663085715 := by
        calc
          (58 : ZMod 892371481) ^ 40562340 = (58 : ZMod 892371481) ^ (20281170 + 20281170) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 20281170 * (58 : ZMod 892371481) ^ 20281170 := by rw [pow_add]
          _ = 663085715 := by rw [factor_4_24]; decide
      have factor_4_26 : (58 : ZMod 892371481) ^ 81124680 = 6672473 := by
        calc
          (58 : ZMod 892371481) ^ 81124680 = (58 : ZMod 892371481) ^ (40562340 + 40562340) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 40562340 * (58 : ZMod 892371481) ^ 40562340 := by rw [pow_add]
          _ = 6672473 := by rw [factor_4_25]; decide
      change (58 : ZMod 892371481) ^ 81124680 ≠ 1
      rw [factor_4_26]
      decide
    ·
      have factor_5_0 : (58 : ZMod 892371481) ^ 1 = 58 := by norm_num
      have factor_5_1 : (58 : ZMod 892371481) ^ 2 = 3364 := by
        calc
          (58 : ZMod 892371481) ^ 2 = (58 : ZMod 892371481) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1 * (58 : ZMod 892371481) ^ 1 := by rw [pow_add]
          _ = 3364 := by rw [factor_5_0]; decide
      have factor_5_2 : (58 : ZMod 892371481) ^ 4 = 11316496 := by
        calc
          (58 : ZMod 892371481) ^ 4 = (58 : ZMod 892371481) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 2 * (58 : ZMod 892371481) ^ 2 := by rw [pow_add]
          _ = 11316496 := by rw [factor_5_1]; decide
      have factor_5_3 : (58 : ZMod 892371481) ^ 8 = 635222668 := by
        calc
          (58 : ZMod 892371481) ^ 8 = (58 : ZMod 892371481) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 4 * (58 : ZMod 892371481) ^ 4 := by rw [pow_add]
          _ = 635222668 := by rw [factor_5_2]; decide
      have factor_5_4 : (58 : ZMod 892371481) ^ 16 = 890677170 := by
        calc
          (58 : ZMod 892371481) ^ 16 = (58 : ZMod 892371481) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 8 * (58 : ZMod 892371481) ^ 8 := by rw [pow_add]
          _ = 890677170 := by rw [factor_5_3]; decide
      have factor_5_5 : (58 : ZMod 892371481) ^ 32 = 823081825 := by
        calc
          (58 : ZMod 892371481) ^ 32 = (58 : ZMod 892371481) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 16 * (58 : ZMod 892371481) ^ 16 := by rw [pow_add]
          _ = 823081825 := by rw [factor_5_4]; decide
      have factor_5_6 : (58 : ZMod 892371481) ^ 65 = 444844328 := by
        calc
          (58 : ZMod 892371481) ^ 65 = (58 : ZMod 892371481) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 32 * (58 : ZMod 892371481) ^ 32) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 444844328 := by rw [factor_5_5]; decide
      have factor_5_7 : (58 : ZMod 892371481) ^ 130 = 143496590 := by
        calc
          (58 : ZMod 892371481) ^ 130 = (58 : ZMod 892371481) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 65 * (58 : ZMod 892371481) ^ 65 := by rw [pow_add]
          _ = 143496590 := by rw [factor_5_6]; decide
      have factor_5_8 : (58 : ZMod 892371481) ^ 261 = 65077597 := by
        calc
          (58 : ZMod 892371481) ^ 261 = (58 : ZMod 892371481) ^ (130 + 130 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 130 * (58 : ZMod 892371481) ^ 130) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 65077597 := by rw [factor_5_7]; decide
      have factor_5_9 : (58 : ZMod 892371481) ^ 523 = 295970474 := by
        calc
          (58 : ZMod 892371481) ^ 523 = (58 : ZMod 892371481) ^ (261 + 261 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 261 * (58 : ZMod 892371481) ^ 261) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 295970474 := by rw [factor_5_8]; decide
      have factor_5_10 : (58 : ZMod 892371481) ^ 1047 = 275917485 := by
        calc
          (58 : ZMod 892371481) ^ 1047 = (58 : ZMod 892371481) ^ (523 + 523 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 523 * (58 : ZMod 892371481) ^ 523) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 275917485 := by rw [factor_5_9]; decide
      have factor_5_11 : (58 : ZMod 892371481) ^ 2094 = 493226067 := by
        calc
          (58 : ZMod 892371481) ^ 2094 = (58 : ZMod 892371481) ^ (1047 + 1047) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1047 * (58 : ZMod 892371481) ^ 1047 := by rw [pow_add]
          _ = 493226067 := by rw [factor_5_10]; decide
      have factor_5_12 : (58 : ZMod 892371481) ^ 4189 = 647073332 := by
        calc
          (58 : ZMod 892371481) ^ 4189 = (58 : ZMod 892371481) ^ (2094 + 2094 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 2094 * (58 : ZMod 892371481) ^ 2094) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 647073332 := by rw [factor_5_11]; decide
      have factor_5_13 : (58 : ZMod 892371481) ^ 8379 = 593756851 := by
        calc
          (58 : ZMod 892371481) ^ 8379 = (58 : ZMod 892371481) ^ (4189 + 4189 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 4189 * (58 : ZMod 892371481) ^ 4189) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 593756851 := by rw [factor_5_12]; decide
      have factor_5_14 : (58 : ZMod 892371481) ^ 16758 = 484741046 := by
        calc
          (58 : ZMod 892371481) ^ 16758 = (58 : ZMod 892371481) ^ (8379 + 8379) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 8379 * (58 : ZMod 892371481) ^ 8379 := by rw [pow_add]
          _ = 484741046 := by rw [factor_5_13]; decide
      have factor_5_15 : (58 : ZMod 892371481) ^ 33517 = 444860469 := by
        calc
          (58 : ZMod 892371481) ^ 33517 = (58 : ZMod 892371481) ^ (16758 + 16758 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 16758 * (58 : ZMod 892371481) ^ 16758) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 444860469 := by rw [factor_5_14]; decide
      have factor_5_16 : (58 : ZMod 892371481) ^ 67035 = 655968977 := by
        calc
          (58 : ZMod 892371481) ^ 67035 = (58 : ZMod 892371481) ^ (33517 + 33517 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 33517 * (58 : ZMod 892371481) ^ 33517) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 655968977 := by rw [factor_5_15]; decide
      have factor_5_17 : (58 : ZMod 892371481) ^ 134070 = 293535390 := by
        calc
          (58 : ZMod 892371481) ^ 134070 = (58 : ZMod 892371481) ^ (67035 + 67035) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 67035 * (58 : ZMod 892371481) ^ 67035 := by rw [pow_add]
          _ = 293535390 := by rw [factor_5_16]; decide
      have factor_5_18 : (58 : ZMod 892371481) ^ 268140 = 458377152 := by
        calc
          (58 : ZMod 892371481) ^ 268140 = (58 : ZMod 892371481) ^ (134070 + 134070) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 134070 * (58 : ZMod 892371481) ^ 134070 := by rw [pow_add]
          _ = 458377152 := by rw [factor_5_17]; decide
      have factor_5_19 : (58 : ZMod 892371481) ^ 536280 = 466880026 := by
        calc
          (58 : ZMod 892371481) ^ 536280 = (58 : ZMod 892371481) ^ (268140 + 268140) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 268140 * (58 : ZMod 892371481) ^ 268140 := by rw [pow_add]
          _ = 466880026 := by rw [factor_5_18]; decide
      have factor_5_20 : (58 : ZMod 892371481) ^ 1072561 = 80483050 := by
        calc
          (58 : ZMod 892371481) ^ 1072561 = (58 : ZMod 892371481) ^ (536280 + 536280 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 536280 * (58 : ZMod 892371481) ^ 536280) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 80483050 := by rw [factor_5_19]; decide
      have factor_5_21 : (58 : ZMod 892371481) ^ 2145123 = 117227010 := by
        calc
          (58 : ZMod 892371481) ^ 2145123 = (58 : ZMod 892371481) ^ (1072561 + 1072561 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 1072561 * (58 : ZMod 892371481) ^ 1072561) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 117227010 := by rw [factor_5_20]; decide
      have factor_5_22 : (58 : ZMod 892371481) ^ 4290247 = 821314880 := by
        calc
          (58 : ZMod 892371481) ^ 4290247 = (58 : ZMod 892371481) ^ (2145123 + 2145123 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 2145123 * (58 : ZMod 892371481) ^ 2145123) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 821314880 := by rw [factor_5_21]; decide
      have factor_5_23 : (58 : ZMod 892371481) ^ 8580495 = 793152483 := by
        calc
          (58 : ZMod 892371481) ^ 8580495 = (58 : ZMod 892371481) ^ (4290247 + 4290247 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 4290247 * (58 : ZMod 892371481) ^ 4290247) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 793152483 := by rw [factor_5_22]; decide
      have factor_5_24 : (58 : ZMod 892371481) ^ 17160990 = 294688545 := by
        calc
          (58 : ZMod 892371481) ^ 17160990 = (58 : ZMod 892371481) ^ (8580495 + 8580495) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 8580495 * (58 : ZMod 892371481) ^ 8580495 := by rw [pow_add]
          _ = 294688545 := by rw [factor_5_23]; decide
      have factor_5_25 : (58 : ZMod 892371481) ^ 34321980 = 850518433 := by
        calc
          (58 : ZMod 892371481) ^ 34321980 = (58 : ZMod 892371481) ^ (17160990 + 17160990) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 17160990 * (58 : ZMod 892371481) ^ 17160990 := by rw [pow_add]
          _ = 850518433 := by rw [factor_5_24]; decide
      have factor_5_26 : (58 : ZMod 892371481) ^ 68643960 = 597747278 := by
        calc
          (58 : ZMod 892371481) ^ 68643960 = (58 : ZMod 892371481) ^ (34321980 + 34321980) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 34321980 * (58 : ZMod 892371481) ^ 34321980 := by rw [pow_add]
          _ = 597747278 := by rw [factor_5_25]; decide
      change (58 : ZMod 892371481) ^ 68643960 ≠ 1
      rw [factor_5_26]
      decide
    ·
      have factor_6_0 : (58 : ZMod 892371481) ^ 1 = 58 := by norm_num
      have factor_6_1 : (58 : ZMod 892371481) ^ 3 = 195112 := by
        calc
          (58 : ZMod 892371481) ^ 3 = (58 : ZMod 892371481) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 1 * (58 : ZMod 892371481) ^ 1) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 195112 := by rw [factor_6_0]; decide
      have factor_6_2 : (58 : ZMod 892371481) ^ 6 = 589090342 := by
        calc
          (58 : ZMod 892371481) ^ 6 = (58 : ZMod 892371481) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 3 * (58 : ZMod 892371481) ^ 3 := by rw [pow_add]
          _ = 589090342 := by rw [factor_6_1]; decide
      have factor_6_3 : (58 : ZMod 892371481) ^ 12 = 778193233 := by
        calc
          (58 : ZMod 892371481) ^ 12 = (58 : ZMod 892371481) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 6 * (58 : ZMod 892371481) ^ 6 := by rw [pow_add]
          _ = 778193233 := by rw [factor_6_2]; decide
      have factor_6_4 : (58 : ZMod 892371481) ^ 25 = 621730145 := by
        calc
          (58 : ZMod 892371481) ^ 25 = (58 : ZMod 892371481) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 12 * (58 : ZMod 892371481) ^ 12) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 621730145 := by rw [factor_6_3]; decide
      have factor_6_5 : (58 : ZMod 892371481) ^ 50 = 820733149 := by
        calc
          (58 : ZMod 892371481) ^ 50 = (58 : ZMod 892371481) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 25 * (58 : ZMod 892371481) ^ 25 := by rw [pow_add]
          _ = 820733149 := by rw [factor_6_4]; decide
      have factor_6_6 : (58 : ZMod 892371481) ^ 100 = 807595680 := by
        calc
          (58 : ZMod 892371481) ^ 100 = (58 : ZMod 892371481) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 50 * (58 : ZMod 892371481) ^ 50 := by rw [pow_add]
          _ = 807595680 := by rw [factor_6_5]; decide
      have factor_6_7 : (58 : ZMod 892371481) ^ 200 = 512459332 := by
        calc
          (58 : ZMod 892371481) ^ 200 = (58 : ZMod 892371481) ^ (100 + 100) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 100 * (58 : ZMod 892371481) ^ 100 := by rw [pow_add]
          _ = 512459332 := by rw [factor_6_6]; decide
      have factor_6_8 : (58 : ZMod 892371481) ^ 400 = 528480634 := by
        calc
          (58 : ZMod 892371481) ^ 400 = (58 : ZMod 892371481) ^ (200 + 200) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 200 * (58 : ZMod 892371481) ^ 200 := by rw [pow_add]
          _ = 528480634 := by rw [factor_6_7]; decide
      have factor_6_9 : (58 : ZMod 892371481) ^ 800 = 271103121 := by
        calc
          (58 : ZMod 892371481) ^ 800 = (58 : ZMod 892371481) ^ (400 + 400) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 400 * (58 : ZMod 892371481) ^ 400 := by rw [pow_add]
          _ = 271103121 := by rw [factor_6_8]; decide
      have factor_6_10 : (58 : ZMod 892371481) ^ 1601 = 120775066 := by
        calc
          (58 : ZMod 892371481) ^ 1601 = (58 : ZMod 892371481) ^ (800 + 800 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 800 * (58 : ZMod 892371481) ^ 800) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 120775066 := by rw [factor_6_9]; decide
      have factor_6_11 : (58 : ZMod 892371481) ^ 3203 = 387643386 := by
        calc
          (58 : ZMod 892371481) ^ 3203 = (58 : ZMod 892371481) ^ (1601 + 1601 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 1601 * (58 : ZMod 892371481) ^ 1601) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 387643386 := by rw [factor_6_10]; decide
      have factor_6_12 : (58 : ZMod 892371481) ^ 6407 = 81943546 := by
        calc
          (58 : ZMod 892371481) ^ 6407 = (58 : ZMod 892371481) ^ (3203 + 3203 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 3203 * (58 : ZMod 892371481) ^ 3203) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 81943546 := by rw [factor_6_11]; decide
      have factor_6_13 : (58 : ZMod 892371481) ^ 12815 = 449483680 := by
        calc
          (58 : ZMod 892371481) ^ 12815 = (58 : ZMod 892371481) ^ (6407 + 6407 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 6407 * (58 : ZMod 892371481) ^ 6407) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 449483680 := by rw [factor_6_12]; decide
      have factor_6_14 : (58 : ZMod 892371481) ^ 25631 = 255171439 := by
        calc
          (58 : ZMod 892371481) ^ 25631 = (58 : ZMod 892371481) ^ (12815 + 12815 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 12815 * (58 : ZMod 892371481) ^ 12815) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 255171439 := by rw [factor_6_13]; decide
      have factor_6_15 : (58 : ZMod 892371481) ^ 51262 = 805817514 := by
        calc
          (58 : ZMod 892371481) ^ 51262 = (58 : ZMod 892371481) ^ (25631 + 25631) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 25631 * (58 : ZMod 892371481) ^ 25631 := by rw [pow_add]
          _ = 805817514 := by rw [factor_6_14]; decide
      have factor_6_16 : (58 : ZMod 892371481) ^ 102524 = 334205863 := by
        calc
          (58 : ZMod 892371481) ^ 102524 = (58 : ZMod 892371481) ^ (51262 + 51262) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 51262 * (58 : ZMod 892371481) ^ 51262 := by rw [pow_add]
          _ = 334205863 := by rw [factor_6_15]; decide
      have factor_6_17 : (58 : ZMod 892371481) ^ 205048 = 237245261 := by
        calc
          (58 : ZMod 892371481) ^ 205048 = (58 : ZMod 892371481) ^ (102524 + 102524) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 102524 * (58 : ZMod 892371481) ^ 102524 := by rw [pow_add]
          _ = 237245261 := by rw [factor_6_16]; decide
      have factor_6_18 : (58 : ZMod 892371481) ^ 410097 = 369544738 := by
        calc
          (58 : ZMod 892371481) ^ 410097 = (58 : ZMod 892371481) ^ (205048 + 205048 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 205048 * (58 : ZMod 892371481) ^ 205048) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 369544738 := by rw [factor_6_17]; decide
      have factor_6_19 : (58 : ZMod 892371481) ^ 820194 = 519669532 := by
        calc
          (58 : ZMod 892371481) ^ 820194 = (58 : ZMod 892371481) ^ (410097 + 410097) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 410097 * (58 : ZMod 892371481) ^ 410097 := by rw [pow_add]
          _ = 519669532 := by rw [factor_6_18]; decide
      have factor_6_20 : (58 : ZMod 892371481) ^ 1640388 = 841841300 := by
        calc
          (58 : ZMod 892371481) ^ 1640388 = (58 : ZMod 892371481) ^ (820194 + 820194) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 820194 * (58 : ZMod 892371481) ^ 820194 := by rw [pow_add]
          _ = 841841300 := by rw [factor_6_19]; decide
      have factor_6_21 : (58 : ZMod 892371481) ^ 3280777 = 862294715 := by
        calc
          (58 : ZMod 892371481) ^ 3280777 = (58 : ZMod 892371481) ^ (1640388 + 1640388 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 1640388 * (58 : ZMod 892371481) ^ 1640388) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 862294715 := by rw [factor_6_20]; decide
      have factor_6_22 : (58 : ZMod 892371481) ^ 6561555 = 275063121 := by
        calc
          (58 : ZMod 892371481) ^ 6561555 = (58 : ZMod 892371481) ^ (3280777 + 3280777 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 3280777 * (58 : ZMod 892371481) ^ 3280777) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 275063121 := by rw [factor_6_21]; decide
      have factor_6_23 : (58 : ZMod 892371481) ^ 13123110 = 55818236 := by
        calc
          (58 : ZMod 892371481) ^ 13123110 = (58 : ZMod 892371481) ^ (6561555 + 6561555) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 6561555 * (58 : ZMod 892371481) ^ 6561555 := by rw [pow_add]
          _ = 55818236 := by rw [factor_6_22]; decide
      have factor_6_24 : (58 : ZMod 892371481) ^ 26246220 = 600956841 := by
        calc
          (58 : ZMod 892371481) ^ 26246220 = (58 : ZMod 892371481) ^ (13123110 + 13123110) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 13123110 * (58 : ZMod 892371481) ^ 13123110 := by rw [pow_add]
          _ = 600956841 := by rw [factor_6_23]; decide
      have factor_6_25 : (58 : ZMod 892371481) ^ 52492440 = 573681245 := by
        calc
          (58 : ZMod 892371481) ^ 52492440 = (58 : ZMod 892371481) ^ (26246220 + 26246220) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 26246220 * (58 : ZMod 892371481) ^ 26246220 := by rw [pow_add]
          _ = 573681245 := by rw [factor_6_24]; decide
      change (58 : ZMod 892371481) ^ 52492440 ≠ 1
      rw [factor_6_25]
      decide
    ·
      have factor_7_0 : (58 : ZMod 892371481) ^ 1 = 58 := by norm_num
      have factor_7_1 : (58 : ZMod 892371481) ^ 2 = 3364 := by
        calc
          (58 : ZMod 892371481) ^ 2 = (58 : ZMod 892371481) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1 * (58 : ZMod 892371481) ^ 1 := by rw [pow_add]
          _ = 3364 := by rw [factor_7_0]; decide
      have factor_7_2 : (58 : ZMod 892371481) ^ 5 = 656356768 := by
        calc
          (58 : ZMod 892371481) ^ 5 = (58 : ZMod 892371481) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 2 * (58 : ZMod 892371481) ^ 2) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 656356768 := by rw [factor_7_1]; decide
      have factor_7_3 : (58 : ZMod 892371481) ^ 11 = 767317169 := by
        calc
          (58 : ZMod 892371481) ^ 11 = (58 : ZMod 892371481) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 5 * (58 : ZMod 892371481) ^ 5) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 767317169 := by rw [factor_7_2]; decide
      have factor_7_4 : (58 : ZMod 892371481) ^ 22 = 84738961 := by
        calc
          (58 : ZMod 892371481) ^ 22 = (58 : ZMod 892371481) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 11 * (58 : ZMod 892371481) ^ 11 := by rw [pow_add]
          _ = 84738961 := by rw [factor_7_3]; decide
      have factor_7_5 : (58 : ZMod 892371481) ^ 44 = 404251290 := by
        calc
          (58 : ZMod 892371481) ^ 44 = (58 : ZMod 892371481) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 22 * (58 : ZMod 892371481) ^ 22 := by rw [pow_add]
          _ = 404251290 := by rw [factor_7_4]; decide
      have factor_7_6 : (58 : ZMod 892371481) ^ 89 = 830246807 := by
        calc
          (58 : ZMod 892371481) ^ 89 = (58 : ZMod 892371481) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 44 * (58 : ZMod 892371481) ^ 44) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 830246807 := by rw [factor_7_5]; decide
      have factor_7_7 : (58 : ZMod 892371481) ^ 179 = 289850058 := by
        calc
          (58 : ZMod 892371481) ^ 179 = (58 : ZMod 892371481) ^ (89 + 89 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 89 * (58 : ZMod 892371481) ^ 89) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 289850058 := by rw [factor_7_6]; decide
      have factor_7_8 : (58 : ZMod 892371481) ^ 358 = 590786172 := by
        calc
          (58 : ZMod 892371481) ^ 358 = (58 : ZMod 892371481) ^ (179 + 179) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 179 * (58 : ZMod 892371481) ^ 179 := by rw [pow_add]
          _ = 590786172 := by rw [factor_7_7]; decide
      have factor_7_9 : (58 : ZMod 892371481) ^ 716 = 786460539 := by
        calc
          (58 : ZMod 892371481) ^ 716 = (58 : ZMod 892371481) ^ (358 + 358) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 358 * (58 : ZMod 892371481) ^ 358 := by rw [pow_add]
          _ = 786460539 := by rw [factor_7_8]; decide
      have factor_7_10 : (58 : ZMod 892371481) ^ 1433 = 589893975 := by
        calc
          (58 : ZMod 892371481) ^ 1433 = (58 : ZMod 892371481) ^ (716 + 716 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 716 * (58 : ZMod 892371481) ^ 716) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 589893975 := by rw [factor_7_9]; decide
      have factor_7_11 : (58 : ZMod 892371481) ^ 2866 = 523722549 := by
        calc
          (58 : ZMod 892371481) ^ 2866 = (58 : ZMod 892371481) ^ (1433 + 1433) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1433 * (58 : ZMod 892371481) ^ 1433 := by rw [pow_add]
          _ = 523722549 := by rw [factor_7_10]; decide
      have factor_7_12 : (58 : ZMod 892371481) ^ 5733 = 521255481 := by
        calc
          (58 : ZMod 892371481) ^ 5733 = (58 : ZMod 892371481) ^ (2866 + 2866 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 2866 * (58 : ZMod 892371481) ^ 2866) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 521255481 := by rw [factor_7_11]; decide
      have factor_7_13 : (58 : ZMod 892371481) ^ 11466 = 603178434 := by
        calc
          (58 : ZMod 892371481) ^ 11466 = (58 : ZMod 892371481) ^ (5733 + 5733) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 5733 * (58 : ZMod 892371481) ^ 5733 := by rw [pow_add]
          _ = 603178434 := by rw [factor_7_12]; decide
      have factor_7_14 : (58 : ZMod 892371481) ^ 22933 = 203406750 := by
        calc
          (58 : ZMod 892371481) ^ 22933 = (58 : ZMod 892371481) ^ (11466 + 11466 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 11466 * (58 : ZMod 892371481) ^ 11466) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 203406750 := by rw [factor_7_13]; decide
      have factor_7_15 : (58 : ZMod 892371481) ^ 45866 = 172283898 := by
        calc
          (58 : ZMod 892371481) ^ 45866 = (58 : ZMod 892371481) ^ (22933 + 22933) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 22933 * (58 : ZMod 892371481) ^ 22933 := by rw [pow_add]
          _ = 172283898 := by rw [factor_7_14]; decide
      have factor_7_16 : (58 : ZMod 892371481) ^ 91732 = 778042602 := by
        calc
          (58 : ZMod 892371481) ^ 91732 = (58 : ZMod 892371481) ^ (45866 + 45866) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 45866 * (58 : ZMod 892371481) ^ 45866 := by rw [pow_add]
          _ = 778042602 := by rw [factor_7_15]; decide
      have factor_7_17 : (58 : ZMod 892371481) ^ 183464 = 99644370 := by
        calc
          (58 : ZMod 892371481) ^ 183464 = (58 : ZMod 892371481) ^ (91732 + 91732) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 91732 * (58 : ZMod 892371481) ^ 91732 := by rw [pow_add]
          _ = 99644370 := by rw [factor_7_16]; decide
      have factor_7_18 : (58 : ZMod 892371481) ^ 366929 = 153623743 := by
        calc
          (58 : ZMod 892371481) ^ 366929 = (58 : ZMod 892371481) ^ (183464 + 183464 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 183464 * (58 : ZMod 892371481) ^ 183464) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 153623743 := by rw [factor_7_17]; decide
      have factor_7_19 : (58 : ZMod 892371481) ^ 733858 = 337911779 := by
        calc
          (58 : ZMod 892371481) ^ 733858 = (58 : ZMod 892371481) ^ (366929 + 366929) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 366929 * (58 : ZMod 892371481) ^ 366929 := by rw [pow_add]
          _ = 337911779 := by rw [factor_7_18]; decide
      have factor_7_20 : (58 : ZMod 892371481) ^ 1467716 = 388818146 := by
        calc
          (58 : ZMod 892371481) ^ 1467716 = (58 : ZMod 892371481) ^ (733858 + 733858) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 733858 * (58 : ZMod 892371481) ^ 733858 := by rw [pow_add]
          _ = 388818146 := by rw [factor_7_19]; decide
      have factor_7_21 : (58 : ZMod 892371481) ^ 2935432 = 532468509 := by
        calc
          (58 : ZMod 892371481) ^ 2935432 = (58 : ZMod 892371481) ^ (1467716 + 1467716) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1467716 * (58 : ZMod 892371481) ^ 1467716 := by rw [pow_add]
          _ = 532468509 := by rw [factor_7_20]; decide
      have factor_7_22 : (58 : ZMod 892371481) ^ 5870865 = 792782293 := by
        calc
          (58 : ZMod 892371481) ^ 5870865 = (58 : ZMod 892371481) ^ (2935432 + 2935432 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 2935432 * (58 : ZMod 892371481) ^ 2935432) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 792782293 := by rw [factor_7_21]; decide
      have factor_7_23 : (58 : ZMod 892371481) ^ 11741730 = 543911372 := by
        calc
          (58 : ZMod 892371481) ^ 11741730 = (58 : ZMod 892371481) ^ (5870865 + 5870865) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 5870865 * (58 : ZMod 892371481) ^ 5870865 := by rw [pow_add]
          _ = 543911372 := by rw [factor_7_22]; decide
      have factor_7_24 : (58 : ZMod 892371481) ^ 23483460 = 29367886 := by
        calc
          (58 : ZMod 892371481) ^ 23483460 = (58 : ZMod 892371481) ^ (11741730 + 11741730) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 11741730 * (58 : ZMod 892371481) ^ 11741730 := by rw [pow_add]
          _ = 29367886 := by rw [factor_7_23]; decide
      have factor_7_25 : (58 : ZMod 892371481) ^ 46966920 = 153579901 := by
        calc
          (58 : ZMod 892371481) ^ 46966920 = (58 : ZMod 892371481) ^ (23483460 + 23483460) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 23483460 * (58 : ZMod 892371481) ^ 23483460 := by rw [pow_add]
          _ = 153579901 := by rw [factor_7_24]; decide
      change (58 : ZMod 892371481) ^ 46966920 ≠ 1
      rw [factor_7_25]
      decide
    ·
      have factor_8_0 : (58 : ZMod 892371481) ^ 1 = 58 := by norm_num
      have factor_8_1 : (58 : ZMod 892371481) ^ 2 = 3364 := by
        calc
          (58 : ZMod 892371481) ^ 2 = (58 : ZMod 892371481) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1 * (58 : ZMod 892371481) ^ 1 := by rw [pow_add]
          _ = 3364 := by rw [factor_8_0]; decide
      have factor_8_2 : (58 : ZMod 892371481) ^ 4 = 11316496 := by
        calc
          (58 : ZMod 892371481) ^ 4 = (58 : ZMod 892371481) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 2 * (58 : ZMod 892371481) ^ 2 := by rw [pow_add]
          _ = 11316496 := by rw [factor_8_1]; decide
      have factor_8_3 : (58 : ZMod 892371481) ^ 9 = 255684023 := by
        calc
          (58 : ZMod 892371481) ^ 9 = (58 : ZMod 892371481) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 4 * (58 : ZMod 892371481) ^ 4) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 255684023 := by rw [factor_8_2]; decide
      have factor_8_4 : (58 : ZMod 892371481) ^ 18 = 546938163 := by
        calc
          (58 : ZMod 892371481) ^ 18 = (58 : ZMod 892371481) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 9 * (58 : ZMod 892371481) ^ 9 := by rw [pow_add]
          _ = 546938163 := by rw [factor_8_3]; decide
      have factor_8_5 : (58 : ZMod 892371481) ^ 37 = 714401497 := by
        calc
          (58 : ZMod 892371481) ^ 37 = (58 : ZMod 892371481) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 18 * (58 : ZMod 892371481) ^ 18) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 714401497 := by rw [factor_8_4]; decide
      have factor_8_6 : (58 : ZMod 892371481) ^ 74 = 326176717 := by
        calc
          (58 : ZMod 892371481) ^ 74 = (58 : ZMod 892371481) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 37 * (58 : ZMod 892371481) ^ 37 := by rw [pow_add]
          _ = 326176717 := by rw [factor_8_5]; decide
      have factor_8_7 : (58 : ZMod 892371481) ^ 148 = 122689558 := by
        calc
          (58 : ZMod 892371481) ^ 148 = (58 : ZMod 892371481) ^ (74 + 74) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 74 * (58 : ZMod 892371481) ^ 74 := by rw [pow_add]
          _ = 122689558 := by rw [factor_8_6]; decide
      have factor_8_8 : (58 : ZMod 892371481) ^ 296 = 255286734 := by
        calc
          (58 : ZMod 892371481) ^ 296 = (58 : ZMod 892371481) ^ (148 + 148) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 148 * (58 : ZMod 892371481) ^ 148 := by rw [pow_add]
          _ = 255286734 := by rw [factor_8_7]; decide
      have factor_8_9 : (58 : ZMod 892371481) ^ 592 = 396958637 := by
        calc
          (58 : ZMod 892371481) ^ 592 = (58 : ZMod 892371481) ^ (296 + 296) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 296 * (58 : ZMod 892371481) ^ 296 := by rw [pow_add]
          _ = 396958637 := by rw [factor_8_8]; decide
      have factor_8_10 : (58 : ZMod 892371481) ^ 1184 = 457161381 := by
        calc
          (58 : ZMod 892371481) ^ 1184 = (58 : ZMod 892371481) ^ (592 + 592) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 592 * (58 : ZMod 892371481) ^ 592 := by rw [pow_add]
          _ = 457161381 := by rw [factor_8_9]; decide
      have factor_8_11 : (58 : ZMod 892371481) ^ 2368 = 557957737 := by
        calc
          (58 : ZMod 892371481) ^ 2368 = (58 : ZMod 892371481) ^ (1184 + 1184) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1184 * (58 : ZMod 892371481) ^ 1184 := by rw [pow_add]
          _ = 557957737 := by rw [factor_8_10]; decide
      have factor_8_12 : (58 : ZMod 892371481) ^ 4736 = 445001911 := by
        calc
          (58 : ZMod 892371481) ^ 4736 = (58 : ZMod 892371481) ^ (2368 + 2368) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 2368 * (58 : ZMod 892371481) ^ 2368 := by rw [pow_add]
          _ = 445001911 := by rw [factor_8_11]; decide
      have factor_8_13 : (58 : ZMod 892371481) ^ 9472 = 205967030 := by
        calc
          (58 : ZMod 892371481) ^ 9472 = (58 : ZMod 892371481) ^ (4736 + 4736) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 4736 * (58 : ZMod 892371481) ^ 4736 := by rw [pow_add]
          _ = 205967030 := by rw [factor_8_12]; decide
      have factor_8_14 : (58 : ZMod 892371481) ^ 18944 = 844763735 := by
        calc
          (58 : ZMod 892371481) ^ 18944 = (58 : ZMod 892371481) ^ (9472 + 9472) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 9472 * (58 : ZMod 892371481) ^ 9472 := by rw [pow_add]
          _ = 844763735 := by rw [factor_8_13]; decide
      have factor_8_15 : (58 : ZMod 892371481) ^ 37889 = 196996723 := by
        calc
          (58 : ZMod 892371481) ^ 37889 = (58 : ZMod 892371481) ^ (18944 + 18944 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 18944 * (58 : ZMod 892371481) ^ 18944) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 196996723 := by rw [factor_8_14]; decide
      have factor_8_16 : (58 : ZMod 892371481) ^ 75778 = 11652720 := by
        calc
          (58 : ZMod 892371481) ^ 75778 = (58 : ZMod 892371481) ^ (37889 + 37889) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 37889 * (58 : ZMod 892371481) ^ 37889 := by rw [pow_add]
          _ = 11652720 := by rw [factor_8_15]; decide
      have factor_8_17 : (58 : ZMod 892371481) ^ 151557 = 457744269 := by
        calc
          (58 : ZMod 892371481) ^ 151557 = (58 : ZMod 892371481) ^ (75778 + 75778 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 75778 * (58 : ZMod 892371481) ^ 75778) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 457744269 := by rw [factor_8_16]; decide
      have factor_8_18 : (58 : ZMod 892371481) ^ 303115 = 464849539 := by
        calc
          (58 : ZMod 892371481) ^ 303115 = (58 : ZMod 892371481) ^ (151557 + 151557 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 151557 * (58 : ZMod 892371481) ^ 151557) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 464849539 := by rw [factor_8_17]; decide
      have factor_8_19 : (58 : ZMod 892371481) ^ 606230 = 836118863 := by
        calc
          (58 : ZMod 892371481) ^ 606230 = (58 : ZMod 892371481) ^ (303115 + 303115) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 303115 * (58 : ZMod 892371481) ^ 303115 := by rw [pow_add]
          _ = 836118863 := by rw [factor_8_18]; decide
      have factor_8_20 : (58 : ZMod 892371481) ^ 1212461 = 337993168 := by
        calc
          (58 : ZMod 892371481) ^ 1212461 = (58 : ZMod 892371481) ^ (606230 + 606230 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 606230 * (58 : ZMod 892371481) ^ 606230) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 337993168 := by rw [factor_8_19]; decide
      have factor_8_21 : (58 : ZMod 892371481) ^ 2424922 = 484231803 := by
        calc
          (58 : ZMod 892371481) ^ 2424922 = (58 : ZMod 892371481) ^ (1212461 + 1212461) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 1212461 * (58 : ZMod 892371481) ^ 1212461 := by rw [pow_add]
          _ = 484231803 := by rw [factor_8_20]; decide
      have factor_8_22 : (58 : ZMod 892371481) ^ 4849845 = 506439062 := by
        calc
          (58 : ZMod 892371481) ^ 4849845 = (58 : ZMod 892371481) ^ (2424922 + 2424922 + 1) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = ((58 : ZMod 892371481) ^ 2424922 * (58 : ZMod 892371481) ^ 2424922) * (58 : ZMod 892371481) := by rw [pow_succ, pow_add]
          _ = 506439062 := by rw [factor_8_21]; decide
      have factor_8_23 : (58 : ZMod 892371481) ^ 9699690 = 861392762 := by
        calc
          (58 : ZMod 892371481) ^ 9699690 = (58 : ZMod 892371481) ^ (4849845 + 4849845) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 4849845 * (58 : ZMod 892371481) ^ 4849845 := by rw [pow_add]
          _ = 861392762 := by rw [factor_8_22]; decide
      have factor_8_24 : (58 : ZMod 892371481) ^ 19399380 = 646183574 := by
        calc
          (58 : ZMod 892371481) ^ 19399380 = (58 : ZMod 892371481) ^ (9699690 + 9699690) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 9699690 * (58 : ZMod 892371481) ^ 9699690 := by rw [pow_add]
          _ = 646183574 := by rw [factor_8_23]; decide
      have factor_8_25 : (58 : ZMod 892371481) ^ 38798760 = 416430642 := by
        calc
          (58 : ZMod 892371481) ^ 38798760 = (58 : ZMod 892371481) ^ (19399380 + 19399380) :=
            congrArg (fun n : ℕ => (58 : ZMod 892371481) ^ n) (by norm_num)
          _ = (58 : ZMod 892371481) ^ 19399380 * (58 : ZMod 892371481) ^ 19399380 := by rw [pow_add]
          _ = 416430642 := by rw [factor_8_24]; decide
      change (58 : ZMod 892371481) ^ 38798760 ≠ 1
      rw [factor_8_25]
      decide

#print axioms prime_lucas_892371481

end TotientTailPeriodKiller
end Erdos249257
