import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=23 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_3569485921 : Nat.Prime 3569485921 := by
  apply lucas_primality 3569485921 (37 : ZMod 3569485921)
  ·
      have fermat_0 : (37 : ZMod 3569485921) ^ 1 = 37 := by norm_num
      have fermat_1 : (37 : ZMod 3569485921) ^ 3 = 50653 := by
        calc
          (37 : ZMod 3569485921) ^ 3 = (37 : ZMod 3569485921) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 1 * (37 : ZMod 3569485921) ^ 1) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [fermat_0]; decide
      have fermat_2 : (37 : ZMod 3569485921) ^ 6 = 2565726409 := by
        calc
          (37 : ZMod 3569485921) ^ 6 = (37 : ZMod 3569485921) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 3 * (37 : ZMod 3569485921) ^ 3 := by rw [pow_add]
          _ = 2565726409 := by rw [fermat_1]; decide
      have fermat_3 : (37 : ZMod 3569485921) ^ 13 = 2480568791 := by
        calc
          (37 : ZMod 3569485921) ^ 13 = (37 : ZMod 3569485921) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 6 * (37 : ZMod 3569485921) ^ 6) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2480568791 := by rw [fermat_2]; decide
      have fermat_4 : (37 : ZMod 3569485921) ^ 26 = 1950281665 := by
        calc
          (37 : ZMod 3569485921) ^ 26 = (37 : ZMod 3569485921) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 13 * (37 : ZMod 3569485921) ^ 13 := by rw [pow_add]
          _ = 1950281665 := by rw [fermat_3]; decide
      have fermat_5 : (37 : ZMod 3569485921) ^ 53 = 287819013 := by
        calc
          (37 : ZMod 3569485921) ^ 53 = (37 : ZMod 3569485921) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 26 * (37 : ZMod 3569485921) ^ 26) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 287819013 := by rw [fermat_4]; decide
      have fermat_6 : (37 : ZMod 3569485921) ^ 106 = 957889446 := by
        calc
          (37 : ZMod 3569485921) ^ 106 = (37 : ZMod 3569485921) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 53 * (37 : ZMod 3569485921) ^ 53 := by rw [pow_add]
          _ = 957889446 := by rw [fermat_5]; decide
      have fermat_7 : (37 : ZMod 3569485921) ^ 212 = 525591360 := by
        calc
          (37 : ZMod 3569485921) ^ 212 = (37 : ZMod 3569485921) ^ (106 + 106) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 106 * (37 : ZMod 3569485921) ^ 106 := by rw [pow_add]
          _ = 525591360 := by rw [fermat_6]; decide
      have fermat_8 : (37 : ZMod 3569485921) ^ 425 = 1565058042 := by
        calc
          (37 : ZMod 3569485921) ^ 425 = (37 : ZMod 3569485921) ^ (212 + 212 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 212 * (37 : ZMod 3569485921) ^ 212) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1565058042 := by rw [fermat_7]; decide
      have fermat_9 : (37 : ZMod 3569485921) ^ 851 = 2511970250 := by
        calc
          (37 : ZMod 3569485921) ^ 851 = (37 : ZMod 3569485921) ^ (425 + 425 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 425 * (37 : ZMod 3569485921) ^ 425) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2511970250 := by rw [fermat_8]; decide
      have fermat_10 : (37 : ZMod 3569485921) ^ 1702 = 1663010791 := by
        calc
          (37 : ZMod 3569485921) ^ 1702 = (37 : ZMod 3569485921) ^ (851 + 851) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 851 * (37 : ZMod 3569485921) ^ 851 := by rw [pow_add]
          _ = 1663010791 := by rw [fermat_9]; decide
      have fermat_11 : (37 : ZMod 3569485921) ^ 3404 = 2967259671 := by
        calc
          (37 : ZMod 3569485921) ^ 3404 = (37 : ZMod 3569485921) ^ (1702 + 1702) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1702 * (37 : ZMod 3569485921) ^ 1702 := by rw [pow_add]
          _ = 2967259671 := by rw [fermat_10]; decide
      have fermat_12 : (37 : ZMod 3569485921) ^ 6808 = 2838267746 := by
        calc
          (37 : ZMod 3569485921) ^ 6808 = (37 : ZMod 3569485921) ^ (3404 + 3404) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 3404 * (37 : ZMod 3569485921) ^ 3404 := by rw [pow_add]
          _ = 2838267746 := by rw [fermat_11]; decide
      have fermat_13 : (37 : ZMod 3569485921) ^ 13616 = 2001751382 := by
        calc
          (37 : ZMod 3569485921) ^ 13616 = (37 : ZMod 3569485921) ^ (6808 + 6808) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 6808 * (37 : ZMod 3569485921) ^ 6808 := by rw [pow_add]
          _ = 2001751382 := by rw [fermat_12]; decide
      have fermat_14 : (37 : ZMod 3569485921) ^ 27233 = 1532210835 := by
        calc
          (37 : ZMod 3569485921) ^ 27233 = (37 : ZMod 3569485921) ^ (13616 + 13616 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 13616 * (37 : ZMod 3569485921) ^ 13616) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1532210835 := by rw [fermat_13]; decide
      have fermat_15 : (37 : ZMod 3569485921) ^ 54466 = 2357731060 := by
        calc
          (37 : ZMod 3569485921) ^ 54466 = (37 : ZMod 3569485921) ^ (27233 + 27233) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 27233 * (37 : ZMod 3569485921) ^ 27233 := by rw [pow_add]
          _ = 2357731060 := by rw [fermat_14]; decide
      have fermat_16 : (37 : ZMod 3569485921) ^ 108932 = 165186648 := by
        calc
          (37 : ZMod 3569485921) ^ 108932 = (37 : ZMod 3569485921) ^ (54466 + 54466) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 54466 * (37 : ZMod 3569485921) ^ 54466 := by rw [pow_add]
          _ = 165186648 := by rw [fermat_15]; decide
      have fermat_17 : (37 : ZMod 3569485921) ^ 217864 = 530180610 := by
        calc
          (37 : ZMod 3569485921) ^ 217864 = (37 : ZMod 3569485921) ^ (108932 + 108932) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 108932 * (37 : ZMod 3569485921) ^ 108932 := by rw [pow_add]
          _ = 530180610 := by rw [fermat_16]; decide
      have fermat_18 : (37 : ZMod 3569485921) ^ 435728 = 2783371492 := by
        calc
          (37 : ZMod 3569485921) ^ 435728 = (37 : ZMod 3569485921) ^ (217864 + 217864) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 217864 * (37 : ZMod 3569485921) ^ 217864 := by rw [pow_add]
          _ = 2783371492 := by rw [fermat_17]; decide
      have fermat_19 : (37 : ZMod 3569485921) ^ 871456 = 113970379 := by
        calc
          (37 : ZMod 3569485921) ^ 871456 = (37 : ZMod 3569485921) ^ (435728 + 435728) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 435728 * (37 : ZMod 3569485921) ^ 435728 := by rw [pow_add]
          _ = 113970379 := by rw [fermat_18]; decide
      have fermat_20 : (37 : ZMod 3569485921) ^ 1742913 = 1019885998 := by
        calc
          (37 : ZMod 3569485921) ^ 1742913 = (37 : ZMod 3569485921) ^ (871456 + 871456 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 871456 * (37 : ZMod 3569485921) ^ 871456) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1019885998 := by rw [fermat_19]; decide
      have fermat_21 : (37 : ZMod 3569485921) ^ 3485826 = 1299484051 := by
        calc
          (37 : ZMod 3569485921) ^ 3485826 = (37 : ZMod 3569485921) ^ (1742913 + 1742913) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1742913 * (37 : ZMod 3569485921) ^ 1742913 := by rw [pow_add]
          _ = 1299484051 := by rw [fermat_20]; decide
      have fermat_22 : (37 : ZMod 3569485921) ^ 6971652 = 2777920169 := by
        calc
          (37 : ZMod 3569485921) ^ 6971652 = (37 : ZMod 3569485921) ^ (3485826 + 3485826) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 3485826 * (37 : ZMod 3569485921) ^ 3485826 := by rw [pow_add]
          _ = 2777920169 := by rw [fermat_21]; decide
      have fermat_23 : (37 : ZMod 3569485921) ^ 13943304 = 61235207 := by
        calc
          (37 : ZMod 3569485921) ^ 13943304 = (37 : ZMod 3569485921) ^ (6971652 + 6971652) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 6971652 * (37 : ZMod 3569485921) ^ 6971652 := by rw [pow_add]
          _ = 61235207 := by rw [fermat_22]; decide
      have fermat_24 : (37 : ZMod 3569485921) ^ 27886608 = 2046836428 := by
        calc
          (37 : ZMod 3569485921) ^ 27886608 = (37 : ZMod 3569485921) ^ (13943304 + 13943304) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 13943304 * (37 : ZMod 3569485921) ^ 13943304 := by rw [pow_add]
          _ = 2046836428 := by rw [fermat_23]; decide
      have fermat_25 : (37 : ZMod 3569485921) ^ 55773217 = 2952236898 := by
        calc
          (37 : ZMod 3569485921) ^ 55773217 = (37 : ZMod 3569485921) ^ (27886608 + 27886608 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 27886608 * (37 : ZMod 3569485921) ^ 27886608) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2952236898 := by rw [fermat_24]; decide
      have fermat_26 : (37 : ZMod 3569485921) ^ 111546435 = 2766145227 := by
        calc
          (37 : ZMod 3569485921) ^ 111546435 = (37 : ZMod 3569485921) ^ (55773217 + 55773217 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 55773217 * (37 : ZMod 3569485921) ^ 55773217) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2766145227 := by rw [fermat_25]; decide
      have fermat_27 : (37 : ZMod 3569485921) ^ 223092870 = 1712337457 := by
        calc
          (37 : ZMod 3569485921) ^ 223092870 = (37 : ZMod 3569485921) ^ (111546435 + 111546435) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 111546435 * (37 : ZMod 3569485921) ^ 111546435 := by rw [pow_add]
          _ = 1712337457 := by rw [fermat_26]; decide
      have fermat_28 : (37 : ZMod 3569485921) ^ 446185740 = 2099741438 := by
        calc
          (37 : ZMod 3569485921) ^ 446185740 = (37 : ZMod 3569485921) ^ (223092870 + 223092870) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 223092870 * (37 : ZMod 3569485921) ^ 223092870 := by rw [pow_add]
          _ = 2099741438 := by rw [fermat_27]; decide
      have fermat_29 : (37 : ZMod 3569485921) ^ 892371480 = 2156390755 := by
        calc
          (37 : ZMod 3569485921) ^ 892371480 = (37 : ZMod 3569485921) ^ (446185740 + 446185740) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 446185740 * (37 : ZMod 3569485921) ^ 446185740 := by rw [pow_add]
          _ = 2156390755 := by rw [fermat_28]; decide
      have fermat_30 : (37 : ZMod 3569485921) ^ 1784742960 = 3569485920 := by
        calc
          (37 : ZMod 3569485921) ^ 1784742960 = (37 : ZMod 3569485921) ^ (892371480 + 892371480) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 892371480 * (37 : ZMod 3569485921) ^ 892371480 := by rw [pow_add]
          _ = 3569485920 := by rw [fermat_29]; decide
      have fermat_31 : (37 : ZMod 3569485921) ^ 3569485920 = 1 := by
        calc
          (37 : ZMod 3569485921) ^ 3569485920 = (37 : ZMod 3569485921) ^ (1784742960 + 1784742960) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1784742960 * (37 : ZMod 3569485921) ^ 1784742960 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 3569485921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (37 : ZMod 3569485921) ^ 1 = 37 := by norm_num
      have factor_0_1 : (37 : ZMod 3569485921) ^ 3 = 50653 := by
        calc
          (37 : ZMod 3569485921) ^ 3 = (37 : ZMod 3569485921) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 1 * (37 : ZMod 3569485921) ^ 1) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [factor_0_0]; decide
      have factor_0_2 : (37 : ZMod 3569485921) ^ 6 = 2565726409 := by
        calc
          (37 : ZMod 3569485921) ^ 6 = (37 : ZMod 3569485921) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 3 * (37 : ZMod 3569485921) ^ 3 := by rw [pow_add]
          _ = 2565726409 := by rw [factor_0_1]; decide
      have factor_0_3 : (37 : ZMod 3569485921) ^ 13 = 2480568791 := by
        calc
          (37 : ZMod 3569485921) ^ 13 = (37 : ZMod 3569485921) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 6 * (37 : ZMod 3569485921) ^ 6) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2480568791 := by rw [factor_0_2]; decide
      have factor_0_4 : (37 : ZMod 3569485921) ^ 26 = 1950281665 := by
        calc
          (37 : ZMod 3569485921) ^ 26 = (37 : ZMod 3569485921) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 13 * (37 : ZMod 3569485921) ^ 13 := by rw [pow_add]
          _ = 1950281665 := by rw [factor_0_3]; decide
      have factor_0_5 : (37 : ZMod 3569485921) ^ 53 = 287819013 := by
        calc
          (37 : ZMod 3569485921) ^ 53 = (37 : ZMod 3569485921) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 26 * (37 : ZMod 3569485921) ^ 26) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 287819013 := by rw [factor_0_4]; decide
      have factor_0_6 : (37 : ZMod 3569485921) ^ 106 = 957889446 := by
        calc
          (37 : ZMod 3569485921) ^ 106 = (37 : ZMod 3569485921) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 53 * (37 : ZMod 3569485921) ^ 53 := by rw [pow_add]
          _ = 957889446 := by rw [factor_0_5]; decide
      have factor_0_7 : (37 : ZMod 3569485921) ^ 212 = 525591360 := by
        calc
          (37 : ZMod 3569485921) ^ 212 = (37 : ZMod 3569485921) ^ (106 + 106) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 106 * (37 : ZMod 3569485921) ^ 106 := by rw [pow_add]
          _ = 525591360 := by rw [factor_0_6]; decide
      have factor_0_8 : (37 : ZMod 3569485921) ^ 425 = 1565058042 := by
        calc
          (37 : ZMod 3569485921) ^ 425 = (37 : ZMod 3569485921) ^ (212 + 212 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 212 * (37 : ZMod 3569485921) ^ 212) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1565058042 := by rw [factor_0_7]; decide
      have factor_0_9 : (37 : ZMod 3569485921) ^ 851 = 2511970250 := by
        calc
          (37 : ZMod 3569485921) ^ 851 = (37 : ZMod 3569485921) ^ (425 + 425 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 425 * (37 : ZMod 3569485921) ^ 425) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2511970250 := by rw [factor_0_8]; decide
      have factor_0_10 : (37 : ZMod 3569485921) ^ 1702 = 1663010791 := by
        calc
          (37 : ZMod 3569485921) ^ 1702 = (37 : ZMod 3569485921) ^ (851 + 851) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 851 * (37 : ZMod 3569485921) ^ 851 := by rw [pow_add]
          _ = 1663010791 := by rw [factor_0_9]; decide
      have factor_0_11 : (37 : ZMod 3569485921) ^ 3404 = 2967259671 := by
        calc
          (37 : ZMod 3569485921) ^ 3404 = (37 : ZMod 3569485921) ^ (1702 + 1702) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1702 * (37 : ZMod 3569485921) ^ 1702 := by rw [pow_add]
          _ = 2967259671 := by rw [factor_0_10]; decide
      have factor_0_12 : (37 : ZMod 3569485921) ^ 6808 = 2838267746 := by
        calc
          (37 : ZMod 3569485921) ^ 6808 = (37 : ZMod 3569485921) ^ (3404 + 3404) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 3404 * (37 : ZMod 3569485921) ^ 3404 := by rw [pow_add]
          _ = 2838267746 := by rw [factor_0_11]; decide
      have factor_0_13 : (37 : ZMod 3569485921) ^ 13616 = 2001751382 := by
        calc
          (37 : ZMod 3569485921) ^ 13616 = (37 : ZMod 3569485921) ^ (6808 + 6808) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 6808 * (37 : ZMod 3569485921) ^ 6808 := by rw [pow_add]
          _ = 2001751382 := by rw [factor_0_12]; decide
      have factor_0_14 : (37 : ZMod 3569485921) ^ 27233 = 1532210835 := by
        calc
          (37 : ZMod 3569485921) ^ 27233 = (37 : ZMod 3569485921) ^ (13616 + 13616 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 13616 * (37 : ZMod 3569485921) ^ 13616) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1532210835 := by rw [factor_0_13]; decide
      have factor_0_15 : (37 : ZMod 3569485921) ^ 54466 = 2357731060 := by
        calc
          (37 : ZMod 3569485921) ^ 54466 = (37 : ZMod 3569485921) ^ (27233 + 27233) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 27233 * (37 : ZMod 3569485921) ^ 27233 := by rw [pow_add]
          _ = 2357731060 := by rw [factor_0_14]; decide
      have factor_0_16 : (37 : ZMod 3569485921) ^ 108932 = 165186648 := by
        calc
          (37 : ZMod 3569485921) ^ 108932 = (37 : ZMod 3569485921) ^ (54466 + 54466) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 54466 * (37 : ZMod 3569485921) ^ 54466 := by rw [pow_add]
          _ = 165186648 := by rw [factor_0_15]; decide
      have factor_0_17 : (37 : ZMod 3569485921) ^ 217864 = 530180610 := by
        calc
          (37 : ZMod 3569485921) ^ 217864 = (37 : ZMod 3569485921) ^ (108932 + 108932) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 108932 * (37 : ZMod 3569485921) ^ 108932 := by rw [pow_add]
          _ = 530180610 := by rw [factor_0_16]; decide
      have factor_0_18 : (37 : ZMod 3569485921) ^ 435728 = 2783371492 := by
        calc
          (37 : ZMod 3569485921) ^ 435728 = (37 : ZMod 3569485921) ^ (217864 + 217864) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 217864 * (37 : ZMod 3569485921) ^ 217864 := by rw [pow_add]
          _ = 2783371492 := by rw [factor_0_17]; decide
      have factor_0_19 : (37 : ZMod 3569485921) ^ 871456 = 113970379 := by
        calc
          (37 : ZMod 3569485921) ^ 871456 = (37 : ZMod 3569485921) ^ (435728 + 435728) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 435728 * (37 : ZMod 3569485921) ^ 435728 := by rw [pow_add]
          _ = 113970379 := by rw [factor_0_18]; decide
      have factor_0_20 : (37 : ZMod 3569485921) ^ 1742913 = 1019885998 := by
        calc
          (37 : ZMod 3569485921) ^ 1742913 = (37 : ZMod 3569485921) ^ (871456 + 871456 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 871456 * (37 : ZMod 3569485921) ^ 871456) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1019885998 := by rw [factor_0_19]; decide
      have factor_0_21 : (37 : ZMod 3569485921) ^ 3485826 = 1299484051 := by
        calc
          (37 : ZMod 3569485921) ^ 3485826 = (37 : ZMod 3569485921) ^ (1742913 + 1742913) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1742913 * (37 : ZMod 3569485921) ^ 1742913 := by rw [pow_add]
          _ = 1299484051 := by rw [factor_0_20]; decide
      have factor_0_22 : (37 : ZMod 3569485921) ^ 6971652 = 2777920169 := by
        calc
          (37 : ZMod 3569485921) ^ 6971652 = (37 : ZMod 3569485921) ^ (3485826 + 3485826) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 3485826 * (37 : ZMod 3569485921) ^ 3485826 := by rw [pow_add]
          _ = 2777920169 := by rw [factor_0_21]; decide
      have factor_0_23 : (37 : ZMod 3569485921) ^ 13943304 = 61235207 := by
        calc
          (37 : ZMod 3569485921) ^ 13943304 = (37 : ZMod 3569485921) ^ (6971652 + 6971652) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 6971652 * (37 : ZMod 3569485921) ^ 6971652 := by rw [pow_add]
          _ = 61235207 := by rw [factor_0_22]; decide
      have factor_0_24 : (37 : ZMod 3569485921) ^ 27886608 = 2046836428 := by
        calc
          (37 : ZMod 3569485921) ^ 27886608 = (37 : ZMod 3569485921) ^ (13943304 + 13943304) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 13943304 * (37 : ZMod 3569485921) ^ 13943304 := by rw [pow_add]
          _ = 2046836428 := by rw [factor_0_23]; decide
      have factor_0_25 : (37 : ZMod 3569485921) ^ 55773217 = 2952236898 := by
        calc
          (37 : ZMod 3569485921) ^ 55773217 = (37 : ZMod 3569485921) ^ (27886608 + 27886608 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 27886608 * (37 : ZMod 3569485921) ^ 27886608) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2952236898 := by rw [factor_0_24]; decide
      have factor_0_26 : (37 : ZMod 3569485921) ^ 111546435 = 2766145227 := by
        calc
          (37 : ZMod 3569485921) ^ 111546435 = (37 : ZMod 3569485921) ^ (55773217 + 55773217 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 55773217 * (37 : ZMod 3569485921) ^ 55773217) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2766145227 := by rw [factor_0_25]; decide
      have factor_0_27 : (37 : ZMod 3569485921) ^ 223092870 = 1712337457 := by
        calc
          (37 : ZMod 3569485921) ^ 223092870 = (37 : ZMod 3569485921) ^ (111546435 + 111546435) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 111546435 * (37 : ZMod 3569485921) ^ 111546435 := by rw [pow_add]
          _ = 1712337457 := by rw [factor_0_26]; decide
      have factor_0_28 : (37 : ZMod 3569485921) ^ 446185740 = 2099741438 := by
        calc
          (37 : ZMod 3569485921) ^ 446185740 = (37 : ZMod 3569485921) ^ (223092870 + 223092870) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 223092870 * (37 : ZMod 3569485921) ^ 223092870 := by rw [pow_add]
          _ = 2099741438 := by rw [factor_0_27]; decide
      have factor_0_29 : (37 : ZMod 3569485921) ^ 892371480 = 2156390755 := by
        calc
          (37 : ZMod 3569485921) ^ 892371480 = (37 : ZMod 3569485921) ^ (446185740 + 446185740) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 446185740 * (37 : ZMod 3569485921) ^ 446185740 := by rw [pow_add]
          _ = 2156390755 := by rw [factor_0_28]; decide
      have factor_0_30 : (37 : ZMod 3569485921) ^ 1784742960 = 3569485920 := by
        calc
          (37 : ZMod 3569485921) ^ 1784742960 = (37 : ZMod 3569485921) ^ (892371480 + 892371480) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 892371480 * (37 : ZMod 3569485921) ^ 892371480 := by rw [pow_add]
          _ = 3569485920 := by rw [factor_0_29]; decide
      change (37 : ZMod 3569485921) ^ 1784742960 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (37 : ZMod 3569485921) ^ 1 = 37 := by norm_num
      have factor_1_1 : (37 : ZMod 3569485921) ^ 2 = 1369 := by
        calc
          (37 : ZMod 3569485921) ^ 2 = (37 : ZMod 3569485921) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1 * (37 : ZMod 3569485921) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_1_0]; decide
      have factor_1_2 : (37 : ZMod 3569485921) ^ 4 = 1874161 := by
        calc
          (37 : ZMod 3569485921) ^ 4 = (37 : ZMod 3569485921) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 2 * (37 : ZMod 3569485921) ^ 2 := by rw [pow_add]
          _ = 1874161 := by rw [factor_1_1]; decide
      have factor_1_3 : (37 : ZMod 3569485921) ^ 8 = 105307657 := by
        calc
          (37 : ZMod 3569485921) ^ 8 = (37 : ZMod 3569485921) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 4 * (37 : ZMod 3569485921) ^ 4 := by rw [pow_add]
          _ = 105307657 := by rw [factor_1_2]; decide
      have factor_1_4 : (37 : ZMod 3569485921) ^ 17 = 1154736847 := by
        calc
          (37 : ZMod 3569485921) ^ 17 = (37 : ZMod 3569485921) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 8 * (37 : ZMod 3569485921) ^ 8) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1154736847 := by rw [factor_1_3]; decide
      have factor_1_5 : (37 : ZMod 3569485921) ^ 35 = 3251092673 := by
        calc
          (37 : ZMod 3569485921) ^ 35 = (37 : ZMod 3569485921) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 17 * (37 : ZMod 3569485921) ^ 17) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 3251092673 := by rw [factor_1_4]; decide
      have factor_1_6 : (37 : ZMod 3569485921) ^ 70 = 3538968464 := by
        calc
          (37 : ZMod 3569485921) ^ 70 = (37 : ZMod 3569485921) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 35 * (37 : ZMod 3569485921) ^ 35 := by rw [pow_add]
          _ = 3538968464 := by rw [factor_1_5]; decide
      have factor_1_7 : (37 : ZMod 3569485921) ^ 141 = 1156737817 := by
        calc
          (37 : ZMod 3569485921) ^ 141 = (37 : ZMod 3569485921) ^ (70 + 70 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 70 * (37 : ZMod 3569485921) ^ 70) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1156737817 := by rw [factor_1_6]; decide
      have factor_1_8 : (37 : ZMod 3569485921) ^ 283 = 2394153531 := by
        calc
          (37 : ZMod 3569485921) ^ 283 = (37 : ZMod 3569485921) ^ (141 + 141 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 141 * (37 : ZMod 3569485921) ^ 141) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2394153531 := by rw [factor_1_7]; decide
      have factor_1_9 : (37 : ZMod 3569485921) ^ 567 = 1162830716 := by
        calc
          (37 : ZMod 3569485921) ^ 567 = (37 : ZMod 3569485921) ^ (283 + 283 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 283 * (37 : ZMod 3569485921) ^ 283) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1162830716 := by rw [factor_1_8]; decide
      have factor_1_10 : (37 : ZMod 3569485921) ^ 1134 = 876287926 := by
        calc
          (37 : ZMod 3569485921) ^ 1134 = (37 : ZMod 3569485921) ^ (567 + 567) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 567 * (37 : ZMod 3569485921) ^ 567 := by rw [pow_add]
          _ = 876287926 := by rw [factor_1_9]; decide
      have factor_1_11 : (37 : ZMod 3569485921) ^ 2269 = 1571395103 := by
        calc
          (37 : ZMod 3569485921) ^ 2269 = (37 : ZMod 3569485921) ^ (1134 + 1134 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 1134 * (37 : ZMod 3569485921) ^ 1134) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1571395103 := by rw [factor_1_10]; decide
      have factor_1_12 : (37 : ZMod 3569485921) ^ 4538 = 1090807604 := by
        calc
          (37 : ZMod 3569485921) ^ 4538 = (37 : ZMod 3569485921) ^ (2269 + 2269) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 2269 * (37 : ZMod 3569485921) ^ 2269 := by rw [pow_add]
          _ = 1090807604 := by rw [factor_1_11]; decide
      have factor_1_13 : (37 : ZMod 3569485921) ^ 9077 = 309579857 := by
        calc
          (37 : ZMod 3569485921) ^ 9077 = (37 : ZMod 3569485921) ^ (4538 + 4538 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 4538 * (37 : ZMod 3569485921) ^ 4538) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 309579857 := by rw [factor_1_12]; decide
      have factor_1_14 : (37 : ZMod 3569485921) ^ 18155 = 2999966194 := by
        calc
          (37 : ZMod 3569485921) ^ 18155 = (37 : ZMod 3569485921) ^ (9077 + 9077 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 9077 * (37 : ZMod 3569485921) ^ 9077) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2999966194 := by rw [factor_1_13]; decide
      have factor_1_15 : (37 : ZMod 3569485921) ^ 36310 = 1709373381 := by
        calc
          (37 : ZMod 3569485921) ^ 36310 = (37 : ZMod 3569485921) ^ (18155 + 18155) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 18155 * (37 : ZMod 3569485921) ^ 18155 := by rw [pow_add]
          _ = 1709373381 := by rw [factor_1_14]; decide
      have factor_1_16 : (37 : ZMod 3569485921) ^ 72621 = 621399699 := by
        calc
          (37 : ZMod 3569485921) ^ 72621 = (37 : ZMod 3569485921) ^ (36310 + 36310 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 36310 * (37 : ZMod 3569485921) ^ 36310) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 621399699 := by rw [factor_1_15]; decide
      have factor_1_17 : (37 : ZMod 3569485921) ^ 145242 = 1009426515 := by
        calc
          (37 : ZMod 3569485921) ^ 145242 = (37 : ZMod 3569485921) ^ (72621 + 72621) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 72621 * (37 : ZMod 3569485921) ^ 72621 := by rw [pow_add]
          _ = 1009426515 := by rw [factor_1_16]; decide
      have factor_1_18 : (37 : ZMod 3569485921) ^ 290485 = 1515942566 := by
        calc
          (37 : ZMod 3569485921) ^ 290485 = (37 : ZMod 3569485921) ^ (145242 + 145242 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 145242 * (37 : ZMod 3569485921) ^ 145242) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1515942566 := by rw [factor_1_17]; decide
      have factor_1_19 : (37 : ZMod 3569485921) ^ 580971 = 2233871456 := by
        calc
          (37 : ZMod 3569485921) ^ 580971 = (37 : ZMod 3569485921) ^ (290485 + 290485 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 290485 * (37 : ZMod 3569485921) ^ 290485) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2233871456 := by rw [factor_1_18]; decide
      have factor_1_20 : (37 : ZMod 3569485921) ^ 1161942 = 626765268 := by
        calc
          (37 : ZMod 3569485921) ^ 1161942 = (37 : ZMod 3569485921) ^ (580971 + 580971) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 580971 * (37 : ZMod 3569485921) ^ 580971 := by rw [pow_add]
          _ = 626765268 := by rw [factor_1_19]; decide
      have factor_1_21 : (37 : ZMod 3569485921) ^ 2323884 = 374950565 := by
        calc
          (37 : ZMod 3569485921) ^ 2323884 = (37 : ZMod 3569485921) ^ (1161942 + 1161942) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1161942 * (37 : ZMod 3569485921) ^ 1161942 := by rw [pow_add]
          _ = 374950565 := by rw [factor_1_20]; decide
      have factor_1_22 : (37 : ZMod 3569485921) ^ 4647768 = 221418622 := by
        calc
          (37 : ZMod 3569485921) ^ 4647768 = (37 : ZMod 3569485921) ^ (2323884 + 2323884) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 2323884 * (37 : ZMod 3569485921) ^ 2323884 := by rw [pow_add]
          _ = 221418622 := by rw [factor_1_21]; decide
      have factor_1_23 : (37 : ZMod 3569485921) ^ 9295536 = 2384740716 := by
        calc
          (37 : ZMod 3569485921) ^ 9295536 = (37 : ZMod 3569485921) ^ (4647768 + 4647768) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 4647768 * (37 : ZMod 3569485921) ^ 4647768 := by rw [pow_add]
          _ = 2384740716 := by rw [factor_1_22]; decide
      have factor_1_24 : (37 : ZMod 3569485921) ^ 18591072 = 1409596516 := by
        calc
          (37 : ZMod 3569485921) ^ 18591072 = (37 : ZMod 3569485921) ^ (9295536 + 9295536) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 9295536 * (37 : ZMod 3569485921) ^ 9295536 := by rw [pow_add]
          _ = 1409596516 := by rw [factor_1_23]; decide
      have factor_1_25 : (37 : ZMod 3569485921) ^ 37182145 = 183466547 := by
        calc
          (37 : ZMod 3569485921) ^ 37182145 = (37 : ZMod 3569485921) ^ (18591072 + 18591072 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 18591072 * (37 : ZMod 3569485921) ^ 18591072) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 183466547 := by rw [factor_1_24]; decide
      have factor_1_26 : (37 : ZMod 3569485921) ^ 74364290 = 52975047 := by
        calc
          (37 : ZMod 3569485921) ^ 74364290 = (37 : ZMod 3569485921) ^ (37182145 + 37182145) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 37182145 * (37 : ZMod 3569485921) ^ 37182145 := by rw [pow_add]
          _ = 52975047 := by rw [factor_1_25]; decide
      have factor_1_27 : (37 : ZMod 3569485921) ^ 148728580 = 787160562 := by
        calc
          (37 : ZMod 3569485921) ^ 148728580 = (37 : ZMod 3569485921) ^ (74364290 + 74364290) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 74364290 * (37 : ZMod 3569485921) ^ 74364290 := by rw [pow_add]
          _ = 787160562 := by rw [factor_1_26]; decide
      have factor_1_28 : (37 : ZMod 3569485921) ^ 297457160 = 736816292 := by
        calc
          (37 : ZMod 3569485921) ^ 297457160 = (37 : ZMod 3569485921) ^ (148728580 + 148728580) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 148728580 * (37 : ZMod 3569485921) ^ 148728580 := by rw [pow_add]
          _ = 736816292 := by rw [factor_1_27]; decide
      have factor_1_29 : (37 : ZMod 3569485921) ^ 594914320 = 3380920145 := by
        calc
          (37 : ZMod 3569485921) ^ 594914320 = (37 : ZMod 3569485921) ^ (297457160 + 297457160) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 297457160 * (37 : ZMod 3569485921) ^ 297457160 := by rw [pow_add]
          _ = 3380920145 := by rw [factor_1_28]; decide
      have factor_1_30 : (37 : ZMod 3569485921) ^ 1189828640 = 3380920144 := by
        calc
          (37 : ZMod 3569485921) ^ 1189828640 = (37 : ZMod 3569485921) ^ (594914320 + 594914320) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 594914320 * (37 : ZMod 3569485921) ^ 594914320 := by rw [pow_add]
          _ = 3380920144 := by rw [factor_1_29]; decide
      change (37 : ZMod 3569485921) ^ 1189828640 ≠ 1
      rw [factor_1_30]
      decide
    ·
      have factor_2_0 : (37 : ZMod 3569485921) ^ 1 = 37 := by norm_num
      have factor_2_1 : (37 : ZMod 3569485921) ^ 2 = 1369 := by
        calc
          (37 : ZMod 3569485921) ^ 2 = (37 : ZMod 3569485921) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1 * (37 : ZMod 3569485921) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_2_0]; decide
      have factor_2_2 : (37 : ZMod 3569485921) ^ 5 = 69343957 := by
        calc
          (37 : ZMod 3569485921) ^ 5 = (37 : ZMod 3569485921) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 2 * (37 : ZMod 3569485921) ^ 2) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 69343957 := by rw [factor_2_1]; decide
      have factor_2_3 : (37 : ZMod 3569485921) ^ 10 = 1386745593 := by
        calc
          (37 : ZMod 3569485921) ^ 10 = (37 : ZMod 3569485921) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 5 * (37 : ZMod 3569485921) ^ 5 := by rw [pow_add]
          _ = 1386745593 := by rw [factor_2_2]; decide
      have factor_2_4 : (37 : ZMod 3569485921) ^ 21 = 1297437672 := by
        calc
          (37 : ZMod 3569485921) ^ 21 = (37 : ZMod 3569485921) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 10 * (37 : ZMod 3569485921) ^ 10) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1297437672 := by rw [factor_2_3]; decide
      have factor_2_5 : (37 : ZMod 3569485921) ^ 42 = 3033373162 := by
        calc
          (37 : ZMod 3569485921) ^ 42 = (37 : ZMod 3569485921) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 21 * (37 : ZMod 3569485921) ^ 21 := by rw [pow_add]
          _ = 3033373162 := by rw [factor_2_4]; decide
      have factor_2_6 : (37 : ZMod 3569485921) ^ 85 = 3214801709 := by
        calc
          (37 : ZMod 3569485921) ^ 85 = (37 : ZMod 3569485921) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 42 * (37 : ZMod 3569485921) ^ 42) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 3214801709 := by rw [factor_2_5]; decide
      have factor_2_7 : (37 : ZMod 3569485921) ^ 170 = 2313657045 := by
        calc
          (37 : ZMod 3569485921) ^ 170 = (37 : ZMod 3569485921) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 85 * (37 : ZMod 3569485921) ^ 85 := by rw [pow_add]
          _ = 2313657045 := by rw [factor_2_6]; decide
      have factor_2_8 : (37 : ZMod 3569485921) ^ 340 = 1428781800 := by
        calc
          (37 : ZMod 3569485921) ^ 340 = (37 : ZMod 3569485921) ^ (170 + 170) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 170 * (37 : ZMod 3569485921) ^ 170 := by rw [pow_add]
          _ = 1428781800 := by rw [factor_2_7]; decide
      have factor_2_9 : (37 : ZMod 3569485921) ^ 680 = 2835979235 := by
        calc
          (37 : ZMod 3569485921) ^ 680 = (37 : ZMod 3569485921) ^ (340 + 340) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 340 * (37 : ZMod 3569485921) ^ 340 := by rw [pow_add]
          _ = 2835979235 := by rw [factor_2_8]; decide
      have factor_2_10 : (37 : ZMod 3569485921) ^ 1361 = 582117537 := by
        calc
          (37 : ZMod 3569485921) ^ 1361 = (37 : ZMod 3569485921) ^ (680 + 680 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 680 * (37 : ZMod 3569485921) ^ 680) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 582117537 := by rw [factor_2_9]; decide
      have factor_2_11 : (37 : ZMod 3569485921) ^ 2723 = 3473446246 := by
        calc
          (37 : ZMod 3569485921) ^ 2723 = (37 : ZMod 3569485921) ^ (1361 + 1361 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 1361 * (37 : ZMod 3569485921) ^ 1361) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 3473446246 := by rw [factor_2_10]; decide
      have factor_2_12 : (37 : ZMod 3569485921) ^ 5446 = 3303495047 := by
        calc
          (37 : ZMod 3569485921) ^ 5446 = (37 : ZMod 3569485921) ^ (2723 + 2723) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 2723 * (37 : ZMod 3569485921) ^ 2723 := by rw [pow_add]
          _ = 3303495047 := by rw [factor_2_11]; decide
      have factor_2_13 : (37 : ZMod 3569485921) ^ 10893 = 1524990953 := by
        calc
          (37 : ZMod 3569485921) ^ 10893 = (37 : ZMod 3569485921) ^ (5446 + 5446 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 5446 * (37 : ZMod 3569485921) ^ 5446) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1524990953 := by rw [factor_2_12]; decide
      have factor_2_14 : (37 : ZMod 3569485921) ^ 21786 = 3426841586 := by
        calc
          (37 : ZMod 3569485921) ^ 21786 = (37 : ZMod 3569485921) ^ (10893 + 10893) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 10893 * (37 : ZMod 3569485921) ^ 10893 := by rw [pow_add]
          _ = 3426841586 := by rw [factor_2_13]; decide
      have factor_2_15 : (37 : ZMod 3569485921) ^ 43572 = 1570157771 := by
        calc
          (37 : ZMod 3569485921) ^ 43572 = (37 : ZMod 3569485921) ^ (21786 + 21786) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 21786 * (37 : ZMod 3569485921) ^ 21786 := by rw [pow_add]
          _ = 1570157771 := by rw [factor_2_14]; decide
      have factor_2_16 : (37 : ZMod 3569485921) ^ 87145 = 2084608489 := by
        calc
          (37 : ZMod 3569485921) ^ 87145 = (37 : ZMod 3569485921) ^ (43572 + 43572 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 43572 * (37 : ZMod 3569485921) ^ 43572) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2084608489 := by rw [factor_2_15]; decide
      have factor_2_17 : (37 : ZMod 3569485921) ^ 174291 = 297651168 := by
        calc
          (37 : ZMod 3569485921) ^ 174291 = (37 : ZMod 3569485921) ^ (87145 + 87145 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 87145 * (37 : ZMod 3569485921) ^ 87145) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 297651168 := by rw [factor_2_16]; decide
      have factor_2_18 : (37 : ZMod 3569485921) ^ 348582 = 3109253063 := by
        calc
          (37 : ZMod 3569485921) ^ 348582 = (37 : ZMod 3569485921) ^ (174291 + 174291) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 174291 * (37 : ZMod 3569485921) ^ 174291 := by rw [pow_add]
          _ = 3109253063 := by rw [factor_2_17]; decide
      have factor_2_19 : (37 : ZMod 3569485921) ^ 697165 = 3336025897 := by
        calc
          (37 : ZMod 3569485921) ^ 697165 = (37 : ZMod 3569485921) ^ (348582 + 348582 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 348582 * (37 : ZMod 3569485921) ^ 348582) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 3336025897 := by rw [factor_2_18]; decide
      have factor_2_20 : (37 : ZMod 3569485921) ^ 1394330 = 2876667908 := by
        calc
          (37 : ZMod 3569485921) ^ 1394330 = (37 : ZMod 3569485921) ^ (697165 + 697165) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 697165 * (37 : ZMod 3569485921) ^ 697165 := by rw [pow_add]
          _ = 2876667908 := by rw [factor_2_19]; decide
      have factor_2_21 : (37 : ZMod 3569485921) ^ 2788660 = 3136047761 := by
        calc
          (37 : ZMod 3569485921) ^ 2788660 = (37 : ZMod 3569485921) ^ (1394330 + 1394330) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1394330 * (37 : ZMod 3569485921) ^ 1394330 := by rw [pow_add]
          _ = 3136047761 := by rw [factor_2_20]; decide
      have factor_2_22 : (37 : ZMod 3569485921) ^ 5577321 = 1532741324 := by
        calc
          (37 : ZMod 3569485921) ^ 5577321 = (37 : ZMod 3569485921) ^ (2788660 + 2788660 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 2788660 * (37 : ZMod 3569485921) ^ 2788660) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1532741324 := by rw [factor_2_21]; decide
      have factor_2_23 : (37 : ZMod 3569485921) ^ 11154643 = 1356510889 := by
        calc
          (37 : ZMod 3569485921) ^ 11154643 = (37 : ZMod 3569485921) ^ (5577321 + 5577321 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 5577321 * (37 : ZMod 3569485921) ^ 5577321) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1356510889 := by rw [factor_2_22]; decide
      have factor_2_24 : (37 : ZMod 3569485921) ^ 22309287 = 3410123821 := by
        calc
          (37 : ZMod 3569485921) ^ 22309287 = (37 : ZMod 3569485921) ^ (11154643 + 11154643 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 11154643 * (37 : ZMod 3569485921) ^ 11154643) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 3410123821 := by rw [factor_2_23]; decide
      have factor_2_25 : (37 : ZMod 3569485921) ^ 44618574 = 540073412 := by
        calc
          (37 : ZMod 3569485921) ^ 44618574 = (37 : ZMod 3569485921) ^ (22309287 + 22309287) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 22309287 * (37 : ZMod 3569485921) ^ 22309287 := by rw [pow_add]
          _ = 540073412 := by rw [factor_2_24]; decide
      have factor_2_26 : (37 : ZMod 3569485921) ^ 89237148 = 1204365015 := by
        calc
          (37 : ZMod 3569485921) ^ 89237148 = (37 : ZMod 3569485921) ^ (44618574 + 44618574) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 44618574 * (37 : ZMod 3569485921) ^ 44618574 := by rw [pow_add]
          _ = 1204365015 := by rw [factor_2_25]; decide
      have factor_2_27 : (37 : ZMod 3569485921) ^ 178474296 = 554117444 := by
        calc
          (37 : ZMod 3569485921) ^ 178474296 = (37 : ZMod 3569485921) ^ (89237148 + 89237148) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 89237148 * (37 : ZMod 3569485921) ^ 89237148 := by rw [pow_add]
          _ = 554117444 := by rw [factor_2_26]; decide
      have factor_2_28 : (37 : ZMod 3569485921) ^ 356948592 = 1541076147 := by
        calc
          (37 : ZMod 3569485921) ^ 356948592 = (37 : ZMod 3569485921) ^ (178474296 + 178474296) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 178474296 * (37 : ZMod 3569485921) ^ 178474296 := by rw [pow_add]
          _ = 1541076147 := by rw [factor_2_27]; decide
      have factor_2_29 : (37 : ZMod 3569485921) ^ 713897184 = 3439263151 := by
        calc
          (37 : ZMod 3569485921) ^ 713897184 = (37 : ZMod 3569485921) ^ (356948592 + 356948592) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 356948592 * (37 : ZMod 3569485921) ^ 356948592 := by rw [pow_add]
          _ = 3439263151 := by rw [factor_2_28]; decide
      change (37 : ZMod 3569485921) ^ 713897184 ≠ 1
      rw [factor_2_29]
      decide
    ·
      have factor_3_0 : (37 : ZMod 3569485921) ^ 1 = 37 := by norm_num
      have factor_3_1 : (37 : ZMod 3569485921) ^ 3 = 50653 := by
        calc
          (37 : ZMod 3569485921) ^ 3 = (37 : ZMod 3569485921) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 1 * (37 : ZMod 3569485921) ^ 1) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [factor_3_0]; decide
      have factor_3_2 : (37 : ZMod 3569485921) ^ 7 = 2125243187 := by
        calc
          (37 : ZMod 3569485921) ^ 7 = (37 : ZMod 3569485921) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 3 * (37 : ZMod 3569485921) ^ 3) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2125243187 := by rw [factor_3_1]; decide
      have factor_3_3 : (37 : ZMod 3569485921) ^ 15 = 1317564008 := by
        calc
          (37 : ZMod 3569485921) ^ 15 = (37 : ZMod 3569485921) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 7 * (37 : ZMod 3569485921) ^ 7) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1317564008 := by rw [factor_3_2]; decide
      have factor_3_4 : (37 : ZMod 3569485921) ^ 30 = 2530397749 := by
        calc
          (37 : ZMod 3569485921) ^ 30 = (37 : ZMod 3569485921) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 15 * (37 : ZMod 3569485921) ^ 15 := by rw [pow_add]
          _ = 2530397749 := by rw [factor_3_3]; decide
      have factor_3_5 : (37 : ZMod 3569485921) ^ 60 = 2568381148 := by
        calc
          (37 : ZMod 3569485921) ^ 60 = (37 : ZMod 3569485921) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 30 * (37 : ZMod 3569485921) ^ 30 := by rw [pow_add]
          _ = 2568381148 := by rw [factor_3_4]; decide
      have factor_3_6 : (37 : ZMod 3569485921) ^ 121 = 1567789300 := by
        calc
          (37 : ZMod 3569485921) ^ 121 = (37 : ZMod 3569485921) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 60 * (37 : ZMod 3569485921) ^ 60) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1567789300 := by rw [factor_3_5]; decide
      have factor_3_7 : (37 : ZMod 3569485921) ^ 243 = 1258437812 := by
        calc
          (37 : ZMod 3569485921) ^ 243 = (37 : ZMod 3569485921) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 121 * (37 : ZMod 3569485921) ^ 121) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1258437812 := by rw [factor_3_6]; decide
      have factor_3_8 : (37 : ZMod 3569485921) ^ 486 = 125860251 := by
        calc
          (37 : ZMod 3569485921) ^ 486 = (37 : ZMod 3569485921) ^ (243 + 243) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 243 * (37 : ZMod 3569485921) ^ 243 := by rw [pow_add]
          _ = 125860251 := by rw [factor_3_7]; decide
      have factor_3_9 : (37 : ZMod 3569485921) ^ 972 = 2521104203 := by
        calc
          (37 : ZMod 3569485921) ^ 972 = (37 : ZMod 3569485921) ^ (486 + 486) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 486 * (37 : ZMod 3569485921) ^ 486 := by rw [pow_add]
          _ = 2521104203 := by rw [factor_3_8]; decide
      have factor_3_10 : (37 : ZMod 3569485921) ^ 1945 = 1119549513 := by
        calc
          (37 : ZMod 3569485921) ^ 1945 = (37 : ZMod 3569485921) ^ (972 + 972 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 972 * (37 : ZMod 3569485921) ^ 972) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1119549513 := by rw [factor_3_9]; decide
      have factor_3_11 : (37 : ZMod 3569485921) ^ 3890 = 1751291538 := by
        calc
          (37 : ZMod 3569485921) ^ 3890 = (37 : ZMod 3569485921) ^ (1945 + 1945) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1945 * (37 : ZMod 3569485921) ^ 1945 := by rw [pow_add]
          _ = 1751291538 := by rw [factor_3_10]; decide
      have factor_3_12 : (37 : ZMod 3569485921) ^ 7780 = 2203013657 := by
        calc
          (37 : ZMod 3569485921) ^ 7780 = (37 : ZMod 3569485921) ^ (3890 + 3890) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 3890 * (37 : ZMod 3569485921) ^ 3890 := by rw [pow_add]
          _ = 2203013657 := by rw [factor_3_11]; decide
      have factor_3_13 : (37 : ZMod 3569485921) ^ 15561 = 1533356479 := by
        calc
          (37 : ZMod 3569485921) ^ 15561 = (37 : ZMod 3569485921) ^ (7780 + 7780 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 7780 * (37 : ZMod 3569485921) ^ 7780) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1533356479 := by rw [factor_3_12]; decide
      have factor_3_14 : (37 : ZMod 3569485921) ^ 31123 = 58712720 := by
        calc
          (37 : ZMod 3569485921) ^ 31123 = (37 : ZMod 3569485921) ^ (15561 + 15561 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 15561 * (37 : ZMod 3569485921) ^ 15561) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 58712720 := by rw [factor_3_13]; decide
      have factor_3_15 : (37 : ZMod 3569485921) ^ 62246 = 2434395544 := by
        calc
          (37 : ZMod 3569485921) ^ 62246 = (37 : ZMod 3569485921) ^ (31123 + 31123) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 31123 * (37 : ZMod 3569485921) ^ 31123 := by rw [pow_add]
          _ = 2434395544 := by rw [factor_3_14]; decide
      have factor_3_16 : (37 : ZMod 3569485921) ^ 124493 = 2759144750 := by
        calc
          (37 : ZMod 3569485921) ^ 124493 = (37 : ZMod 3569485921) ^ (62246 + 62246 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 62246 * (37 : ZMod 3569485921) ^ 62246) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2759144750 := by rw [factor_3_15]; decide
      have factor_3_17 : (37 : ZMod 3569485921) ^ 248987 = 1222812920 := by
        calc
          (37 : ZMod 3569485921) ^ 248987 = (37 : ZMod 3569485921) ^ (124493 + 124493 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 124493 * (37 : ZMod 3569485921) ^ 124493) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1222812920 := by rw [factor_3_16]; decide
      have factor_3_18 : (37 : ZMod 3569485921) ^ 497975 = 1601725110 := by
        calc
          (37 : ZMod 3569485921) ^ 497975 = (37 : ZMod 3569485921) ^ (248987 + 248987 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 248987 * (37 : ZMod 3569485921) ^ 248987) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1601725110 := by rw [factor_3_17]; decide
      have factor_3_19 : (37 : ZMod 3569485921) ^ 995950 = 1541035257 := by
        calc
          (37 : ZMod 3569485921) ^ 995950 = (37 : ZMod 3569485921) ^ (497975 + 497975) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 497975 * (37 : ZMod 3569485921) ^ 497975 := by rw [pow_add]
          _ = 1541035257 := by rw [factor_3_18]; decide
      have factor_3_20 : (37 : ZMod 3569485921) ^ 1991900 = 173880417 := by
        calc
          (37 : ZMod 3569485921) ^ 1991900 = (37 : ZMod 3569485921) ^ (995950 + 995950) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 995950 * (37 : ZMod 3569485921) ^ 995950 := by rw [pow_add]
          _ = 173880417 := by rw [factor_3_19]; decide
      have factor_3_21 : (37 : ZMod 3569485921) ^ 3983801 = 2801854885 := by
        calc
          (37 : ZMod 3569485921) ^ 3983801 = (37 : ZMod 3569485921) ^ (1991900 + 1991900 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 1991900 * (37 : ZMod 3569485921) ^ 1991900) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2801854885 := by rw [factor_3_20]; decide
      have factor_3_22 : (37 : ZMod 3569485921) ^ 7967602 = 222566947 := by
        calc
          (37 : ZMod 3569485921) ^ 7967602 = (37 : ZMod 3569485921) ^ (3983801 + 3983801) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 3983801 * (37 : ZMod 3569485921) ^ 3983801 := by rw [pow_add]
          _ = 222566947 := by rw [factor_3_21]; decide
      have factor_3_23 : (37 : ZMod 3569485921) ^ 15935205 = 3354951919 := by
        calc
          (37 : ZMod 3569485921) ^ 15935205 = (37 : ZMod 3569485921) ^ (7967602 + 7967602 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 7967602 * (37 : ZMod 3569485921) ^ 7967602) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 3354951919 := by rw [factor_3_22]; decide
      have factor_3_24 : (37 : ZMod 3569485921) ^ 31870410 = 772311476 := by
        calc
          (37 : ZMod 3569485921) ^ 31870410 = (37 : ZMod 3569485921) ^ (15935205 + 15935205) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 15935205 * (37 : ZMod 3569485921) ^ 15935205 := by rw [pow_add]
          _ = 772311476 := by rw [factor_3_23]; decide
      have factor_3_25 : (37 : ZMod 3569485921) ^ 63740820 = 2836143239 := by
        calc
          (37 : ZMod 3569485921) ^ 63740820 = (37 : ZMod 3569485921) ^ (31870410 + 31870410) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 31870410 * (37 : ZMod 3569485921) ^ 31870410 := by rw [pow_add]
          _ = 2836143239 := by rw [factor_3_24]; decide
      have factor_3_26 : (37 : ZMod 3569485921) ^ 127481640 = 889841075 := by
        calc
          (37 : ZMod 3569485921) ^ 127481640 = (37 : ZMod 3569485921) ^ (63740820 + 63740820) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 63740820 * (37 : ZMod 3569485921) ^ 63740820 := by rw [pow_add]
          _ = 889841075 := by rw [factor_3_25]; decide
      have factor_3_27 : (37 : ZMod 3569485921) ^ 254963280 = 854637044 := by
        calc
          (37 : ZMod 3569485921) ^ 254963280 = (37 : ZMod 3569485921) ^ (127481640 + 127481640) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 127481640 * (37 : ZMod 3569485921) ^ 127481640 := by rw [pow_add]
          _ = 854637044 := by rw [factor_3_26]; decide
      have factor_3_28 : (37 : ZMod 3569485921) ^ 509926560 = 1674695939 := by
        calc
          (37 : ZMod 3569485921) ^ 509926560 = (37 : ZMod 3569485921) ^ (254963280 + 254963280) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 254963280 * (37 : ZMod 3569485921) ^ 254963280 := by rw [pow_add]
          _ = 1674695939 := by rw [factor_3_27]; decide
      change (37 : ZMod 3569485921) ^ 509926560 ≠ 1
      rw [factor_3_28]
      decide
    ·
      have factor_4_0 : (37 : ZMod 3569485921) ^ 1 = 37 := by norm_num
      have factor_4_1 : (37 : ZMod 3569485921) ^ 2 = 1369 := by
        calc
          (37 : ZMod 3569485921) ^ 2 = (37 : ZMod 3569485921) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1 * (37 : ZMod 3569485921) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_4_0]; decide
      have factor_4_2 : (37 : ZMod 3569485921) ^ 4 = 1874161 := by
        calc
          (37 : ZMod 3569485921) ^ 4 = (37 : ZMod 3569485921) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 2 * (37 : ZMod 3569485921) ^ 2 := by rw [pow_add]
          _ = 1874161 := by rw [factor_4_1]; decide
      have factor_4_3 : (37 : ZMod 3569485921) ^ 9 = 326897388 := by
        calc
          (37 : ZMod 3569485921) ^ 9 = (37 : ZMod 3569485921) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 4 * (37 : ZMod 3569485921) ^ 4) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 326897388 := by rw [factor_4_2]; decide
      have factor_4_4 : (37 : ZMod 3569485921) ^ 19 = 3121966461 := by
        calc
          (37 : ZMod 3569485921) ^ 19 = (37 : ZMod 3569485921) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 9 * (37 : ZMod 3569485921) ^ 9) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 3121966461 := by rw [factor_4_3]; decide
      have factor_4_5 : (37 : ZMod 3569485921) ^ 38 = 2933686055 := by
        calc
          (37 : ZMod 3569485921) ^ 38 = (37 : ZMod 3569485921) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 19 * (37 : ZMod 3569485921) ^ 19 := by rw [pow_add]
          _ = 2933686055 := by rw [factor_4_4]; decide
      have factor_4_6 : (37 : ZMod 3569485921) ^ 77 = 2618380470 := by
        calc
          (37 : ZMod 3569485921) ^ 77 = (37 : ZMod 3569485921) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 38 * (37 : ZMod 3569485921) ^ 38) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2618380470 := by rw [factor_4_5]; decide
      have factor_4_7 : (37 : ZMod 3569485921) ^ 154 = 1186164390 := by
        calc
          (37 : ZMod 3569485921) ^ 154 = (37 : ZMod 3569485921) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 77 * (37 : ZMod 3569485921) ^ 77 := by rw [pow_add]
          _ = 1186164390 := by rw [factor_4_6]; decide
      have factor_4_8 : (37 : ZMod 3569485921) ^ 309 = 3049375335 := by
        calc
          (37 : ZMod 3569485921) ^ 309 = (37 : ZMod 3569485921) ^ (154 + 154 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 154 * (37 : ZMod 3569485921) ^ 154) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 3049375335 := by rw [factor_4_7]; decide
      have factor_4_9 : (37 : ZMod 3569485921) ^ 618 = 3406304208 := by
        calc
          (37 : ZMod 3569485921) ^ 618 = (37 : ZMod 3569485921) ^ (309 + 309) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 309 * (37 : ZMod 3569485921) ^ 309 := by rw [pow_add]
          _ = 3406304208 := by rw [factor_4_8]; decide
      have factor_4_10 : (37 : ZMod 3569485921) ^ 1237 = 2418655023 := by
        calc
          (37 : ZMod 3569485921) ^ 1237 = (37 : ZMod 3569485921) ^ (618 + 618 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 618 * (37 : ZMod 3569485921) ^ 618) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2418655023 := by rw [factor_4_9]; decide
      have factor_4_11 : (37 : ZMod 3569485921) ^ 2475 = 1566702118 := by
        calc
          (37 : ZMod 3569485921) ^ 2475 = (37 : ZMod 3569485921) ^ (1237 + 1237 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 1237 * (37 : ZMod 3569485921) ^ 1237) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1566702118 := by rw [factor_4_10]; decide
      have factor_4_12 : (37 : ZMod 3569485921) ^ 4951 = 1063729835 := by
        calc
          (37 : ZMod 3569485921) ^ 4951 = (37 : ZMod 3569485921) ^ (2475 + 2475 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 2475 * (37 : ZMod 3569485921) ^ 2475) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1063729835 := by rw [factor_4_11]; decide
      have factor_4_13 : (37 : ZMod 3569485921) ^ 9902 = 285953191 := by
        calc
          (37 : ZMod 3569485921) ^ 9902 = (37 : ZMod 3569485921) ^ (4951 + 4951) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 4951 * (37 : ZMod 3569485921) ^ 4951 := by rw [pow_add]
          _ = 285953191 := by rw [factor_4_12]; decide
      have factor_4_14 : (37 : ZMod 3569485921) ^ 19805 = 1214984441 := by
        calc
          (37 : ZMod 3569485921) ^ 19805 = (37 : ZMod 3569485921) ^ (9902 + 9902 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 9902 * (37 : ZMod 3569485921) ^ 9902) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1214984441 := by rw [factor_4_13]; decide
      have factor_4_15 : (37 : ZMod 3569485921) ^ 39611 = 2782285613 := by
        calc
          (37 : ZMod 3569485921) ^ 39611 = (37 : ZMod 3569485921) ^ (19805 + 19805 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 19805 * (37 : ZMod 3569485921) ^ 19805) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2782285613 := by rw [factor_4_14]; decide
      have factor_4_16 : (37 : ZMod 3569485921) ^ 79223 = 2714436472 := by
        calc
          (37 : ZMod 3569485921) ^ 79223 = (37 : ZMod 3569485921) ^ (39611 + 39611 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 39611 * (37 : ZMod 3569485921) ^ 39611) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2714436472 := by rw [factor_4_15]; decide
      have factor_4_17 : (37 : ZMod 3569485921) ^ 158446 = 809380553 := by
        calc
          (37 : ZMod 3569485921) ^ 158446 = (37 : ZMod 3569485921) ^ (79223 + 79223) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 79223 * (37 : ZMod 3569485921) ^ 79223 := by rw [pow_add]
          _ = 809380553 := by rw [factor_4_16]; decide
      have factor_4_18 : (37 : ZMod 3569485921) ^ 316893 = 3195788344 := by
        calc
          (37 : ZMod 3569485921) ^ 316893 = (37 : ZMod 3569485921) ^ (158446 + 158446 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 158446 * (37 : ZMod 3569485921) ^ 158446) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 3195788344 := by rw [factor_4_17]; decide
      have factor_4_19 : (37 : ZMod 3569485921) ^ 633786 = 3274851363 := by
        calc
          (37 : ZMod 3569485921) ^ 633786 = (37 : ZMod 3569485921) ^ (316893 + 316893) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 316893 * (37 : ZMod 3569485921) ^ 316893 := by rw [pow_add]
          _ = 3274851363 := by rw [factor_4_18]; decide
      have factor_4_20 : (37 : ZMod 3569485921) ^ 1267573 = 2280297474 := by
        calc
          (37 : ZMod 3569485921) ^ 1267573 = (37 : ZMod 3569485921) ^ (633786 + 633786 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 633786 * (37 : ZMod 3569485921) ^ 633786) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2280297474 := by rw [factor_4_19]; decide
      have factor_4_21 : (37 : ZMod 3569485921) ^ 2535146 = 847475503 := by
        calc
          (37 : ZMod 3569485921) ^ 2535146 = (37 : ZMod 3569485921) ^ (1267573 + 1267573) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1267573 * (37 : ZMod 3569485921) ^ 1267573 := by rw [pow_add]
          _ = 847475503 := by rw [factor_4_20]; decide
      have factor_4_22 : (37 : ZMod 3569485921) ^ 5070292 = 899639039 := by
        calc
          (37 : ZMod 3569485921) ^ 5070292 = (37 : ZMod 3569485921) ^ (2535146 + 2535146) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 2535146 * (37 : ZMod 3569485921) ^ 2535146 := by rw [pow_add]
          _ = 899639039 := by rw [factor_4_21]; decide
      have factor_4_23 : (37 : ZMod 3569485921) ^ 10140585 = 1277167962 := by
        calc
          (37 : ZMod 3569485921) ^ 10140585 = (37 : ZMod 3569485921) ^ (5070292 + 5070292 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 5070292 * (37 : ZMod 3569485921) ^ 5070292) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1277167962 := by rw [factor_4_22]; decide
      have factor_4_24 : (37 : ZMod 3569485921) ^ 20281170 = 2292883197 := by
        calc
          (37 : ZMod 3569485921) ^ 20281170 = (37 : ZMod 3569485921) ^ (10140585 + 10140585) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 10140585 * (37 : ZMod 3569485921) ^ 10140585 := by rw [pow_add]
          _ = 2292883197 := by rw [factor_4_23]; decide
      have factor_4_25 : (37 : ZMod 3569485921) ^ 40562340 = 3455864566 := by
        calc
          (37 : ZMod 3569485921) ^ 40562340 = (37 : ZMod 3569485921) ^ (20281170 + 20281170) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 20281170 * (37 : ZMod 3569485921) ^ 20281170 := by rw [pow_add]
          _ = 3455864566 := by rw [factor_4_24]; decide
      have factor_4_26 : (37 : ZMod 3569485921) ^ 81124680 = 2608752431 := by
        calc
          (37 : ZMod 3569485921) ^ 81124680 = (37 : ZMod 3569485921) ^ (40562340 + 40562340) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 40562340 * (37 : ZMod 3569485921) ^ 40562340 := by rw [pow_add]
          _ = 2608752431 := by rw [factor_4_25]; decide
      have factor_4_27 : (37 : ZMod 3569485921) ^ 162249360 = 433953291 := by
        calc
          (37 : ZMod 3569485921) ^ 162249360 = (37 : ZMod 3569485921) ^ (81124680 + 81124680) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 81124680 * (37 : ZMod 3569485921) ^ 81124680 := by rw [pow_add]
          _ = 433953291 := by rw [factor_4_26]; decide
      have factor_4_28 : (37 : ZMod 3569485921) ^ 324498720 = 798385656 := by
        calc
          (37 : ZMod 3569485921) ^ 324498720 = (37 : ZMod 3569485921) ^ (162249360 + 162249360) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 162249360 * (37 : ZMod 3569485921) ^ 162249360 := by rw [pow_add]
          _ = 798385656 := by rw [factor_4_27]; decide
      change (37 : ZMod 3569485921) ^ 324498720 ≠ 1
      rw [factor_4_28]
      decide
    ·
      have factor_5_0 : (37 : ZMod 3569485921) ^ 1 = 37 := by norm_num
      have factor_5_1 : (37 : ZMod 3569485921) ^ 2 = 1369 := by
        calc
          (37 : ZMod 3569485921) ^ 2 = (37 : ZMod 3569485921) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1 * (37 : ZMod 3569485921) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_5_0]; decide
      have factor_5_2 : (37 : ZMod 3569485921) ^ 4 = 1874161 := by
        calc
          (37 : ZMod 3569485921) ^ 4 = (37 : ZMod 3569485921) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 2 * (37 : ZMod 3569485921) ^ 2 := by rw [pow_add]
          _ = 1874161 := by rw [factor_5_1]; decide
      have factor_5_3 : (37 : ZMod 3569485921) ^ 8 = 105307657 := by
        calc
          (37 : ZMod 3569485921) ^ 8 = (37 : ZMod 3569485921) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 4 * (37 : ZMod 3569485921) ^ 4 := by rw [pow_add]
          _ = 105307657 := by rw [factor_5_2]; decide
      have factor_5_4 : (37 : ZMod 3569485921) ^ 16 = 2346551323 := by
        calc
          (37 : ZMod 3569485921) ^ 16 = (37 : ZMod 3569485921) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 8 * (37 : ZMod 3569485921) ^ 8 := by rw [pow_add]
          _ = 2346551323 := by rw [factor_5_3]; decide
      have factor_5_5 : (37 : ZMod 3569485921) ^ 32 = 1713175011 := by
        calc
          (37 : ZMod 3569485921) ^ 32 = (37 : ZMod 3569485921) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 16 * (37 : ZMod 3569485921) ^ 16 := by rw [pow_add]
          _ = 1713175011 := by rw [factor_5_4]; decide
      have factor_5_6 : (37 : ZMod 3569485921) ^ 65 = 2346442537 := by
        calc
          (37 : ZMod 3569485921) ^ 65 = (37 : ZMod 3569485921) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 32 * (37 : ZMod 3569485921) ^ 32) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2346442537 := by rw [factor_5_5]; decide
      have factor_5_7 : (37 : ZMod 3569485921) ^ 130 = 2545943918 := by
        calc
          (37 : ZMod 3569485921) ^ 130 = (37 : ZMod 3569485921) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 65 * (37 : ZMod 3569485921) ^ 65 := by rw [pow_add]
          _ = 2545943918 := by rw [factor_5_6]; decide
      have factor_5_8 : (37 : ZMod 3569485921) ^ 261 = 2869836385 := by
        calc
          (37 : ZMod 3569485921) ^ 261 = (37 : ZMod 3569485921) ^ (130 + 130 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 130 * (37 : ZMod 3569485921) ^ 130) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2869836385 := by rw [factor_5_7]; decide
      have factor_5_9 : (37 : ZMod 3569485921) ^ 523 = 1555297565 := by
        calc
          (37 : ZMod 3569485921) ^ 523 = (37 : ZMod 3569485921) ^ (261 + 261 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 261 * (37 : ZMod 3569485921) ^ 261) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1555297565 := by rw [factor_5_8]; decide
      have factor_5_10 : (37 : ZMod 3569485921) ^ 1047 = 3185497437 := by
        calc
          (37 : ZMod 3569485921) ^ 1047 = (37 : ZMod 3569485921) ^ (523 + 523 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 523 * (37 : ZMod 3569485921) ^ 523) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 3185497437 := by rw [factor_5_9]; decide
      have factor_5_11 : (37 : ZMod 3569485921) ^ 2094 = 2211332344 := by
        calc
          (37 : ZMod 3569485921) ^ 2094 = (37 : ZMod 3569485921) ^ (1047 + 1047) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1047 * (37 : ZMod 3569485921) ^ 1047 := by rw [pow_add]
          _ = 2211332344 := by rw [factor_5_10]; decide
      have factor_5_12 : (37 : ZMod 3569485921) ^ 4189 = 1331492421 := by
        calc
          (37 : ZMod 3569485921) ^ 4189 = (37 : ZMod 3569485921) ^ (2094 + 2094 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 2094 * (37 : ZMod 3569485921) ^ 2094) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1331492421 := by rw [factor_5_11]; decide
      have factor_5_13 : (37 : ZMod 3569485921) ^ 8379 = 1660506344 := by
        calc
          (37 : ZMod 3569485921) ^ 8379 = (37 : ZMod 3569485921) ^ (4189 + 4189 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 4189 * (37 : ZMod 3569485921) ^ 4189) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1660506344 := by rw [factor_5_12]; decide
      have factor_5_14 : (37 : ZMod 3569485921) ^ 16758 = 444690754 := by
        calc
          (37 : ZMod 3569485921) ^ 16758 = (37 : ZMod 3569485921) ^ (8379 + 8379) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 8379 * (37 : ZMod 3569485921) ^ 8379 := by rw [pow_add]
          _ = 444690754 := by rw [factor_5_13]; decide
      have factor_5_15 : (37 : ZMod 3569485921) ^ 33517 = 1615560939 := by
        calc
          (37 : ZMod 3569485921) ^ 33517 = (37 : ZMod 3569485921) ^ (16758 + 16758 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 16758 * (37 : ZMod 3569485921) ^ 16758) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1615560939 := by rw [factor_5_14]; decide
      have factor_5_16 : (37 : ZMod 3569485921) ^ 67035 = 2890725837 := by
        calc
          (37 : ZMod 3569485921) ^ 67035 = (37 : ZMod 3569485921) ^ (33517 + 33517 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 33517 * (37 : ZMod 3569485921) ^ 33517) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2890725837 := by rw [factor_5_15]; decide
      have factor_5_17 : (37 : ZMod 3569485921) ^ 134070 = 1163432739 := by
        calc
          (37 : ZMod 3569485921) ^ 134070 = (37 : ZMod 3569485921) ^ (67035 + 67035) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 67035 * (37 : ZMod 3569485921) ^ 67035 := by rw [pow_add]
          _ = 1163432739 := by rw [factor_5_16]; decide
      have factor_5_18 : (37 : ZMod 3569485921) ^ 268140 = 2165554488 := by
        calc
          (37 : ZMod 3569485921) ^ 268140 = (37 : ZMod 3569485921) ^ (134070 + 134070) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 134070 * (37 : ZMod 3569485921) ^ 134070 := by rw [pow_add]
          _ = 2165554488 := by rw [factor_5_17]; decide
      have factor_5_19 : (37 : ZMod 3569485921) ^ 536280 = 3309192801 := by
        calc
          (37 : ZMod 3569485921) ^ 536280 = (37 : ZMod 3569485921) ^ (268140 + 268140) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 268140 * (37 : ZMod 3569485921) ^ 268140 := by rw [pow_add]
          _ = 3309192801 := by rw [factor_5_18]; decide
      have factor_5_20 : (37 : ZMod 3569485921) ^ 1072561 = 2316344405 := by
        calc
          (37 : ZMod 3569485921) ^ 1072561 = (37 : ZMod 3569485921) ^ (536280 + 536280 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 536280 * (37 : ZMod 3569485921) ^ 536280) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2316344405 := by rw [factor_5_19]; decide
      have factor_5_21 : (37 : ZMod 3569485921) ^ 2145123 = 1275023851 := by
        calc
          (37 : ZMod 3569485921) ^ 2145123 = (37 : ZMod 3569485921) ^ (1072561 + 1072561 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 1072561 * (37 : ZMod 3569485921) ^ 1072561) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1275023851 := by rw [factor_5_20]; decide
      have factor_5_22 : (37 : ZMod 3569485921) ^ 4290247 = 2864161580 := by
        calc
          (37 : ZMod 3569485921) ^ 4290247 = (37 : ZMod 3569485921) ^ (2145123 + 2145123 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 2145123 * (37 : ZMod 3569485921) ^ 2145123) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2864161580 := by rw [factor_5_21]; decide
      have factor_5_23 : (37 : ZMod 3569485921) ^ 8580495 = 769714865 := by
        calc
          (37 : ZMod 3569485921) ^ 8580495 = (37 : ZMod 3569485921) ^ (4290247 + 4290247 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 4290247 * (37 : ZMod 3569485921) ^ 4290247) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 769714865 := by rw [factor_5_22]; decide
      have factor_5_24 : (37 : ZMod 3569485921) ^ 17160990 = 2552807270 := by
        calc
          (37 : ZMod 3569485921) ^ 17160990 = (37 : ZMod 3569485921) ^ (8580495 + 8580495) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 8580495 * (37 : ZMod 3569485921) ^ 8580495 := by rw [pow_add]
          _ = 2552807270 := by rw [factor_5_23]; decide
      have factor_5_25 : (37 : ZMod 3569485921) ^ 34321980 = 1834884035 := by
        calc
          (37 : ZMod 3569485921) ^ 34321980 = (37 : ZMod 3569485921) ^ (17160990 + 17160990) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 17160990 * (37 : ZMod 3569485921) ^ 17160990 := by rw [pow_add]
          _ = 1834884035 := by rw [factor_5_24]; decide
      have factor_5_26 : (37 : ZMod 3569485921) ^ 68643960 = 1885017772 := by
        calc
          (37 : ZMod 3569485921) ^ 68643960 = (37 : ZMod 3569485921) ^ (34321980 + 34321980) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 34321980 * (37 : ZMod 3569485921) ^ 34321980 := by rw [pow_add]
          _ = 1885017772 := by rw [factor_5_25]; decide
      have factor_5_27 : (37 : ZMod 3569485921) ^ 137287920 = 2119715470 := by
        calc
          (37 : ZMod 3569485921) ^ 137287920 = (37 : ZMod 3569485921) ^ (68643960 + 68643960) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 68643960 * (37 : ZMod 3569485921) ^ 68643960 := by rw [pow_add]
          _ = 2119715470 := by rw [factor_5_26]; decide
      have factor_5_28 : (37 : ZMod 3569485921) ^ 274575840 = 1901390449 := by
        calc
          (37 : ZMod 3569485921) ^ 274575840 = (37 : ZMod 3569485921) ^ (137287920 + 137287920) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 137287920 * (37 : ZMod 3569485921) ^ 137287920 := by rw [pow_add]
          _ = 1901390449 := by rw [factor_5_27]; decide
      change (37 : ZMod 3569485921) ^ 274575840 ≠ 1
      rw [factor_5_28]
      decide
    ·
      have factor_6_0 : (37 : ZMod 3569485921) ^ 1 = 37 := by norm_num
      have factor_6_1 : (37 : ZMod 3569485921) ^ 3 = 50653 := by
        calc
          (37 : ZMod 3569485921) ^ 3 = (37 : ZMod 3569485921) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 1 * (37 : ZMod 3569485921) ^ 1) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [factor_6_0]; decide
      have factor_6_2 : (37 : ZMod 3569485921) ^ 6 = 2565726409 := by
        calc
          (37 : ZMod 3569485921) ^ 6 = (37 : ZMod 3569485921) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 3 * (37 : ZMod 3569485921) ^ 3 := by rw [pow_add]
          _ = 2565726409 := by rw [factor_6_1]; decide
      have factor_6_3 : (37 : ZMod 3569485921) ^ 12 = 3057692766 := by
        calc
          (37 : ZMod 3569485921) ^ 12 = (37 : ZMod 3569485921) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 6 * (37 : ZMod 3569485921) ^ 6 := by rw [pow_add]
          _ = 3057692766 := by rw [factor_6_2]; decide
      have factor_6_4 : (37 : ZMod 3569485921) ^ 25 = 1885689572 := by
        calc
          (37 : ZMod 3569485921) ^ 25 = (37 : ZMod 3569485921) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 12 * (37 : ZMod 3569485921) ^ 12) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1885689572 := by rw [factor_6_3]; decide
      have factor_6_5 : (37 : ZMod 3569485921) ^ 50 = 2670372679 := by
        calc
          (37 : ZMod 3569485921) ^ 50 = (37 : ZMod 3569485921) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 25 * (37 : ZMod 3569485921) ^ 25 := by rw [pow_add]
          _ = 2670372679 := by rw [factor_6_4]; decide
      have factor_6_6 : (37 : ZMod 3569485921) ^ 100 = 864168800 := by
        calc
          (37 : ZMod 3569485921) ^ 100 = (37 : ZMod 3569485921) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 50 * (37 : ZMod 3569485921) ^ 50 := by rw [pow_add]
          _ = 864168800 := by rw [factor_6_5]; decide
      have factor_6_7 : (37 : ZMod 3569485921) ^ 200 = 2402414440 := by
        calc
          (37 : ZMod 3569485921) ^ 200 = (37 : ZMod 3569485921) ^ (100 + 100) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 100 * (37 : ZMod 3569485921) ^ 100 := by rw [pow_add]
          _ = 2402414440 := by rw [factor_6_6]; decide
      have factor_6_8 : (37 : ZMod 3569485921) ^ 400 = 3090321687 := by
        calc
          (37 : ZMod 3569485921) ^ 400 = (37 : ZMod 3569485921) ^ (200 + 200) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 200 * (37 : ZMod 3569485921) ^ 200 := by rw [pow_add]
          _ = 3090321687 := by rw [factor_6_7]; decide
      have factor_6_9 : (37 : ZMod 3569485921) ^ 800 = 1476192547 := by
        calc
          (37 : ZMod 3569485921) ^ 800 = (37 : ZMod 3569485921) ^ (400 + 400) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 400 * (37 : ZMod 3569485921) ^ 400 := by rw [pow_add]
          _ = 1476192547 := by rw [factor_6_8]; decide
      have factor_6_10 : (37 : ZMod 3569485921) ^ 1601 = 21540972 := by
        calc
          (37 : ZMod 3569485921) ^ 1601 = (37 : ZMod 3569485921) ^ (800 + 800 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 800 * (37 : ZMod 3569485921) ^ 800) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 21540972 := by rw [factor_6_9]; decide
      have factor_6_11 : (37 : ZMod 3569485921) ^ 3203 = 3028680813 := by
        calc
          (37 : ZMod 3569485921) ^ 3203 = (37 : ZMod 3569485921) ^ (1601 + 1601 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 1601 * (37 : ZMod 3569485921) ^ 1601) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 3028680813 := by rw [factor_6_10]; decide
      have factor_6_12 : (37 : ZMod 3569485921) ^ 6407 = 1389763144 := by
        calc
          (37 : ZMod 3569485921) ^ 6407 = (37 : ZMod 3569485921) ^ (3203 + 3203 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 3203 * (37 : ZMod 3569485921) ^ 3203) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1389763144 := by rw [factor_6_11]; decide
      have factor_6_13 : (37 : ZMod 3569485921) ^ 12815 = 447670232 := by
        calc
          (37 : ZMod 3569485921) ^ 12815 = (37 : ZMod 3569485921) ^ (6407 + 6407 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 6407 * (37 : ZMod 3569485921) ^ 6407) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 447670232 := by rw [factor_6_12]; decide
      have factor_6_14 : (37 : ZMod 3569485921) ^ 25631 = 3020423248 := by
        calc
          (37 : ZMod 3569485921) ^ 25631 = (37 : ZMod 3569485921) ^ (12815 + 12815 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 12815 * (37 : ZMod 3569485921) ^ 12815) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 3020423248 := by rw [factor_6_13]; decide
      have factor_6_15 : (37 : ZMod 3569485921) ^ 51262 = 973392560 := by
        calc
          (37 : ZMod 3569485921) ^ 51262 = (37 : ZMod 3569485921) ^ (25631 + 25631) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 25631 * (37 : ZMod 3569485921) ^ 25631 := by rw [pow_add]
          _ = 973392560 := by rw [factor_6_14]; decide
      have factor_6_16 : (37 : ZMod 3569485921) ^ 102524 = 2030550834 := by
        calc
          (37 : ZMod 3569485921) ^ 102524 = (37 : ZMod 3569485921) ^ (51262 + 51262) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 51262 * (37 : ZMod 3569485921) ^ 51262 := by rw [pow_add]
          _ = 2030550834 := by rw [factor_6_15]; decide
      have factor_6_17 : (37 : ZMod 3569485921) ^ 205048 = 615691692 := by
        calc
          (37 : ZMod 3569485921) ^ 205048 = (37 : ZMod 3569485921) ^ (102524 + 102524) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 102524 * (37 : ZMod 3569485921) ^ 102524 := by rw [pow_add]
          _ = 615691692 := by rw [factor_6_16]; decide
      have factor_6_18 : (37 : ZMod 3569485921) ^ 410097 = 3091528331 := by
        calc
          (37 : ZMod 3569485921) ^ 410097 = (37 : ZMod 3569485921) ^ (205048 + 205048 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 205048 * (37 : ZMod 3569485921) ^ 205048) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 3091528331 := by rw [factor_6_17]; decide
      have factor_6_19 : (37 : ZMod 3569485921) ^ 820194 = 3339733441 := by
        calc
          (37 : ZMod 3569485921) ^ 820194 = (37 : ZMod 3569485921) ^ (410097 + 410097) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 410097 * (37 : ZMod 3569485921) ^ 410097 := by rw [pow_add]
          _ = 3339733441 := by rw [factor_6_18]; decide
      have factor_6_20 : (37 : ZMod 3569485921) ^ 1640388 = 1758936620 := by
        calc
          (37 : ZMod 3569485921) ^ 1640388 = (37 : ZMod 3569485921) ^ (820194 + 820194) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 820194 * (37 : ZMod 3569485921) ^ 820194 := by rw [pow_add]
          _ = 1758936620 := by rw [factor_6_19]; decide
      have factor_6_21 : (37 : ZMod 3569485921) ^ 3280777 = 3474487055 := by
        calc
          (37 : ZMod 3569485921) ^ 3280777 = (37 : ZMod 3569485921) ^ (1640388 + 1640388 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 1640388 * (37 : ZMod 3569485921) ^ 1640388) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 3474487055 := by rw [factor_6_20]; decide
      have factor_6_22 : (37 : ZMod 3569485921) ^ 6561555 = 1270972880 := by
        calc
          (37 : ZMod 3569485921) ^ 6561555 = (37 : ZMod 3569485921) ^ (3280777 + 3280777 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 3280777 * (37 : ZMod 3569485921) ^ 3280777) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1270972880 := by rw [factor_6_21]; decide
      have factor_6_23 : (37 : ZMod 3569485921) ^ 13123110 = 1660703102 := by
        calc
          (37 : ZMod 3569485921) ^ 13123110 = (37 : ZMod 3569485921) ^ (6561555 + 6561555) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 6561555 * (37 : ZMod 3569485921) ^ 6561555 := by rw [pow_add]
          _ = 1660703102 := by rw [factor_6_22]; decide
      have factor_6_24 : (37 : ZMod 3569485921) ^ 26246220 = 2046337510 := by
        calc
          (37 : ZMod 3569485921) ^ 26246220 = (37 : ZMod 3569485921) ^ (13123110 + 13123110) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 13123110 * (37 : ZMod 3569485921) ^ 13123110 := by rw [pow_add]
          _ = 2046337510 := by rw [factor_6_23]; decide
      have factor_6_25 : (37 : ZMod 3569485921) ^ 52492440 = 581553644 := by
        calc
          (37 : ZMod 3569485921) ^ 52492440 = (37 : ZMod 3569485921) ^ (26246220 + 26246220) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 26246220 * (37 : ZMod 3569485921) ^ 26246220 := by rw [pow_add]
          _ = 581553644 := by rw [factor_6_24]; decide
      have factor_6_26 : (37 : ZMod 3569485921) ^ 104984880 = 1147054859 := by
        calc
          (37 : ZMod 3569485921) ^ 104984880 = (37 : ZMod 3569485921) ^ (52492440 + 52492440) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 52492440 * (37 : ZMod 3569485921) ^ 52492440 := by rw [pow_add]
          _ = 1147054859 := by rw [factor_6_25]; decide
      have factor_6_27 : (37 : ZMod 3569485921) ^ 209969760 = 1232016263 := by
        calc
          (37 : ZMod 3569485921) ^ 209969760 = (37 : ZMod 3569485921) ^ (104984880 + 104984880) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 104984880 * (37 : ZMod 3569485921) ^ 104984880 := by rw [pow_add]
          _ = 1232016263 := by rw [factor_6_26]; decide
      change (37 : ZMod 3569485921) ^ 209969760 ≠ 1
      rw [factor_6_27]
      decide
    ·
      have factor_7_0 : (37 : ZMod 3569485921) ^ 1 = 37 := by norm_num
      have factor_7_1 : (37 : ZMod 3569485921) ^ 2 = 1369 := by
        calc
          (37 : ZMod 3569485921) ^ 2 = (37 : ZMod 3569485921) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1 * (37 : ZMod 3569485921) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_7_0]; decide
      have factor_7_2 : (37 : ZMod 3569485921) ^ 5 = 69343957 := by
        calc
          (37 : ZMod 3569485921) ^ 5 = (37 : ZMod 3569485921) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 2 * (37 : ZMod 3569485921) ^ 2) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 69343957 := by rw [factor_7_1]; decide
      have factor_7_3 : (37 : ZMod 3569485921) ^ 11 = 1336784047 := by
        calc
          (37 : ZMod 3569485921) ^ 11 = (37 : ZMod 3569485921) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 5 * (37 : ZMod 3569485921) ^ 5) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1336784047 := by rw [factor_7_2]; decide
      have factor_7_4 : (37 : ZMod 3569485921) ^ 22 = 1601876891 := by
        calc
          (37 : ZMod 3569485921) ^ 22 = (37 : ZMod 3569485921) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 11 * (37 : ZMod 3569485921) ^ 11 := by rw [pow_add]
          _ = 1601876891 := by rw [factor_7_3]; decide
      have factor_7_5 : (37 : ZMod 3569485921) ^ 44 = 1375732655 := by
        calc
          (37 : ZMod 3569485921) ^ 44 = (37 : ZMod 3569485921) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 22 * (37 : ZMod 3569485921) ^ 22 := by rw [pow_add]
          _ = 1375732655 := by rw [factor_7_4]; decide
      have factor_7_6 : (37 : ZMod 3569485921) ^ 89 = 2906649856 := by
        calc
          (37 : ZMod 3569485921) ^ 89 = (37 : ZMod 3569485921) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 44 * (37 : ZMod 3569485921) ^ 44) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2906649856 := by rw [factor_7_5]; decide
      have factor_7_7 : (37 : ZMod 3569485921) ^ 179 = 3247440682 := by
        calc
          (37 : ZMod 3569485921) ^ 179 = (37 : ZMod 3569485921) ^ (89 + 89 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 89 * (37 : ZMod 3569485921) ^ 89) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 3247440682 := by rw [factor_7_6]; decide
      have factor_7_8 : (37 : ZMod 3569485921) ^ 358 = 2035698199 := by
        calc
          (37 : ZMod 3569485921) ^ 358 = (37 : ZMod 3569485921) ^ (179 + 179) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 179 * (37 : ZMod 3569485921) ^ 179 := by rw [pow_add]
          _ = 2035698199 := by rw [factor_7_7]; decide
      have factor_7_9 : (37 : ZMod 3569485921) ^ 716 = 2584753617 := by
        calc
          (37 : ZMod 3569485921) ^ 716 = (37 : ZMod 3569485921) ^ (358 + 358) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 358 * (37 : ZMod 3569485921) ^ 358 := by rw [pow_add]
          _ = 2584753617 := by rw [factor_7_8]; decide
      have factor_7_10 : (37 : ZMod 3569485921) ^ 1433 = 3081090378 := by
        calc
          (37 : ZMod 3569485921) ^ 1433 = (37 : ZMod 3569485921) ^ (716 + 716 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 716 * (37 : ZMod 3569485921) ^ 716) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 3081090378 := by rw [factor_7_9]; decide
      have factor_7_11 : (37 : ZMod 3569485921) ^ 2866 = 2231708523 := by
        calc
          (37 : ZMod 3569485921) ^ 2866 = (37 : ZMod 3569485921) ^ (1433 + 1433) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1433 * (37 : ZMod 3569485921) ^ 1433 := by rw [pow_add]
          _ = 2231708523 := by rw [factor_7_10]; decide
      have factor_7_12 : (37 : ZMod 3569485921) ^ 5733 = 1353840483 := by
        calc
          (37 : ZMod 3569485921) ^ 5733 = (37 : ZMod 3569485921) ^ (2866 + 2866 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 2866 * (37 : ZMod 3569485921) ^ 2866) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1353840483 := by rw [factor_7_11]; decide
      have factor_7_13 : (37 : ZMod 3569485921) ^ 11466 = 271921807 := by
        calc
          (37 : ZMod 3569485921) ^ 11466 = (37 : ZMod 3569485921) ^ (5733 + 5733) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 5733 * (37 : ZMod 3569485921) ^ 5733 := by rw [pow_add]
          _ = 271921807 := by rw [factor_7_12]; decide
      have factor_7_14 : (37 : ZMod 3569485921) ^ 22933 = 2958301609 := by
        calc
          (37 : ZMod 3569485921) ^ 22933 = (37 : ZMod 3569485921) ^ (11466 + 11466 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 11466 * (37 : ZMod 3569485921) ^ 11466) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2958301609 := by rw [factor_7_13]; decide
      have factor_7_15 : (37 : ZMod 3569485921) ^ 45866 = 649031627 := by
        calc
          (37 : ZMod 3569485921) ^ 45866 = (37 : ZMod 3569485921) ^ (22933 + 22933) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 22933 * (37 : ZMod 3569485921) ^ 22933 := by rw [pow_add]
          _ = 649031627 := by rw [factor_7_14]; decide
      have factor_7_16 : (37 : ZMod 3569485921) ^ 91732 = 1699736443 := by
        calc
          (37 : ZMod 3569485921) ^ 91732 = (37 : ZMod 3569485921) ^ (45866 + 45866) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 45866 * (37 : ZMod 3569485921) ^ 45866 := by rw [pow_add]
          _ = 1699736443 := by rw [factor_7_15]; decide
      have factor_7_17 : (37 : ZMod 3569485921) ^ 183464 = 562288795 := by
        calc
          (37 : ZMod 3569485921) ^ 183464 = (37 : ZMod 3569485921) ^ (91732 + 91732) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 91732 * (37 : ZMod 3569485921) ^ 91732 := by rw [pow_add]
          _ = 562288795 := by rw [factor_7_16]; decide
      have factor_7_18 : (37 : ZMod 3569485921) ^ 366929 = 281192571 := by
        calc
          (37 : ZMod 3569485921) ^ 366929 = (37 : ZMod 3569485921) ^ (183464 + 183464 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 183464 * (37 : ZMod 3569485921) ^ 183464) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 281192571 := by rw [factor_7_17]; decide
      have factor_7_19 : (37 : ZMod 3569485921) ^ 733858 = 1636741959 := by
        calc
          (37 : ZMod 3569485921) ^ 733858 = (37 : ZMod 3569485921) ^ (366929 + 366929) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 366929 * (37 : ZMod 3569485921) ^ 366929 := by rw [pow_add]
          _ = 1636741959 := by rw [factor_7_18]; decide
      have factor_7_20 : (37 : ZMod 3569485921) ^ 1467716 = 2418978182 := by
        calc
          (37 : ZMod 3569485921) ^ 1467716 = (37 : ZMod 3569485921) ^ (733858 + 733858) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 733858 * (37 : ZMod 3569485921) ^ 733858 := by rw [pow_add]
          _ = 2418978182 := by rw [factor_7_19]; decide
      have factor_7_21 : (37 : ZMod 3569485921) ^ 2935432 = 1729574556 := by
        calc
          (37 : ZMod 3569485921) ^ 2935432 = (37 : ZMod 3569485921) ^ (1467716 + 1467716) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1467716 * (37 : ZMod 3569485921) ^ 1467716 := by rw [pow_add]
          _ = 1729574556 := by rw [factor_7_20]; decide
      have factor_7_22 : (37 : ZMod 3569485921) ^ 5870865 = 2908385462 := by
        calc
          (37 : ZMod 3569485921) ^ 5870865 = (37 : ZMod 3569485921) ^ (2935432 + 2935432 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 2935432 * (37 : ZMod 3569485921) ^ 2935432) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2908385462 := by rw [factor_7_21]; decide
      have factor_7_23 : (37 : ZMod 3569485921) ^ 11741730 = 3250768532 := by
        calc
          (37 : ZMod 3569485921) ^ 11741730 = (37 : ZMod 3569485921) ^ (5870865 + 5870865) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 5870865 * (37 : ZMod 3569485921) ^ 5870865 := by rw [pow_add]
          _ = 3250768532 := by rw [factor_7_22]; decide
      have factor_7_24 : (37 : ZMod 3569485921) ^ 23483460 = 1040510905 := by
        calc
          (37 : ZMod 3569485921) ^ 23483460 = (37 : ZMod 3569485921) ^ (11741730 + 11741730) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 11741730 * (37 : ZMod 3569485921) ^ 11741730 := by rw [pow_add]
          _ = 1040510905 := by rw [factor_7_23]; decide
      have factor_7_25 : (37 : ZMod 3569485921) ^ 46966920 = 2047454978 := by
        calc
          (37 : ZMod 3569485921) ^ 46966920 = (37 : ZMod 3569485921) ^ (23483460 + 23483460) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 23483460 * (37 : ZMod 3569485921) ^ 23483460 := by rw [pow_add]
          _ = 2047454978 := by rw [factor_7_24]; decide
      have factor_7_26 : (37 : ZMod 3569485921) ^ 93933840 = 973293060 := by
        calc
          (37 : ZMod 3569485921) ^ 93933840 = (37 : ZMod 3569485921) ^ (46966920 + 46966920) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 46966920 * (37 : ZMod 3569485921) ^ 46966920 := by rw [pow_add]
          _ = 973293060 := by rw [factor_7_25]; decide
      have factor_7_27 : (37 : ZMod 3569485921) ^ 187867680 = 1395377978 := by
        calc
          (37 : ZMod 3569485921) ^ 187867680 = (37 : ZMod 3569485921) ^ (93933840 + 93933840) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 93933840 * (37 : ZMod 3569485921) ^ 93933840 := by rw [pow_add]
          _ = 1395377978 := by rw [factor_7_26]; decide
      change (37 : ZMod 3569485921) ^ 187867680 ≠ 1
      rw [factor_7_27]
      decide
    ·
      have factor_8_0 : (37 : ZMod 3569485921) ^ 1 = 37 := by norm_num
      have factor_8_1 : (37 : ZMod 3569485921) ^ 2 = 1369 := by
        calc
          (37 : ZMod 3569485921) ^ 2 = (37 : ZMod 3569485921) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1 * (37 : ZMod 3569485921) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_8_0]; decide
      have factor_8_2 : (37 : ZMod 3569485921) ^ 4 = 1874161 := by
        calc
          (37 : ZMod 3569485921) ^ 4 = (37 : ZMod 3569485921) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 2 * (37 : ZMod 3569485921) ^ 2 := by rw [pow_add]
          _ = 1874161 := by rw [factor_8_1]; decide
      have factor_8_3 : (37 : ZMod 3569485921) ^ 9 = 326897388 := by
        calc
          (37 : ZMod 3569485921) ^ 9 = (37 : ZMod 3569485921) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 4 * (37 : ZMod 3569485921) ^ 4) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 326897388 := by rw [factor_8_2]; decide
      have factor_8_4 : (37 : ZMod 3569485921) ^ 18 = 3460918208 := by
        calc
          (37 : ZMod 3569485921) ^ 18 = (37 : ZMod 3569485921) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 9 * (37 : ZMod 3569485921) ^ 9 := by rw [pow_add]
          _ = 3460918208 := by rw [factor_8_3]; decide
      have factor_8_5 : (37 : ZMod 3569485921) ^ 37 = 3166411771 := by
        calc
          (37 : ZMod 3569485921) ^ 37 = (37 : ZMod 3569485921) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 18 * (37 : ZMod 3569485921) ^ 18) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 3166411771 := by rw [factor_8_4]; decide
      have factor_8_6 : (37 : ZMod 3569485921) ^ 74 = 2814669527 := by
        calc
          (37 : ZMod 3569485921) ^ 74 = (37 : ZMod 3569485921) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 37 * (37 : ZMod 3569485921) ^ 37 := by rw [pow_add]
          _ = 2814669527 := by rw [factor_8_5]; decide
      have factor_8_7 : (37 : ZMod 3569485921) ^ 148 = 2848671194 := by
        calc
          (37 : ZMod 3569485921) ^ 148 = (37 : ZMod 3569485921) ^ (74 + 74) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 74 * (37 : ZMod 3569485921) ^ 74 := by rw [pow_add]
          _ = 2848671194 := by rw [factor_8_6]; decide
      have factor_8_8 : (37 : ZMod 3569485921) ^ 296 = 3296839390 := by
        calc
          (37 : ZMod 3569485921) ^ 296 = (37 : ZMod 3569485921) ^ (148 + 148) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 148 * (37 : ZMod 3569485921) ^ 148 := by rw [pow_add]
          _ = 3296839390 := by rw [factor_8_7]; decide
      have factor_8_9 : (37 : ZMod 3569485921) ^ 592 = 1709760037 := by
        calc
          (37 : ZMod 3569485921) ^ 592 = (37 : ZMod 3569485921) ^ (296 + 296) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 296 * (37 : ZMod 3569485921) ^ 296 := by rw [pow_add]
          _ = 1709760037 := by rw [factor_8_8]; decide
      have factor_8_10 : (37 : ZMod 3569485921) ^ 1184 = 1440117353 := by
        calc
          (37 : ZMod 3569485921) ^ 1184 = (37 : ZMod 3569485921) ^ (592 + 592) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 592 * (37 : ZMod 3569485921) ^ 592 := by rw [pow_add]
          _ = 1440117353 := by rw [factor_8_9]; decide
      have factor_8_11 : (37 : ZMod 3569485921) ^ 2368 = 3022180092 := by
        calc
          (37 : ZMod 3569485921) ^ 2368 = (37 : ZMod 3569485921) ^ (1184 + 1184) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1184 * (37 : ZMod 3569485921) ^ 1184 := by rw [pow_add]
          _ = 3022180092 := by rw [factor_8_10]; decide
      have factor_8_12 : (37 : ZMod 3569485921) ^ 4736 = 694125287 := by
        calc
          (37 : ZMod 3569485921) ^ 4736 = (37 : ZMod 3569485921) ^ (2368 + 2368) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 2368 * (37 : ZMod 3569485921) ^ 2368 := by rw [pow_add]
          _ = 694125287 := by rw [factor_8_11]; decide
      have factor_8_13 : (37 : ZMod 3569485921) ^ 9472 = 1247525932 := by
        calc
          (37 : ZMod 3569485921) ^ 9472 = (37 : ZMod 3569485921) ^ (4736 + 4736) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 4736 * (37 : ZMod 3569485921) ^ 4736 := by rw [pow_add]
          _ = 1247525932 := by rw [factor_8_12]; decide
      have factor_8_14 : (37 : ZMod 3569485921) ^ 18944 = 3109415836 := by
        calc
          (37 : ZMod 3569485921) ^ 18944 = (37 : ZMod 3569485921) ^ (9472 + 9472) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 9472 * (37 : ZMod 3569485921) ^ 9472 := by rw [pow_add]
          _ = 3109415836 := by rw [factor_8_13]; decide
      have factor_8_15 : (37 : ZMod 3569485921) ^ 37889 = 1551163771 := by
        calc
          (37 : ZMod 3569485921) ^ 37889 = (37 : ZMod 3569485921) ^ (18944 + 18944 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 18944 * (37 : ZMod 3569485921) ^ 18944) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1551163771 := by rw [factor_8_14]; decide
      have factor_8_16 : (37 : ZMod 3569485921) ^ 75778 = 1521212530 := by
        calc
          (37 : ZMod 3569485921) ^ 75778 = (37 : ZMod 3569485921) ^ (37889 + 37889) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 37889 * (37 : ZMod 3569485921) ^ 37889 := by rw [pow_add]
          _ = 1521212530 := by rw [factor_8_15]; decide
      have factor_8_17 : (37 : ZMod 3569485921) ^ 151557 = 497534467 := by
        calc
          (37 : ZMod 3569485921) ^ 151557 = (37 : ZMod 3569485921) ^ (75778 + 75778 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 75778 * (37 : ZMod 3569485921) ^ 75778) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 497534467 := by rw [factor_8_16]; decide
      have factor_8_18 : (37 : ZMod 3569485921) ^ 303115 = 2490082649 := by
        calc
          (37 : ZMod 3569485921) ^ 303115 = (37 : ZMod 3569485921) ^ (151557 + 151557 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 151557 * (37 : ZMod 3569485921) ^ 151557) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2490082649 := by rw [factor_8_17]; decide
      have factor_8_19 : (37 : ZMod 3569485921) ^ 606230 = 266040918 := by
        calc
          (37 : ZMod 3569485921) ^ 606230 = (37 : ZMod 3569485921) ^ (303115 + 303115) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 303115 * (37 : ZMod 3569485921) ^ 303115 := by rw [pow_add]
          _ = 266040918 := by rw [factor_8_18]; decide
      have factor_8_20 : (37 : ZMod 3569485921) ^ 1212461 = 1916041144 := by
        calc
          (37 : ZMod 3569485921) ^ 1212461 = (37 : ZMod 3569485921) ^ (606230 + 606230 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 606230 * (37 : ZMod 3569485921) ^ 606230) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 1916041144 := by rw [factor_8_19]; decide
      have factor_8_21 : (37 : ZMod 3569485921) ^ 2424922 = 1477051066 := by
        calc
          (37 : ZMod 3569485921) ^ 2424922 = (37 : ZMod 3569485921) ^ (1212461 + 1212461) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 1212461 * (37 : ZMod 3569485921) ^ 1212461 := by rw [pow_add]
          _ = 1477051066 := by rw [factor_8_20]; decide
      have factor_8_22 : (37 : ZMod 3569485921) ^ 4849845 = 2370982369 := by
        calc
          (37 : ZMod 3569485921) ^ 4849845 = (37 : ZMod 3569485921) ^ (2424922 + 2424922 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = ((37 : ZMod 3569485921) ^ 2424922 * (37 : ZMod 3569485921) ^ 2424922) * (37 : ZMod 3569485921) := by rw [pow_succ, pow_add]
          _ = 2370982369 := by rw [factor_8_21]; decide
      have factor_8_23 : (37 : ZMod 3569485921) ^ 9699690 = 2983457041 := by
        calc
          (37 : ZMod 3569485921) ^ 9699690 = (37 : ZMod 3569485921) ^ (4849845 + 4849845) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 4849845 * (37 : ZMod 3569485921) ^ 4849845 := by rw [pow_add]
          _ = 2983457041 := by rw [factor_8_22]; decide
      have factor_8_24 : (37 : ZMod 3569485921) ^ 19399380 = 2248030989 := by
        calc
          (37 : ZMod 3569485921) ^ 19399380 = (37 : ZMod 3569485921) ^ (9699690 + 9699690) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 9699690 * (37 : ZMod 3569485921) ^ 9699690 := by rw [pow_add]
          _ = 2248030989 := by rw [factor_8_23]; decide
      have factor_8_25 : (37 : ZMod 3569485921) ^ 38798760 = 2304593002 := by
        calc
          (37 : ZMod 3569485921) ^ 38798760 = (37 : ZMod 3569485921) ^ (19399380 + 19399380) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 19399380 * (37 : ZMod 3569485921) ^ 19399380 := by rw [pow_add]
          _ = 2304593002 := by rw [factor_8_24]; decide
      have factor_8_26 : (37 : ZMod 3569485921) ^ 77597520 = 2598998243 := by
        calc
          (37 : ZMod 3569485921) ^ 77597520 = (37 : ZMod 3569485921) ^ (38798760 + 38798760) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 38798760 * (37 : ZMod 3569485921) ^ 38798760 := by rw [pow_add]
          _ = 2598998243 := by rw [factor_8_25]; decide
      have factor_8_27 : (37 : ZMod 3569485921) ^ 155195040 = 430783026 := by
        calc
          (37 : ZMod 3569485921) ^ 155195040 = (37 : ZMod 3569485921) ^ (77597520 + 77597520) :=
            congrArg (fun n : ℕ => (37 : ZMod 3569485921) ^ n) (by norm_num)
          _ = (37 : ZMod 3569485921) ^ 77597520 * (37 : ZMod 3569485921) ^ 77597520 := by rw [pow_add]
          _ = 430783026 := by rw [factor_8_26]; decide
      change (37 : ZMod 3569485921) ^ 155195040 ≠ 1
      rw [factor_8_27]
      decide

#print axioms prime_lucas_3569485921

end TotientTailPeriodKiller
end Erdos249257
