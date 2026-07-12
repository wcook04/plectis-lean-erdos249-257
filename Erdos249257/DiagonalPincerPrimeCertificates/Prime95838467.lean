import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_95838467 : Nat.Prime 95838467 := by
  apply lucas_primality 95838467 (2 : ZMod 95838467)
  ·
      have fermat_0 : (2 : ZMod 95838467) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 95838467) ^ 2 = 4 := by
        calc
          (2 : ZMod 95838467) ^ 2 = (2 : ZMod 95838467) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 1 * (2 : ZMod 95838467) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 95838467) ^ 5 = 32 := by
        calc
          (2 : ZMod 95838467) ^ 5 = (2 : ZMod 95838467) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 2 * (2 : ZMod 95838467) ^ 2) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 95838467) ^ 11 = 2048 := by
        calc
          (2 : ZMod 95838467) ^ 11 = (2 : ZMod 95838467) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 5 * (2 : ZMod 95838467) ^ 5) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 95838467) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 95838467) ^ 22 = (2 : ZMod 95838467) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 11 * (2 : ZMod 95838467) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 95838467) ^ 45 = 58245325 := by
        calc
          (2 : ZMod 95838467) ^ 45 = (2 : ZMod 95838467) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 22 * (2 : ZMod 95838467) ^ 22) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 58245325 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 95838467) ^ 91 = 72668390 := by
        calc
          (2 : ZMod 95838467) ^ 91 = (2 : ZMod 95838467) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 45 * (2 : ZMod 95838467) ^ 45) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 72668390 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 95838467) ^ 182 = 69576983 := by
        calc
          (2 : ZMod 95838467) ^ 182 = (2 : ZMod 95838467) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 91 * (2 : ZMod 95838467) ^ 91 := by rw [pow_add]
          _ = 69576983 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 95838467) ^ 365 = 2922229 := by
        calc
          (2 : ZMod 95838467) ^ 365 = (2 : ZMod 95838467) ^ (182 + 182 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 182 * (2 : ZMod 95838467) ^ 182) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 2922229 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 95838467) ^ 731 = 46483614 := by
        calc
          (2 : ZMod 95838467) ^ 731 = (2 : ZMod 95838467) ^ (365 + 365 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 365 * (2 : ZMod 95838467) ^ 365) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 46483614 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 95838467) ^ 1462 = 21075562 := by
        calc
          (2 : ZMod 95838467) ^ 1462 = (2 : ZMod 95838467) ^ (731 + 731) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 731 * (2 : ZMod 95838467) ^ 731 := by rw [pow_add]
          _ = 21075562 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 95838467) ^ 2924 = 29118822 := by
        calc
          (2 : ZMod 95838467) ^ 2924 = (2 : ZMod 95838467) ^ (1462 + 1462) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 1462 * (2 : ZMod 95838467) ^ 1462 := by rw [pow_add]
          _ = 29118822 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 95838467) ^ 5849 = 39288609 := by
        calc
          (2 : ZMod 95838467) ^ 5849 = (2 : ZMod 95838467) ^ (2924 + 2924 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 2924 * (2 : ZMod 95838467) ^ 2924) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 39288609 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 95838467) ^ 11699 = 68118820 := by
        calc
          (2 : ZMod 95838467) ^ 11699 = (2 : ZMod 95838467) ^ (5849 + 5849 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 5849 * (2 : ZMod 95838467) ^ 5849) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 68118820 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 95838467) ^ 23398 = 54293997 := by
        calc
          (2 : ZMod 95838467) ^ 23398 = (2 : ZMod 95838467) ^ (11699 + 11699) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 11699 * (2 : ZMod 95838467) ^ 11699 := by rw [pow_add]
          _ = 54293997 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 95838467) ^ 46796 = 15186275 := by
        calc
          (2 : ZMod 95838467) ^ 46796 = (2 : ZMod 95838467) ^ (23398 + 23398) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 23398 * (2 : ZMod 95838467) ^ 23398 := by rw [pow_add]
          _ = 15186275 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 95838467) ^ 93592 = 40702368 := by
        calc
          (2 : ZMod 95838467) ^ 93592 = (2 : ZMod 95838467) ^ (46796 + 46796) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 46796 * (2 : ZMod 95838467) ^ 46796 := by rw [pow_add]
          _ = 40702368 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 95838467) ^ 187184 = 44228958 := by
        calc
          (2 : ZMod 95838467) ^ 187184 = (2 : ZMod 95838467) ^ (93592 + 93592) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 93592 * (2 : ZMod 95838467) ^ 93592 := by rw [pow_add]
          _ = 44228958 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 95838467) ^ 374369 = 76352771 := by
        calc
          (2 : ZMod 95838467) ^ 374369 = (2 : ZMod 95838467) ^ (187184 + 187184 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 187184 * (2 : ZMod 95838467) ^ 187184) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 76352771 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 95838467) ^ 748738 = 85074618 := by
        calc
          (2 : ZMod 95838467) ^ 748738 = (2 : ZMod 95838467) ^ (374369 + 374369) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 374369 * (2 : ZMod 95838467) ^ 374369 := by rw [pow_add]
          _ = 85074618 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 95838467) ^ 1497476 = 76638430 := by
        calc
          (2 : ZMod 95838467) ^ 1497476 = (2 : ZMod 95838467) ^ (748738 + 748738) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 748738 * (2 : ZMod 95838467) ^ 748738 := by rw [pow_add]
          _ = 76638430 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 95838467) ^ 2994952 = 3385940 := by
        calc
          (2 : ZMod 95838467) ^ 2994952 = (2 : ZMod 95838467) ^ (1497476 + 1497476) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 1497476 * (2 : ZMod 95838467) ^ 1497476 := by rw [pow_add]
          _ = 3385940 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 95838467) ^ 5989904 = 8907192 := by
        calc
          (2 : ZMod 95838467) ^ 5989904 = (2 : ZMod 95838467) ^ (2994952 + 2994952) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 2994952 * (2 : ZMod 95838467) ^ 2994952 := by rw [pow_add]
          _ = 8907192 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 95838467) ^ 11979808 = 15349787 := by
        calc
          (2 : ZMod 95838467) ^ 11979808 = (2 : ZMod 95838467) ^ (5989904 + 5989904) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 5989904 * (2 : ZMod 95838467) ^ 5989904 := by rw [pow_add]
          _ = 15349787 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 95838467) ^ 23959616 = 60818346 := by
        calc
          (2 : ZMod 95838467) ^ 23959616 = (2 : ZMod 95838467) ^ (11979808 + 11979808) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 11979808 * (2 : ZMod 95838467) ^ 11979808 := by rw [pow_add]
          _ = 60818346 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 95838467) ^ 47919233 = 95838466 := by
        calc
          (2 : ZMod 95838467) ^ 47919233 = (2 : ZMod 95838467) ^ (23959616 + 23959616 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 23959616 * (2 : ZMod 95838467) ^ 23959616) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 95838466 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 95838467) ^ 95838466 = 1 := by
        calc
          (2 : ZMod 95838467) ^ 95838466 = (2 : ZMod 95838467) ^ (47919233 + 47919233) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 47919233 * (2 : ZMod 95838467) ^ 47919233 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (4013, 1), (11941, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (4013, 1), (11941, 1)] : List FactorBlock).map factorBlockValue).prod = 95838467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 95838467) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 95838467) ^ 2 = 4 := by
        calc
          (2 : ZMod 95838467) ^ 2 = (2 : ZMod 95838467) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 1 * (2 : ZMod 95838467) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 95838467) ^ 5 = 32 := by
        calc
          (2 : ZMod 95838467) ^ 5 = (2 : ZMod 95838467) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 2 * (2 : ZMod 95838467) ^ 2) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 95838467) ^ 11 = 2048 := by
        calc
          (2 : ZMod 95838467) ^ 11 = (2 : ZMod 95838467) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 5 * (2 : ZMod 95838467) ^ 5) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 95838467) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 95838467) ^ 22 = (2 : ZMod 95838467) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 11 * (2 : ZMod 95838467) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 95838467) ^ 45 = 58245325 := by
        calc
          (2 : ZMod 95838467) ^ 45 = (2 : ZMod 95838467) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 22 * (2 : ZMod 95838467) ^ 22) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 58245325 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 95838467) ^ 91 = 72668390 := by
        calc
          (2 : ZMod 95838467) ^ 91 = (2 : ZMod 95838467) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 45 * (2 : ZMod 95838467) ^ 45) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 72668390 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 95838467) ^ 182 = 69576983 := by
        calc
          (2 : ZMod 95838467) ^ 182 = (2 : ZMod 95838467) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 91 * (2 : ZMod 95838467) ^ 91 := by rw [pow_add]
          _ = 69576983 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 95838467) ^ 365 = 2922229 := by
        calc
          (2 : ZMod 95838467) ^ 365 = (2 : ZMod 95838467) ^ (182 + 182 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 182 * (2 : ZMod 95838467) ^ 182) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 2922229 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 95838467) ^ 731 = 46483614 := by
        calc
          (2 : ZMod 95838467) ^ 731 = (2 : ZMod 95838467) ^ (365 + 365 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 365 * (2 : ZMod 95838467) ^ 365) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 46483614 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 95838467) ^ 1462 = 21075562 := by
        calc
          (2 : ZMod 95838467) ^ 1462 = (2 : ZMod 95838467) ^ (731 + 731) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 731 * (2 : ZMod 95838467) ^ 731 := by rw [pow_add]
          _ = 21075562 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 95838467) ^ 2924 = 29118822 := by
        calc
          (2 : ZMod 95838467) ^ 2924 = (2 : ZMod 95838467) ^ (1462 + 1462) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 1462 * (2 : ZMod 95838467) ^ 1462 := by rw [pow_add]
          _ = 29118822 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 95838467) ^ 5849 = 39288609 := by
        calc
          (2 : ZMod 95838467) ^ 5849 = (2 : ZMod 95838467) ^ (2924 + 2924 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 2924 * (2 : ZMod 95838467) ^ 2924) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 39288609 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 95838467) ^ 11699 = 68118820 := by
        calc
          (2 : ZMod 95838467) ^ 11699 = (2 : ZMod 95838467) ^ (5849 + 5849 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 5849 * (2 : ZMod 95838467) ^ 5849) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 68118820 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 95838467) ^ 23398 = 54293997 := by
        calc
          (2 : ZMod 95838467) ^ 23398 = (2 : ZMod 95838467) ^ (11699 + 11699) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 11699 * (2 : ZMod 95838467) ^ 11699 := by rw [pow_add]
          _ = 54293997 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 95838467) ^ 46796 = 15186275 := by
        calc
          (2 : ZMod 95838467) ^ 46796 = (2 : ZMod 95838467) ^ (23398 + 23398) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 23398 * (2 : ZMod 95838467) ^ 23398 := by rw [pow_add]
          _ = 15186275 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 95838467) ^ 93592 = 40702368 := by
        calc
          (2 : ZMod 95838467) ^ 93592 = (2 : ZMod 95838467) ^ (46796 + 46796) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 46796 * (2 : ZMod 95838467) ^ 46796 := by rw [pow_add]
          _ = 40702368 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 95838467) ^ 187184 = 44228958 := by
        calc
          (2 : ZMod 95838467) ^ 187184 = (2 : ZMod 95838467) ^ (93592 + 93592) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 93592 * (2 : ZMod 95838467) ^ 93592 := by rw [pow_add]
          _ = 44228958 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 95838467) ^ 374369 = 76352771 := by
        calc
          (2 : ZMod 95838467) ^ 374369 = (2 : ZMod 95838467) ^ (187184 + 187184 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 187184 * (2 : ZMod 95838467) ^ 187184) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 76352771 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 95838467) ^ 748738 = 85074618 := by
        calc
          (2 : ZMod 95838467) ^ 748738 = (2 : ZMod 95838467) ^ (374369 + 374369) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 374369 * (2 : ZMod 95838467) ^ 374369 := by rw [pow_add]
          _ = 85074618 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 95838467) ^ 1497476 = 76638430 := by
        calc
          (2 : ZMod 95838467) ^ 1497476 = (2 : ZMod 95838467) ^ (748738 + 748738) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 748738 * (2 : ZMod 95838467) ^ 748738 := by rw [pow_add]
          _ = 76638430 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 95838467) ^ 2994952 = 3385940 := by
        calc
          (2 : ZMod 95838467) ^ 2994952 = (2 : ZMod 95838467) ^ (1497476 + 1497476) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 1497476 * (2 : ZMod 95838467) ^ 1497476 := by rw [pow_add]
          _ = 3385940 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 95838467) ^ 5989904 = 8907192 := by
        calc
          (2 : ZMod 95838467) ^ 5989904 = (2 : ZMod 95838467) ^ (2994952 + 2994952) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 2994952 * (2 : ZMod 95838467) ^ 2994952 := by rw [pow_add]
          _ = 8907192 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 95838467) ^ 11979808 = 15349787 := by
        calc
          (2 : ZMod 95838467) ^ 11979808 = (2 : ZMod 95838467) ^ (5989904 + 5989904) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 5989904 * (2 : ZMod 95838467) ^ 5989904 := by rw [pow_add]
          _ = 15349787 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 95838467) ^ 23959616 = 60818346 := by
        calc
          (2 : ZMod 95838467) ^ 23959616 = (2 : ZMod 95838467) ^ (11979808 + 11979808) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 11979808 * (2 : ZMod 95838467) ^ 11979808 := by rw [pow_add]
          _ = 60818346 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 95838467) ^ 47919233 = 95838466 := by
        calc
          (2 : ZMod 95838467) ^ 47919233 = (2 : ZMod 95838467) ^ (23959616 + 23959616 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 23959616 * (2 : ZMod 95838467) ^ 23959616) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 95838466 := by rw [factor_0_24]; decide
      change (2 : ZMod 95838467) ^ 47919233 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (2 : ZMod 95838467) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 95838467) ^ 2 = 4 := by
        calc
          (2 : ZMod 95838467) ^ 2 = (2 : ZMod 95838467) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 1 * (2 : ZMod 95838467) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 95838467) ^ 5 = 32 := by
        calc
          (2 : ZMod 95838467) ^ 5 = (2 : ZMod 95838467) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 2 * (2 : ZMod 95838467) ^ 2) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 95838467) ^ 11 = 2048 := by
        calc
          (2 : ZMod 95838467) ^ 11 = (2 : ZMod 95838467) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 5 * (2 : ZMod 95838467) ^ 5) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 95838467) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 95838467) ^ 23 = (2 : ZMod 95838467) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 11 * (2 : ZMod 95838467) ^ 11) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 95838467) ^ 46 = 20652183 := by
        calc
          (2 : ZMod 95838467) ^ 46 = (2 : ZMod 95838467) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 23 * (2 : ZMod 95838467) ^ 23 := by rw [pow_add]
          _ = 20652183 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 95838467) ^ 93 = 3158159 := by
        calc
          (2 : ZMod 95838467) ^ 93 = (2 : ZMod 95838467) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 46 * (2 : ZMod 95838467) ^ 46) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 3158159 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 95838467) ^ 186 = 59008591 := by
        calc
          (2 : ZMod 95838467) ^ 186 = (2 : ZMod 95838467) ^ (93 + 93) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 93 * (2 : ZMod 95838467) ^ 93 := by rw [pow_add]
          _ = 59008591 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 95838467) ^ 373 = 77221355 := by
        calc
          (2 : ZMod 95838467) ^ 373 = (2 : ZMod 95838467) ^ (186 + 186 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 186 * (2 : ZMod 95838467) ^ 186) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 77221355 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 95838467) ^ 746 = 14307521 := by
        calc
          (2 : ZMod 95838467) ^ 746 = (2 : ZMod 95838467) ^ (373 + 373) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 373 * (2 : ZMod 95838467) ^ 373 := by rw [pow_add]
          _ = 14307521 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 95838467) ^ 1492 = 37799928 := by
        calc
          (2 : ZMod 95838467) ^ 1492 = (2 : ZMod 95838467) ^ (746 + 746) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 746 * (2 : ZMod 95838467) ^ 746 := by rw [pow_add]
          _ = 37799928 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 95838467) ^ 2985 = 65206782 := by
        calc
          (2 : ZMod 95838467) ^ 2985 = (2 : ZMod 95838467) ^ (1492 + 1492 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 1492 * (2 : ZMod 95838467) ^ 1492) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 65206782 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 95838467) ^ 5970 = 35953014 := by
        calc
          (2 : ZMod 95838467) ^ 5970 = (2 : ZMod 95838467) ^ (2985 + 2985) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 2985 * (2 : ZMod 95838467) ^ 2985 := by rw [pow_add]
          _ = 35953014 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 95838467) ^ 11941 = 935940 := by
        calc
          (2 : ZMod 95838467) ^ 11941 = (2 : ZMod 95838467) ^ (5970 + 5970 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 5970 * (2 : ZMod 95838467) ^ 5970) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 935940 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 95838467) ^ 23882 = 20095220 := by
        calc
          (2 : ZMod 95838467) ^ 23882 = (2 : ZMod 95838467) ^ (11941 + 11941) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 11941 * (2 : ZMod 95838467) ^ 11941 := by rw [pow_add]
          _ = 20095220 := by rw [factor_1_13]; decide
      change (2 : ZMod 95838467) ^ 23882 ≠ 1
      rw [factor_1_14]
      decide
    ·
      have factor_2_0 : (2 : ZMod 95838467) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 95838467) ^ 3 = 8 := by
        calc
          (2 : ZMod 95838467) ^ 3 = (2 : ZMod 95838467) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 1 * (2 : ZMod 95838467) ^ 1) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 95838467) ^ 7 = 128 := by
        calc
          (2 : ZMod 95838467) ^ 7 = (2 : ZMod 95838467) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 3 * (2 : ZMod 95838467) ^ 3) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 95838467) ^ 15 = 32768 := by
        calc
          (2 : ZMod 95838467) ^ 15 = (2 : ZMod 95838467) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 7 * (2 : ZMod 95838467) ^ 7) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 95838467) ^ 31 = 39037374 := by
        calc
          (2 : ZMod 95838467) ^ 31 = (2 : ZMod 95838467) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 15 * (2 : ZMod 95838467) ^ 15) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 39037374 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 95838467) ^ 62 = 30634114 := by
        calc
          (2 : ZMod 95838467) ^ 62 = (2 : ZMod 95838467) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 31 * (2 : ZMod 95838467) ^ 31 := by rw [pow_add]
          _ = 30634114 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 95838467) ^ 125 = 26879068 := by
        calc
          (2 : ZMod 95838467) ^ 125 = (2 : ZMod 95838467) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 62 * (2 : ZMod 95838467) ^ 62) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 26879068 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 95838467) ^ 250 = 71084170 := by
        calc
          (2 : ZMod 95838467) ^ 250 = (2 : ZMod 95838467) ^ (125 + 125) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 125 * (2 : ZMod 95838467) ^ 125 := by rw [pow_add]
          _ = 71084170 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 95838467) ^ 501 = 38141929 := by
        calc
          (2 : ZMod 95838467) ^ 501 = (2 : ZMod 95838467) ^ (250 + 250 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 250 * (2 : ZMod 95838467) ^ 250) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 38141929 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 95838467) ^ 1003 = 94002963 := by
        calc
          (2 : ZMod 95838467) ^ 1003 = (2 : ZMod 95838467) ^ (501 + 501 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 501 * (2 : ZMod 95838467) ^ 501) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 94002963 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 95838467) ^ 2006 = 65303565 := by
        calc
          (2 : ZMod 95838467) ^ 2006 = (2 : ZMod 95838467) ^ (1003 + 1003) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 1003 * (2 : ZMod 95838467) ^ 1003 := by rw [pow_add]
          _ = 65303565 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 95838467) ^ 4013 = 88701499 := by
        calc
          (2 : ZMod 95838467) ^ 4013 = (2 : ZMod 95838467) ^ (2006 + 2006 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = ((2 : ZMod 95838467) ^ 2006 * (2 : ZMod 95838467) ^ 2006) * (2 : ZMod 95838467) := by rw [pow_succ, pow_add]
          _ = 88701499 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 95838467) ^ 8026 = 83791864 := by
        calc
          (2 : ZMod 95838467) ^ 8026 = (2 : ZMod 95838467) ^ (4013 + 4013) :=
            congrArg (fun n : ℕ => (2 : ZMod 95838467) ^ n) (by norm_num)
          _ = (2 : ZMod 95838467) ^ 4013 * (2 : ZMod 95838467) ^ 4013 := by rw [pow_add]
          _ = 83791864 := by rw [factor_2_11]; decide
      change (2 : ZMod 95838467) ^ 8026 ≠ 1
      rw [factor_2_12]
      decide

#print axioms prime_lucas_95838467

end TotientTailPeriodKiller
end Erdos249257
