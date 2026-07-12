import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1567050703 : Nat.Prime 1567050703 := by
  apply lucas_primality 1567050703 (3 : ZMod 1567050703)
  ·
      have fermat_0 : (3 : ZMod 1567050703) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 1567050703) ^ 2 = 9 := by
        calc
          (3 : ZMod 1567050703) ^ 2 = (3 : ZMod 1567050703) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 1 * (3 : ZMod 1567050703) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 1567050703) ^ 5 = 243 := by
        calc
          (3 : ZMod 1567050703) ^ 5 = (3 : ZMod 1567050703) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 2 * (3 : ZMod 1567050703) ^ 2) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 1567050703) ^ 11 = 177147 := by
        calc
          (3 : ZMod 1567050703) ^ 11 = (3 : ZMod 1567050703) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 5 * (3 : ZMod 1567050703) ^ 5) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 1567050703) ^ 23 = 120136647 := by
        calc
          (3 : ZMod 1567050703) ^ 23 = (3 : ZMod 1567050703) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 11 * (3 : ZMod 1567050703) ^ 11) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 120136647 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 1567050703) ^ 46 = 1176848881 := by
        calc
          (3 : ZMod 1567050703) ^ 46 = (3 : ZMod 1567050703) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 23 * (3 : ZMod 1567050703) ^ 23 := by rw [pow_add]
          _ = 1176848881 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 1567050703) ^ 93 = 362629882 := by
        calc
          (3 : ZMod 1567050703) ^ 93 = (3 : ZMod 1567050703) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 46 * (3 : ZMod 1567050703) ^ 46) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 362629882 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 1567050703) ^ 186 = 407723799 := by
        calc
          (3 : ZMod 1567050703) ^ 186 = (3 : ZMod 1567050703) ^ (93 + 93) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 93 * (3 : ZMod 1567050703) ^ 93 := by rw [pow_add]
          _ = 407723799 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 1567050703) ^ 373 = 876989488 := by
        calc
          (3 : ZMod 1567050703) ^ 373 = (3 : ZMod 1567050703) ^ (186 + 186 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 186 * (3 : ZMod 1567050703) ^ 186) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 876989488 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 1567050703) ^ 747 = 496711304 := by
        calc
          (3 : ZMod 1567050703) ^ 747 = (3 : ZMod 1567050703) ^ (373 + 373 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 373 * (3 : ZMod 1567050703) ^ 373) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 496711304 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 1567050703) ^ 1494 = 1355073289 := by
        calc
          (3 : ZMod 1567050703) ^ 1494 = (3 : ZMod 1567050703) ^ (747 + 747) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 747 * (3 : ZMod 1567050703) ^ 747 := by rw [pow_add]
          _ = 1355073289 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 1567050703) ^ 2988 = 456041242 := by
        calc
          (3 : ZMod 1567050703) ^ 2988 = (3 : ZMod 1567050703) ^ (1494 + 1494) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 1494 * (3 : ZMod 1567050703) ^ 1494 := by rw [pow_add]
          _ = 456041242 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 1567050703) ^ 5977 = 712034848 := by
        calc
          (3 : ZMod 1567050703) ^ 5977 = (3 : ZMod 1567050703) ^ (2988 + 2988 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 2988 * (3 : ZMod 1567050703) ^ 2988) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 712034848 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 1567050703) ^ 11955 = 1476094116 := by
        calc
          (3 : ZMod 1567050703) ^ 11955 = (3 : ZMod 1567050703) ^ (5977 + 5977 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 5977 * (3 : ZMod 1567050703) ^ 5977) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1476094116 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 1567050703) ^ 23911 = 535543532 := by
        calc
          (3 : ZMod 1567050703) ^ 23911 = (3 : ZMod 1567050703) ^ (11955 + 11955 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 11955 * (3 : ZMod 1567050703) ^ 11955) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 535543532 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 1567050703) ^ 47822 = 682967865 := by
        calc
          (3 : ZMod 1567050703) ^ 47822 = (3 : ZMod 1567050703) ^ (23911 + 23911) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 23911 * (3 : ZMod 1567050703) ^ 23911 := by rw [pow_add]
          _ = 682967865 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 1567050703) ^ 95645 = 361401798 := by
        calc
          (3 : ZMod 1567050703) ^ 95645 = (3 : ZMod 1567050703) ^ (47822 + 47822 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 47822 * (3 : ZMod 1567050703) ^ 47822) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 361401798 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 1567050703) ^ 191290 = 1461817533 := by
        calc
          (3 : ZMod 1567050703) ^ 191290 = (3 : ZMod 1567050703) ^ (95645 + 95645) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 95645 * (3 : ZMod 1567050703) ^ 95645 := by rw [pow_add]
          _ = 1461817533 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 1567050703) ^ 382580 = 263744827 := by
        calc
          (3 : ZMod 1567050703) ^ 382580 = (3 : ZMod 1567050703) ^ (191290 + 191290) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 191290 * (3 : ZMod 1567050703) ^ 191290 := by rw [pow_add]
          _ = 263744827 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 1567050703) ^ 765161 = 223833057 := by
        calc
          (3 : ZMod 1567050703) ^ 765161 = (3 : ZMod 1567050703) ^ (382580 + 382580 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 382580 * (3 : ZMod 1567050703) ^ 382580) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 223833057 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 1567050703) ^ 1530322 = 54077021 := by
        calc
          (3 : ZMod 1567050703) ^ 1530322 = (3 : ZMod 1567050703) ^ (765161 + 765161) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 765161 * (3 : ZMod 1567050703) ^ 765161 := by rw [pow_add]
          _ = 54077021 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 1567050703) ^ 3060645 = 646180232 := by
        calc
          (3 : ZMod 1567050703) ^ 3060645 = (3 : ZMod 1567050703) ^ (1530322 + 1530322 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 1530322 * (3 : ZMod 1567050703) ^ 1530322) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 646180232 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 1567050703) ^ 6121291 = 520592192 := by
        calc
          (3 : ZMod 1567050703) ^ 6121291 = (3 : ZMod 1567050703) ^ (3060645 + 3060645 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 3060645 * (3 : ZMod 1567050703) ^ 3060645) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 520592192 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 1567050703) ^ 12242583 = 944228194 := by
        calc
          (3 : ZMod 1567050703) ^ 12242583 = (3 : ZMod 1567050703) ^ (6121291 + 6121291 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 6121291 * (3 : ZMod 1567050703) ^ 6121291) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 944228194 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 1567050703) ^ 24485167 = 1315108403 := by
        calc
          (3 : ZMod 1567050703) ^ 24485167 = (3 : ZMod 1567050703) ^ (12242583 + 12242583 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 12242583 * (3 : ZMod 1567050703) ^ 12242583) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1315108403 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 1567050703) ^ 48970334 = 1228687466 := by
        calc
          (3 : ZMod 1567050703) ^ 48970334 = (3 : ZMod 1567050703) ^ (24485167 + 24485167) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 24485167 * (3 : ZMod 1567050703) ^ 24485167 := by rw [pow_add]
          _ = 1228687466 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 1567050703) ^ 97940668 = 1458060042 := by
        calc
          (3 : ZMod 1567050703) ^ 97940668 = (3 : ZMod 1567050703) ^ (48970334 + 48970334) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 48970334 * (3 : ZMod 1567050703) ^ 48970334 := by rw [pow_add]
          _ = 1458060042 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 1567050703) ^ 195881337 = 173562029 := by
        calc
          (3 : ZMod 1567050703) ^ 195881337 = (3 : ZMod 1567050703) ^ (97940668 + 97940668 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 97940668 * (3 : ZMod 1567050703) ^ 97940668) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 173562029 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 1567050703) ^ 391762675 = 774346344 := by
        calc
          (3 : ZMod 1567050703) ^ 391762675 = (3 : ZMod 1567050703) ^ (195881337 + 195881337 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 195881337 * (3 : ZMod 1567050703) ^ 195881337) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 774346344 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 1567050703) ^ 783525351 = 1567050702 := by
        calc
          (3 : ZMod 1567050703) ^ 783525351 = (3 : ZMod 1567050703) ^ (391762675 + 391762675 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 391762675 * (3 : ZMod 1567050703) ^ 391762675) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1567050702 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 1567050703) ^ 1567050702 = 1 := by
        calc
          (3 : ZMod 1567050703) ^ 1567050702 = (3 : ZMod 1567050703) ^ (783525351 + 783525351) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 783525351 * (3 : ZMod 1567050703) ^ 783525351 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (997, 1), (37423, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (997, 1), (37423, 1)] : List FactorBlock).map factorBlockValue).prod = 1567050703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 1567050703) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 1567050703) ^ 2 = 9 := by
        calc
          (3 : ZMod 1567050703) ^ 2 = (3 : ZMod 1567050703) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 1 * (3 : ZMod 1567050703) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 1567050703) ^ 5 = 243 := by
        calc
          (3 : ZMod 1567050703) ^ 5 = (3 : ZMod 1567050703) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 2 * (3 : ZMod 1567050703) ^ 2) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 1567050703) ^ 11 = 177147 := by
        calc
          (3 : ZMod 1567050703) ^ 11 = (3 : ZMod 1567050703) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 5 * (3 : ZMod 1567050703) ^ 5) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 1567050703) ^ 23 = 120136647 := by
        calc
          (3 : ZMod 1567050703) ^ 23 = (3 : ZMod 1567050703) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 11 * (3 : ZMod 1567050703) ^ 11) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 120136647 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 1567050703) ^ 46 = 1176848881 := by
        calc
          (3 : ZMod 1567050703) ^ 46 = (3 : ZMod 1567050703) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 23 * (3 : ZMod 1567050703) ^ 23 := by rw [pow_add]
          _ = 1176848881 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 1567050703) ^ 93 = 362629882 := by
        calc
          (3 : ZMod 1567050703) ^ 93 = (3 : ZMod 1567050703) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 46 * (3 : ZMod 1567050703) ^ 46) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 362629882 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 1567050703) ^ 186 = 407723799 := by
        calc
          (3 : ZMod 1567050703) ^ 186 = (3 : ZMod 1567050703) ^ (93 + 93) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 93 * (3 : ZMod 1567050703) ^ 93 := by rw [pow_add]
          _ = 407723799 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 1567050703) ^ 373 = 876989488 := by
        calc
          (3 : ZMod 1567050703) ^ 373 = (3 : ZMod 1567050703) ^ (186 + 186 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 186 * (3 : ZMod 1567050703) ^ 186) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 876989488 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 1567050703) ^ 747 = 496711304 := by
        calc
          (3 : ZMod 1567050703) ^ 747 = (3 : ZMod 1567050703) ^ (373 + 373 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 373 * (3 : ZMod 1567050703) ^ 373) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 496711304 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 1567050703) ^ 1494 = 1355073289 := by
        calc
          (3 : ZMod 1567050703) ^ 1494 = (3 : ZMod 1567050703) ^ (747 + 747) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 747 * (3 : ZMod 1567050703) ^ 747 := by rw [pow_add]
          _ = 1355073289 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 1567050703) ^ 2988 = 456041242 := by
        calc
          (3 : ZMod 1567050703) ^ 2988 = (3 : ZMod 1567050703) ^ (1494 + 1494) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 1494 * (3 : ZMod 1567050703) ^ 1494 := by rw [pow_add]
          _ = 456041242 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 1567050703) ^ 5977 = 712034848 := by
        calc
          (3 : ZMod 1567050703) ^ 5977 = (3 : ZMod 1567050703) ^ (2988 + 2988 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 2988 * (3 : ZMod 1567050703) ^ 2988) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 712034848 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 1567050703) ^ 11955 = 1476094116 := by
        calc
          (3 : ZMod 1567050703) ^ 11955 = (3 : ZMod 1567050703) ^ (5977 + 5977 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 5977 * (3 : ZMod 1567050703) ^ 5977) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1476094116 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 1567050703) ^ 23911 = 535543532 := by
        calc
          (3 : ZMod 1567050703) ^ 23911 = (3 : ZMod 1567050703) ^ (11955 + 11955 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 11955 * (3 : ZMod 1567050703) ^ 11955) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 535543532 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 1567050703) ^ 47822 = 682967865 := by
        calc
          (3 : ZMod 1567050703) ^ 47822 = (3 : ZMod 1567050703) ^ (23911 + 23911) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 23911 * (3 : ZMod 1567050703) ^ 23911 := by rw [pow_add]
          _ = 682967865 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 1567050703) ^ 95645 = 361401798 := by
        calc
          (3 : ZMod 1567050703) ^ 95645 = (3 : ZMod 1567050703) ^ (47822 + 47822 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 47822 * (3 : ZMod 1567050703) ^ 47822) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 361401798 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 1567050703) ^ 191290 = 1461817533 := by
        calc
          (3 : ZMod 1567050703) ^ 191290 = (3 : ZMod 1567050703) ^ (95645 + 95645) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 95645 * (3 : ZMod 1567050703) ^ 95645 := by rw [pow_add]
          _ = 1461817533 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 1567050703) ^ 382580 = 263744827 := by
        calc
          (3 : ZMod 1567050703) ^ 382580 = (3 : ZMod 1567050703) ^ (191290 + 191290) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 191290 * (3 : ZMod 1567050703) ^ 191290 := by rw [pow_add]
          _ = 263744827 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 1567050703) ^ 765161 = 223833057 := by
        calc
          (3 : ZMod 1567050703) ^ 765161 = (3 : ZMod 1567050703) ^ (382580 + 382580 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 382580 * (3 : ZMod 1567050703) ^ 382580) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 223833057 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 1567050703) ^ 1530322 = 54077021 := by
        calc
          (3 : ZMod 1567050703) ^ 1530322 = (3 : ZMod 1567050703) ^ (765161 + 765161) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 765161 * (3 : ZMod 1567050703) ^ 765161 := by rw [pow_add]
          _ = 54077021 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 1567050703) ^ 3060645 = 646180232 := by
        calc
          (3 : ZMod 1567050703) ^ 3060645 = (3 : ZMod 1567050703) ^ (1530322 + 1530322 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 1530322 * (3 : ZMod 1567050703) ^ 1530322) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 646180232 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 1567050703) ^ 6121291 = 520592192 := by
        calc
          (3 : ZMod 1567050703) ^ 6121291 = (3 : ZMod 1567050703) ^ (3060645 + 3060645 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 3060645 * (3 : ZMod 1567050703) ^ 3060645) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 520592192 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 1567050703) ^ 12242583 = 944228194 := by
        calc
          (3 : ZMod 1567050703) ^ 12242583 = (3 : ZMod 1567050703) ^ (6121291 + 6121291 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 6121291 * (3 : ZMod 1567050703) ^ 6121291) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 944228194 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 1567050703) ^ 24485167 = 1315108403 := by
        calc
          (3 : ZMod 1567050703) ^ 24485167 = (3 : ZMod 1567050703) ^ (12242583 + 12242583 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 12242583 * (3 : ZMod 1567050703) ^ 12242583) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1315108403 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 1567050703) ^ 48970334 = 1228687466 := by
        calc
          (3 : ZMod 1567050703) ^ 48970334 = (3 : ZMod 1567050703) ^ (24485167 + 24485167) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 24485167 * (3 : ZMod 1567050703) ^ 24485167 := by rw [pow_add]
          _ = 1228687466 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 1567050703) ^ 97940668 = 1458060042 := by
        calc
          (3 : ZMod 1567050703) ^ 97940668 = (3 : ZMod 1567050703) ^ (48970334 + 48970334) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 48970334 * (3 : ZMod 1567050703) ^ 48970334 := by rw [pow_add]
          _ = 1458060042 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 1567050703) ^ 195881337 = 173562029 := by
        calc
          (3 : ZMod 1567050703) ^ 195881337 = (3 : ZMod 1567050703) ^ (97940668 + 97940668 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 97940668 * (3 : ZMod 1567050703) ^ 97940668) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 173562029 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 1567050703) ^ 391762675 = 774346344 := by
        calc
          (3 : ZMod 1567050703) ^ 391762675 = (3 : ZMod 1567050703) ^ (195881337 + 195881337 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 195881337 * (3 : ZMod 1567050703) ^ 195881337) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 774346344 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 1567050703) ^ 783525351 = 1567050702 := by
        calc
          (3 : ZMod 1567050703) ^ 783525351 = (3 : ZMod 1567050703) ^ (391762675 + 391762675 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 391762675 * (3 : ZMod 1567050703) ^ 391762675) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1567050702 := by rw [factor_0_28]; decide
      change (3 : ZMod 1567050703) ^ 783525351 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (3 : ZMod 1567050703) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 1567050703) ^ 3 = 27 := by
        calc
          (3 : ZMod 1567050703) ^ 3 = (3 : ZMod 1567050703) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 1 * (3 : ZMod 1567050703) ^ 1) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 1567050703) ^ 7 = 2187 := by
        calc
          (3 : ZMod 1567050703) ^ 7 = (3 : ZMod 1567050703) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 3 * (3 : ZMod 1567050703) ^ 3) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 1567050703) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 1567050703) ^ 15 = (3 : ZMod 1567050703) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 7 * (3 : ZMod 1567050703) ^ 7) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 1567050703) ^ 31 = 1557088061 := by
        calc
          (3 : ZMod 1567050703) ^ 31 = (3 : ZMod 1567050703) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 15 * (3 : ZMod 1567050703) ^ 15) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1557088061 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 1567050703) ^ 62 = 378193550 := by
        calc
          (3 : ZMod 1567050703) ^ 62 = (3 : ZMod 1567050703) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 31 * (3 : ZMod 1567050703) ^ 31 := by rw [pow_add]
          _ = 378193550 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 1567050703) ^ 124 = 649210997 := by
        calc
          (3 : ZMod 1567050703) ^ 124 = (3 : ZMod 1567050703) ^ (62 + 62) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 62 * (3 : ZMod 1567050703) ^ 62 := by rw [pow_add]
          _ = 649210997 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 1567050703) ^ 249 = 1267268507 := by
        calc
          (3 : ZMod 1567050703) ^ 249 = (3 : ZMod 1567050703) ^ (124 + 124 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 124 * (3 : ZMod 1567050703) ^ 124) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1267268507 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 1567050703) ^ 498 = 731678118 := by
        calc
          (3 : ZMod 1567050703) ^ 498 = (3 : ZMod 1567050703) ^ (249 + 249) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 249 * (3 : ZMod 1567050703) ^ 249 := by rw [pow_add]
          _ = 731678118 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 1567050703) ^ 996 = 1566932968 := by
        calc
          (3 : ZMod 1567050703) ^ 996 = (3 : ZMod 1567050703) ^ (498 + 498) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 498 * (3 : ZMod 1567050703) ^ 498 := by rw [pow_add]
          _ = 1566932968 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 1567050703) ^ 1992 = 1325124601 := by
        calc
          (3 : ZMod 1567050703) ^ 1992 = (3 : ZMod 1567050703) ^ (996 + 996) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 996 * (3 : ZMod 1567050703) ^ 996 := by rw [pow_add]
          _ = 1325124601 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 1567050703) ^ 3985 = 1094880760 := by
        calc
          (3 : ZMod 1567050703) ^ 3985 = (3 : ZMod 1567050703) ^ (1992 + 1992 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 1992 * (3 : ZMod 1567050703) ^ 1992) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1094880760 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 1567050703) ^ 7970 = 1119945761 := by
        calc
          (3 : ZMod 1567050703) ^ 7970 = (3 : ZMod 1567050703) ^ (3985 + 3985) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 3985 * (3 : ZMod 1567050703) ^ 3985 := by rw [pow_add]
          _ = 1119945761 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 1567050703) ^ 15940 = 407728524 := by
        calc
          (3 : ZMod 1567050703) ^ 15940 = (3 : ZMod 1567050703) ^ (7970 + 7970) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 7970 * (3 : ZMod 1567050703) ^ 7970 := by rw [pow_add]
          _ = 407728524 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 1567050703) ^ 31881 = 1347682685 := by
        calc
          (3 : ZMod 1567050703) ^ 31881 = (3 : ZMod 1567050703) ^ (15940 + 15940 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 15940 * (3 : ZMod 1567050703) ^ 15940) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1347682685 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 1567050703) ^ 63763 = 753077510 := by
        calc
          (3 : ZMod 1567050703) ^ 63763 = (3 : ZMod 1567050703) ^ (31881 + 31881 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 31881 * (3 : ZMod 1567050703) ^ 31881) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 753077510 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 1567050703) ^ 127526 = 1113775592 := by
        calc
          (3 : ZMod 1567050703) ^ 127526 = (3 : ZMod 1567050703) ^ (63763 + 63763) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 63763 * (3 : ZMod 1567050703) ^ 63763 := by rw [pow_add]
          _ = 1113775592 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 1567050703) ^ 255053 = 948140406 := by
        calc
          (3 : ZMod 1567050703) ^ 255053 = (3 : ZMod 1567050703) ^ (127526 + 127526 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 127526 * (3 : ZMod 1567050703) ^ 127526) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 948140406 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 1567050703) ^ 510107 = 1214014959 := by
        calc
          (3 : ZMod 1567050703) ^ 510107 = (3 : ZMod 1567050703) ^ (255053 + 255053 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 255053 * (3 : ZMod 1567050703) ^ 255053) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1214014959 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 1567050703) ^ 1020215 = 641371663 := by
        calc
          (3 : ZMod 1567050703) ^ 1020215 = (3 : ZMod 1567050703) ^ (510107 + 510107 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 510107 * (3 : ZMod 1567050703) ^ 510107) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 641371663 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 1567050703) ^ 2040430 = 1128885252 := by
        calc
          (3 : ZMod 1567050703) ^ 2040430 = (3 : ZMod 1567050703) ^ (1020215 + 1020215) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 1020215 * (3 : ZMod 1567050703) ^ 1020215 := by rw [pow_add]
          _ = 1128885252 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 1567050703) ^ 4080861 = 1199566480 := by
        calc
          (3 : ZMod 1567050703) ^ 4080861 = (3 : ZMod 1567050703) ^ (2040430 + 2040430 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 2040430 * (3 : ZMod 1567050703) ^ 2040430) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1199566480 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 1567050703) ^ 8161722 = 1161567959 := by
        calc
          (3 : ZMod 1567050703) ^ 8161722 = (3 : ZMod 1567050703) ^ (4080861 + 4080861) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 4080861 * (3 : ZMod 1567050703) ^ 4080861 := by rw [pow_add]
          _ = 1161567959 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 1567050703) ^ 16323444 = 1539128858 := by
        calc
          (3 : ZMod 1567050703) ^ 16323444 = (3 : ZMod 1567050703) ^ (8161722 + 8161722) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 8161722 * (3 : ZMod 1567050703) ^ 8161722 := by rw [pow_add]
          _ = 1539128858 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 1567050703) ^ 32646889 = 861305752 := by
        calc
          (3 : ZMod 1567050703) ^ 32646889 = (3 : ZMod 1567050703) ^ (16323444 + 16323444 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 16323444 * (3 : ZMod 1567050703) ^ 16323444) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 861305752 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 1567050703) ^ 65293779 = 456706727 := by
        calc
          (3 : ZMod 1567050703) ^ 65293779 = (3 : ZMod 1567050703) ^ (32646889 + 32646889 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 32646889 * (3 : ZMod 1567050703) ^ 32646889) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 456706727 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 1567050703) ^ 130587558 = 1170698523 := by
        calc
          (3 : ZMod 1567050703) ^ 130587558 = (3 : ZMod 1567050703) ^ (65293779 + 65293779) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 65293779 * (3 : ZMod 1567050703) ^ 65293779 := by rw [pow_add]
          _ = 1170698523 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 1567050703) ^ 261175117 = 1189056539 := by
        calc
          (3 : ZMod 1567050703) ^ 261175117 = (3 : ZMod 1567050703) ^ (130587558 + 130587558 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 130587558 * (3 : ZMod 1567050703) ^ 130587558) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1189056539 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 1567050703) ^ 522350234 = 1189056538 := by
        calc
          (3 : ZMod 1567050703) ^ 522350234 = (3 : ZMod 1567050703) ^ (261175117 + 261175117) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 261175117 * (3 : ZMod 1567050703) ^ 261175117 := by rw [pow_add]
          _ = 1189056538 := by rw [factor_1_27]; decide
      change (3 : ZMod 1567050703) ^ 522350234 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (3 : ZMod 1567050703) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 1567050703) ^ 3 = 27 := by
        calc
          (3 : ZMod 1567050703) ^ 3 = (3 : ZMod 1567050703) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 1 * (3 : ZMod 1567050703) ^ 1) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 1567050703) ^ 6 = 729 := by
        calc
          (3 : ZMod 1567050703) ^ 6 = (3 : ZMod 1567050703) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 3 * (3 : ZMod 1567050703) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 1567050703) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 1567050703) ^ 13 = (3 : ZMod 1567050703) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 6 * (3 : ZMod 1567050703) ^ 6) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 1567050703) ^ 26 = 109588063 := by
        calc
          (3 : ZMod 1567050703) ^ 26 = (3 : ZMod 1567050703) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 13 * (3 : ZMod 1567050703) ^ 13 := by rw [pow_add]
          _ = 109588063 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 1567050703) ^ 53 = 671248421 := by
        calc
          (3 : ZMod 1567050703) ^ 53 = (3 : ZMod 1567050703) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 26 * (3 : ZMod 1567050703) ^ 26) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 671248421 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 1567050703) ^ 106 = 1474995066 := by
        calc
          (3 : ZMod 1567050703) ^ 106 = (3 : ZMod 1567050703) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 53 * (3 : ZMod 1567050703) ^ 53 := by rw [pow_add]
          _ = 1474995066 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 1567050703) ^ 213 = 1343903734 := by
        calc
          (3 : ZMod 1567050703) ^ 213 = (3 : ZMod 1567050703) ^ (106 + 106 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 106 * (3 : ZMod 1567050703) ^ 106) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1343903734 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 1567050703) ^ 426 = 1110474427 := by
        calc
          (3 : ZMod 1567050703) ^ 426 = (3 : ZMod 1567050703) ^ (213 + 213) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 213 * (3 : ZMod 1567050703) ^ 213 := by rw [pow_add]
          _ = 1110474427 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 1567050703) ^ 853 = 393362750 := by
        calc
          (3 : ZMod 1567050703) ^ 853 = (3 : ZMod 1567050703) ^ (426 + 426 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 426 * (3 : ZMod 1567050703) ^ 426) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 393362750 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 1567050703) ^ 1707 = 891143143 := by
        calc
          (3 : ZMod 1567050703) ^ 1707 = (3 : ZMod 1567050703) ^ (853 + 853 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 853 * (3 : ZMod 1567050703) ^ 853) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 891143143 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 1567050703) ^ 3415 = 1034531016 := by
        calc
          (3 : ZMod 1567050703) ^ 3415 = (3 : ZMod 1567050703) ^ (1707 + 1707 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 1707 * (3 : ZMod 1567050703) ^ 1707) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1034531016 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 1567050703) ^ 6831 = 246835032 := by
        calc
          (3 : ZMod 1567050703) ^ 6831 = (3 : ZMod 1567050703) ^ (3415 + 3415 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 3415 * (3 : ZMod 1567050703) ^ 3415) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 246835032 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 1567050703) ^ 13663 = 1394043919 := by
        calc
          (3 : ZMod 1567050703) ^ 13663 = (3 : ZMod 1567050703) ^ (6831 + 6831 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 6831 * (3 : ZMod 1567050703) ^ 6831) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1394043919 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 1567050703) ^ 27327 = 1049304771 := by
        calc
          (3 : ZMod 1567050703) ^ 27327 = (3 : ZMod 1567050703) ^ (13663 + 13663 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 13663 * (3 : ZMod 1567050703) ^ 13663) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1049304771 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 1567050703) ^ 54654 = 363949810 := by
        calc
          (3 : ZMod 1567050703) ^ 54654 = (3 : ZMod 1567050703) ^ (27327 + 27327) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 27327 * (3 : ZMod 1567050703) ^ 27327 := by rw [pow_add]
          _ = 363949810 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 1567050703) ^ 109308 = 1391291381 := by
        calc
          (3 : ZMod 1567050703) ^ 109308 = (3 : ZMod 1567050703) ^ (54654 + 54654) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 54654 * (3 : ZMod 1567050703) ^ 54654 := by rw [pow_add]
          _ = 1391291381 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 1567050703) ^ 218617 = 1001339959 := by
        calc
          (3 : ZMod 1567050703) ^ 218617 = (3 : ZMod 1567050703) ^ (109308 + 109308 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 109308 * (3 : ZMod 1567050703) ^ 109308) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1001339959 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 1567050703) ^ 437235 = 883299827 := by
        calc
          (3 : ZMod 1567050703) ^ 437235 = (3 : ZMod 1567050703) ^ (218617 + 218617 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 218617 * (3 : ZMod 1567050703) ^ 218617) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 883299827 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 1567050703) ^ 874470 = 1332990687 := by
        calc
          (3 : ZMod 1567050703) ^ 874470 = (3 : ZMod 1567050703) ^ (437235 + 437235) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 437235 * (3 : ZMod 1567050703) ^ 437235 := by rw [pow_add]
          _ = 1332990687 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 1567050703) ^ 1748940 = 80090959 := by
        calc
          (3 : ZMod 1567050703) ^ 1748940 = (3 : ZMod 1567050703) ^ (874470 + 874470) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 874470 * (3 : ZMod 1567050703) ^ 874470 := by rw [pow_add]
          _ = 80090959 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 1567050703) ^ 3497881 = 66993364 := by
        calc
          (3 : ZMod 1567050703) ^ 3497881 = (3 : ZMod 1567050703) ^ (1748940 + 1748940 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 1748940 * (3 : ZMod 1567050703) ^ 1748940) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 66993364 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 1567050703) ^ 6995762 = 821160049 := by
        calc
          (3 : ZMod 1567050703) ^ 6995762 = (3 : ZMod 1567050703) ^ (3497881 + 3497881) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 3497881 * (3 : ZMod 1567050703) ^ 3497881 := by rw [pow_add]
          _ = 821160049 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 1567050703) ^ 13991524 = 1472076850 := by
        calc
          (3 : ZMod 1567050703) ^ 13991524 = (3 : ZMod 1567050703) ^ (6995762 + 6995762) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 6995762 * (3 : ZMod 1567050703) ^ 6995762 := by rw [pow_add]
          _ = 1472076850 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 1567050703) ^ 27983048 = 1152358241 := by
        calc
          (3 : ZMod 1567050703) ^ 27983048 = (3 : ZMod 1567050703) ^ (13991524 + 13991524) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 13991524 * (3 : ZMod 1567050703) ^ 13991524 := by rw [pow_add]
          _ = 1152358241 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 1567050703) ^ 55966096 = 1477642204 := by
        calc
          (3 : ZMod 1567050703) ^ 55966096 = (3 : ZMod 1567050703) ^ (27983048 + 27983048) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 27983048 * (3 : ZMod 1567050703) ^ 27983048 := by rw [pow_add]
          _ = 1477642204 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 1567050703) ^ 111932193 = 1278964072 := by
        calc
          (3 : ZMod 1567050703) ^ 111932193 = (3 : ZMod 1567050703) ^ (55966096 + 55966096 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 55966096 * (3 : ZMod 1567050703) ^ 55966096) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1278964072 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 1567050703) ^ 223864386 = 1119198908 := by
        calc
          (3 : ZMod 1567050703) ^ 223864386 = (3 : ZMod 1567050703) ^ (111932193 + 111932193) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 111932193 * (3 : ZMod 1567050703) ^ 111932193 := by rw [pow_add]
          _ = 1119198908 := by rw [factor_2_26]; decide
      change (3 : ZMod 1567050703) ^ 223864386 ≠ 1
      rw [factor_2_27]
      decide
    ·
      have factor_3_0 : (3 : ZMod 1567050703) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 1567050703) ^ 2 = 9 := by
        calc
          (3 : ZMod 1567050703) ^ 2 = (3 : ZMod 1567050703) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 1 * (3 : ZMod 1567050703) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 1567050703) ^ 5 = 243 := by
        calc
          (3 : ZMod 1567050703) ^ 5 = (3 : ZMod 1567050703) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 2 * (3 : ZMod 1567050703) ^ 2) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 1567050703) ^ 11 = 177147 := by
        calc
          (3 : ZMod 1567050703) ^ 11 = (3 : ZMod 1567050703) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 5 * (3 : ZMod 1567050703) ^ 5) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 1567050703) ^ 23 = 120136647 := by
        calc
          (3 : ZMod 1567050703) ^ 23 = (3 : ZMod 1567050703) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 11 * (3 : ZMod 1567050703) ^ 11) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 120136647 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 1567050703) ^ 47 = 396445237 := by
        calc
          (3 : ZMod 1567050703) ^ 47 = (3 : ZMod 1567050703) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 23 * (3 : ZMod 1567050703) ^ 23) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 396445237 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 1567050703) ^ 95 = 129567532 := by
        calc
          (3 : ZMod 1567050703) ^ 95 = (3 : ZMod 1567050703) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 47 * (3 : ZMod 1567050703) ^ 47) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 129567532 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 1567050703) ^ 191 = 352688868 := by
        calc
          (3 : ZMod 1567050703) ^ 191 = (3 : ZMod 1567050703) ^ (95 + 95 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 95 * (3 : ZMod 1567050703) ^ 95) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 352688868 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 1567050703) ^ 383 = 594745574 := by
        calc
          (3 : ZMod 1567050703) ^ 383 = (3 : ZMod 1567050703) ^ (191 + 191 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 191 * (3 : ZMod 1567050703) ^ 191) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 594745574 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 1567050703) ^ 767 = 1137342906 := by
        calc
          (3 : ZMod 1567050703) ^ 767 = (3 : ZMod 1567050703) ^ (383 + 383 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 383 * (3 : ZMod 1567050703) ^ 383) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1137342906 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 1567050703) ^ 1534 = 282364871 := by
        calc
          (3 : ZMod 1567050703) ^ 1534 = (3 : ZMod 1567050703) ^ (767 + 767) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 767 * (3 : ZMod 1567050703) ^ 767 := by rw [pow_add]
          _ = 282364871 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 1567050703) ^ 3069 = 1242849926 := by
        calc
          (3 : ZMod 1567050703) ^ 3069 = (3 : ZMod 1567050703) ^ (1534 + 1534 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 1534 * (3 : ZMod 1567050703) ^ 1534) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1242849926 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 1567050703) ^ 6139 = 725176610 := by
        calc
          (3 : ZMod 1567050703) ^ 6139 = (3 : ZMod 1567050703) ^ (3069 + 3069 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 3069 * (3 : ZMod 1567050703) ^ 3069) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 725176610 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 1567050703) ^ 12279 = 306023985 := by
        calc
          (3 : ZMod 1567050703) ^ 12279 = (3 : ZMod 1567050703) ^ (6139 + 6139 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 6139 * (3 : ZMod 1567050703) ^ 6139) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 306023985 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 1567050703) ^ 24558 = 1370377788 := by
        calc
          (3 : ZMod 1567050703) ^ 24558 = (3 : ZMod 1567050703) ^ (12279 + 12279) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 12279 * (3 : ZMod 1567050703) ^ 12279 := by rw [pow_add]
          _ = 1370377788 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 1567050703) ^ 49117 = 179171723 := by
        calc
          (3 : ZMod 1567050703) ^ 49117 = (3 : ZMod 1567050703) ^ (24558 + 24558 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 24558 * (3 : ZMod 1567050703) ^ 24558) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 179171723 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 1567050703) ^ 98235 = 499569430 := by
        calc
          (3 : ZMod 1567050703) ^ 98235 = (3 : ZMod 1567050703) ^ (49117 + 49117 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 49117 * (3 : ZMod 1567050703) ^ 49117) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 499569430 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 1567050703) ^ 196470 = 1556542958 := by
        calc
          (3 : ZMod 1567050703) ^ 196470 = (3 : ZMod 1567050703) ^ (98235 + 98235) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 98235 * (3 : ZMod 1567050703) ^ 98235 := by rw [pow_add]
          _ = 1556542958 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 1567050703) ^ 392941 = 1205557747 := by
        calc
          (3 : ZMod 1567050703) ^ 392941 = (3 : ZMod 1567050703) ^ (196470 + 196470 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 196470 * (3 : ZMod 1567050703) ^ 196470) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1205557747 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 1567050703) ^ 785883 = 1322818921 := by
        calc
          (3 : ZMod 1567050703) ^ 785883 = (3 : ZMod 1567050703) ^ (392941 + 392941 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 392941 * (3 : ZMod 1567050703) ^ 392941) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1322818921 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 1567050703) ^ 1571766 = 448329615 := by
        calc
          (3 : ZMod 1567050703) ^ 1571766 = (3 : ZMod 1567050703) ^ (785883 + 785883) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 785883 * (3 : ZMod 1567050703) ^ 785883 := by rw [pow_add]
          _ = 448329615 := by rw [factor_3_19]; decide
      change (3 : ZMod 1567050703) ^ 1571766 ≠ 1
      rw [factor_3_20]
      decide
    ·
      have factor_4_0 : (3 : ZMod 1567050703) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 1567050703) ^ 2 = 9 := by
        calc
          (3 : ZMod 1567050703) ^ 2 = (3 : ZMod 1567050703) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 1 * (3 : ZMod 1567050703) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 1567050703) ^ 5 = 243 := by
        calc
          (3 : ZMod 1567050703) ^ 5 = (3 : ZMod 1567050703) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 2 * (3 : ZMod 1567050703) ^ 2) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 1567050703) ^ 10 = 59049 := by
        calc
          (3 : ZMod 1567050703) ^ 10 = (3 : ZMod 1567050703) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 5 * (3 : ZMod 1567050703) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 1567050703) ^ 20 = 352682995 := by
        calc
          (3 : ZMod 1567050703) ^ 20 = (3 : ZMod 1567050703) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 10 * (3 : ZMod 1567050703) ^ 10 := by rw [pow_add]
          _ = 352682995 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 1567050703) ^ 40 = 1353706092 := by
        calc
          (3 : ZMod 1567050703) ^ 40 = (3 : ZMod 1567050703) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 20 * (3 : ZMod 1567050703) ^ 20 := by rw [pow_add]
          _ = 1353706092 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 1567050703) ^ 81 = 1101560593 := by
        calc
          (3 : ZMod 1567050703) ^ 81 = (3 : ZMod 1567050703) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 40 * (3 : ZMod 1567050703) ^ 40) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1101560593 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 1567050703) ^ 163 = 1112355920 := by
        calc
          (3 : ZMod 1567050703) ^ 163 = (3 : ZMod 1567050703) ^ (81 + 81 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 81 * (3 : ZMod 1567050703) ^ 81) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1112355920 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 1567050703) ^ 327 = 1222890520 := by
        calc
          (3 : ZMod 1567050703) ^ 327 = (3 : ZMod 1567050703) ^ (163 + 163 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 163 * (3 : ZMod 1567050703) ^ 163) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1222890520 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 1567050703) ^ 654 = 570572842 := by
        calc
          (3 : ZMod 1567050703) ^ 654 = (3 : ZMod 1567050703) ^ (327 + 327) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 327 * (3 : ZMod 1567050703) ^ 327 := by rw [pow_add]
          _ = 570572842 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 1567050703) ^ 1308 = 1093542476 := by
        calc
          (3 : ZMod 1567050703) ^ 1308 = (3 : ZMod 1567050703) ^ (654 + 654) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 654 * (3 : ZMod 1567050703) ^ 654 := by rw [pow_add]
          _ = 1093542476 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 1567050703) ^ 2617 = 1115240513 := by
        calc
          (3 : ZMod 1567050703) ^ 2617 = (3 : ZMod 1567050703) ^ (1308 + 1308 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 1308 * (3 : ZMod 1567050703) ^ 1308) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 1115240513 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 1567050703) ^ 5234 = 317527475 := by
        calc
          (3 : ZMod 1567050703) ^ 5234 = (3 : ZMod 1567050703) ^ (2617 + 2617) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 2617 * (3 : ZMod 1567050703) ^ 2617 := by rw [pow_add]
          _ = 317527475 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 1567050703) ^ 10468 = 1467060988 := by
        calc
          (3 : ZMod 1567050703) ^ 10468 = (3 : ZMod 1567050703) ^ (5234 + 5234) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 5234 * (3 : ZMod 1567050703) ^ 5234 := by rw [pow_add]
          _ = 1467060988 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 1567050703) ^ 20937 = 911459260 := by
        calc
          (3 : ZMod 1567050703) ^ 20937 = (3 : ZMod 1567050703) ^ (10468 + 10468 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = ((3 : ZMod 1567050703) ^ 10468 * (3 : ZMod 1567050703) ^ 10468) * (3 : ZMod 1567050703) := by rw [pow_succ, pow_add]
          _ = 911459260 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 1567050703) ^ 41874 = 762605003 := by
        calc
          (3 : ZMod 1567050703) ^ 41874 = (3 : ZMod 1567050703) ^ (20937 + 20937) :=
            congrArg (fun n : ℕ => (3 : ZMod 1567050703) ^ n) (by norm_num)
          _ = (3 : ZMod 1567050703) ^ 20937 * (3 : ZMod 1567050703) ^ 20937 := by rw [pow_add]
          _ = 762605003 := by rw [factor_4_14]; decide
      change (3 : ZMod 1567050703) ^ 41874 ≠ 1
      rw [factor_4_15]
      decide

#print axioms prime_lucas_1567050703

end TotientTailPeriodKiller
end Erdos249257
