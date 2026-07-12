import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_103010909 : Nat.Prime 103010909 := by
  apply lucas_primality 103010909 (2 : ZMod 103010909)
  ·
      have fermat_0 : (2 : ZMod 103010909) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 103010909) ^ 3 = 8 := by
        calc
          (2 : ZMod 103010909) ^ 3 = (2 : ZMod 103010909) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 1 * (2 : ZMod 103010909) ^ 1) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 103010909) ^ 6 = 64 := by
        calc
          (2 : ZMod 103010909) ^ 6 = (2 : ZMod 103010909) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 3 * (2 : ZMod 103010909) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 103010909) ^ 12 = 4096 := by
        calc
          (2 : ZMod 103010909) ^ 12 = (2 : ZMod 103010909) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 6 * (2 : ZMod 103010909) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 103010909) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 103010909) ^ 24 = (2 : ZMod 103010909) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 12 * (2 : ZMod 103010909) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 103010909) ^ 49 = 74238126 := by
        calc
          (2 : ZMod 103010909) ^ 49 = (2 : ZMod 103010909) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 24 * (2 : ZMod 103010909) ^ 24) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 74238126 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 103010909) ^ 98 = 15648430 := by
        calc
          (2 : ZMod 103010909) ^ 98 = (2 : ZMod 103010909) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 49 * (2 : ZMod 103010909) ^ 49 := by rw [pow_add]
          _ = 15648430 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 103010909) ^ 196 = 52037369 := by
        calc
          (2 : ZMod 103010909) ^ 196 = (2 : ZMod 103010909) ^ (98 + 98) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 98 * (2 : ZMod 103010909) ^ 98 := by rw [pow_add]
          _ = 52037369 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 103010909) ^ 392 = 39326469 := by
        calc
          (2 : ZMod 103010909) ^ 392 = (2 : ZMod 103010909) ^ (196 + 196) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 196 * (2 : ZMod 103010909) ^ 196 := by rw [pow_add]
          _ = 39326469 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 103010909) ^ 785 = 78905679 := by
        calc
          (2 : ZMod 103010909) ^ 785 = (2 : ZMod 103010909) ^ (392 + 392 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 392 * (2 : ZMod 103010909) ^ 392) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 78905679 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 103010909) ^ 1571 = 64124124 := by
        calc
          (2 : ZMod 103010909) ^ 1571 = (2 : ZMod 103010909) ^ (785 + 785 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 785 * (2 : ZMod 103010909) ^ 785) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 64124124 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 103010909) ^ 3143 = 66872418 := by
        calc
          (2 : ZMod 103010909) ^ 3143 = (2 : ZMod 103010909) ^ (1571 + 1571 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 1571 * (2 : ZMod 103010909) ^ 1571) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 66872418 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 103010909) ^ 6287 = 92059285 := by
        calc
          (2 : ZMod 103010909) ^ 6287 = (2 : ZMod 103010909) ^ (3143 + 3143 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 3143 * (2 : ZMod 103010909) ^ 3143) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 92059285 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 103010909) ^ 12574 = 97637769 := by
        calc
          (2 : ZMod 103010909) ^ 12574 = (2 : ZMod 103010909) ^ (6287 + 6287) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 6287 * (2 : ZMod 103010909) ^ 6287 := by rw [pow_add]
          _ = 97637769 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 103010909) ^ 25149 = 47042885 := by
        calc
          (2 : ZMod 103010909) ^ 25149 = (2 : ZMod 103010909) ^ (12574 + 12574 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 12574 * (2 : ZMod 103010909) ^ 12574) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 47042885 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 103010909) ^ 50298 = 19818087 := by
        calc
          (2 : ZMod 103010909) ^ 50298 = (2 : ZMod 103010909) ^ (25149 + 25149) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 25149 * (2 : ZMod 103010909) ^ 25149 := by rw [pow_add]
          _ = 19818087 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 103010909) ^ 100596 = 80875275 := by
        calc
          (2 : ZMod 103010909) ^ 100596 = (2 : ZMod 103010909) ^ (50298 + 50298) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 50298 * (2 : ZMod 103010909) ^ 50298 := by rw [pow_add]
          _ = 80875275 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 103010909) ^ 201193 = 37694211 := by
        calc
          (2 : ZMod 103010909) ^ 201193 = (2 : ZMod 103010909) ^ (100596 + 100596 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 100596 * (2 : ZMod 103010909) ^ 100596) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 37694211 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 103010909) ^ 402386 = 73533724 := by
        calc
          (2 : ZMod 103010909) ^ 402386 = (2 : ZMod 103010909) ^ (201193 + 201193) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 201193 * (2 : ZMod 103010909) ^ 201193 := by rw [pow_add]
          _ = 73533724 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 103010909) ^ 804772 = 1323777 := by
        calc
          (2 : ZMod 103010909) ^ 804772 = (2 : ZMod 103010909) ^ (402386 + 402386) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 402386 * (2 : ZMod 103010909) ^ 402386 := by rw [pow_add]
          _ = 1323777 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 103010909) ^ 1609545 = 30934551 := by
        calc
          (2 : ZMod 103010909) ^ 1609545 = (2 : ZMod 103010909) ^ (804772 + 804772 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 804772 * (2 : ZMod 103010909) ^ 804772) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 30934551 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 103010909) ^ 3219090 = 29601579 := by
        calc
          (2 : ZMod 103010909) ^ 3219090 = (2 : ZMod 103010909) ^ (1609545 + 1609545) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 1609545 * (2 : ZMod 103010909) ^ 1609545 := by rw [pow_add]
          _ = 29601579 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 103010909) ^ 6438181 = 81645830 := by
        calc
          (2 : ZMod 103010909) ^ 6438181 = (2 : ZMod 103010909) ^ (3219090 + 3219090 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 3219090 * (2 : ZMod 103010909) ^ 3219090) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 81645830 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 103010909) ^ 12876363 = 50449072 := by
        calc
          (2 : ZMod 103010909) ^ 12876363 = (2 : ZMod 103010909) ^ (6438181 + 6438181 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 6438181 * (2 : ZMod 103010909) ^ 6438181) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 50449072 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 103010909) ^ 25752727 = 2112764 := by
        calc
          (2 : ZMod 103010909) ^ 25752727 = (2 : ZMod 103010909) ^ (12876363 + 12876363 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 12876363 * (2 : ZMod 103010909) ^ 12876363) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 2112764 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 103010909) ^ 51505454 = 103010908 := by
        calc
          (2 : ZMod 103010909) ^ 51505454 = (2 : ZMod 103010909) ^ (25752727 + 25752727) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 25752727 * (2 : ZMod 103010909) ^ 25752727 := by rw [pow_add]
          _ = 103010908 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 103010909) ^ 103010908 = 1 := by
        calc
          (2 : ZMod 103010909) ^ 103010908 = (2 : ZMod 103010909) ^ (51505454 + 51505454) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 51505454 * (2 : ZMod 103010909) ^ 51505454 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (11, 1), (13, 2), (1979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (11, 1), (13, 2), (1979, 1)] : List FactorBlock).map factorBlockValue).prod = 103010909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 103010909) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 103010909) ^ 3 = 8 := by
        calc
          (2 : ZMod 103010909) ^ 3 = (2 : ZMod 103010909) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 1 * (2 : ZMod 103010909) ^ 1) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 103010909) ^ 6 = 64 := by
        calc
          (2 : ZMod 103010909) ^ 6 = (2 : ZMod 103010909) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 3 * (2 : ZMod 103010909) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 103010909) ^ 12 = 4096 := by
        calc
          (2 : ZMod 103010909) ^ 12 = (2 : ZMod 103010909) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 6 * (2 : ZMod 103010909) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 103010909) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 103010909) ^ 24 = (2 : ZMod 103010909) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 12 * (2 : ZMod 103010909) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 103010909) ^ 49 = 74238126 := by
        calc
          (2 : ZMod 103010909) ^ 49 = (2 : ZMod 103010909) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 24 * (2 : ZMod 103010909) ^ 24) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 74238126 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 103010909) ^ 98 = 15648430 := by
        calc
          (2 : ZMod 103010909) ^ 98 = (2 : ZMod 103010909) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 49 * (2 : ZMod 103010909) ^ 49 := by rw [pow_add]
          _ = 15648430 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 103010909) ^ 196 = 52037369 := by
        calc
          (2 : ZMod 103010909) ^ 196 = (2 : ZMod 103010909) ^ (98 + 98) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 98 * (2 : ZMod 103010909) ^ 98 := by rw [pow_add]
          _ = 52037369 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 103010909) ^ 392 = 39326469 := by
        calc
          (2 : ZMod 103010909) ^ 392 = (2 : ZMod 103010909) ^ (196 + 196) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 196 * (2 : ZMod 103010909) ^ 196 := by rw [pow_add]
          _ = 39326469 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 103010909) ^ 785 = 78905679 := by
        calc
          (2 : ZMod 103010909) ^ 785 = (2 : ZMod 103010909) ^ (392 + 392 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 392 * (2 : ZMod 103010909) ^ 392) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 78905679 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 103010909) ^ 1571 = 64124124 := by
        calc
          (2 : ZMod 103010909) ^ 1571 = (2 : ZMod 103010909) ^ (785 + 785 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 785 * (2 : ZMod 103010909) ^ 785) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 64124124 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 103010909) ^ 3143 = 66872418 := by
        calc
          (2 : ZMod 103010909) ^ 3143 = (2 : ZMod 103010909) ^ (1571 + 1571 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 1571 * (2 : ZMod 103010909) ^ 1571) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 66872418 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 103010909) ^ 6287 = 92059285 := by
        calc
          (2 : ZMod 103010909) ^ 6287 = (2 : ZMod 103010909) ^ (3143 + 3143 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 3143 * (2 : ZMod 103010909) ^ 3143) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 92059285 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 103010909) ^ 12574 = 97637769 := by
        calc
          (2 : ZMod 103010909) ^ 12574 = (2 : ZMod 103010909) ^ (6287 + 6287) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 6287 * (2 : ZMod 103010909) ^ 6287 := by rw [pow_add]
          _ = 97637769 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 103010909) ^ 25149 = 47042885 := by
        calc
          (2 : ZMod 103010909) ^ 25149 = (2 : ZMod 103010909) ^ (12574 + 12574 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 12574 * (2 : ZMod 103010909) ^ 12574) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 47042885 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 103010909) ^ 50298 = 19818087 := by
        calc
          (2 : ZMod 103010909) ^ 50298 = (2 : ZMod 103010909) ^ (25149 + 25149) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 25149 * (2 : ZMod 103010909) ^ 25149 := by rw [pow_add]
          _ = 19818087 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 103010909) ^ 100596 = 80875275 := by
        calc
          (2 : ZMod 103010909) ^ 100596 = (2 : ZMod 103010909) ^ (50298 + 50298) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 50298 * (2 : ZMod 103010909) ^ 50298 := by rw [pow_add]
          _ = 80875275 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 103010909) ^ 201193 = 37694211 := by
        calc
          (2 : ZMod 103010909) ^ 201193 = (2 : ZMod 103010909) ^ (100596 + 100596 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 100596 * (2 : ZMod 103010909) ^ 100596) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 37694211 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 103010909) ^ 402386 = 73533724 := by
        calc
          (2 : ZMod 103010909) ^ 402386 = (2 : ZMod 103010909) ^ (201193 + 201193) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 201193 * (2 : ZMod 103010909) ^ 201193 := by rw [pow_add]
          _ = 73533724 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 103010909) ^ 804772 = 1323777 := by
        calc
          (2 : ZMod 103010909) ^ 804772 = (2 : ZMod 103010909) ^ (402386 + 402386) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 402386 * (2 : ZMod 103010909) ^ 402386 := by rw [pow_add]
          _ = 1323777 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 103010909) ^ 1609545 = 30934551 := by
        calc
          (2 : ZMod 103010909) ^ 1609545 = (2 : ZMod 103010909) ^ (804772 + 804772 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 804772 * (2 : ZMod 103010909) ^ 804772) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 30934551 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 103010909) ^ 3219090 = 29601579 := by
        calc
          (2 : ZMod 103010909) ^ 3219090 = (2 : ZMod 103010909) ^ (1609545 + 1609545) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 1609545 * (2 : ZMod 103010909) ^ 1609545 := by rw [pow_add]
          _ = 29601579 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 103010909) ^ 6438181 = 81645830 := by
        calc
          (2 : ZMod 103010909) ^ 6438181 = (2 : ZMod 103010909) ^ (3219090 + 3219090 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 3219090 * (2 : ZMod 103010909) ^ 3219090) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 81645830 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 103010909) ^ 12876363 = 50449072 := by
        calc
          (2 : ZMod 103010909) ^ 12876363 = (2 : ZMod 103010909) ^ (6438181 + 6438181 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 6438181 * (2 : ZMod 103010909) ^ 6438181) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 50449072 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 103010909) ^ 25752727 = 2112764 := by
        calc
          (2 : ZMod 103010909) ^ 25752727 = (2 : ZMod 103010909) ^ (12876363 + 12876363 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 12876363 * (2 : ZMod 103010909) ^ 12876363) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 2112764 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 103010909) ^ 51505454 = 103010908 := by
        calc
          (2 : ZMod 103010909) ^ 51505454 = (2 : ZMod 103010909) ^ (25752727 + 25752727) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 25752727 * (2 : ZMod 103010909) ^ 25752727 := by rw [pow_add]
          _ = 103010908 := by rw [factor_0_24]; decide
      change (2 : ZMod 103010909) ^ 51505454 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (2 : ZMod 103010909) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 103010909) ^ 3 = 8 := by
        calc
          (2 : ZMod 103010909) ^ 3 = (2 : ZMod 103010909) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 1 * (2 : ZMod 103010909) ^ 1) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 103010909) ^ 7 = 128 := by
        calc
          (2 : ZMod 103010909) ^ 7 = (2 : ZMod 103010909) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 3 * (2 : ZMod 103010909) ^ 3) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 103010909) ^ 14 = 16384 := by
        calc
          (2 : ZMod 103010909) ^ 14 = (2 : ZMod 103010909) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 7 * (2 : ZMod 103010909) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 103010909) ^ 28 = 62413638 := by
        calc
          (2 : ZMod 103010909) ^ 28 = (2 : ZMod 103010909) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 14 * (2 : ZMod 103010909) ^ 14 := by rw [pow_add]
          _ = 62413638 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 103010909) ^ 56 = 25476500 := by
        calc
          (2 : ZMod 103010909) ^ 56 = (2 : ZMod 103010909) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 28 * (2 : ZMod 103010909) ^ 28 := by rw [pow_add]
          _ = 25476500 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 103010909) ^ 112 = 92735528 := by
        calc
          (2 : ZMod 103010909) ^ 112 = (2 : ZMod 103010909) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 56 * (2 : ZMod 103010909) ^ 56 := by rw [pow_add]
          _ = 92735528 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 103010909) ^ 224 = 54264704 := by
        calc
          (2 : ZMod 103010909) ^ 224 = (2 : ZMod 103010909) ^ (112 + 112) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 112 * (2 : ZMod 103010909) ^ 112 := by rw [pow_add]
          _ = 54264704 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 103010909) ^ 449 = 100565393 := by
        calc
          (2 : ZMod 103010909) ^ 449 = (2 : ZMod 103010909) ^ (224 + 224 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 224 * (2 : ZMod 103010909) ^ 224) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 100565393 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 103010909) ^ 898 = 44162443 := by
        calc
          (2 : ZMod 103010909) ^ 898 = (2 : ZMod 103010909) ^ (449 + 449) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 449 * (2 : ZMod 103010909) ^ 449 := by rw [pow_add]
          _ = 44162443 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 103010909) ^ 1796 = 70962172 := by
        calc
          (2 : ZMod 103010909) ^ 1796 = (2 : ZMod 103010909) ^ (898 + 898) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 898 * (2 : ZMod 103010909) ^ 898 := by rw [pow_add]
          _ = 70962172 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 103010909) ^ 3592 = 78688896 := by
        calc
          (2 : ZMod 103010909) ^ 3592 = (2 : ZMod 103010909) ^ (1796 + 1796) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 1796 * (2 : ZMod 103010909) ^ 1796 := by rw [pow_add]
          _ = 78688896 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 103010909) ^ 7185 = 65613919 := by
        calc
          (2 : ZMod 103010909) ^ 7185 = (2 : ZMod 103010909) ^ (3592 + 3592 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 3592 * (2 : ZMod 103010909) ^ 3592) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 65613919 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 103010909) ^ 14370 = 44257970 := by
        calc
          (2 : ZMod 103010909) ^ 14370 = (2 : ZMod 103010909) ^ (7185 + 7185) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 7185 * (2 : ZMod 103010909) ^ 7185 := by rw [pow_add]
          _ = 44257970 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 103010909) ^ 28741 = 44499100 := by
        calc
          (2 : ZMod 103010909) ^ 28741 = (2 : ZMod 103010909) ^ (14370 + 14370 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 14370 * (2 : ZMod 103010909) ^ 14370) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 44499100 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 103010909) ^ 57483 = 9071439 := by
        calc
          (2 : ZMod 103010909) ^ 57483 = (2 : ZMod 103010909) ^ (28741 + 28741 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 28741 * (2 : ZMod 103010909) ^ 28741) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 9071439 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 103010909) ^ 114967 = 39599416 := by
        calc
          (2 : ZMod 103010909) ^ 114967 = (2 : ZMod 103010909) ^ (57483 + 57483 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 57483 * (2 : ZMod 103010909) ^ 57483) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 39599416 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 103010909) ^ 229935 = 6184438 := by
        calc
          (2 : ZMod 103010909) ^ 229935 = (2 : ZMod 103010909) ^ (114967 + 114967 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 114967 * (2 : ZMod 103010909) ^ 114967) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 6184438 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 103010909) ^ 459870 = 43940507 := by
        calc
          (2 : ZMod 103010909) ^ 459870 = (2 : ZMod 103010909) ^ (229935 + 229935) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 229935 * (2 : ZMod 103010909) ^ 229935 := by rw [pow_add]
          _ = 43940507 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 103010909) ^ 919740 = 76364625 := by
        calc
          (2 : ZMod 103010909) ^ 919740 = (2 : ZMod 103010909) ^ (459870 + 459870) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 459870 * (2 : ZMod 103010909) ^ 459870 := by rw [pow_add]
          _ = 76364625 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 103010909) ^ 1839480 = 25424357 := by
        calc
          (2 : ZMod 103010909) ^ 1839480 = (2 : ZMod 103010909) ^ (919740 + 919740) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 919740 * (2 : ZMod 103010909) ^ 919740 := by rw [pow_add]
          _ = 25424357 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 103010909) ^ 3678961 = 90838724 := by
        calc
          (2 : ZMod 103010909) ^ 3678961 = (2 : ZMod 103010909) ^ (1839480 + 1839480 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 1839480 * (2 : ZMod 103010909) ^ 1839480) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 90838724 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 103010909) ^ 7357922 = 55106799 := by
        calc
          (2 : ZMod 103010909) ^ 7357922 = (2 : ZMod 103010909) ^ (3678961 + 3678961) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 3678961 * (2 : ZMod 103010909) ^ 3678961 := by rw [pow_add]
          _ = 55106799 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 103010909) ^ 14715844 = 67957308 := by
        calc
          (2 : ZMod 103010909) ^ 14715844 = (2 : ZMod 103010909) ^ (7357922 + 7357922) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 7357922 * (2 : ZMod 103010909) ^ 7357922 := by rw [pow_add]
          _ = 67957308 := by rw [factor_1_22]; decide
      change (2 : ZMod 103010909) ^ 14715844 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (2 : ZMod 103010909) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 103010909) ^ 2 = 4 := by
        calc
          (2 : ZMod 103010909) ^ 2 = (2 : ZMod 103010909) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 1 * (2 : ZMod 103010909) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 103010909) ^ 4 = 16 := by
        calc
          (2 : ZMod 103010909) ^ 4 = (2 : ZMod 103010909) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 2 * (2 : ZMod 103010909) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 103010909) ^ 8 = 256 := by
        calc
          (2 : ZMod 103010909) ^ 8 = (2 : ZMod 103010909) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 4 * (2 : ZMod 103010909) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 103010909) ^ 17 = 131072 := by
        calc
          (2 : ZMod 103010909) ^ 17 = (2 : ZMod 103010909) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 8 * (2 : ZMod 103010909) ^ 8) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 103010909) ^ 35 = 57105671 := by
        calc
          (2 : ZMod 103010909) ^ 35 = (2 : ZMod 103010909) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 17 * (2 : ZMod 103010909) ^ 17) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 57105671 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 103010909) ^ 71 = 13545464 := by
        calc
          (2 : ZMod 103010909) ^ 71 = (2 : ZMod 103010909) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 35 * (2 : ZMod 103010909) ^ 35) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 13545464 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 103010909) ^ 142 = 66235402 := by
        calc
          (2 : ZMod 103010909) ^ 142 = (2 : ZMod 103010909) ^ (71 + 71) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 71 * (2 : ZMod 103010909) ^ 71 := by rw [pow_add]
          _ = 66235402 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 103010909) ^ 285 = 33066657 := by
        calc
          (2 : ZMod 103010909) ^ 285 = (2 : ZMod 103010909) ^ (142 + 142 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 142 * (2 : ZMod 103010909) ^ 142) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 33066657 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 103010909) ^ 571 = 45317561 := by
        calc
          (2 : ZMod 103010909) ^ 571 = (2 : ZMod 103010909) ^ (285 + 285 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 285 * (2 : ZMod 103010909) ^ 285) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 45317561 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 103010909) ^ 1143 = 42504086 := by
        calc
          (2 : ZMod 103010909) ^ 1143 = (2 : ZMod 103010909) ^ (571 + 571 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 571 * (2 : ZMod 103010909) ^ 571) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 42504086 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 103010909) ^ 2286 = 39504298 := by
        calc
          (2 : ZMod 103010909) ^ 2286 = (2 : ZMod 103010909) ^ (1143 + 1143) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 1143 * (2 : ZMod 103010909) ^ 1143 := by rw [pow_add]
          _ = 39504298 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 103010909) ^ 4572 = 41850054 := by
        calc
          (2 : ZMod 103010909) ^ 4572 = (2 : ZMod 103010909) ^ (2286 + 2286) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 2286 * (2 : ZMod 103010909) ^ 2286 := by rw [pow_add]
          _ = 41850054 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 103010909) ^ 9145 = 12442622 := by
        calc
          (2 : ZMod 103010909) ^ 9145 = (2 : ZMod 103010909) ^ (4572 + 4572 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 4572 * (2 : ZMod 103010909) ^ 4572) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 12442622 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 103010909) ^ 18290 = 38706060 := by
        calc
          (2 : ZMod 103010909) ^ 18290 = (2 : ZMod 103010909) ^ (9145 + 9145) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 9145 * (2 : ZMod 103010909) ^ 9145 := by rw [pow_add]
          _ = 38706060 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 103010909) ^ 36580 = 44576663 := by
        calc
          (2 : ZMod 103010909) ^ 36580 = (2 : ZMod 103010909) ^ (18290 + 18290) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 18290 * (2 : ZMod 103010909) ^ 18290 := by rw [pow_add]
          _ = 44576663 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 103010909) ^ 73161 = 92549317 := by
        calc
          (2 : ZMod 103010909) ^ 73161 = (2 : ZMod 103010909) ^ (36580 + 36580 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 36580 * (2 : ZMod 103010909) ^ 36580) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 92549317 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 103010909) ^ 146322 = 39809233 := by
        calc
          (2 : ZMod 103010909) ^ 146322 = (2 : ZMod 103010909) ^ (73161 + 73161) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 73161 * (2 : ZMod 103010909) ^ 73161 := by rw [pow_add]
          _ = 39809233 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 103010909) ^ 292644 = 97155974 := by
        calc
          (2 : ZMod 103010909) ^ 292644 = (2 : ZMod 103010909) ^ (146322 + 146322) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 146322 * (2 : ZMod 103010909) ^ 146322 := by rw [pow_add]
          _ = 97155974 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 103010909) ^ 585289 = 72059865 := by
        calc
          (2 : ZMod 103010909) ^ 585289 = (2 : ZMod 103010909) ^ (292644 + 292644 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 292644 * (2 : ZMod 103010909) ^ 292644) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 72059865 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 103010909) ^ 1170578 = 76633542 := by
        calc
          (2 : ZMod 103010909) ^ 1170578 = (2 : ZMod 103010909) ^ (585289 + 585289) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 585289 * (2 : ZMod 103010909) ^ 585289 := by rw [pow_add]
          _ = 76633542 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 103010909) ^ 2341157 = 80627976 := by
        calc
          (2 : ZMod 103010909) ^ 2341157 = (2 : ZMod 103010909) ^ (1170578 + 1170578 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 1170578 * (2 : ZMod 103010909) ^ 1170578) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 80627976 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 103010909) ^ 4682314 = 73542809 := by
        calc
          (2 : ZMod 103010909) ^ 4682314 = (2 : ZMod 103010909) ^ (2341157 + 2341157) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 2341157 * (2 : ZMod 103010909) ^ 2341157 := by rw [pow_add]
          _ = 73542809 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 103010909) ^ 9364628 = 37125443 := by
        calc
          (2 : ZMod 103010909) ^ 9364628 = (2 : ZMod 103010909) ^ (4682314 + 4682314) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 4682314 * (2 : ZMod 103010909) ^ 4682314 := by rw [pow_add]
          _ = 37125443 := by rw [factor_2_22]; decide
      change (2 : ZMod 103010909) ^ 9364628 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (2 : ZMod 103010909) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 103010909) ^ 3 = 8 := by
        calc
          (2 : ZMod 103010909) ^ 3 = (2 : ZMod 103010909) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 1 * (2 : ZMod 103010909) ^ 1) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 103010909) ^ 7 = 128 := by
        calc
          (2 : ZMod 103010909) ^ 7 = (2 : ZMod 103010909) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 3 * (2 : ZMod 103010909) ^ 3) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 103010909) ^ 15 = 32768 := by
        calc
          (2 : ZMod 103010909) ^ 15 = (2 : ZMod 103010909) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 7 * (2 : ZMod 103010909) ^ 7) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 103010909) ^ 30 = 43632734 := by
        calc
          (2 : ZMod 103010909) ^ 30 = (2 : ZMod 103010909) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 15 * (2 : ZMod 103010909) ^ 15 := by rw [pow_add]
          _ = 43632734 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 103010909) ^ 60 = 98591273 := by
        calc
          (2 : ZMod 103010909) ^ 60 = (2 : ZMod 103010909) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 30 * (2 : ZMod 103010909) ^ 30 := by rw [pow_add]
          _ = 98591273 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 103010909) ^ 120 = 47786098 := by
        calc
          (2 : ZMod 103010909) ^ 120 = (2 : ZMod 103010909) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 60 * (2 : ZMod 103010909) ^ 60 := by rw [pow_add]
          _ = 47786098 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 103010909) ^ 241 = 92059874 := by
        calc
          (2 : ZMod 103010909) ^ 241 = (2 : ZMod 103010909) ^ (120 + 120 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 120 * (2 : ZMod 103010909) ^ 120) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 92059874 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 103010909) ^ 483 = 43659577 := by
        calc
          (2 : ZMod 103010909) ^ 483 = (2 : ZMod 103010909) ^ (241 + 241 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 241 * (2 : ZMod 103010909) ^ 241) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 43659577 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 103010909) ^ 967 = 90885937 := by
        calc
          (2 : ZMod 103010909) ^ 967 = (2 : ZMod 103010909) ^ (483 + 483 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 483 * (2 : ZMod 103010909) ^ 483) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 90885937 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 103010909) ^ 1934 = 42915982 := by
        calc
          (2 : ZMod 103010909) ^ 1934 = (2 : ZMod 103010909) ^ (967 + 967) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 967 * (2 : ZMod 103010909) ^ 967 := by rw [pow_add]
          _ = 42915982 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 103010909) ^ 3869 = 47554008 := by
        calc
          (2 : ZMod 103010909) ^ 3869 = (2 : ZMod 103010909) ^ (1934 + 1934 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 1934 * (2 : ZMod 103010909) ^ 1934) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 47554008 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 103010909) ^ 7738 = 25157960 := by
        calc
          (2 : ZMod 103010909) ^ 7738 = (2 : ZMod 103010909) ^ (3869 + 3869) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 3869 * (2 : ZMod 103010909) ^ 3869 := by rw [pow_add]
          _ = 25157960 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 103010909) ^ 15476 = 27934712 := by
        calc
          (2 : ZMod 103010909) ^ 15476 = (2 : ZMod 103010909) ^ (7738 + 7738) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 7738 * (2 : ZMod 103010909) ^ 7738 := by rw [pow_add]
          _ = 27934712 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 103010909) ^ 30952 = 15560707 := by
        calc
          (2 : ZMod 103010909) ^ 30952 = (2 : ZMod 103010909) ^ (15476 + 15476) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 15476 * (2 : ZMod 103010909) ^ 15476 := by rw [pow_add]
          _ = 15560707 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 103010909) ^ 61905 = 27681622 := by
        calc
          (2 : ZMod 103010909) ^ 61905 = (2 : ZMod 103010909) ^ (30952 + 30952 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 30952 * (2 : ZMod 103010909) ^ 30952) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 27681622 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 103010909) ^ 123811 = 6497904 := by
        calc
          (2 : ZMod 103010909) ^ 123811 = (2 : ZMod 103010909) ^ (61905 + 61905 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 61905 * (2 : ZMod 103010909) ^ 61905) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 6497904 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 103010909) ^ 247622 = 26946842 := by
        calc
          (2 : ZMod 103010909) ^ 247622 = (2 : ZMod 103010909) ^ (123811 + 123811) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 123811 * (2 : ZMod 103010909) ^ 123811 := by rw [pow_add]
          _ = 26946842 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 103010909) ^ 495244 = 52348335 := by
        calc
          (2 : ZMod 103010909) ^ 495244 = (2 : ZMod 103010909) ^ (247622 + 247622) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 247622 * (2 : ZMod 103010909) ^ 247622 := by rw [pow_add]
          _ = 52348335 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 103010909) ^ 990489 = 14101269 := by
        calc
          (2 : ZMod 103010909) ^ 990489 = (2 : ZMod 103010909) ^ (495244 + 495244 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 495244 * (2 : ZMod 103010909) ^ 495244) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 14101269 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 103010909) ^ 1980979 = 36728056 := by
        calc
          (2 : ZMod 103010909) ^ 1980979 = (2 : ZMod 103010909) ^ (990489 + 990489 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 990489 * (2 : ZMod 103010909) ^ 990489) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 36728056 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 103010909) ^ 3961958 = 96838701 := by
        calc
          (2 : ZMod 103010909) ^ 3961958 = (2 : ZMod 103010909) ^ (1980979 + 1980979) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 1980979 * (2 : ZMod 103010909) ^ 1980979 := by rw [pow_add]
          _ = 96838701 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 103010909) ^ 7923916 = 39163430 := by
        calc
          (2 : ZMod 103010909) ^ 7923916 = (2 : ZMod 103010909) ^ (3961958 + 3961958) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 3961958 * (2 : ZMod 103010909) ^ 3961958 := by rw [pow_add]
          _ = 39163430 := by rw [factor_3_21]; decide
      change (2 : ZMod 103010909) ^ 7923916 ≠ 1
      rw [factor_3_22]
      decide
    ·
      have factor_4_0 : (2 : ZMod 103010909) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 103010909) ^ 3 = 8 := by
        calc
          (2 : ZMod 103010909) ^ 3 = (2 : ZMod 103010909) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 1 * (2 : ZMod 103010909) ^ 1) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 103010909) ^ 6 = 64 := by
        calc
          (2 : ZMod 103010909) ^ 6 = (2 : ZMod 103010909) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 3 * (2 : ZMod 103010909) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 103010909) ^ 12 = 4096 := by
        calc
          (2 : ZMod 103010909) ^ 12 = (2 : ZMod 103010909) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 6 * (2 : ZMod 103010909) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 103010909) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 103010909) ^ 25 = (2 : ZMod 103010909) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 12 * (2 : ZMod 103010909) ^ 12) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 103010909) ^ 50 = 45465343 := by
        calc
          (2 : ZMod 103010909) ^ 50 = (2 : ZMod 103010909) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 25 * (2 : ZMod 103010909) ^ 25 := by rw [pow_add]
          _ = 45465343 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 103010909) ^ 101 = 22176531 := by
        calc
          (2 : ZMod 103010909) ^ 101 = (2 : ZMod 103010909) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 50 * (2 : ZMod 103010909) ^ 50) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 22176531 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 103010909) ^ 203 = 68085056 := by
        calc
          (2 : ZMod 103010909) ^ 203 = (2 : ZMod 103010909) ^ (101 + 101 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 101 * (2 : ZMod 103010909) ^ 101) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 68085056 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 103010909) ^ 406 = 94643210 := by
        calc
          (2 : ZMod 103010909) ^ 406 = (2 : ZMod 103010909) ^ (203 + 203) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 203 * (2 : ZMod 103010909) ^ 203 := by rw [pow_add]
          _ = 94643210 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 103010909) ^ 813 = 35021878 := by
        calc
          (2 : ZMod 103010909) ^ 813 = (2 : ZMod 103010909) ^ (406 + 406 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 406 * (2 : ZMod 103010909) ^ 406) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 35021878 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 103010909) ^ 1626 = 102202049 := by
        calc
          (2 : ZMod 103010909) ^ 1626 = (2 : ZMod 103010909) ^ (813 + 813) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 813 * (2 : ZMod 103010909) ^ 813 := by rw [pow_add]
          _ = 102202049 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 103010909) ^ 3253 = 64433082 := by
        calc
          (2 : ZMod 103010909) ^ 3253 = (2 : ZMod 103010909) ^ (1626 + 1626 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 1626 * (2 : ZMod 103010909) ^ 1626) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 64433082 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 103010909) ^ 6506 = 70417155 := by
        calc
          (2 : ZMod 103010909) ^ 6506 = (2 : ZMod 103010909) ^ (3253 + 3253) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 3253 * (2 : ZMod 103010909) ^ 3253 := by rw [pow_add]
          _ = 70417155 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 103010909) ^ 13013 = 15318307 := by
        calc
          (2 : ZMod 103010909) ^ 13013 = (2 : ZMod 103010909) ^ (6506 + 6506 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = ((2 : ZMod 103010909) ^ 6506 * (2 : ZMod 103010909) ^ 6506) * (2 : ZMod 103010909) := by rw [pow_succ, pow_add]
          _ = 15318307 := by rw [factor_4_12]; decide
      have factor_4_14 : (2 : ZMod 103010909) ^ 26026 = 22527878 := by
        calc
          (2 : ZMod 103010909) ^ 26026 = (2 : ZMod 103010909) ^ (13013 + 13013) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 13013 * (2 : ZMod 103010909) ^ 13013 := by rw [pow_add]
          _ = 22527878 := by rw [factor_4_13]; decide
      have factor_4_15 : (2 : ZMod 103010909) ^ 52052 = 102670767 := by
        calc
          (2 : ZMod 103010909) ^ 52052 = (2 : ZMod 103010909) ^ (26026 + 26026) :=
            congrArg (fun n : ℕ => (2 : ZMod 103010909) ^ n) (by norm_num)
          _ = (2 : ZMod 103010909) ^ 26026 * (2 : ZMod 103010909) ^ 26026 := by rw [pow_add]
          _ = 102670767 := by rw [factor_4_14]; decide
      change (2 : ZMod 103010909) ^ 52052 ≠ 1
      rw [factor_4_15]
      decide

#print axioms prime_lucas_103010909

end TotientTailPeriodKiller
end Erdos249257
