import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_176320181 : Nat.Prime 176320181 := by
  apply lucas_primality 176320181 (2 : ZMod 176320181)
  ·
      have fermat_0 : (2 : ZMod 176320181) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 176320181) ^ 2 = 4 := by
        calc
          (2 : ZMod 176320181) ^ 2 = (2 : ZMod 176320181) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 1 * (2 : ZMod 176320181) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 176320181) ^ 5 = 32 := by
        calc
          (2 : ZMod 176320181) ^ 5 = (2 : ZMod 176320181) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 2 * (2 : ZMod 176320181) ^ 2) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 176320181) ^ 10 = 1024 := by
        calc
          (2 : ZMod 176320181) ^ 10 = (2 : ZMod 176320181) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 5 * (2 : ZMod 176320181) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 176320181) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 176320181) ^ 21 = (2 : ZMod 176320181) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 10 * (2 : ZMod 176320181) ^ 10) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 176320181) ^ 42 = 92236421 := by
        calc
          (2 : ZMod 176320181) ^ 42 = (2 : ZMod 176320181) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 21 * (2 : ZMod 176320181) ^ 21 := by rw [pow_add]
          _ = 92236421 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 176320181) ^ 84 = 12407745 := by
        calc
          (2 : ZMod 176320181) ^ 84 = (2 : ZMod 176320181) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 42 * (2 : ZMod 176320181) ^ 42 := by rw [pow_add]
          _ = 12407745 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 176320181) ^ 168 = 109466866 := by
        calc
          (2 : ZMod 176320181) ^ 168 = (2 : ZMod 176320181) ^ (84 + 84) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 84 * (2 : ZMod 176320181) ^ 84 := by rw [pow_add]
          _ = 109466866 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 176320181) ^ 336 = 15299415 := by
        calc
          (2 : ZMod 176320181) ^ 336 = (2 : ZMod 176320181) ^ (168 + 168) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 168 * (2 : ZMod 176320181) ^ 168 := by rw [pow_add]
          _ = 15299415 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 176320181) ^ 672 = 6257485 := by
        calc
          (2 : ZMod 176320181) ^ 672 = (2 : ZMod 176320181) ^ (336 + 336) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 336 * (2 : ZMod 176320181) ^ 336 := by rw [pow_add]
          _ = 6257485 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 176320181) ^ 1345 = 157619843 := by
        calc
          (2 : ZMod 176320181) ^ 1345 = (2 : ZMod 176320181) ^ (672 + 672 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 672 * (2 : ZMod 176320181) ^ 672) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 157619843 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 176320181) ^ 2690 = 126170066 := by
        calc
          (2 : ZMod 176320181) ^ 2690 = (2 : ZMod 176320181) ^ (1345 + 1345) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 1345 * (2 : ZMod 176320181) ^ 1345 := by rw [pow_add]
          _ = 126170066 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 176320181) ^ 5380 = 151606329 := by
        calc
          (2 : ZMod 176320181) ^ 5380 = (2 : ZMod 176320181) ^ (2690 + 2690) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 2690 * (2 : ZMod 176320181) ^ 2690 := by rw [pow_add]
          _ = 151606329 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 176320181) ^ 10761 = 102585093 := by
        calc
          (2 : ZMod 176320181) ^ 10761 = (2 : ZMod 176320181) ^ (5380 + 5380 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 5380 * (2 : ZMod 176320181) ^ 5380) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 102585093 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 176320181) ^ 21523 = 12003043 := by
        calc
          (2 : ZMod 176320181) ^ 21523 = (2 : ZMod 176320181) ^ (10761 + 10761 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 10761 * (2 : ZMod 176320181) ^ 10761) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 12003043 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 176320181) ^ 43046 = 58162939 := by
        calc
          (2 : ZMod 176320181) ^ 43046 = (2 : ZMod 176320181) ^ (21523 + 21523) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 21523 * (2 : ZMod 176320181) ^ 21523 := by rw [pow_add]
          _ = 58162939 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 176320181) ^ 86093 = 161124073 := by
        calc
          (2 : ZMod 176320181) ^ 86093 = (2 : ZMod 176320181) ^ (43046 + 43046 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 43046 * (2 : ZMod 176320181) ^ 43046) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 161124073 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 176320181) ^ 172187 = 12193883 := by
        calc
          (2 : ZMod 176320181) ^ 172187 = (2 : ZMod 176320181) ^ (86093 + 86093 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 86093 * (2 : ZMod 176320181) ^ 86093) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 12193883 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 176320181) ^ 344375 = 124280959 := by
        calc
          (2 : ZMod 176320181) ^ 344375 = (2 : ZMod 176320181) ^ (172187 + 172187 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 172187 * (2 : ZMod 176320181) ^ 172187) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 124280959 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 176320181) ^ 688750 = 124808004 := by
        calc
          (2 : ZMod 176320181) ^ 688750 = (2 : ZMod 176320181) ^ (344375 + 344375) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 344375 * (2 : ZMod 176320181) ^ 344375 := by rw [pow_add]
          _ = 124808004 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 176320181) ^ 1377501 = 174053596 := by
        calc
          (2 : ZMod 176320181) ^ 1377501 = (2 : ZMod 176320181) ^ (688750 + 688750 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 688750 * (2 : ZMod 176320181) ^ 688750) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 174053596 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 176320181) ^ 2755002 = 142768609 := by
        calc
          (2 : ZMod 176320181) ^ 2755002 = (2 : ZMod 176320181) ^ (1377501 + 1377501) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 1377501 * (2 : ZMod 176320181) ^ 1377501 := by rw [pow_add]
          _ = 142768609 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 176320181) ^ 5510005 = 150250382 := by
        calc
          (2 : ZMod 176320181) ^ 5510005 = (2 : ZMod 176320181) ^ (2755002 + 2755002 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 2755002 * (2 : ZMod 176320181) ^ 2755002) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 150250382 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 176320181) ^ 11020011 = 166694969 := by
        calc
          (2 : ZMod 176320181) ^ 11020011 = (2 : ZMod 176320181) ^ (5510005 + 5510005 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 5510005 * (2 : ZMod 176320181) ^ 5510005) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 166694969 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 176320181) ^ 22040022 = 88061390 := by
        calc
          (2 : ZMod 176320181) ^ 22040022 = (2 : ZMod 176320181) ^ (11020011 + 11020011) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 11020011 * (2 : ZMod 176320181) ^ 11020011 := by rw [pow_add]
          _ = 88061390 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 176320181) ^ 44080045 = 197400 := by
        calc
          (2 : ZMod 176320181) ^ 44080045 = (2 : ZMod 176320181) ^ (22040022 + 22040022 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 22040022 * (2 : ZMod 176320181) ^ 22040022) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 197400 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 176320181) ^ 88160090 = 176320180 := by
        calc
          (2 : ZMod 176320181) ^ 88160090 = (2 : ZMod 176320181) ^ (44080045 + 44080045) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 44080045 * (2 : ZMod 176320181) ^ 44080045 := by rw [pow_add]
          _ = 176320180 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 176320181) ^ 176320180 = 1 := by
        calc
          (2 : ZMod 176320181) ^ 176320180 = (2 : ZMod 176320181) ^ (88160090 + 88160090) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 88160090 * (2 : ZMod 176320181) ^ 88160090 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (2069, 1), (4261, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (2069, 1), (4261, 1)] : List FactorBlock).map factorBlockValue).prod = 176320181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 176320181) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 176320181) ^ 2 = 4 := by
        calc
          (2 : ZMod 176320181) ^ 2 = (2 : ZMod 176320181) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 1 * (2 : ZMod 176320181) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 176320181) ^ 5 = 32 := by
        calc
          (2 : ZMod 176320181) ^ 5 = (2 : ZMod 176320181) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 2 * (2 : ZMod 176320181) ^ 2) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 176320181) ^ 10 = 1024 := by
        calc
          (2 : ZMod 176320181) ^ 10 = (2 : ZMod 176320181) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 5 * (2 : ZMod 176320181) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 176320181) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 176320181) ^ 21 = (2 : ZMod 176320181) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 10 * (2 : ZMod 176320181) ^ 10) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 176320181) ^ 42 = 92236421 := by
        calc
          (2 : ZMod 176320181) ^ 42 = (2 : ZMod 176320181) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 21 * (2 : ZMod 176320181) ^ 21 := by rw [pow_add]
          _ = 92236421 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 176320181) ^ 84 = 12407745 := by
        calc
          (2 : ZMod 176320181) ^ 84 = (2 : ZMod 176320181) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 42 * (2 : ZMod 176320181) ^ 42 := by rw [pow_add]
          _ = 12407745 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 176320181) ^ 168 = 109466866 := by
        calc
          (2 : ZMod 176320181) ^ 168 = (2 : ZMod 176320181) ^ (84 + 84) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 84 * (2 : ZMod 176320181) ^ 84 := by rw [pow_add]
          _ = 109466866 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 176320181) ^ 336 = 15299415 := by
        calc
          (2 : ZMod 176320181) ^ 336 = (2 : ZMod 176320181) ^ (168 + 168) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 168 * (2 : ZMod 176320181) ^ 168 := by rw [pow_add]
          _ = 15299415 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 176320181) ^ 672 = 6257485 := by
        calc
          (2 : ZMod 176320181) ^ 672 = (2 : ZMod 176320181) ^ (336 + 336) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 336 * (2 : ZMod 176320181) ^ 336 := by rw [pow_add]
          _ = 6257485 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 176320181) ^ 1345 = 157619843 := by
        calc
          (2 : ZMod 176320181) ^ 1345 = (2 : ZMod 176320181) ^ (672 + 672 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 672 * (2 : ZMod 176320181) ^ 672) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 157619843 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 176320181) ^ 2690 = 126170066 := by
        calc
          (2 : ZMod 176320181) ^ 2690 = (2 : ZMod 176320181) ^ (1345 + 1345) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 1345 * (2 : ZMod 176320181) ^ 1345 := by rw [pow_add]
          _ = 126170066 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 176320181) ^ 5380 = 151606329 := by
        calc
          (2 : ZMod 176320181) ^ 5380 = (2 : ZMod 176320181) ^ (2690 + 2690) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 2690 * (2 : ZMod 176320181) ^ 2690 := by rw [pow_add]
          _ = 151606329 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 176320181) ^ 10761 = 102585093 := by
        calc
          (2 : ZMod 176320181) ^ 10761 = (2 : ZMod 176320181) ^ (5380 + 5380 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 5380 * (2 : ZMod 176320181) ^ 5380) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 102585093 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 176320181) ^ 21523 = 12003043 := by
        calc
          (2 : ZMod 176320181) ^ 21523 = (2 : ZMod 176320181) ^ (10761 + 10761 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 10761 * (2 : ZMod 176320181) ^ 10761) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 12003043 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 176320181) ^ 43046 = 58162939 := by
        calc
          (2 : ZMod 176320181) ^ 43046 = (2 : ZMod 176320181) ^ (21523 + 21523) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 21523 * (2 : ZMod 176320181) ^ 21523 := by rw [pow_add]
          _ = 58162939 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 176320181) ^ 86093 = 161124073 := by
        calc
          (2 : ZMod 176320181) ^ 86093 = (2 : ZMod 176320181) ^ (43046 + 43046 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 43046 * (2 : ZMod 176320181) ^ 43046) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 161124073 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 176320181) ^ 172187 = 12193883 := by
        calc
          (2 : ZMod 176320181) ^ 172187 = (2 : ZMod 176320181) ^ (86093 + 86093 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 86093 * (2 : ZMod 176320181) ^ 86093) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 12193883 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 176320181) ^ 344375 = 124280959 := by
        calc
          (2 : ZMod 176320181) ^ 344375 = (2 : ZMod 176320181) ^ (172187 + 172187 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 172187 * (2 : ZMod 176320181) ^ 172187) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 124280959 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 176320181) ^ 688750 = 124808004 := by
        calc
          (2 : ZMod 176320181) ^ 688750 = (2 : ZMod 176320181) ^ (344375 + 344375) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 344375 * (2 : ZMod 176320181) ^ 344375 := by rw [pow_add]
          _ = 124808004 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 176320181) ^ 1377501 = 174053596 := by
        calc
          (2 : ZMod 176320181) ^ 1377501 = (2 : ZMod 176320181) ^ (688750 + 688750 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 688750 * (2 : ZMod 176320181) ^ 688750) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 174053596 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 176320181) ^ 2755002 = 142768609 := by
        calc
          (2 : ZMod 176320181) ^ 2755002 = (2 : ZMod 176320181) ^ (1377501 + 1377501) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 1377501 * (2 : ZMod 176320181) ^ 1377501 := by rw [pow_add]
          _ = 142768609 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 176320181) ^ 5510005 = 150250382 := by
        calc
          (2 : ZMod 176320181) ^ 5510005 = (2 : ZMod 176320181) ^ (2755002 + 2755002 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 2755002 * (2 : ZMod 176320181) ^ 2755002) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 150250382 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 176320181) ^ 11020011 = 166694969 := by
        calc
          (2 : ZMod 176320181) ^ 11020011 = (2 : ZMod 176320181) ^ (5510005 + 5510005 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 5510005 * (2 : ZMod 176320181) ^ 5510005) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 166694969 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 176320181) ^ 22040022 = 88061390 := by
        calc
          (2 : ZMod 176320181) ^ 22040022 = (2 : ZMod 176320181) ^ (11020011 + 11020011) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 11020011 * (2 : ZMod 176320181) ^ 11020011 := by rw [pow_add]
          _ = 88061390 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 176320181) ^ 44080045 = 197400 := by
        calc
          (2 : ZMod 176320181) ^ 44080045 = (2 : ZMod 176320181) ^ (22040022 + 22040022 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 22040022 * (2 : ZMod 176320181) ^ 22040022) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 197400 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 176320181) ^ 88160090 = 176320180 := by
        calc
          (2 : ZMod 176320181) ^ 88160090 = (2 : ZMod 176320181) ^ (44080045 + 44080045) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 44080045 * (2 : ZMod 176320181) ^ 44080045 := by rw [pow_add]
          _ = 176320180 := by rw [factor_0_25]; decide
      change (2 : ZMod 176320181) ^ 88160090 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (2 : ZMod 176320181) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 176320181) ^ 2 = 4 := by
        calc
          (2 : ZMod 176320181) ^ 2 = (2 : ZMod 176320181) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 1 * (2 : ZMod 176320181) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 176320181) ^ 4 = 16 := by
        calc
          (2 : ZMod 176320181) ^ 4 = (2 : ZMod 176320181) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 2 * (2 : ZMod 176320181) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 176320181) ^ 8 = 256 := by
        calc
          (2 : ZMod 176320181) ^ 8 = (2 : ZMod 176320181) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 4 * (2 : ZMod 176320181) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 176320181) ^ 16 = 65536 := by
        calc
          (2 : ZMod 176320181) ^ 16 = (2 : ZMod 176320181) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 8 * (2 : ZMod 176320181) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 176320181) ^ 33 = 126565904 := by
        calc
          (2 : ZMod 176320181) ^ 33 = (2 : ZMod 176320181) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 16 * (2 : ZMod 176320181) ^ 16) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 126565904 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 176320181) ^ 67 = 161042655 := by
        calc
          (2 : ZMod 176320181) ^ 67 = (2 : ZMod 176320181) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 33 * (2 : ZMod 176320181) ^ 33) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 161042655 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 176320181) ^ 134 = 19003012 := by
        calc
          (2 : ZMod 176320181) ^ 134 = (2 : ZMod 176320181) ^ (67 + 67) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 67 * (2 : ZMod 176320181) ^ 67 := by rw [pow_add]
          _ = 19003012 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 176320181) ^ 269 = 134026387 := by
        calc
          (2 : ZMod 176320181) ^ 269 = (2 : ZMod 176320181) ^ (134 + 134 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 134 * (2 : ZMod 176320181) ^ 134) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 134026387 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 176320181) ^ 538 = 124752875 := by
        calc
          (2 : ZMod 176320181) ^ 538 = (2 : ZMod 176320181) ^ (269 + 269) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 269 * (2 : ZMod 176320181) ^ 269 := by rw [pow_add]
          _ = 124752875 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 176320181) ^ 1076 = 132731656 := by
        calc
          (2 : ZMod 176320181) ^ 1076 = (2 : ZMod 176320181) ^ (538 + 538) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 538 * (2 : ZMod 176320181) ^ 538 := by rw [pow_add]
          _ = 132731656 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 176320181) ^ 2152 = 66568224 := by
        calc
          (2 : ZMod 176320181) ^ 2152 = (2 : ZMod 176320181) ^ (1076 + 1076) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 1076 * (2 : ZMod 176320181) ^ 1076 := by rw [pow_add]
          _ = 66568224 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 176320181) ^ 4304 = 111651315 := by
        calc
          (2 : ZMod 176320181) ^ 4304 = (2 : ZMod 176320181) ^ (2152 + 2152) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 2152 * (2 : ZMod 176320181) ^ 2152 := by rw [pow_add]
          _ = 111651315 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 176320181) ^ 8609 = 53810296 := by
        calc
          (2 : ZMod 176320181) ^ 8609 = (2 : ZMod 176320181) ^ (4304 + 4304 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 4304 * (2 : ZMod 176320181) ^ 4304) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 53810296 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 176320181) ^ 17218 = 134887335 := by
        calc
          (2 : ZMod 176320181) ^ 17218 = (2 : ZMod 176320181) ^ (8609 + 8609) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 8609 * (2 : ZMod 176320181) ^ 8609 := by rw [pow_add]
          _ = 134887335 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 176320181) ^ 34437 = 55311141 := by
        calc
          (2 : ZMod 176320181) ^ 34437 = (2 : ZMod 176320181) ^ (17218 + 17218 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 17218 * (2 : ZMod 176320181) ^ 17218) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 55311141 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 176320181) ^ 68875 = 53680586 := by
        calc
          (2 : ZMod 176320181) ^ 68875 = (2 : ZMod 176320181) ^ (34437 + 34437 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 34437 * (2 : ZMod 176320181) ^ 34437) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 53680586 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 176320181) ^ 137750 = 10895690 := by
        calc
          (2 : ZMod 176320181) ^ 137750 = (2 : ZMod 176320181) ^ (68875 + 68875) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 68875 * (2 : ZMod 176320181) ^ 68875 := by rw [pow_add]
          _ = 10895690 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 176320181) ^ 275500 = 35349162 := by
        calc
          (2 : ZMod 176320181) ^ 275500 = (2 : ZMod 176320181) ^ (137750 + 137750) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 137750 * (2 : ZMod 176320181) ^ 137750 := by rw [pow_add]
          _ = 35349162 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 176320181) ^ 551000 = 116013706 := by
        calc
          (2 : ZMod 176320181) ^ 551000 = (2 : ZMod 176320181) ^ (275500 + 275500) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 275500 * (2 : ZMod 176320181) ^ 275500 := by rw [pow_add]
          _ = 116013706 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 176320181) ^ 1102001 = 137452820 := by
        calc
          (2 : ZMod 176320181) ^ 1102001 = (2 : ZMod 176320181) ^ (551000 + 551000 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 551000 * (2 : ZMod 176320181) ^ 551000) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 137452820 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 176320181) ^ 2204002 = 112337046 := by
        calc
          (2 : ZMod 176320181) ^ 2204002 = (2 : ZMod 176320181) ^ (1102001 + 1102001) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 1102001 * (2 : ZMod 176320181) ^ 1102001 := by rw [pow_add]
          _ = 112337046 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 176320181) ^ 4408004 = 106249681 := by
        calc
          (2 : ZMod 176320181) ^ 4408004 = (2 : ZMod 176320181) ^ (2204002 + 2204002) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 2204002 * (2 : ZMod 176320181) ^ 2204002 := by rw [pow_add]
          _ = 106249681 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 176320181) ^ 8816009 = 174998404 := by
        calc
          (2 : ZMod 176320181) ^ 8816009 = (2 : ZMod 176320181) ^ (4408004 + 4408004 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 4408004 * (2 : ZMod 176320181) ^ 4408004) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 174998404 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 176320181) ^ 17632018 = 114084381 := by
        calc
          (2 : ZMod 176320181) ^ 17632018 = (2 : ZMod 176320181) ^ (8816009 + 8816009) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 8816009 * (2 : ZMod 176320181) ^ 8816009 := by rw [pow_add]
          _ = 114084381 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 176320181) ^ 35264036 = 91781867 := by
        calc
          (2 : ZMod 176320181) ^ 35264036 = (2 : ZMod 176320181) ^ (17632018 + 17632018) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 17632018 * (2 : ZMod 176320181) ^ 17632018 := by rw [pow_add]
          _ = 91781867 := by rw [factor_1_24]; decide
      change (2 : ZMod 176320181) ^ 35264036 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (2 : ZMod 176320181) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 176320181) ^ 2 = 4 := by
        calc
          (2 : ZMod 176320181) ^ 2 = (2 : ZMod 176320181) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 1 * (2 : ZMod 176320181) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 176320181) ^ 5 = 32 := by
        calc
          (2 : ZMod 176320181) ^ 5 = (2 : ZMod 176320181) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 2 * (2 : ZMod 176320181) ^ 2) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 176320181) ^ 10 = 1024 := by
        calc
          (2 : ZMod 176320181) ^ 10 = (2 : ZMod 176320181) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 5 * (2 : ZMod 176320181) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 176320181) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 176320181) ^ 20 = (2 : ZMod 176320181) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 10 * (2 : ZMod 176320181) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 176320181) ^ 41 = 134278301 := by
        calc
          (2 : ZMod 176320181) ^ 41 = (2 : ZMod 176320181) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 20 * (2 : ZMod 176320181) ^ 20) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 134278301 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 176320181) ^ 83 = 94363963 := by
        calc
          (2 : ZMod 176320181) ^ 83 = (2 : ZMod 176320181) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 41 * (2 : ZMod 176320181) ^ 41) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 94363963 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 176320181) ^ 166 = 115526807 := by
        calc
          (2 : ZMod 176320181) ^ 166 = (2 : ZMod 176320181) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 83 * (2 : ZMod 176320181) ^ 83 := by rw [pow_add]
          _ = 115526807 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 176320181) ^ 332 = 56056270 := by
        calc
          (2 : ZMod 176320181) ^ 332 = (2 : ZMod 176320181) ^ (166 + 166) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 166 * (2 : ZMod 176320181) ^ 166 := by rw [pow_add]
          _ = 56056270 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 176320181) ^ 665 = 97851487 := by
        calc
          (2 : ZMod 176320181) ^ 665 = (2 : ZMod 176320181) ^ (332 + 332 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 332 * (2 : ZMod 176320181) ^ 332) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 97851487 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 176320181) ^ 1331 = 12848364 := by
        calc
          (2 : ZMod 176320181) ^ 1331 = (2 : ZMod 176320181) ^ (665 + 665 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 665 * (2 : ZMod 176320181) ^ 665) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 12848364 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 176320181) ^ 2663 = 141789225 := by
        calc
          (2 : ZMod 176320181) ^ 2663 = (2 : ZMod 176320181) ^ (1331 + 1331 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 1331 * (2 : ZMod 176320181) ^ 1331) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 141789225 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 176320181) ^ 5326 = 10879173 := by
        calc
          (2 : ZMod 176320181) ^ 5326 = (2 : ZMod 176320181) ^ (2663 + 2663) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 2663 * (2 : ZMod 176320181) ^ 2663 := by rw [pow_add]
          _ = 10879173 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 176320181) ^ 10652 = 73106231 := by
        calc
          (2 : ZMod 176320181) ^ 10652 = (2 : ZMod 176320181) ^ (5326 + 5326) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 5326 * (2 : ZMod 176320181) ^ 5326 := by rw [pow_add]
          _ = 73106231 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 176320181) ^ 21305 = 87064555 := by
        calc
          (2 : ZMod 176320181) ^ 21305 = (2 : ZMod 176320181) ^ (10652 + 10652 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 10652 * (2 : ZMod 176320181) ^ 10652) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 87064555 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 176320181) ^ 42610 = 118799829 := by
        calc
          (2 : ZMod 176320181) ^ 42610 = (2 : ZMod 176320181) ^ (21305 + 21305) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 21305 * (2 : ZMod 176320181) ^ 21305 := by rw [pow_add]
          _ = 118799829 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 176320181) ^ 85220 = 1797729 := by
        calc
          (2 : ZMod 176320181) ^ 85220 = (2 : ZMod 176320181) ^ (42610 + 42610) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 42610 * (2 : ZMod 176320181) ^ 42610 := by rw [pow_add]
          _ = 1797729 := by rw [factor_2_15]; decide
      change (2 : ZMod 176320181) ^ 85220 ≠ 1
      rw [factor_2_16]
      decide
    ·
      have factor_3_0 : (2 : ZMod 176320181) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 176320181) ^ 2 = 4 := by
        calc
          (2 : ZMod 176320181) ^ 2 = (2 : ZMod 176320181) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 1 * (2 : ZMod 176320181) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 176320181) ^ 5 = 32 := by
        calc
          (2 : ZMod 176320181) ^ 5 = (2 : ZMod 176320181) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 2 * (2 : ZMod 176320181) ^ 2) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 176320181) ^ 10 = 1024 := by
        calc
          (2 : ZMod 176320181) ^ 10 = (2 : ZMod 176320181) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 5 * (2 : ZMod 176320181) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 176320181) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 176320181) ^ 20 = (2 : ZMod 176320181) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 10 * (2 : ZMod 176320181) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 176320181) ^ 40 = 155299241 := by
        calc
          (2 : ZMod 176320181) ^ 40 = (2 : ZMod 176320181) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 20 * (2 : ZMod 176320181) ^ 20 := by rw [pow_add]
          _ = 155299241 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 176320181) ^ 80 = 33835518 := by
        calc
          (2 : ZMod 176320181) ^ 80 = (2 : ZMod 176320181) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 40 * (2 : ZMod 176320181) ^ 40 := by rw [pow_add]
          _ = 33835518 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 176320181) ^ 161 = 31160241 := by
        calc
          (2 : ZMod 176320181) ^ 161 = (2 : ZMod 176320181) ^ (80 + 80 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 80 * (2 : ZMod 176320181) ^ 80) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 31160241 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 176320181) ^ 323 = 58653295 := by
        calc
          (2 : ZMod 176320181) ^ 323 = (2 : ZMod 176320181) ^ (161 + 161 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 161 * (2 : ZMod 176320181) ^ 161) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 58653295 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 176320181) ^ 646 = 43799418 := by
        calc
          (2 : ZMod 176320181) ^ 646 = (2 : ZMod 176320181) ^ (323 + 323) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 323 * (2 : ZMod 176320181) ^ 323 := by rw [pow_add]
          _ = 43799418 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 176320181) ^ 1293 = 115505320 := by
        calc
          (2 : ZMod 176320181) ^ 1293 = (2 : ZMod 176320181) ^ (646 + 646 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 646 * (2 : ZMod 176320181) ^ 646) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 115505320 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 176320181) ^ 2586 = 163439476 := by
        calc
          (2 : ZMod 176320181) ^ 2586 = (2 : ZMod 176320181) ^ (1293 + 1293) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 1293 * (2 : ZMod 176320181) ^ 1293 := by rw [pow_add]
          _ = 163439476 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 176320181) ^ 5172 = 31620912 := by
        calc
          (2 : ZMod 176320181) ^ 5172 = (2 : ZMod 176320181) ^ (2586 + 2586) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 2586 * (2 : ZMod 176320181) ^ 2586 := by rw [pow_add]
          _ = 31620912 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 176320181) ^ 10345 = 78422485 := by
        calc
          (2 : ZMod 176320181) ^ 10345 = (2 : ZMod 176320181) ^ (5172 + 5172 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = ((2 : ZMod 176320181) ^ 5172 * (2 : ZMod 176320181) ^ 5172) * (2 : ZMod 176320181) := by rw [pow_succ, pow_add]
          _ = 78422485 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 176320181) ^ 20690 = 155136129 := by
        calc
          (2 : ZMod 176320181) ^ 20690 = (2 : ZMod 176320181) ^ (10345 + 10345) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 10345 * (2 : ZMod 176320181) ^ 10345 := by rw [pow_add]
          _ = 155136129 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 176320181) ^ 41380 = 105663839 := by
        calc
          (2 : ZMod 176320181) ^ 41380 = (2 : ZMod 176320181) ^ (20690 + 20690) :=
            congrArg (fun n : ℕ => (2 : ZMod 176320181) ^ n) (by norm_num)
          _ = (2 : ZMod 176320181) ^ 20690 * (2 : ZMod 176320181) ^ 20690 := by rw [pow_add]
          _ = 105663839 := by rw [factor_3_14]; decide
      change (2 : ZMod 176320181) ^ 41380 ≠ 1
      rw [factor_3_15]
      decide

#print axioms prime_lucas_176320181

end TotientTailPeriodKiller
end Erdos249257
