import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_608994259 : Nat.Prime 608994259 := by
  apply lucas_primality 608994259 (2 : ZMod 608994259)
  ·
      have fermat_0 : (2 : ZMod 608994259) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 608994259) ^ 2 = 4 := by
        calc
          (2 : ZMod 608994259) ^ 2 = (2 : ZMod 608994259) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 1 * (2 : ZMod 608994259) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 608994259) ^ 4 = 16 := by
        calc
          (2 : ZMod 608994259) ^ 4 = (2 : ZMod 608994259) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 2 * (2 : ZMod 608994259) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 608994259) ^ 9 = 512 := by
        calc
          (2 : ZMod 608994259) ^ 9 = (2 : ZMod 608994259) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 4 * (2 : ZMod 608994259) ^ 4) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 608994259) ^ 18 = 262144 := by
        calc
          (2 : ZMod 608994259) ^ 18 = (2 : ZMod 608994259) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 9 * (2 : ZMod 608994259) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 608994259) ^ 36 = 512119728 := by
        calc
          (2 : ZMod 608994259) ^ 36 = (2 : ZMod 608994259) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 18 * (2 : ZMod 608994259) ^ 18 := by rw [pow_add]
          _ = 512119728 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 608994259) ^ 72 = 145968881 := by
        calc
          (2 : ZMod 608994259) ^ 72 = (2 : ZMod 608994259) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 36 * (2 : ZMod 608994259) ^ 36 := by rw [pow_add]
          _ = 145968881 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 608994259) ^ 145 = 217121127 := by
        calc
          (2 : ZMod 608994259) ^ 145 = (2 : ZMod 608994259) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 72 * (2 : ZMod 608994259) ^ 72) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 217121127 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 608994259) ^ 290 = 177319662 := by
        calc
          (2 : ZMod 608994259) ^ 290 = (2 : ZMod 608994259) ^ (145 + 145) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 145 * (2 : ZMod 608994259) ^ 145 := by rw [pow_add]
          _ = 177319662 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 608994259) ^ 580 = 385573641 := by
        calc
          (2 : ZMod 608994259) ^ 580 = (2 : ZMod 608994259) ^ (290 + 290) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 290 * (2 : ZMod 608994259) ^ 290 := by rw [pow_add]
          _ = 385573641 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 608994259) ^ 1161 = 539651360 := by
        calc
          (2 : ZMod 608994259) ^ 1161 = (2 : ZMod 608994259) ^ (580 + 580 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 580 * (2 : ZMod 608994259) ^ 580) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 539651360 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 608994259) ^ 2323 = 296904507 := by
        calc
          (2 : ZMod 608994259) ^ 2323 = (2 : ZMod 608994259) ^ (1161 + 1161 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 1161 * (2 : ZMod 608994259) ^ 1161) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 296904507 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 608994259) ^ 4646 = 63124872 := by
        calc
          (2 : ZMod 608994259) ^ 4646 = (2 : ZMod 608994259) ^ (2323 + 2323) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 2323 * (2 : ZMod 608994259) ^ 2323 := by rw [pow_add]
          _ = 63124872 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 608994259) ^ 9292 = 153320908 := by
        calc
          (2 : ZMod 608994259) ^ 9292 = (2 : ZMod 608994259) ^ (4646 + 4646) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 4646 * (2 : ZMod 608994259) ^ 4646 := by rw [pow_add]
          _ = 153320908 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 608994259) ^ 18585 = 49396810 := by
        calc
          (2 : ZMod 608994259) ^ 18585 = (2 : ZMod 608994259) ^ (9292 + 9292 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 9292 * (2 : ZMod 608994259) ^ 9292) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 49396810 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 608994259) ^ 37170 = 329520239 := by
        calc
          (2 : ZMod 608994259) ^ 37170 = (2 : ZMod 608994259) ^ (18585 + 18585) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 18585 * (2 : ZMod 608994259) ^ 18585 := by rw [pow_add]
          _ = 329520239 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 608994259) ^ 74340 = 444078935 := by
        calc
          (2 : ZMod 608994259) ^ 74340 = (2 : ZMod 608994259) ^ (37170 + 37170) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 37170 * (2 : ZMod 608994259) ^ 37170 := by rw [pow_add]
          _ = 444078935 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 608994259) ^ 148680 = 439240638 := by
        calc
          (2 : ZMod 608994259) ^ 148680 = (2 : ZMod 608994259) ^ (74340 + 74340) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 74340 * (2 : ZMod 608994259) ^ 74340 := by rw [pow_add]
          _ = 439240638 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 608994259) ^ 297360 = 152319599 := by
        calc
          (2 : ZMod 608994259) ^ 297360 = (2 : ZMod 608994259) ^ (148680 + 148680) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 148680 * (2 : ZMod 608994259) ^ 148680 := by rw [pow_add]
          _ = 152319599 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 608994259) ^ 594720 = 364221307 := by
        calc
          (2 : ZMod 608994259) ^ 594720 = (2 : ZMod 608994259) ^ (297360 + 297360) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 297360 * (2 : ZMod 608994259) ^ 297360 := by rw [pow_add]
          _ = 364221307 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 608994259) ^ 1189441 = 214522744 := by
        calc
          (2 : ZMod 608994259) ^ 1189441 = (2 : ZMod 608994259) ^ (594720 + 594720 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 594720 * (2 : ZMod 608994259) ^ 594720) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 214522744 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 608994259) ^ 2378883 = 563479486 := by
        calc
          (2 : ZMod 608994259) ^ 2378883 = (2 : ZMod 608994259) ^ (1189441 + 1189441 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 1189441 * (2 : ZMod 608994259) ^ 1189441) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 563479486 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 608994259) ^ 4757767 = 210400588 := by
        calc
          (2 : ZMod 608994259) ^ 4757767 = (2 : ZMod 608994259) ^ (2378883 + 2378883 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 2378883 * (2 : ZMod 608994259) ^ 2378883) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 210400588 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 608994259) ^ 9515535 = 537656826 := by
        calc
          (2 : ZMod 608994259) ^ 9515535 = (2 : ZMod 608994259) ^ (4757767 + 4757767 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 4757767 * (2 : ZMod 608994259) ^ 4757767) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 537656826 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 608994259) ^ 19031070 = 489397457 := by
        calc
          (2 : ZMod 608994259) ^ 19031070 = (2 : ZMod 608994259) ^ (9515535 + 9515535) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 9515535 * (2 : ZMod 608994259) ^ 9515535 := by rw [pow_add]
          _ = 489397457 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 608994259) ^ 38062141 = 348983733 := by
        calc
          (2 : ZMod 608994259) ^ 38062141 = (2 : ZMod 608994259) ^ (19031070 + 19031070 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 19031070 * (2 : ZMod 608994259) ^ 19031070) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 348983733 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 608994259) ^ 76124282 = 264828592 := by
        calc
          (2 : ZMod 608994259) ^ 76124282 = (2 : ZMod 608994259) ^ (38062141 + 38062141) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 38062141 * (2 : ZMod 608994259) ^ 38062141 := by rw [pow_add]
          _ = 264828592 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 608994259) ^ 152248564 = 573922191 := by
        calc
          (2 : ZMod 608994259) ^ 152248564 = (2 : ZMod 608994259) ^ (76124282 + 76124282) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 76124282 * (2 : ZMod 608994259) ^ 76124282 := by rw [pow_add]
          _ = 573922191 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 608994259) ^ 304497129 = 608994258 := by
        calc
          (2 : ZMod 608994259) ^ 304497129 = (2 : ZMod 608994259) ^ (152248564 + 152248564 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 152248564 * (2 : ZMod 608994259) ^ 152248564) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 608994258 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 608994259) ^ 608994258 = 1 := by
        calc
          (2 : ZMod 608994259) ^ 608994258 = (2 : ZMod 608994259) ^ (304497129 + 304497129) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 304497129 * (2 : ZMod 608994259) ^ 304497129 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (29, 1), (3499967, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (29, 1), (3499967, 1)] : List FactorBlock).map factorBlockValue).prod = 608994259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 608994259) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 608994259) ^ 2 = 4 := by
        calc
          (2 : ZMod 608994259) ^ 2 = (2 : ZMod 608994259) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 1 * (2 : ZMod 608994259) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 608994259) ^ 4 = 16 := by
        calc
          (2 : ZMod 608994259) ^ 4 = (2 : ZMod 608994259) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 2 * (2 : ZMod 608994259) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 608994259) ^ 9 = 512 := by
        calc
          (2 : ZMod 608994259) ^ 9 = (2 : ZMod 608994259) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 4 * (2 : ZMod 608994259) ^ 4) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 608994259) ^ 18 = 262144 := by
        calc
          (2 : ZMod 608994259) ^ 18 = (2 : ZMod 608994259) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 9 * (2 : ZMod 608994259) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 608994259) ^ 36 = 512119728 := by
        calc
          (2 : ZMod 608994259) ^ 36 = (2 : ZMod 608994259) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 18 * (2 : ZMod 608994259) ^ 18 := by rw [pow_add]
          _ = 512119728 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 608994259) ^ 72 = 145968881 := by
        calc
          (2 : ZMod 608994259) ^ 72 = (2 : ZMod 608994259) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 36 * (2 : ZMod 608994259) ^ 36 := by rw [pow_add]
          _ = 145968881 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 608994259) ^ 145 = 217121127 := by
        calc
          (2 : ZMod 608994259) ^ 145 = (2 : ZMod 608994259) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 72 * (2 : ZMod 608994259) ^ 72) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 217121127 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 608994259) ^ 290 = 177319662 := by
        calc
          (2 : ZMod 608994259) ^ 290 = (2 : ZMod 608994259) ^ (145 + 145) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 145 * (2 : ZMod 608994259) ^ 145 := by rw [pow_add]
          _ = 177319662 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 608994259) ^ 580 = 385573641 := by
        calc
          (2 : ZMod 608994259) ^ 580 = (2 : ZMod 608994259) ^ (290 + 290) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 290 * (2 : ZMod 608994259) ^ 290 := by rw [pow_add]
          _ = 385573641 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 608994259) ^ 1161 = 539651360 := by
        calc
          (2 : ZMod 608994259) ^ 1161 = (2 : ZMod 608994259) ^ (580 + 580 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 580 * (2 : ZMod 608994259) ^ 580) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 539651360 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 608994259) ^ 2323 = 296904507 := by
        calc
          (2 : ZMod 608994259) ^ 2323 = (2 : ZMod 608994259) ^ (1161 + 1161 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 1161 * (2 : ZMod 608994259) ^ 1161) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 296904507 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 608994259) ^ 4646 = 63124872 := by
        calc
          (2 : ZMod 608994259) ^ 4646 = (2 : ZMod 608994259) ^ (2323 + 2323) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 2323 * (2 : ZMod 608994259) ^ 2323 := by rw [pow_add]
          _ = 63124872 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 608994259) ^ 9292 = 153320908 := by
        calc
          (2 : ZMod 608994259) ^ 9292 = (2 : ZMod 608994259) ^ (4646 + 4646) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 4646 * (2 : ZMod 608994259) ^ 4646 := by rw [pow_add]
          _ = 153320908 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 608994259) ^ 18585 = 49396810 := by
        calc
          (2 : ZMod 608994259) ^ 18585 = (2 : ZMod 608994259) ^ (9292 + 9292 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 9292 * (2 : ZMod 608994259) ^ 9292) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 49396810 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 608994259) ^ 37170 = 329520239 := by
        calc
          (2 : ZMod 608994259) ^ 37170 = (2 : ZMod 608994259) ^ (18585 + 18585) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 18585 * (2 : ZMod 608994259) ^ 18585 := by rw [pow_add]
          _ = 329520239 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 608994259) ^ 74340 = 444078935 := by
        calc
          (2 : ZMod 608994259) ^ 74340 = (2 : ZMod 608994259) ^ (37170 + 37170) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 37170 * (2 : ZMod 608994259) ^ 37170 := by rw [pow_add]
          _ = 444078935 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 608994259) ^ 148680 = 439240638 := by
        calc
          (2 : ZMod 608994259) ^ 148680 = (2 : ZMod 608994259) ^ (74340 + 74340) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 74340 * (2 : ZMod 608994259) ^ 74340 := by rw [pow_add]
          _ = 439240638 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 608994259) ^ 297360 = 152319599 := by
        calc
          (2 : ZMod 608994259) ^ 297360 = (2 : ZMod 608994259) ^ (148680 + 148680) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 148680 * (2 : ZMod 608994259) ^ 148680 := by rw [pow_add]
          _ = 152319599 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 608994259) ^ 594720 = 364221307 := by
        calc
          (2 : ZMod 608994259) ^ 594720 = (2 : ZMod 608994259) ^ (297360 + 297360) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 297360 * (2 : ZMod 608994259) ^ 297360 := by rw [pow_add]
          _ = 364221307 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 608994259) ^ 1189441 = 214522744 := by
        calc
          (2 : ZMod 608994259) ^ 1189441 = (2 : ZMod 608994259) ^ (594720 + 594720 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 594720 * (2 : ZMod 608994259) ^ 594720) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 214522744 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 608994259) ^ 2378883 = 563479486 := by
        calc
          (2 : ZMod 608994259) ^ 2378883 = (2 : ZMod 608994259) ^ (1189441 + 1189441 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 1189441 * (2 : ZMod 608994259) ^ 1189441) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 563479486 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 608994259) ^ 4757767 = 210400588 := by
        calc
          (2 : ZMod 608994259) ^ 4757767 = (2 : ZMod 608994259) ^ (2378883 + 2378883 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 2378883 * (2 : ZMod 608994259) ^ 2378883) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 210400588 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 608994259) ^ 9515535 = 537656826 := by
        calc
          (2 : ZMod 608994259) ^ 9515535 = (2 : ZMod 608994259) ^ (4757767 + 4757767 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 4757767 * (2 : ZMod 608994259) ^ 4757767) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 537656826 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 608994259) ^ 19031070 = 489397457 := by
        calc
          (2 : ZMod 608994259) ^ 19031070 = (2 : ZMod 608994259) ^ (9515535 + 9515535) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 9515535 * (2 : ZMod 608994259) ^ 9515535 := by rw [pow_add]
          _ = 489397457 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 608994259) ^ 38062141 = 348983733 := by
        calc
          (2 : ZMod 608994259) ^ 38062141 = (2 : ZMod 608994259) ^ (19031070 + 19031070 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 19031070 * (2 : ZMod 608994259) ^ 19031070) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 348983733 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 608994259) ^ 76124282 = 264828592 := by
        calc
          (2 : ZMod 608994259) ^ 76124282 = (2 : ZMod 608994259) ^ (38062141 + 38062141) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 38062141 * (2 : ZMod 608994259) ^ 38062141 := by rw [pow_add]
          _ = 264828592 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 608994259) ^ 152248564 = 573922191 := by
        calc
          (2 : ZMod 608994259) ^ 152248564 = (2 : ZMod 608994259) ^ (76124282 + 76124282) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 76124282 * (2 : ZMod 608994259) ^ 76124282 := by rw [pow_add]
          _ = 573922191 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 608994259) ^ 304497129 = 608994258 := by
        calc
          (2 : ZMod 608994259) ^ 304497129 = (2 : ZMod 608994259) ^ (152248564 + 152248564 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 152248564 * (2 : ZMod 608994259) ^ 152248564) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 608994258 := by rw [factor_0_27]; decide
      change (2 : ZMod 608994259) ^ 304497129 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (2 : ZMod 608994259) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 608994259) ^ 3 = 8 := by
        calc
          (2 : ZMod 608994259) ^ 3 = (2 : ZMod 608994259) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 1 * (2 : ZMod 608994259) ^ 1) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 608994259) ^ 6 = 64 := by
        calc
          (2 : ZMod 608994259) ^ 6 = (2 : ZMod 608994259) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 3 * (2 : ZMod 608994259) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 608994259) ^ 12 = 4096 := by
        calc
          (2 : ZMod 608994259) ^ 12 = (2 : ZMod 608994259) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 6 * (2 : ZMod 608994259) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 608994259) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 608994259) ^ 24 = (2 : ZMod 608994259) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 12 * (2 : ZMod 608994259) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 608994259) ^ 48 = 266177892 := by
        calc
          (2 : ZMod 608994259) ^ 48 = (2 : ZMod 608994259) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 24 * (2 : ZMod 608994259) ^ 24 := by rw [pow_add]
          _ = 266177892 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 608994259) ^ 96 = 396121560 := by
        calc
          (2 : ZMod 608994259) ^ 96 = (2 : ZMod 608994259) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 48 * (2 : ZMod 608994259) ^ 48 := by rw [pow_add]
          _ = 396121560 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 608994259) ^ 193 = 19718796 := by
        calc
          (2 : ZMod 608994259) ^ 193 = (2 : ZMod 608994259) ^ (96 + 96 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 96 * (2 : ZMod 608994259) ^ 96) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 19718796 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 608994259) ^ 387 = 522406592 := by
        calc
          (2 : ZMod 608994259) ^ 387 = (2 : ZMod 608994259) ^ (193 + 193 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 193 * (2 : ZMod 608994259) ^ 193) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 522406592 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 608994259) ^ 774 = 141855226 := by
        calc
          (2 : ZMod 608994259) ^ 774 = (2 : ZMod 608994259) ^ (387 + 387) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 387 * (2 : ZMod 608994259) ^ 387 := by rw [pow_add]
          _ = 141855226 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 608994259) ^ 1548 = 410501444 := by
        calc
          (2 : ZMod 608994259) ^ 1548 = (2 : ZMod 608994259) ^ (774 + 774) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 774 * (2 : ZMod 608994259) ^ 774 := by rw [pow_add]
          _ = 410501444 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 608994259) ^ 3097 = 58929258 := by
        calc
          (2 : ZMod 608994259) ^ 3097 = (2 : ZMod 608994259) ^ (1548 + 1548 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 1548 * (2 : ZMod 608994259) ^ 1548) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 58929258 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 608994259) ^ 6195 = 285468793 := by
        calc
          (2 : ZMod 608994259) ^ 6195 = (2 : ZMod 608994259) ^ (3097 + 3097 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 3097 * (2 : ZMod 608994259) ^ 3097) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 285468793 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 608994259) ^ 12390 = 205517347 := by
        calc
          (2 : ZMod 608994259) ^ 12390 = (2 : ZMod 608994259) ^ (6195 + 6195) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 6195 * (2 : ZMod 608994259) ^ 6195 := by rw [pow_add]
          _ = 205517347 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 608994259) ^ 24780 = 277467546 := by
        calc
          (2 : ZMod 608994259) ^ 24780 = (2 : ZMod 608994259) ^ (12390 + 12390) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 12390 * (2 : ZMod 608994259) ^ 12390 := by rw [pow_add]
          _ = 277467546 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 608994259) ^ 49560 = 303794917 := by
        calc
          (2 : ZMod 608994259) ^ 49560 = (2 : ZMod 608994259) ^ (24780 + 24780) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 24780 * (2 : ZMod 608994259) ^ 24780 := by rw [pow_add]
          _ = 303794917 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 608994259) ^ 99120 = 578288190 := by
        calc
          (2 : ZMod 608994259) ^ 99120 = (2 : ZMod 608994259) ^ (49560 + 49560) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 49560 * (2 : ZMod 608994259) ^ 49560 := by rw [pow_add]
          _ = 578288190 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 608994259) ^ 198240 = 100815450 := by
        calc
          (2 : ZMod 608994259) ^ 198240 = (2 : ZMod 608994259) ^ (99120 + 99120) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 99120 * (2 : ZMod 608994259) ^ 99120 := by rw [pow_add]
          _ = 100815450 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 608994259) ^ 396480 = 82605310 := by
        calc
          (2 : ZMod 608994259) ^ 396480 = (2 : ZMod 608994259) ^ (198240 + 198240) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 198240 * (2 : ZMod 608994259) ^ 198240 := by rw [pow_add]
          _ = 82605310 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 608994259) ^ 792961 = 581492448 := by
        calc
          (2 : ZMod 608994259) ^ 792961 = (2 : ZMod 608994259) ^ (396480 + 396480 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 396480 * (2 : ZMod 608994259) ^ 396480) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 581492448 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 608994259) ^ 1585922 = 53400786 := by
        calc
          (2 : ZMod 608994259) ^ 1585922 = (2 : ZMod 608994259) ^ (792961 + 792961) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 792961 * (2 : ZMod 608994259) ^ 792961 := by rw [pow_add]
          _ = 53400786 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 608994259) ^ 3171845 = 18834505 := by
        calc
          (2 : ZMod 608994259) ^ 3171845 = (2 : ZMod 608994259) ^ (1585922 + 1585922 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 1585922 * (2 : ZMod 608994259) ^ 1585922) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 18834505 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 608994259) ^ 6343690 = 31721784 := by
        calc
          (2 : ZMod 608994259) ^ 6343690 = (2 : ZMod 608994259) ^ (3171845 + 3171845) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 3171845 * (2 : ZMod 608994259) ^ 3171845 := by rw [pow_add]
          _ = 31721784 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 608994259) ^ 12687380 = 525278265 := by
        calc
          (2 : ZMod 608994259) ^ 12687380 = (2 : ZMod 608994259) ^ (6343690 + 6343690) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 6343690 * (2 : ZMod 608994259) ^ 6343690 := by rw [pow_add]
          _ = 525278265 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 608994259) ^ 25374760 = 210415877 := by
        calc
          (2 : ZMod 608994259) ^ 25374760 = (2 : ZMod 608994259) ^ (12687380 + 12687380) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 12687380 * (2 : ZMod 608994259) ^ 12687380 := by rw [pow_add]
          _ = 210415877 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 608994259) ^ 50749521 = 214830926 := by
        calc
          (2 : ZMod 608994259) ^ 50749521 = (2 : ZMod 608994259) ^ (25374760 + 25374760 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 25374760 * (2 : ZMod 608994259) ^ 25374760) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 214830926 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 608994259) ^ 101499043 = 253686916 := by
        calc
          (2 : ZMod 608994259) ^ 101499043 = (2 : ZMod 608994259) ^ (50749521 + 50749521 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 50749521 * (2 : ZMod 608994259) ^ 50749521) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 253686916 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 608994259) ^ 202998086 = 253686915 := by
        calc
          (2 : ZMod 608994259) ^ 202998086 = (2 : ZMod 608994259) ^ (101499043 + 101499043) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 101499043 * (2 : ZMod 608994259) ^ 101499043 := by rw [pow_add]
          _ = 253686915 := by rw [factor_1_26]; decide
      change (2 : ZMod 608994259) ^ 202998086 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (2 : ZMod 608994259) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 608994259) ^ 2 = 4 := by
        calc
          (2 : ZMod 608994259) ^ 2 = (2 : ZMod 608994259) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 1 * (2 : ZMod 608994259) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 608994259) ^ 5 = 32 := by
        calc
          (2 : ZMod 608994259) ^ 5 = (2 : ZMod 608994259) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 2 * (2 : ZMod 608994259) ^ 2) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 608994259) ^ 10 = 1024 := by
        calc
          (2 : ZMod 608994259) ^ 10 = (2 : ZMod 608994259) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 5 * (2 : ZMod 608994259) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 608994259) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 608994259) ^ 20 = (2 : ZMod 608994259) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 10 * (2 : ZMod 608994259) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 608994259) ^ 40 = 276990281 := by
        calc
          (2 : ZMod 608994259) ^ 40 = (2 : ZMod 608994259) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 20 * (2 : ZMod 608994259) ^ 20 := by rw [pow_add]
          _ = 276990281 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 608994259) ^ 80 = 219383737 := by
        calc
          (2 : ZMod 608994259) ^ 80 = (2 : ZMod 608994259) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 40 * (2 : ZMod 608994259) ^ 40 := by rw [pow_add]
          _ = 219383737 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 608994259) ^ 160 = 354155898 := by
        calc
          (2 : ZMod 608994259) ^ 160 = (2 : ZMod 608994259) ^ (80 + 80) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 80 * (2 : ZMod 608994259) ^ 80 := by rw [pow_add]
          _ = 354155898 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 608994259) ^ 320 = 296147565 := by
        calc
          (2 : ZMod 608994259) ^ 320 = (2 : ZMod 608994259) ^ (160 + 160) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 160 * (2 : ZMod 608994259) ^ 160 := by rw [pow_add]
          _ = 296147565 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 608994259) ^ 640 = 152794941 := by
        calc
          (2 : ZMod 608994259) ^ 640 = (2 : ZMod 608994259) ^ (320 + 320) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 320 * (2 : ZMod 608994259) ^ 320 := by rw [pow_add]
          _ = 152794941 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 608994259) ^ 1281 = 11266461 := by
        calc
          (2 : ZMod 608994259) ^ 1281 = (2 : ZMod 608994259) ^ (640 + 640 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 640 * (2 : ZMod 608994259) ^ 640) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 11266461 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 608994259) ^ 2563 = 331128043 := by
        calc
          (2 : ZMod 608994259) ^ 2563 = (2 : ZMod 608994259) ^ (1281 + 1281 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 1281 * (2 : ZMod 608994259) ^ 1281) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 331128043 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 608994259) ^ 5126 = 223786079 := by
        calc
          (2 : ZMod 608994259) ^ 5126 = (2 : ZMod 608994259) ^ (2563 + 2563) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 2563 * (2 : ZMod 608994259) ^ 2563 := by rw [pow_add]
          _ = 223786079 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 608994259) ^ 10253 = 347477557 := by
        calc
          (2 : ZMod 608994259) ^ 10253 = (2 : ZMod 608994259) ^ (5126 + 5126 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 5126 * (2 : ZMod 608994259) ^ 5126) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 347477557 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 608994259) ^ 20507 = 410046622 := by
        calc
          (2 : ZMod 608994259) ^ 20507 = (2 : ZMod 608994259) ^ (10253 + 10253 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 10253 * (2 : ZMod 608994259) ^ 10253) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 410046622 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 608994259) ^ 41015 = 548587255 := by
        calc
          (2 : ZMod 608994259) ^ 41015 = (2 : ZMod 608994259) ^ (20507 + 20507 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 20507 * (2 : ZMod 608994259) ^ 20507) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 548587255 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 608994259) ^ 82030 = 227501312 := by
        calc
          (2 : ZMod 608994259) ^ 82030 = (2 : ZMod 608994259) ^ (41015 + 41015) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 41015 * (2 : ZMod 608994259) ^ 41015 := by rw [pow_add]
          _ = 227501312 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 608994259) ^ 164060 = 357459377 := by
        calc
          (2 : ZMod 608994259) ^ 164060 = (2 : ZMod 608994259) ^ (82030 + 82030) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 82030 * (2 : ZMod 608994259) ^ 82030 := by rw [pow_add]
          _ = 357459377 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 608994259) ^ 328121 = 538563470 := by
        calc
          (2 : ZMod 608994259) ^ 328121 = (2 : ZMod 608994259) ^ (164060 + 164060 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 164060 * (2 : ZMod 608994259) ^ 164060) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 538563470 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 608994259) ^ 656243 = 583693022 := by
        calc
          (2 : ZMod 608994259) ^ 656243 = (2 : ZMod 608994259) ^ (328121 + 328121 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 328121 * (2 : ZMod 608994259) ^ 328121) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 583693022 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 608994259) ^ 1312487 = 113919645 := by
        calc
          (2 : ZMod 608994259) ^ 1312487 = (2 : ZMod 608994259) ^ (656243 + 656243 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 656243 * (2 : ZMod 608994259) ^ 656243) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 113919645 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 608994259) ^ 2624975 = 393605028 := by
        calc
          (2 : ZMod 608994259) ^ 2624975 = (2 : ZMod 608994259) ^ (1312487 + 1312487 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 1312487 * (2 : ZMod 608994259) ^ 1312487) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 393605028 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 608994259) ^ 5249950 = 156910894 := by
        calc
          (2 : ZMod 608994259) ^ 5249950 = (2 : ZMod 608994259) ^ (2624975 + 2624975) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 2624975 * (2 : ZMod 608994259) ^ 2624975 := by rw [pow_add]
          _ = 156910894 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 608994259) ^ 10499901 = 126530731 := by
        calc
          (2 : ZMod 608994259) ^ 10499901 = (2 : ZMod 608994259) ^ (5249950 + 5249950 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 5249950 * (2 : ZMod 608994259) ^ 5249950) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 126530731 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 608994259) ^ 20999802 = 422196769 := by
        calc
          (2 : ZMod 608994259) ^ 20999802 = (2 : ZMod 608994259) ^ (10499901 + 10499901) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 10499901 * (2 : ZMod 608994259) ^ 10499901 := by rw [pow_add]
          _ = 422196769 := by rw [factor_2_23]; decide
      change (2 : ZMod 608994259) ^ 20999802 ≠ 1
      rw [factor_2_24]
      decide
    ·
      have factor_3_0 : (2 : ZMod 608994259) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 608994259) ^ 2 = 4 := by
        calc
          (2 : ZMod 608994259) ^ 2 = (2 : ZMod 608994259) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 1 * (2 : ZMod 608994259) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 608994259) ^ 5 = 32 := by
        calc
          (2 : ZMod 608994259) ^ 5 = (2 : ZMod 608994259) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 2 * (2 : ZMod 608994259) ^ 2) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 608994259) ^ 10 = 1024 := by
        calc
          (2 : ZMod 608994259) ^ 10 = (2 : ZMod 608994259) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 5 * (2 : ZMod 608994259) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 608994259) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 608994259) ^ 21 = (2 : ZMod 608994259) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 10 * (2 : ZMod 608994259) ^ 10) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 608994259) ^ 43 = 388939471 := by
        calc
          (2 : ZMod 608994259) ^ 43 = (2 : ZMod 608994259) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 21 * (2 : ZMod 608994259) ^ 21) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 388939471 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 608994259) ^ 87 = 67382422 := by
        calc
          (2 : ZMod 608994259) ^ 87 = (2 : ZMod 608994259) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = ((2 : ZMod 608994259) ^ 43 * (2 : ZMod 608994259) ^ 43) * (2 : ZMod 608994259) := by rw [pow_succ, pow_add]
          _ = 67382422 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 608994259) ^ 174 = 601927339 := by
        calc
          (2 : ZMod 608994259) ^ 174 = (2 : ZMod 608994259) ^ (87 + 87) :=
            congrArg (fun n : ℕ => (2 : ZMod 608994259) ^ n) (by norm_num)
          _ = (2 : ZMod 608994259) ^ 87 * (2 : ZMod 608994259) ^ 87 := by rw [pow_add]
          _ = 601927339 := by rw [factor_3_6]; decide
      change (2 : ZMod 608994259) ^ 174 ≠ 1
      rw [factor_3_7]
      decide

#print axioms prime_lucas_608994259

end TotientTailPeriodKiller
end Erdos249257
