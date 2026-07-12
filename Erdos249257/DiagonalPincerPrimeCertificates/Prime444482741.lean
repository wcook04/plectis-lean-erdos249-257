import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_444482741 : Nat.Prime 444482741 := by
  apply lucas_primality 444482741 (3 : ZMod 444482741)
  ·
      have fermat_0 : (3 : ZMod 444482741) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 444482741) ^ 3 = 27 := by
        calc
          (3 : ZMod 444482741) ^ 3 = (3 : ZMod 444482741) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 1 * (3 : ZMod 444482741) ^ 1) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 444482741) ^ 6 = 729 := by
        calc
          (3 : ZMod 444482741) ^ 6 = (3 : ZMod 444482741) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 3 * (3 : ZMod 444482741) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 444482741) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 444482741) ^ 13 = (3 : ZMod 444482741) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 6 * (3 : ZMod 444482741) ^ 6) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 444482741) ^ 26 = 313515291 := by
        calc
          (3 : ZMod 444482741) ^ 26 = (3 : ZMod 444482741) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 13 * (3 : ZMod 444482741) ^ 13 := by rw [pow_add]
          _ = 313515291 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 444482741) ^ 52 = 438790642 := by
        calc
          (3 : ZMod 444482741) ^ 52 = (3 : ZMod 444482741) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 26 * (3 : ZMod 444482741) ^ 26 := by rw [pow_add]
          _ = 438790642 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 444482741) ^ 105 = 42792782 := by
        calc
          (3 : ZMod 444482741) ^ 105 = (3 : ZMod 444482741) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 52 * (3 : ZMod 444482741) ^ 52) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 42792782 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 444482741) ^ 211 = 351684728 := by
        calc
          (3 : ZMod 444482741) ^ 211 = (3 : ZMod 444482741) ^ (105 + 105 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 105 * (3 : ZMod 444482741) ^ 105) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 351684728 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 444482741) ^ 423 = 206125805 := by
        calc
          (3 : ZMod 444482741) ^ 423 = (3 : ZMod 444482741) ^ (211 + 211 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 211 * (3 : ZMod 444482741) ^ 211) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 206125805 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 444482741) ^ 847 = 224093415 := by
        calc
          (3 : ZMod 444482741) ^ 847 = (3 : ZMod 444482741) ^ (423 + 423 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 423 * (3 : ZMod 444482741) ^ 423) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 224093415 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 444482741) ^ 1695 = 97673735 := by
        calc
          (3 : ZMod 444482741) ^ 1695 = (3 : ZMod 444482741) ^ (847 + 847 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 847 * (3 : ZMod 444482741) ^ 847) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 97673735 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 444482741) ^ 3391 = 258052614 := by
        calc
          (3 : ZMod 444482741) ^ 3391 = (3 : ZMod 444482741) ^ (1695 + 1695 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 1695 * (3 : ZMod 444482741) ^ 1695) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 258052614 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 444482741) ^ 6782 = 332459875 := by
        calc
          (3 : ZMod 444482741) ^ 6782 = (3 : ZMod 444482741) ^ (3391 + 3391) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 3391 * (3 : ZMod 444482741) ^ 3391 := by rw [pow_add]
          _ = 332459875 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 444482741) ^ 13564 = 387788784 := by
        calc
          (3 : ZMod 444482741) ^ 13564 = (3 : ZMod 444482741) ^ (6782 + 6782) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 6782 * (3 : ZMod 444482741) ^ 6782 := by rw [pow_add]
          _ = 387788784 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 444482741) ^ 27129 = 363906655 := by
        calc
          (3 : ZMod 444482741) ^ 27129 = (3 : ZMod 444482741) ^ (13564 + 13564 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 13564 * (3 : ZMod 444482741) ^ 13564) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 363906655 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 444482741) ^ 54258 = 19704057 := by
        calc
          (3 : ZMod 444482741) ^ 54258 = (3 : ZMod 444482741) ^ (27129 + 27129) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 27129 * (3 : ZMod 444482741) ^ 27129 := by rw [pow_add]
          _ = 19704057 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 444482741) ^ 108516 = 410754123 := by
        calc
          (3 : ZMod 444482741) ^ 108516 = (3 : ZMod 444482741) ^ (54258 + 54258) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 54258 * (3 : ZMod 444482741) ^ 54258 := by rw [pow_add]
          _ = 410754123 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 444482741) ^ 217032 = 321771481 := by
        calc
          (3 : ZMod 444482741) ^ 217032 = (3 : ZMod 444482741) ^ (108516 + 108516) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 108516 * (3 : ZMod 444482741) ^ 108516 := by rw [pow_add]
          _ = 321771481 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 444482741) ^ 434065 = 239070218 := by
        calc
          (3 : ZMod 444482741) ^ 434065 = (3 : ZMod 444482741) ^ (217032 + 217032 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 217032 * (3 : ZMod 444482741) ^ 217032) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 239070218 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 444482741) ^ 868130 = 262422824 := by
        calc
          (3 : ZMod 444482741) ^ 868130 = (3 : ZMod 444482741) ^ (434065 + 434065) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 434065 * (3 : ZMod 444482741) ^ 434065 := by rw [pow_add]
          _ = 262422824 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 444482741) ^ 1736260 = 207223275 := by
        calc
          (3 : ZMod 444482741) ^ 1736260 = (3 : ZMod 444482741) ^ (868130 + 868130) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 868130 * (3 : ZMod 444482741) ^ 868130 := by rw [pow_add]
          _ = 207223275 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 444482741) ^ 3472521 = 279078861 := by
        calc
          (3 : ZMod 444482741) ^ 3472521 = (3 : ZMod 444482741) ^ (1736260 + 1736260 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 1736260 * (3 : ZMod 444482741) ^ 1736260) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 279078861 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 444482741) ^ 6945042 = 98111646 := by
        calc
          (3 : ZMod 444482741) ^ 6945042 = (3 : ZMod 444482741) ^ (3472521 + 3472521) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 3472521 * (3 : ZMod 444482741) ^ 3472521 := by rw [pow_add]
          _ = 98111646 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 444482741) ^ 13890085 = 257289935 := by
        calc
          (3 : ZMod 444482741) ^ 13890085 = (3 : ZMod 444482741) ^ (6945042 + 6945042 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 6945042 * (3 : ZMod 444482741) ^ 6945042) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 257289935 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 444482741) ^ 27780171 = 214987148 := by
        calc
          (3 : ZMod 444482741) ^ 27780171 = (3 : ZMod 444482741) ^ (13890085 + 13890085 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 13890085 * (3 : ZMod 444482741) ^ 13890085) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 214987148 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 444482741) ^ 55560342 = 432286349 := by
        calc
          (3 : ZMod 444482741) ^ 55560342 = (3 : ZMod 444482741) ^ (27780171 + 27780171) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 27780171 * (3 : ZMod 444482741) ^ 27780171 := by rw [pow_add]
          _ = 432286349 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 444482741) ^ 111120685 = 150799143 := by
        calc
          (3 : ZMod 444482741) ^ 111120685 = (3 : ZMod 444482741) ^ (55560342 + 55560342 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 55560342 * (3 : ZMod 444482741) ^ 55560342) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 150799143 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 444482741) ^ 222241370 = 444482740 := by
        calc
          (3 : ZMod 444482741) ^ 222241370 = (3 : ZMod 444482741) ^ (111120685 + 111120685) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 111120685 * (3 : ZMod 444482741) ^ 111120685 := by rw [pow_add]
          _ = 444482740 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 444482741) ^ 444482740 = 1 := by
        calc
          (3 : ZMod 444482741) ^ 444482740 = (3 : ZMod 444482741) ^ (222241370 + 222241370) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 222241370 * (3 : ZMod 444482741) ^ 222241370 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (13, 1), (683, 1), (2503, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (13, 1), (683, 1), (2503, 1)] : List FactorBlock).map factorBlockValue).prod = 444482741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 444482741) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 444482741) ^ 3 = 27 := by
        calc
          (3 : ZMod 444482741) ^ 3 = (3 : ZMod 444482741) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 1 * (3 : ZMod 444482741) ^ 1) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 444482741) ^ 6 = 729 := by
        calc
          (3 : ZMod 444482741) ^ 6 = (3 : ZMod 444482741) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 3 * (3 : ZMod 444482741) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 444482741) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 444482741) ^ 13 = (3 : ZMod 444482741) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 6 * (3 : ZMod 444482741) ^ 6) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 444482741) ^ 26 = 313515291 := by
        calc
          (3 : ZMod 444482741) ^ 26 = (3 : ZMod 444482741) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 13 * (3 : ZMod 444482741) ^ 13 := by rw [pow_add]
          _ = 313515291 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 444482741) ^ 52 = 438790642 := by
        calc
          (3 : ZMod 444482741) ^ 52 = (3 : ZMod 444482741) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 26 * (3 : ZMod 444482741) ^ 26 := by rw [pow_add]
          _ = 438790642 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 444482741) ^ 105 = 42792782 := by
        calc
          (3 : ZMod 444482741) ^ 105 = (3 : ZMod 444482741) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 52 * (3 : ZMod 444482741) ^ 52) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 42792782 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 444482741) ^ 211 = 351684728 := by
        calc
          (3 : ZMod 444482741) ^ 211 = (3 : ZMod 444482741) ^ (105 + 105 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 105 * (3 : ZMod 444482741) ^ 105) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 351684728 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 444482741) ^ 423 = 206125805 := by
        calc
          (3 : ZMod 444482741) ^ 423 = (3 : ZMod 444482741) ^ (211 + 211 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 211 * (3 : ZMod 444482741) ^ 211) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 206125805 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 444482741) ^ 847 = 224093415 := by
        calc
          (3 : ZMod 444482741) ^ 847 = (3 : ZMod 444482741) ^ (423 + 423 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 423 * (3 : ZMod 444482741) ^ 423) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 224093415 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 444482741) ^ 1695 = 97673735 := by
        calc
          (3 : ZMod 444482741) ^ 1695 = (3 : ZMod 444482741) ^ (847 + 847 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 847 * (3 : ZMod 444482741) ^ 847) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 97673735 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 444482741) ^ 3391 = 258052614 := by
        calc
          (3 : ZMod 444482741) ^ 3391 = (3 : ZMod 444482741) ^ (1695 + 1695 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 1695 * (3 : ZMod 444482741) ^ 1695) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 258052614 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 444482741) ^ 6782 = 332459875 := by
        calc
          (3 : ZMod 444482741) ^ 6782 = (3 : ZMod 444482741) ^ (3391 + 3391) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 3391 * (3 : ZMod 444482741) ^ 3391 := by rw [pow_add]
          _ = 332459875 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 444482741) ^ 13564 = 387788784 := by
        calc
          (3 : ZMod 444482741) ^ 13564 = (3 : ZMod 444482741) ^ (6782 + 6782) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 6782 * (3 : ZMod 444482741) ^ 6782 := by rw [pow_add]
          _ = 387788784 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 444482741) ^ 27129 = 363906655 := by
        calc
          (3 : ZMod 444482741) ^ 27129 = (3 : ZMod 444482741) ^ (13564 + 13564 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 13564 * (3 : ZMod 444482741) ^ 13564) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 363906655 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 444482741) ^ 54258 = 19704057 := by
        calc
          (3 : ZMod 444482741) ^ 54258 = (3 : ZMod 444482741) ^ (27129 + 27129) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 27129 * (3 : ZMod 444482741) ^ 27129 := by rw [pow_add]
          _ = 19704057 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 444482741) ^ 108516 = 410754123 := by
        calc
          (3 : ZMod 444482741) ^ 108516 = (3 : ZMod 444482741) ^ (54258 + 54258) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 54258 * (3 : ZMod 444482741) ^ 54258 := by rw [pow_add]
          _ = 410754123 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 444482741) ^ 217032 = 321771481 := by
        calc
          (3 : ZMod 444482741) ^ 217032 = (3 : ZMod 444482741) ^ (108516 + 108516) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 108516 * (3 : ZMod 444482741) ^ 108516 := by rw [pow_add]
          _ = 321771481 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 444482741) ^ 434065 = 239070218 := by
        calc
          (3 : ZMod 444482741) ^ 434065 = (3 : ZMod 444482741) ^ (217032 + 217032 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 217032 * (3 : ZMod 444482741) ^ 217032) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 239070218 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 444482741) ^ 868130 = 262422824 := by
        calc
          (3 : ZMod 444482741) ^ 868130 = (3 : ZMod 444482741) ^ (434065 + 434065) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 434065 * (3 : ZMod 444482741) ^ 434065 := by rw [pow_add]
          _ = 262422824 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 444482741) ^ 1736260 = 207223275 := by
        calc
          (3 : ZMod 444482741) ^ 1736260 = (3 : ZMod 444482741) ^ (868130 + 868130) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 868130 * (3 : ZMod 444482741) ^ 868130 := by rw [pow_add]
          _ = 207223275 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 444482741) ^ 3472521 = 279078861 := by
        calc
          (3 : ZMod 444482741) ^ 3472521 = (3 : ZMod 444482741) ^ (1736260 + 1736260 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 1736260 * (3 : ZMod 444482741) ^ 1736260) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 279078861 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 444482741) ^ 6945042 = 98111646 := by
        calc
          (3 : ZMod 444482741) ^ 6945042 = (3 : ZMod 444482741) ^ (3472521 + 3472521) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 3472521 * (3 : ZMod 444482741) ^ 3472521 := by rw [pow_add]
          _ = 98111646 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 444482741) ^ 13890085 = 257289935 := by
        calc
          (3 : ZMod 444482741) ^ 13890085 = (3 : ZMod 444482741) ^ (6945042 + 6945042 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 6945042 * (3 : ZMod 444482741) ^ 6945042) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 257289935 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 444482741) ^ 27780171 = 214987148 := by
        calc
          (3 : ZMod 444482741) ^ 27780171 = (3 : ZMod 444482741) ^ (13890085 + 13890085 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 13890085 * (3 : ZMod 444482741) ^ 13890085) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 214987148 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 444482741) ^ 55560342 = 432286349 := by
        calc
          (3 : ZMod 444482741) ^ 55560342 = (3 : ZMod 444482741) ^ (27780171 + 27780171) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 27780171 * (3 : ZMod 444482741) ^ 27780171 := by rw [pow_add]
          _ = 432286349 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 444482741) ^ 111120685 = 150799143 := by
        calc
          (3 : ZMod 444482741) ^ 111120685 = (3 : ZMod 444482741) ^ (55560342 + 55560342 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 55560342 * (3 : ZMod 444482741) ^ 55560342) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 150799143 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 444482741) ^ 222241370 = 444482740 := by
        calc
          (3 : ZMod 444482741) ^ 222241370 = (3 : ZMod 444482741) ^ (111120685 + 111120685) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 111120685 * (3 : ZMod 444482741) ^ 111120685 := by rw [pow_add]
          _ = 444482740 := by rw [factor_0_26]; decide
      change (3 : ZMod 444482741) ^ 222241370 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (3 : ZMod 444482741) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 444482741) ^ 2 = 9 := by
        calc
          (3 : ZMod 444482741) ^ 2 = (3 : ZMod 444482741) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 1 * (3 : ZMod 444482741) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 444482741) ^ 5 = 243 := by
        calc
          (3 : ZMod 444482741) ^ 5 = (3 : ZMod 444482741) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 2 * (3 : ZMod 444482741) ^ 2) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 444482741) ^ 10 = 59049 := by
        calc
          (3 : ZMod 444482741) ^ 10 = (3 : ZMod 444482741) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 5 * (3 : ZMod 444482741) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 444482741) ^ 21 = 237250160 := by
        calc
          (3 : ZMod 444482741) ^ 21 = (3 : ZMod 444482741) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 10 * (3 : ZMod 444482741) ^ 10) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 237250160 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 444482741) ^ 42 = 242478566 := by
        calc
          (3 : ZMod 444482741) ^ 42 = (3 : ZMod 444482741) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 21 * (3 : ZMod 444482741) ^ 21 := by rw [pow_add]
          _ = 242478566 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 444482741) ^ 84 = 239923581 := by
        calc
          (3 : ZMod 444482741) ^ 84 = (3 : ZMod 444482741) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 42 * (3 : ZMod 444482741) ^ 42 := by rw [pow_add]
          _ = 239923581 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 444482741) ^ 169 = 110390359 := by
        calc
          (3 : ZMod 444482741) ^ 169 = (3 : ZMod 444482741) ^ (84 + 84 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 84 * (3 : ZMod 444482741) ^ 84) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 110390359 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 444482741) ^ 339 = 241448259 := by
        calc
          (3 : ZMod 444482741) ^ 339 = (3 : ZMod 444482741) ^ (169 + 169 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 169 * (3 : ZMod 444482741) ^ 169) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 241448259 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 444482741) ^ 678 = 225562164 := by
        calc
          (3 : ZMod 444482741) ^ 678 = (3 : ZMod 444482741) ^ (339 + 339) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 339 * (3 : ZMod 444482741) ^ 339 := by rw [pow_add]
          _ = 225562164 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 444482741) ^ 1356 = 386027488 := by
        calc
          (3 : ZMod 444482741) ^ 1356 = (3 : ZMod 444482741) ^ (678 + 678) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 678 * (3 : ZMod 444482741) ^ 678 := by rw [pow_add]
          _ = 386027488 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 444482741) ^ 2712 = 415996625 := by
        calc
          (3 : ZMod 444482741) ^ 2712 = (3 : ZMod 444482741) ^ (1356 + 1356) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 1356 * (3 : ZMod 444482741) ^ 1356 := by rw [pow_add]
          _ = 415996625 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 444482741) ^ 5425 = 2181993 := by
        calc
          (3 : ZMod 444482741) ^ 5425 = (3 : ZMod 444482741) ^ (2712 + 2712 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 2712 * (3 : ZMod 444482741) ^ 2712) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 2181993 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 444482741) ^ 10851 = 271956853 := by
        calc
          (3 : ZMod 444482741) ^ 10851 = (3 : ZMod 444482741) ^ (5425 + 5425 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 5425 * (3 : ZMod 444482741) ^ 5425) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 271956853 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 444482741) ^ 21703 = 401900385 := by
        calc
          (3 : ZMod 444482741) ^ 21703 = (3 : ZMod 444482741) ^ (10851 + 10851 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 10851 * (3 : ZMod 444482741) ^ 10851) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 401900385 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 444482741) ^ 43406 = 368187020 := by
        calc
          (3 : ZMod 444482741) ^ 43406 = (3 : ZMod 444482741) ^ (21703 + 21703) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 21703 * (3 : ZMod 444482741) ^ 21703 := by rw [pow_add]
          _ = 368187020 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 444482741) ^ 86813 = 287918549 := by
        calc
          (3 : ZMod 444482741) ^ 86813 = (3 : ZMod 444482741) ^ (43406 + 43406 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 43406 * (3 : ZMod 444482741) ^ 43406) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 287918549 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 444482741) ^ 173626 = 14910857 := by
        calc
          (3 : ZMod 444482741) ^ 173626 = (3 : ZMod 444482741) ^ (86813 + 86813) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 86813 * (3 : ZMod 444482741) ^ 86813 := by rw [pow_add]
          _ = 14910857 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 444482741) ^ 347252 = 278047062 := by
        calc
          (3 : ZMod 444482741) ^ 347252 = (3 : ZMod 444482741) ^ (173626 + 173626) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 173626 * (3 : ZMod 444482741) ^ 173626 := by rw [pow_add]
          _ = 278047062 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 444482741) ^ 694504 = 100614872 := by
        calc
          (3 : ZMod 444482741) ^ 694504 = (3 : ZMod 444482741) ^ (347252 + 347252) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 347252 * (3 : ZMod 444482741) ^ 347252 := by rw [pow_add]
          _ = 100614872 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 444482741) ^ 1389008 = 241311604 := by
        calc
          (3 : ZMod 444482741) ^ 1389008 = (3 : ZMod 444482741) ^ (694504 + 694504) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 694504 * (3 : ZMod 444482741) ^ 694504 := by rw [pow_add]
          _ = 241311604 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 444482741) ^ 2778017 = 415054026 := by
        calc
          (3 : ZMod 444482741) ^ 2778017 = (3 : ZMod 444482741) ^ (1389008 + 1389008 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 1389008 * (3 : ZMod 444482741) ^ 1389008) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 415054026 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 444482741) ^ 5556034 = 425711703 := by
        calc
          (3 : ZMod 444482741) ^ 5556034 = (3 : ZMod 444482741) ^ (2778017 + 2778017) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 2778017 * (3 : ZMod 444482741) ^ 2778017 := by rw [pow_add]
          _ = 425711703 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 444482741) ^ 11112068 = 175703701 := by
        calc
          (3 : ZMod 444482741) ^ 11112068 = (3 : ZMod 444482741) ^ (5556034 + 5556034) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 5556034 * (3 : ZMod 444482741) ^ 5556034 := by rw [pow_add]
          _ = 175703701 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 444482741) ^ 22224137 = 355476632 := by
        calc
          (3 : ZMod 444482741) ^ 22224137 = (3 : ZMod 444482741) ^ (11112068 + 11112068 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 11112068 * (3 : ZMod 444482741) ^ 11112068) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 355476632 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 444482741) ^ 44448274 = 429238321 := by
        calc
          (3 : ZMod 444482741) ^ 44448274 = (3 : ZMod 444482741) ^ (22224137 + 22224137) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 22224137 * (3 : ZMod 444482741) ^ 22224137 := by rw [pow_add]
          _ = 429238321 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 444482741) ^ 88896548 = 318280183 := by
        calc
          (3 : ZMod 444482741) ^ 88896548 = (3 : ZMod 444482741) ^ (44448274 + 44448274) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 44448274 * (3 : ZMod 444482741) ^ 44448274 := by rw [pow_add]
          _ = 318280183 := by rw [factor_1_25]; decide
      change (3 : ZMod 444482741) ^ 88896548 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (3 : ZMod 444482741) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 444482741) ^ 2 = 9 := by
        calc
          (3 : ZMod 444482741) ^ 2 = (3 : ZMod 444482741) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 1 * (3 : ZMod 444482741) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 444482741) ^ 4 = 81 := by
        calc
          (3 : ZMod 444482741) ^ 4 = (3 : ZMod 444482741) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 2 * (3 : ZMod 444482741) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 444482741) ^ 8 = 6561 := by
        calc
          (3 : ZMod 444482741) ^ 8 = (3 : ZMod 444482741) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 4 * (3 : ZMod 444482741) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 444482741) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 444482741) ^ 16 = (3 : ZMod 444482741) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 8 * (3 : ZMod 444482741) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 444482741) ^ 32 = 88518265 := by
        calc
          (3 : ZMod 444482741) ^ 32 = (3 : ZMod 444482741) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 16 * (3 : ZMod 444482741) ^ 16 := by rw [pow_add]
          _ = 88518265 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 444482741) ^ 65 = 404251761 := by
        calc
          (3 : ZMod 444482741) ^ 65 = (3 : ZMod 444482741) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 32 * (3 : ZMod 444482741) ^ 32) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 404251761 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 444482741) ^ 130 = 299372338 := by
        calc
          (3 : ZMod 444482741) ^ 130 = (3 : ZMod 444482741) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 65 * (3 : ZMod 444482741) ^ 65 := by rw [pow_add]
          _ = 299372338 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 444482741) ^ 260 = 122209756 := by
        calc
          (3 : ZMod 444482741) ^ 260 = (3 : ZMod 444482741) ^ (130 + 130) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 130 * (3 : ZMod 444482741) ^ 130 := by rw [pow_add]
          _ = 122209756 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 444482741) ^ 521 = 46838069 := by
        calc
          (3 : ZMod 444482741) ^ 521 = (3 : ZMod 444482741) ^ (260 + 260 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 260 * (3 : ZMod 444482741) ^ 260) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 46838069 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 444482741) ^ 1043 = 402819678 := by
        calc
          (3 : ZMod 444482741) ^ 1043 = (3 : ZMod 444482741) ^ (521 + 521 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 521 * (3 : ZMod 444482741) ^ 521) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 402819678 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 444482741) ^ 2086 = 372527352 := by
        calc
          (3 : ZMod 444482741) ^ 2086 = (3 : ZMod 444482741) ^ (1043 + 1043) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 1043 * (3 : ZMod 444482741) ^ 1043 := by rw [pow_add]
          _ = 372527352 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 444482741) ^ 4173 = 165224723 := by
        calc
          (3 : ZMod 444482741) ^ 4173 = (3 : ZMod 444482741) ^ (2086 + 2086 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 2086 * (3 : ZMod 444482741) ^ 2086) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 165224723 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 444482741) ^ 8347 = 319338243 := by
        calc
          (3 : ZMod 444482741) ^ 8347 = (3 : ZMod 444482741) ^ (4173 + 4173 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 4173 * (3 : ZMod 444482741) ^ 4173) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 319338243 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 444482741) ^ 16694 = 18115123 := by
        calc
          (3 : ZMod 444482741) ^ 16694 = (3 : ZMod 444482741) ^ (8347 + 8347) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 8347 * (3 : ZMod 444482741) ^ 8347 := by rw [pow_add]
          _ = 18115123 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 444482741) ^ 33389 = 221908494 := by
        calc
          (3 : ZMod 444482741) ^ 33389 = (3 : ZMod 444482741) ^ (16694 + 16694 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 16694 * (3 : ZMod 444482741) ^ 16694) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 221908494 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 444482741) ^ 66779 = 58323174 := by
        calc
          (3 : ZMod 444482741) ^ 66779 = (3 : ZMod 444482741) ^ (33389 + 33389 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 33389 * (3 : ZMod 444482741) ^ 33389) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 58323174 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 444482741) ^ 133558 = 433732333 := by
        calc
          (3 : ZMod 444482741) ^ 133558 = (3 : ZMod 444482741) ^ (66779 + 66779) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 66779 * (3 : ZMod 444482741) ^ 66779 := by rw [pow_add]
          _ = 433732333 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 444482741) ^ 267117 = 388175234 := by
        calc
          (3 : ZMod 444482741) ^ 267117 = (3 : ZMod 444482741) ^ (133558 + 133558 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 133558 * (3 : ZMod 444482741) ^ 133558) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 388175234 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 444482741) ^ 534234 = 394038100 := by
        calc
          (3 : ZMod 444482741) ^ 534234 = (3 : ZMod 444482741) ^ (267117 + 267117) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 267117 * (3 : ZMod 444482741) ^ 267117 := by rw [pow_add]
          _ = 394038100 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 444482741) ^ 1068468 = 335807586 := by
        calc
          (3 : ZMod 444482741) ^ 1068468 = (3 : ZMod 444482741) ^ (534234 + 534234) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 534234 * (3 : ZMod 444482741) ^ 534234 := by rw [pow_add]
          _ = 335807586 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 444482741) ^ 2136936 = 186264024 := by
        calc
          (3 : ZMod 444482741) ^ 2136936 = (3 : ZMod 444482741) ^ (1068468 + 1068468) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 1068468 * (3 : ZMod 444482741) ^ 1068468 := by rw [pow_add]
          _ = 186264024 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 444482741) ^ 4273872 = 49649097 := by
        calc
          (3 : ZMod 444482741) ^ 4273872 = (3 : ZMod 444482741) ^ (2136936 + 2136936) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 2136936 * (3 : ZMod 444482741) ^ 2136936 := by rw [pow_add]
          _ = 49649097 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 444482741) ^ 8547745 = 5014569 := by
        calc
          (3 : ZMod 444482741) ^ 8547745 = (3 : ZMod 444482741) ^ (4273872 + 4273872 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 4273872 * (3 : ZMod 444482741) ^ 4273872) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 5014569 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 444482741) ^ 17095490 = 180149168 := by
        calc
          (3 : ZMod 444482741) ^ 17095490 = (3 : ZMod 444482741) ^ (8547745 + 8547745) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 8547745 * (3 : ZMod 444482741) ^ 8547745 := by rw [pow_add]
          _ = 180149168 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 444482741) ^ 34190980 = 301797480 := by
        calc
          (3 : ZMod 444482741) ^ 34190980 = (3 : ZMod 444482741) ^ (17095490 + 17095490) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 17095490 * (3 : ZMod 444482741) ^ 17095490 := by rw [pow_add]
          _ = 301797480 := by rw [factor_2_24]; decide
      change (3 : ZMod 444482741) ^ 34190980 ≠ 1
      rw [factor_2_25]
      decide
    ·
      have factor_3_0 : (3 : ZMod 444482741) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 444482741) ^ 2 = 9 := by
        calc
          (3 : ZMod 444482741) ^ 2 = (3 : ZMod 444482741) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 1 * (3 : ZMod 444482741) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 444482741) ^ 4 = 81 := by
        calc
          (3 : ZMod 444482741) ^ 4 = (3 : ZMod 444482741) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 2 * (3 : ZMod 444482741) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 444482741) ^ 9 = 19683 := by
        calc
          (3 : ZMod 444482741) ^ 9 = (3 : ZMod 444482741) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 4 * (3 : ZMod 444482741) ^ 4) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 444482741) ^ 19 = 273295985 := by
        calc
          (3 : ZMod 444482741) ^ 19 = (3 : ZMod 444482741) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 9 * (3 : ZMod 444482741) ^ 9) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 273295985 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 444482741) ^ 39 = 239453220 := by
        calc
          (3 : ZMod 444482741) ^ 39 = (3 : ZMod 444482741) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 19 * (3 : ZMod 444482741) ^ 19) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 239453220 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 444482741) ^ 79 = 160123136 := by
        calc
          (3 : ZMod 444482741) ^ 79 = (3 : ZMod 444482741) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 39 * (3 : ZMod 444482741) ^ 39) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 160123136 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 444482741) ^ 158 = 261315235 := by
        calc
          (3 : ZMod 444482741) ^ 158 = (3 : ZMod 444482741) ^ (79 + 79) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 79 * (3 : ZMod 444482741) ^ 79 := by rw [pow_add]
          _ = 261315235 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 444482741) ^ 317 = 356349858 := by
        calc
          (3 : ZMod 444482741) ^ 317 = (3 : ZMod 444482741) ^ (158 + 158 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 158 * (3 : ZMod 444482741) ^ 158) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 356349858 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 444482741) ^ 635 = 371792761 := by
        calc
          (3 : ZMod 444482741) ^ 635 = (3 : ZMod 444482741) ^ (317 + 317 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 317 * (3 : ZMod 444482741) ^ 317) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 371792761 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 444482741) ^ 1271 = 36983659 := by
        calc
          (3 : ZMod 444482741) ^ 1271 = (3 : ZMod 444482741) ^ (635 + 635 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 635 * (3 : ZMod 444482741) ^ 635) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 36983659 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 444482741) ^ 2542 = 295527657 := by
        calc
          (3 : ZMod 444482741) ^ 2542 = (3 : ZMod 444482741) ^ (1271 + 1271) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 1271 * (3 : ZMod 444482741) ^ 1271 := by rw [pow_add]
          _ = 295527657 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 444482741) ^ 5084 = 34895839 := by
        calc
          (3 : ZMod 444482741) ^ 5084 = (3 : ZMod 444482741) ^ (2542 + 2542) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 2542 * (3 : ZMod 444482741) ^ 2542 := by rw [pow_add]
          _ = 34895839 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 444482741) ^ 10168 = 438822609 := by
        calc
          (3 : ZMod 444482741) ^ 10168 = (3 : ZMod 444482741) ^ (5084 + 5084) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 5084 * (3 : ZMod 444482741) ^ 5084 := by rw [pow_add]
          _ = 438822609 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 444482741) ^ 20336 = 111734367 := by
        calc
          (3 : ZMod 444482741) ^ 20336 = (3 : ZMod 444482741) ^ (10168 + 10168) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 10168 * (3 : ZMod 444482741) ^ 10168 := by rw [pow_add]
          _ = 111734367 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 444482741) ^ 40673 = 190764769 := by
        calc
          (3 : ZMod 444482741) ^ 40673 = (3 : ZMod 444482741) ^ (20336 + 20336 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 20336 * (3 : ZMod 444482741) ^ 20336) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 190764769 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 444482741) ^ 81347 = 8370827 := by
        calc
          (3 : ZMod 444482741) ^ 81347 = (3 : ZMod 444482741) ^ (40673 + 40673 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 40673 * (3 : ZMod 444482741) ^ 40673) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 8370827 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 444482741) ^ 162695 = 344394211 := by
        calc
          (3 : ZMod 444482741) ^ 162695 = (3 : ZMod 444482741) ^ (81347 + 81347 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 81347 * (3 : ZMod 444482741) ^ 81347) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 344394211 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 444482741) ^ 325390 = 46418626 := by
        calc
          (3 : ZMod 444482741) ^ 325390 = (3 : ZMod 444482741) ^ (162695 + 162695) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 162695 * (3 : ZMod 444482741) ^ 162695 := by rw [pow_add]
          _ = 46418626 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 444482741) ^ 650780 = 81008564 := by
        calc
          (3 : ZMod 444482741) ^ 650780 = (3 : ZMod 444482741) ^ (325390 + 325390) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 325390 * (3 : ZMod 444482741) ^ 325390 := by rw [pow_add]
          _ = 81008564 := by rw [factor_3_18]; decide
      change (3 : ZMod 444482741) ^ 650780 ≠ 1
      rw [factor_3_19]
      decide
    ·
      have factor_4_0 : (3 : ZMod 444482741) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 444482741) ^ 2 = 9 := by
        calc
          (3 : ZMod 444482741) ^ 2 = (3 : ZMod 444482741) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 1 * (3 : ZMod 444482741) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 444482741) ^ 5 = 243 := by
        calc
          (3 : ZMod 444482741) ^ 5 = (3 : ZMod 444482741) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 2 * (3 : ZMod 444482741) ^ 2) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 444482741) ^ 10 = 59049 := by
        calc
          (3 : ZMod 444482741) ^ 10 = (3 : ZMod 444482741) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 5 * (3 : ZMod 444482741) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 444482741) ^ 21 = 237250160 := by
        calc
          (3 : ZMod 444482741) ^ 21 = (3 : ZMod 444482741) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 10 * (3 : ZMod 444482741) ^ 10) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 237250160 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 444482741) ^ 43 = 282952957 := by
        calc
          (3 : ZMod 444482741) ^ 43 = (3 : ZMod 444482741) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 21 * (3 : ZMod 444482741) ^ 21) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 282952957 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 444482741) ^ 86 = 381381265 := by
        calc
          (3 : ZMod 444482741) ^ 86 = (3 : ZMod 444482741) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 43 * (3 : ZMod 444482741) ^ 43 := by rw [pow_add]
          _ = 381381265 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 444482741) ^ 173 = 51964259 := by
        calc
          (3 : ZMod 444482741) ^ 173 = (3 : ZMod 444482741) ^ (86 + 86 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 86 * (3 : ZMod 444482741) ^ 86) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 51964259 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 444482741) ^ 346 = 1846125 := by
        calc
          (3 : ZMod 444482741) ^ 346 = (3 : ZMod 444482741) ^ (173 + 173) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 173 * (3 : ZMod 444482741) ^ 173 := by rw [pow_add]
          _ = 1846125 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 444482741) ^ 693 = 96055652 := by
        calc
          (3 : ZMod 444482741) ^ 693 = (3 : ZMod 444482741) ^ (346 + 346 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 346 * (3 : ZMod 444482741) ^ 346) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 96055652 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 444482741) ^ 1387 = 378346073 := by
        calc
          (3 : ZMod 444482741) ^ 1387 = (3 : ZMod 444482741) ^ (693 + 693 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 693 * (3 : ZMod 444482741) ^ 693) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 378346073 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 444482741) ^ 2774 = 208233280 := by
        calc
          (3 : ZMod 444482741) ^ 2774 = (3 : ZMod 444482741) ^ (1387 + 1387) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 1387 * (3 : ZMod 444482741) ^ 1387 := by rw [pow_add]
          _ = 208233280 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 444482741) ^ 5549 = 300067741 := by
        calc
          (3 : ZMod 444482741) ^ 5549 = (3 : ZMod 444482741) ^ (2774 + 2774 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 2774 * (3 : ZMod 444482741) ^ 2774) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 300067741 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 444482741) ^ 11098 = 191095376 := by
        calc
          (3 : ZMod 444482741) ^ 11098 = (3 : ZMod 444482741) ^ (5549 + 5549) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 5549 * (3 : ZMod 444482741) ^ 5549 := by rw [pow_add]
          _ = 191095376 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 444482741) ^ 22197 = 287362628 := by
        calc
          (3 : ZMod 444482741) ^ 22197 = (3 : ZMod 444482741) ^ (11098 + 11098 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 11098 * (3 : ZMod 444482741) ^ 11098) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 287362628 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 444482741) ^ 44395 = 269928178 := by
        calc
          (3 : ZMod 444482741) ^ 44395 = (3 : ZMod 444482741) ^ (22197 + 22197 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = ((3 : ZMod 444482741) ^ 22197 * (3 : ZMod 444482741) ^ 22197) * (3 : ZMod 444482741) := by rw [pow_succ, pow_add]
          _ = 269928178 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 444482741) ^ 88790 = 12709041 := by
        calc
          (3 : ZMod 444482741) ^ 88790 = (3 : ZMod 444482741) ^ (44395 + 44395) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 44395 * (3 : ZMod 444482741) ^ 44395 := by rw [pow_add]
          _ = 12709041 := by rw [factor_4_15]; decide
      have factor_4_17 : (3 : ZMod 444482741) ^ 177580 = 28853173 := by
        calc
          (3 : ZMod 444482741) ^ 177580 = (3 : ZMod 444482741) ^ (88790 + 88790) :=
            congrArg (fun n : ℕ => (3 : ZMod 444482741) ^ n) (by norm_num)
          _ = (3 : ZMod 444482741) ^ 88790 * (3 : ZMod 444482741) ^ 88790 := by rw [pow_add]
          _ = 28853173 := by rw [factor_4_16]; decide
      change (3 : ZMod 444482741) ^ 177580 ≠ 1
      rw [factor_4_17]
      decide

#print axioms prime_lucas_444482741

end TotientTailPeriodKiller
end Erdos249257
