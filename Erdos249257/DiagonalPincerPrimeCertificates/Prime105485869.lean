import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_105485869 : Nat.Prime 105485869 := by
  apply lucas_primality 105485869 (2 : ZMod 105485869)
  ·
      have fermat_0 : (2 : ZMod 105485869) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 105485869) ^ 3 = 8 := by
        calc
          (2 : ZMod 105485869) ^ 3 = (2 : ZMod 105485869) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 1 * (2 : ZMod 105485869) ^ 1) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 105485869) ^ 6 = 64 := by
        calc
          (2 : ZMod 105485869) ^ 6 = (2 : ZMod 105485869) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 3 * (2 : ZMod 105485869) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 105485869) ^ 12 = 4096 := by
        calc
          (2 : ZMod 105485869) ^ 12 = (2 : ZMod 105485869) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 6 * (2 : ZMod 105485869) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 105485869) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 105485869) ^ 25 = (2 : ZMod 105485869) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 12 * (2 : ZMod 105485869) ^ 12) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 105485869) ^ 50 = 70590670 := by
        calc
          (2 : ZMod 105485869) ^ 50 = (2 : ZMod 105485869) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 25 * (2 : ZMod 105485869) ^ 25 := by rw [pow_add]
          _ = 70590670 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 105485869) ^ 100 = 50278529 := by
        calc
          (2 : ZMod 105485869) ^ 100 = (2 : ZMod 105485869) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 50 * (2 : ZMod 105485869) ^ 50 := by rw [pow_add]
          _ = 50278529 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 105485869) ^ 201 = 49350314 := by
        calc
          (2 : ZMod 105485869) ^ 201 = (2 : ZMod 105485869) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 100 * (2 : ZMod 105485869) ^ 100) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 49350314 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 105485869) ^ 402 = 73347225 := by
        calc
          (2 : ZMod 105485869) ^ 402 = (2 : ZMod 105485869) ^ (201 + 201) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 201 * (2 : ZMod 105485869) ^ 201 := by rw [pow_add]
          _ = 73347225 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 105485869) ^ 804 = 20033427 := by
        calc
          (2 : ZMod 105485869) ^ 804 = (2 : ZMod 105485869) ^ (402 + 402) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 402 * (2 : ZMod 105485869) ^ 402 := by rw [pow_add]
          _ = 20033427 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 105485869) ^ 1609 = 29114364 := by
        calc
          (2 : ZMod 105485869) ^ 1609 = (2 : ZMod 105485869) ^ (804 + 804 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 804 * (2 : ZMod 105485869) ^ 804) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 29114364 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 105485869) ^ 3219 = 78421886 := by
        calc
          (2 : ZMod 105485869) ^ 3219 = (2 : ZMod 105485869) ^ (1609 + 1609 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 1609 * (2 : ZMod 105485869) ^ 1609) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 78421886 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 105485869) ^ 6438 = 6339190 := by
        calc
          (2 : ZMod 105485869) ^ 6438 = (2 : ZMod 105485869) ^ (3219 + 3219) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 3219 * (2 : ZMod 105485869) ^ 3219 := by rw [pow_add]
          _ = 6339190 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 105485869) ^ 12876 = 66117074 := by
        calc
          (2 : ZMod 105485869) ^ 12876 = (2 : ZMod 105485869) ^ (6438 + 6438) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 6438 * (2 : ZMod 105485869) ^ 6438 := by rw [pow_add]
          _ = 66117074 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 105485869) ^ 25753 = 90561334 := by
        calc
          (2 : ZMod 105485869) ^ 25753 = (2 : ZMod 105485869) ^ (12876 + 12876 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 12876 * (2 : ZMod 105485869) ^ 12876) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 90561334 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 105485869) ^ 51506 = 104674943 := by
        calc
          (2 : ZMod 105485869) ^ 51506 = (2 : ZMod 105485869) ^ (25753 + 25753) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 25753 * (2 : ZMod 105485869) ^ 25753 := by rw [pow_add]
          _ = 104674943 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 105485869) ^ 103013 = 4140260 := by
        calc
          (2 : ZMod 105485869) ^ 103013 = (2 : ZMod 105485869) ^ (51506 + 51506 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 51506 * (2 : ZMod 105485869) ^ 51506) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 4140260 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 105485869) ^ 206027 = 70880855 := by
        calc
          (2 : ZMod 105485869) ^ 206027 = (2 : ZMod 105485869) ^ (103013 + 103013 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 103013 * (2 : ZMod 105485869) ^ 103013) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 70880855 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 105485869) ^ 412054 = 79749103 := by
        calc
          (2 : ZMod 105485869) ^ 412054 = (2 : ZMod 105485869) ^ (206027 + 206027) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 206027 * (2 : ZMod 105485869) ^ 206027 := by rw [pow_add]
          _ = 79749103 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 105485869) ^ 824108 = 14921641 := by
        calc
          (2 : ZMod 105485869) ^ 824108 = (2 : ZMod 105485869) ^ (412054 + 412054) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 412054 * (2 : ZMod 105485869) ^ 412054 := by rw [pow_add]
          _ = 14921641 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 105485869) ^ 1648216 = 17282441 := by
        calc
          (2 : ZMod 105485869) ^ 1648216 = (2 : ZMod 105485869) ^ (824108 + 824108) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 824108 * (2 : ZMod 105485869) ^ 824108 := by rw [pow_add]
          _ = 17282441 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 105485869) ^ 3296433 = 7062783 := by
        calc
          (2 : ZMod 105485869) ^ 3296433 = (2 : ZMod 105485869) ^ (1648216 + 1648216 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 1648216 * (2 : ZMod 105485869) ^ 1648216) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 7062783 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 105485869) ^ 6592866 = 7571286 := by
        calc
          (2 : ZMod 105485869) ^ 6592866 = (2 : ZMod 105485869) ^ (3296433 + 3296433) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 3296433 * (2 : ZMod 105485869) ^ 3296433 := by rw [pow_add]
          _ = 7571286 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 105485869) ^ 13185733 = 55348645 := by
        calc
          (2 : ZMod 105485869) ^ 13185733 = (2 : ZMod 105485869) ^ (6592866 + 6592866 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 6592866 * (2 : ZMod 105485869) ^ 6592866) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 55348645 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 105485869) ^ 26371467 = 100274447 := by
        calc
          (2 : ZMod 105485869) ^ 26371467 = (2 : ZMod 105485869) ^ (13185733 + 13185733 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 13185733 * (2 : ZMod 105485869) ^ 13185733) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 100274447 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 105485869) ^ 52742934 = 105485868 := by
        calc
          (2 : ZMod 105485869) ^ 52742934 = (2 : ZMod 105485869) ^ (26371467 + 26371467) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 26371467 * (2 : ZMod 105485869) ^ 26371467 := by rw [pow_add]
          _ = 105485868 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 105485869) ^ 105485868 = 1 := by
        calc
          (2 : ZMod 105485869) ^ 105485868 = (2 : ZMod 105485869) ^ (52742934 + 52742934) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 52742934 * (2 : ZMod 105485869) ^ 52742934 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (976721, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (976721, 1)] : List FactorBlock).map factorBlockValue).prod = 105485869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 105485869) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 105485869) ^ 3 = 8 := by
        calc
          (2 : ZMod 105485869) ^ 3 = (2 : ZMod 105485869) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 1 * (2 : ZMod 105485869) ^ 1) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 105485869) ^ 6 = 64 := by
        calc
          (2 : ZMod 105485869) ^ 6 = (2 : ZMod 105485869) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 3 * (2 : ZMod 105485869) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 105485869) ^ 12 = 4096 := by
        calc
          (2 : ZMod 105485869) ^ 12 = (2 : ZMod 105485869) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 6 * (2 : ZMod 105485869) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 105485869) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 105485869) ^ 25 = (2 : ZMod 105485869) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 12 * (2 : ZMod 105485869) ^ 12) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 105485869) ^ 50 = 70590670 := by
        calc
          (2 : ZMod 105485869) ^ 50 = (2 : ZMod 105485869) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 25 * (2 : ZMod 105485869) ^ 25 := by rw [pow_add]
          _ = 70590670 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 105485869) ^ 100 = 50278529 := by
        calc
          (2 : ZMod 105485869) ^ 100 = (2 : ZMod 105485869) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 50 * (2 : ZMod 105485869) ^ 50 := by rw [pow_add]
          _ = 50278529 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 105485869) ^ 201 = 49350314 := by
        calc
          (2 : ZMod 105485869) ^ 201 = (2 : ZMod 105485869) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 100 * (2 : ZMod 105485869) ^ 100) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 49350314 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 105485869) ^ 402 = 73347225 := by
        calc
          (2 : ZMod 105485869) ^ 402 = (2 : ZMod 105485869) ^ (201 + 201) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 201 * (2 : ZMod 105485869) ^ 201 := by rw [pow_add]
          _ = 73347225 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 105485869) ^ 804 = 20033427 := by
        calc
          (2 : ZMod 105485869) ^ 804 = (2 : ZMod 105485869) ^ (402 + 402) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 402 * (2 : ZMod 105485869) ^ 402 := by rw [pow_add]
          _ = 20033427 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 105485869) ^ 1609 = 29114364 := by
        calc
          (2 : ZMod 105485869) ^ 1609 = (2 : ZMod 105485869) ^ (804 + 804 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 804 * (2 : ZMod 105485869) ^ 804) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 29114364 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 105485869) ^ 3219 = 78421886 := by
        calc
          (2 : ZMod 105485869) ^ 3219 = (2 : ZMod 105485869) ^ (1609 + 1609 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 1609 * (2 : ZMod 105485869) ^ 1609) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 78421886 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 105485869) ^ 6438 = 6339190 := by
        calc
          (2 : ZMod 105485869) ^ 6438 = (2 : ZMod 105485869) ^ (3219 + 3219) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 3219 * (2 : ZMod 105485869) ^ 3219 := by rw [pow_add]
          _ = 6339190 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 105485869) ^ 12876 = 66117074 := by
        calc
          (2 : ZMod 105485869) ^ 12876 = (2 : ZMod 105485869) ^ (6438 + 6438) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 6438 * (2 : ZMod 105485869) ^ 6438 := by rw [pow_add]
          _ = 66117074 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 105485869) ^ 25753 = 90561334 := by
        calc
          (2 : ZMod 105485869) ^ 25753 = (2 : ZMod 105485869) ^ (12876 + 12876 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 12876 * (2 : ZMod 105485869) ^ 12876) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 90561334 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 105485869) ^ 51506 = 104674943 := by
        calc
          (2 : ZMod 105485869) ^ 51506 = (2 : ZMod 105485869) ^ (25753 + 25753) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 25753 * (2 : ZMod 105485869) ^ 25753 := by rw [pow_add]
          _ = 104674943 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 105485869) ^ 103013 = 4140260 := by
        calc
          (2 : ZMod 105485869) ^ 103013 = (2 : ZMod 105485869) ^ (51506 + 51506 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 51506 * (2 : ZMod 105485869) ^ 51506) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 4140260 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 105485869) ^ 206027 = 70880855 := by
        calc
          (2 : ZMod 105485869) ^ 206027 = (2 : ZMod 105485869) ^ (103013 + 103013 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 103013 * (2 : ZMod 105485869) ^ 103013) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 70880855 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 105485869) ^ 412054 = 79749103 := by
        calc
          (2 : ZMod 105485869) ^ 412054 = (2 : ZMod 105485869) ^ (206027 + 206027) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 206027 * (2 : ZMod 105485869) ^ 206027 := by rw [pow_add]
          _ = 79749103 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 105485869) ^ 824108 = 14921641 := by
        calc
          (2 : ZMod 105485869) ^ 824108 = (2 : ZMod 105485869) ^ (412054 + 412054) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 412054 * (2 : ZMod 105485869) ^ 412054 := by rw [pow_add]
          _ = 14921641 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 105485869) ^ 1648216 = 17282441 := by
        calc
          (2 : ZMod 105485869) ^ 1648216 = (2 : ZMod 105485869) ^ (824108 + 824108) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 824108 * (2 : ZMod 105485869) ^ 824108 := by rw [pow_add]
          _ = 17282441 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 105485869) ^ 3296433 = 7062783 := by
        calc
          (2 : ZMod 105485869) ^ 3296433 = (2 : ZMod 105485869) ^ (1648216 + 1648216 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 1648216 * (2 : ZMod 105485869) ^ 1648216) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 7062783 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 105485869) ^ 6592866 = 7571286 := by
        calc
          (2 : ZMod 105485869) ^ 6592866 = (2 : ZMod 105485869) ^ (3296433 + 3296433) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 3296433 * (2 : ZMod 105485869) ^ 3296433 := by rw [pow_add]
          _ = 7571286 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 105485869) ^ 13185733 = 55348645 := by
        calc
          (2 : ZMod 105485869) ^ 13185733 = (2 : ZMod 105485869) ^ (6592866 + 6592866 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 6592866 * (2 : ZMod 105485869) ^ 6592866) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 55348645 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 105485869) ^ 26371467 = 100274447 := by
        calc
          (2 : ZMod 105485869) ^ 26371467 = (2 : ZMod 105485869) ^ (13185733 + 13185733 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 13185733 * (2 : ZMod 105485869) ^ 13185733) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 100274447 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 105485869) ^ 52742934 = 105485868 := by
        calc
          (2 : ZMod 105485869) ^ 52742934 = (2 : ZMod 105485869) ^ (26371467 + 26371467) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 26371467 * (2 : ZMod 105485869) ^ 26371467 := by rw [pow_add]
          _ = 105485868 := by rw [factor_0_24]; decide
      change (2 : ZMod 105485869) ^ 52742934 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (2 : ZMod 105485869) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 105485869) ^ 2 = 4 := by
        calc
          (2 : ZMod 105485869) ^ 2 = (2 : ZMod 105485869) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 1 * (2 : ZMod 105485869) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 105485869) ^ 4 = 16 := by
        calc
          (2 : ZMod 105485869) ^ 4 = (2 : ZMod 105485869) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 2 * (2 : ZMod 105485869) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 105485869) ^ 8 = 256 := by
        calc
          (2 : ZMod 105485869) ^ 8 = (2 : ZMod 105485869) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 4 * (2 : ZMod 105485869) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 105485869) ^ 16 = 65536 := by
        calc
          (2 : ZMod 105485869) ^ 16 = (2 : ZMod 105485869) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 8 * (2 : ZMod 105485869) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 105485869) ^ 33 = 45579203 := by
        calc
          (2 : ZMod 105485869) ^ 33 = (2 : ZMod 105485869) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 16 * (2 : ZMod 105485869) ^ 16) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 45579203 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 105485869) ^ 67 = 83756512 := by
        calc
          (2 : ZMod 105485869) ^ 67 = (2 : ZMod 105485869) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 33 * (2 : ZMod 105485869) ^ 33) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 83756512 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 105485869) ^ 134 = 79346025 := by
        calc
          (2 : ZMod 105485869) ^ 134 = (2 : ZMod 105485869) ^ (67 + 67) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 67 * (2 : ZMod 105485869) ^ 67 := by rw [pow_add]
          _ = 79346025 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 105485869) ^ 268 = 82287089 := by
        calc
          (2 : ZMod 105485869) ^ 268 = (2 : ZMod 105485869) ^ (134 + 134) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 134 * (2 : ZMod 105485869) ^ 134 := by rw [pow_add]
          _ = 82287089 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 105485869) ^ 536 = 80601457 := by
        calc
          (2 : ZMod 105485869) ^ 536 = (2 : ZMod 105485869) ^ (268 + 268) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 268 * (2 : ZMod 105485869) ^ 268 := by rw [pow_add]
          _ = 80601457 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 105485869) ^ 1073 = 160743 := by
        calc
          (2 : ZMod 105485869) ^ 1073 = (2 : ZMod 105485869) ^ (536 + 536 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 536 * (2 : ZMod 105485869) ^ 536) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 160743 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 105485869) ^ 2146 = 99760013 := by
        calc
          (2 : ZMod 105485869) ^ 2146 = (2 : ZMod 105485869) ^ (1073 + 1073) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 1073 * (2 : ZMod 105485869) ^ 1073 := by rw [pow_add]
          _ = 99760013 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 105485869) ^ 4292 = 102389929 := by
        calc
          (2 : ZMod 105485869) ^ 4292 = (2 : ZMod 105485869) ^ (2146 + 2146) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 2146 * (2 : ZMod 105485869) ^ 2146 := by rw [pow_add]
          _ = 102389929 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 105485869) ^ 8584 = 81968653 := by
        calc
          (2 : ZMod 105485869) ^ 8584 = (2 : ZMod 105485869) ^ (4292 + 4292) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 4292 * (2 : ZMod 105485869) ^ 4292 := by rw [pow_add]
          _ = 81968653 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 105485869) ^ 17168 = 96313857 := by
        calc
          (2 : ZMod 105485869) ^ 17168 = (2 : ZMod 105485869) ^ (8584 + 8584) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 8584 * (2 : ZMod 105485869) ^ 8584 := by rw [pow_add]
          _ = 96313857 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 105485869) ^ 34337 = 64913253 := by
        calc
          (2 : ZMod 105485869) ^ 34337 = (2 : ZMod 105485869) ^ (17168 + 17168 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 17168 * (2 : ZMod 105485869) ^ 17168) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 64913253 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 105485869) ^ 68675 = 28759844 := by
        calc
          (2 : ZMod 105485869) ^ 68675 = (2 : ZMod 105485869) ^ (34337 + 34337 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 34337 * (2 : ZMod 105485869) ^ 34337) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 28759844 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 105485869) ^ 137351 = 7881256 := by
        calc
          (2 : ZMod 105485869) ^ 137351 = (2 : ZMod 105485869) ^ (68675 + 68675 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 68675 * (2 : ZMod 105485869) ^ 68675) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 7881256 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 105485869) ^ 274702 = 2521445 := by
        calc
          (2 : ZMod 105485869) ^ 274702 = (2 : ZMod 105485869) ^ (137351 + 137351) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 137351 * (2 : ZMod 105485869) ^ 137351 := by rw [pow_add]
          _ = 2521445 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 105485869) ^ 549405 = 103126790 := by
        calc
          (2 : ZMod 105485869) ^ 549405 = (2 : ZMod 105485869) ^ (274702 + 274702 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 274702 * (2 : ZMod 105485869) ^ 274702) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 103126790 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 105485869) ^ 1098811 = 60503078 := by
        calc
          (2 : ZMod 105485869) ^ 1098811 = (2 : ZMod 105485869) ^ (549405 + 549405 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 549405 * (2 : ZMod 105485869) ^ 549405) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 60503078 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 105485869) ^ 2197622 = 27874405 := by
        calc
          (2 : ZMod 105485869) ^ 2197622 = (2 : ZMod 105485869) ^ (1098811 + 1098811) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 1098811 * (2 : ZMod 105485869) ^ 1098811 := by rw [pow_add]
          _ = 27874405 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 105485869) ^ 4395244 = 20003144 := by
        calc
          (2 : ZMod 105485869) ^ 4395244 = (2 : ZMod 105485869) ^ (2197622 + 2197622) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 2197622 * (2 : ZMod 105485869) ^ 2197622 := by rw [pow_add]
          _ = 20003144 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 105485869) ^ 8790489 = 83311750 := by
        calc
          (2 : ZMod 105485869) ^ 8790489 = (2 : ZMod 105485869) ^ (4395244 + 4395244 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 4395244 * (2 : ZMod 105485869) ^ 4395244) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 83311750 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 105485869) ^ 17580978 = 82442278 := by
        calc
          (2 : ZMod 105485869) ^ 17580978 = (2 : ZMod 105485869) ^ (8790489 + 8790489) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 8790489 * (2 : ZMod 105485869) ^ 8790489 := by rw [pow_add]
          _ = 82442278 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 105485869) ^ 35161956 = 82442277 := by
        calc
          (2 : ZMod 105485869) ^ 35161956 = (2 : ZMod 105485869) ^ (17580978 + 17580978) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 17580978 * (2 : ZMod 105485869) ^ 17580978 := by rw [pow_add]
          _ = 82442277 := by rw [factor_1_24]; decide
      change (2 : ZMod 105485869) ^ 35161956 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (2 : ZMod 105485869) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 105485869) ^ 3 = 8 := by
        calc
          (2 : ZMod 105485869) ^ 3 = (2 : ZMod 105485869) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 1 * (2 : ZMod 105485869) ^ 1) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 105485869) ^ 6 = 64 := by
        calc
          (2 : ZMod 105485869) ^ 6 = (2 : ZMod 105485869) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 3 * (2 : ZMod 105485869) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 105485869) ^ 13 = 8192 := by
        calc
          (2 : ZMod 105485869) ^ 13 = (2 : ZMod 105485869) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 6 * (2 : ZMod 105485869) ^ 6) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 105485869) ^ 27 = 28731859 := by
        calc
          (2 : ZMod 105485869) ^ 27 = (2 : ZMod 105485869) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = ((2 : ZMod 105485869) ^ 13 * (2 : ZMod 105485869) ^ 13) * (2 : ZMod 105485869) := by rw [pow_succ, pow_add]
          _ = 28731859 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 105485869) ^ 54 = 74592030 := by
        calc
          (2 : ZMod 105485869) ^ 54 = (2 : ZMod 105485869) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 27 * (2 : ZMod 105485869) ^ 27 := by rw [pow_add]
          _ = 74592030 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 105485869) ^ 108 = 2027406 := by
        calc
          (2 : ZMod 105485869) ^ 108 = (2 : ZMod 105485869) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (2 : ZMod 105485869) ^ n) (by norm_num)
          _ = (2 : ZMod 105485869) ^ 54 * (2 : ZMod 105485869) ^ 54 := by rw [pow_add]
          _ = 2027406 := by rw [factor_2_5]; decide
      change (2 : ZMod 105485869) ^ 108 ≠ 1
      rw [factor_2_6]
      decide

#print axioms prime_lucas_105485869

end TotientTailPeriodKiller
end Erdos249257
