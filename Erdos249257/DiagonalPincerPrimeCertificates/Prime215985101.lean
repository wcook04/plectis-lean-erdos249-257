import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_215985101 : Nat.Prime 215985101 := by
  apply lucas_primality 215985101 (2 : ZMod 215985101)
  ·
      have fermat_0 : (2 : ZMod 215985101) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 215985101) ^ 3 = 8 := by
        calc
          (2 : ZMod 215985101) ^ 3 = (2 : ZMod 215985101) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 1 * (2 : ZMod 215985101) ^ 1) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 215985101) ^ 6 = 64 := by
        calc
          (2 : ZMod 215985101) ^ 6 = (2 : ZMod 215985101) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 3 * (2 : ZMod 215985101) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 215985101) ^ 12 = 4096 := by
        calc
          (2 : ZMod 215985101) ^ 12 = (2 : ZMod 215985101) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 6 * (2 : ZMod 215985101) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 215985101) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 215985101) ^ 25 = (2 : ZMod 215985101) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 12 * (2 : ZMod 215985101) ^ 12) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 215985101) ^ 51 = 58457730 := by
        calc
          (2 : ZMod 215985101) ^ 51 = (2 : ZMod 215985101) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 25 * (2 : ZMod 215985101) ^ 25) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 58457730 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 215985101) ^ 102 = 80030647 := by
        calc
          (2 : ZMod 215985101) ^ 102 = (2 : ZMod 215985101) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 51 * (2 : ZMod 215985101) ^ 51 := by rw [pow_add]
          _ = 80030647 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 215985101) ^ 205 = 183707357 := by
        calc
          (2 : ZMod 215985101) ^ 205 = (2 : ZMod 215985101) ^ (102 + 102 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 102 * (2 : ZMod 215985101) ^ 102) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 183707357 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 215985101) ^ 411 = 52816622 := by
        calc
          (2 : ZMod 215985101) ^ 411 = (2 : ZMod 215985101) ^ (205 + 205 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 205 * (2 : ZMod 215985101) ^ 205) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 52816622 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 215985101) ^ 823 = 60563398 := by
        calc
          (2 : ZMod 215985101) ^ 823 = (2 : ZMod 215985101) ^ (411 + 411 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 411 * (2 : ZMod 215985101) ^ 411) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 60563398 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 215985101) ^ 1647 = 201366996 := by
        calc
          (2 : ZMod 215985101) ^ 1647 = (2 : ZMod 215985101) ^ (823 + 823 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 823 * (2 : ZMod 215985101) ^ 823) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 201366996 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 215985101) ^ 3295 = 60799512 := by
        calc
          (2 : ZMod 215985101) ^ 3295 = (2 : ZMod 215985101) ^ (1647 + 1647 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 1647 * (2 : ZMod 215985101) ^ 1647) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 60799512 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 215985101) ^ 6591 = 167035429 := by
        calc
          (2 : ZMod 215985101) ^ 6591 = (2 : ZMod 215985101) ^ (3295 + 3295 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 3295 * (2 : ZMod 215985101) ^ 3295) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 167035429 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 215985101) ^ 13182 = 145690601 := by
        calc
          (2 : ZMod 215985101) ^ 13182 = (2 : ZMod 215985101) ^ (6591 + 6591) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 6591 * (2 : ZMod 215985101) ^ 6591 := by rw [pow_add]
          _ = 145690601 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 215985101) ^ 26365 = 172455112 := by
        calc
          (2 : ZMod 215985101) ^ 26365 = (2 : ZMod 215985101) ^ (13182 + 13182 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 13182 * (2 : ZMod 215985101) ^ 13182) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 172455112 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 215985101) ^ 52730 = 188816617 := by
        calc
          (2 : ZMod 215985101) ^ 52730 = (2 : ZMod 215985101) ^ (26365 + 26365) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 26365 * (2 : ZMod 215985101) ^ 26365 := by rw [pow_add]
          _ = 188816617 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 215985101) ^ 105461 = 64023936 := by
        calc
          (2 : ZMod 215985101) ^ 105461 = (2 : ZMod 215985101) ^ (52730 + 52730 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 52730 * (2 : ZMod 215985101) ^ 52730) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 64023936 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 215985101) ^ 210922 = 212977838 := by
        calc
          (2 : ZMod 215985101) ^ 210922 = (2 : ZMod 215985101) ^ (105461 + 105461) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 105461 * (2 : ZMod 215985101) ^ 105461 := by rw [pow_add]
          _ = 212977838 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 215985101) ^ 421845 = 21189295 := by
        calc
          (2 : ZMod 215985101) ^ 421845 = (2 : ZMod 215985101) ^ (210922 + 210922 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 210922 * (2 : ZMod 215985101) ^ 210922) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 21189295 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 215985101) ^ 843691 = 132769884 := by
        calc
          (2 : ZMod 215985101) ^ 843691 = (2 : ZMod 215985101) ^ (421845 + 421845 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 421845 * (2 : ZMod 215985101) ^ 421845) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 132769884 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 215985101) ^ 1687383 = 84597993 := by
        calc
          (2 : ZMod 215985101) ^ 1687383 = (2 : ZMod 215985101) ^ (843691 + 843691 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 843691 * (2 : ZMod 215985101) ^ 843691) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 84597993 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 215985101) ^ 3374767 = 201232072 := by
        calc
          (2 : ZMod 215985101) ^ 3374767 = (2 : ZMod 215985101) ^ (1687383 + 1687383 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 1687383 * (2 : ZMod 215985101) ^ 1687383) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 201232072 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 215985101) ^ 6749534 = 6650424 := by
        calc
          (2 : ZMod 215985101) ^ 6749534 = (2 : ZMod 215985101) ^ (3374767 + 3374767) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 3374767 * (2 : ZMod 215985101) ^ 3374767 := by rw [pow_add]
          _ = 6650424 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 215985101) ^ 13499068 = 6307602 := by
        calc
          (2 : ZMod 215985101) ^ 13499068 = (2 : ZMod 215985101) ^ (6749534 + 6749534) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 6749534 * (2 : ZMod 215985101) ^ 6749534 := by rw [pow_add]
          _ = 6307602 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 215985101) ^ 26998137 = 182951196 := by
        calc
          (2 : ZMod 215985101) ^ 26998137 = (2 : ZMod 215985101) ^ (13499068 + 13499068 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 13499068 * (2 : ZMod 215985101) ^ 13499068) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 182951196 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 215985101) ^ 53996275 = 149917290 := by
        calc
          (2 : ZMod 215985101) ^ 53996275 = (2 : ZMod 215985101) ^ (26998137 + 26998137 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 26998137 * (2 : ZMod 215985101) ^ 26998137) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 149917290 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 215985101) ^ 107992550 = 215985100 := by
        calc
          (2 : ZMod 215985101) ^ 107992550 = (2 : ZMod 215985101) ^ (53996275 + 53996275) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 53996275 * (2 : ZMod 215985101) ^ 53996275 := by rw [pow_add]
          _ = 215985100 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 215985101) ^ 215985100 = 1 := by
        calc
          (2 : ZMod 215985101) ^ 215985100 = (2 : ZMod 215985101) ^ (107992550 + 107992550) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 107992550 * (2 : ZMod 215985101) ^ 107992550 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (73, 1), (29587, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (73, 1), (29587, 1)] : List FactorBlock).map factorBlockValue).prod = 215985101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 215985101) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 215985101) ^ 3 = 8 := by
        calc
          (2 : ZMod 215985101) ^ 3 = (2 : ZMod 215985101) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 1 * (2 : ZMod 215985101) ^ 1) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 215985101) ^ 6 = 64 := by
        calc
          (2 : ZMod 215985101) ^ 6 = (2 : ZMod 215985101) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 3 * (2 : ZMod 215985101) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 215985101) ^ 12 = 4096 := by
        calc
          (2 : ZMod 215985101) ^ 12 = (2 : ZMod 215985101) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 6 * (2 : ZMod 215985101) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 215985101) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 215985101) ^ 25 = (2 : ZMod 215985101) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 12 * (2 : ZMod 215985101) ^ 12) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 215985101) ^ 51 = 58457730 := by
        calc
          (2 : ZMod 215985101) ^ 51 = (2 : ZMod 215985101) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 25 * (2 : ZMod 215985101) ^ 25) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 58457730 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 215985101) ^ 102 = 80030647 := by
        calc
          (2 : ZMod 215985101) ^ 102 = (2 : ZMod 215985101) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 51 * (2 : ZMod 215985101) ^ 51 := by rw [pow_add]
          _ = 80030647 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 215985101) ^ 205 = 183707357 := by
        calc
          (2 : ZMod 215985101) ^ 205 = (2 : ZMod 215985101) ^ (102 + 102 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 102 * (2 : ZMod 215985101) ^ 102) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 183707357 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 215985101) ^ 411 = 52816622 := by
        calc
          (2 : ZMod 215985101) ^ 411 = (2 : ZMod 215985101) ^ (205 + 205 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 205 * (2 : ZMod 215985101) ^ 205) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 52816622 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 215985101) ^ 823 = 60563398 := by
        calc
          (2 : ZMod 215985101) ^ 823 = (2 : ZMod 215985101) ^ (411 + 411 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 411 * (2 : ZMod 215985101) ^ 411) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 60563398 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 215985101) ^ 1647 = 201366996 := by
        calc
          (2 : ZMod 215985101) ^ 1647 = (2 : ZMod 215985101) ^ (823 + 823 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 823 * (2 : ZMod 215985101) ^ 823) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 201366996 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 215985101) ^ 3295 = 60799512 := by
        calc
          (2 : ZMod 215985101) ^ 3295 = (2 : ZMod 215985101) ^ (1647 + 1647 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 1647 * (2 : ZMod 215985101) ^ 1647) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 60799512 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 215985101) ^ 6591 = 167035429 := by
        calc
          (2 : ZMod 215985101) ^ 6591 = (2 : ZMod 215985101) ^ (3295 + 3295 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 3295 * (2 : ZMod 215985101) ^ 3295) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 167035429 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 215985101) ^ 13182 = 145690601 := by
        calc
          (2 : ZMod 215985101) ^ 13182 = (2 : ZMod 215985101) ^ (6591 + 6591) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 6591 * (2 : ZMod 215985101) ^ 6591 := by rw [pow_add]
          _ = 145690601 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 215985101) ^ 26365 = 172455112 := by
        calc
          (2 : ZMod 215985101) ^ 26365 = (2 : ZMod 215985101) ^ (13182 + 13182 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 13182 * (2 : ZMod 215985101) ^ 13182) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 172455112 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 215985101) ^ 52730 = 188816617 := by
        calc
          (2 : ZMod 215985101) ^ 52730 = (2 : ZMod 215985101) ^ (26365 + 26365) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 26365 * (2 : ZMod 215985101) ^ 26365 := by rw [pow_add]
          _ = 188816617 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 215985101) ^ 105461 = 64023936 := by
        calc
          (2 : ZMod 215985101) ^ 105461 = (2 : ZMod 215985101) ^ (52730 + 52730 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 52730 * (2 : ZMod 215985101) ^ 52730) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 64023936 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 215985101) ^ 210922 = 212977838 := by
        calc
          (2 : ZMod 215985101) ^ 210922 = (2 : ZMod 215985101) ^ (105461 + 105461) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 105461 * (2 : ZMod 215985101) ^ 105461 := by rw [pow_add]
          _ = 212977838 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 215985101) ^ 421845 = 21189295 := by
        calc
          (2 : ZMod 215985101) ^ 421845 = (2 : ZMod 215985101) ^ (210922 + 210922 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 210922 * (2 : ZMod 215985101) ^ 210922) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 21189295 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 215985101) ^ 843691 = 132769884 := by
        calc
          (2 : ZMod 215985101) ^ 843691 = (2 : ZMod 215985101) ^ (421845 + 421845 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 421845 * (2 : ZMod 215985101) ^ 421845) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 132769884 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 215985101) ^ 1687383 = 84597993 := by
        calc
          (2 : ZMod 215985101) ^ 1687383 = (2 : ZMod 215985101) ^ (843691 + 843691 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 843691 * (2 : ZMod 215985101) ^ 843691) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 84597993 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 215985101) ^ 3374767 = 201232072 := by
        calc
          (2 : ZMod 215985101) ^ 3374767 = (2 : ZMod 215985101) ^ (1687383 + 1687383 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 1687383 * (2 : ZMod 215985101) ^ 1687383) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 201232072 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 215985101) ^ 6749534 = 6650424 := by
        calc
          (2 : ZMod 215985101) ^ 6749534 = (2 : ZMod 215985101) ^ (3374767 + 3374767) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 3374767 * (2 : ZMod 215985101) ^ 3374767 := by rw [pow_add]
          _ = 6650424 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 215985101) ^ 13499068 = 6307602 := by
        calc
          (2 : ZMod 215985101) ^ 13499068 = (2 : ZMod 215985101) ^ (6749534 + 6749534) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 6749534 * (2 : ZMod 215985101) ^ 6749534 := by rw [pow_add]
          _ = 6307602 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 215985101) ^ 26998137 = 182951196 := by
        calc
          (2 : ZMod 215985101) ^ 26998137 = (2 : ZMod 215985101) ^ (13499068 + 13499068 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 13499068 * (2 : ZMod 215985101) ^ 13499068) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 182951196 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 215985101) ^ 53996275 = 149917290 := by
        calc
          (2 : ZMod 215985101) ^ 53996275 = (2 : ZMod 215985101) ^ (26998137 + 26998137 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 26998137 * (2 : ZMod 215985101) ^ 26998137) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 149917290 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 215985101) ^ 107992550 = 215985100 := by
        calc
          (2 : ZMod 215985101) ^ 107992550 = (2 : ZMod 215985101) ^ (53996275 + 53996275) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 53996275 * (2 : ZMod 215985101) ^ 53996275 := by rw [pow_add]
          _ = 215985100 := by rw [factor_0_25]; decide
      change (2 : ZMod 215985101) ^ 107992550 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (2 : ZMod 215985101) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 215985101) ^ 2 = 4 := by
        calc
          (2 : ZMod 215985101) ^ 2 = (2 : ZMod 215985101) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 1 * (2 : ZMod 215985101) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 215985101) ^ 5 = 32 := by
        calc
          (2 : ZMod 215985101) ^ 5 = (2 : ZMod 215985101) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 2 * (2 : ZMod 215985101) ^ 2) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 215985101) ^ 10 = 1024 := by
        calc
          (2 : ZMod 215985101) ^ 10 = (2 : ZMod 215985101) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 5 * (2 : ZMod 215985101) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 215985101) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 215985101) ^ 20 = (2 : ZMod 215985101) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 10 * (2 : ZMod 215985101) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 215985101) ^ 41 = 78942271 := by
        calc
          (2 : ZMod 215985101) ^ 41 = (2 : ZMod 215985101) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 20 * (2 : ZMod 215985101) ^ 20) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 78942271 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 215985101) ^ 82 = 99894545 := by
        calc
          (2 : ZMod 215985101) ^ 82 = (2 : ZMod 215985101) ^ (41 + 41) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 41 * (2 : ZMod 215985101) ^ 41 := by rw [pow_add]
          _ = 99894545 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 215985101) ^ 164 = 26731034 := by
        calc
          (2 : ZMod 215985101) ^ 164 = (2 : ZMod 215985101) ^ (82 + 82) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 82 * (2 : ZMod 215985101) ^ 82 := by rw [pow_add]
          _ = 26731034 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 215985101) ^ 329 = 50782369 := by
        calc
          (2 : ZMod 215985101) ^ 329 = (2 : ZMod 215985101) ^ (164 + 164 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 164 * (2 : ZMod 215985101) ^ 164) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 50782369 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 215985101) ^ 659 = 140806644 := by
        calc
          (2 : ZMod 215985101) ^ 659 = (2 : ZMod 215985101) ^ (329 + 329 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 329 * (2 : ZMod 215985101) ^ 329) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 140806644 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 215985101) ^ 1318 = 115183602 := by
        calc
          (2 : ZMod 215985101) ^ 1318 = (2 : ZMod 215985101) ^ (659 + 659) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 659 * (2 : ZMod 215985101) ^ 659 := by rw [pow_add]
          _ = 115183602 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 215985101) ^ 2636 = 14797957 := by
        calc
          (2 : ZMod 215985101) ^ 2636 = (2 : ZMod 215985101) ^ (1318 + 1318) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 1318 * (2 : ZMod 215985101) ^ 1318 := by rw [pow_add]
          _ = 14797957 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 215985101) ^ 5273 = 25867170 := by
        calc
          (2 : ZMod 215985101) ^ 5273 = (2 : ZMod 215985101) ^ (2636 + 2636 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 2636 * (2 : ZMod 215985101) ^ 2636) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 25867170 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 215985101) ^ 10546 = 88121253 := by
        calc
          (2 : ZMod 215985101) ^ 10546 = (2 : ZMod 215985101) ^ (5273 + 5273) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 5273 * (2 : ZMod 215985101) ^ 5273 := by rw [pow_add]
          _ = 88121253 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 215985101) ^ 21092 = 128987011 := by
        calc
          (2 : ZMod 215985101) ^ 21092 = (2 : ZMod 215985101) ^ (10546 + 10546) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 10546 * (2 : ZMod 215985101) ^ 10546 := by rw [pow_add]
          _ = 128987011 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 215985101) ^ 42184 = 42526055 := by
        calc
          (2 : ZMod 215985101) ^ 42184 = (2 : ZMod 215985101) ^ (21092 + 21092) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 21092 * (2 : ZMod 215985101) ^ 21092 := by rw [pow_add]
          _ = 42526055 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 215985101) ^ 84369 = 145419446 := by
        calc
          (2 : ZMod 215985101) ^ 84369 = (2 : ZMod 215985101) ^ (42184 + 42184 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 42184 * (2 : ZMod 215985101) ^ 42184) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 145419446 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 215985101) ^ 168738 = 310640 := by
        calc
          (2 : ZMod 215985101) ^ 168738 = (2 : ZMod 215985101) ^ (84369 + 84369) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 84369 * (2 : ZMod 215985101) ^ 84369 := by rw [pow_add]
          _ = 310640 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 215985101) ^ 337476 = 167854554 := by
        calc
          (2 : ZMod 215985101) ^ 337476 = (2 : ZMod 215985101) ^ (168738 + 168738) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 168738 * (2 : ZMod 215985101) ^ 168738 := by rw [pow_add]
          _ = 167854554 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 215985101) ^ 674953 = 115666206 := by
        calc
          (2 : ZMod 215985101) ^ 674953 = (2 : ZMod 215985101) ^ (337476 + 337476 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 337476 * (2 : ZMod 215985101) ^ 337476) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 115666206 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 215985101) ^ 1349906 = 52710371 := by
        calc
          (2 : ZMod 215985101) ^ 1349906 = (2 : ZMod 215985101) ^ (674953 + 674953) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 674953 * (2 : ZMod 215985101) ^ 674953 := by rw [pow_add]
          _ = 52710371 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 215985101) ^ 2699813 = 16608237 := by
        calc
          (2 : ZMod 215985101) ^ 2699813 = (2 : ZMod 215985101) ^ (1349906 + 1349906 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 1349906 * (2 : ZMod 215985101) ^ 1349906) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 16608237 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 215985101) ^ 5399627 = 87373148 := by
        calc
          (2 : ZMod 215985101) ^ 5399627 = (2 : ZMod 215985101) ^ (2699813 + 2699813 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 2699813 * (2 : ZMod 215985101) ^ 2699813) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 87373148 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 215985101) ^ 10799255 = 107316027 := by
        calc
          (2 : ZMod 215985101) ^ 10799255 = (2 : ZMod 215985101) ^ (5399627 + 5399627 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 5399627 * (2 : ZMod 215985101) ^ 5399627) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 107316027 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 215985101) ^ 21598510 = 173605859 := by
        calc
          (2 : ZMod 215985101) ^ 21598510 = (2 : ZMod 215985101) ^ (10799255 + 10799255) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 10799255 * (2 : ZMod 215985101) ^ 10799255 := by rw [pow_add]
          _ = 173605859 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 215985101) ^ 43197020 = 19475275 := by
        calc
          (2 : ZMod 215985101) ^ 43197020 = (2 : ZMod 215985101) ^ (21598510 + 21598510) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 21598510 * (2 : ZMod 215985101) ^ 21598510 := by rw [pow_add]
          _ = 19475275 := by rw [factor_1_24]; decide
      change (2 : ZMod 215985101) ^ 43197020 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (2 : ZMod 215985101) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 215985101) ^ 2 = 4 := by
        calc
          (2 : ZMod 215985101) ^ 2 = (2 : ZMod 215985101) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 1 * (2 : ZMod 215985101) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 215985101) ^ 5 = 32 := by
        calc
          (2 : ZMod 215985101) ^ 5 = (2 : ZMod 215985101) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 2 * (2 : ZMod 215985101) ^ 2) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 215985101) ^ 11 = 2048 := by
        calc
          (2 : ZMod 215985101) ^ 11 = (2 : ZMod 215985101) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 5 * (2 : ZMod 215985101) ^ 5) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 215985101) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 215985101) ^ 22 = (2 : ZMod 215985101) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 11 * (2 : ZMod 215985101) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 215985101) ^ 45 = 183150831 := by
        calc
          (2 : ZMod 215985101) ^ 45 = (2 : ZMod 215985101) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 22 * (2 : ZMod 215985101) ^ 22) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 183150831 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 215985101) ^ 90 = 86761602 := by
        calc
          (2 : ZMod 215985101) ^ 90 = (2 : ZMod 215985101) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 45 * (2 : ZMod 215985101) ^ 45 := by rw [pow_add]
          _ = 86761602 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 215985101) ^ 180 = 205875114 := by
        calc
          (2 : ZMod 215985101) ^ 180 = (2 : ZMod 215985101) ^ (90 + 90) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 90 * (2 : ZMod 215985101) ^ 90 := by rw [pow_add]
          _ = 205875114 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 215985101) ^ 361 = 39751767 := by
        calc
          (2 : ZMod 215985101) ^ 361 = (2 : ZMod 215985101) ^ (180 + 180 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 180 * (2 : ZMod 215985101) ^ 180) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 39751767 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 215985101) ^ 722 = 40565130 := by
        calc
          (2 : ZMod 215985101) ^ 722 = (2 : ZMod 215985101) ^ (361 + 361) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 361 * (2 : ZMod 215985101) ^ 361 := by rw [pow_add]
          _ = 40565130 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 215985101) ^ 1444 = 195196382 := by
        calc
          (2 : ZMod 215985101) ^ 1444 = (2 : ZMod 215985101) ^ (722 + 722) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 722 * (2 : ZMod 215985101) ^ 722 := by rw [pow_add]
          _ = 195196382 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 215985101) ^ 2889 = 186989365 := by
        calc
          (2 : ZMod 215985101) ^ 2889 = (2 : ZMod 215985101) ^ (1444 + 1444 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 1444 * (2 : ZMod 215985101) ^ 1444) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 186989365 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 215985101) ^ 5778 = 30654854 := by
        calc
          (2 : ZMod 215985101) ^ 5778 = (2 : ZMod 215985101) ^ (2889 + 2889) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 2889 * (2 : ZMod 215985101) ^ 2889 := by rw [pow_add]
          _ = 30654854 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 215985101) ^ 11557 = 2329720 := by
        calc
          (2 : ZMod 215985101) ^ 11557 = (2 : ZMod 215985101) ^ (5778 + 5778 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 5778 * (2 : ZMod 215985101) ^ 5778) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 2329720 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 215985101) ^ 23114 = 105675371 := by
        calc
          (2 : ZMod 215985101) ^ 23114 = (2 : ZMod 215985101) ^ (11557 + 11557) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 11557 * (2 : ZMod 215985101) ^ 11557 := by rw [pow_add]
          _ = 105675371 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 215985101) ^ 46229 = 186426372 := by
        calc
          (2 : ZMod 215985101) ^ 46229 = (2 : ZMod 215985101) ^ (23114 + 23114 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 23114 * (2 : ZMod 215985101) ^ 23114) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 186426372 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 215985101) ^ 92459 = 173191039 := by
        calc
          (2 : ZMod 215985101) ^ 92459 = (2 : ZMod 215985101) ^ (46229 + 46229 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 46229 * (2 : ZMod 215985101) ^ 46229) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 173191039 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 215985101) ^ 184918 = 118663672 := by
        calc
          (2 : ZMod 215985101) ^ 184918 = (2 : ZMod 215985101) ^ (92459 + 92459) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 92459 * (2 : ZMod 215985101) ^ 92459 := by rw [pow_add]
          _ = 118663672 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 215985101) ^ 369837 = 70393524 := by
        calc
          (2 : ZMod 215985101) ^ 369837 = (2 : ZMod 215985101) ^ (184918 + 184918 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 184918 * (2 : ZMod 215985101) ^ 184918) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 70393524 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 215985101) ^ 739675 = 212262860 := by
        calc
          (2 : ZMod 215985101) ^ 739675 = (2 : ZMod 215985101) ^ (369837 + 369837 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 369837 * (2 : ZMod 215985101) ^ 369837) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 212262860 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 215985101) ^ 1479350 = 65803133 := by
        calc
          (2 : ZMod 215985101) ^ 1479350 = (2 : ZMod 215985101) ^ (739675 + 739675) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 739675 * (2 : ZMod 215985101) ^ 739675 := by rw [pow_add]
          _ = 65803133 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 215985101) ^ 2958700 = 70590668 := by
        calc
          (2 : ZMod 215985101) ^ 2958700 = (2 : ZMod 215985101) ^ (1479350 + 1479350) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 1479350 * (2 : ZMod 215985101) ^ 1479350 := by rw [pow_add]
          _ = 70590668 := by rw [factor_2_20]; decide
      change (2 : ZMod 215985101) ^ 2958700 ≠ 1
      rw [factor_2_21]
      decide
    ·
      have factor_3_0 : (2 : ZMod 215985101) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 215985101) ^ 3 = 8 := by
        calc
          (2 : ZMod 215985101) ^ 3 = (2 : ZMod 215985101) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 1 * (2 : ZMod 215985101) ^ 1) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 215985101) ^ 7 = 128 := by
        calc
          (2 : ZMod 215985101) ^ 7 = (2 : ZMod 215985101) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 3 * (2 : ZMod 215985101) ^ 3) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 215985101) ^ 14 = 16384 := by
        calc
          (2 : ZMod 215985101) ^ 14 = (2 : ZMod 215985101) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 7 * (2 : ZMod 215985101) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 215985101) ^ 28 = 52450355 := by
        calc
          (2 : ZMod 215985101) ^ 28 = (2 : ZMod 215985101) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 14 * (2 : ZMod 215985101) ^ 14 := by rw [pow_add]
          _ = 52450355 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 215985101) ^ 57 = 69548003 := by
        calc
          (2 : ZMod 215985101) ^ 57 = (2 : ZMod 215985101) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 28 * (2 : ZMod 215985101) ^ 28) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 69548003 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 215985101) ^ 114 = 156131895 := by
        calc
          (2 : ZMod 215985101) ^ 114 = (2 : ZMod 215985101) ^ (57 + 57) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 57 * (2 : ZMod 215985101) ^ 57 := by rw [pow_add]
          _ = 156131895 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 215985101) ^ 228 = 60626278 := by
        calc
          (2 : ZMod 215985101) ^ 228 = (2 : ZMod 215985101) ^ (114 + 114) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 114 * (2 : ZMod 215985101) ^ 114 := by rw [pow_add]
          _ = 60626278 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 215985101) ^ 456 = 121176896 := by
        calc
          (2 : ZMod 215985101) ^ 456 = (2 : ZMod 215985101) ^ (228 + 228) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 228 * (2 : ZMod 215985101) ^ 228 := by rw [pow_add]
          _ = 121176896 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 215985101) ^ 912 = 159116386 := by
        calc
          (2 : ZMod 215985101) ^ 912 = (2 : ZMod 215985101) ^ (456 + 456) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 456 * (2 : ZMod 215985101) ^ 456 := by rw [pow_add]
          _ = 159116386 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 215985101) ^ 1825 = 207542571 := by
        calc
          (2 : ZMod 215985101) ^ 1825 = (2 : ZMod 215985101) ^ (912 + 912 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = ((2 : ZMod 215985101) ^ 912 * (2 : ZMod 215985101) ^ 912) * (2 : ZMod 215985101) := by rw [pow_succ, pow_add]
          _ = 207542571 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 215985101) ^ 3650 = 149545395 := by
        calc
          (2 : ZMod 215985101) ^ 3650 = (2 : ZMod 215985101) ^ (1825 + 1825) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 1825 * (2 : ZMod 215985101) ^ 1825 := by rw [pow_add]
          _ = 149545395 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 215985101) ^ 7300 = 154360756 := by
        calc
          (2 : ZMod 215985101) ^ 7300 = (2 : ZMod 215985101) ^ (3650 + 3650) :=
            congrArg (fun n : ℕ => (2 : ZMod 215985101) ^ n) (by norm_num)
          _ = (2 : ZMod 215985101) ^ 3650 * (2 : ZMod 215985101) ^ 3650 := by rw [pow_add]
          _ = 154360756 := by rw [factor_3_11]; decide
      change (2 : ZMod 215985101) ^ 7300 ≠ 1
      rw [factor_3_12]
      decide

#print axioms prime_lucas_215985101

end TotientTailPeriodKiller
end Erdos249257
