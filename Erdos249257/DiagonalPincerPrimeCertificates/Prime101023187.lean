import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=23 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_101023187 : Nat.Prime 101023187 := by
  apply lucas_primality 101023187 (2 : ZMod 101023187)
  ·
      have fermat_0 : (2 : ZMod 101023187) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 101023187) ^ 3 = 8 := by
        calc
          (2 : ZMod 101023187) ^ 3 = (2 : ZMod 101023187) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 1 * (2 : ZMod 101023187) ^ 1) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 101023187) ^ 6 = 64 := by
        calc
          (2 : ZMod 101023187) ^ 6 = (2 : ZMod 101023187) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 3 * (2 : ZMod 101023187) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 101023187) ^ 12 = 4096 := by
        calc
          (2 : ZMod 101023187) ^ 12 = (2 : ZMod 101023187) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 6 * (2 : ZMod 101023187) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 101023187) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 101023187) ^ 24 = (2 : ZMod 101023187) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 12 * (2 : ZMod 101023187) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 101023187) ^ 48 = 31140589 := by
        calc
          (2 : ZMod 101023187) ^ 48 = (2 : ZMod 101023187) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 24 * (2 : ZMod 101023187) ^ 24 := by rw [pow_add]
          _ = 31140589 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 101023187) ^ 96 = 62891806 := by
        calc
          (2 : ZMod 101023187) ^ 96 = (2 : ZMod 101023187) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 48 * (2 : ZMod 101023187) ^ 48 := by rw [pow_add]
          _ = 62891806 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 101023187) ^ 192 = 35110602 := by
        calc
          (2 : ZMod 101023187) ^ 192 = (2 : ZMod 101023187) ^ (96 + 96) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 96 * (2 : ZMod 101023187) ^ 96 := by rw [pow_add]
          _ = 35110602 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 101023187) ^ 385 = 84197870 := by
        calc
          (2 : ZMod 101023187) ^ 385 = (2 : ZMod 101023187) ^ (192 + 192 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 192 * (2 : ZMod 101023187) ^ 192) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 84197870 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 101023187) ^ 770 = 76611609 := by
        calc
          (2 : ZMod 101023187) ^ 770 = (2 : ZMod 101023187) ^ (385 + 385) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 385 * (2 : ZMod 101023187) ^ 385 := by rw [pow_add]
          _ = 76611609 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 101023187) ^ 1541 = 36566625 := by
        calc
          (2 : ZMod 101023187) ^ 1541 = (2 : ZMod 101023187) ^ (770 + 770 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 770 * (2 : ZMod 101023187) ^ 770) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 36566625 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 101023187) ^ 3082 = 12462627 := by
        calc
          (2 : ZMod 101023187) ^ 3082 = (2 : ZMod 101023187) ^ (1541 + 1541) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 1541 * (2 : ZMod 101023187) ^ 1541 := by rw [pow_add]
          _ = 12462627 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 101023187) ^ 6165 = 67262885 := by
        calc
          (2 : ZMod 101023187) ^ 6165 = (2 : ZMod 101023187) ^ (3082 + 3082 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 3082 * (2 : ZMod 101023187) ^ 3082) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 67262885 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 101023187) ^ 12331 = 100209300 := by
        calc
          (2 : ZMod 101023187) ^ 12331 = (2 : ZMod 101023187) ^ (6165 + 6165 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 6165 * (2 : ZMod 101023187) ^ 6165) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 100209300 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 101023187) ^ 24663 = 6023220 := by
        calc
          (2 : ZMod 101023187) ^ 24663 = (2 : ZMod 101023187) ^ (12331 + 12331 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 12331 * (2 : ZMod 101023187) ^ 12331) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 6023220 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 101023187) ^ 49327 = 70645042 := by
        calc
          (2 : ZMod 101023187) ^ 49327 = (2 : ZMod 101023187) ^ (24663 + 24663 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 24663 * (2 : ZMod 101023187) ^ 24663) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 70645042 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 101023187) ^ 98655 = 67748150 := by
        calc
          (2 : ZMod 101023187) ^ 98655 = (2 : ZMod 101023187) ^ (49327 + 49327 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 49327 * (2 : ZMod 101023187) ^ 49327) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 67748150 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 101023187) ^ 197310 = 16631563 := by
        calc
          (2 : ZMod 101023187) ^ 197310 = (2 : ZMod 101023187) ^ (98655 + 98655) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 98655 * (2 : ZMod 101023187) ^ 98655 := by rw [pow_add]
          _ = 16631563 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 101023187) ^ 394621 = 54248636 := by
        calc
          (2 : ZMod 101023187) ^ 394621 = (2 : ZMod 101023187) ^ (197310 + 197310 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 197310 * (2 : ZMod 101023187) ^ 197310) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 54248636 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 101023187) ^ 789243 = 32040259 := by
        calc
          (2 : ZMod 101023187) ^ 789243 = (2 : ZMod 101023187) ^ (394621 + 394621 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 394621 * (2 : ZMod 101023187) ^ 394621) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 32040259 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 101023187) ^ 1578487 = 34913157 := by
        calc
          (2 : ZMod 101023187) ^ 1578487 = (2 : ZMod 101023187) ^ (789243 + 789243 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 789243 * (2 : ZMod 101023187) ^ 789243) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 34913157 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 101023187) ^ 3156974 = 32329626 := by
        calc
          (2 : ZMod 101023187) ^ 3156974 = (2 : ZMod 101023187) ^ (1578487 + 1578487) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 1578487 * (2 : ZMod 101023187) ^ 1578487 := by rw [pow_add]
          _ = 32329626 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 101023187) ^ 6313949 = 68570188 := by
        calc
          (2 : ZMod 101023187) ^ 6313949 = (2 : ZMod 101023187) ^ (3156974 + 3156974 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 3156974 * (2 : ZMod 101023187) ^ 3156974) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 68570188 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 101023187) ^ 12627898 = 11639714 := by
        calc
          (2 : ZMod 101023187) ^ 12627898 = (2 : ZMod 101023187) ^ (6313949 + 6313949) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 6313949 * (2 : ZMod 101023187) ^ 6313949 := by rw [pow_add]
          _ = 11639714 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 101023187) ^ 25255796 = 38753787 := by
        calc
          (2 : ZMod 101023187) ^ 25255796 = (2 : ZMod 101023187) ^ (12627898 + 12627898) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 12627898 * (2 : ZMod 101023187) ^ 12627898 := by rw [pow_add]
          _ = 38753787 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 101023187) ^ 50511593 = 101023186 := by
        calc
          (2 : ZMod 101023187) ^ 50511593 = (2 : ZMod 101023187) ^ (25255796 + 25255796 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 25255796 * (2 : ZMod 101023187) ^ 25255796) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 101023186 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 101023187) ^ 101023186 = 1 := by
        calc
          (2 : ZMod 101023187) ^ 101023186 = (2 : ZMod 101023187) ^ (50511593 + 50511593) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 50511593 * (2 : ZMod 101023187) ^ 50511593 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (331, 1), (13873, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (331, 1), (13873, 1)] : List FactorBlock).map factorBlockValue).prod = 101023187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 101023187) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 101023187) ^ 3 = 8 := by
        calc
          (2 : ZMod 101023187) ^ 3 = (2 : ZMod 101023187) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 1 * (2 : ZMod 101023187) ^ 1) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 101023187) ^ 6 = 64 := by
        calc
          (2 : ZMod 101023187) ^ 6 = (2 : ZMod 101023187) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 3 * (2 : ZMod 101023187) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 101023187) ^ 12 = 4096 := by
        calc
          (2 : ZMod 101023187) ^ 12 = (2 : ZMod 101023187) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 6 * (2 : ZMod 101023187) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 101023187) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 101023187) ^ 24 = (2 : ZMod 101023187) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 12 * (2 : ZMod 101023187) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 101023187) ^ 48 = 31140589 := by
        calc
          (2 : ZMod 101023187) ^ 48 = (2 : ZMod 101023187) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 24 * (2 : ZMod 101023187) ^ 24 := by rw [pow_add]
          _ = 31140589 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 101023187) ^ 96 = 62891806 := by
        calc
          (2 : ZMod 101023187) ^ 96 = (2 : ZMod 101023187) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 48 * (2 : ZMod 101023187) ^ 48 := by rw [pow_add]
          _ = 62891806 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 101023187) ^ 192 = 35110602 := by
        calc
          (2 : ZMod 101023187) ^ 192 = (2 : ZMod 101023187) ^ (96 + 96) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 96 * (2 : ZMod 101023187) ^ 96 := by rw [pow_add]
          _ = 35110602 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 101023187) ^ 385 = 84197870 := by
        calc
          (2 : ZMod 101023187) ^ 385 = (2 : ZMod 101023187) ^ (192 + 192 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 192 * (2 : ZMod 101023187) ^ 192) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 84197870 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 101023187) ^ 770 = 76611609 := by
        calc
          (2 : ZMod 101023187) ^ 770 = (2 : ZMod 101023187) ^ (385 + 385) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 385 * (2 : ZMod 101023187) ^ 385 := by rw [pow_add]
          _ = 76611609 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 101023187) ^ 1541 = 36566625 := by
        calc
          (2 : ZMod 101023187) ^ 1541 = (2 : ZMod 101023187) ^ (770 + 770 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 770 * (2 : ZMod 101023187) ^ 770) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 36566625 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 101023187) ^ 3082 = 12462627 := by
        calc
          (2 : ZMod 101023187) ^ 3082 = (2 : ZMod 101023187) ^ (1541 + 1541) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 1541 * (2 : ZMod 101023187) ^ 1541 := by rw [pow_add]
          _ = 12462627 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 101023187) ^ 6165 = 67262885 := by
        calc
          (2 : ZMod 101023187) ^ 6165 = (2 : ZMod 101023187) ^ (3082 + 3082 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 3082 * (2 : ZMod 101023187) ^ 3082) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 67262885 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 101023187) ^ 12331 = 100209300 := by
        calc
          (2 : ZMod 101023187) ^ 12331 = (2 : ZMod 101023187) ^ (6165 + 6165 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 6165 * (2 : ZMod 101023187) ^ 6165) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 100209300 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 101023187) ^ 24663 = 6023220 := by
        calc
          (2 : ZMod 101023187) ^ 24663 = (2 : ZMod 101023187) ^ (12331 + 12331 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 12331 * (2 : ZMod 101023187) ^ 12331) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 6023220 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 101023187) ^ 49327 = 70645042 := by
        calc
          (2 : ZMod 101023187) ^ 49327 = (2 : ZMod 101023187) ^ (24663 + 24663 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 24663 * (2 : ZMod 101023187) ^ 24663) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 70645042 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 101023187) ^ 98655 = 67748150 := by
        calc
          (2 : ZMod 101023187) ^ 98655 = (2 : ZMod 101023187) ^ (49327 + 49327 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 49327 * (2 : ZMod 101023187) ^ 49327) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 67748150 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 101023187) ^ 197310 = 16631563 := by
        calc
          (2 : ZMod 101023187) ^ 197310 = (2 : ZMod 101023187) ^ (98655 + 98655) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 98655 * (2 : ZMod 101023187) ^ 98655 := by rw [pow_add]
          _ = 16631563 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 101023187) ^ 394621 = 54248636 := by
        calc
          (2 : ZMod 101023187) ^ 394621 = (2 : ZMod 101023187) ^ (197310 + 197310 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 197310 * (2 : ZMod 101023187) ^ 197310) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 54248636 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 101023187) ^ 789243 = 32040259 := by
        calc
          (2 : ZMod 101023187) ^ 789243 = (2 : ZMod 101023187) ^ (394621 + 394621 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 394621 * (2 : ZMod 101023187) ^ 394621) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 32040259 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 101023187) ^ 1578487 = 34913157 := by
        calc
          (2 : ZMod 101023187) ^ 1578487 = (2 : ZMod 101023187) ^ (789243 + 789243 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 789243 * (2 : ZMod 101023187) ^ 789243) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 34913157 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 101023187) ^ 3156974 = 32329626 := by
        calc
          (2 : ZMod 101023187) ^ 3156974 = (2 : ZMod 101023187) ^ (1578487 + 1578487) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 1578487 * (2 : ZMod 101023187) ^ 1578487 := by rw [pow_add]
          _ = 32329626 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 101023187) ^ 6313949 = 68570188 := by
        calc
          (2 : ZMod 101023187) ^ 6313949 = (2 : ZMod 101023187) ^ (3156974 + 3156974 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 3156974 * (2 : ZMod 101023187) ^ 3156974) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 68570188 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 101023187) ^ 12627898 = 11639714 := by
        calc
          (2 : ZMod 101023187) ^ 12627898 = (2 : ZMod 101023187) ^ (6313949 + 6313949) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 6313949 * (2 : ZMod 101023187) ^ 6313949 := by rw [pow_add]
          _ = 11639714 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 101023187) ^ 25255796 = 38753787 := by
        calc
          (2 : ZMod 101023187) ^ 25255796 = (2 : ZMod 101023187) ^ (12627898 + 12627898) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 12627898 * (2 : ZMod 101023187) ^ 12627898 := by rw [pow_add]
          _ = 38753787 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 101023187) ^ 50511593 = 101023186 := by
        calc
          (2 : ZMod 101023187) ^ 50511593 = (2 : ZMod 101023187) ^ (25255796 + 25255796 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 25255796 * (2 : ZMod 101023187) ^ 25255796) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 101023186 := by rw [factor_0_24]; decide
      change (2 : ZMod 101023187) ^ 50511593 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (2 : ZMod 101023187) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 101023187) ^ 2 = 4 := by
        calc
          (2 : ZMod 101023187) ^ 2 = (2 : ZMod 101023187) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 1 * (2 : ZMod 101023187) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 101023187) ^ 4 = 16 := by
        calc
          (2 : ZMod 101023187) ^ 4 = (2 : ZMod 101023187) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 2 * (2 : ZMod 101023187) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 101023187) ^ 8 = 256 := by
        calc
          (2 : ZMod 101023187) ^ 8 = (2 : ZMod 101023187) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 4 * (2 : ZMod 101023187) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 101023187) ^ 17 = 131072 := by
        calc
          (2 : ZMod 101023187) ^ 17 = (2 : ZMod 101023187) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 8 * (2 : ZMod 101023187) ^ 8) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 101023187) ^ 35 = 11854788 := by
        calc
          (2 : ZMod 101023187) ^ 35 = (2 : ZMod 101023187) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 17 * (2 : ZMod 101023187) ^ 17) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 11854788 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 101023187) ^ 70 = 16486382 := by
        calc
          (2 : ZMod 101023187) ^ 70 = (2 : ZMod 101023187) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 35 * (2 : ZMod 101023187) ^ 35 := by rw [pow_add]
          _ = 16486382 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 101023187) ^ 140 = 28313351 := by
        calc
          (2 : ZMod 101023187) ^ 140 = (2 : ZMod 101023187) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 70 * (2 : ZMod 101023187) ^ 70 := by rw [pow_add]
          _ = 28313351 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 101023187) ^ 280 = 84859646 := by
        calc
          (2 : ZMod 101023187) ^ 280 = (2 : ZMod 101023187) ^ (140 + 140) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 140 * (2 : ZMod 101023187) ^ 140 := by rw [pow_add]
          _ = 84859646 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 101023187) ^ 560 = 53853688 := by
        calc
          (2 : ZMod 101023187) ^ 560 = (2 : ZMod 101023187) ^ (280 + 280) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 280 * (2 : ZMod 101023187) ^ 280 := by rw [pow_add]
          _ = 53853688 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 101023187) ^ 1121 = 85487331 := by
        calc
          (2 : ZMod 101023187) ^ 1121 = (2 : ZMod 101023187) ^ (560 + 560 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 560 * (2 : ZMod 101023187) ^ 560) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 85487331 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 101023187) ^ 2242 = 41689702 := by
        calc
          (2 : ZMod 101023187) ^ 2242 = (2 : ZMod 101023187) ^ (1121 + 1121) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 1121 * (2 : ZMod 101023187) ^ 1121 := by rw [pow_add]
          _ = 41689702 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 101023187) ^ 4484 = 57208444 := by
        calc
          (2 : ZMod 101023187) ^ 4484 = (2 : ZMod 101023187) ^ (2242 + 2242) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 2242 * (2 : ZMod 101023187) ^ 2242 := by rw [pow_add]
          _ = 57208444 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 101023187) ^ 8968 = 2331115 := by
        calc
          (2 : ZMod 101023187) ^ 8968 = (2 : ZMod 101023187) ^ (4484 + 4484) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 4484 * (2 : ZMod 101023187) ^ 4484 := by rw [pow_add]
          _ = 2331115 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 101023187) ^ 17937 = 18805803 := by
        calc
          (2 : ZMod 101023187) ^ 17937 = (2 : ZMod 101023187) ^ (8968 + 8968 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 8968 * (2 : ZMod 101023187) ^ 8968) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 18805803 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 101023187) ^ 35874 = 92306315 := by
        calc
          (2 : ZMod 101023187) ^ 35874 = (2 : ZMod 101023187) ^ (17937 + 17937) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 17937 * (2 : ZMod 101023187) ^ 17937 := by rw [pow_add]
          _ = 92306315 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 101023187) ^ 71749 = 50072473 := by
        calc
          (2 : ZMod 101023187) ^ 71749 = (2 : ZMod 101023187) ^ (35874 + 35874 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 35874 * (2 : ZMod 101023187) ^ 35874) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 50072473 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 101023187) ^ 143498 = 99828521 := by
        calc
          (2 : ZMod 101023187) ^ 143498 = (2 : ZMod 101023187) ^ (71749 + 71749) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 71749 * (2 : ZMod 101023187) ^ 71749 := by rw [pow_add]
          _ = 99828521 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 101023187) ^ 286997 = 43554427 := by
        calc
          (2 : ZMod 101023187) ^ 286997 = (2 : ZMod 101023187) ^ (143498 + 143498 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 143498 * (2 : ZMod 101023187) ^ 143498) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 43554427 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 101023187) ^ 573995 = 24241345 := by
        calc
          (2 : ZMod 101023187) ^ 573995 = (2 : ZMod 101023187) ^ (286997 + 286997 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 286997 * (2 : ZMod 101023187) ^ 286997) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 24241345 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 101023187) ^ 1147990 = 20716855 := by
        calc
          (2 : ZMod 101023187) ^ 1147990 = (2 : ZMod 101023187) ^ (573995 + 573995) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 573995 * (2 : ZMod 101023187) ^ 573995 := by rw [pow_add]
          _ = 20716855 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 101023187) ^ 2295981 = 23347149 := by
        calc
          (2 : ZMod 101023187) ^ 2295981 = (2 : ZMod 101023187) ^ (1147990 + 1147990 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 1147990 * (2 : ZMod 101023187) ^ 1147990) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 23347149 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 101023187) ^ 4591963 = 42337025 := by
        calc
          (2 : ZMod 101023187) ^ 4591963 = (2 : ZMod 101023187) ^ (2295981 + 2295981 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 2295981 * (2 : ZMod 101023187) ^ 2295981) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 42337025 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 101023187) ^ 9183926 = 90981660 := by
        calc
          (2 : ZMod 101023187) ^ 9183926 = (2 : ZMod 101023187) ^ (4591963 + 4591963) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 4591963 * (2 : ZMod 101023187) ^ 4591963 := by rw [pow_add]
          _ = 90981660 := by rw [factor_1_22]; decide
      change (2 : ZMod 101023187) ^ 9183926 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (2 : ZMod 101023187) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 101023187) ^ 2 = 4 := by
        calc
          (2 : ZMod 101023187) ^ 2 = (2 : ZMod 101023187) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 1 * (2 : ZMod 101023187) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 101023187) ^ 4 = 16 := by
        calc
          (2 : ZMod 101023187) ^ 4 = (2 : ZMod 101023187) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 2 * (2 : ZMod 101023187) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 101023187) ^ 9 = 512 := by
        calc
          (2 : ZMod 101023187) ^ 9 = (2 : ZMod 101023187) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 4 * (2 : ZMod 101023187) ^ 4) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 101023187) ^ 18 = 262144 := by
        calc
          (2 : ZMod 101023187) ^ 18 = (2 : ZMod 101023187) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 9 * (2 : ZMod 101023187) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 101023187) ^ 37 = 47419152 := by
        calc
          (2 : ZMod 101023187) ^ 37 = (2 : ZMod 101023187) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 18 * (2 : ZMod 101023187) ^ 18) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 47419152 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 101023187) ^ 74 = 61735738 := by
        calc
          (2 : ZMod 101023187) ^ 74 = (2 : ZMod 101023187) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 37 * (2 : ZMod 101023187) ^ 37 := by rw [pow_add]
          _ = 61735738 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 101023187) ^ 149 = 50119971 := by
        calc
          (2 : ZMod 101023187) ^ 149 = (2 : ZMod 101023187) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 74 * (2 : ZMod 101023187) ^ 74) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 50119971 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 101023187) ^ 298 = 40240437 := by
        calc
          (2 : ZMod 101023187) ^ 298 = (2 : ZMod 101023187) ^ (149 + 149) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 149 * (2 : ZMod 101023187) ^ 149 := by rw [pow_add]
          _ = 40240437 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 101023187) ^ 596 = 86359742 := by
        calc
          (2 : ZMod 101023187) ^ 596 = (2 : ZMod 101023187) ^ (298 + 298) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 298 * (2 : ZMod 101023187) ^ 298 := by rw [pow_add]
          _ = 86359742 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 101023187) ^ 1192 = 80335469 := by
        calc
          (2 : ZMod 101023187) ^ 1192 = (2 : ZMod 101023187) ^ (596 + 596) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 596 * (2 : ZMod 101023187) ^ 596 := by rw [pow_add]
          _ = 80335469 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 101023187) ^ 2384 = 76040821 := by
        calc
          (2 : ZMod 101023187) ^ 2384 = (2 : ZMod 101023187) ^ (1192 + 1192) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 1192 * (2 : ZMod 101023187) ^ 1192 := by rw [pow_add]
          _ = 76040821 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 101023187) ^ 4768 = 89298005 := by
        calc
          (2 : ZMod 101023187) ^ 4768 = (2 : ZMod 101023187) ^ (2384 + 2384) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 2384 * (2 : ZMod 101023187) ^ 2384 := by rw [pow_add]
          _ = 89298005 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 101023187) ^ 9537 = 27672185 := by
        calc
          (2 : ZMod 101023187) ^ 9537 = (2 : ZMod 101023187) ^ (4768 + 4768 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 4768 * (2 : ZMod 101023187) ^ 4768) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 27672185 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 101023187) ^ 19075 = 51164516 := by
        calc
          (2 : ZMod 101023187) ^ 19075 = (2 : ZMod 101023187) ^ (9537 + 9537 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 9537 * (2 : ZMod 101023187) ^ 9537) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 51164516 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 101023187) ^ 38150 = 15197663 := by
        calc
          (2 : ZMod 101023187) ^ 38150 = (2 : ZMod 101023187) ^ (19075 + 19075) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 19075 * (2 : ZMod 101023187) ^ 19075 := by rw [pow_add]
          _ = 15197663 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 101023187) ^ 76301 = 3609247 := by
        calc
          (2 : ZMod 101023187) ^ 76301 = (2 : ZMod 101023187) ^ (38150 + 38150 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 38150 * (2 : ZMod 101023187) ^ 38150) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 3609247 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 101023187) ^ 152603 = 54025840 := by
        calc
          (2 : ZMod 101023187) ^ 152603 = (2 : ZMod 101023187) ^ (76301 + 76301 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 76301 * (2 : ZMod 101023187) ^ 76301) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 54025840 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 101023187) ^ 305206 = 71154183 := by
        calc
          (2 : ZMod 101023187) ^ 305206 = (2 : ZMod 101023187) ^ (152603 + 152603) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 152603 * (2 : ZMod 101023187) ^ 152603 := by rw [pow_add]
          _ = 71154183 := by rw [factor_2_17]; decide
      change (2 : ZMod 101023187) ^ 305206 ≠ 1
      rw [factor_2_18]
      decide
    ·
      have factor_3_0 : (2 : ZMod 101023187) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 101023187) ^ 3 = 8 := by
        calc
          (2 : ZMod 101023187) ^ 3 = (2 : ZMod 101023187) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 1 * (2 : ZMod 101023187) ^ 1) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 101023187) ^ 7 = 128 := by
        calc
          (2 : ZMod 101023187) ^ 7 = (2 : ZMod 101023187) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 3 * (2 : ZMod 101023187) ^ 3) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 101023187) ^ 14 = 16384 := by
        calc
          (2 : ZMod 101023187) ^ 14 = (2 : ZMod 101023187) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 7 * (2 : ZMod 101023187) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 101023187) ^ 28 = 66389082 := by
        calc
          (2 : ZMod 101023187) ^ 28 = (2 : ZMod 101023187) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 14 * (2 : ZMod 101023187) ^ 14 := by rw [pow_add]
          _ = 66389082 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 101023187) ^ 56 = 92182198 := by
        calc
          (2 : ZMod 101023187) ^ 56 = (2 : ZMod 101023187) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 28 * (2 : ZMod 101023187) ^ 28 := by rw [pow_add]
          _ = 92182198 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 101023187) ^ 113 = 64783206 := by
        calc
          (2 : ZMod 101023187) ^ 113 = (2 : ZMod 101023187) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 56 * (2 : ZMod 101023187) ^ 56) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 64783206 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 101023187) ^ 227 = 79808066 := by
        calc
          (2 : ZMod 101023187) ^ 227 = (2 : ZMod 101023187) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 113 * (2 : ZMod 101023187) ^ 113) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 79808066 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 101023187) ^ 455 = 55346010 := by
        calc
          (2 : ZMod 101023187) ^ 455 = (2 : ZMod 101023187) ^ (227 + 227 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 227 * (2 : ZMod 101023187) ^ 227) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 55346010 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 101023187) ^ 910 = 95885193 := by
        calc
          (2 : ZMod 101023187) ^ 910 = (2 : ZMod 101023187) ^ (455 + 455) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 455 * (2 : ZMod 101023187) ^ 455 := by rw [pow_add]
          _ = 95885193 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 101023187) ^ 1820 = 7209944 := by
        calc
          (2 : ZMod 101023187) ^ 1820 = (2 : ZMod 101023187) ^ (910 + 910) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 910 * (2 : ZMod 101023187) ^ 910 := by rw [pow_add]
          _ = 7209944 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 101023187) ^ 3641 = 87413027 := by
        calc
          (2 : ZMod 101023187) ^ 3641 = (2 : ZMod 101023187) ^ (1820 + 1820 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = ((2 : ZMod 101023187) ^ 1820 * (2 : ZMod 101023187) ^ 1820) * (2 : ZMod 101023187) := by rw [pow_succ, pow_add]
          _ = 87413027 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 101023187) ^ 7282 = 36472839 := by
        calc
          (2 : ZMod 101023187) ^ 7282 = (2 : ZMod 101023187) ^ (3641 + 3641) :=
            congrArg (fun n : ℕ => (2 : ZMod 101023187) ^ n) (by norm_num)
          _ = (2 : ZMod 101023187) ^ 3641 * (2 : ZMod 101023187) ^ 3641 := by rw [pow_add]
          _ = 36472839 := by rw [factor_3_11]; decide
      change (2 : ZMod 101023187) ^ 7282 ≠ 1
      rw [factor_3_12]
      decide

#print axioms prime_lucas_101023187

end TotientTailPeriodKiller
end Erdos249257
