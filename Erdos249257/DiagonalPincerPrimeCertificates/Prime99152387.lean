import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=23 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_99152387 : Nat.Prime 99152387 := by
  apply lucas_primality 99152387 (2 : ZMod 99152387)
  ·
      have fermat_0 : (2 : ZMod 99152387) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 99152387) ^ 2 = 4 := by
        calc
          (2 : ZMod 99152387) ^ 2 = (2 : ZMod 99152387) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 1 * (2 : ZMod 99152387) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 99152387) ^ 5 = 32 := by
        calc
          (2 : ZMod 99152387) ^ 5 = (2 : ZMod 99152387) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 2 * (2 : ZMod 99152387) ^ 2) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 99152387) ^ 11 = 2048 := by
        calc
          (2 : ZMod 99152387) ^ 11 = (2 : ZMod 99152387) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 5 * (2 : ZMod 99152387) ^ 5) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 99152387) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 99152387) ^ 23 = (2 : ZMod 99152387) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 11 * (2 : ZMod 99152387) ^ 11) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 99152387) ^ 47 = 94485593 := by
        calc
          (2 : ZMod 99152387) ^ 47 = (2 : ZMod 99152387) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 23 * (2 : ZMod 99152387) ^ 23) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 94485593 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 99152387) ^ 94 = 45281499 := by
        calc
          (2 : ZMod 99152387) ^ 94 = (2 : ZMod 99152387) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 47 * (2 : ZMod 99152387) ^ 47 := by rw [pow_add]
          _ = 45281499 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 99152387) ^ 189 = 98060987 := by
        calc
          (2 : ZMod 99152387) ^ 189 = (2 : ZMod 99152387) ^ (94 + 94 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 94 * (2 : ZMod 99152387) ^ 94) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 98060987 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 99152387) ^ 378 = 36334969 := by
        calc
          (2 : ZMod 99152387) ^ 378 = (2 : ZMod 99152387) ^ (189 + 189) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 189 * (2 : ZMod 99152387) ^ 189 := by rw [pow_add]
          _ = 36334969 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 99152387) ^ 756 = 74944041 := by
        calc
          (2 : ZMod 99152387) ^ 756 = (2 : ZMod 99152387) ^ (378 + 378) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 378 * (2 : ZMod 99152387) ^ 378 := by rw [pow_add]
          _ = 74944041 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 99152387) ^ 1512 = 64901510 := by
        calc
          (2 : ZMod 99152387) ^ 1512 = (2 : ZMod 99152387) ^ (756 + 756) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 756 * (2 : ZMod 99152387) ^ 756 := by rw [pow_add]
          _ = 64901510 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 99152387) ^ 3025 = 35604744 := by
        calc
          (2 : ZMod 99152387) ^ 3025 = (2 : ZMod 99152387) ^ (1512 + 1512 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 1512 * (2 : ZMod 99152387) ^ 1512) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 35604744 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 99152387) ^ 6051 = 44959720 := by
        calc
          (2 : ZMod 99152387) ^ 6051 = (2 : ZMod 99152387) ^ (3025 + 3025 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 3025 * (2 : ZMod 99152387) ^ 3025) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 44959720 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 99152387) ^ 12103 = 76605038 := by
        calc
          (2 : ZMod 99152387) ^ 12103 = (2 : ZMod 99152387) ^ (6051 + 6051 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 6051 * (2 : ZMod 99152387) ^ 6051) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 76605038 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 99152387) ^ 24207 = 7477916 := by
        calc
          (2 : ZMod 99152387) ^ 24207 = (2 : ZMod 99152387) ^ (12103 + 12103 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 12103 * (2 : ZMod 99152387) ^ 12103) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 7477916 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 99152387) ^ 48414 = 57701892 := by
        calc
          (2 : ZMod 99152387) ^ 48414 = (2 : ZMod 99152387) ^ (24207 + 24207) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 24207 * (2 : ZMod 99152387) ^ 24207 := by rw [pow_add]
          _ = 57701892 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 99152387) ^ 96828 = 38264281 := by
        calc
          (2 : ZMod 99152387) ^ 96828 = (2 : ZMod 99152387) ^ (48414 + 48414) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 48414 * (2 : ZMod 99152387) ^ 48414 := by rw [pow_add]
          _ = 38264281 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 99152387) ^ 193657 = 22639351 := by
        calc
          (2 : ZMod 99152387) ^ 193657 = (2 : ZMod 99152387) ^ (96828 + 96828 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 96828 * (2 : ZMod 99152387) ^ 96828) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 22639351 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 99152387) ^ 387314 = 9230222 := by
        calc
          (2 : ZMod 99152387) ^ 387314 = (2 : ZMod 99152387) ^ (193657 + 193657) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 193657 * (2 : ZMod 99152387) ^ 193657 := by rw [pow_add]
          _ = 9230222 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 99152387) ^ 774628 = 12182373 := by
        calc
          (2 : ZMod 99152387) ^ 774628 = (2 : ZMod 99152387) ^ (387314 + 387314) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 387314 * (2 : ZMod 99152387) ^ 387314 := by rw [pow_add]
          _ = 12182373 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 99152387) ^ 1549256 = 9725786 := by
        calc
          (2 : ZMod 99152387) ^ 1549256 = (2 : ZMod 99152387) ^ (774628 + 774628) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 774628 * (2 : ZMod 99152387) ^ 774628 := by rw [pow_add]
          _ = 9725786 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 99152387) ^ 3098512 = 31881731 := by
        calc
          (2 : ZMod 99152387) ^ 3098512 = (2 : ZMod 99152387) ^ (1549256 + 1549256) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 1549256 * (2 : ZMod 99152387) ^ 1549256 := by rw [pow_add]
          _ = 31881731 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 99152387) ^ 6197024 = 39760168 := by
        calc
          (2 : ZMod 99152387) ^ 6197024 = (2 : ZMod 99152387) ^ (3098512 + 3098512) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 3098512 * (2 : ZMod 99152387) ^ 3098512 := by rw [pow_add]
          _ = 39760168 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 99152387) ^ 12394048 = 74765887 := by
        calc
          (2 : ZMod 99152387) ^ 12394048 = (2 : ZMod 99152387) ^ (6197024 + 6197024) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 6197024 * (2 : ZMod 99152387) ^ 6197024 := by rw [pow_add]
          _ = 74765887 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 99152387) ^ 24788096 = 39577276 := by
        calc
          (2 : ZMod 99152387) ^ 24788096 = (2 : ZMod 99152387) ^ (12394048 + 12394048) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 12394048 * (2 : ZMod 99152387) ^ 12394048 := by rw [pow_add]
          _ = 39577276 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 99152387) ^ 49576193 = 99152386 := by
        calc
          (2 : ZMod 99152387) ^ 49576193 = (2 : ZMod 99152387) ^ (24788096 + 24788096 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 24788096 * (2 : ZMod 99152387) ^ 24788096) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 99152386 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 99152387) ^ 99152386 = 1 := by
        calc
          (2 : ZMod 99152387) ^ 99152386 = (2 : ZMod 99152387) ^ (49576193 + 49576193) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 49576193 * (2 : ZMod 99152387) ^ 49576193 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3571, 1), (13883, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3571, 1), (13883, 1)] : List FactorBlock).map factorBlockValue).prod = 99152387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 99152387) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 99152387) ^ 2 = 4 := by
        calc
          (2 : ZMod 99152387) ^ 2 = (2 : ZMod 99152387) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 1 * (2 : ZMod 99152387) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 99152387) ^ 5 = 32 := by
        calc
          (2 : ZMod 99152387) ^ 5 = (2 : ZMod 99152387) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 2 * (2 : ZMod 99152387) ^ 2) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 99152387) ^ 11 = 2048 := by
        calc
          (2 : ZMod 99152387) ^ 11 = (2 : ZMod 99152387) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 5 * (2 : ZMod 99152387) ^ 5) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 99152387) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 99152387) ^ 23 = (2 : ZMod 99152387) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 11 * (2 : ZMod 99152387) ^ 11) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 99152387) ^ 47 = 94485593 := by
        calc
          (2 : ZMod 99152387) ^ 47 = (2 : ZMod 99152387) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 23 * (2 : ZMod 99152387) ^ 23) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 94485593 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 99152387) ^ 94 = 45281499 := by
        calc
          (2 : ZMod 99152387) ^ 94 = (2 : ZMod 99152387) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 47 * (2 : ZMod 99152387) ^ 47 := by rw [pow_add]
          _ = 45281499 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 99152387) ^ 189 = 98060987 := by
        calc
          (2 : ZMod 99152387) ^ 189 = (2 : ZMod 99152387) ^ (94 + 94 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 94 * (2 : ZMod 99152387) ^ 94) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 98060987 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 99152387) ^ 378 = 36334969 := by
        calc
          (2 : ZMod 99152387) ^ 378 = (2 : ZMod 99152387) ^ (189 + 189) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 189 * (2 : ZMod 99152387) ^ 189 := by rw [pow_add]
          _ = 36334969 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 99152387) ^ 756 = 74944041 := by
        calc
          (2 : ZMod 99152387) ^ 756 = (2 : ZMod 99152387) ^ (378 + 378) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 378 * (2 : ZMod 99152387) ^ 378 := by rw [pow_add]
          _ = 74944041 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 99152387) ^ 1512 = 64901510 := by
        calc
          (2 : ZMod 99152387) ^ 1512 = (2 : ZMod 99152387) ^ (756 + 756) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 756 * (2 : ZMod 99152387) ^ 756 := by rw [pow_add]
          _ = 64901510 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 99152387) ^ 3025 = 35604744 := by
        calc
          (2 : ZMod 99152387) ^ 3025 = (2 : ZMod 99152387) ^ (1512 + 1512 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 1512 * (2 : ZMod 99152387) ^ 1512) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 35604744 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 99152387) ^ 6051 = 44959720 := by
        calc
          (2 : ZMod 99152387) ^ 6051 = (2 : ZMod 99152387) ^ (3025 + 3025 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 3025 * (2 : ZMod 99152387) ^ 3025) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 44959720 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 99152387) ^ 12103 = 76605038 := by
        calc
          (2 : ZMod 99152387) ^ 12103 = (2 : ZMod 99152387) ^ (6051 + 6051 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 6051 * (2 : ZMod 99152387) ^ 6051) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 76605038 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 99152387) ^ 24207 = 7477916 := by
        calc
          (2 : ZMod 99152387) ^ 24207 = (2 : ZMod 99152387) ^ (12103 + 12103 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 12103 * (2 : ZMod 99152387) ^ 12103) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 7477916 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 99152387) ^ 48414 = 57701892 := by
        calc
          (2 : ZMod 99152387) ^ 48414 = (2 : ZMod 99152387) ^ (24207 + 24207) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 24207 * (2 : ZMod 99152387) ^ 24207 := by rw [pow_add]
          _ = 57701892 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 99152387) ^ 96828 = 38264281 := by
        calc
          (2 : ZMod 99152387) ^ 96828 = (2 : ZMod 99152387) ^ (48414 + 48414) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 48414 * (2 : ZMod 99152387) ^ 48414 := by rw [pow_add]
          _ = 38264281 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 99152387) ^ 193657 = 22639351 := by
        calc
          (2 : ZMod 99152387) ^ 193657 = (2 : ZMod 99152387) ^ (96828 + 96828 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 96828 * (2 : ZMod 99152387) ^ 96828) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 22639351 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 99152387) ^ 387314 = 9230222 := by
        calc
          (2 : ZMod 99152387) ^ 387314 = (2 : ZMod 99152387) ^ (193657 + 193657) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 193657 * (2 : ZMod 99152387) ^ 193657 := by rw [pow_add]
          _ = 9230222 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 99152387) ^ 774628 = 12182373 := by
        calc
          (2 : ZMod 99152387) ^ 774628 = (2 : ZMod 99152387) ^ (387314 + 387314) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 387314 * (2 : ZMod 99152387) ^ 387314 := by rw [pow_add]
          _ = 12182373 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 99152387) ^ 1549256 = 9725786 := by
        calc
          (2 : ZMod 99152387) ^ 1549256 = (2 : ZMod 99152387) ^ (774628 + 774628) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 774628 * (2 : ZMod 99152387) ^ 774628 := by rw [pow_add]
          _ = 9725786 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 99152387) ^ 3098512 = 31881731 := by
        calc
          (2 : ZMod 99152387) ^ 3098512 = (2 : ZMod 99152387) ^ (1549256 + 1549256) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 1549256 * (2 : ZMod 99152387) ^ 1549256 := by rw [pow_add]
          _ = 31881731 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 99152387) ^ 6197024 = 39760168 := by
        calc
          (2 : ZMod 99152387) ^ 6197024 = (2 : ZMod 99152387) ^ (3098512 + 3098512) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 3098512 * (2 : ZMod 99152387) ^ 3098512 := by rw [pow_add]
          _ = 39760168 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 99152387) ^ 12394048 = 74765887 := by
        calc
          (2 : ZMod 99152387) ^ 12394048 = (2 : ZMod 99152387) ^ (6197024 + 6197024) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 6197024 * (2 : ZMod 99152387) ^ 6197024 := by rw [pow_add]
          _ = 74765887 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 99152387) ^ 24788096 = 39577276 := by
        calc
          (2 : ZMod 99152387) ^ 24788096 = (2 : ZMod 99152387) ^ (12394048 + 12394048) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 12394048 * (2 : ZMod 99152387) ^ 12394048 := by rw [pow_add]
          _ = 39577276 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 99152387) ^ 49576193 = 99152386 := by
        calc
          (2 : ZMod 99152387) ^ 49576193 = (2 : ZMod 99152387) ^ (24788096 + 24788096 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 24788096 * (2 : ZMod 99152387) ^ 24788096) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 99152386 := by rw [factor_0_24]; decide
      change (2 : ZMod 99152387) ^ 49576193 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (2 : ZMod 99152387) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 99152387) ^ 3 = 8 := by
        calc
          (2 : ZMod 99152387) ^ 3 = (2 : ZMod 99152387) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 1 * (2 : ZMod 99152387) ^ 1) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 99152387) ^ 6 = 64 := by
        calc
          (2 : ZMod 99152387) ^ 6 = (2 : ZMod 99152387) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 3 * (2 : ZMod 99152387) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 99152387) ^ 13 = 8192 := by
        calc
          (2 : ZMod 99152387) ^ 13 = (2 : ZMod 99152387) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 6 * (2 : ZMod 99152387) ^ 6) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 99152387) ^ 27 = 35065341 := by
        calc
          (2 : ZMod 99152387) ^ 27 = (2 : ZMod 99152387) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 13 * (2 : ZMod 99152387) ^ 13) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 35065341 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 99152387) ^ 54 = 96717077 := by
        calc
          (2 : ZMod 99152387) ^ 54 = (2 : ZMod 99152387) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 27 * (2 : ZMod 99152387) ^ 27 := by rw [pow_add]
          _ = 96717077 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 99152387) ^ 108 = 33920082 := by
        calc
          (2 : ZMod 99152387) ^ 108 = (2 : ZMod 99152387) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 54 * (2 : ZMod 99152387) ^ 54 := by rw [pow_add]
          _ = 33920082 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 99152387) ^ 216 = 29404925 := by
        calc
          (2 : ZMod 99152387) ^ 216 = (2 : ZMod 99152387) ^ (108 + 108) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 108 * (2 : ZMod 99152387) ^ 108 := by rw [pow_add]
          _ = 29404925 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 99152387) ^ 433 = 95969136 := by
        calc
          (2 : ZMod 99152387) ^ 433 = (2 : ZMod 99152387) ^ (216 + 216 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 216 * (2 : ZMod 99152387) ^ 216) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 95969136 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 99152387) ^ 867 = 20869524 := by
        calc
          (2 : ZMod 99152387) ^ 867 = (2 : ZMod 99152387) ^ (433 + 433 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 433 * (2 : ZMod 99152387) ^ 433) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 20869524 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 99152387) ^ 1735 = 17938817 := by
        calc
          (2 : ZMod 99152387) ^ 1735 = (2 : ZMod 99152387) ^ (867 + 867 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 867 * (2 : ZMod 99152387) ^ 867) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 17938817 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 99152387) ^ 3470 = 1150862 := by
        calc
          (2 : ZMod 99152387) ^ 3470 = (2 : ZMod 99152387) ^ (1735 + 1735) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 1735 * (2 : ZMod 99152387) ^ 1735 := by rw [pow_add]
          _ = 1150862 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 99152387) ^ 6941 = 11514996 := by
        calc
          (2 : ZMod 99152387) ^ 6941 = (2 : ZMod 99152387) ^ (3470 + 3470 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 3470 * (2 : ZMod 99152387) ^ 3470) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 11514996 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 99152387) ^ 13883 = 67756668 := by
        calc
          (2 : ZMod 99152387) ^ 13883 = (2 : ZMod 99152387) ^ (6941 + 6941 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 6941 * (2 : ZMod 99152387) ^ 6941) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 67756668 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 99152387) ^ 27766 = 39844623 := by
        calc
          (2 : ZMod 99152387) ^ 27766 = (2 : ZMod 99152387) ^ (13883 + 13883) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 13883 * (2 : ZMod 99152387) ^ 13883 := by rw [pow_add]
          _ = 39844623 := by rw [factor_1_13]; decide
      change (2 : ZMod 99152387) ^ 27766 ≠ 1
      rw [factor_1_14]
      decide
    ·
      have factor_2_0 : (2 : ZMod 99152387) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 99152387) ^ 3 = 8 := by
        calc
          (2 : ZMod 99152387) ^ 3 = (2 : ZMod 99152387) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 1 * (2 : ZMod 99152387) ^ 1) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 99152387) ^ 6 = 64 := by
        calc
          (2 : ZMod 99152387) ^ 6 = (2 : ZMod 99152387) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 3 * (2 : ZMod 99152387) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 99152387) ^ 13 = 8192 := by
        calc
          (2 : ZMod 99152387) ^ 13 = (2 : ZMod 99152387) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 6 * (2 : ZMod 99152387) ^ 6) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 99152387) ^ 27 = 35065341 := by
        calc
          (2 : ZMod 99152387) ^ 27 = (2 : ZMod 99152387) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 13 * (2 : ZMod 99152387) ^ 13) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 35065341 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 99152387) ^ 55 = 94281767 := by
        calc
          (2 : ZMod 99152387) ^ 55 = (2 : ZMod 99152387) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 27 * (2 : ZMod 99152387) ^ 27) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 94281767 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 99152387) ^ 111 = 73055882 := by
        calc
          (2 : ZMod 99152387) ^ 111 = (2 : ZMod 99152387) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 55 * (2 : ZMod 99152387) ^ 55) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 73055882 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 99152387) ^ 223 = 95192081 := by
        calc
          (2 : ZMod 99152387) ^ 223 = (2 : ZMod 99152387) ^ (111 + 111 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 111 * (2 : ZMod 99152387) ^ 111) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 95192081 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 99152387) ^ 446 = 99037976 := by
        calc
          (2 : ZMod 99152387) ^ 446 = (2 : ZMod 99152387) ^ (223 + 223) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 223 * (2 : ZMod 99152387) ^ 223 := by rw [pow_add]
          _ = 99037976 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 99152387) ^ 892 = 1761837 := by
        calc
          (2 : ZMod 99152387) ^ 892 = (2 : ZMod 99152387) ^ (446 + 446) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 446 * (2 : ZMod 99152387) ^ 446 := by rw [pow_add]
          _ = 1761837 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 99152387) ^ 1785 = 9974294 := by
        calc
          (2 : ZMod 99152387) ^ 1785 = (2 : ZMod 99152387) ^ (892 + 892 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 892 * (2 : ZMod 99152387) ^ 892) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 9974294 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 99152387) ^ 3571 = 20508492 := by
        calc
          (2 : ZMod 99152387) ^ 3571 = (2 : ZMod 99152387) ^ (1785 + 1785 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = ((2 : ZMod 99152387) ^ 1785 * (2 : ZMod 99152387) ^ 1785) * (2 : ZMod 99152387) := by rw [pow_succ, pow_add]
          _ = 20508492 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 99152387) ^ 7142 = 65060445 := by
        calc
          (2 : ZMod 99152387) ^ 7142 = (2 : ZMod 99152387) ^ (3571 + 3571) :=
            congrArg (fun n : ℕ => (2 : ZMod 99152387) ^ n) (by norm_num)
          _ = (2 : ZMod 99152387) ^ 3571 * (2 : ZMod 99152387) ^ 3571 := by rw [pow_add]
          _ = 65060445 := by rw [factor_2_11]; decide
      change (2 : ZMod 99152387) ^ 7142 ≠ 1
      rw [factor_2_12]
      decide

#print axioms prime_lucas_99152387

end TotientTailPeriodKiller
end Erdos249257
