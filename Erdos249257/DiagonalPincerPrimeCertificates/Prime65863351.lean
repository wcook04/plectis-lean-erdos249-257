import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_65863351 : Nat.Prime 65863351 := by
  apply lucas_primality 65863351 (6 : ZMod 65863351)
  ·
      have fermat_0 : (6 : ZMod 65863351) ^ 1 = 6 := by norm_num
      have fermat_1 : (6 : ZMod 65863351) ^ 3 = 216 := by
        calc
          (6 : ZMod 65863351) ^ 3 = (6 : ZMod 65863351) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 1 * (6 : ZMod 65863351) ^ 1) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [fermat_0]; decide
      have fermat_2 : (6 : ZMod 65863351) ^ 7 = 279936 := by
        calc
          (6 : ZMod 65863351) ^ 7 = (6 : ZMod 65863351) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 3 * (6 : ZMod 65863351) ^ 3) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 279936 := by rw [fermat_1]; decide
      have fermat_3 : (6 : ZMod 65863351) ^ 15 = 52385138 := by
        calc
          (6 : ZMod 65863351) ^ 15 = (6 : ZMod 65863351) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 7 * (6 : ZMod 65863351) ^ 7) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 52385138 := by rw [fermat_2]; decide
      have fermat_4 : (6 : ZMod 65863351) ^ 31 = 33844353 := by
        calc
          (6 : ZMod 65863351) ^ 31 = (6 : ZMod 65863351) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 15 * (6 : ZMod 65863351) ^ 15) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 33844353 := by rw [fermat_3]; decide
      have fermat_5 : (6 : ZMod 65863351) ^ 62 = 22884747 := by
        calc
          (6 : ZMod 65863351) ^ 62 = (6 : ZMod 65863351) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 31 * (6 : ZMod 65863351) ^ 31 := by rw [pow_add]
          _ = 22884747 := by rw [fermat_4]; decide
      have fermat_6 : (6 : ZMod 65863351) ^ 125 = 826326 := by
        calc
          (6 : ZMod 65863351) ^ 125 = (6 : ZMod 65863351) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 62 * (6 : ZMod 65863351) ^ 62) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 826326 := by rw [fermat_5]; decide
      have fermat_7 : (6 : ZMod 65863351) ^ 251 = 55790754 := by
        calc
          (6 : ZMod 65863351) ^ 251 = (6 : ZMod 65863351) ^ (125 + 125 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 125 * (6 : ZMod 65863351) ^ 125) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 55790754 := by rw [fermat_6]; decide
      have fermat_8 : (6 : ZMod 65863351) ^ 502 = 53040340 := by
        calc
          (6 : ZMod 65863351) ^ 502 = (6 : ZMod 65863351) ^ (251 + 251) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 251 * (6 : ZMod 65863351) ^ 251 := by rw [pow_add]
          _ = 53040340 := by rw [fermat_7]; decide
      have fermat_9 : (6 : ZMod 65863351) ^ 1004 = 42887495 := by
        calc
          (6 : ZMod 65863351) ^ 1004 = (6 : ZMod 65863351) ^ (502 + 502) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 502 * (6 : ZMod 65863351) ^ 502 := by rw [pow_add]
          _ = 42887495 := by rw [fermat_8]; decide
      have fermat_10 : (6 : ZMod 65863351) ^ 2009 = 52154154 := by
        calc
          (6 : ZMod 65863351) ^ 2009 = (6 : ZMod 65863351) ^ (1004 + 1004 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 1004 * (6 : ZMod 65863351) ^ 1004) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 52154154 := by rw [fermat_9]; decide
      have fermat_11 : (6 : ZMod 65863351) ^ 4019 = 2409562 := by
        calc
          (6 : ZMod 65863351) ^ 4019 = (6 : ZMod 65863351) ^ (2009 + 2009 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 2009 * (6 : ZMod 65863351) ^ 2009) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 2409562 := by rw [fermat_10]; decide
      have fermat_12 : (6 : ZMod 65863351) ^ 8039 = 17486952 := by
        calc
          (6 : ZMod 65863351) ^ 8039 = (6 : ZMod 65863351) ^ (4019 + 4019 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 4019 * (6 : ZMod 65863351) ^ 4019) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 17486952 := by rw [fermat_11]; decide
      have fermat_13 : (6 : ZMod 65863351) ^ 16079 = 40173340 := by
        calc
          (6 : ZMod 65863351) ^ 16079 = (6 : ZMod 65863351) ^ (8039 + 8039 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 8039 * (6 : ZMod 65863351) ^ 8039) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 40173340 := by rw [fermat_12]; decide
      have fermat_14 : (6 : ZMod 65863351) ^ 32159 = 23179068 := by
        calc
          (6 : ZMod 65863351) ^ 32159 = (6 : ZMod 65863351) ^ (16079 + 16079 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 16079 * (6 : ZMod 65863351) ^ 16079) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 23179068 := by rw [fermat_13]; decide
      have fermat_15 : (6 : ZMod 65863351) ^ 64319 = 33244605 := by
        calc
          (6 : ZMod 65863351) ^ 64319 = (6 : ZMod 65863351) ^ (32159 + 32159 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 32159 * (6 : ZMod 65863351) ^ 32159) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 33244605 := by rw [fermat_14]; decide
      have fermat_16 : (6 : ZMod 65863351) ^ 128639 = 15209226 := by
        calc
          (6 : ZMod 65863351) ^ 128639 = (6 : ZMod 65863351) ^ (64319 + 64319 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 64319 * (6 : ZMod 65863351) ^ 64319) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 15209226 := by rw [fermat_15]; decide
      have fermat_17 : (6 : ZMod 65863351) ^ 257278 = 36298148 := by
        calc
          (6 : ZMod 65863351) ^ 257278 = (6 : ZMod 65863351) ^ (128639 + 128639) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 128639 * (6 : ZMod 65863351) ^ 128639 := by rw [pow_add]
          _ = 36298148 := by rw [fermat_16]; decide
      have fermat_18 : (6 : ZMod 65863351) ^ 514557 = 17061740 := by
        calc
          (6 : ZMod 65863351) ^ 514557 = (6 : ZMod 65863351) ^ (257278 + 257278 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 257278 * (6 : ZMod 65863351) ^ 257278) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 17061740 := by rw [fermat_17]; decide
      have fermat_19 : (6 : ZMod 65863351) ^ 1029114 = 1351098 := by
        calc
          (6 : ZMod 65863351) ^ 1029114 = (6 : ZMod 65863351) ^ (514557 + 514557) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 514557 * (6 : ZMod 65863351) ^ 514557 := by rw [pow_add]
          _ = 1351098 := by rw [fermat_18]; decide
      have fermat_20 : (6 : ZMod 65863351) ^ 2058229 = 48879079 := by
        calc
          (6 : ZMod 65863351) ^ 2058229 = (6 : ZMod 65863351) ^ (1029114 + 1029114 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 1029114 * (6 : ZMod 65863351) ^ 1029114) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 48879079 := by rw [fermat_19]; decide
      have fermat_21 : (6 : ZMod 65863351) ^ 4116459 = 4978960 := by
        calc
          (6 : ZMod 65863351) ^ 4116459 = (6 : ZMod 65863351) ^ (2058229 + 2058229 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 2058229 * (6 : ZMod 65863351) ^ 2058229) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 4978960 := by rw [fermat_20]; decide
      have fermat_22 : (6 : ZMod 65863351) ^ 8232918 = 65315465 := by
        calc
          (6 : ZMod 65863351) ^ 8232918 = (6 : ZMod 65863351) ^ (4116459 + 4116459) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 4116459 * (6 : ZMod 65863351) ^ 4116459 := by rw [pow_add]
          _ = 65315465 := by rw [fermat_21]; decide
      have fermat_23 : (6 : ZMod 65863351) ^ 16465837 = 41080881 := by
        calc
          (6 : ZMod 65863351) ^ 16465837 = (6 : ZMod 65863351) ^ (8232918 + 8232918 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 8232918 * (6 : ZMod 65863351) ^ 8232918) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 41080881 := by rw [fermat_22]; decide
      have fermat_24 : (6 : ZMod 65863351) ^ 32931675 = 65863350 := by
        calc
          (6 : ZMod 65863351) ^ 32931675 = (6 : ZMod 65863351) ^ (16465837 + 16465837 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 16465837 * (6 : ZMod 65863351) ^ 16465837) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 65863350 := by rw [fermat_23]; decide
      have fermat_25 : (6 : ZMod 65863351) ^ 65863350 = 1 := by
        calc
          (6 : ZMod 65863351) ^ 65863350 = (6 : ZMod 65863351) ^ (32931675 + 32931675) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 32931675 * (6 : ZMod 65863351) ^ 32931675 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 2), (7, 2), (29, 1), (103, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 2), (7, 2), (29, 1), (103, 1)] : List FactorBlock).map factorBlockValue).prod = 65863351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (6 : ZMod 65863351) ^ 1 = 6 := by norm_num
      have factor_0_1 : (6 : ZMod 65863351) ^ 3 = 216 := by
        calc
          (6 : ZMod 65863351) ^ 3 = (6 : ZMod 65863351) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 1 * (6 : ZMod 65863351) ^ 1) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_0_0]; decide
      have factor_0_2 : (6 : ZMod 65863351) ^ 7 = 279936 := by
        calc
          (6 : ZMod 65863351) ^ 7 = (6 : ZMod 65863351) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 3 * (6 : ZMod 65863351) ^ 3) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 279936 := by rw [factor_0_1]; decide
      have factor_0_3 : (6 : ZMod 65863351) ^ 15 = 52385138 := by
        calc
          (6 : ZMod 65863351) ^ 15 = (6 : ZMod 65863351) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 7 * (6 : ZMod 65863351) ^ 7) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 52385138 := by rw [factor_0_2]; decide
      have factor_0_4 : (6 : ZMod 65863351) ^ 31 = 33844353 := by
        calc
          (6 : ZMod 65863351) ^ 31 = (6 : ZMod 65863351) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 15 * (6 : ZMod 65863351) ^ 15) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 33844353 := by rw [factor_0_3]; decide
      have factor_0_5 : (6 : ZMod 65863351) ^ 62 = 22884747 := by
        calc
          (6 : ZMod 65863351) ^ 62 = (6 : ZMod 65863351) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 31 * (6 : ZMod 65863351) ^ 31 := by rw [pow_add]
          _ = 22884747 := by rw [factor_0_4]; decide
      have factor_0_6 : (6 : ZMod 65863351) ^ 125 = 826326 := by
        calc
          (6 : ZMod 65863351) ^ 125 = (6 : ZMod 65863351) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 62 * (6 : ZMod 65863351) ^ 62) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 826326 := by rw [factor_0_5]; decide
      have factor_0_7 : (6 : ZMod 65863351) ^ 251 = 55790754 := by
        calc
          (6 : ZMod 65863351) ^ 251 = (6 : ZMod 65863351) ^ (125 + 125 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 125 * (6 : ZMod 65863351) ^ 125) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 55790754 := by rw [factor_0_6]; decide
      have factor_0_8 : (6 : ZMod 65863351) ^ 502 = 53040340 := by
        calc
          (6 : ZMod 65863351) ^ 502 = (6 : ZMod 65863351) ^ (251 + 251) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 251 * (6 : ZMod 65863351) ^ 251 := by rw [pow_add]
          _ = 53040340 := by rw [factor_0_7]; decide
      have factor_0_9 : (6 : ZMod 65863351) ^ 1004 = 42887495 := by
        calc
          (6 : ZMod 65863351) ^ 1004 = (6 : ZMod 65863351) ^ (502 + 502) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 502 * (6 : ZMod 65863351) ^ 502 := by rw [pow_add]
          _ = 42887495 := by rw [factor_0_8]; decide
      have factor_0_10 : (6 : ZMod 65863351) ^ 2009 = 52154154 := by
        calc
          (6 : ZMod 65863351) ^ 2009 = (6 : ZMod 65863351) ^ (1004 + 1004 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 1004 * (6 : ZMod 65863351) ^ 1004) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 52154154 := by rw [factor_0_9]; decide
      have factor_0_11 : (6 : ZMod 65863351) ^ 4019 = 2409562 := by
        calc
          (6 : ZMod 65863351) ^ 4019 = (6 : ZMod 65863351) ^ (2009 + 2009 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 2009 * (6 : ZMod 65863351) ^ 2009) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 2409562 := by rw [factor_0_10]; decide
      have factor_0_12 : (6 : ZMod 65863351) ^ 8039 = 17486952 := by
        calc
          (6 : ZMod 65863351) ^ 8039 = (6 : ZMod 65863351) ^ (4019 + 4019 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 4019 * (6 : ZMod 65863351) ^ 4019) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 17486952 := by rw [factor_0_11]; decide
      have factor_0_13 : (6 : ZMod 65863351) ^ 16079 = 40173340 := by
        calc
          (6 : ZMod 65863351) ^ 16079 = (6 : ZMod 65863351) ^ (8039 + 8039 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 8039 * (6 : ZMod 65863351) ^ 8039) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 40173340 := by rw [factor_0_12]; decide
      have factor_0_14 : (6 : ZMod 65863351) ^ 32159 = 23179068 := by
        calc
          (6 : ZMod 65863351) ^ 32159 = (6 : ZMod 65863351) ^ (16079 + 16079 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 16079 * (6 : ZMod 65863351) ^ 16079) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 23179068 := by rw [factor_0_13]; decide
      have factor_0_15 : (6 : ZMod 65863351) ^ 64319 = 33244605 := by
        calc
          (6 : ZMod 65863351) ^ 64319 = (6 : ZMod 65863351) ^ (32159 + 32159 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 32159 * (6 : ZMod 65863351) ^ 32159) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 33244605 := by rw [factor_0_14]; decide
      have factor_0_16 : (6 : ZMod 65863351) ^ 128639 = 15209226 := by
        calc
          (6 : ZMod 65863351) ^ 128639 = (6 : ZMod 65863351) ^ (64319 + 64319 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 64319 * (6 : ZMod 65863351) ^ 64319) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 15209226 := by rw [factor_0_15]; decide
      have factor_0_17 : (6 : ZMod 65863351) ^ 257278 = 36298148 := by
        calc
          (6 : ZMod 65863351) ^ 257278 = (6 : ZMod 65863351) ^ (128639 + 128639) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 128639 * (6 : ZMod 65863351) ^ 128639 := by rw [pow_add]
          _ = 36298148 := by rw [factor_0_16]; decide
      have factor_0_18 : (6 : ZMod 65863351) ^ 514557 = 17061740 := by
        calc
          (6 : ZMod 65863351) ^ 514557 = (6 : ZMod 65863351) ^ (257278 + 257278 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 257278 * (6 : ZMod 65863351) ^ 257278) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 17061740 := by rw [factor_0_17]; decide
      have factor_0_19 : (6 : ZMod 65863351) ^ 1029114 = 1351098 := by
        calc
          (6 : ZMod 65863351) ^ 1029114 = (6 : ZMod 65863351) ^ (514557 + 514557) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 514557 * (6 : ZMod 65863351) ^ 514557 := by rw [pow_add]
          _ = 1351098 := by rw [factor_0_18]; decide
      have factor_0_20 : (6 : ZMod 65863351) ^ 2058229 = 48879079 := by
        calc
          (6 : ZMod 65863351) ^ 2058229 = (6 : ZMod 65863351) ^ (1029114 + 1029114 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 1029114 * (6 : ZMod 65863351) ^ 1029114) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 48879079 := by rw [factor_0_19]; decide
      have factor_0_21 : (6 : ZMod 65863351) ^ 4116459 = 4978960 := by
        calc
          (6 : ZMod 65863351) ^ 4116459 = (6 : ZMod 65863351) ^ (2058229 + 2058229 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 2058229 * (6 : ZMod 65863351) ^ 2058229) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 4978960 := by rw [factor_0_20]; decide
      have factor_0_22 : (6 : ZMod 65863351) ^ 8232918 = 65315465 := by
        calc
          (6 : ZMod 65863351) ^ 8232918 = (6 : ZMod 65863351) ^ (4116459 + 4116459) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 4116459 * (6 : ZMod 65863351) ^ 4116459 := by rw [pow_add]
          _ = 65315465 := by rw [factor_0_21]; decide
      have factor_0_23 : (6 : ZMod 65863351) ^ 16465837 = 41080881 := by
        calc
          (6 : ZMod 65863351) ^ 16465837 = (6 : ZMod 65863351) ^ (8232918 + 8232918 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 8232918 * (6 : ZMod 65863351) ^ 8232918) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 41080881 := by rw [factor_0_22]; decide
      have factor_0_24 : (6 : ZMod 65863351) ^ 32931675 = 65863350 := by
        calc
          (6 : ZMod 65863351) ^ 32931675 = (6 : ZMod 65863351) ^ (16465837 + 16465837 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 16465837 * (6 : ZMod 65863351) ^ 16465837) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 65863350 := by rw [factor_0_23]; decide
      change (6 : ZMod 65863351) ^ 32931675 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (6 : ZMod 65863351) ^ 1 = 6 := by norm_num
      have factor_1_1 : (6 : ZMod 65863351) ^ 2 = 36 := by
        calc
          (6 : ZMod 65863351) ^ 2 = (6 : ZMod 65863351) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 1 * (6 : ZMod 65863351) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_1_0]; decide
      have factor_1_2 : (6 : ZMod 65863351) ^ 5 = 7776 := by
        calc
          (6 : ZMod 65863351) ^ 5 = (6 : ZMod 65863351) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 2 * (6 : ZMod 65863351) ^ 2) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_1_1]; decide
      have factor_1_3 : (6 : ZMod 65863351) ^ 10 = 60466176 := by
        calc
          (6 : ZMod 65863351) ^ 10 = (6 : ZMod 65863351) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 5 * (6 : ZMod 65863351) ^ 5 := by rw [pow_add]
          _ = 60466176 := by rw [factor_1_2]; decide
      have factor_1_4 : (6 : ZMod 65863351) ^ 20 = 47870504 := by
        calc
          (6 : ZMod 65863351) ^ 20 = (6 : ZMod 65863351) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 10 * (6 : ZMod 65863351) ^ 10 := by rw [pow_add]
          _ = 47870504 := by rw [factor_1_3]; decide
      have factor_1_5 : (6 : ZMod 65863351) ^ 41 = 6903552 := by
        calc
          (6 : ZMod 65863351) ^ 41 = (6 : ZMod 65863351) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 20 * (6 : ZMod 65863351) ^ 20) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 6903552 := by rw [factor_1_4]; decide
      have factor_1_6 : (6 : ZMod 65863351) ^ 83 = 12424796 := by
        calc
          (6 : ZMod 65863351) ^ 83 = (6 : ZMod 65863351) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 41 * (6 : ZMod 65863351) ^ 41) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 12424796 := by rw [factor_1_5]; decide
      have factor_1_7 : (6 : ZMod 65863351) ^ 167 = 35992138 := by
        calc
          (6 : ZMod 65863351) ^ 167 = (6 : ZMod 65863351) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 83 * (6 : ZMod 65863351) ^ 83) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 35992138 := by rw [factor_1_6]; decide
      have factor_1_8 : (6 : ZMod 65863351) ^ 334 = 20034034 := by
        calc
          (6 : ZMod 65863351) ^ 334 = (6 : ZMod 65863351) ^ (167 + 167) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 167 * (6 : ZMod 65863351) ^ 167 := by rw [pow_add]
          _ = 20034034 := by rw [factor_1_7]; decide
      have factor_1_9 : (6 : ZMod 65863351) ^ 669 = 37005683 := by
        calc
          (6 : ZMod 65863351) ^ 669 = (6 : ZMod 65863351) ^ (334 + 334 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 334 * (6 : ZMod 65863351) ^ 334) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 37005683 := by rw [factor_1_8]; decide
      have factor_1_10 : (6 : ZMod 65863351) ^ 1339 = 606715 := by
        calc
          (6 : ZMod 65863351) ^ 1339 = (6 : ZMod 65863351) ^ (669 + 669 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 669 * (6 : ZMod 65863351) ^ 669) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 606715 := by rw [factor_1_9]; decide
      have factor_1_11 : (6 : ZMod 65863351) ^ 2679 = 22798267 := by
        calc
          (6 : ZMod 65863351) ^ 2679 = (6 : ZMod 65863351) ^ (1339 + 1339 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 1339 * (6 : ZMod 65863351) ^ 1339) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 22798267 := by rw [factor_1_10]; decide
      have factor_1_12 : (6 : ZMod 65863351) ^ 5359 = 20956853 := by
        calc
          (6 : ZMod 65863351) ^ 5359 = (6 : ZMod 65863351) ^ (2679 + 2679 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 2679 * (6 : ZMod 65863351) ^ 2679) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 20956853 := by rw [factor_1_11]; decide
      have factor_1_13 : (6 : ZMod 65863351) ^ 10719 = 53189633 := by
        calc
          (6 : ZMod 65863351) ^ 10719 = (6 : ZMod 65863351) ^ (5359 + 5359 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 5359 * (6 : ZMod 65863351) ^ 5359) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 53189633 := by rw [factor_1_12]; decide
      have factor_1_14 : (6 : ZMod 65863351) ^ 21439 = 2215446 := by
        calc
          (6 : ZMod 65863351) ^ 21439 = (6 : ZMod 65863351) ^ (10719 + 10719 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 10719 * (6 : ZMod 65863351) ^ 10719) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 2215446 := by rw [factor_1_13]; decide
      have factor_1_15 : (6 : ZMod 65863351) ^ 42879 = 55057621 := by
        calc
          (6 : ZMod 65863351) ^ 42879 = (6 : ZMod 65863351) ^ (21439 + 21439 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 21439 * (6 : ZMod 65863351) ^ 21439) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 55057621 := by rw [factor_1_14]; decide
      have factor_1_16 : (6 : ZMod 65863351) ^ 85759 = 4658586 := by
        calc
          (6 : ZMod 65863351) ^ 85759 = (6 : ZMod 65863351) ^ (42879 + 42879 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 42879 * (6 : ZMod 65863351) ^ 42879) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 4658586 := by rw [factor_1_15]; decide
      have factor_1_17 : (6 : ZMod 65863351) ^ 171519 = 61655336 := by
        calc
          (6 : ZMod 65863351) ^ 171519 = (6 : ZMod 65863351) ^ (85759 + 85759 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 85759 * (6 : ZMod 65863351) ^ 85759) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 61655336 := by rw [factor_1_16]; decide
      have factor_1_18 : (6 : ZMod 65863351) ^ 343038 = 28323875 := by
        calc
          (6 : ZMod 65863351) ^ 343038 = (6 : ZMod 65863351) ^ (171519 + 171519) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 171519 * (6 : ZMod 65863351) ^ 171519 := by rw [pow_add]
          _ = 28323875 := by rw [factor_1_17]; decide
      have factor_1_19 : (6 : ZMod 65863351) ^ 686076 = 358576 := by
        calc
          (6 : ZMod 65863351) ^ 686076 = (6 : ZMod 65863351) ^ (343038 + 343038) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 343038 * (6 : ZMod 65863351) ^ 343038 := by rw [pow_add]
          _ = 358576 := by rw [factor_1_18]; decide
      have factor_1_20 : (6 : ZMod 65863351) ^ 1372153 = 3056393 := by
        calc
          (6 : ZMod 65863351) ^ 1372153 = (6 : ZMod 65863351) ^ (686076 + 686076 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 686076 * (6 : ZMod 65863351) ^ 686076) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 3056393 := by rw [factor_1_19]; decide
      have factor_1_21 : (6 : ZMod 65863351) ^ 2744306 = 7371417 := by
        calc
          (6 : ZMod 65863351) ^ 2744306 = (6 : ZMod 65863351) ^ (1372153 + 1372153) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 1372153 * (6 : ZMod 65863351) ^ 1372153 := by rw [pow_add]
          _ = 7371417 := by rw [factor_1_20]; decide
      have factor_1_22 : (6 : ZMod 65863351) ^ 5488612 = 62969432 := by
        calc
          (6 : ZMod 65863351) ^ 5488612 = (6 : ZMod 65863351) ^ (2744306 + 2744306) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 2744306 * (6 : ZMod 65863351) ^ 2744306 := by rw [pow_add]
          _ = 62969432 := by rw [factor_1_21]; decide
      have factor_1_23 : (6 : ZMod 65863351) ^ 10977225 = 3599744 := by
        calc
          (6 : ZMod 65863351) ^ 10977225 = (6 : ZMod 65863351) ^ (5488612 + 5488612 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 5488612 * (6 : ZMod 65863351) ^ 5488612) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 3599744 := by rw [factor_1_22]; decide
      have factor_1_24 : (6 : ZMod 65863351) ^ 21954450 = 3599743 := by
        calc
          (6 : ZMod 65863351) ^ 21954450 = (6 : ZMod 65863351) ^ (10977225 + 10977225) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 10977225 * (6 : ZMod 65863351) ^ 10977225 := by rw [pow_add]
          _ = 3599743 := by rw [factor_1_23]; decide
      change (6 : ZMod 65863351) ^ 21954450 ≠ 1
      rw [factor_1_24]
      decide
    ·
      have factor_2_0 : (6 : ZMod 65863351) ^ 1 = 6 := by norm_num
      have factor_2_1 : (6 : ZMod 65863351) ^ 3 = 216 := by
        calc
          (6 : ZMod 65863351) ^ 3 = (6 : ZMod 65863351) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 1 * (6 : ZMod 65863351) ^ 1) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_2_0]; decide
      have factor_2_2 : (6 : ZMod 65863351) ^ 6 = 46656 := by
        calc
          (6 : ZMod 65863351) ^ 6 = (6 : ZMod 65863351) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 3 * (6 : ZMod 65863351) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [factor_2_1]; decide
      have factor_2_3 : (6 : ZMod 65863351) ^ 12 = 3291753 := by
        calc
          (6 : ZMod 65863351) ^ 12 = (6 : ZMod 65863351) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 6 * (6 : ZMod 65863351) ^ 6 := by rw [pow_add]
          _ = 3291753 := by rw [factor_2_2]; decide
      have factor_2_4 : (6 : ZMod 65863351) ^ 25 = 47242603 := by
        calc
          (6 : ZMod 65863351) ^ 25 = (6 : ZMod 65863351) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 12 * (6 : ZMod 65863351) ^ 12) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 47242603 := by rw [factor_2_3]; decide
      have factor_2_5 : (6 : ZMod 65863351) ^ 50 = 45534786 := by
        calc
          (6 : ZMod 65863351) ^ 50 = (6 : ZMod 65863351) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 25 * (6 : ZMod 65863351) ^ 25 := by rw [pow_add]
          _ = 45534786 := by rw [factor_2_4]; decide
      have factor_2_6 : (6 : ZMod 65863351) ^ 100 = 48252163 := by
        calc
          (6 : ZMod 65863351) ^ 100 = (6 : ZMod 65863351) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 50 * (6 : ZMod 65863351) ^ 50 := by rw [pow_add]
          _ = 48252163 := by rw [factor_2_5]; decide
      have factor_2_7 : (6 : ZMod 65863351) ^ 200 = 63881443 := by
        calc
          (6 : ZMod 65863351) ^ 200 = (6 : ZMod 65863351) ^ (100 + 100) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 100 * (6 : ZMod 65863351) ^ 100 := by rw [pow_add]
          _ = 63881443 := by rw [factor_2_6]; decide
      have factor_2_8 : (6 : ZMod 65863351) ^ 401 = 4761156 := by
        calc
          (6 : ZMod 65863351) ^ 401 = (6 : ZMod 65863351) ^ (200 + 200 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 200 * (6 : ZMod 65863351) ^ 200) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 4761156 := by rw [factor_2_7]; decide
      have factor_2_9 : (6 : ZMod 65863351) ^ 803 = 64712009 := by
        calc
          (6 : ZMod 65863351) ^ 803 = (6 : ZMod 65863351) ^ (401 + 401 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 401 * (6 : ZMod 65863351) ^ 401) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 64712009 := by rw [factor_2_8]; decide
      have factor_2_10 : (6 : ZMod 65863351) ^ 1607 = 3865726 := by
        calc
          (6 : ZMod 65863351) ^ 1607 = (6 : ZMod 65863351) ^ (803 + 803 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 803 * (6 : ZMod 65863351) ^ 803) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 3865726 := by rw [factor_2_9]; decide
      have factor_2_11 : (6 : ZMod 65863351) ^ 3215 = 18021957 := by
        calc
          (6 : ZMod 65863351) ^ 3215 = (6 : ZMod 65863351) ^ (1607 + 1607 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 1607 * (6 : ZMod 65863351) ^ 1607) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 18021957 := by rw [factor_2_10]; decide
      have factor_2_12 : (6 : ZMod 65863351) ^ 6431 = 7369586 := by
        calc
          (6 : ZMod 65863351) ^ 6431 = (6 : ZMod 65863351) ^ (3215 + 3215 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 3215 * (6 : ZMod 65863351) ^ 3215) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 7369586 := by rw [factor_2_11]; decide
      have factor_2_13 : (6 : ZMod 65863351) ^ 12863 = 61820988 := by
        calc
          (6 : ZMod 65863351) ^ 12863 = (6 : ZMod 65863351) ^ (6431 + 6431 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 6431 * (6 : ZMod 65863351) ^ 6431) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 61820988 := by rw [factor_2_12]; decide
      have factor_2_14 : (6 : ZMod 65863351) ^ 25727 = 7444014 := by
        calc
          (6 : ZMod 65863351) ^ 25727 = (6 : ZMod 65863351) ^ (12863 + 12863 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 12863 * (6 : ZMod 65863351) ^ 12863) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 7444014 := by rw [factor_2_13]; decide
      have factor_2_15 : (6 : ZMod 65863351) ^ 51455 = 26571348 := by
        calc
          (6 : ZMod 65863351) ^ 51455 = (6 : ZMod 65863351) ^ (25727 + 25727 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 25727 * (6 : ZMod 65863351) ^ 25727) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 26571348 := by rw [factor_2_14]; decide
      have factor_2_16 : (6 : ZMod 65863351) ^ 102911 = 43419218 := by
        calc
          (6 : ZMod 65863351) ^ 102911 = (6 : ZMod 65863351) ^ (51455 + 51455 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 51455 * (6 : ZMod 65863351) ^ 51455) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 43419218 := by rw [factor_2_15]; decide
      have factor_2_17 : (6 : ZMod 65863351) ^ 205822 = 61152694 := by
        calc
          (6 : ZMod 65863351) ^ 205822 = (6 : ZMod 65863351) ^ (102911 + 102911) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 102911 * (6 : ZMod 65863351) ^ 102911 := by rw [pow_add]
          _ = 61152694 := by rw [factor_2_16]; decide
      have factor_2_18 : (6 : ZMod 65863351) ^ 411645 = 25997010 := by
        calc
          (6 : ZMod 65863351) ^ 411645 = (6 : ZMod 65863351) ^ (205822 + 205822 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 205822 * (6 : ZMod 65863351) ^ 205822) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 25997010 := by rw [factor_2_17]; decide
      have factor_2_19 : (6 : ZMod 65863351) ^ 823291 = 19421316 := by
        calc
          (6 : ZMod 65863351) ^ 823291 = (6 : ZMod 65863351) ^ (411645 + 411645 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 411645 * (6 : ZMod 65863351) ^ 411645) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 19421316 := by rw [factor_2_18]; decide
      have factor_2_20 : (6 : ZMod 65863351) ^ 1646583 = 19841620 := by
        calc
          (6 : ZMod 65863351) ^ 1646583 = (6 : ZMod 65863351) ^ (823291 + 823291 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 823291 * (6 : ZMod 65863351) ^ 823291) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 19841620 := by rw [factor_2_19]; decide
      have factor_2_21 : (6 : ZMod 65863351) ^ 3293167 = 14424756 := by
        calc
          (6 : ZMod 65863351) ^ 3293167 = (6 : ZMod 65863351) ^ (1646583 + 1646583 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 1646583 * (6 : ZMod 65863351) ^ 1646583) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 14424756 := by rw [factor_2_20]; decide
      have factor_2_22 : (6 : ZMod 65863351) ^ 6586335 = 49168441 := by
        calc
          (6 : ZMod 65863351) ^ 6586335 = (6 : ZMod 65863351) ^ (3293167 + 3293167 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 3293167 * (6 : ZMod 65863351) ^ 3293167) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 49168441 := by rw [factor_2_21]; decide
      have factor_2_23 : (6 : ZMod 65863351) ^ 13172670 = 18053108 := by
        calc
          (6 : ZMod 65863351) ^ 13172670 = (6 : ZMod 65863351) ^ (6586335 + 6586335) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 6586335 * (6 : ZMod 65863351) ^ 6586335 := by rw [pow_add]
          _ = 18053108 := by rw [factor_2_22]; decide
      change (6 : ZMod 65863351) ^ 13172670 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (6 : ZMod 65863351) ^ 1 = 6 := by norm_num
      have factor_3_1 : (6 : ZMod 65863351) ^ 2 = 36 := by
        calc
          (6 : ZMod 65863351) ^ 2 = (6 : ZMod 65863351) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 1 * (6 : ZMod 65863351) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_3_0]; decide
      have factor_3_2 : (6 : ZMod 65863351) ^ 4 = 1296 := by
        calc
          (6 : ZMod 65863351) ^ 4 = (6 : ZMod 65863351) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 2 * (6 : ZMod 65863351) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_3_1]; decide
      have factor_3_3 : (6 : ZMod 65863351) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 65863351) ^ 8 = (6 : ZMod 65863351) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 4 * (6 : ZMod 65863351) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_3_2]; decide
      have factor_3_4 : (6 : ZMod 65863351) ^ 17 = 41691140 := by
        calc
          (6 : ZMod 65863351) ^ 17 = (6 : ZMod 65863351) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 8 * (6 : ZMod 65863351) ^ 8) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 41691140 := by rw [factor_3_3]; decide
      have factor_3_5 : (6 : ZMod 65863351) ^ 35 = 63153073 := by
        calc
          (6 : ZMod 65863351) ^ 35 = (6 : ZMod 65863351) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 17 * (6 : ZMod 65863351) ^ 17) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 63153073 := by rw [factor_3_4]; decide
      have factor_3_6 : (6 : ZMod 65863351) ^ 71 = 60025087 := by
        calc
          (6 : ZMod 65863351) ^ 71 = (6 : ZMod 65863351) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 35 * (6 : ZMod 65863351) ^ 35) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 60025087 := by rw [factor_3_5]; decide
      have factor_3_7 : (6 : ZMod 65863351) ^ 143 = 63192182 := by
        calc
          (6 : ZMod 65863351) ^ 143 = (6 : ZMod 65863351) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 71 * (6 : ZMod 65863351) ^ 71) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 63192182 := by rw [factor_3_6]; decide
      have factor_3_8 : (6 : ZMod 65863351) ^ 287 = 14126121 := by
        calc
          (6 : ZMod 65863351) ^ 287 = (6 : ZMod 65863351) ^ (143 + 143 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 143 * (6 : ZMod 65863351) ^ 143) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 14126121 := by rw [factor_3_7]; decide
      have factor_3_9 : (6 : ZMod 65863351) ^ 574 = 46168325 := by
        calc
          (6 : ZMod 65863351) ^ 574 = (6 : ZMod 65863351) ^ (287 + 287) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 287 * (6 : ZMod 65863351) ^ 287 := by rw [pow_add]
          _ = 46168325 := by rw [factor_3_8]; decide
      have factor_3_10 : (6 : ZMod 65863351) ^ 1148 = 10481700 := by
        calc
          (6 : ZMod 65863351) ^ 1148 = (6 : ZMod 65863351) ^ (574 + 574) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 574 * (6 : ZMod 65863351) ^ 574 := by rw [pow_add]
          _ = 10481700 := by rw [factor_3_9]; decide
      have factor_3_11 : (6 : ZMod 65863351) ^ 2297 = 28732407 := by
        calc
          (6 : ZMod 65863351) ^ 2297 = (6 : ZMod 65863351) ^ (1148 + 1148 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 1148 * (6 : ZMod 65863351) ^ 1148) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 28732407 := by rw [factor_3_10]; decide
      have factor_3_12 : (6 : ZMod 65863351) ^ 4594 = 13984296 := by
        calc
          (6 : ZMod 65863351) ^ 4594 = (6 : ZMod 65863351) ^ (2297 + 2297) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 2297 * (6 : ZMod 65863351) ^ 2297 := by rw [pow_add]
          _ = 13984296 := by rw [factor_3_11]; decide
      have factor_3_13 : (6 : ZMod 65863351) ^ 9188 = 60776681 := by
        calc
          (6 : ZMod 65863351) ^ 9188 = (6 : ZMod 65863351) ^ (4594 + 4594) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 4594 * (6 : ZMod 65863351) ^ 4594 := by rw [pow_add]
          _ = 60776681 := by rw [factor_3_12]; decide
      have factor_3_14 : (6 : ZMod 65863351) ^ 18377 = 16894969 := by
        calc
          (6 : ZMod 65863351) ^ 18377 = (6 : ZMod 65863351) ^ (9188 + 9188 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 9188 * (6 : ZMod 65863351) ^ 9188) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 16894969 := by rw [factor_3_13]; decide
      have factor_3_15 : (6 : ZMod 65863351) ^ 36754 = 3816790 := by
        calc
          (6 : ZMod 65863351) ^ 36754 = (6 : ZMod 65863351) ^ (18377 + 18377) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 18377 * (6 : ZMod 65863351) ^ 18377 := by rw [pow_add]
          _ = 3816790 := by rw [factor_3_14]; decide
      have factor_3_16 : (6 : ZMod 65863351) ^ 73508 = 32339867 := by
        calc
          (6 : ZMod 65863351) ^ 73508 = (6 : ZMod 65863351) ^ (36754 + 36754) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 36754 * (6 : ZMod 65863351) ^ 36754 := by rw [pow_add]
          _ = 32339867 := by rw [factor_3_15]; decide
      have factor_3_17 : (6 : ZMod 65863351) ^ 147016 = 58329243 := by
        calc
          (6 : ZMod 65863351) ^ 147016 = (6 : ZMod 65863351) ^ (73508 + 73508) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 73508 * (6 : ZMod 65863351) ^ 73508 := by rw [pow_add]
          _ = 58329243 := by rw [factor_3_16]; decide
      have factor_3_18 : (6 : ZMod 65863351) ^ 294032 = 35016738 := by
        calc
          (6 : ZMod 65863351) ^ 294032 = (6 : ZMod 65863351) ^ (147016 + 147016) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 147016 * (6 : ZMod 65863351) ^ 147016 := by rw [pow_add]
          _ = 35016738 := by rw [factor_3_17]; decide
      have factor_3_19 : (6 : ZMod 65863351) ^ 588065 = 29994967 := by
        calc
          (6 : ZMod 65863351) ^ 588065 = (6 : ZMod 65863351) ^ (294032 + 294032 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 294032 * (6 : ZMod 65863351) ^ 294032) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 29994967 := by rw [factor_3_18]; decide
      have factor_3_20 : (6 : ZMod 65863351) ^ 1176131 = 32102359 := by
        calc
          (6 : ZMod 65863351) ^ 1176131 = (6 : ZMod 65863351) ^ (588065 + 588065 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 588065 * (6 : ZMod 65863351) ^ 588065) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 32102359 := by rw [factor_3_19]; decide
      have factor_3_21 : (6 : ZMod 65863351) ^ 2352262 = 37211868 := by
        calc
          (6 : ZMod 65863351) ^ 2352262 = (6 : ZMod 65863351) ^ (1176131 + 1176131) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 1176131 * (6 : ZMod 65863351) ^ 1176131 := by rw [pow_add]
          _ = 37211868 := by rw [factor_3_20]; decide
      have factor_3_22 : (6 : ZMod 65863351) ^ 4704525 = 51383199 := by
        calc
          (6 : ZMod 65863351) ^ 4704525 = (6 : ZMod 65863351) ^ (2352262 + 2352262 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 2352262 * (6 : ZMod 65863351) ^ 2352262) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 51383199 := by rw [factor_3_21]; decide
      have factor_3_23 : (6 : ZMod 65863351) ^ 9409050 = 9574922 := by
        calc
          (6 : ZMod 65863351) ^ 9409050 = (6 : ZMod 65863351) ^ (4704525 + 4704525) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 4704525 * (6 : ZMod 65863351) ^ 4704525 := by rw [pow_add]
          _ = 9574922 := by rw [factor_3_22]; decide
      change (6 : ZMod 65863351) ^ 9409050 ≠ 1
      rw [factor_3_23]
      decide
    ·
      have factor_4_0 : (6 : ZMod 65863351) ^ 1 = 6 := by norm_num
      have factor_4_1 : (6 : ZMod 65863351) ^ 2 = 36 := by
        calc
          (6 : ZMod 65863351) ^ 2 = (6 : ZMod 65863351) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 1 * (6 : ZMod 65863351) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_4_0]; decide
      have factor_4_2 : (6 : ZMod 65863351) ^ 4 = 1296 := by
        calc
          (6 : ZMod 65863351) ^ 4 = (6 : ZMod 65863351) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 2 * (6 : ZMod 65863351) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_4_1]; decide
      have factor_4_3 : (6 : ZMod 65863351) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 65863351) ^ 8 = (6 : ZMod 65863351) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 4 * (6 : ZMod 65863351) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_4_2]; decide
      have factor_4_4 : (6 : ZMod 65863351) ^ 17 = 41691140 := by
        calc
          (6 : ZMod 65863351) ^ 17 = (6 : ZMod 65863351) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 8 * (6 : ZMod 65863351) ^ 8) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 41691140 := by rw [factor_4_3]; decide
      have factor_4_5 : (6 : ZMod 65863351) ^ 34 = 65411638 := by
        calc
          (6 : ZMod 65863351) ^ 34 = (6 : ZMod 65863351) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 17 * (6 : ZMod 65863351) ^ 17 := by rw [pow_add]
          _ = 65411638 := by rw [factor_4_4]; decide
      have factor_4_6 : (6 : ZMod 65863351) ^ 69 = 65701177 := by
        calc
          (6 : ZMod 65863351) ^ 69 = (6 : ZMod 65863351) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 34 * (6 : ZMod 65863351) ^ 34) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 65701177 := by rw [factor_4_5]; decide
      have factor_4_7 : (6 : ZMod 65863351) ^ 138 = 20929227 := by
        calc
          (6 : ZMod 65863351) ^ 138 = (6 : ZMod 65863351) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 69 * (6 : ZMod 65863351) ^ 69 := by rw [pow_add]
          _ = 20929227 := by rw [factor_4_6]; decide
      have factor_4_8 : (6 : ZMod 65863351) ^ 277 = 37532116 := by
        calc
          (6 : ZMod 65863351) ^ 277 = (6 : ZMod 65863351) ^ (138 + 138 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 138 * (6 : ZMod 65863351) ^ 138) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 37532116 := by rw [factor_4_7]; decide
      have factor_4_9 : (6 : ZMod 65863351) ^ 554 = 1092995 := by
        calc
          (6 : ZMod 65863351) ^ 554 = (6 : ZMod 65863351) ^ (277 + 277) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 277 * (6 : ZMod 65863351) ^ 277 := by rw [pow_add]
          _ = 1092995 := by rw [factor_4_8]; decide
      have factor_4_10 : (6 : ZMod 65863351) ^ 1108 = 8609587 := by
        calc
          (6 : ZMod 65863351) ^ 1108 = (6 : ZMod 65863351) ^ (554 + 554) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 554 * (6 : ZMod 65863351) ^ 554 := by rw [pow_add]
          _ = 8609587 := by rw [factor_4_9]; decide
      have factor_4_11 : (6 : ZMod 65863351) ^ 2217 = 12087198 := by
        calc
          (6 : ZMod 65863351) ^ 2217 = (6 : ZMod 65863351) ^ (1108 + 1108 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 1108 * (6 : ZMod 65863351) ^ 1108) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 12087198 := by rw [factor_4_10]; decide
      have factor_4_12 : (6 : ZMod 65863351) ^ 4435 = 53967718 := by
        calc
          (6 : ZMod 65863351) ^ 4435 = (6 : ZMod 65863351) ^ (2217 + 2217 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 2217 * (6 : ZMod 65863351) ^ 2217) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 53967718 := by rw [factor_4_11]; decide
      have factor_4_13 : (6 : ZMod 65863351) ^ 8871 = 18548605 := by
        calc
          (6 : ZMod 65863351) ^ 8871 = (6 : ZMod 65863351) ^ (4435 + 4435 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 4435 * (6 : ZMod 65863351) ^ 4435) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 18548605 := by rw [factor_4_12]; decide
      have factor_4_14 : (6 : ZMod 65863351) ^ 17743 = 57336718 := by
        calc
          (6 : ZMod 65863351) ^ 17743 = (6 : ZMod 65863351) ^ (8871 + 8871 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 8871 * (6 : ZMod 65863351) ^ 8871) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 57336718 := by rw [factor_4_13]; decide
      have factor_4_15 : (6 : ZMod 65863351) ^ 35486 = 12725286 := by
        calc
          (6 : ZMod 65863351) ^ 35486 = (6 : ZMod 65863351) ^ (17743 + 17743) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 17743 * (6 : ZMod 65863351) ^ 17743 := by rw [pow_add]
          _ = 12725286 := by rw [factor_4_14]; decide
      have factor_4_16 : (6 : ZMod 65863351) ^ 70973 = 39793811 := by
        calc
          (6 : ZMod 65863351) ^ 70973 = (6 : ZMod 65863351) ^ (35486 + 35486 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 35486 * (6 : ZMod 65863351) ^ 35486) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 39793811 := by rw [factor_4_15]; decide
      have factor_4_17 : (6 : ZMod 65863351) ^ 141946 = 49015450 := by
        calc
          (6 : ZMod 65863351) ^ 141946 = (6 : ZMod 65863351) ^ (70973 + 70973) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 70973 * (6 : ZMod 65863351) ^ 70973 := by rw [pow_add]
          _ = 49015450 := by rw [factor_4_16]; decide
      have factor_4_18 : (6 : ZMod 65863351) ^ 283893 = 7819162 := by
        calc
          (6 : ZMod 65863351) ^ 283893 = (6 : ZMod 65863351) ^ (141946 + 141946 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 141946 * (6 : ZMod 65863351) ^ 141946) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 7819162 := by rw [factor_4_17]; decide
      have factor_4_19 : (6 : ZMod 65863351) ^ 567787 = 19259665 := by
        calc
          (6 : ZMod 65863351) ^ 567787 = (6 : ZMod 65863351) ^ (283893 + 283893 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 283893 * (6 : ZMod 65863351) ^ 283893) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 19259665 := by rw [factor_4_18]; decide
      have factor_4_20 : (6 : ZMod 65863351) ^ 1135575 = 54553752 := by
        calc
          (6 : ZMod 65863351) ^ 1135575 = (6 : ZMod 65863351) ^ (567787 + 567787 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 567787 * (6 : ZMod 65863351) ^ 567787) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 54553752 := by rw [factor_4_19]; decide
      have factor_4_21 : (6 : ZMod 65863351) ^ 2271150 = 6718695 := by
        calc
          (6 : ZMod 65863351) ^ 2271150 = (6 : ZMod 65863351) ^ (1135575 + 1135575) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 1135575 * (6 : ZMod 65863351) ^ 1135575 := by rw [pow_add]
          _ = 6718695 := by rw [factor_4_20]; decide
      change (6 : ZMod 65863351) ^ 2271150 ≠ 1
      rw [factor_4_21]
      decide
    ·
      have factor_5_0 : (6 : ZMod 65863351) ^ 1 = 6 := by norm_num
      have factor_5_1 : (6 : ZMod 65863351) ^ 2 = 36 := by
        calc
          (6 : ZMod 65863351) ^ 2 = (6 : ZMod 65863351) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 1 * (6 : ZMod 65863351) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_5_0]; decide
      have factor_5_2 : (6 : ZMod 65863351) ^ 4 = 1296 := by
        calc
          (6 : ZMod 65863351) ^ 4 = (6 : ZMod 65863351) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 2 * (6 : ZMod 65863351) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_5_1]; decide
      have factor_5_3 : (6 : ZMod 65863351) ^ 9 = 10077696 := by
        calc
          (6 : ZMod 65863351) ^ 9 = (6 : ZMod 65863351) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 4 * (6 : ZMod 65863351) ^ 4) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 10077696 := by rw [factor_5_2]; decide
      have factor_5_4 : (6 : ZMod 65863351) ^ 19 = 51887318 := by
        calc
          (6 : ZMod 65863351) ^ 19 = (6 : ZMod 65863351) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 9 * (6 : ZMod 65863351) ^ 9) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 51887318 := by rw [factor_5_3]; decide
      have factor_5_5 : (6 : ZMod 65863351) ^ 39 = 44100666 := by
        calc
          (6 : ZMod 65863351) ^ 39 = (6 : ZMod 65863351) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 19 * (6 : ZMod 65863351) ^ 19) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 44100666 := by rw [factor_5_4]; decide
      have factor_5_6 : (6 : ZMod 65863351) ^ 78 = 58783961 := by
        calc
          (6 : ZMod 65863351) ^ 78 = (6 : ZMod 65863351) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 39 * (6 : ZMod 65863351) ^ 39 := by rw [pow_add]
          _ = 58783961 := by rw [factor_5_5]; decide
      have factor_5_7 : (6 : ZMod 65863351) ^ 156 = 33778915 := by
        calc
          (6 : ZMod 65863351) ^ 156 = (6 : ZMod 65863351) ^ (78 + 78) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 78 * (6 : ZMod 65863351) ^ 78 := by rw [pow_add]
          _ = 33778915 := by rw [factor_5_6]; decide
      have factor_5_8 : (6 : ZMod 65863351) ^ 312 = 52437000 := by
        calc
          (6 : ZMod 65863351) ^ 312 = (6 : ZMod 65863351) ^ (156 + 156) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 156 * (6 : ZMod 65863351) ^ 156 := by rw [pow_add]
          _ = 52437000 := by rw [factor_5_7]; decide
      have factor_5_9 : (6 : ZMod 65863351) ^ 624 = 29165168 := by
        calc
          (6 : ZMod 65863351) ^ 624 = (6 : ZMod 65863351) ^ (312 + 312) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 312 * (6 : ZMod 65863351) ^ 312 := by rw [pow_add]
          _ = 29165168 := by rw [factor_5_8]; decide
      have factor_5_10 : (6 : ZMod 65863351) ^ 1248 = 24588100 := by
        calc
          (6 : ZMod 65863351) ^ 1248 = (6 : ZMod 65863351) ^ (624 + 624) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 624 * (6 : ZMod 65863351) ^ 624 := by rw [pow_add]
          _ = 24588100 := by rw [factor_5_9]; decide
      have factor_5_11 : (6 : ZMod 65863351) ^ 2497 = 4938587 := by
        calc
          (6 : ZMod 65863351) ^ 2497 = (6 : ZMod 65863351) ^ (1248 + 1248 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 1248 * (6 : ZMod 65863351) ^ 1248) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 4938587 := by rw [factor_5_10]; decide
      have factor_5_12 : (6 : ZMod 65863351) ^ 4995 = 21553574 := by
        calc
          (6 : ZMod 65863351) ^ 4995 = (6 : ZMod 65863351) ^ (2497 + 2497 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 2497 * (6 : ZMod 65863351) ^ 2497) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 21553574 := by rw [factor_5_11]; decide
      have factor_5_13 : (6 : ZMod 65863351) ^ 9991 = 59366922 := by
        calc
          (6 : ZMod 65863351) ^ 9991 = (6 : ZMod 65863351) ^ (4995 + 4995 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 4995 * (6 : ZMod 65863351) ^ 4995) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 59366922 := by rw [factor_5_12]; decide
      have factor_5_14 : (6 : ZMod 65863351) ^ 19982 = 1015016 := by
        calc
          (6 : ZMod 65863351) ^ 19982 = (6 : ZMod 65863351) ^ (9991 + 9991) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 9991 * (6 : ZMod 65863351) ^ 9991 := by rw [pow_add]
          _ = 1015016 := by rw [factor_5_13]; decide
      have factor_5_15 : (6 : ZMod 65863351) ^ 39965 = 5936782 := by
        calc
          (6 : ZMod 65863351) ^ 39965 = (6 : ZMod 65863351) ^ (19982 + 19982 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 19982 * (6 : ZMod 65863351) ^ 19982) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 5936782 := by rw [factor_5_14]; decide
      have factor_5_16 : (6 : ZMod 65863351) ^ 79931 = 14012821 := by
        calc
          (6 : ZMod 65863351) ^ 79931 = (6 : ZMod 65863351) ^ (39965 + 39965 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 39965 * (6 : ZMod 65863351) ^ 39965) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 14012821 := by rw [factor_5_15]; decide
      have factor_5_17 : (6 : ZMod 65863351) ^ 159862 = 19544880 := by
        calc
          (6 : ZMod 65863351) ^ 159862 = (6 : ZMod 65863351) ^ (79931 + 79931) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 79931 * (6 : ZMod 65863351) ^ 79931 := by rw [pow_add]
          _ = 19544880 := by rw [factor_5_16]; decide
      have factor_5_18 : (6 : ZMod 65863351) ^ 319725 = 16944615 := by
        calc
          (6 : ZMod 65863351) ^ 319725 = (6 : ZMod 65863351) ^ (159862 + 159862 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = ((6 : ZMod 65863351) ^ 159862 * (6 : ZMod 65863351) ^ 159862) * (6 : ZMod 65863351) := by rw [pow_succ, pow_add]
          _ = 16944615 := by rw [factor_5_17]; decide
      have factor_5_19 : (6 : ZMod 65863351) ^ 639450 = 27310097 := by
        calc
          (6 : ZMod 65863351) ^ 639450 = (6 : ZMod 65863351) ^ (319725 + 319725) :=
            congrArg (fun n : ℕ => (6 : ZMod 65863351) ^ n) (by norm_num)
          _ = (6 : ZMod 65863351) ^ 319725 * (6 : ZMod 65863351) ^ 319725 := by rw [pow_add]
          _ = 27310097 := by rw [factor_5_18]; decide
      change (6 : ZMod 65863351) ^ 639450 ≠ 1
      rw [factor_5_19]
      decide

#print axioms prime_lucas_65863351

end TotientTailPeriodKiller
end Erdos249257
