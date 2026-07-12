import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_39404513 : Nat.Prime 39404513 := by
  apply lucas_primality 39404513 (3 : ZMod 39404513)
  ·
      have fermat_0 : (3 : ZMod 39404513) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 39404513) ^ 2 = 9 := by
        calc
          (3 : ZMod 39404513) ^ 2 = (3 : ZMod 39404513) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 1 * (3 : ZMod 39404513) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 39404513) ^ 4 = 81 := by
        calc
          (3 : ZMod 39404513) ^ 4 = (3 : ZMod 39404513) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 2 * (3 : ZMod 39404513) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 39404513) ^ 9 = 19683 := by
        calc
          (3 : ZMod 39404513) ^ 9 = (3 : ZMod 39404513) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 4 * (3 : ZMod 39404513) ^ 4) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 39404513) ^ 18 = 32779872 := by
        calc
          (3 : ZMod 39404513) ^ 18 = (3 : ZMod 39404513) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 9 * (3 : ZMod 39404513) ^ 9 := by rw [pow_add]
          _ = 32779872 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 39404513) ^ 37 = 34391303 := by
        calc
          (3 : ZMod 39404513) ^ 37 = (3 : ZMod 39404513) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 18 * (3 : ZMod 39404513) ^ 18) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 34391303 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 39404513) ^ 75 = 31315535 := by
        calc
          (3 : ZMod 39404513) ^ 75 = (3 : ZMod 39404513) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 37 * (3 : ZMod 39404513) ^ 37) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 31315535 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 39404513) ^ 150 = 16607367 := by
        calc
          (3 : ZMod 39404513) ^ 150 = (3 : ZMod 39404513) ^ (75 + 75) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 75 * (3 : ZMod 39404513) ^ 75 := by rw [pow_add]
          _ = 16607367 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 39404513) ^ 300 = 359581 := by
        calc
          (3 : ZMod 39404513) ^ 300 = (3 : ZMod 39404513) ^ (150 + 150) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 150 * (3 : ZMod 39404513) ^ 150 := by rw [pow_add]
          _ = 359581 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 39404513) ^ 601 = 36865224 := by
        calc
          (3 : ZMod 39404513) ^ 601 = (3 : ZMod 39404513) ^ (300 + 300 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 300 * (3 : ZMod 39404513) ^ 300) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 36865224 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 39404513) ^ 1202 = 31140766 := by
        calc
          (3 : ZMod 39404513) ^ 1202 = (3 : ZMod 39404513) ^ (601 + 601) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 601 * (3 : ZMod 39404513) ^ 601 := by rw [pow_add]
          _ = 31140766 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 39404513) ^ 2405 = 27643058 := by
        calc
          (3 : ZMod 39404513) ^ 2405 = (3 : ZMod 39404513) ^ (1202 + 1202 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 1202 * (3 : ZMod 39404513) ^ 1202) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 27643058 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 39404513) ^ 4810 = 34773284 := by
        calc
          (3 : ZMod 39404513) ^ 4810 = (3 : ZMod 39404513) ^ (2405 + 2405) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 2405 * (3 : ZMod 39404513) ^ 2405 := by rw [pow_add]
          _ = 34773284 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 39404513) ^ 9620 = 11579411 := by
        calc
          (3 : ZMod 39404513) ^ 9620 = (3 : ZMod 39404513) ^ (4810 + 4810) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 4810 * (3 : ZMod 39404513) ^ 4810 := by rw [pow_add]
          _ = 11579411 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 39404513) ^ 19240 = 37608996 := by
        calc
          (3 : ZMod 39404513) ^ 19240 = (3 : ZMod 39404513) ^ (9620 + 9620) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 9620 * (3 : ZMod 39404513) ^ 9620 := by rw [pow_add]
          _ = 37608996 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 39404513) ^ 38480 = 1066194 := by
        calc
          (3 : ZMod 39404513) ^ 38480 = (3 : ZMod 39404513) ^ (19240 + 19240) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 19240 * (3 : ZMod 39404513) ^ 19240 := by rw [pow_add]
          _ = 1066194 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 39404513) ^ 76961 = 5954810 := by
        calc
          (3 : ZMod 39404513) ^ 76961 = (3 : ZMod 39404513) ^ (38480 + 38480 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 38480 * (3 : ZMod 39404513) ^ 38480) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 5954810 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 39404513) ^ 153923 = 25988564 := by
        calc
          (3 : ZMod 39404513) ^ 153923 = (3 : ZMod 39404513) ^ (76961 + 76961 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 76961 * (3 : ZMod 39404513) ^ 76961) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 25988564 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 39404513) ^ 307847 = 26329815 := by
        calc
          (3 : ZMod 39404513) ^ 307847 = (3 : ZMod 39404513) ^ (153923 + 153923 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 153923 * (3 : ZMod 39404513) ^ 153923) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 26329815 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 39404513) ^ 615695 = 27232283 := by
        calc
          (3 : ZMod 39404513) ^ 615695 = (3 : ZMod 39404513) ^ (307847 + 307847 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 307847 * (3 : ZMod 39404513) ^ 307847) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 27232283 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 39404513) ^ 1231391 = 22920516 := by
        calc
          (3 : ZMod 39404513) ^ 1231391 = (3 : ZMod 39404513) ^ (615695 + 615695 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 615695 * (3 : ZMod 39404513) ^ 615695) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 22920516 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 39404513) ^ 2462782 = 23352266 := by
        calc
          (3 : ZMod 39404513) ^ 2462782 = (3 : ZMod 39404513) ^ (1231391 + 1231391) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 1231391 * (3 : ZMod 39404513) ^ 1231391 := by rw [pow_add]
          _ = 23352266 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 39404513) ^ 4925564 = 11867201 := by
        calc
          (3 : ZMod 39404513) ^ 4925564 = (3 : ZMod 39404513) ^ (2462782 + 2462782) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 2462782 * (3 : ZMod 39404513) ^ 2462782 := by rw [pow_add]
          _ = 11867201 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 39404513) ^ 9851128 = 30461330 := by
        calc
          (3 : ZMod 39404513) ^ 9851128 = (3 : ZMod 39404513) ^ (4925564 + 4925564) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 4925564 * (3 : ZMod 39404513) ^ 4925564 := by rw [pow_add]
          _ = 30461330 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 39404513) ^ 19702256 = 39404512 := by
        calc
          (3 : ZMod 39404513) ^ 19702256 = (3 : ZMod 39404513) ^ (9851128 + 9851128) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 9851128 * (3 : ZMod 39404513) ^ 9851128 := by rw [pow_add]
          _ = 39404512 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 39404513) ^ 39404512 = 1 := by
        calc
          (3 : ZMod 39404513) ^ 39404512 = (3 : ZMod 39404513) ^ (19702256 + 19702256) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 19702256 * (3 : ZMod 39404513) ^ 19702256 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (7, 1), (43, 1), (4091, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (7, 1), (43, 1), (4091, 1)] : List FactorBlock).map factorBlockValue).prod = 39404513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 39404513) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 39404513) ^ 2 = 9 := by
        calc
          (3 : ZMod 39404513) ^ 2 = (3 : ZMod 39404513) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 1 * (3 : ZMod 39404513) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 39404513) ^ 4 = 81 := by
        calc
          (3 : ZMod 39404513) ^ 4 = (3 : ZMod 39404513) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 2 * (3 : ZMod 39404513) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 39404513) ^ 9 = 19683 := by
        calc
          (3 : ZMod 39404513) ^ 9 = (3 : ZMod 39404513) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 4 * (3 : ZMod 39404513) ^ 4) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 39404513) ^ 18 = 32779872 := by
        calc
          (3 : ZMod 39404513) ^ 18 = (3 : ZMod 39404513) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 9 * (3 : ZMod 39404513) ^ 9 := by rw [pow_add]
          _ = 32779872 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 39404513) ^ 37 = 34391303 := by
        calc
          (3 : ZMod 39404513) ^ 37 = (3 : ZMod 39404513) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 18 * (3 : ZMod 39404513) ^ 18) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 34391303 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 39404513) ^ 75 = 31315535 := by
        calc
          (3 : ZMod 39404513) ^ 75 = (3 : ZMod 39404513) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 37 * (3 : ZMod 39404513) ^ 37) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 31315535 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 39404513) ^ 150 = 16607367 := by
        calc
          (3 : ZMod 39404513) ^ 150 = (3 : ZMod 39404513) ^ (75 + 75) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 75 * (3 : ZMod 39404513) ^ 75 := by rw [pow_add]
          _ = 16607367 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 39404513) ^ 300 = 359581 := by
        calc
          (3 : ZMod 39404513) ^ 300 = (3 : ZMod 39404513) ^ (150 + 150) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 150 * (3 : ZMod 39404513) ^ 150 := by rw [pow_add]
          _ = 359581 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 39404513) ^ 601 = 36865224 := by
        calc
          (3 : ZMod 39404513) ^ 601 = (3 : ZMod 39404513) ^ (300 + 300 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 300 * (3 : ZMod 39404513) ^ 300) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 36865224 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 39404513) ^ 1202 = 31140766 := by
        calc
          (3 : ZMod 39404513) ^ 1202 = (3 : ZMod 39404513) ^ (601 + 601) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 601 * (3 : ZMod 39404513) ^ 601 := by rw [pow_add]
          _ = 31140766 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 39404513) ^ 2405 = 27643058 := by
        calc
          (3 : ZMod 39404513) ^ 2405 = (3 : ZMod 39404513) ^ (1202 + 1202 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 1202 * (3 : ZMod 39404513) ^ 1202) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 27643058 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 39404513) ^ 4810 = 34773284 := by
        calc
          (3 : ZMod 39404513) ^ 4810 = (3 : ZMod 39404513) ^ (2405 + 2405) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 2405 * (3 : ZMod 39404513) ^ 2405 := by rw [pow_add]
          _ = 34773284 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 39404513) ^ 9620 = 11579411 := by
        calc
          (3 : ZMod 39404513) ^ 9620 = (3 : ZMod 39404513) ^ (4810 + 4810) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 4810 * (3 : ZMod 39404513) ^ 4810 := by rw [pow_add]
          _ = 11579411 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 39404513) ^ 19240 = 37608996 := by
        calc
          (3 : ZMod 39404513) ^ 19240 = (3 : ZMod 39404513) ^ (9620 + 9620) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 9620 * (3 : ZMod 39404513) ^ 9620 := by rw [pow_add]
          _ = 37608996 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 39404513) ^ 38480 = 1066194 := by
        calc
          (3 : ZMod 39404513) ^ 38480 = (3 : ZMod 39404513) ^ (19240 + 19240) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 19240 * (3 : ZMod 39404513) ^ 19240 := by rw [pow_add]
          _ = 1066194 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 39404513) ^ 76961 = 5954810 := by
        calc
          (3 : ZMod 39404513) ^ 76961 = (3 : ZMod 39404513) ^ (38480 + 38480 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 38480 * (3 : ZMod 39404513) ^ 38480) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 5954810 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 39404513) ^ 153923 = 25988564 := by
        calc
          (3 : ZMod 39404513) ^ 153923 = (3 : ZMod 39404513) ^ (76961 + 76961 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 76961 * (3 : ZMod 39404513) ^ 76961) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 25988564 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 39404513) ^ 307847 = 26329815 := by
        calc
          (3 : ZMod 39404513) ^ 307847 = (3 : ZMod 39404513) ^ (153923 + 153923 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 153923 * (3 : ZMod 39404513) ^ 153923) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 26329815 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 39404513) ^ 615695 = 27232283 := by
        calc
          (3 : ZMod 39404513) ^ 615695 = (3 : ZMod 39404513) ^ (307847 + 307847 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 307847 * (3 : ZMod 39404513) ^ 307847) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 27232283 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 39404513) ^ 1231391 = 22920516 := by
        calc
          (3 : ZMod 39404513) ^ 1231391 = (3 : ZMod 39404513) ^ (615695 + 615695 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 615695 * (3 : ZMod 39404513) ^ 615695) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 22920516 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 39404513) ^ 2462782 = 23352266 := by
        calc
          (3 : ZMod 39404513) ^ 2462782 = (3 : ZMod 39404513) ^ (1231391 + 1231391) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 1231391 * (3 : ZMod 39404513) ^ 1231391 := by rw [pow_add]
          _ = 23352266 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 39404513) ^ 4925564 = 11867201 := by
        calc
          (3 : ZMod 39404513) ^ 4925564 = (3 : ZMod 39404513) ^ (2462782 + 2462782) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 2462782 * (3 : ZMod 39404513) ^ 2462782 := by rw [pow_add]
          _ = 11867201 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 39404513) ^ 9851128 = 30461330 := by
        calc
          (3 : ZMod 39404513) ^ 9851128 = (3 : ZMod 39404513) ^ (4925564 + 4925564) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 4925564 * (3 : ZMod 39404513) ^ 4925564 := by rw [pow_add]
          _ = 30461330 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 39404513) ^ 19702256 = 39404512 := by
        calc
          (3 : ZMod 39404513) ^ 19702256 = (3 : ZMod 39404513) ^ (9851128 + 9851128) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 9851128 * (3 : ZMod 39404513) ^ 9851128 := by rw [pow_add]
          _ = 39404512 := by rw [factor_0_23]; decide
      change (3 : ZMod 39404513) ^ 19702256 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (3 : ZMod 39404513) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 39404513) ^ 2 = 9 := by
        calc
          (3 : ZMod 39404513) ^ 2 = (3 : ZMod 39404513) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 1 * (3 : ZMod 39404513) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 39404513) ^ 5 = 243 := by
        calc
          (3 : ZMod 39404513) ^ 5 = (3 : ZMod 39404513) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 2 * (3 : ZMod 39404513) ^ 2) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 39404513) ^ 10 = 59049 := by
        calc
          (3 : ZMod 39404513) ^ 10 = (3 : ZMod 39404513) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 5 * (3 : ZMod 39404513) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 39404513) ^ 21 = 18157258 := by
        calc
          (3 : ZMod 39404513) ^ 21 = (3 : ZMod 39404513) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 10 * (3 : ZMod 39404513) ^ 10) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 18157258 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 39404513) ^ 42 = 3329873 := by
        calc
          (3 : ZMod 39404513) ^ 42 = (3 : ZMod 39404513) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 21 * (3 : ZMod 39404513) ^ 21 := by rw [pow_add]
          _ = 3329873 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 39404513) ^ 85 = 15444664 := by
        calc
          (3 : ZMod 39404513) ^ 85 = (3 : ZMod 39404513) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 42 * (3 : ZMod 39404513) ^ 42) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 15444664 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 39404513) ^ 171 = 29451796 := by
        calc
          (3 : ZMod 39404513) ^ 171 = (3 : ZMod 39404513) ^ (85 + 85 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 85 * (3 : ZMod 39404513) ^ 85) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 29451796 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 39404513) ^ 343 = 1189072 := by
        calc
          (3 : ZMod 39404513) ^ 343 = (3 : ZMod 39404513) ^ (171 + 171 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 171 * (3 : ZMod 39404513) ^ 171) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 1189072 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 39404513) ^ 687 = 17266180 := by
        calc
          (3 : ZMod 39404513) ^ 687 = (3 : ZMod 39404513) ^ (343 + 343 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 343 * (3 : ZMod 39404513) ^ 343) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 17266180 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 39404513) ^ 1374 = 20991385 := by
        calc
          (3 : ZMod 39404513) ^ 1374 = (3 : ZMod 39404513) ^ (687 + 687) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 687 * (3 : ZMod 39404513) ^ 687 := by rw [pow_add]
          _ = 20991385 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 39404513) ^ 2748 = 35911635 := by
        calc
          (3 : ZMod 39404513) ^ 2748 = (3 : ZMod 39404513) ^ (1374 + 1374) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 1374 * (3 : ZMod 39404513) ^ 1374 := by rw [pow_add]
          _ = 35911635 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 39404513) ^ 5497 = 23504706 := by
        calc
          (3 : ZMod 39404513) ^ 5497 = (3 : ZMod 39404513) ^ (2748 + 2748 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 2748 * (3 : ZMod 39404513) ^ 2748) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 23504706 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 39404513) ^ 10994 = 32607371 := by
        calc
          (3 : ZMod 39404513) ^ 10994 = (3 : ZMod 39404513) ^ (5497 + 5497) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 5497 * (3 : ZMod 39404513) ^ 5497 := by rw [pow_add]
          _ = 32607371 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 39404513) ^ 21989 = 13852642 := by
        calc
          (3 : ZMod 39404513) ^ 21989 = (3 : ZMod 39404513) ^ (10994 + 10994 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 10994 * (3 : ZMod 39404513) ^ 10994) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 13852642 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 39404513) ^ 43978 = 7162081 := by
        calc
          (3 : ZMod 39404513) ^ 43978 = (3 : ZMod 39404513) ^ (21989 + 21989) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 21989 * (3 : ZMod 39404513) ^ 21989 := by rw [pow_add]
          _ = 7162081 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 39404513) ^ 87956 = 27789629 := by
        calc
          (3 : ZMod 39404513) ^ 87956 = (3 : ZMod 39404513) ^ (43978 + 43978) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 43978 * (3 : ZMod 39404513) ^ 43978 := by rw [pow_add]
          _ = 27789629 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 39404513) ^ 175913 = 9598734 := by
        calc
          (3 : ZMod 39404513) ^ 175913 = (3 : ZMod 39404513) ^ (87956 + 87956 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 87956 * (3 : ZMod 39404513) ^ 87956) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 9598734 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 39404513) ^ 351826 = 22701643 := by
        calc
          (3 : ZMod 39404513) ^ 351826 = (3 : ZMod 39404513) ^ (175913 + 175913) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 175913 * (3 : ZMod 39404513) ^ 175913 := by rw [pow_add]
          _ = 22701643 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 39404513) ^ 703652 = 22780276 := by
        calc
          (3 : ZMod 39404513) ^ 703652 = (3 : ZMod 39404513) ^ (351826 + 351826) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 351826 * (3 : ZMod 39404513) ^ 351826 := by rw [pow_add]
          _ = 22780276 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 39404513) ^ 1407304 = 9512610 := by
        calc
          (3 : ZMod 39404513) ^ 1407304 = (3 : ZMod 39404513) ^ (703652 + 703652) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 703652 * (3 : ZMod 39404513) ^ 703652 := by rw [pow_add]
          _ = 9512610 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 39404513) ^ 2814608 = 3818997 := by
        calc
          (3 : ZMod 39404513) ^ 2814608 = (3 : ZMod 39404513) ^ (1407304 + 1407304) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 1407304 * (3 : ZMod 39404513) ^ 1407304 := by rw [pow_add]
          _ = 3818997 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 39404513) ^ 5629216 = 24498345 := by
        calc
          (3 : ZMod 39404513) ^ 5629216 = (3 : ZMod 39404513) ^ (2814608 + 2814608) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 2814608 * (3 : ZMod 39404513) ^ 2814608 := by rw [pow_add]
          _ = 24498345 := by rw [factor_1_21]; decide
      change (3 : ZMod 39404513) ^ 5629216 ≠ 1
      rw [factor_1_22]
      decide
    ·
      have factor_2_0 : (3 : ZMod 39404513) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 39404513) ^ 3 = 27 := by
        calc
          (3 : ZMod 39404513) ^ 3 = (3 : ZMod 39404513) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 1 * (3 : ZMod 39404513) ^ 1) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 39404513) ^ 6 = 729 := by
        calc
          (3 : ZMod 39404513) ^ 6 = (3 : ZMod 39404513) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 3 * (3 : ZMod 39404513) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 39404513) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 39404513) ^ 13 = (3 : ZMod 39404513) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 6 * (3 : ZMod 39404513) ^ 6) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 39404513) ^ 27 = 36129227 := by
        calc
          (3 : ZMod 39404513) ^ 27 = (3 : ZMod 39404513) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 13 * (3 : ZMod 39404513) ^ 13) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 36129227 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 39404513) ^ 55 = 1883515 := by
        calc
          (3 : ZMod 39404513) ^ 55 = (3 : ZMod 39404513) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 27 * (3 : ZMod 39404513) ^ 27) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 1883515 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 39404513) ^ 111 = 3135966 := by
        calc
          (3 : ZMod 39404513) ^ 111 = (3 : ZMod 39404513) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 55 * (3 : ZMod 39404513) ^ 55) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 3135966 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 39404513) ^ 223 = 19499647 := by
        calc
          (3 : ZMod 39404513) ^ 223 = (3 : ZMod 39404513) ^ (111 + 111 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 111 * (3 : ZMod 39404513) ^ 111) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 19499647 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 39404513) ^ 447 = 22576474 := by
        calc
          (3 : ZMod 39404513) ^ 447 = (3 : ZMod 39404513) ^ (223 + 223 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 223 * (3 : ZMod 39404513) ^ 223) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 22576474 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 39404513) ^ 894 = 39044754 := by
        calc
          (3 : ZMod 39404513) ^ 894 = (3 : ZMod 39404513) ^ (447 + 447) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 447 * (3 : ZMod 39404513) ^ 447 := by rw [pow_add]
          _ = 39044754 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 39404513) ^ 1789 = 26947654 := by
        calc
          (3 : ZMod 39404513) ^ 1789 = (3 : ZMod 39404513) ^ (894 + 894 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 894 * (3 : ZMod 39404513) ^ 894) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 26947654 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 39404513) ^ 3579 = 17419768 := by
        calc
          (3 : ZMod 39404513) ^ 3579 = (3 : ZMod 39404513) ^ (1789 + 1789 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 1789 * (3 : ZMod 39404513) ^ 1789) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 17419768 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 39404513) ^ 7159 = 22690757 := by
        calc
          (3 : ZMod 39404513) ^ 7159 = (3 : ZMod 39404513) ^ (3579 + 3579 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 3579 * (3 : ZMod 39404513) ^ 3579) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 22690757 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 39404513) ^ 14318 = 13706896 := by
        calc
          (3 : ZMod 39404513) ^ 14318 = (3 : ZMod 39404513) ^ (7159 + 7159) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 7159 * (3 : ZMod 39404513) ^ 7159 := by rw [pow_add]
          _ = 13706896 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 39404513) ^ 28637 = 1903651 := by
        calc
          (3 : ZMod 39404513) ^ 28637 = (3 : ZMod 39404513) ^ (14318 + 14318 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 14318 * (3 : ZMod 39404513) ^ 14318) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 1903651 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 39404513) ^ 57274 = 11687243 := by
        calc
          (3 : ZMod 39404513) ^ 57274 = (3 : ZMod 39404513) ^ (28637 + 28637) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 28637 * (3 : ZMod 39404513) ^ 28637 := by rw [pow_add]
          _ = 11687243 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 39404513) ^ 114548 = 2695901 := by
        calc
          (3 : ZMod 39404513) ^ 114548 = (3 : ZMod 39404513) ^ (57274 + 57274) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 57274 * (3 : ZMod 39404513) ^ 57274 := by rw [pow_add]
          _ = 2695901 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 39404513) ^ 229096 = 35015055 := by
        calc
          (3 : ZMod 39404513) ^ 229096 = (3 : ZMod 39404513) ^ (114548 + 114548) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 114548 * (3 : ZMod 39404513) ^ 114548 := by rw [pow_add]
          _ = 35015055 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 39404513) ^ 458192 = 32048258 := by
        calc
          (3 : ZMod 39404513) ^ 458192 = (3 : ZMod 39404513) ^ (229096 + 229096) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 229096 * (3 : ZMod 39404513) ^ 229096 := by rw [pow_add]
          _ = 32048258 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 39404513) ^ 916384 = 33495047 := by
        calc
          (3 : ZMod 39404513) ^ 916384 = (3 : ZMod 39404513) ^ (458192 + 458192) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 458192 * (3 : ZMod 39404513) ^ 458192 := by rw [pow_add]
          _ = 33495047 := by rw [factor_2_18]; decide
      change (3 : ZMod 39404513) ^ 916384 ≠ 1
      rw [factor_2_19]
      decide
    ·
      have factor_3_0 : (3 : ZMod 39404513) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 39404513) ^ 2 = 9 := by
        calc
          (3 : ZMod 39404513) ^ 2 = (3 : ZMod 39404513) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 1 * (3 : ZMod 39404513) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 39404513) ^ 4 = 81 := by
        calc
          (3 : ZMod 39404513) ^ 4 = (3 : ZMod 39404513) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 2 * (3 : ZMod 39404513) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 39404513) ^ 9 = 19683 := by
        calc
          (3 : ZMod 39404513) ^ 9 = (3 : ZMod 39404513) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 4 * (3 : ZMod 39404513) ^ 4) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 39404513) ^ 18 = 32779872 := by
        calc
          (3 : ZMod 39404513) ^ 18 = (3 : ZMod 39404513) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 9 * (3 : ZMod 39404513) ^ 9 := by rw [pow_add]
          _ = 32779872 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 39404513) ^ 37 = 34391303 := by
        calc
          (3 : ZMod 39404513) ^ 37 = (3 : ZMod 39404513) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 18 * (3 : ZMod 39404513) ^ 18) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 34391303 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 39404513) ^ 75 = 31315535 := by
        calc
          (3 : ZMod 39404513) ^ 75 = (3 : ZMod 39404513) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 37 * (3 : ZMod 39404513) ^ 37) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 31315535 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 39404513) ^ 150 = 16607367 := by
        calc
          (3 : ZMod 39404513) ^ 150 = (3 : ZMod 39404513) ^ (75 + 75) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 75 * (3 : ZMod 39404513) ^ 75 := by rw [pow_add]
          _ = 16607367 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 39404513) ^ 301 = 1078743 := by
        calc
          (3 : ZMod 39404513) ^ 301 = (3 : ZMod 39404513) ^ (150 + 150 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = ((3 : ZMod 39404513) ^ 150 * (3 : ZMod 39404513) ^ 150) * (3 : ZMod 39404513) := by rw [pow_succ, pow_add]
          _ = 1078743 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 39404513) ^ 602 = 31786646 := by
        calc
          (3 : ZMod 39404513) ^ 602 = (3 : ZMod 39404513) ^ (301 + 301) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 301 * (3 : ZMod 39404513) ^ 301 := by rw [pow_add]
          _ = 31786646 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 39404513) ^ 1204 = 4435303 := by
        calc
          (3 : ZMod 39404513) ^ 1204 = (3 : ZMod 39404513) ^ (602 + 602) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 602 * (3 : ZMod 39404513) ^ 602 := by rw [pow_add]
          _ = 4435303 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 39404513) ^ 2408 = 37081332 := by
        calc
          (3 : ZMod 39404513) ^ 2408 = (3 : ZMod 39404513) ^ (1204 + 1204) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 1204 * (3 : ZMod 39404513) ^ 1204 := by rw [pow_add]
          _ = 37081332 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 39404513) ^ 4816 = 12622177 := by
        calc
          (3 : ZMod 39404513) ^ 4816 = (3 : ZMod 39404513) ^ (2408 + 2408) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 2408 * (3 : ZMod 39404513) ^ 2408 := by rw [pow_add]
          _ = 12622177 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 39404513) ^ 9632 = 10370554 := by
        calc
          (3 : ZMod 39404513) ^ 9632 = (3 : ZMod 39404513) ^ (4816 + 4816) :=
            congrArg (fun n : ℕ => (3 : ZMod 39404513) ^ n) (by norm_num)
          _ = (3 : ZMod 39404513) ^ 4816 * (3 : ZMod 39404513) ^ 4816 := by rw [pow_add]
          _ = 10370554 := by rw [factor_3_12]; decide
      change (3 : ZMod 39404513) ^ 9632 ≠ 1
      rw [factor_3_13]
      decide

#print axioms prime_lucas_39404513

end TotientTailPeriodKiller
end Erdos249257
