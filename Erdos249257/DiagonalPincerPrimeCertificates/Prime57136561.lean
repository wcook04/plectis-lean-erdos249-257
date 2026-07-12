import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_57136561 : Nat.Prime 57136561 := by
  apply lucas_primality 57136561 (7 : ZMod 57136561)
  ·
      have fermat_0 : (7 : ZMod 57136561) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 57136561) ^ 3 = 343 := by
        calc
          (7 : ZMod 57136561) ^ 3 = (7 : ZMod 57136561) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 1 * (7 : ZMod 57136561) ^ 1) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 57136561) ^ 6 = 117649 := by
        calc
          (7 : ZMod 57136561) ^ 6 = (7 : ZMod 57136561) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 3 * (7 : ZMod 57136561) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 57136561) ^ 13 = 42539512 := by
        calc
          (7 : ZMod 57136561) ^ 13 = (7 : ZMod 57136561) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 6 * (7 : ZMod 57136561) ^ 6) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 42539512 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 57136561) ^ 27 = 33722626 := by
        calc
          (7 : ZMod 57136561) ^ 27 = (7 : ZMod 57136561) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 13 * (7 : ZMod 57136561) ^ 13) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 33722626 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 57136561) ^ 54 = 19388572 := by
        calc
          (7 : ZMod 57136561) ^ 54 = (7 : ZMod 57136561) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 27 * (7 : ZMod 57136561) ^ 27 := by rw [pow_add]
          _ = 19388572 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 57136561) ^ 108 = 33918397 := by
        calc
          (7 : ZMod 57136561) ^ 108 = (7 : ZMod 57136561) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 54 * (7 : ZMod 57136561) ^ 54 := by rw [pow_add]
          _ = 33918397 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 57136561) ^ 217 = 33797151 := by
        calc
          (7 : ZMod 57136561) ^ 217 = (7 : ZMod 57136561) ^ (108 + 108 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 108 * (7 : ZMod 57136561) ^ 108) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 33797151 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 57136561) ^ 435 = 25397760 := by
        calc
          (7 : ZMod 57136561) ^ 435 = (7 : ZMod 57136561) ^ (217 + 217 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 217 * (7 : ZMod 57136561) ^ 217) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 25397760 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 57136561) ^ 871 = 27002252 := by
        calc
          (7 : ZMod 57136561) ^ 871 = (7 : ZMod 57136561) ^ (435 + 435 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 435 * (7 : ZMod 57136561) ^ 435) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 27002252 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 57136561) ^ 1743 = 51415449 := by
        calc
          (7 : ZMod 57136561) ^ 1743 = (7 : ZMod 57136561) ^ (871 + 871 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 871 * (7 : ZMod 57136561) ^ 871) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 51415449 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 57136561) ^ 3487 = 19459564 := by
        calc
          (7 : ZMod 57136561) ^ 3487 = (7 : ZMod 57136561) ^ (1743 + 1743 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 1743 * (7 : ZMod 57136561) ^ 1743) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 19459564 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 57136561) ^ 6974 = 16126400 := by
        calc
          (7 : ZMod 57136561) ^ 6974 = (7 : ZMod 57136561) ^ (3487 + 3487) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 3487 * (7 : ZMod 57136561) ^ 3487 := by rw [pow_add]
          _ = 16126400 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 57136561) ^ 13949 = 39844245 := by
        calc
          (7 : ZMod 57136561) ^ 13949 = (7 : ZMod 57136561) ^ (6974 + 6974 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 6974 * (7 : ZMod 57136561) ^ 6974) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 39844245 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 57136561) ^ 27898 = 650356 := by
        calc
          (7 : ZMod 57136561) ^ 27898 = (7 : ZMod 57136561) ^ (13949 + 13949) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 13949 * (7 : ZMod 57136561) ^ 13949 := by rw [pow_add]
          _ = 650356 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 57136561) ^ 55797 = 38169254 := by
        calc
          (7 : ZMod 57136561) ^ 55797 = (7 : ZMod 57136561) ^ (27898 + 27898 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 27898 * (7 : ZMod 57136561) ^ 27898) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 38169254 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 57136561) ^ 111594 = 35456018 := by
        calc
          (7 : ZMod 57136561) ^ 111594 = (7 : ZMod 57136561) ^ (55797 + 55797) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 55797 * (7 : ZMod 57136561) ^ 55797 := by rw [pow_add]
          _ = 35456018 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 57136561) ^ 223189 = 17804090 := by
        calc
          (7 : ZMod 57136561) ^ 223189 = (7 : ZMod 57136561) ^ (111594 + 111594 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 111594 * (7 : ZMod 57136561) ^ 111594) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 17804090 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 57136561) ^ 446379 = 27340163 := by
        calc
          (7 : ZMod 57136561) ^ 446379 = (7 : ZMod 57136561) ^ (223189 + 223189 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 223189 * (7 : ZMod 57136561) ^ 223189) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 27340163 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 57136561) ^ 892758 = 24508949 := by
        calc
          (7 : ZMod 57136561) ^ 892758 = (7 : ZMod 57136561) ^ (446379 + 446379) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 446379 * (7 : ZMod 57136561) ^ 446379 := by rw [pow_add]
          _ = 24508949 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 57136561) ^ 1785517 = 44798708 := by
        calc
          (7 : ZMod 57136561) ^ 1785517 = (7 : ZMod 57136561) ^ (892758 + 892758 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 892758 * (7 : ZMod 57136561) ^ 892758) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 44798708 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 57136561) ^ 3571035 = 21075938 := by
        calc
          (7 : ZMod 57136561) ^ 3571035 = (7 : ZMod 57136561) ^ (1785517 + 1785517 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 1785517 * (7 : ZMod 57136561) ^ 1785517) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 21075938 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 57136561) ^ 7142070 = 53357813 := by
        calc
          (7 : ZMod 57136561) ^ 7142070 = (7 : ZMod 57136561) ^ (3571035 + 3571035) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 3571035 * (7 : ZMod 57136561) ^ 3571035 := by rw [pow_add]
          _ = 53357813 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 57136561) ^ 14284140 = 52761116 := by
        calc
          (7 : ZMod 57136561) ^ 14284140 = (7 : ZMod 57136561) ^ (7142070 + 7142070) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 7142070 * (7 : ZMod 57136561) ^ 7142070 := by rw [pow_add]
          _ = 52761116 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 57136561) ^ 28568280 = 57136560 := by
        calc
          (7 : ZMod 57136561) ^ 28568280 = (7 : ZMod 57136561) ^ (14284140 + 14284140) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 14284140 * (7 : ZMod 57136561) ^ 14284140 := by rw [pow_add]
          _ = 57136560 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 57136561) ^ 57136560 = 1 := by
        calc
          (7 : ZMod 57136561) ^ 57136560 = (7 : ZMod 57136561) ^ (28568280 + 28568280) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 28568280 * (7 : ZMod 57136561) ^ 28568280 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (13, 1), (18313, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (13, 1), (18313, 1)] : List FactorBlock).map factorBlockValue).prod = 57136561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 57136561) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 57136561) ^ 3 = 343 := by
        calc
          (7 : ZMod 57136561) ^ 3 = (7 : ZMod 57136561) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 1 * (7 : ZMod 57136561) ^ 1) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 57136561) ^ 6 = 117649 := by
        calc
          (7 : ZMod 57136561) ^ 6 = (7 : ZMod 57136561) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 3 * (7 : ZMod 57136561) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 57136561) ^ 13 = 42539512 := by
        calc
          (7 : ZMod 57136561) ^ 13 = (7 : ZMod 57136561) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 6 * (7 : ZMod 57136561) ^ 6) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 42539512 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 57136561) ^ 27 = 33722626 := by
        calc
          (7 : ZMod 57136561) ^ 27 = (7 : ZMod 57136561) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 13 * (7 : ZMod 57136561) ^ 13) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 33722626 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 57136561) ^ 54 = 19388572 := by
        calc
          (7 : ZMod 57136561) ^ 54 = (7 : ZMod 57136561) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 27 * (7 : ZMod 57136561) ^ 27 := by rw [pow_add]
          _ = 19388572 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 57136561) ^ 108 = 33918397 := by
        calc
          (7 : ZMod 57136561) ^ 108 = (7 : ZMod 57136561) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 54 * (7 : ZMod 57136561) ^ 54 := by rw [pow_add]
          _ = 33918397 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 57136561) ^ 217 = 33797151 := by
        calc
          (7 : ZMod 57136561) ^ 217 = (7 : ZMod 57136561) ^ (108 + 108 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 108 * (7 : ZMod 57136561) ^ 108) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 33797151 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 57136561) ^ 435 = 25397760 := by
        calc
          (7 : ZMod 57136561) ^ 435 = (7 : ZMod 57136561) ^ (217 + 217 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 217 * (7 : ZMod 57136561) ^ 217) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 25397760 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 57136561) ^ 871 = 27002252 := by
        calc
          (7 : ZMod 57136561) ^ 871 = (7 : ZMod 57136561) ^ (435 + 435 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 435 * (7 : ZMod 57136561) ^ 435) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 27002252 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 57136561) ^ 1743 = 51415449 := by
        calc
          (7 : ZMod 57136561) ^ 1743 = (7 : ZMod 57136561) ^ (871 + 871 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 871 * (7 : ZMod 57136561) ^ 871) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 51415449 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 57136561) ^ 3487 = 19459564 := by
        calc
          (7 : ZMod 57136561) ^ 3487 = (7 : ZMod 57136561) ^ (1743 + 1743 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 1743 * (7 : ZMod 57136561) ^ 1743) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 19459564 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 57136561) ^ 6974 = 16126400 := by
        calc
          (7 : ZMod 57136561) ^ 6974 = (7 : ZMod 57136561) ^ (3487 + 3487) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 3487 * (7 : ZMod 57136561) ^ 3487 := by rw [pow_add]
          _ = 16126400 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 57136561) ^ 13949 = 39844245 := by
        calc
          (7 : ZMod 57136561) ^ 13949 = (7 : ZMod 57136561) ^ (6974 + 6974 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 6974 * (7 : ZMod 57136561) ^ 6974) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 39844245 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 57136561) ^ 27898 = 650356 := by
        calc
          (7 : ZMod 57136561) ^ 27898 = (7 : ZMod 57136561) ^ (13949 + 13949) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 13949 * (7 : ZMod 57136561) ^ 13949 := by rw [pow_add]
          _ = 650356 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 57136561) ^ 55797 = 38169254 := by
        calc
          (7 : ZMod 57136561) ^ 55797 = (7 : ZMod 57136561) ^ (27898 + 27898 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 27898 * (7 : ZMod 57136561) ^ 27898) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 38169254 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 57136561) ^ 111594 = 35456018 := by
        calc
          (7 : ZMod 57136561) ^ 111594 = (7 : ZMod 57136561) ^ (55797 + 55797) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 55797 * (7 : ZMod 57136561) ^ 55797 := by rw [pow_add]
          _ = 35456018 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 57136561) ^ 223189 = 17804090 := by
        calc
          (7 : ZMod 57136561) ^ 223189 = (7 : ZMod 57136561) ^ (111594 + 111594 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 111594 * (7 : ZMod 57136561) ^ 111594) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 17804090 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 57136561) ^ 446379 = 27340163 := by
        calc
          (7 : ZMod 57136561) ^ 446379 = (7 : ZMod 57136561) ^ (223189 + 223189 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 223189 * (7 : ZMod 57136561) ^ 223189) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 27340163 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 57136561) ^ 892758 = 24508949 := by
        calc
          (7 : ZMod 57136561) ^ 892758 = (7 : ZMod 57136561) ^ (446379 + 446379) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 446379 * (7 : ZMod 57136561) ^ 446379 := by rw [pow_add]
          _ = 24508949 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 57136561) ^ 1785517 = 44798708 := by
        calc
          (7 : ZMod 57136561) ^ 1785517 = (7 : ZMod 57136561) ^ (892758 + 892758 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 892758 * (7 : ZMod 57136561) ^ 892758) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 44798708 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 57136561) ^ 3571035 = 21075938 := by
        calc
          (7 : ZMod 57136561) ^ 3571035 = (7 : ZMod 57136561) ^ (1785517 + 1785517 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 1785517 * (7 : ZMod 57136561) ^ 1785517) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 21075938 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 57136561) ^ 7142070 = 53357813 := by
        calc
          (7 : ZMod 57136561) ^ 7142070 = (7 : ZMod 57136561) ^ (3571035 + 3571035) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 3571035 * (7 : ZMod 57136561) ^ 3571035 := by rw [pow_add]
          _ = 53357813 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 57136561) ^ 14284140 = 52761116 := by
        calc
          (7 : ZMod 57136561) ^ 14284140 = (7 : ZMod 57136561) ^ (7142070 + 7142070) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 7142070 * (7 : ZMod 57136561) ^ 7142070 := by rw [pow_add]
          _ = 52761116 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 57136561) ^ 28568280 = 57136560 := by
        calc
          (7 : ZMod 57136561) ^ 28568280 = (7 : ZMod 57136561) ^ (14284140 + 14284140) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 14284140 * (7 : ZMod 57136561) ^ 14284140 := by rw [pow_add]
          _ = 57136560 := by rw [factor_0_23]; decide
      change (7 : ZMod 57136561) ^ 28568280 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (7 : ZMod 57136561) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 57136561) ^ 2 = 49 := by
        calc
          (7 : ZMod 57136561) ^ 2 = (7 : ZMod 57136561) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 1 * (7 : ZMod 57136561) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 57136561) ^ 4 = 2401 := by
        calc
          (7 : ZMod 57136561) ^ 4 = (7 : ZMod 57136561) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 2 * (7 : ZMod 57136561) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 57136561) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 57136561) ^ 9 = (7 : ZMod 57136561) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 4 * (7 : ZMod 57136561) ^ 4) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 57136561) ^ 18 = 11790391 := by
        calc
          (7 : ZMod 57136561) ^ 18 = (7 : ZMod 57136561) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 9 * (7 : ZMod 57136561) ^ 9 := by rw [pow_add]
          _ = 11790391 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 57136561) ^ 36 = 9883320 := by
        calc
          (7 : ZMod 57136561) ^ 36 = (7 : ZMod 57136561) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 18 * (7 : ZMod 57136561) ^ 18 := by rw [pow_add]
          _ = 9883320 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 57136561) ^ 72 = 35175532 := by
        calc
          (7 : ZMod 57136561) ^ 72 = (7 : ZMod 57136561) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 36 * (7 : ZMod 57136561) ^ 36 := by rw [pow_add]
          _ = 35175532 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 57136561) ^ 145 = 38253725 := by
        calc
          (7 : ZMod 57136561) ^ 145 = (7 : ZMod 57136561) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 72 * (7 : ZMod 57136561) ^ 72) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 38253725 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 57136561) ^ 290 = 43707103 := by
        calc
          (7 : ZMod 57136561) ^ 290 = (7 : ZMod 57136561) ^ (145 + 145) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 145 * (7 : ZMod 57136561) ^ 145 := by rw [pow_add]
          _ = 43707103 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 57136561) ^ 581 = 24988437 := by
        calc
          (7 : ZMod 57136561) ^ 581 = (7 : ZMod 57136561) ^ (290 + 290 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 290 * (7 : ZMod 57136561) ^ 290) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 24988437 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 57136561) ^ 1162 = 48797101 := by
        calc
          (7 : ZMod 57136561) ^ 1162 = (7 : ZMod 57136561) ^ (581 + 581) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 581 * (7 : ZMod 57136561) ^ 581 := by rw [pow_add]
          _ = 48797101 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 57136561) ^ 2324 = 28178961 := by
        calc
          (7 : ZMod 57136561) ^ 2324 = (7 : ZMod 57136561) ^ (1162 + 1162) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 1162 * (7 : ZMod 57136561) ^ 1162 := by rw [pow_add]
          _ = 28178961 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 57136561) ^ 4649 = 33194493 := by
        calc
          (7 : ZMod 57136561) ^ 4649 = (7 : ZMod 57136561) ^ (2324 + 2324 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 2324 * (7 : ZMod 57136561) ^ 2324) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 33194493 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 57136561) ^ 9299 = 46096380 := by
        calc
          (7 : ZMod 57136561) ^ 9299 = (7 : ZMod 57136561) ^ (4649 + 4649 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 4649 * (7 : ZMod 57136561) ^ 4649) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 46096380 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 57136561) ^ 18599 = 50703897 := by
        calc
          (7 : ZMod 57136561) ^ 18599 = (7 : ZMod 57136561) ^ (9299 + 9299 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 9299 * (7 : ZMod 57136561) ^ 9299) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 50703897 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 57136561) ^ 37198 = 11612281 := by
        calc
          (7 : ZMod 57136561) ^ 37198 = (7 : ZMod 57136561) ^ (18599 + 18599) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 18599 * (7 : ZMod 57136561) ^ 18599 := by rw [pow_add]
          _ = 11612281 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 57136561) ^ 74396 = 43508033 := by
        calc
          (7 : ZMod 57136561) ^ 74396 = (7 : ZMod 57136561) ^ (37198 + 37198) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 37198 * (7 : ZMod 57136561) ^ 37198 := by rw [pow_add]
          _ = 43508033 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 57136561) ^ 148793 = 12793506 := by
        calc
          (7 : ZMod 57136561) ^ 148793 = (7 : ZMod 57136561) ^ (74396 + 74396 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 74396 * (7 : ZMod 57136561) ^ 74396) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 12793506 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 57136561) ^ 297586 = 3175509 := by
        calc
          (7 : ZMod 57136561) ^ 297586 = (7 : ZMod 57136561) ^ (148793 + 148793) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 148793 * (7 : ZMod 57136561) ^ 148793 := by rw [pow_add]
          _ = 3175509 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 57136561) ^ 595172 = 54304435 := by
        calc
          (7 : ZMod 57136561) ^ 595172 = (7 : ZMod 57136561) ^ (297586 + 297586) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 297586 * (7 : ZMod 57136561) ^ 297586 := by rw [pow_add]
          _ = 54304435 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 57136561) ^ 1190345 = 7951579 := by
        calc
          (7 : ZMod 57136561) ^ 1190345 = (7 : ZMod 57136561) ^ (595172 + 595172 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 595172 * (7 : ZMod 57136561) ^ 595172) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 7951579 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 57136561) ^ 2380690 = 4507836 := by
        calc
          (7 : ZMod 57136561) ^ 2380690 = (7 : ZMod 57136561) ^ (1190345 + 1190345) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 1190345 * (7 : ZMod 57136561) ^ 1190345 := by rw [pow_add]
          _ = 4507836 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 57136561) ^ 4761380 = 24619807 := by
        calc
          (7 : ZMod 57136561) ^ 4761380 = (7 : ZMod 57136561) ^ (2380690 + 2380690) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 2380690 * (7 : ZMod 57136561) ^ 2380690 := by rw [pow_add]
          _ = 24619807 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 57136561) ^ 9522760 = 32388480 := by
        calc
          (7 : ZMod 57136561) ^ 9522760 = (7 : ZMod 57136561) ^ (4761380 + 4761380) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 4761380 * (7 : ZMod 57136561) ^ 4761380 := by rw [pow_add]
          _ = 32388480 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 57136561) ^ 19045520 = 32388479 := by
        calc
          (7 : ZMod 57136561) ^ 19045520 = (7 : ZMod 57136561) ^ (9522760 + 9522760) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 9522760 * (7 : ZMod 57136561) ^ 9522760 := by rw [pow_add]
          _ = 32388479 := by rw [factor_1_23]; decide
      change (7 : ZMod 57136561) ^ 19045520 ≠ 1
      rw [factor_1_24]
      decide
    ·
      have factor_2_0 : (7 : ZMod 57136561) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 57136561) ^ 2 = 49 := by
        calc
          (7 : ZMod 57136561) ^ 2 = (7 : ZMod 57136561) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 1 * (7 : ZMod 57136561) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 57136561) ^ 5 = 16807 := by
        calc
          (7 : ZMod 57136561) ^ 5 = (7 : ZMod 57136561) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 2 * (7 : ZMod 57136561) ^ 2) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 57136561) ^ 10 = 53929005 := by
        calc
          (7 : ZMod 57136561) ^ 10 = (7 : ZMod 57136561) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 5 * (7 : ZMod 57136561) ^ 5 := by rw [pow_add]
          _ = 53929005 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 57136561) ^ 21 = 44544843 := by
        calc
          (7 : ZMod 57136561) ^ 21 = (7 : ZMod 57136561) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 10 * (7 : ZMod 57136561) ^ 10) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 44544843 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 57136561) ^ 43 = 7342066 := by
        calc
          (7 : ZMod 57136561) ^ 43 = (7 : ZMod 57136561) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 21 * (7 : ZMod 57136561) ^ 21) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 7342066 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 57136561) ^ 87 = 27336048 := by
        calc
          (7 : ZMod 57136561) ^ 87 = (7 : ZMod 57136561) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 43 * (7 : ZMod 57136561) ^ 43) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 27336048 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 57136561) ^ 174 = 35677902 := by
        calc
          (7 : ZMod 57136561) ^ 174 = (7 : ZMod 57136561) ^ (87 + 87) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 87 * (7 : ZMod 57136561) ^ 87 := by rw [pow_add]
          _ = 35677902 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 57136561) ^ 348 = 44988618 := by
        calc
          (7 : ZMod 57136561) ^ 348 = (7 : ZMod 57136561) ^ (174 + 174) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 174 * (7 : ZMod 57136561) ^ 174 := by rw [pow_add]
          _ = 44988618 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 57136561) ^ 697 = 37249118 := by
        calc
          (7 : ZMod 57136561) ^ 697 = (7 : ZMod 57136561) ^ (348 + 348 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 348 * (7 : ZMod 57136561) ^ 348) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 37249118 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 57136561) ^ 1394 = 29343415 := by
        calc
          (7 : ZMod 57136561) ^ 1394 = (7 : ZMod 57136561) ^ (697 + 697) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 697 * (7 : ZMod 57136561) ^ 697 := by rw [pow_add]
          _ = 29343415 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 57136561) ^ 2789 = 26480562 := by
        calc
          (7 : ZMod 57136561) ^ 2789 = (7 : ZMod 57136561) ^ (1394 + 1394 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 1394 * (7 : ZMod 57136561) ^ 1394) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 26480562 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 57136561) ^ 5579 = 41778373 := by
        calc
          (7 : ZMod 57136561) ^ 5579 = (7 : ZMod 57136561) ^ (2789 + 2789 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 2789 * (7 : ZMod 57136561) ^ 2789) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 41778373 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 57136561) ^ 11159 = 29094707 := by
        calc
          (7 : ZMod 57136561) ^ 11159 = (7 : ZMod 57136561) ^ (5579 + 5579 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 5579 * (7 : ZMod 57136561) ^ 5579) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 29094707 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 57136561) ^ 22318 = 55391473 := by
        calc
          (7 : ZMod 57136561) ^ 22318 = (7 : ZMod 57136561) ^ (11159 + 11159) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 11159 * (7 : ZMod 57136561) ^ 11159 := by rw [pow_add]
          _ = 55391473 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 57136561) ^ 44637 = 16804474 := by
        calc
          (7 : ZMod 57136561) ^ 44637 = (7 : ZMod 57136561) ^ (22318 + 22318 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 22318 * (7 : ZMod 57136561) ^ 22318) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 16804474 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 57136561) ^ 89275 = 21663863 := by
        calc
          (7 : ZMod 57136561) ^ 89275 = (7 : ZMod 57136561) ^ (44637 + 44637 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 44637 * (7 : ZMod 57136561) ^ 44637) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 21663863 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 57136561) ^ 178551 = 52986666 := by
        calc
          (7 : ZMod 57136561) ^ 178551 = (7 : ZMod 57136561) ^ (89275 + 89275 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 89275 * (7 : ZMod 57136561) ^ 89275) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 52986666 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 57136561) ^ 357103 = 55117934 := by
        calc
          (7 : ZMod 57136561) ^ 357103 = (7 : ZMod 57136561) ^ (178551 + 178551 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 178551 * (7 : ZMod 57136561) ^ 178551) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 55117934 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 57136561) ^ 714207 = 42227239 := by
        calc
          (7 : ZMod 57136561) ^ 714207 = (7 : ZMod 57136561) ^ (357103 + 357103 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 357103 * (7 : ZMod 57136561) ^ 357103) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 42227239 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 57136561) ^ 1428414 = 34572258 := by
        calc
          (7 : ZMod 57136561) ^ 1428414 = (7 : ZMod 57136561) ^ (714207 + 714207) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 714207 * (7 : ZMod 57136561) ^ 714207 := by rw [pow_add]
          _ = 34572258 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 57136561) ^ 2856828 = 46655222 := by
        calc
          (7 : ZMod 57136561) ^ 2856828 = (7 : ZMod 57136561) ^ (1428414 + 1428414) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 1428414 * (7 : ZMod 57136561) ^ 1428414 := by rw [pow_add]
          _ = 46655222 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 57136561) ^ 5713656 = 1618586 := by
        calc
          (7 : ZMod 57136561) ^ 5713656 = (7 : ZMod 57136561) ^ (2856828 + 2856828) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 2856828 * (7 : ZMod 57136561) ^ 2856828 := by rw [pow_add]
          _ = 1618586 := by rw [factor_2_21]; decide
      have factor_2_23 : (7 : ZMod 57136561) ^ 11427312 = 52180985 := by
        calc
          (7 : ZMod 57136561) ^ 11427312 = (7 : ZMod 57136561) ^ (5713656 + 5713656) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 5713656 * (7 : ZMod 57136561) ^ 5713656 := by rw [pow_add]
          _ = 52180985 := by rw [factor_2_22]; decide
      change (7 : ZMod 57136561) ^ 11427312 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (7 : ZMod 57136561) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 57136561) ^ 2 = 49 := by
        calc
          (7 : ZMod 57136561) ^ 2 = (7 : ZMod 57136561) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 1 * (7 : ZMod 57136561) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 57136561) ^ 4 = 2401 := by
        calc
          (7 : ZMod 57136561) ^ 4 = (7 : ZMod 57136561) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 2 * (7 : ZMod 57136561) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 57136561) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 57136561) ^ 8 = (7 : ZMod 57136561) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 4 * (7 : ZMod 57136561) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 57136561) ^ 16 = 21229561 := by
        calc
          (7 : ZMod 57136561) ^ 16 = (7 : ZMod 57136561) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 8 * (7 : ZMod 57136561) ^ 8 := by rw [pow_add]
          _ = 21229561 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 57136561) ^ 33 = 41840117 := by
        calc
          (7 : ZMod 57136561) ^ 33 = (7 : ZMod 57136561) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 16 * (7 : ZMod 57136561) ^ 16) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 41840117 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 57136561) ^ 67 = 20491297 := by
        calc
          (7 : ZMod 57136561) ^ 67 = (7 : ZMod 57136561) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 33 * (7 : ZMod 57136561) ^ 33) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 20491297 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 57136561) ^ 134 = 37010308 := by
        calc
          (7 : ZMod 57136561) ^ 134 = (7 : ZMod 57136561) ^ (67 + 67) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 67 * (7 : ZMod 57136561) ^ 67 := by rw [pow_add]
          _ = 37010308 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 57136561) ^ 268 = 10213852 := by
        calc
          (7 : ZMod 57136561) ^ 268 = (7 : ZMod 57136561) ^ (134 + 134) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 134 * (7 : ZMod 57136561) ^ 134 := by rw [pow_add]
          _ = 10213852 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 57136561) ^ 536 = 39912615 := by
        calc
          (7 : ZMod 57136561) ^ 536 = (7 : ZMod 57136561) ^ (268 + 268) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 268 * (7 : ZMod 57136561) ^ 268 := by rw [pow_add]
          _ = 39912615 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 57136561) ^ 1073 = 17828549 := by
        calc
          (7 : ZMod 57136561) ^ 1073 = (7 : ZMod 57136561) ^ (536 + 536 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 536 * (7 : ZMod 57136561) ^ 536) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 17828549 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 57136561) ^ 2146 = 14171008 := by
        calc
          (7 : ZMod 57136561) ^ 2146 = (7 : ZMod 57136561) ^ (1073 + 1073) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 1073 * (7 : ZMod 57136561) ^ 1073 := by rw [pow_add]
          _ = 14171008 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 57136561) ^ 4292 = 53881852 := by
        calc
          (7 : ZMod 57136561) ^ 4292 = (7 : ZMod 57136561) ^ (2146 + 2146) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 2146 * (7 : ZMod 57136561) ^ 2146 := by rw [pow_add]
          _ = 53881852 := by rw [factor_3_11]; decide
      have factor_3_13 : (7 : ZMod 57136561) ^ 8584 = 12265281 := by
        calc
          (7 : ZMod 57136561) ^ 8584 = (7 : ZMod 57136561) ^ (4292 + 4292) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 4292 * (7 : ZMod 57136561) ^ 4292 := by rw [pow_add]
          _ = 12265281 := by rw [factor_3_12]; decide
      have factor_3_14 : (7 : ZMod 57136561) ^ 17168 = 38226182 := by
        calc
          (7 : ZMod 57136561) ^ 17168 = (7 : ZMod 57136561) ^ (8584 + 8584) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 8584 * (7 : ZMod 57136561) ^ 8584 := by rw [pow_add]
          _ = 38226182 := by rw [factor_3_13]; decide
      have factor_3_15 : (7 : ZMod 57136561) ^ 34336 = 11222989 := by
        calc
          (7 : ZMod 57136561) ^ 34336 = (7 : ZMod 57136561) ^ (17168 + 17168) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 17168 * (7 : ZMod 57136561) ^ 17168 := by rw [pow_add]
          _ = 11222989 := by rw [factor_3_14]; decide
      have factor_3_16 : (7 : ZMod 57136561) ^ 68673 = 46273841 := by
        calc
          (7 : ZMod 57136561) ^ 68673 = (7 : ZMod 57136561) ^ (34336 + 34336 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 34336 * (7 : ZMod 57136561) ^ 34336) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 46273841 := by rw [factor_3_15]; decide
      have factor_3_17 : (7 : ZMod 57136561) ^ 137347 = 48915009 := by
        calc
          (7 : ZMod 57136561) ^ 137347 = (7 : ZMod 57136561) ^ (68673 + 68673 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 68673 * (7 : ZMod 57136561) ^ 68673) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 48915009 := by rw [factor_3_16]; decide
      have factor_3_18 : (7 : ZMod 57136561) ^ 274695 = 17574241 := by
        calc
          (7 : ZMod 57136561) ^ 274695 = (7 : ZMod 57136561) ^ (137347 + 137347 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 137347 * (7 : ZMod 57136561) ^ 137347) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 17574241 := by rw [factor_3_17]; decide
      have factor_3_19 : (7 : ZMod 57136561) ^ 549390 = 37914702 := by
        calc
          (7 : ZMod 57136561) ^ 549390 = (7 : ZMod 57136561) ^ (274695 + 274695) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 274695 * (7 : ZMod 57136561) ^ 274695 := by rw [pow_add]
          _ = 37914702 := by rw [factor_3_18]; decide
      have factor_3_20 : (7 : ZMod 57136561) ^ 1098780 = 6687671 := by
        calc
          (7 : ZMod 57136561) ^ 1098780 = (7 : ZMod 57136561) ^ (549390 + 549390) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 549390 * (7 : ZMod 57136561) ^ 549390 := by rw [pow_add]
          _ = 6687671 := by rw [factor_3_19]; decide
      have factor_3_21 : (7 : ZMod 57136561) ^ 2197560 = 43277149 := by
        calc
          (7 : ZMod 57136561) ^ 2197560 = (7 : ZMod 57136561) ^ (1098780 + 1098780) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 1098780 * (7 : ZMod 57136561) ^ 1098780 := by rw [pow_add]
          _ = 43277149 := by rw [factor_3_20]; decide
      have factor_3_22 : (7 : ZMod 57136561) ^ 4395120 = 10392236 := by
        calc
          (7 : ZMod 57136561) ^ 4395120 = (7 : ZMod 57136561) ^ (2197560 + 2197560) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 2197560 * (7 : ZMod 57136561) ^ 2197560 := by rw [pow_add]
          _ = 10392236 := by rw [factor_3_21]; decide
      change (7 : ZMod 57136561) ^ 4395120 ≠ 1
      rw [factor_3_22]
      decide
    ·
      have factor_4_0 : (7 : ZMod 57136561) ^ 1 = 7 := by norm_num
      have factor_4_1 : (7 : ZMod 57136561) ^ 3 = 343 := by
        calc
          (7 : ZMod 57136561) ^ 3 = (7 : ZMod 57136561) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 1 * (7 : ZMod 57136561) ^ 1) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_4_0]; decide
      have factor_4_2 : (7 : ZMod 57136561) ^ 6 = 117649 := by
        calc
          (7 : ZMod 57136561) ^ 6 = (7 : ZMod 57136561) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 3 * (7 : ZMod 57136561) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_4_1]; decide
      have factor_4_3 : (7 : ZMod 57136561) ^ 12 = 14239439 := by
        calc
          (7 : ZMod 57136561) ^ 12 = (7 : ZMod 57136561) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 6 * (7 : ZMod 57136561) ^ 6 := by rw [pow_add]
          _ = 14239439 := by rw [factor_4_2]; decide
      have factor_4_4 : (7 : ZMod 57136561) ^ 24 = 23419362 := by
        calc
          (7 : ZMod 57136561) ^ 24 = (7 : ZMod 57136561) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 12 * (7 : ZMod 57136561) ^ 12 := by rw [pow_add]
          _ = 23419362 := by rw [factor_4_3]; decide
      have factor_4_5 : (7 : ZMod 57136561) ^ 48 = 40268063 := by
        calc
          (7 : ZMod 57136561) ^ 48 = (7 : ZMod 57136561) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 24 * (7 : ZMod 57136561) ^ 24 := by rw [pow_add]
          _ = 40268063 := by rw [factor_4_4]; decide
      have factor_4_6 : (7 : ZMod 57136561) ^ 97 = 33141595 := by
        calc
          (7 : ZMod 57136561) ^ 97 = (7 : ZMod 57136561) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 48 * (7 : ZMod 57136561) ^ 48) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 33141595 := by rw [factor_4_5]; decide
      have factor_4_7 : (7 : ZMod 57136561) ^ 195 = 14671917 := by
        calc
          (7 : ZMod 57136561) ^ 195 = (7 : ZMod 57136561) ^ (97 + 97 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = ((7 : ZMod 57136561) ^ 97 * (7 : ZMod 57136561) ^ 97) * (7 : ZMod 57136561) := by rw [pow_succ, pow_add]
          _ = 14671917 := by rw [factor_4_6]; decide
      have factor_4_8 : (7 : ZMod 57136561) ^ 390 = 12376534 := by
        calc
          (7 : ZMod 57136561) ^ 390 = (7 : ZMod 57136561) ^ (195 + 195) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 195 * (7 : ZMod 57136561) ^ 195 := by rw [pow_add]
          _ = 12376534 := by rw [factor_4_7]; decide
      have factor_4_9 : (7 : ZMod 57136561) ^ 780 = 44737036 := by
        calc
          (7 : ZMod 57136561) ^ 780 = (7 : ZMod 57136561) ^ (390 + 390) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 390 * (7 : ZMod 57136561) ^ 390 := by rw [pow_add]
          _ = 44737036 := by rw [factor_4_8]; decide
      have factor_4_10 : (7 : ZMod 57136561) ^ 1560 = 19596335 := by
        calc
          (7 : ZMod 57136561) ^ 1560 = (7 : ZMod 57136561) ^ (780 + 780) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 780 * (7 : ZMod 57136561) ^ 780 := by rw [pow_add]
          _ = 19596335 := by rw [factor_4_9]; decide
      have factor_4_11 : (7 : ZMod 57136561) ^ 3120 = 33400639 := by
        calc
          (7 : ZMod 57136561) ^ 3120 = (7 : ZMod 57136561) ^ (1560 + 1560) :=
            congrArg (fun n : ℕ => (7 : ZMod 57136561) ^ n) (by norm_num)
          _ = (7 : ZMod 57136561) ^ 1560 * (7 : ZMod 57136561) ^ 1560 := by rw [pow_add]
          _ = 33400639 := by rw [factor_4_10]; decide
      change (7 : ZMod 57136561) ^ 3120 ≠ 1
      rw [factor_4_11]
      decide

#print axioms prime_lucas_57136561

end TotientTailPeriodKiller
end Erdos249257
