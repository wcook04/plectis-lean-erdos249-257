import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_61384157 : Nat.Prime 61384157 := by
  apply lucas_primality 61384157 (2 : ZMod 61384157)
  ·
      have fermat_0 : (2 : ZMod 61384157) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 61384157) ^ 3 = 8 := by
        calc
          (2 : ZMod 61384157) ^ 3 = (2 : ZMod 61384157) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 1 * (2 : ZMod 61384157) ^ 1) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 61384157) ^ 7 = 128 := by
        calc
          (2 : ZMod 61384157) ^ 7 = (2 : ZMod 61384157) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 3 * (2 : ZMod 61384157) ^ 3) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 61384157) ^ 14 = 16384 := by
        calc
          (2 : ZMod 61384157) ^ 14 = (2 : ZMod 61384157) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 7 * (2 : ZMod 61384157) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 61384157) ^ 29 = 45797656 := by
        calc
          (2 : ZMod 61384157) ^ 29 = (2 : ZMod 61384157) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 14 * (2 : ZMod 61384157) ^ 14) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 45797656 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 61384157) ^ 58 = 40178927 := by
        calc
          (2 : ZMod 61384157) ^ 58 = (2 : ZMod 61384157) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 29 * (2 : ZMod 61384157) ^ 29 := by rw [pow_add]
          _ = 40178927 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 61384157) ^ 117 = 50227149 := by
        calc
          (2 : ZMod 61384157) ^ 117 = (2 : ZMod 61384157) ^ (58 + 58 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 58 * (2 : ZMod 61384157) ^ 58) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 50227149 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 61384157) ^ 234 = 43977259 := by
        calc
          (2 : ZMod 61384157) ^ 234 = (2 : ZMod 61384157) ^ (117 + 117) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 117 * (2 : ZMod 61384157) ^ 117 := by rw [pow_add]
          _ = 43977259 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 61384157) ^ 468 = 41858308 := by
        calc
          (2 : ZMod 61384157) ^ 468 = (2 : ZMod 61384157) ^ (234 + 234) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 234 * (2 : ZMod 61384157) ^ 234 := by rw [pow_add]
          _ = 41858308 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 61384157) ^ 936 = 61287405 := by
        calc
          (2 : ZMod 61384157) ^ 936 = (2 : ZMod 61384157) ^ (468 + 468) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 468 * (2 : ZMod 61384157) ^ 468 := by rw [pow_add]
          _ = 61287405 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 61384157) ^ 1873 = 61115280 := by
        calc
          (2 : ZMod 61384157) ^ 1873 = (2 : ZMod 61384157) ^ (936 + 936 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 936 * (2 : ZMod 61384157) ^ 936) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 61115280 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 61384157) ^ 3746 = 45688340 := by
        calc
          (2 : ZMod 61384157) ^ 3746 = (2 : ZMod 61384157) ^ (1873 + 1873) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 1873 * (2 : ZMod 61384157) ^ 1873 := by rw [pow_add]
          _ = 45688340 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 61384157) ^ 7493 = 34718047 := by
        calc
          (2 : ZMod 61384157) ^ 7493 = (2 : ZMod 61384157) ^ (3746 + 3746 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 3746 * (2 : ZMod 61384157) ^ 3746) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 34718047 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 61384157) ^ 14986 = 43129417 := by
        calc
          (2 : ZMod 61384157) ^ 14986 = (2 : ZMod 61384157) ^ (7493 + 7493) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 7493 * (2 : ZMod 61384157) ^ 7493 := by rw [pow_add]
          _ = 43129417 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 61384157) ^ 29972 = 34587427 := by
        calc
          (2 : ZMod 61384157) ^ 29972 = (2 : ZMod 61384157) ^ (14986 + 14986) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 14986 * (2 : ZMod 61384157) ^ 14986 := by rw [pow_add]
          _ = 34587427 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 61384157) ^ 59945 = 42722381 := by
        calc
          (2 : ZMod 61384157) ^ 59945 = (2 : ZMod 61384157) ^ (29972 + 29972 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 29972 * (2 : ZMod 61384157) ^ 29972) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 42722381 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 61384157) ^ 119890 = 35033659 := by
        calc
          (2 : ZMod 61384157) ^ 119890 = (2 : ZMod 61384157) ^ (59945 + 59945) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 59945 * (2 : ZMod 61384157) ^ 59945 := by rw [pow_add]
          _ = 35033659 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 61384157) ^ 239781 = 22835588 := by
        calc
          (2 : ZMod 61384157) ^ 239781 = (2 : ZMod 61384157) ^ (119890 + 119890 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 119890 * (2 : ZMod 61384157) ^ 119890) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 22835588 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 61384157) ^ 479563 = 36496600 := by
        calc
          (2 : ZMod 61384157) ^ 479563 = (2 : ZMod 61384157) ^ (239781 + 239781 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 239781 * (2 : ZMod 61384157) ^ 239781) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 36496600 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 61384157) ^ 959127 = 20959997 := by
        calc
          (2 : ZMod 61384157) ^ 959127 = (2 : ZMod 61384157) ^ (479563 + 479563 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 479563 * (2 : ZMod 61384157) ^ 479563) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 20959997 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 61384157) ^ 1918254 = 34707726 := by
        calc
          (2 : ZMod 61384157) ^ 1918254 = (2 : ZMod 61384157) ^ (959127 + 959127) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 959127 * (2 : ZMod 61384157) ^ 959127 := by rw [pow_add]
          _ = 34707726 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 61384157) ^ 3836509 = 12597733 := by
        calc
          (2 : ZMod 61384157) ^ 3836509 = (2 : ZMod 61384157) ^ (1918254 + 1918254 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 1918254 * (2 : ZMod 61384157) ^ 1918254) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 12597733 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 61384157) ^ 7673019 = 2005565 := by
        calc
          (2 : ZMod 61384157) ^ 7673019 = (2 : ZMod 61384157) ^ (3836509 + 3836509 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 3836509 * (2 : ZMod 61384157) ^ 3836509) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 2005565 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 61384157) ^ 15346039 = 4011129 := by
        calc
          (2 : ZMod 61384157) ^ 15346039 = (2 : ZMod 61384157) ^ (7673019 + 7673019 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 7673019 * (2 : ZMod 61384157) ^ 7673019) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 4011129 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 61384157) ^ 30692078 = 61384156 := by
        calc
          (2 : ZMod 61384157) ^ 30692078 = (2 : ZMod 61384157) ^ (15346039 + 15346039) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 15346039 * (2 : ZMod 61384157) ^ 15346039 := by rw [pow_add]
          _ = 61384156 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 61384157) ^ 61384156 = 1 := by
        calc
          (2 : ZMod 61384157) ^ 61384156 = (2 : ZMod 61384157) ^ (30692078 + 30692078) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 30692078 * (2 : ZMod 61384157) ^ 30692078 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1103, 1), (13913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1103, 1), (13913, 1)] : List FactorBlock).map factorBlockValue).prod = 61384157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 61384157) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 61384157) ^ 3 = 8 := by
        calc
          (2 : ZMod 61384157) ^ 3 = (2 : ZMod 61384157) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 1 * (2 : ZMod 61384157) ^ 1) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 61384157) ^ 7 = 128 := by
        calc
          (2 : ZMod 61384157) ^ 7 = (2 : ZMod 61384157) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 3 * (2 : ZMod 61384157) ^ 3) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 61384157) ^ 14 = 16384 := by
        calc
          (2 : ZMod 61384157) ^ 14 = (2 : ZMod 61384157) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 7 * (2 : ZMod 61384157) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 61384157) ^ 29 = 45797656 := by
        calc
          (2 : ZMod 61384157) ^ 29 = (2 : ZMod 61384157) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 14 * (2 : ZMod 61384157) ^ 14) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 45797656 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 61384157) ^ 58 = 40178927 := by
        calc
          (2 : ZMod 61384157) ^ 58 = (2 : ZMod 61384157) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 29 * (2 : ZMod 61384157) ^ 29 := by rw [pow_add]
          _ = 40178927 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 61384157) ^ 117 = 50227149 := by
        calc
          (2 : ZMod 61384157) ^ 117 = (2 : ZMod 61384157) ^ (58 + 58 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 58 * (2 : ZMod 61384157) ^ 58) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 50227149 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 61384157) ^ 234 = 43977259 := by
        calc
          (2 : ZMod 61384157) ^ 234 = (2 : ZMod 61384157) ^ (117 + 117) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 117 * (2 : ZMod 61384157) ^ 117 := by rw [pow_add]
          _ = 43977259 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 61384157) ^ 468 = 41858308 := by
        calc
          (2 : ZMod 61384157) ^ 468 = (2 : ZMod 61384157) ^ (234 + 234) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 234 * (2 : ZMod 61384157) ^ 234 := by rw [pow_add]
          _ = 41858308 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 61384157) ^ 936 = 61287405 := by
        calc
          (2 : ZMod 61384157) ^ 936 = (2 : ZMod 61384157) ^ (468 + 468) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 468 * (2 : ZMod 61384157) ^ 468 := by rw [pow_add]
          _ = 61287405 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 61384157) ^ 1873 = 61115280 := by
        calc
          (2 : ZMod 61384157) ^ 1873 = (2 : ZMod 61384157) ^ (936 + 936 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 936 * (2 : ZMod 61384157) ^ 936) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 61115280 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 61384157) ^ 3746 = 45688340 := by
        calc
          (2 : ZMod 61384157) ^ 3746 = (2 : ZMod 61384157) ^ (1873 + 1873) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 1873 * (2 : ZMod 61384157) ^ 1873 := by rw [pow_add]
          _ = 45688340 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 61384157) ^ 7493 = 34718047 := by
        calc
          (2 : ZMod 61384157) ^ 7493 = (2 : ZMod 61384157) ^ (3746 + 3746 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 3746 * (2 : ZMod 61384157) ^ 3746) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 34718047 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 61384157) ^ 14986 = 43129417 := by
        calc
          (2 : ZMod 61384157) ^ 14986 = (2 : ZMod 61384157) ^ (7493 + 7493) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 7493 * (2 : ZMod 61384157) ^ 7493 := by rw [pow_add]
          _ = 43129417 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 61384157) ^ 29972 = 34587427 := by
        calc
          (2 : ZMod 61384157) ^ 29972 = (2 : ZMod 61384157) ^ (14986 + 14986) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 14986 * (2 : ZMod 61384157) ^ 14986 := by rw [pow_add]
          _ = 34587427 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 61384157) ^ 59945 = 42722381 := by
        calc
          (2 : ZMod 61384157) ^ 59945 = (2 : ZMod 61384157) ^ (29972 + 29972 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 29972 * (2 : ZMod 61384157) ^ 29972) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 42722381 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 61384157) ^ 119890 = 35033659 := by
        calc
          (2 : ZMod 61384157) ^ 119890 = (2 : ZMod 61384157) ^ (59945 + 59945) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 59945 * (2 : ZMod 61384157) ^ 59945 := by rw [pow_add]
          _ = 35033659 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 61384157) ^ 239781 = 22835588 := by
        calc
          (2 : ZMod 61384157) ^ 239781 = (2 : ZMod 61384157) ^ (119890 + 119890 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 119890 * (2 : ZMod 61384157) ^ 119890) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 22835588 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 61384157) ^ 479563 = 36496600 := by
        calc
          (2 : ZMod 61384157) ^ 479563 = (2 : ZMod 61384157) ^ (239781 + 239781 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 239781 * (2 : ZMod 61384157) ^ 239781) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 36496600 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 61384157) ^ 959127 = 20959997 := by
        calc
          (2 : ZMod 61384157) ^ 959127 = (2 : ZMod 61384157) ^ (479563 + 479563 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 479563 * (2 : ZMod 61384157) ^ 479563) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 20959997 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 61384157) ^ 1918254 = 34707726 := by
        calc
          (2 : ZMod 61384157) ^ 1918254 = (2 : ZMod 61384157) ^ (959127 + 959127) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 959127 * (2 : ZMod 61384157) ^ 959127 := by rw [pow_add]
          _ = 34707726 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 61384157) ^ 3836509 = 12597733 := by
        calc
          (2 : ZMod 61384157) ^ 3836509 = (2 : ZMod 61384157) ^ (1918254 + 1918254 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 1918254 * (2 : ZMod 61384157) ^ 1918254) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 12597733 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 61384157) ^ 7673019 = 2005565 := by
        calc
          (2 : ZMod 61384157) ^ 7673019 = (2 : ZMod 61384157) ^ (3836509 + 3836509 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 3836509 * (2 : ZMod 61384157) ^ 3836509) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 2005565 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 61384157) ^ 15346039 = 4011129 := by
        calc
          (2 : ZMod 61384157) ^ 15346039 = (2 : ZMod 61384157) ^ (7673019 + 7673019 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 7673019 * (2 : ZMod 61384157) ^ 7673019) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 4011129 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 61384157) ^ 30692078 = 61384156 := by
        calc
          (2 : ZMod 61384157) ^ 30692078 = (2 : ZMod 61384157) ^ (15346039 + 15346039) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 15346039 * (2 : ZMod 61384157) ^ 15346039 := by rw [pow_add]
          _ = 61384156 := by rw [factor_0_23]; decide
      change (2 : ZMod 61384157) ^ 30692078 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (2 : ZMod 61384157) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 61384157) ^ 3 = 8 := by
        calc
          (2 : ZMod 61384157) ^ 3 = (2 : ZMod 61384157) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 1 * (2 : ZMod 61384157) ^ 1) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 61384157) ^ 6 = 64 := by
        calc
          (2 : ZMod 61384157) ^ 6 = (2 : ZMod 61384157) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 3 * (2 : ZMod 61384157) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 61384157) ^ 13 = 8192 := by
        calc
          (2 : ZMod 61384157) ^ 13 = (2 : ZMod 61384157) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 6 * (2 : ZMod 61384157) ^ 6) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 61384157) ^ 27 = 11449414 := by
        calc
          (2 : ZMod 61384157) ^ 27 = (2 : ZMod 61384157) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 13 * (2 : ZMod 61384157) ^ 13) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 11449414 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 61384157) ^ 54 = 21693732 := by
        calc
          (2 : ZMod 61384157) ^ 54 = (2 : ZMod 61384157) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 27 * (2 : ZMod 61384157) ^ 27 := by rw [pow_add]
          _ = 21693732 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 61384157) ^ 108 = 40261562 := by
        calc
          (2 : ZMod 61384157) ^ 108 = (2 : ZMod 61384157) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 54 * (2 : ZMod 61384157) ^ 54 := by rw [pow_add]
          _ = 40261562 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 61384157) ^ 217 = 53273590 := by
        calc
          (2 : ZMod 61384157) ^ 217 = (2 : ZMod 61384157) ^ (108 + 108 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 108 * (2 : ZMod 61384157) ^ 108) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 53273590 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 61384157) ^ 434 = 8743108 := by
        calc
          (2 : ZMod 61384157) ^ 434 = (2 : ZMod 61384157) ^ (217 + 217) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 217 * (2 : ZMod 61384157) ^ 217 := by rw [pow_add]
          _ = 8743108 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 61384157) ^ 869 = 2501872 := by
        calc
          (2 : ZMod 61384157) ^ 869 = (2 : ZMod 61384157) ^ (434 + 434 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 434 * (2 : ZMod 61384157) ^ 434) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 2501872 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 61384157) ^ 1739 = 42030188 := by
        calc
          (2 : ZMod 61384157) ^ 1739 = (2 : ZMod 61384157) ^ (869 + 869 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 869 * (2 : ZMod 61384157) ^ 869) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 42030188 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 61384157) ^ 3478 = 45805527 := by
        calc
          (2 : ZMod 61384157) ^ 3478 = (2 : ZMod 61384157) ^ (1739 + 1739) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 1739 * (2 : ZMod 61384157) ^ 1739 := by rw [pow_add]
          _ = 45805527 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 61384157) ^ 6956 = 30524198 := by
        calc
          (2 : ZMod 61384157) ^ 6956 = (2 : ZMod 61384157) ^ (3478 + 3478) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 3478 * (2 : ZMod 61384157) ^ 3478 := by rw [pow_add]
          _ = 30524198 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 61384157) ^ 13913 = 47760513 := by
        calc
          (2 : ZMod 61384157) ^ 13913 = (2 : ZMod 61384157) ^ (6956 + 6956 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 6956 * (2 : ZMod 61384157) ^ 6956) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 47760513 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 61384157) ^ 27826 = 21983099 := by
        calc
          (2 : ZMod 61384157) ^ 27826 = (2 : ZMod 61384157) ^ (13913 + 13913) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 13913 * (2 : ZMod 61384157) ^ 13913 := by rw [pow_add]
          _ = 21983099 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 61384157) ^ 55652 = 44196181 := by
        calc
          (2 : ZMod 61384157) ^ 55652 = (2 : ZMod 61384157) ^ (27826 + 27826) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 27826 * (2 : ZMod 61384157) ^ 27826 := by rw [pow_add]
          _ = 44196181 := by rw [factor_1_14]; decide
      change (2 : ZMod 61384157) ^ 55652 ≠ 1
      rw [factor_1_15]
      decide
    ·
      have factor_2_0 : (2 : ZMod 61384157) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 61384157) ^ 2 = 4 := by
        calc
          (2 : ZMod 61384157) ^ 2 = (2 : ZMod 61384157) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 1 * (2 : ZMod 61384157) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 61384157) ^ 4 = 16 := by
        calc
          (2 : ZMod 61384157) ^ 4 = (2 : ZMod 61384157) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 2 * (2 : ZMod 61384157) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 61384157) ^ 8 = 256 := by
        calc
          (2 : ZMod 61384157) ^ 8 = (2 : ZMod 61384157) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 4 * (2 : ZMod 61384157) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 61384157) ^ 17 = 131072 := by
        calc
          (2 : ZMod 61384157) ^ 17 = (2 : ZMod 61384157) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 8 * (2 : ZMod 61384157) ^ 8) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 61384157) ^ 34 = 53689381 := by
        calc
          (2 : ZMod 61384157) ^ 34 = (2 : ZMod 61384157) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 17 * (2 : ZMod 61384157) ^ 17 := by rw [pow_add]
          _ = 53689381 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 61384157) ^ 68 = 15836058 := by
        calc
          (2 : ZMod 61384157) ^ 68 = (2 : ZMod 61384157) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 34 * (2 : ZMod 61384157) ^ 34 := by rw [pow_add]
          _ = 15836058 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 61384157) ^ 137 = 51509551 := by
        calc
          (2 : ZMod 61384157) ^ 137 = (2 : ZMod 61384157) ^ (68 + 68 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 68 * (2 : ZMod 61384157) ^ 68) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 51509551 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 61384157) ^ 275 = 662025 := by
        calc
          (2 : ZMod 61384157) ^ 275 = (2 : ZMod 61384157) ^ (137 + 137 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 137 * (2 : ZMod 61384157) ^ 137) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 662025 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 61384157) ^ 551 = 49823447 := by
        calc
          (2 : ZMod 61384157) ^ 551 = (2 : ZMod 61384157) ^ (275 + 275 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 275 * (2 : ZMod 61384157) ^ 275) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 49823447 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 61384157) ^ 1103 = 18848792 := by
        calc
          (2 : ZMod 61384157) ^ 1103 = (2 : ZMod 61384157) ^ (551 + 551 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = ((2 : ZMod 61384157) ^ 551 * (2 : ZMod 61384157) ^ 551) * (2 : ZMod 61384157) := by rw [pow_succ, pow_add]
          _ = 18848792 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 61384157) ^ 2206 = 7188473 := by
        calc
          (2 : ZMod 61384157) ^ 2206 = (2 : ZMod 61384157) ^ (1103 + 1103) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 1103 * (2 : ZMod 61384157) ^ 1103 := by rw [pow_add]
          _ = 7188473 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 61384157) ^ 4412 = 39946774 := by
        calc
          (2 : ZMod 61384157) ^ 4412 = (2 : ZMod 61384157) ^ (2206 + 2206) :=
            congrArg (fun n : ℕ => (2 : ZMod 61384157) ^ n) (by norm_num)
          _ = (2 : ZMod 61384157) ^ 2206 * (2 : ZMod 61384157) ^ 2206 := by rw [pow_add]
          _ = 39946774 := by rw [factor_2_11]; decide
      change (2 : ZMod 61384157) ^ 4412 ≠ 1
      rw [factor_2_12]
      decide

#print axioms prime_lucas_61384157

end TotientTailPeriodKiller
end Erdos249257
