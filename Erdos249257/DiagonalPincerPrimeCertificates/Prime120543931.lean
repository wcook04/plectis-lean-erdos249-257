import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_120543931 : Nat.Prime 120543931 := by
  apply lucas_primality 120543931 (10 : ZMod 120543931)
  ·
      have fermat_0 : (10 : ZMod 120543931) ^ 1 = 10 := by norm_num
      have fermat_1 : (10 : ZMod 120543931) ^ 3 = 1000 := by
        calc
          (10 : ZMod 120543931) ^ 3 = (10 : ZMod 120543931) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 1 * (10 : ZMod 120543931) ^ 1) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [fermat_0]; decide
      have fermat_2 : (10 : ZMod 120543931) ^ 7 = 10000000 := by
        calc
          (10 : ZMod 120543931) ^ 7 = (10 : ZMod 120543931) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 3 * (10 : ZMod 120543931) ^ 3) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 10000000 := by rw [fermat_1]; decide
      have fermat_3 : (10 : ZMod 120543931) ^ 14 = 9528537 := by
        calc
          (10 : ZMod 120543931) ^ 14 = (10 : ZMod 120543931) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 7 * (10 : ZMod 120543931) ^ 7 := by rw [pow_add]
          _ = 9528537 := by rw [fermat_2]; decide
      have fermat_4 : (10 : ZMod 120543931) ^ 28 = 51794755 := by
        calc
          (10 : ZMod 120543931) ^ 28 = (10 : ZMod 120543931) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 14 * (10 : ZMod 120543931) ^ 14 := by rw [pow_add]
          _ = 51794755 := by rw [fermat_3]; decide
      have fermat_5 : (10 : ZMod 120543931) ^ 57 = 76697329 := by
        calc
          (10 : ZMod 120543931) ^ 57 = (10 : ZMod 120543931) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 28 * (10 : ZMod 120543931) ^ 28) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 76697329 := by rw [fermat_4]; decide
      have fermat_6 : (10 : ZMod 120543931) ^ 114 = 90129809 := by
        calc
          (10 : ZMod 120543931) ^ 114 = (10 : ZMod 120543931) ^ (57 + 57) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 57 * (10 : ZMod 120543931) ^ 57 := by rw [pow_add]
          _ = 90129809 := by rw [fermat_5]; decide
      have fermat_7 : (10 : ZMod 120543931) ^ 229 = 99086670 := by
        calc
          (10 : ZMod 120543931) ^ 229 = (10 : ZMod 120543931) ^ (114 + 114 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 114 * (10 : ZMod 120543931) ^ 114) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 99086670 := by rw [fermat_6]; decide
      have fermat_8 : (10 : ZMod 120543931) ^ 459 = 9416200 := by
        calc
          (10 : ZMod 120543931) ^ 459 = (10 : ZMod 120543931) ^ (229 + 229 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 229 * (10 : ZMod 120543931) ^ 229) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 9416200 := by rw [fermat_7]; decide
      have fermat_9 : (10 : ZMod 120543931) ^ 919 = 117586186 := by
        calc
          (10 : ZMod 120543931) ^ 919 = (10 : ZMod 120543931) ^ (459 + 459 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 459 * (10 : ZMod 120543931) ^ 459) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 117586186 := by rw [fermat_8]; decide
      have fermat_10 : (10 : ZMod 120543931) ^ 1839 = 87261689 := by
        calc
          (10 : ZMod 120543931) ^ 1839 = (10 : ZMod 120543931) ^ (919 + 919 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 919 * (10 : ZMod 120543931) ^ 919) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 87261689 := by rw [fermat_9]; decide
      have fermat_11 : (10 : ZMod 120543931) ^ 3678 = 37868400 := by
        calc
          (10 : ZMod 120543931) ^ 3678 = (10 : ZMod 120543931) ^ (1839 + 1839) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 1839 * (10 : ZMod 120543931) ^ 1839 := by rw [pow_add]
          _ = 37868400 := by rw [fermat_10]; decide
      have fermat_12 : (10 : ZMod 120543931) ^ 7357 = 60831727 := by
        calc
          (10 : ZMod 120543931) ^ 7357 = (10 : ZMod 120543931) ^ (3678 + 3678 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 3678 * (10 : ZMod 120543931) ^ 3678) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 60831727 := by rw [fermat_11]; decide
      have fermat_13 : (10 : ZMod 120543931) ^ 14714 = 69396196 := by
        calc
          (10 : ZMod 120543931) ^ 14714 = (10 : ZMod 120543931) ^ (7357 + 7357) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 7357 * (10 : ZMod 120543931) ^ 7357 := by rw [pow_add]
          _ = 69396196 := by rw [fermat_12]; decide
      have fermat_14 : (10 : ZMod 120543931) ^ 29429 = 77091831 := by
        calc
          (10 : ZMod 120543931) ^ 29429 = (10 : ZMod 120543931) ^ (14714 + 14714 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 14714 * (10 : ZMod 120543931) ^ 14714) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 77091831 := by rw [fermat_13]; decide
      have fermat_15 : (10 : ZMod 120543931) ^ 58859 = 27888912 := by
        calc
          (10 : ZMod 120543931) ^ 58859 = (10 : ZMod 120543931) ^ (29429 + 29429 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 29429 * (10 : ZMod 120543931) ^ 29429) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 27888912 := by rw [fermat_14]; decide
      have fermat_16 : (10 : ZMod 120543931) ^ 117718 = 20443756 := by
        calc
          (10 : ZMod 120543931) ^ 117718 = (10 : ZMod 120543931) ^ (58859 + 58859) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 58859 * (10 : ZMod 120543931) ^ 58859 := by rw [pow_add]
          _ = 20443756 := by rw [fermat_15]; decide
      have fermat_17 : (10 : ZMod 120543931) ^ 235437 = 22803559 := by
        calc
          (10 : ZMod 120543931) ^ 235437 = (10 : ZMod 120543931) ^ (117718 + 117718 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 117718 * (10 : ZMod 120543931) ^ 117718) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 22803559 := by rw [fermat_16]; decide
      have fermat_18 : (10 : ZMod 120543931) ^ 470874 = 14062612 := by
        calc
          (10 : ZMod 120543931) ^ 470874 = (10 : ZMod 120543931) ^ (235437 + 235437) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 235437 * (10 : ZMod 120543931) ^ 235437 := by rw [pow_add]
          _ = 14062612 := by rw [fermat_17]; decide
      have fermat_19 : (10 : ZMod 120543931) ^ 941749 = 805557 := by
        calc
          (10 : ZMod 120543931) ^ 941749 = (10 : ZMod 120543931) ^ (470874 + 470874 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 470874 * (10 : ZMod 120543931) ^ 470874) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 805557 := by rw [fermat_18]; decide
      have fermat_20 : (10 : ZMod 120543931) ^ 1883498 = 34099676 := by
        calc
          (10 : ZMod 120543931) ^ 1883498 = (10 : ZMod 120543931) ^ (941749 + 941749) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 941749 * (10 : ZMod 120543931) ^ 941749 := by rw [pow_add]
          _ = 34099676 := by rw [fermat_19]; decide
      have fermat_21 : (10 : ZMod 120543931) ^ 3766997 = 14734786 := by
        calc
          (10 : ZMod 120543931) ^ 3766997 = (10 : ZMod 120543931) ^ (1883498 + 1883498 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 1883498 * (10 : ZMod 120543931) ^ 1883498) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 14734786 := by rw [fermat_20]; decide
      have fermat_22 : (10 : ZMod 120543931) ^ 7533995 = 22245794 := by
        calc
          (10 : ZMod 120543931) ^ 7533995 = (10 : ZMod 120543931) ^ (3766997 + 3766997 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 3766997 * (10 : ZMod 120543931) ^ 3766997) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 22245794 := by rw [fermat_21]; decide
      have fermat_23 : (10 : ZMod 120543931) ^ 15067991 = 101453654 := by
        calc
          (10 : ZMod 120543931) ^ 15067991 = (10 : ZMod 120543931) ^ (7533995 + 7533995 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 7533995 * (10 : ZMod 120543931) ^ 7533995) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 101453654 := by rw [fermat_22]; decide
      have fermat_24 : (10 : ZMod 120543931) ^ 30135982 = 17503394 := by
        calc
          (10 : ZMod 120543931) ^ 30135982 = (10 : ZMod 120543931) ^ (15067991 + 15067991) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 15067991 * (10 : ZMod 120543931) ^ 15067991 := by rw [pow_add]
          _ = 17503394 := by rw [fermat_23]; decide
      have fermat_25 : (10 : ZMod 120543931) ^ 60271965 = 120543930 := by
        calc
          (10 : ZMod 120543931) ^ 60271965 = (10 : ZMod 120543931) ^ (30135982 + 30135982 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 30135982 * (10 : ZMod 120543931) ^ 30135982) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 120543930 := by rw [fermat_24]; decide
      have fermat_26 : (10 : ZMod 120543931) ^ 120543930 = 1 := by
        calc
          (10 : ZMod 120543931) ^ 120543930 = (10 : ZMod 120543931) ^ (60271965 + 60271965) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 60271965 * (10 : ZMod 120543931) ^ 60271965 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 1), (13, 1), (61, 1), (563, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 1), (13, 1), (61, 1), (563, 1)] : List FactorBlock).map factorBlockValue).prod = 120543931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (10 : ZMod 120543931) ^ 1 = 10 := by norm_num
      have factor_0_1 : (10 : ZMod 120543931) ^ 3 = 1000 := by
        calc
          (10 : ZMod 120543931) ^ 3 = (10 : ZMod 120543931) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 1 * (10 : ZMod 120543931) ^ 1) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_0_0]; decide
      have factor_0_2 : (10 : ZMod 120543931) ^ 7 = 10000000 := by
        calc
          (10 : ZMod 120543931) ^ 7 = (10 : ZMod 120543931) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 3 * (10 : ZMod 120543931) ^ 3) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 10000000 := by rw [factor_0_1]; decide
      have factor_0_3 : (10 : ZMod 120543931) ^ 14 = 9528537 := by
        calc
          (10 : ZMod 120543931) ^ 14 = (10 : ZMod 120543931) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 7 * (10 : ZMod 120543931) ^ 7 := by rw [pow_add]
          _ = 9528537 := by rw [factor_0_2]; decide
      have factor_0_4 : (10 : ZMod 120543931) ^ 28 = 51794755 := by
        calc
          (10 : ZMod 120543931) ^ 28 = (10 : ZMod 120543931) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 14 * (10 : ZMod 120543931) ^ 14 := by rw [pow_add]
          _ = 51794755 := by rw [factor_0_3]; decide
      have factor_0_5 : (10 : ZMod 120543931) ^ 57 = 76697329 := by
        calc
          (10 : ZMod 120543931) ^ 57 = (10 : ZMod 120543931) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 28 * (10 : ZMod 120543931) ^ 28) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 76697329 := by rw [factor_0_4]; decide
      have factor_0_6 : (10 : ZMod 120543931) ^ 114 = 90129809 := by
        calc
          (10 : ZMod 120543931) ^ 114 = (10 : ZMod 120543931) ^ (57 + 57) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 57 * (10 : ZMod 120543931) ^ 57 := by rw [pow_add]
          _ = 90129809 := by rw [factor_0_5]; decide
      have factor_0_7 : (10 : ZMod 120543931) ^ 229 = 99086670 := by
        calc
          (10 : ZMod 120543931) ^ 229 = (10 : ZMod 120543931) ^ (114 + 114 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 114 * (10 : ZMod 120543931) ^ 114) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 99086670 := by rw [factor_0_6]; decide
      have factor_0_8 : (10 : ZMod 120543931) ^ 459 = 9416200 := by
        calc
          (10 : ZMod 120543931) ^ 459 = (10 : ZMod 120543931) ^ (229 + 229 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 229 * (10 : ZMod 120543931) ^ 229) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 9416200 := by rw [factor_0_7]; decide
      have factor_0_9 : (10 : ZMod 120543931) ^ 919 = 117586186 := by
        calc
          (10 : ZMod 120543931) ^ 919 = (10 : ZMod 120543931) ^ (459 + 459 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 459 * (10 : ZMod 120543931) ^ 459) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 117586186 := by rw [factor_0_8]; decide
      have factor_0_10 : (10 : ZMod 120543931) ^ 1839 = 87261689 := by
        calc
          (10 : ZMod 120543931) ^ 1839 = (10 : ZMod 120543931) ^ (919 + 919 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 919 * (10 : ZMod 120543931) ^ 919) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 87261689 := by rw [factor_0_9]; decide
      have factor_0_11 : (10 : ZMod 120543931) ^ 3678 = 37868400 := by
        calc
          (10 : ZMod 120543931) ^ 3678 = (10 : ZMod 120543931) ^ (1839 + 1839) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 1839 * (10 : ZMod 120543931) ^ 1839 := by rw [pow_add]
          _ = 37868400 := by rw [factor_0_10]; decide
      have factor_0_12 : (10 : ZMod 120543931) ^ 7357 = 60831727 := by
        calc
          (10 : ZMod 120543931) ^ 7357 = (10 : ZMod 120543931) ^ (3678 + 3678 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 3678 * (10 : ZMod 120543931) ^ 3678) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 60831727 := by rw [factor_0_11]; decide
      have factor_0_13 : (10 : ZMod 120543931) ^ 14714 = 69396196 := by
        calc
          (10 : ZMod 120543931) ^ 14714 = (10 : ZMod 120543931) ^ (7357 + 7357) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 7357 * (10 : ZMod 120543931) ^ 7357 := by rw [pow_add]
          _ = 69396196 := by rw [factor_0_12]; decide
      have factor_0_14 : (10 : ZMod 120543931) ^ 29429 = 77091831 := by
        calc
          (10 : ZMod 120543931) ^ 29429 = (10 : ZMod 120543931) ^ (14714 + 14714 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 14714 * (10 : ZMod 120543931) ^ 14714) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 77091831 := by rw [factor_0_13]; decide
      have factor_0_15 : (10 : ZMod 120543931) ^ 58859 = 27888912 := by
        calc
          (10 : ZMod 120543931) ^ 58859 = (10 : ZMod 120543931) ^ (29429 + 29429 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 29429 * (10 : ZMod 120543931) ^ 29429) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 27888912 := by rw [factor_0_14]; decide
      have factor_0_16 : (10 : ZMod 120543931) ^ 117718 = 20443756 := by
        calc
          (10 : ZMod 120543931) ^ 117718 = (10 : ZMod 120543931) ^ (58859 + 58859) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 58859 * (10 : ZMod 120543931) ^ 58859 := by rw [pow_add]
          _ = 20443756 := by rw [factor_0_15]; decide
      have factor_0_17 : (10 : ZMod 120543931) ^ 235437 = 22803559 := by
        calc
          (10 : ZMod 120543931) ^ 235437 = (10 : ZMod 120543931) ^ (117718 + 117718 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 117718 * (10 : ZMod 120543931) ^ 117718) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 22803559 := by rw [factor_0_16]; decide
      have factor_0_18 : (10 : ZMod 120543931) ^ 470874 = 14062612 := by
        calc
          (10 : ZMod 120543931) ^ 470874 = (10 : ZMod 120543931) ^ (235437 + 235437) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 235437 * (10 : ZMod 120543931) ^ 235437 := by rw [pow_add]
          _ = 14062612 := by rw [factor_0_17]; decide
      have factor_0_19 : (10 : ZMod 120543931) ^ 941749 = 805557 := by
        calc
          (10 : ZMod 120543931) ^ 941749 = (10 : ZMod 120543931) ^ (470874 + 470874 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 470874 * (10 : ZMod 120543931) ^ 470874) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 805557 := by rw [factor_0_18]; decide
      have factor_0_20 : (10 : ZMod 120543931) ^ 1883498 = 34099676 := by
        calc
          (10 : ZMod 120543931) ^ 1883498 = (10 : ZMod 120543931) ^ (941749 + 941749) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 941749 * (10 : ZMod 120543931) ^ 941749 := by rw [pow_add]
          _ = 34099676 := by rw [factor_0_19]; decide
      have factor_0_21 : (10 : ZMod 120543931) ^ 3766997 = 14734786 := by
        calc
          (10 : ZMod 120543931) ^ 3766997 = (10 : ZMod 120543931) ^ (1883498 + 1883498 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 1883498 * (10 : ZMod 120543931) ^ 1883498) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 14734786 := by rw [factor_0_20]; decide
      have factor_0_22 : (10 : ZMod 120543931) ^ 7533995 = 22245794 := by
        calc
          (10 : ZMod 120543931) ^ 7533995 = (10 : ZMod 120543931) ^ (3766997 + 3766997 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 3766997 * (10 : ZMod 120543931) ^ 3766997) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 22245794 := by rw [factor_0_21]; decide
      have factor_0_23 : (10 : ZMod 120543931) ^ 15067991 = 101453654 := by
        calc
          (10 : ZMod 120543931) ^ 15067991 = (10 : ZMod 120543931) ^ (7533995 + 7533995 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 7533995 * (10 : ZMod 120543931) ^ 7533995) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 101453654 := by rw [factor_0_22]; decide
      have factor_0_24 : (10 : ZMod 120543931) ^ 30135982 = 17503394 := by
        calc
          (10 : ZMod 120543931) ^ 30135982 = (10 : ZMod 120543931) ^ (15067991 + 15067991) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 15067991 * (10 : ZMod 120543931) ^ 15067991 := by rw [pow_add]
          _ = 17503394 := by rw [factor_0_23]; decide
      have factor_0_25 : (10 : ZMod 120543931) ^ 60271965 = 120543930 := by
        calc
          (10 : ZMod 120543931) ^ 60271965 = (10 : ZMod 120543931) ^ (30135982 + 30135982 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 30135982 * (10 : ZMod 120543931) ^ 30135982) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 120543930 := by rw [factor_0_24]; decide
      change (10 : ZMod 120543931) ^ 60271965 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (10 : ZMod 120543931) ^ 1 = 10 := by norm_num
      have factor_1_1 : (10 : ZMod 120543931) ^ 2 = 100 := by
        calc
          (10 : ZMod 120543931) ^ 2 = (10 : ZMod 120543931) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 1 * (10 : ZMod 120543931) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_1_0]; decide
      have factor_1_2 : (10 : ZMod 120543931) ^ 4 = 10000 := by
        calc
          (10 : ZMod 120543931) ^ 4 = (10 : ZMod 120543931) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 2 * (10 : ZMod 120543931) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [factor_1_1]; decide
      have factor_1_3 : (10 : ZMod 120543931) ^ 9 = 35648552 := by
        calc
          (10 : ZMod 120543931) ^ 9 = (10 : ZMod 120543931) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 4 * (10 : ZMod 120543931) ^ 4) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 35648552 := by rw [factor_1_2]; decide
      have factor_1_4 : (10 : ZMod 120543931) ^ 19 = 74469376 := by
        calc
          (10 : ZMod 120543931) ^ 19 = (10 : ZMod 120543931) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 9 * (10 : ZMod 120543931) ^ 9) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 74469376 := by rw [factor_1_3]; decide
      have factor_1_5 : (10 : ZMod 120543931) ^ 38 = 45715222 := by
        calc
          (10 : ZMod 120543931) ^ 38 = (10 : ZMod 120543931) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 19 * (10 : ZMod 120543931) ^ 19 := by rw [pow_add]
          _ = 45715222 := by rw [factor_1_4]; decide
      have factor_1_6 : (10 : ZMod 120543931) ^ 76 = 59632770 := by
        calc
          (10 : ZMod 120543931) ^ 76 = (10 : ZMod 120543931) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 38 * (10 : ZMod 120543931) ^ 38 := by rw [pow_add]
          _ = 59632770 := by rw [factor_1_5]; decide
      have factor_1_7 : (10 : ZMod 120543931) ^ 153 = 53146854 := by
        calc
          (10 : ZMod 120543931) ^ 153 = (10 : ZMod 120543931) ^ (76 + 76 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 76 * (10 : ZMod 120543931) ^ 76) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 53146854 := by rw [factor_1_6]; decide
      have factor_1_8 : (10 : ZMod 120543931) ^ 306 = 46938834 := by
        calc
          (10 : ZMod 120543931) ^ 306 = (10 : ZMod 120543931) ^ (153 + 153) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 153 * (10 : ZMod 120543931) ^ 153 := by rw [pow_add]
          _ = 46938834 := by rw [factor_1_7]; decide
      have factor_1_9 : (10 : ZMod 120543931) ^ 613 = 103477699 := by
        calc
          (10 : ZMod 120543931) ^ 613 = (10 : ZMod 120543931) ^ (306 + 306 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 306 * (10 : ZMod 120543931) ^ 306) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 103477699 := by rw [factor_1_8]; decide
      have factor_1_10 : (10 : ZMod 120543931) ^ 1226 = 77842451 := by
        calc
          (10 : ZMod 120543931) ^ 1226 = (10 : ZMod 120543931) ^ (613 + 613) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 613 * (10 : ZMod 120543931) ^ 613 := by rw [pow_add]
          _ = 77842451 := by rw [factor_1_9]; decide
      have factor_1_11 : (10 : ZMod 120543931) ^ 2452 = 63299799 := by
        calc
          (10 : ZMod 120543931) ^ 2452 = (10 : ZMod 120543931) ^ (1226 + 1226) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 1226 * (10 : ZMod 120543931) ^ 1226 := by rw [pow_add]
          _ = 63299799 := by rw [factor_1_10]; decide
      have factor_1_12 : (10 : ZMod 120543931) ^ 4904 = 78255362 := by
        calc
          (10 : ZMod 120543931) ^ 4904 = (10 : ZMod 120543931) ^ (2452 + 2452) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 2452 * (10 : ZMod 120543931) ^ 2452 := by rw [pow_add]
          _ = 78255362 := by rw [factor_1_11]; decide
      have factor_1_13 : (10 : ZMod 120543931) ^ 9809 = 47087833 := by
        calc
          (10 : ZMod 120543931) ^ 9809 = (10 : ZMod 120543931) ^ (4904 + 4904 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 4904 * (10 : ZMod 120543931) ^ 4904) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 47087833 := by rw [factor_1_12]; decide
      have factor_1_14 : (10 : ZMod 120543931) ^ 19619 = 88466347 := by
        calc
          (10 : ZMod 120543931) ^ 19619 = (10 : ZMod 120543931) ^ (9809 + 9809 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 9809 * (10 : ZMod 120543931) ^ 9809) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 88466347 := by rw [factor_1_13]; decide
      have factor_1_15 : (10 : ZMod 120543931) ^ 39239 = 104034584 := by
        calc
          (10 : ZMod 120543931) ^ 39239 = (10 : ZMod 120543931) ^ (19619 + 19619 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 19619 * (10 : ZMod 120543931) ^ 19619) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 104034584 := by rw [factor_1_14]; decide
      have factor_1_16 : (10 : ZMod 120543931) ^ 78479 = 71035908 := by
        calc
          (10 : ZMod 120543931) ^ 78479 = (10 : ZMod 120543931) ^ (39239 + 39239 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 39239 * (10 : ZMod 120543931) ^ 39239) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 71035908 := by rw [factor_1_15]; decide
      have factor_1_17 : (10 : ZMod 120543931) ^ 156958 = 1383605 := by
        calc
          (10 : ZMod 120543931) ^ 156958 = (10 : ZMod 120543931) ^ (78479 + 78479) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 78479 * (10 : ZMod 120543931) ^ 78479 := by rw [pow_add]
          _ = 1383605 := by rw [factor_1_16]; decide
      have factor_1_18 : (10 : ZMod 120543931) ^ 313916 = 4627814 := by
        calc
          (10 : ZMod 120543931) ^ 313916 = (10 : ZMod 120543931) ^ (156958 + 156958) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 156958 * (10 : ZMod 120543931) ^ 156958 := by rw [pow_add]
          _ = 4627814 := by rw [factor_1_17]; decide
      have factor_1_19 : (10 : ZMod 120543931) ^ 627832 = 104373550 := by
        calc
          (10 : ZMod 120543931) ^ 627832 = (10 : ZMod 120543931) ^ (313916 + 313916) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 313916 * (10 : ZMod 120543931) ^ 313916 := by rw [pow_add]
          _ = 104373550 := by rw [factor_1_18]; decide
      have factor_1_20 : (10 : ZMod 120543931) ^ 1255665 = 26352292 := by
        calc
          (10 : ZMod 120543931) ^ 1255665 = (10 : ZMod 120543931) ^ (627832 + 627832 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 627832 * (10 : ZMod 120543931) ^ 627832) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 26352292 := by rw [factor_1_19]; decide
      have factor_1_21 : (10 : ZMod 120543931) ^ 2511331 = 16139714 := by
        calc
          (10 : ZMod 120543931) ^ 2511331 = (10 : ZMod 120543931) ^ (1255665 + 1255665 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 1255665 * (10 : ZMod 120543931) ^ 1255665) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 16139714 := by rw [factor_1_20]; decide
      have factor_1_22 : (10 : ZMod 120543931) ^ 5022663 = 80102911 := by
        calc
          (10 : ZMod 120543931) ^ 5022663 = (10 : ZMod 120543931) ^ (2511331 + 2511331 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 2511331 * (10 : ZMod 120543931) ^ 2511331) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 80102911 := by rw [factor_1_21]; decide
      have factor_1_23 : (10 : ZMod 120543931) ^ 10045327 = 34421886 := by
        calc
          (10 : ZMod 120543931) ^ 10045327 = (10 : ZMod 120543931) ^ (5022663 + 5022663 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 5022663 * (10 : ZMod 120543931) ^ 5022663) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 34421886 := by rw [factor_1_22]; decide
      have factor_1_24 : (10 : ZMod 120543931) ^ 20090655 = 17936557 := by
        calc
          (10 : ZMod 120543931) ^ 20090655 = (10 : ZMod 120543931) ^ (10045327 + 10045327 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 10045327 * (10 : ZMod 120543931) ^ 10045327) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 17936557 := by rw [factor_1_23]; decide
      have factor_1_25 : (10 : ZMod 120543931) ^ 40181310 = 17936556 := by
        calc
          (10 : ZMod 120543931) ^ 40181310 = (10 : ZMod 120543931) ^ (20090655 + 20090655) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 20090655 * (10 : ZMod 120543931) ^ 20090655 := by rw [pow_add]
          _ = 17936556 := by rw [factor_1_24]; decide
      change (10 : ZMod 120543931) ^ 40181310 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (10 : ZMod 120543931) ^ 1 = 10 := by norm_num
      have factor_2_1 : (10 : ZMod 120543931) ^ 2 = 100 := by
        calc
          (10 : ZMod 120543931) ^ 2 = (10 : ZMod 120543931) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 1 * (10 : ZMod 120543931) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_2_0]; decide
      have factor_2_2 : (10 : ZMod 120543931) ^ 5 = 100000 := by
        calc
          (10 : ZMod 120543931) ^ 5 = (10 : ZMod 120543931) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 2 * (10 : ZMod 120543931) ^ 2) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 100000 := by rw [factor_2_1]; decide
      have factor_2_3 : (10 : ZMod 120543931) ^ 11 = 69081201 := by
        calc
          (10 : ZMod 120543931) ^ 11 = (10 : ZMod 120543931) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 5 * (10 : ZMod 120543931) ^ 5) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 69081201 := by rw [factor_2_2]; decide
      have factor_2_4 : (10 : ZMod 120543931) ^ 22 = 93770573 := by
        calc
          (10 : ZMod 120543931) ^ 22 = (10 : ZMod 120543931) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 11 * (10 : ZMod 120543931) ^ 11 := by rw [pow_add]
          _ = 93770573 := by rw [factor_2_3]; decide
      have factor_2_5 : (10 : ZMod 120543931) ^ 45 = 90092359 := by
        calc
          (10 : ZMod 120543931) ^ 45 = (10 : ZMod 120543931) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 22 * (10 : ZMod 120543931) ^ 22) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 90092359 := by rw [factor_2_4]; decide
      have factor_2_6 : (10 : ZMod 120543931) ^ 91 = 46857225 := by
        calc
          (10 : ZMod 120543931) ^ 91 = (10 : ZMod 120543931) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 45 * (10 : ZMod 120543931) ^ 45) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 46857225 := by rw [factor_2_5]; decide
      have factor_2_7 : (10 : ZMod 120543931) ^ 183 = 76593044 := by
        calc
          (10 : ZMod 120543931) ^ 183 = (10 : ZMod 120543931) ^ (91 + 91 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 91 * (10 : ZMod 120543931) ^ 91) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 76593044 := by rw [factor_2_6]; decide
      have factor_2_8 : (10 : ZMod 120543931) ^ 367 = 43927449 := by
        calc
          (10 : ZMod 120543931) ^ 367 = (10 : ZMod 120543931) ^ (183 + 183 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 183 * (10 : ZMod 120543931) ^ 183) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 43927449 := by rw [factor_2_7]; decide
      have factor_2_9 : (10 : ZMod 120543931) ^ 735 = 99393946 := by
        calc
          (10 : ZMod 120543931) ^ 735 = (10 : ZMod 120543931) ^ (367 + 367 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 367 * (10 : ZMod 120543931) ^ 367) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 99393946 := by rw [factor_2_8]; decide
      have factor_2_10 : (10 : ZMod 120543931) ^ 1471 = 87848823 := by
        calc
          (10 : ZMod 120543931) ^ 1471 = (10 : ZMod 120543931) ^ (735 + 735 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 735 * (10 : ZMod 120543931) ^ 735) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 87848823 := by rw [factor_2_9]; decide
      have factor_2_11 : (10 : ZMod 120543931) ^ 2942 = 7943936 := by
        calc
          (10 : ZMod 120543931) ^ 2942 = (10 : ZMod 120543931) ^ (1471 + 1471) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 1471 * (10 : ZMod 120543931) ^ 1471 := by rw [pow_add]
          _ = 7943936 := by rw [factor_2_10]; decide
      have factor_2_12 : (10 : ZMod 120543931) ^ 5885 = 91471757 := by
        calc
          (10 : ZMod 120543931) ^ 5885 = (10 : ZMod 120543931) ^ (2942 + 2942 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 2942 * (10 : ZMod 120543931) ^ 2942) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 91471757 := by rw [factor_2_11]; decide
      have factor_2_13 : (10 : ZMod 120543931) ^ 11771 = 303615 := by
        calc
          (10 : ZMod 120543931) ^ 11771 = (10 : ZMod 120543931) ^ (5885 + 5885 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 5885 * (10 : ZMod 120543931) ^ 5885) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 303615 := by rw [factor_2_12]; decide
      have factor_2_14 : (10 : ZMod 120543931) ^ 23543 = 21241893 := by
        calc
          (10 : ZMod 120543931) ^ 23543 = (10 : ZMod 120543931) ^ (11771 + 11771 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 11771 * (10 : ZMod 120543931) ^ 11771) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 21241893 := by rw [factor_2_13]; decide
      have factor_2_15 : (10 : ZMod 120543931) ^ 47087 = 8422898 := by
        calc
          (10 : ZMod 120543931) ^ 47087 = (10 : ZMod 120543931) ^ (23543 + 23543 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 23543 * (10 : ZMod 120543931) ^ 23543) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 8422898 := by rw [factor_2_14]; decide
      have factor_2_16 : (10 : ZMod 120543931) ^ 94174 = 44479802 := by
        calc
          (10 : ZMod 120543931) ^ 94174 = (10 : ZMod 120543931) ^ (47087 + 47087) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 47087 * (10 : ZMod 120543931) ^ 47087 := by rw [pow_add]
          _ = 44479802 := by rw [factor_2_15]; decide
      have factor_2_17 : (10 : ZMod 120543931) ^ 188349 = 113259044 := by
        calc
          (10 : ZMod 120543931) ^ 188349 = (10 : ZMod 120543931) ^ (94174 + 94174 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 94174 * (10 : ZMod 120543931) ^ 94174) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 113259044 := by rw [factor_2_16]; decide
      have factor_2_18 : (10 : ZMod 120543931) ^ 376699 = 44904811 := by
        calc
          (10 : ZMod 120543931) ^ 376699 = (10 : ZMod 120543931) ^ (188349 + 188349 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 188349 * (10 : ZMod 120543931) ^ 188349) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 44904811 := by rw [factor_2_17]; decide
      have factor_2_19 : (10 : ZMod 120543931) ^ 753399 = 11104886 := by
        calc
          (10 : ZMod 120543931) ^ 753399 = (10 : ZMod 120543931) ^ (376699 + 376699 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 376699 * (10 : ZMod 120543931) ^ 376699) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 11104886 := by rw [factor_2_18]; decide
      have factor_2_20 : (10 : ZMod 120543931) ^ 1506799 = 24131690 := by
        calc
          (10 : ZMod 120543931) ^ 1506799 = (10 : ZMod 120543931) ^ (753399 + 753399 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 753399 * (10 : ZMod 120543931) ^ 753399) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 24131690 := by rw [factor_2_19]; decide
      have factor_2_21 : (10 : ZMod 120543931) ^ 3013598 = 13477787 := by
        calc
          (10 : ZMod 120543931) ^ 3013598 = (10 : ZMod 120543931) ^ (1506799 + 1506799) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 1506799 * (10 : ZMod 120543931) ^ 1506799 := by rw [pow_add]
          _ = 13477787 := by rw [factor_2_20]; decide
      have factor_2_22 : (10 : ZMod 120543931) ^ 6027196 = 79195194 := by
        calc
          (10 : ZMod 120543931) ^ 6027196 = (10 : ZMod 120543931) ^ (3013598 + 3013598) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 3013598 * (10 : ZMod 120543931) ^ 3013598 := by rw [pow_add]
          _ = 79195194 := by rw [factor_2_21]; decide
      have factor_2_23 : (10 : ZMod 120543931) ^ 12054393 = 99806504 := by
        calc
          (10 : ZMod 120543931) ^ 12054393 = (10 : ZMod 120543931) ^ (6027196 + 6027196 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 6027196 * (10 : ZMod 120543931) ^ 6027196) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 99806504 := by rw [factor_2_22]; decide
      have factor_2_24 : (10 : ZMod 120543931) ^ 24108786 = 43106036 := by
        calc
          (10 : ZMod 120543931) ^ 24108786 = (10 : ZMod 120543931) ^ (12054393 + 12054393) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 12054393 * (10 : ZMod 120543931) ^ 12054393 := by rw [pow_add]
          _ = 43106036 := by rw [factor_2_23]; decide
      change (10 : ZMod 120543931) ^ 24108786 ≠ 1
      rw [factor_2_24]
      decide
    ·
      have factor_3_0 : (10 : ZMod 120543931) ^ 1 = 10 := by norm_num
      have factor_3_1 : (10 : ZMod 120543931) ^ 2 = 100 := by
        calc
          (10 : ZMod 120543931) ^ 2 = (10 : ZMod 120543931) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 1 * (10 : ZMod 120543931) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_3_0]; decide
      have factor_3_2 : (10 : ZMod 120543931) ^ 4 = 10000 := by
        calc
          (10 : ZMod 120543931) ^ 4 = (10 : ZMod 120543931) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 2 * (10 : ZMod 120543931) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [factor_3_1]; decide
      have factor_3_3 : (10 : ZMod 120543931) ^ 8 = 100000000 := by
        calc
          (10 : ZMod 120543931) ^ 8 = (10 : ZMod 120543931) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 4 * (10 : ZMod 120543931) ^ 4 := by rw [pow_add]
          _ = 100000000 := by rw [factor_3_2]; decide
      have factor_3_4 : (10 : ZMod 120543931) ^ 17 = 5566451 := by
        calc
          (10 : ZMod 120543931) ^ 17 = (10 : ZMod 120543931) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 8 * (10 : ZMod 120543931) ^ 8) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 5566451 := by rw [factor_3_3]; decide
      have factor_3_5 : (10 : ZMod 120543931) ^ 35 = 52843957 := by
        calc
          (10 : ZMod 120543931) ^ 35 = (10 : ZMod 120543931) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 17 * (10 : ZMod 120543931) ^ 17) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 52843957 := by rw [factor_3_4]; decide
      have factor_3_6 : (10 : ZMod 120543931) ^ 70 = 92858666 := by
        calc
          (10 : ZMod 120543931) ^ 70 = (10 : ZMod 120543931) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 35 * (10 : ZMod 120543931) ^ 35 := by rw [pow_add]
          _ = 92858666 := by rw [factor_3_5]; decide
      have factor_3_7 : (10 : ZMod 120543931) ^ 141 = 20156409 := by
        calc
          (10 : ZMod 120543931) ^ 141 = (10 : ZMod 120543931) ^ (70 + 70 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 70 * (10 : ZMod 120543931) ^ 70) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 20156409 := by rw [factor_3_6]; decide
      have factor_3_8 : (10 : ZMod 120543931) ^ 282 = 40908605 := by
        calc
          (10 : ZMod 120543931) ^ 282 = (10 : ZMod 120543931) ^ (141 + 141) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 141 * (10 : ZMod 120543931) ^ 141 := by rw [pow_add]
          _ = 40908605 := by rw [factor_3_7]; decide
      have factor_3_9 : (10 : ZMod 120543931) ^ 565 = 13872947 := by
        calc
          (10 : ZMod 120543931) ^ 565 = (10 : ZMod 120543931) ^ (282 + 282 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 282 * (10 : ZMod 120543931) ^ 282) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 13872947 := by rw [factor_3_8]; decide
      have factor_3_10 : (10 : ZMod 120543931) ^ 1131 = 22803878 := by
        calc
          (10 : ZMod 120543931) ^ 1131 = (10 : ZMod 120543931) ^ (565 + 565 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 565 * (10 : ZMod 120543931) ^ 565) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 22803878 := by rw [factor_3_9]; decide
      have factor_3_11 : (10 : ZMod 120543931) ^ 2263 = 11281502 := by
        calc
          (10 : ZMod 120543931) ^ 2263 = (10 : ZMod 120543931) ^ (1131 + 1131 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 1131 * (10 : ZMod 120543931) ^ 1131) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 11281502 := by rw [factor_3_10]; decide
      have factor_3_12 : (10 : ZMod 120543931) ^ 4527 = 39969494 := by
        calc
          (10 : ZMod 120543931) ^ 4527 = (10 : ZMod 120543931) ^ (2263 + 2263 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 2263 * (10 : ZMod 120543931) ^ 2263) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 39969494 := by rw [factor_3_11]; decide
      have factor_3_13 : (10 : ZMod 120543931) ^ 9055 = 23867026 := by
        calc
          (10 : ZMod 120543931) ^ 9055 = (10 : ZMod 120543931) ^ (4527 + 4527 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 4527 * (10 : ZMod 120543931) ^ 4527) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 23867026 := by rw [factor_3_12]; decide
      have factor_3_14 : (10 : ZMod 120543931) ^ 18110 = 3474798 := by
        calc
          (10 : ZMod 120543931) ^ 18110 = (10 : ZMod 120543931) ^ (9055 + 9055) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 9055 * (10 : ZMod 120543931) ^ 9055 := by rw [pow_add]
          _ = 3474798 := by rw [factor_3_13]; decide
      have factor_3_15 : (10 : ZMod 120543931) ^ 36221 = 106185476 := by
        calc
          (10 : ZMod 120543931) ^ 36221 = (10 : ZMod 120543931) ^ (18110 + 18110 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 18110 * (10 : ZMod 120543931) ^ 18110) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 106185476 := by rw [factor_3_14]; decide
      have factor_3_16 : (10 : ZMod 120543931) ^ 72442 = 29693104 := by
        calc
          (10 : ZMod 120543931) ^ 72442 = (10 : ZMod 120543931) ^ (36221 + 36221) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 36221 * (10 : ZMod 120543931) ^ 36221 := by rw [pow_add]
          _ = 29693104 := by rw [factor_3_15]; decide
      have factor_3_17 : (10 : ZMod 120543931) ^ 144884 = 54281443 := by
        calc
          (10 : ZMod 120543931) ^ 144884 = (10 : ZMod 120543931) ^ (72442 + 72442) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 72442 * (10 : ZMod 120543931) ^ 72442 := by rw [pow_add]
          _ = 54281443 := by rw [factor_3_16]; decide
      have factor_3_18 : (10 : ZMod 120543931) ^ 289769 = 36333512 := by
        calc
          (10 : ZMod 120543931) ^ 289769 = (10 : ZMod 120543931) ^ (144884 + 144884 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 144884 * (10 : ZMod 120543931) ^ 144884) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 36333512 := by rw [factor_3_17]; decide
      have factor_3_19 : (10 : ZMod 120543931) ^ 579538 = 11564330 := by
        calc
          (10 : ZMod 120543931) ^ 579538 = (10 : ZMod 120543931) ^ (289769 + 289769) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 289769 * (10 : ZMod 120543931) ^ 289769 := by rw [pow_add]
          _ = 11564330 := by rw [factor_3_18]; decide
      have factor_3_20 : (10 : ZMod 120543931) ^ 1159076 = 962811 := by
        calc
          (10 : ZMod 120543931) ^ 1159076 = (10 : ZMod 120543931) ^ (579538 + 579538) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 579538 * (10 : ZMod 120543931) ^ 579538 := by rw [pow_add]
          _ = 962811 := by rw [factor_3_19]; decide
      have factor_3_21 : (10 : ZMod 120543931) ^ 2318152 = 22192331 := by
        calc
          (10 : ZMod 120543931) ^ 2318152 = (10 : ZMod 120543931) ^ (1159076 + 1159076) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 1159076 * (10 : ZMod 120543931) ^ 1159076 := by rw [pow_add]
          _ = 22192331 := by rw [factor_3_20]; decide
      have factor_3_22 : (10 : ZMod 120543931) ^ 4636305 = 29501763 := by
        calc
          (10 : ZMod 120543931) ^ 4636305 = (10 : ZMod 120543931) ^ (2318152 + 2318152 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 2318152 * (10 : ZMod 120543931) ^ 2318152) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 29501763 := by rw [factor_3_21]; decide
      have factor_3_23 : (10 : ZMod 120543931) ^ 9272610 = 77535487 := by
        calc
          (10 : ZMod 120543931) ^ 9272610 = (10 : ZMod 120543931) ^ (4636305 + 4636305) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 4636305 * (10 : ZMod 120543931) ^ 4636305 := by rw [pow_add]
          _ = 77535487 := by rw [factor_3_22]; decide
      change (10 : ZMod 120543931) ^ 9272610 ≠ 1
      rw [factor_3_23]
      decide
    ·
      have factor_4_0 : (10 : ZMod 120543931) ^ 1 = 10 := by norm_num
      have factor_4_1 : (10 : ZMod 120543931) ^ 3 = 1000 := by
        calc
          (10 : ZMod 120543931) ^ 3 = (10 : ZMod 120543931) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 1 * (10 : ZMod 120543931) ^ 1) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_4_0]; decide
      have factor_4_2 : (10 : ZMod 120543931) ^ 7 = 10000000 := by
        calc
          (10 : ZMod 120543931) ^ 7 = (10 : ZMod 120543931) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 3 * (10 : ZMod 120543931) ^ 3) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 10000000 := by rw [factor_4_1]; decide
      have factor_4_3 : (10 : ZMod 120543931) ^ 15 = 95285370 := by
        calc
          (10 : ZMod 120543931) ^ 15 = (10 : ZMod 120543931) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 7 * (10 : ZMod 120543931) ^ 7) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 95285370 := by rw [factor_4_2]; decide
      have factor_4_4 : (10 : ZMod 120543931) ^ 30 = 116630398 := by
        calc
          (10 : ZMod 120543931) ^ 30 = (10 : ZMod 120543931) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 15 * (10 : ZMod 120543931) ^ 15 := by rw [pow_add]
          _ = 116630398 := by rw [factor_4_3]; decide
      have factor_4_5 : (10 : ZMod 120543931) ^ 60 = 31388884 := by
        calc
          (10 : ZMod 120543931) ^ 60 = (10 : ZMod 120543931) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 30 * (10 : ZMod 120543931) ^ 30 := by rw [pow_add]
          _ = 31388884 := by rw [factor_4_4]; decide
      have factor_4_6 : (10 : ZMod 120543931) ^ 120 = 76142748 := by
        calc
          (10 : ZMod 120543931) ^ 120 = (10 : ZMod 120543931) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 60 * (10 : ZMod 120543931) ^ 60 := by rw [pow_add]
          _ = 76142748 := by rw [factor_4_5]; decide
      have factor_4_7 : (10 : ZMod 120543931) ^ 241 = 39215767 := by
        calc
          (10 : ZMod 120543931) ^ 241 = (10 : ZMod 120543931) ^ (120 + 120 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 120 * (10 : ZMod 120543931) ^ 120) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 39215767 := by rw [factor_4_6]; decide
      have factor_4_8 : (10 : ZMod 120543931) ^ 482 = 54135041 := by
        calc
          (10 : ZMod 120543931) ^ 482 = (10 : ZMod 120543931) ^ (241 + 241) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 241 * (10 : ZMod 120543931) ^ 241 := by rw [pow_add]
          _ = 54135041 := by rw [factor_4_7]; decide
      have factor_4_9 : (10 : ZMod 120543931) ^ 964 = 91004491 := by
        calc
          (10 : ZMod 120543931) ^ 964 = (10 : ZMod 120543931) ^ (482 + 482) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 482 * (10 : ZMod 120543931) ^ 482 := by rw [pow_add]
          _ = 91004491 := by rw [factor_4_8]; decide
      have factor_4_10 : (10 : ZMod 120543931) ^ 1929 = 70206716 := by
        calc
          (10 : ZMod 120543931) ^ 1929 = (10 : ZMod 120543931) ^ (964 + 964 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 964 * (10 : ZMod 120543931) ^ 964) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 70206716 := by rw [factor_4_9]; decide
      have factor_4_11 : (10 : ZMod 120543931) ^ 3859 = 2860462 := by
        calc
          (10 : ZMod 120543931) ^ 3859 = (10 : ZMod 120543931) ^ (1929 + 1929 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 1929 * (10 : ZMod 120543931) ^ 1929) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 2860462 := by rw [factor_4_10]; decide
      have factor_4_12 : (10 : ZMod 120543931) ^ 7719 = 101225984 := by
        calc
          (10 : ZMod 120543931) ^ 7719 = (10 : ZMod 120543931) ^ (3859 + 3859 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 3859 * (10 : ZMod 120543931) ^ 3859) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 101225984 := by rw [factor_4_11]; decide
      have factor_4_13 : (10 : ZMod 120543931) ^ 15438 = 40562803 := by
        calc
          (10 : ZMod 120543931) ^ 15438 = (10 : ZMod 120543931) ^ (7719 + 7719) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 7719 * (10 : ZMod 120543931) ^ 7719 := by rw [pow_add]
          _ = 40562803 := by rw [factor_4_12]; decide
      have factor_4_14 : (10 : ZMod 120543931) ^ 30877 = 106637092 := by
        calc
          (10 : ZMod 120543931) ^ 30877 = (10 : ZMod 120543931) ^ (15438 + 15438 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 15438 * (10 : ZMod 120543931) ^ 15438) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 106637092 := by rw [factor_4_13]; decide
      have factor_4_15 : (10 : ZMod 120543931) ^ 61754 = 90795176 := by
        calc
          (10 : ZMod 120543931) ^ 61754 = (10 : ZMod 120543931) ^ (30877 + 30877) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 30877 * (10 : ZMod 120543931) ^ 30877 := by rw [pow_add]
          _ = 90795176 := by rw [factor_4_14]; decide
      have factor_4_16 : (10 : ZMod 120543931) ^ 123508 = 86622150 := by
        calc
          (10 : ZMod 120543931) ^ 123508 = (10 : ZMod 120543931) ^ (61754 + 61754) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 61754 * (10 : ZMod 120543931) ^ 61754 := by rw [pow_add]
          _ = 86622150 := by rw [factor_4_15]; decide
      have factor_4_17 : (10 : ZMod 120543931) ^ 247016 = 54567540 := by
        calc
          (10 : ZMod 120543931) ^ 247016 = (10 : ZMod 120543931) ^ (123508 + 123508) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 123508 * (10 : ZMod 120543931) ^ 123508 := by rw [pow_add]
          _ = 54567540 := by rw [factor_4_16]; decide
      have factor_4_18 : (10 : ZMod 120543931) ^ 494032 = 27879376 := by
        calc
          (10 : ZMod 120543931) ^ 494032 = (10 : ZMod 120543931) ^ (247016 + 247016) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 247016 * (10 : ZMod 120543931) ^ 247016 := by rw [pow_add]
          _ = 27879376 := by rw [factor_4_17]; decide
      have factor_4_19 : (10 : ZMod 120543931) ^ 988065 = 56553876 := by
        calc
          (10 : ZMod 120543931) ^ 988065 = (10 : ZMod 120543931) ^ (494032 + 494032 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 494032 * (10 : ZMod 120543931) ^ 494032) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 56553876 := by rw [factor_4_18]; decide
      have factor_4_20 : (10 : ZMod 120543931) ^ 1976130 = 571051 := by
        calc
          (10 : ZMod 120543931) ^ 1976130 = (10 : ZMod 120543931) ^ (988065 + 988065) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 988065 * (10 : ZMod 120543931) ^ 988065 := by rw [pow_add]
          _ = 571051 := by rw [factor_4_19]; decide
      change (10 : ZMod 120543931) ^ 1976130 ≠ 1
      rw [factor_4_20]
      decide
    ·
      have factor_5_0 : (10 : ZMod 120543931) ^ 1 = 10 := by norm_num
      have factor_5_1 : (10 : ZMod 120543931) ^ 3 = 1000 := by
        calc
          (10 : ZMod 120543931) ^ 3 = (10 : ZMod 120543931) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 1 * (10 : ZMod 120543931) ^ 1) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_5_0]; decide
      have factor_5_2 : (10 : ZMod 120543931) ^ 6 = 1000000 := by
        calc
          (10 : ZMod 120543931) ^ 6 = (10 : ZMod 120543931) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 3 * (10 : ZMod 120543931) ^ 3 := by rw [pow_add]
          _ = 1000000 := by rw [factor_5_1]; decide
      have factor_5_3 : (10 : ZMod 120543931) ^ 13 = 37116033 := by
        calc
          (10 : ZMod 120543931) ^ 13 = (10 : ZMod 120543931) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 6 * (10 : ZMod 120543931) ^ 6) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 37116033 := by rw [factor_5_2]; decide
      have factor_5_4 : (10 : ZMod 120543931) ^ 26 = 115034682 := by
        calc
          (10 : ZMod 120543931) ^ 26 = (10 : ZMod 120543931) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 13 * (10 : ZMod 120543931) ^ 13 := by rw [pow_add]
          _ = 115034682 := by rw [factor_5_3]; decide
      have factor_5_5 : (10 : ZMod 120543931) ^ 52 = 68157511 := by
        calc
          (10 : ZMod 120543931) ^ 52 = (10 : ZMod 120543931) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 26 * (10 : ZMod 120543931) ^ 26 := by rw [pow_add]
          _ = 68157511 := by rw [factor_5_4]; decide
      have factor_5_6 : (10 : ZMod 120543931) ^ 104 = 114969720 := by
        calc
          (10 : ZMod 120543931) ^ 104 = (10 : ZMod 120543931) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 52 * (10 : ZMod 120543931) ^ 52 := by rw [pow_add]
          _ = 114969720 := by rw [factor_5_5]; decide
      have factor_5_7 : (10 : ZMod 120543931) ^ 209 = 27142025 := by
        calc
          (10 : ZMod 120543931) ^ 209 = (10 : ZMod 120543931) ^ (104 + 104 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 104 * (10 : ZMod 120543931) ^ 104) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 27142025 := by rw [factor_5_6]; decide
      have factor_5_8 : (10 : ZMod 120543931) ^ 418 = 113697638 := by
        calc
          (10 : ZMod 120543931) ^ 418 = (10 : ZMod 120543931) ^ (209 + 209) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 209 * (10 : ZMod 120543931) ^ 209 := by rw [pow_add]
          _ = 113697638 := by rw [factor_5_7]; decide
      have factor_5_9 : (10 : ZMod 120543931) ^ 836 = 28431464 := by
        calc
          (10 : ZMod 120543931) ^ 836 = (10 : ZMod 120543931) ^ (418 + 418) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 418 * (10 : ZMod 120543931) ^ 418 := by rw [pow_add]
          _ = 28431464 := by rw [factor_5_8]; decide
      have factor_5_10 : (10 : ZMod 120543931) ^ 1672 = 72014118 := by
        calc
          (10 : ZMod 120543931) ^ 1672 = (10 : ZMod 120543931) ^ (836 + 836) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 836 * (10 : ZMod 120543931) ^ 836 := by rw [pow_add]
          _ = 72014118 := by rw [factor_5_9]; decide
      have factor_5_11 : (10 : ZMod 120543931) ^ 3345 = 30826528 := by
        calc
          (10 : ZMod 120543931) ^ 3345 = (10 : ZMod 120543931) ^ (1672 + 1672 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 1672 * (10 : ZMod 120543931) ^ 1672) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 30826528 := by rw [factor_5_10]; decide
      have factor_5_12 : (10 : ZMod 120543931) ^ 6690 = 18621240 := by
        calc
          (10 : ZMod 120543931) ^ 6690 = (10 : ZMod 120543931) ^ (3345 + 3345) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 3345 * (10 : ZMod 120543931) ^ 3345 := by rw [pow_add]
          _ = 18621240 := by rw [factor_5_11]; decide
      have factor_5_13 : (10 : ZMod 120543931) ^ 13381 = 67459086 := by
        calc
          (10 : ZMod 120543931) ^ 13381 = (10 : ZMod 120543931) ^ (6690 + 6690 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 6690 * (10 : ZMod 120543931) ^ 6690) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 67459086 := by rw [factor_5_12]; decide
      have factor_5_14 : (10 : ZMod 120543931) ^ 26763 = 53321483 := by
        calc
          (10 : ZMod 120543931) ^ 26763 = (10 : ZMod 120543931) ^ (13381 + 13381 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 13381 * (10 : ZMod 120543931) ^ 13381) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 53321483 := by rw [factor_5_13]; decide
      have factor_5_15 : (10 : ZMod 120543931) ^ 53527 = 31136566 := by
        calc
          (10 : ZMod 120543931) ^ 53527 = (10 : ZMod 120543931) ^ (26763 + 26763 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 26763 * (10 : ZMod 120543931) ^ 26763) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 31136566 := by rw [factor_5_14]; decide
      have factor_5_16 : (10 : ZMod 120543931) ^ 107055 = 27824523 := by
        calc
          (10 : ZMod 120543931) ^ 107055 = (10 : ZMod 120543931) ^ (53527 + 53527 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = ((10 : ZMod 120543931) ^ 53527 * (10 : ZMod 120543931) ^ 53527) * (10 : ZMod 120543931) := by rw [pow_succ, pow_add]
          _ = 27824523 := by rw [factor_5_15]; decide
      have factor_5_17 : (10 : ZMod 120543931) ^ 214110 = 75464101 := by
        calc
          (10 : ZMod 120543931) ^ 214110 = (10 : ZMod 120543931) ^ (107055 + 107055) :=
            congrArg (fun n : ℕ => (10 : ZMod 120543931) ^ n) (by norm_num)
          _ = (10 : ZMod 120543931) ^ 107055 * (10 : ZMod 120543931) ^ 107055 := by rw [pow_add]
          _ = 75464101 := by rw [factor_5_16]; decide
      change (10 : ZMod 120543931) ^ 214110 ≠ 1
      rw [factor_5_17]
      decide

#print axioms prime_lucas_120543931

end TotientTailPeriodKiller
end Erdos249257
