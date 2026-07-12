import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_57339083 : Nat.Prime 57339083 := by
  apply lucas_primality 57339083 (2 : ZMod 57339083)
  ·
      have fermat_0 : (2 : ZMod 57339083) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 57339083) ^ 3 = 8 := by
        calc
          (2 : ZMod 57339083) ^ 3 = (2 : ZMod 57339083) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 1 * (2 : ZMod 57339083) ^ 1) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 57339083) ^ 6 = 64 := by
        calc
          (2 : ZMod 57339083) ^ 6 = (2 : ZMod 57339083) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 3 * (2 : ZMod 57339083) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 57339083) ^ 13 = 8192 := by
        calc
          (2 : ZMod 57339083) ^ 13 = (2 : ZMod 57339083) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 6 * (2 : ZMod 57339083) ^ 6) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 57339083) ^ 27 = 19539562 := by
        calc
          (2 : ZMod 57339083) ^ 27 = (2 : ZMod 57339083) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 13 * (2 : ZMod 57339083) ^ 13) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 19539562 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 57339083) ^ 54 = 20111190 := by
        calc
          (2 : ZMod 57339083) ^ 54 = (2 : ZMod 57339083) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 27 * (2 : ZMod 57339083) ^ 27 := by rw [pow_add]
          _ = 20111190 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 57339083) ^ 109 = 40130001 := by
        calc
          (2 : ZMod 57339083) ^ 109 = (2 : ZMod 57339083) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 54 * (2 : ZMod 57339083) ^ 54) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 40130001 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 57339083) ^ 218 = 38645368 := by
        calc
          (2 : ZMod 57339083) ^ 218 = (2 : ZMod 57339083) ^ (109 + 109) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 109 * (2 : ZMod 57339083) ^ 109 := by rw [pow_add]
          _ = 38645368 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 57339083) ^ 437 = 36596889 := by
        calc
          (2 : ZMod 57339083) ^ 437 = (2 : ZMod 57339083) ^ (218 + 218 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 218 * (2 : ZMod 57339083) ^ 218) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 36596889 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 57339083) ^ 874 = 20499689 := by
        calc
          (2 : ZMod 57339083) ^ 874 = (2 : ZMod 57339083) ^ (437 + 437) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 437 * (2 : ZMod 57339083) ^ 437 := by rw [pow_add]
          _ = 20499689 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 57339083) ^ 1749 = 54430098 := by
        calc
          (2 : ZMod 57339083) ^ 1749 = (2 : ZMod 57339083) ^ (874 + 874 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 874 * (2 : ZMod 57339083) ^ 874) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 54430098 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 57339083) ^ 3499 = 11704921 := by
        calc
          (2 : ZMod 57339083) ^ 3499 = (2 : ZMod 57339083) ^ (1749 + 1749 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 1749 * (2 : ZMod 57339083) ^ 1749) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 11704921 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 57339083) ^ 6999 = 4225489 := by
        calc
          (2 : ZMod 57339083) ^ 6999 = (2 : ZMod 57339083) ^ (3499 + 3499 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 3499 * (2 : ZMod 57339083) ^ 3499) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 4225489 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 57339083) ^ 13998 = 54911917 := by
        calc
          (2 : ZMod 57339083) ^ 13998 = (2 : ZMod 57339083) ^ (6999 + 6999) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 6999 * (2 : ZMod 57339083) ^ 6999 := by rw [pow_add]
          _ = 54911917 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 57339083) ^ 27997 = 5451940 := by
        calc
          (2 : ZMod 57339083) ^ 27997 = (2 : ZMod 57339083) ^ (13998 + 13998 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 13998 * (2 : ZMod 57339083) ^ 13998) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 5451940 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 57339083) ^ 55995 = 30462539 := by
        calc
          (2 : ZMod 57339083) ^ 55995 = (2 : ZMod 57339083) ^ (27997 + 27997 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 27997 * (2 : ZMod 57339083) ^ 27997) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 30462539 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 57339083) ^ 111990 = 24003216 := by
        calc
          (2 : ZMod 57339083) ^ 111990 = (2 : ZMod 57339083) ^ (55995 + 55995) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 55995 * (2 : ZMod 57339083) ^ 55995 := by rw [pow_add]
          _ = 24003216 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 57339083) ^ 223980 = 33898388 := by
        calc
          (2 : ZMod 57339083) ^ 223980 = (2 : ZMod 57339083) ^ (111990 + 111990) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 111990 * (2 : ZMod 57339083) ^ 111990 := by rw [pow_add]
          _ = 33898388 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 57339083) ^ 447961 = 54251384 := by
        calc
          (2 : ZMod 57339083) ^ 447961 = (2 : ZMod 57339083) ^ (223980 + 223980 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 223980 * (2 : ZMod 57339083) ^ 223980) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 54251384 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 57339083) ^ 895923 = 2212050 := by
        calc
          (2 : ZMod 57339083) ^ 895923 = (2 : ZMod 57339083) ^ (447961 + 447961 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 447961 * (2 : ZMod 57339083) ^ 447961) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 2212050 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 57339083) ^ 1791846 = 19876529 := by
        calc
          (2 : ZMod 57339083) ^ 1791846 = (2 : ZMod 57339083) ^ (895923 + 895923) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 895923 * (2 : ZMod 57339083) ^ 895923 := by rw [pow_add]
          _ = 19876529 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 57339083) ^ 3583692 = 31539233 := by
        calc
          (2 : ZMod 57339083) ^ 3583692 = (2 : ZMod 57339083) ^ (1791846 + 1791846) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 1791846 * (2 : ZMod 57339083) ^ 1791846 := by rw [pow_add]
          _ = 31539233 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 57339083) ^ 7167385 = 37061717 := by
        calc
          (2 : ZMod 57339083) ^ 7167385 = (2 : ZMod 57339083) ^ (3583692 + 3583692 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 3583692 * (2 : ZMod 57339083) ^ 3583692) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 37061717 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 57339083) ^ 14334770 = 3073082 := by
        calc
          (2 : ZMod 57339083) ^ 14334770 = (2 : ZMod 57339083) ^ (7167385 + 7167385) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 7167385 * (2 : ZMod 57339083) ^ 7167385 := by rw [pow_add]
          _ = 3073082 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 57339083) ^ 28669541 = 57339082 := by
        calc
          (2 : ZMod 57339083) ^ 28669541 = (2 : ZMod 57339083) ^ (14334770 + 14334770 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 14334770 * (2 : ZMod 57339083) ^ 14334770) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 57339082 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 57339083) ^ 57339082 = 1 := by
        calc
          (2 : ZMod 57339083) ^ 57339082 = (2 : ZMod 57339083) ^ (28669541 + 28669541) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 28669541 * (2 : ZMod 57339083) ^ 28669541 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (28669541, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (28669541, 1)] : List FactorBlock).map factorBlockValue).prod = 57339083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 57339083) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 57339083) ^ 3 = 8 := by
        calc
          (2 : ZMod 57339083) ^ 3 = (2 : ZMod 57339083) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 1 * (2 : ZMod 57339083) ^ 1) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 57339083) ^ 6 = 64 := by
        calc
          (2 : ZMod 57339083) ^ 6 = (2 : ZMod 57339083) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 3 * (2 : ZMod 57339083) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 57339083) ^ 13 = 8192 := by
        calc
          (2 : ZMod 57339083) ^ 13 = (2 : ZMod 57339083) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 6 * (2 : ZMod 57339083) ^ 6) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 57339083) ^ 27 = 19539562 := by
        calc
          (2 : ZMod 57339083) ^ 27 = (2 : ZMod 57339083) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 13 * (2 : ZMod 57339083) ^ 13) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 19539562 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 57339083) ^ 54 = 20111190 := by
        calc
          (2 : ZMod 57339083) ^ 54 = (2 : ZMod 57339083) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 27 * (2 : ZMod 57339083) ^ 27 := by rw [pow_add]
          _ = 20111190 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 57339083) ^ 109 = 40130001 := by
        calc
          (2 : ZMod 57339083) ^ 109 = (2 : ZMod 57339083) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 54 * (2 : ZMod 57339083) ^ 54) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 40130001 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 57339083) ^ 218 = 38645368 := by
        calc
          (2 : ZMod 57339083) ^ 218 = (2 : ZMod 57339083) ^ (109 + 109) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 109 * (2 : ZMod 57339083) ^ 109 := by rw [pow_add]
          _ = 38645368 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 57339083) ^ 437 = 36596889 := by
        calc
          (2 : ZMod 57339083) ^ 437 = (2 : ZMod 57339083) ^ (218 + 218 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 218 * (2 : ZMod 57339083) ^ 218) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 36596889 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 57339083) ^ 874 = 20499689 := by
        calc
          (2 : ZMod 57339083) ^ 874 = (2 : ZMod 57339083) ^ (437 + 437) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 437 * (2 : ZMod 57339083) ^ 437 := by rw [pow_add]
          _ = 20499689 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 57339083) ^ 1749 = 54430098 := by
        calc
          (2 : ZMod 57339083) ^ 1749 = (2 : ZMod 57339083) ^ (874 + 874 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 874 * (2 : ZMod 57339083) ^ 874) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 54430098 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 57339083) ^ 3499 = 11704921 := by
        calc
          (2 : ZMod 57339083) ^ 3499 = (2 : ZMod 57339083) ^ (1749 + 1749 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 1749 * (2 : ZMod 57339083) ^ 1749) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 11704921 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 57339083) ^ 6999 = 4225489 := by
        calc
          (2 : ZMod 57339083) ^ 6999 = (2 : ZMod 57339083) ^ (3499 + 3499 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 3499 * (2 : ZMod 57339083) ^ 3499) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 4225489 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 57339083) ^ 13998 = 54911917 := by
        calc
          (2 : ZMod 57339083) ^ 13998 = (2 : ZMod 57339083) ^ (6999 + 6999) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 6999 * (2 : ZMod 57339083) ^ 6999 := by rw [pow_add]
          _ = 54911917 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 57339083) ^ 27997 = 5451940 := by
        calc
          (2 : ZMod 57339083) ^ 27997 = (2 : ZMod 57339083) ^ (13998 + 13998 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 13998 * (2 : ZMod 57339083) ^ 13998) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 5451940 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 57339083) ^ 55995 = 30462539 := by
        calc
          (2 : ZMod 57339083) ^ 55995 = (2 : ZMod 57339083) ^ (27997 + 27997 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 27997 * (2 : ZMod 57339083) ^ 27997) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 30462539 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 57339083) ^ 111990 = 24003216 := by
        calc
          (2 : ZMod 57339083) ^ 111990 = (2 : ZMod 57339083) ^ (55995 + 55995) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 55995 * (2 : ZMod 57339083) ^ 55995 := by rw [pow_add]
          _ = 24003216 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 57339083) ^ 223980 = 33898388 := by
        calc
          (2 : ZMod 57339083) ^ 223980 = (2 : ZMod 57339083) ^ (111990 + 111990) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 111990 * (2 : ZMod 57339083) ^ 111990 := by rw [pow_add]
          _ = 33898388 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 57339083) ^ 447961 = 54251384 := by
        calc
          (2 : ZMod 57339083) ^ 447961 = (2 : ZMod 57339083) ^ (223980 + 223980 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 223980 * (2 : ZMod 57339083) ^ 223980) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 54251384 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 57339083) ^ 895923 = 2212050 := by
        calc
          (2 : ZMod 57339083) ^ 895923 = (2 : ZMod 57339083) ^ (447961 + 447961 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 447961 * (2 : ZMod 57339083) ^ 447961) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 2212050 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 57339083) ^ 1791846 = 19876529 := by
        calc
          (2 : ZMod 57339083) ^ 1791846 = (2 : ZMod 57339083) ^ (895923 + 895923) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 895923 * (2 : ZMod 57339083) ^ 895923 := by rw [pow_add]
          _ = 19876529 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 57339083) ^ 3583692 = 31539233 := by
        calc
          (2 : ZMod 57339083) ^ 3583692 = (2 : ZMod 57339083) ^ (1791846 + 1791846) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 1791846 * (2 : ZMod 57339083) ^ 1791846 := by rw [pow_add]
          _ = 31539233 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 57339083) ^ 7167385 = 37061717 := by
        calc
          (2 : ZMod 57339083) ^ 7167385 = (2 : ZMod 57339083) ^ (3583692 + 3583692 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 3583692 * (2 : ZMod 57339083) ^ 3583692) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 37061717 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 57339083) ^ 14334770 = 3073082 := by
        calc
          (2 : ZMod 57339083) ^ 14334770 = (2 : ZMod 57339083) ^ (7167385 + 7167385) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 7167385 * (2 : ZMod 57339083) ^ 7167385 := by rw [pow_add]
          _ = 3073082 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 57339083) ^ 28669541 = 57339082 := by
        calc
          (2 : ZMod 57339083) ^ 28669541 = (2 : ZMod 57339083) ^ (14334770 + 14334770 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = ((2 : ZMod 57339083) ^ 14334770 * (2 : ZMod 57339083) ^ 14334770) * (2 : ZMod 57339083) := by rw [pow_succ, pow_add]
          _ = 57339082 := by rw [factor_0_23]; decide
      change (2 : ZMod 57339083) ^ 28669541 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (2 : ZMod 57339083) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 57339083) ^ 2 = 4 := by
        calc
          (2 : ZMod 57339083) ^ 2 = (2 : ZMod 57339083) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 57339083) ^ n) (by norm_num)
          _ = (2 : ZMod 57339083) ^ 1 * (2 : ZMod 57339083) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      change (2 : ZMod 57339083) ^ 2 ≠ 1
      rw [factor_1_1]
      decide

#print axioms prime_lucas_57339083

end TotientTailPeriodKiller
end Erdos249257
