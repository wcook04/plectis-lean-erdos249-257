import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_231823871 : Nat.Prime 231823871 := by
  apply lucas_primality 231823871 (13 : ZMod 231823871)
  ·
      have fermat_0 : (13 : ZMod 231823871) ^ 1 = 13 := by norm_num
      have fermat_1 : (13 : ZMod 231823871) ^ 3 = 2197 := by
        calc
          (13 : ZMod 231823871) ^ 3 = (13 : ZMod 231823871) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 1 * (13 : ZMod 231823871) ^ 1) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [fermat_0]; decide
      have fermat_2 : (13 : ZMod 231823871) ^ 6 = 4826809 := by
        calc
          (13 : ZMod 231823871) ^ 6 = (13 : ZMod 231823871) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 3 * (13 : ZMod 231823871) ^ 3 := by rw [pow_add]
          _ = 4826809 := by rw [fermat_1]; decide
      have fermat_3 : (13 : ZMod 231823871) ^ 13 = 1017205 := by
        calc
          (13 : ZMod 231823871) ^ 13 = (13 : ZMod 231823871) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 6 * (13 : ZMod 231823871) ^ 6) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 1017205 := by rw [fermat_2]; decide
      have fermat_4 : (13 : ZMod 231823871) ^ 27 = 61689292 := by
        calc
          (13 : ZMod 231823871) ^ 27 = (13 : ZMod 231823871) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 13 * (13 : ZMod 231823871) ^ 13) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 61689292 := by rw [fermat_3]; decide
      have fermat_5 : (13 : ZMod 231823871) ^ 55 = 125740784 := by
        calc
          (13 : ZMod 231823871) ^ 55 = (13 : ZMod 231823871) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 27 * (13 : ZMod 231823871) ^ 27) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 125740784 := by rw [fermat_4]; decide
      have fermat_6 : (13 : ZMod 231823871) ^ 110 = 213621058 := by
        calc
          (13 : ZMod 231823871) ^ 110 = (13 : ZMod 231823871) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 55 * (13 : ZMod 231823871) ^ 55 := by rw [pow_add]
          _ = 213621058 := by rw [fermat_5]; decide
      have fermat_7 : (13 : ZMod 231823871) ^ 221 = 23635671 := by
        calc
          (13 : ZMod 231823871) ^ 221 = (13 : ZMod 231823871) ^ (110 + 110 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 110 * (13 : ZMod 231823871) ^ 110) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 23635671 := by rw [fermat_6]; decide
      have fermat_8 : (13 : ZMod 231823871) ^ 442 = 183937990 := by
        calc
          (13 : ZMod 231823871) ^ 442 = (13 : ZMod 231823871) ^ (221 + 221) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 221 * (13 : ZMod 231823871) ^ 221 := by rw [pow_add]
          _ = 183937990 := by rw [fermat_7]; decide
      have fermat_9 : (13 : ZMod 231823871) ^ 884 = 61661923 := by
        calc
          (13 : ZMod 231823871) ^ 884 = (13 : ZMod 231823871) ^ (442 + 442) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 442 * (13 : ZMod 231823871) ^ 442 := by rw [pow_add]
          _ = 61661923 := by rw [fermat_8]; decide
      have fermat_10 : (13 : ZMod 231823871) ^ 1768 = 61302406 := by
        calc
          (13 : ZMod 231823871) ^ 1768 = (13 : ZMod 231823871) ^ (884 + 884) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 884 * (13 : ZMod 231823871) ^ 884 := by rw [pow_add]
          _ = 61302406 := by rw [fermat_9]; decide
      have fermat_11 : (13 : ZMod 231823871) ^ 3537 = 15749167 := by
        calc
          (13 : ZMod 231823871) ^ 3537 = (13 : ZMod 231823871) ^ (1768 + 1768 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 1768 * (13 : ZMod 231823871) ^ 1768) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 15749167 := by rw [fermat_10]; decide
      have fermat_12 : (13 : ZMod 231823871) ^ 7074 = 19599375 := by
        calc
          (13 : ZMod 231823871) ^ 7074 = (13 : ZMod 231823871) ^ (3537 + 3537) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 3537 * (13 : ZMod 231823871) ^ 3537 := by rw [pow_add]
          _ = 19599375 := by rw [fermat_11]; decide
      have fermat_13 : (13 : ZMod 231823871) ^ 14149 = 148803248 := by
        calc
          (13 : ZMod 231823871) ^ 14149 = (13 : ZMod 231823871) ^ (7074 + 7074 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 7074 * (13 : ZMod 231823871) ^ 7074) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 148803248 := by rw [fermat_12]; decide
      have fermat_14 : (13 : ZMod 231823871) ^ 28298 = 178389055 := by
        calc
          (13 : ZMod 231823871) ^ 28298 = (13 : ZMod 231823871) ^ (14149 + 14149) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 14149 * (13 : ZMod 231823871) ^ 14149 := by rw [pow_add]
          _ = 178389055 := by rw [fermat_13]; decide
      have fermat_15 : (13 : ZMod 231823871) ^ 56597 = 97065429 := by
        calc
          (13 : ZMod 231823871) ^ 56597 = (13 : ZMod 231823871) ^ (28298 + 28298 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 28298 * (13 : ZMod 231823871) ^ 28298) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 97065429 := by rw [fermat_14]; decide
      have fermat_16 : (13 : ZMod 231823871) ^ 113195 = 171197983 := by
        calc
          (13 : ZMod 231823871) ^ 113195 = (13 : ZMod 231823871) ^ (56597 + 56597 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 56597 * (13 : ZMod 231823871) ^ 56597) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 171197983 := by rw [fermat_15]; decide
      have fermat_17 : (13 : ZMod 231823871) ^ 226390 = 136420973 := by
        calc
          (13 : ZMod 231823871) ^ 226390 = (13 : ZMod 231823871) ^ (113195 + 113195) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 113195 * (13 : ZMod 231823871) ^ 113195 := by rw [pow_add]
          _ = 136420973 := by rw [fermat_16]; decide
      have fermat_18 : (13 : ZMod 231823871) ^ 452780 = 141061587 := by
        calc
          (13 : ZMod 231823871) ^ 452780 = (13 : ZMod 231823871) ^ (226390 + 226390) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 226390 * (13 : ZMod 231823871) ^ 226390 := by rw [pow_add]
          _ = 141061587 := by rw [fermat_17]; decide
      have fermat_19 : (13 : ZMod 231823871) ^ 905561 = 85703911 := by
        calc
          (13 : ZMod 231823871) ^ 905561 = (13 : ZMod 231823871) ^ (452780 + 452780 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 452780 * (13 : ZMod 231823871) ^ 452780) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 85703911 := by rw [fermat_18]; decide
      have fermat_20 : (13 : ZMod 231823871) ^ 1811123 = 152809071 := by
        calc
          (13 : ZMod 231823871) ^ 1811123 = (13 : ZMod 231823871) ^ (905561 + 905561 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 905561 * (13 : ZMod 231823871) ^ 905561) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 152809071 := by rw [fermat_19]; decide
      have fermat_21 : (13 : ZMod 231823871) ^ 3622247 = 19201676 := by
        calc
          (13 : ZMod 231823871) ^ 3622247 = (13 : ZMod 231823871) ^ (1811123 + 1811123 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 1811123 * (13 : ZMod 231823871) ^ 1811123) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 19201676 := by rw [fermat_20]; decide
      have fermat_22 : (13 : ZMod 231823871) ^ 7244495 = 185205854 := by
        calc
          (13 : ZMod 231823871) ^ 7244495 = (13 : ZMod 231823871) ^ (3622247 + 3622247 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 3622247 * (13 : ZMod 231823871) ^ 3622247) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 185205854 := by rw [fermat_21]; decide
      have fermat_23 : (13 : ZMod 231823871) ^ 14488991 = 187540116 := by
        calc
          (13 : ZMod 231823871) ^ 14488991 = (13 : ZMod 231823871) ^ (7244495 + 7244495 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 7244495 * (13 : ZMod 231823871) ^ 7244495) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 187540116 := by rw [fermat_22]; decide
      have fermat_24 : (13 : ZMod 231823871) ^ 28977983 = 155137423 := by
        calc
          (13 : ZMod 231823871) ^ 28977983 = (13 : ZMod 231823871) ^ (14488991 + 14488991 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 14488991 * (13 : ZMod 231823871) ^ 14488991) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 155137423 := by rw [fermat_23]; decide
      have fermat_25 : (13 : ZMod 231823871) ^ 57955967 = 653972 := by
        calc
          (13 : ZMod 231823871) ^ 57955967 = (13 : ZMod 231823871) ^ (28977983 + 28977983 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 28977983 * (13 : ZMod 231823871) ^ 28977983) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 653972 := by rw [fermat_24]; decide
      have fermat_26 : (13 : ZMod 231823871) ^ 115911935 = 231823870 := by
        calc
          (13 : ZMod 231823871) ^ 115911935 = (13 : ZMod 231823871) ^ (57955967 + 57955967 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 57955967 * (13 : ZMod 231823871) ^ 57955967) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 231823870 := by rw [fermat_25]; decide
      have fermat_27 : (13 : ZMod 231823871) ^ 231823870 = 1 := by
        calc
          (13 : ZMod 231823871) ^ 231823870 = (13 : ZMod 231823871) ^ (115911935 + 115911935) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 115911935 * (13 : ZMod 231823871) ^ 115911935 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (37, 1), (433, 1), (1447, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (37, 1), (433, 1), (1447, 1)] : List FactorBlock).map factorBlockValue).prod = 231823871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (13 : ZMod 231823871) ^ 1 = 13 := by norm_num
      have factor_0_1 : (13 : ZMod 231823871) ^ 3 = 2197 := by
        calc
          (13 : ZMod 231823871) ^ 3 = (13 : ZMod 231823871) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 1 * (13 : ZMod 231823871) ^ 1) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_0_0]; decide
      have factor_0_2 : (13 : ZMod 231823871) ^ 6 = 4826809 := by
        calc
          (13 : ZMod 231823871) ^ 6 = (13 : ZMod 231823871) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 3 * (13 : ZMod 231823871) ^ 3 := by rw [pow_add]
          _ = 4826809 := by rw [factor_0_1]; decide
      have factor_0_3 : (13 : ZMod 231823871) ^ 13 = 1017205 := by
        calc
          (13 : ZMod 231823871) ^ 13 = (13 : ZMod 231823871) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 6 * (13 : ZMod 231823871) ^ 6) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 1017205 := by rw [factor_0_2]; decide
      have factor_0_4 : (13 : ZMod 231823871) ^ 27 = 61689292 := by
        calc
          (13 : ZMod 231823871) ^ 27 = (13 : ZMod 231823871) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 13 * (13 : ZMod 231823871) ^ 13) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 61689292 := by rw [factor_0_3]; decide
      have factor_0_5 : (13 : ZMod 231823871) ^ 55 = 125740784 := by
        calc
          (13 : ZMod 231823871) ^ 55 = (13 : ZMod 231823871) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 27 * (13 : ZMod 231823871) ^ 27) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 125740784 := by rw [factor_0_4]; decide
      have factor_0_6 : (13 : ZMod 231823871) ^ 110 = 213621058 := by
        calc
          (13 : ZMod 231823871) ^ 110 = (13 : ZMod 231823871) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 55 * (13 : ZMod 231823871) ^ 55 := by rw [pow_add]
          _ = 213621058 := by rw [factor_0_5]; decide
      have factor_0_7 : (13 : ZMod 231823871) ^ 221 = 23635671 := by
        calc
          (13 : ZMod 231823871) ^ 221 = (13 : ZMod 231823871) ^ (110 + 110 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 110 * (13 : ZMod 231823871) ^ 110) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 23635671 := by rw [factor_0_6]; decide
      have factor_0_8 : (13 : ZMod 231823871) ^ 442 = 183937990 := by
        calc
          (13 : ZMod 231823871) ^ 442 = (13 : ZMod 231823871) ^ (221 + 221) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 221 * (13 : ZMod 231823871) ^ 221 := by rw [pow_add]
          _ = 183937990 := by rw [factor_0_7]; decide
      have factor_0_9 : (13 : ZMod 231823871) ^ 884 = 61661923 := by
        calc
          (13 : ZMod 231823871) ^ 884 = (13 : ZMod 231823871) ^ (442 + 442) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 442 * (13 : ZMod 231823871) ^ 442 := by rw [pow_add]
          _ = 61661923 := by rw [factor_0_8]; decide
      have factor_0_10 : (13 : ZMod 231823871) ^ 1768 = 61302406 := by
        calc
          (13 : ZMod 231823871) ^ 1768 = (13 : ZMod 231823871) ^ (884 + 884) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 884 * (13 : ZMod 231823871) ^ 884 := by rw [pow_add]
          _ = 61302406 := by rw [factor_0_9]; decide
      have factor_0_11 : (13 : ZMod 231823871) ^ 3537 = 15749167 := by
        calc
          (13 : ZMod 231823871) ^ 3537 = (13 : ZMod 231823871) ^ (1768 + 1768 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 1768 * (13 : ZMod 231823871) ^ 1768) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 15749167 := by rw [factor_0_10]; decide
      have factor_0_12 : (13 : ZMod 231823871) ^ 7074 = 19599375 := by
        calc
          (13 : ZMod 231823871) ^ 7074 = (13 : ZMod 231823871) ^ (3537 + 3537) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 3537 * (13 : ZMod 231823871) ^ 3537 := by rw [pow_add]
          _ = 19599375 := by rw [factor_0_11]; decide
      have factor_0_13 : (13 : ZMod 231823871) ^ 14149 = 148803248 := by
        calc
          (13 : ZMod 231823871) ^ 14149 = (13 : ZMod 231823871) ^ (7074 + 7074 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 7074 * (13 : ZMod 231823871) ^ 7074) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 148803248 := by rw [factor_0_12]; decide
      have factor_0_14 : (13 : ZMod 231823871) ^ 28298 = 178389055 := by
        calc
          (13 : ZMod 231823871) ^ 28298 = (13 : ZMod 231823871) ^ (14149 + 14149) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 14149 * (13 : ZMod 231823871) ^ 14149 := by rw [pow_add]
          _ = 178389055 := by rw [factor_0_13]; decide
      have factor_0_15 : (13 : ZMod 231823871) ^ 56597 = 97065429 := by
        calc
          (13 : ZMod 231823871) ^ 56597 = (13 : ZMod 231823871) ^ (28298 + 28298 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 28298 * (13 : ZMod 231823871) ^ 28298) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 97065429 := by rw [factor_0_14]; decide
      have factor_0_16 : (13 : ZMod 231823871) ^ 113195 = 171197983 := by
        calc
          (13 : ZMod 231823871) ^ 113195 = (13 : ZMod 231823871) ^ (56597 + 56597 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 56597 * (13 : ZMod 231823871) ^ 56597) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 171197983 := by rw [factor_0_15]; decide
      have factor_0_17 : (13 : ZMod 231823871) ^ 226390 = 136420973 := by
        calc
          (13 : ZMod 231823871) ^ 226390 = (13 : ZMod 231823871) ^ (113195 + 113195) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 113195 * (13 : ZMod 231823871) ^ 113195 := by rw [pow_add]
          _ = 136420973 := by rw [factor_0_16]; decide
      have factor_0_18 : (13 : ZMod 231823871) ^ 452780 = 141061587 := by
        calc
          (13 : ZMod 231823871) ^ 452780 = (13 : ZMod 231823871) ^ (226390 + 226390) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 226390 * (13 : ZMod 231823871) ^ 226390 := by rw [pow_add]
          _ = 141061587 := by rw [factor_0_17]; decide
      have factor_0_19 : (13 : ZMod 231823871) ^ 905561 = 85703911 := by
        calc
          (13 : ZMod 231823871) ^ 905561 = (13 : ZMod 231823871) ^ (452780 + 452780 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 452780 * (13 : ZMod 231823871) ^ 452780) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 85703911 := by rw [factor_0_18]; decide
      have factor_0_20 : (13 : ZMod 231823871) ^ 1811123 = 152809071 := by
        calc
          (13 : ZMod 231823871) ^ 1811123 = (13 : ZMod 231823871) ^ (905561 + 905561 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 905561 * (13 : ZMod 231823871) ^ 905561) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 152809071 := by rw [factor_0_19]; decide
      have factor_0_21 : (13 : ZMod 231823871) ^ 3622247 = 19201676 := by
        calc
          (13 : ZMod 231823871) ^ 3622247 = (13 : ZMod 231823871) ^ (1811123 + 1811123 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 1811123 * (13 : ZMod 231823871) ^ 1811123) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 19201676 := by rw [factor_0_20]; decide
      have factor_0_22 : (13 : ZMod 231823871) ^ 7244495 = 185205854 := by
        calc
          (13 : ZMod 231823871) ^ 7244495 = (13 : ZMod 231823871) ^ (3622247 + 3622247 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 3622247 * (13 : ZMod 231823871) ^ 3622247) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 185205854 := by rw [factor_0_21]; decide
      have factor_0_23 : (13 : ZMod 231823871) ^ 14488991 = 187540116 := by
        calc
          (13 : ZMod 231823871) ^ 14488991 = (13 : ZMod 231823871) ^ (7244495 + 7244495 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 7244495 * (13 : ZMod 231823871) ^ 7244495) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 187540116 := by rw [factor_0_22]; decide
      have factor_0_24 : (13 : ZMod 231823871) ^ 28977983 = 155137423 := by
        calc
          (13 : ZMod 231823871) ^ 28977983 = (13 : ZMod 231823871) ^ (14488991 + 14488991 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 14488991 * (13 : ZMod 231823871) ^ 14488991) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 155137423 := by rw [factor_0_23]; decide
      have factor_0_25 : (13 : ZMod 231823871) ^ 57955967 = 653972 := by
        calc
          (13 : ZMod 231823871) ^ 57955967 = (13 : ZMod 231823871) ^ (28977983 + 28977983 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 28977983 * (13 : ZMod 231823871) ^ 28977983) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 653972 := by rw [factor_0_24]; decide
      have factor_0_26 : (13 : ZMod 231823871) ^ 115911935 = 231823870 := by
        calc
          (13 : ZMod 231823871) ^ 115911935 = (13 : ZMod 231823871) ^ (57955967 + 57955967 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 57955967 * (13 : ZMod 231823871) ^ 57955967) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 231823870 := by rw [factor_0_25]; decide
      change (13 : ZMod 231823871) ^ 115911935 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (13 : ZMod 231823871) ^ 1 = 13 := by norm_num
      have factor_1_1 : (13 : ZMod 231823871) ^ 2 = 169 := by
        calc
          (13 : ZMod 231823871) ^ 2 = (13 : ZMod 231823871) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 1 * (13 : ZMod 231823871) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_1_0]; decide
      have factor_1_2 : (13 : ZMod 231823871) ^ 5 = 371293 := by
        calc
          (13 : ZMod 231823871) ^ 5 = (13 : ZMod 231823871) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 2 * (13 : ZMod 231823871) ^ 2) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 371293 := by rw [factor_1_1]; decide
      have factor_1_3 : (13 : ZMod 231823871) ^ 11 = 161871207 := by
        calc
          (13 : ZMod 231823871) ^ 11 = (13 : ZMod 231823871) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 5 * (13 : ZMod 231823871) ^ 5) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 161871207 := by rw [factor_1_2]; decide
      have factor_1_4 : (13 : ZMod 231823871) ^ 22 = 71633407 := by
        calc
          (13 : ZMod 231823871) ^ 22 = (13 : ZMod 231823871) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 11 * (13 : ZMod 231823871) ^ 11 := by rw [pow_add]
          _ = 71633407 := by rw [factor_1_3]; decide
      have factor_1_5 : (13 : ZMod 231823871) ^ 44 = 115720079 := by
        calc
          (13 : ZMod 231823871) ^ 44 = (13 : ZMod 231823871) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 22 * (13 : ZMod 231823871) ^ 22 := by rw [pow_add]
          _ = 115720079 := by rw [factor_1_4]; decide
      have factor_1_6 : (13 : ZMod 231823871) ^ 88 = 6877071 := by
        calc
          (13 : ZMod 231823871) ^ 88 = (13 : ZMod 231823871) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 44 * (13 : ZMod 231823871) ^ 44 := by rw [pow_add]
          _ = 6877071 := by rw [factor_1_5]; decide
      have factor_1_7 : (13 : ZMod 231823871) ^ 176 = 181264073 := by
        calc
          (13 : ZMod 231823871) ^ 176 = (13 : ZMod 231823871) ^ (88 + 88) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 88 * (13 : ZMod 231823871) ^ 88 := by rw [pow_add]
          _ = 181264073 := by rw [factor_1_6]; decide
      have factor_1_8 : (13 : ZMod 231823871) ^ 353 = 68650149 := by
        calc
          (13 : ZMod 231823871) ^ 353 = (13 : ZMod 231823871) ^ (176 + 176 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 176 * (13 : ZMod 231823871) ^ 176) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 68650149 := by rw [factor_1_7]; decide
      have factor_1_9 : (13 : ZMod 231823871) ^ 707 = 109116279 := by
        calc
          (13 : ZMod 231823871) ^ 707 = (13 : ZMod 231823871) ^ (353 + 353 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 353 * (13 : ZMod 231823871) ^ 353) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 109116279 := by rw [factor_1_8]; decide
      have factor_1_10 : (13 : ZMod 231823871) ^ 1414 = 67351663 := by
        calc
          (13 : ZMod 231823871) ^ 1414 = (13 : ZMod 231823871) ^ (707 + 707) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 707 * (13 : ZMod 231823871) ^ 707 := by rw [pow_add]
          _ = 67351663 := by rw [factor_1_9]; decide
      have factor_1_11 : (13 : ZMod 231823871) ^ 2829 = 154907902 := by
        calc
          (13 : ZMod 231823871) ^ 2829 = (13 : ZMod 231823871) ^ (1414 + 1414 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 1414 * (13 : ZMod 231823871) ^ 1414) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 154907902 := by rw [factor_1_10]; decide
      have factor_1_12 : (13 : ZMod 231823871) ^ 5659 = 111385668 := by
        calc
          (13 : ZMod 231823871) ^ 5659 = (13 : ZMod 231823871) ^ (2829 + 2829 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 2829 * (13 : ZMod 231823871) ^ 2829) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 111385668 := by rw [factor_1_11]; decide
      have factor_1_13 : (13 : ZMod 231823871) ^ 11319 = 80074623 := by
        calc
          (13 : ZMod 231823871) ^ 11319 = (13 : ZMod 231823871) ^ (5659 + 5659 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 5659 * (13 : ZMod 231823871) ^ 5659) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 80074623 := by rw [factor_1_12]; decide
      have factor_1_14 : (13 : ZMod 231823871) ^ 22639 = 80557580 := by
        calc
          (13 : ZMod 231823871) ^ 22639 = (13 : ZMod 231823871) ^ (11319 + 11319 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 11319 * (13 : ZMod 231823871) ^ 11319) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 80557580 := by rw [factor_1_13]; decide
      have factor_1_15 : (13 : ZMod 231823871) ^ 45278 = 181732744 := by
        calc
          (13 : ZMod 231823871) ^ 45278 = (13 : ZMod 231823871) ^ (22639 + 22639) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 22639 * (13 : ZMod 231823871) ^ 22639 := by rw [pow_add]
          _ = 181732744 := by rw [factor_1_14]; decide
      have factor_1_16 : (13 : ZMod 231823871) ^ 90556 = 141515826 := by
        calc
          (13 : ZMod 231823871) ^ 90556 = (13 : ZMod 231823871) ^ (45278 + 45278) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 45278 * (13 : ZMod 231823871) ^ 45278 := by rw [pow_add]
          _ = 141515826 := by rw [factor_1_15]; decide
      have factor_1_17 : (13 : ZMod 231823871) ^ 181112 = 74090415 := by
        calc
          (13 : ZMod 231823871) ^ 181112 = (13 : ZMod 231823871) ^ (90556 + 90556) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 90556 * (13 : ZMod 231823871) ^ 90556 := by rw [pow_add]
          _ = 74090415 := by rw [factor_1_16]; decide
      have factor_1_18 : (13 : ZMod 231823871) ^ 362224 = 161769027 := by
        calc
          (13 : ZMod 231823871) ^ 362224 = (13 : ZMod 231823871) ^ (181112 + 181112) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 181112 * (13 : ZMod 231823871) ^ 181112 := by rw [pow_add]
          _ = 161769027 := by rw [factor_1_17]; decide
      have factor_1_19 : (13 : ZMod 231823871) ^ 724449 = 122139971 := by
        calc
          (13 : ZMod 231823871) ^ 724449 = (13 : ZMod 231823871) ^ (362224 + 362224 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 362224 * (13 : ZMod 231823871) ^ 362224) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 122139971 := by rw [factor_1_18]; decide
      have factor_1_20 : (13 : ZMod 231823871) ^ 1448899 = 223649411 := by
        calc
          (13 : ZMod 231823871) ^ 1448899 = (13 : ZMod 231823871) ^ (724449 + 724449 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 724449 * (13 : ZMod 231823871) ^ 724449) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 223649411 := by rw [factor_1_19]; decide
      have factor_1_21 : (13 : ZMod 231823871) ^ 2897798 = 188242947 := by
        calc
          (13 : ZMod 231823871) ^ 2897798 = (13 : ZMod 231823871) ^ (1448899 + 1448899) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 1448899 * (13 : ZMod 231823871) ^ 1448899 := by rw [pow_add]
          _ = 188242947 := by rw [factor_1_20]; decide
      have factor_1_22 : (13 : ZMod 231823871) ^ 5795596 = 126114652 := by
        calc
          (13 : ZMod 231823871) ^ 5795596 = (13 : ZMod 231823871) ^ (2897798 + 2897798) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 2897798 * (13 : ZMod 231823871) ^ 2897798 := by rw [pow_add]
          _ = 126114652 := by rw [factor_1_21]; decide
      have factor_1_23 : (13 : ZMod 231823871) ^ 11591193 = 18947892 := by
        calc
          (13 : ZMod 231823871) ^ 11591193 = (13 : ZMod 231823871) ^ (5795596 + 5795596 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 5795596 * (13 : ZMod 231823871) ^ 5795596) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 18947892 := by rw [factor_1_22]; decide
      have factor_1_24 : (13 : ZMod 231823871) ^ 23182387 = 178995602 := by
        calc
          (13 : ZMod 231823871) ^ 23182387 = (13 : ZMod 231823871) ^ (11591193 + 11591193 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 11591193 * (13 : ZMod 231823871) ^ 11591193) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 178995602 := by rw [factor_1_23]; decide
      have factor_1_25 : (13 : ZMod 231823871) ^ 46364774 = 193246730 := by
        calc
          (13 : ZMod 231823871) ^ 46364774 = (13 : ZMod 231823871) ^ (23182387 + 23182387) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 23182387 * (13 : ZMod 231823871) ^ 23182387 := by rw [pow_add]
          _ = 193246730 := by rw [factor_1_24]; decide
      change (13 : ZMod 231823871) ^ 46364774 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (13 : ZMod 231823871) ^ 1 = 13 := by norm_num
      have factor_2_1 : (13 : ZMod 231823871) ^ 2 = 169 := by
        calc
          (13 : ZMod 231823871) ^ 2 = (13 : ZMod 231823871) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 1 * (13 : ZMod 231823871) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_2_0]; decide
      have factor_2_2 : (13 : ZMod 231823871) ^ 5 = 371293 := by
        calc
          (13 : ZMod 231823871) ^ 5 = (13 : ZMod 231823871) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 2 * (13 : ZMod 231823871) ^ 2) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 371293 := by rw [factor_2_1]; decide
      have factor_2_3 : (13 : ZMod 231823871) ^ 11 = 161871207 := by
        calc
          (13 : ZMod 231823871) ^ 11 = (13 : ZMod 231823871) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 5 * (13 : ZMod 231823871) ^ 5) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 161871207 := by rw [factor_2_2]; decide
      have factor_2_4 : (13 : ZMod 231823871) ^ 23 = 3938807 := by
        calc
          (13 : ZMod 231823871) ^ 23 = (13 : ZMod 231823871) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 11 * (13 : ZMod 231823871) ^ 11) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 3938807 := by rw [factor_2_3]; decide
      have factor_2_5 : (13 : ZMod 231823871) ^ 47 = 158050947 := by
        calc
          (13 : ZMod 231823871) ^ 47 = (13 : ZMod 231823871) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 23 * (13 : ZMod 231823871) ^ 23) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 158050947 := by rw [factor_2_4]; decide
      have factor_2_6 : (13 : ZMod 231823871) ^ 95 = 11943338 := by
        calc
          (13 : ZMod 231823871) ^ 95 = (13 : ZMod 231823871) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 47 * (13 : ZMod 231823871) ^ 47) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 11943338 := by rw [factor_2_5]; decide
      have factor_2_7 : (13 : ZMod 231823871) ^ 191 = 108434365 := by
        calc
          (13 : ZMod 231823871) ^ 191 = (13 : ZMod 231823871) ^ (95 + 95 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 95 * (13 : ZMod 231823871) ^ 95) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 108434365 := by rw [factor_2_6]; decide
      have factor_2_8 : (13 : ZMod 231823871) ^ 382 = 55444206 := by
        calc
          (13 : ZMod 231823871) ^ 382 = (13 : ZMod 231823871) ^ (191 + 191) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 191 * (13 : ZMod 231823871) ^ 191 := by rw [pow_add]
          _ = 55444206 := by rw [factor_2_7]; decide
      have factor_2_9 : (13 : ZMod 231823871) ^ 764 = 106752361 := by
        calc
          (13 : ZMod 231823871) ^ 764 = (13 : ZMod 231823871) ^ (382 + 382) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 382 * (13 : ZMod 231823871) ^ 382 := by rw [pow_add]
          _ = 106752361 := by rw [factor_2_8]; decide
      have factor_2_10 : (13 : ZMod 231823871) ^ 1529 = 20733339 := by
        calc
          (13 : ZMod 231823871) ^ 1529 = (13 : ZMod 231823871) ^ (764 + 764 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 764 * (13 : ZMod 231823871) ^ 764) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 20733339 := by rw [factor_2_9]; decide
      have factor_2_11 : (13 : ZMod 231823871) ^ 3059 = 42563524 := by
        calc
          (13 : ZMod 231823871) ^ 3059 = (13 : ZMod 231823871) ^ (1529 + 1529 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 1529 * (13 : ZMod 231823871) ^ 1529) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 42563524 := by rw [factor_2_10]; decide
      have factor_2_12 : (13 : ZMod 231823871) ^ 6118 = 97389712 := by
        calc
          (13 : ZMod 231823871) ^ 6118 = (13 : ZMod 231823871) ^ (3059 + 3059) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 3059 * (13 : ZMod 231823871) ^ 3059 := by rw [pow_add]
          _ = 97389712 := by rw [factor_2_11]; decide
      have factor_2_13 : (13 : ZMod 231823871) ^ 12237 = 121475137 := by
        calc
          (13 : ZMod 231823871) ^ 12237 = (13 : ZMod 231823871) ^ (6118 + 6118 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 6118 * (13 : ZMod 231823871) ^ 6118) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 121475137 := by rw [factor_2_12]; decide
      have factor_2_14 : (13 : ZMod 231823871) ^ 24474 = 86635457 := by
        calc
          (13 : ZMod 231823871) ^ 24474 = (13 : ZMod 231823871) ^ (12237 + 12237) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 12237 * (13 : ZMod 231823871) ^ 12237 := by rw [pow_add]
          _ = 86635457 := by rw [factor_2_13]; decide
      have factor_2_15 : (13 : ZMod 231823871) ^ 48949 = 229498660 := by
        calc
          (13 : ZMod 231823871) ^ 48949 = (13 : ZMod 231823871) ^ (24474 + 24474 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 24474 * (13 : ZMod 231823871) ^ 24474) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 229498660 := by rw [factor_2_14]; decide
      have factor_2_16 : (13 : ZMod 231823871) ^ 97898 = 9875059 := by
        calc
          (13 : ZMod 231823871) ^ 97898 = (13 : ZMod 231823871) ^ (48949 + 48949) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 48949 * (13 : ZMod 231823871) ^ 48949 := by rw [pow_add]
          _ = 9875059 := by rw [factor_2_15]; decide
      have factor_2_17 : (13 : ZMod 231823871) ^ 195797 = 98629819 := by
        calc
          (13 : ZMod 231823871) ^ 195797 = (13 : ZMod 231823871) ^ (97898 + 97898 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 97898 * (13 : ZMod 231823871) ^ 97898) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 98629819 := by rw [factor_2_16]; decide
      have factor_2_18 : (13 : ZMod 231823871) ^ 391594 = 165353335 := by
        calc
          (13 : ZMod 231823871) ^ 391594 = (13 : ZMod 231823871) ^ (195797 + 195797) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 195797 * (13 : ZMod 231823871) ^ 195797 := by rw [pow_add]
          _ = 165353335 := by rw [factor_2_17]; decide
      have factor_2_19 : (13 : ZMod 231823871) ^ 783188 = 71442812 := by
        calc
          (13 : ZMod 231823871) ^ 783188 = (13 : ZMod 231823871) ^ (391594 + 391594) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 391594 * (13 : ZMod 231823871) ^ 391594 := by rw [pow_add]
          _ = 71442812 := by rw [factor_2_18]; decide
      have factor_2_20 : (13 : ZMod 231823871) ^ 1566377 = 221467036 := by
        calc
          (13 : ZMod 231823871) ^ 1566377 = (13 : ZMod 231823871) ^ (783188 + 783188 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 783188 * (13 : ZMod 231823871) ^ 783188) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 221467036 := by rw [factor_2_19]; decide
      have factor_2_21 : (13 : ZMod 231823871) ^ 3132755 = 230565375 := by
        calc
          (13 : ZMod 231823871) ^ 3132755 = (13 : ZMod 231823871) ^ (1566377 + 1566377 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 1566377 * (13 : ZMod 231823871) ^ 1566377) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 230565375 := by rw [factor_2_20]; decide
      have factor_2_22 : (13 : ZMod 231823871) ^ 6265510 = 223319215 := by
        calc
          (13 : ZMod 231823871) ^ 6265510 = (13 : ZMod 231823871) ^ (3132755 + 3132755) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 3132755 * (13 : ZMod 231823871) ^ 3132755 := by rw [pow_add]
          _ = 223319215 := by rw [factor_2_21]; decide
      change (13 : ZMod 231823871) ^ 6265510 ≠ 1
      rw [factor_2_22]
      decide
    ·
      have factor_3_0 : (13 : ZMod 231823871) ^ 1 = 13 := by norm_num
      have factor_3_1 : (13 : ZMod 231823871) ^ 2 = 169 := by
        calc
          (13 : ZMod 231823871) ^ 2 = (13 : ZMod 231823871) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 1 * (13 : ZMod 231823871) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_3_0]; decide
      have factor_3_2 : (13 : ZMod 231823871) ^ 4 = 28561 := by
        calc
          (13 : ZMod 231823871) ^ 4 = (13 : ZMod 231823871) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 2 * (13 : ZMod 231823871) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_3_1]; decide
      have factor_3_3 : (13 : ZMod 231823871) ^ 8 = 120259108 := by
        calc
          (13 : ZMod 231823871) ^ 8 = (13 : ZMod 231823871) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 4 * (13 : ZMod 231823871) ^ 4 := by rw [pow_add]
          _ = 120259108 := by rw [factor_3_2]; decide
      have factor_3_4 : (13 : ZMod 231823871) ^ 16 = 148384546 := by
        calc
          (13 : ZMod 231823871) ^ 16 = (13 : ZMod 231823871) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 8 * (13 : ZMod 231823871) ^ 8 := by rw [pow_add]
          _ = 148384546 := by rw [factor_3_3]; decide
      have factor_3_5 : (13 : ZMod 231823871) ^ 32 = 140192014 := by
        calc
          (13 : ZMod 231823871) ^ 32 = (13 : ZMod 231823871) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 16 * (13 : ZMod 231823871) ^ 16 := by rw [pow_add]
          _ = 140192014 := by rw [factor_3_4]; decide
      have factor_3_6 : (13 : ZMod 231823871) ^ 65 = 195828378 := by
        calc
          (13 : ZMod 231823871) ^ 65 = (13 : ZMod 231823871) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 32 * (13 : ZMod 231823871) ^ 32) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 195828378 := by rw [factor_3_5]; decide
      have factor_3_7 : (13 : ZMod 231823871) ^ 130 = 78276628 := by
        calc
          (13 : ZMod 231823871) ^ 130 = (13 : ZMod 231823871) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 65 * (13 : ZMod 231823871) ^ 65 := by rw [pow_add]
          _ = 78276628 := by rw [factor_3_6]; decide
      have factor_3_8 : (13 : ZMod 231823871) ^ 261 = 43065410 := by
        calc
          (13 : ZMod 231823871) ^ 261 = (13 : ZMod 231823871) ^ (130 + 130 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 130 * (13 : ZMod 231823871) ^ 130) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 43065410 := by rw [factor_3_7]; decide
      have factor_3_9 : (13 : ZMod 231823871) ^ 522 = 87705514 := by
        calc
          (13 : ZMod 231823871) ^ 522 = (13 : ZMod 231823871) ^ (261 + 261) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 261 * (13 : ZMod 231823871) ^ 261 := by rw [pow_add]
          _ = 87705514 := by rw [factor_3_8]; decide
      have factor_3_10 : (13 : ZMod 231823871) ^ 1045 = 110262318 := by
        calc
          (13 : ZMod 231823871) ^ 1045 = (13 : ZMod 231823871) ^ (522 + 522 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 522 * (13 : ZMod 231823871) ^ 522) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 110262318 := by rw [factor_3_9]; decide
      have factor_3_11 : (13 : ZMod 231823871) ^ 2091 = 155854082 := by
        calc
          (13 : ZMod 231823871) ^ 2091 = (13 : ZMod 231823871) ^ (1045 + 1045 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 1045 * (13 : ZMod 231823871) ^ 1045) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 155854082 := by rw [factor_3_10]; decide
      have factor_3_12 : (13 : ZMod 231823871) ^ 4182 = 104756919 := by
        calc
          (13 : ZMod 231823871) ^ 4182 = (13 : ZMod 231823871) ^ (2091 + 2091) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 2091 * (13 : ZMod 231823871) ^ 2091 := by rw [pow_add]
          _ = 104756919 := by rw [factor_3_11]; decide
      have factor_3_13 : (13 : ZMod 231823871) ^ 8365 = 133469413 := by
        calc
          (13 : ZMod 231823871) ^ 8365 = (13 : ZMod 231823871) ^ (4182 + 4182 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 4182 * (13 : ZMod 231823871) ^ 4182) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 133469413 := by rw [factor_3_12]; decide
      have factor_3_14 : (13 : ZMod 231823871) ^ 16730 = 63543176 := by
        calc
          (13 : ZMod 231823871) ^ 16730 = (13 : ZMod 231823871) ^ (8365 + 8365) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 8365 * (13 : ZMod 231823871) ^ 8365 := by rw [pow_add]
          _ = 63543176 := by rw [factor_3_13]; decide
      have factor_3_15 : (13 : ZMod 231823871) ^ 33461 = 95705388 := by
        calc
          (13 : ZMod 231823871) ^ 33461 = (13 : ZMod 231823871) ^ (16730 + 16730 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 16730 * (13 : ZMod 231823871) ^ 16730) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 95705388 := by rw [factor_3_14]; decide
      have factor_3_16 : (13 : ZMod 231823871) ^ 66923 = 158905492 := by
        calc
          (13 : ZMod 231823871) ^ 66923 = (13 : ZMod 231823871) ^ (33461 + 33461 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 33461 * (13 : ZMod 231823871) ^ 33461) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 158905492 := by rw [factor_3_15]; decide
      have factor_3_17 : (13 : ZMod 231823871) ^ 133847 = 222997825 := by
        calc
          (13 : ZMod 231823871) ^ 133847 = (13 : ZMod 231823871) ^ (66923 + 66923 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 66923 * (13 : ZMod 231823871) ^ 66923) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 222997825 := by rw [factor_3_16]; decide
      have factor_3_18 : (13 : ZMod 231823871) ^ 267695 = 105216787 := by
        calc
          (13 : ZMod 231823871) ^ 267695 = (13 : ZMod 231823871) ^ (133847 + 133847 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 133847 * (13 : ZMod 231823871) ^ 133847) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 105216787 := by rw [factor_3_17]; decide
      have factor_3_19 : (13 : ZMod 231823871) ^ 535390 = 188611942 := by
        calc
          (13 : ZMod 231823871) ^ 535390 = (13 : ZMod 231823871) ^ (267695 + 267695) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 267695 * (13 : ZMod 231823871) ^ 267695 := by rw [pow_add]
          _ = 188611942 := by rw [factor_3_18]; decide
      change (13 : ZMod 231823871) ^ 535390 ≠ 1
      rw [factor_3_19]
      decide
    ·
      have factor_4_0 : (13 : ZMod 231823871) ^ 1 = 13 := by norm_num
      have factor_4_1 : (13 : ZMod 231823871) ^ 2 = 169 := by
        calc
          (13 : ZMod 231823871) ^ 2 = (13 : ZMod 231823871) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 1 * (13 : ZMod 231823871) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_4_0]; decide
      have factor_4_2 : (13 : ZMod 231823871) ^ 4 = 28561 := by
        calc
          (13 : ZMod 231823871) ^ 4 = (13 : ZMod 231823871) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 2 * (13 : ZMod 231823871) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_4_1]; decide
      have factor_4_3 : (13 : ZMod 231823871) ^ 9 = 172425178 := by
        calc
          (13 : ZMod 231823871) ^ 9 = (13 : ZMod 231823871) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 4 * (13 : ZMod 231823871) ^ 4) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 172425178 := by rw [factor_4_2]; decide
      have factor_4_4 : (13 : ZMod 231823871) ^ 19 = 56484936 := by
        calc
          (13 : ZMod 231823871) ^ 19 = (13 : ZMod 231823871) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 9 * (13 : ZMod 231823871) ^ 9) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 56484936 := by rw [factor_4_3]; decide
      have factor_4_5 : (13 : ZMod 231823871) ^ 39 = 204406263 := by
        calc
          (13 : ZMod 231823871) ^ 39 = (13 : ZMod 231823871) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 19 * (13 : ZMod 231823871) ^ 19) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 204406263 := by rw [factor_4_4]; decide
      have factor_4_6 : (13 : ZMod 231823871) ^ 78 = 162200288 := by
        calc
          (13 : ZMod 231823871) ^ 78 = (13 : ZMod 231823871) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 39 * (13 : ZMod 231823871) ^ 39 := by rw [pow_add]
          _ = 162200288 := by rw [factor_4_5]; decide
      have factor_4_7 : (13 : ZMod 231823871) ^ 156 = 139727243 := by
        calc
          (13 : ZMod 231823871) ^ 156 = (13 : ZMod 231823871) ^ (78 + 78) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 78 * (13 : ZMod 231823871) ^ 78 := by rw [pow_add]
          _ = 139727243 := by rw [factor_4_6]; decide
      have factor_4_8 : (13 : ZMod 231823871) ^ 312 = 5856603 := by
        calc
          (13 : ZMod 231823871) ^ 312 = (13 : ZMod 231823871) ^ (156 + 156) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 156 * (13 : ZMod 231823871) ^ 156 := by rw [pow_add]
          _ = 5856603 := by rw [factor_4_7]; decide
      have factor_4_9 : (13 : ZMod 231823871) ^ 625 = 163073516 := by
        calc
          (13 : ZMod 231823871) ^ 625 = (13 : ZMod 231823871) ^ (312 + 312 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 312 * (13 : ZMod 231823871) ^ 312) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 163073516 := by rw [factor_4_8]; decide
      have factor_4_10 : (13 : ZMod 231823871) ^ 1251 = 62129472 := by
        calc
          (13 : ZMod 231823871) ^ 1251 = (13 : ZMod 231823871) ^ (625 + 625 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 625 * (13 : ZMod 231823871) ^ 625) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 62129472 := by rw [factor_4_9]; decide
      have factor_4_11 : (13 : ZMod 231823871) ^ 2503 = 158188662 := by
        calc
          (13 : ZMod 231823871) ^ 2503 = (13 : ZMod 231823871) ^ (1251 + 1251 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 1251 * (13 : ZMod 231823871) ^ 1251) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 158188662 := by rw [factor_4_10]; decide
      have factor_4_12 : (13 : ZMod 231823871) ^ 5006 = 185279195 := by
        calc
          (13 : ZMod 231823871) ^ 5006 = (13 : ZMod 231823871) ^ (2503 + 2503) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 2503 * (13 : ZMod 231823871) ^ 2503 := by rw [pow_add]
          _ = 185279195 := by rw [factor_4_11]; decide
      have factor_4_13 : (13 : ZMod 231823871) ^ 10013 = 45134181 := by
        calc
          (13 : ZMod 231823871) ^ 10013 = (13 : ZMod 231823871) ^ (5006 + 5006 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 5006 * (13 : ZMod 231823871) ^ 5006) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 45134181 := by rw [factor_4_12]; decide
      have factor_4_14 : (13 : ZMod 231823871) ^ 20026 = 215919882 := by
        calc
          (13 : ZMod 231823871) ^ 20026 = (13 : ZMod 231823871) ^ (10013 + 10013) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 10013 * (13 : ZMod 231823871) ^ 10013 := by rw [pow_add]
          _ = 215919882 := by rw [factor_4_13]; decide
      have factor_4_15 : (13 : ZMod 231823871) ^ 40052 = 99708538 := by
        calc
          (13 : ZMod 231823871) ^ 40052 = (13 : ZMod 231823871) ^ (20026 + 20026) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 20026 * (13 : ZMod 231823871) ^ 20026 := by rw [pow_add]
          _ = 99708538 := by rw [factor_4_14]; decide
      have factor_4_16 : (13 : ZMod 231823871) ^ 80105 = 36622693 := by
        calc
          (13 : ZMod 231823871) ^ 80105 = (13 : ZMod 231823871) ^ (40052 + 40052 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = ((13 : ZMod 231823871) ^ 40052 * (13 : ZMod 231823871) ^ 40052) * (13 : ZMod 231823871) := by rw [pow_succ, pow_add]
          _ = 36622693 := by rw [factor_4_15]; decide
      have factor_4_17 : (13 : ZMod 231823871) ^ 160210 = 424329 := by
        calc
          (13 : ZMod 231823871) ^ 160210 = (13 : ZMod 231823871) ^ (80105 + 80105) :=
            congrArg (fun n : ℕ => (13 : ZMod 231823871) ^ n) (by norm_num)
          _ = (13 : ZMod 231823871) ^ 80105 * (13 : ZMod 231823871) ^ 80105 := by rw [pow_add]
          _ = 424329 := by rw [factor_4_16]; decide
      change (13 : ZMod 231823871) ^ 160210 ≠ 1
      rw [factor_4_17]
      decide

#print axioms prime_lucas_231823871

end TotientTailPeriodKiller
end Erdos249257
