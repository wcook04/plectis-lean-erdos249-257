import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_73703323 : Nat.Prime 73703323 := by
  apply lucas_primality 73703323 (7 : ZMod 73703323)
  ·
      have fermat_0 : (7 : ZMod 73703323) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 73703323) ^ 2 = 49 := by
        calc
          (7 : ZMod 73703323) ^ 2 = (7 : ZMod 73703323) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 1 * (7 : ZMod 73703323) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 73703323) ^ 4 = 2401 := by
        calc
          (7 : ZMod 73703323) ^ 4 = (7 : ZMod 73703323) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 2 * (7 : ZMod 73703323) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 73703323) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 73703323) ^ 8 = (7 : ZMod 73703323) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 4 * (7 : ZMod 73703323) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 73703323) ^ 17 = 52272400 := by
        calc
          (7 : ZMod 73703323) ^ 17 = (7 : ZMod 73703323) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 8 * (7 : ZMod 73703323) ^ 8) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 52272400 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 73703323) ^ 35 = 19507496 := by
        calc
          (7 : ZMod 73703323) ^ 35 = (7 : ZMod 73703323) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 17 * (7 : ZMod 73703323) ^ 17) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 19507496 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 73703323) ^ 70 = 56196044 := by
        calc
          (7 : ZMod 73703323) ^ 70 = (7 : ZMod 73703323) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 35 * (7 : ZMod 73703323) ^ 35 := by rw [pow_add]
          _ = 56196044 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 73703323) ^ 140 = 41559674 := by
        calc
          (7 : ZMod 73703323) ^ 140 = (7 : ZMod 73703323) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 70 * (7 : ZMod 73703323) ^ 70 := by rw [pow_add]
          _ = 41559674 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 73703323) ^ 281 = 71215291 := by
        calc
          (7 : ZMod 73703323) ^ 281 = (7 : ZMod 73703323) ^ (140 + 140 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 140 * (7 : ZMod 73703323) ^ 140) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 71215291 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 73703323) ^ 562 = 34837577 := by
        calc
          (7 : ZMod 73703323) ^ 562 = (7 : ZMod 73703323) ^ (281 + 281) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 281 * (7 : ZMod 73703323) ^ 281 := by rw [pow_add]
          _ = 34837577 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 73703323) ^ 1124 = 71307697 := by
        calc
          (7 : ZMod 73703323) ^ 1124 = (7 : ZMod 73703323) ^ (562 + 562) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 562 * (7 : ZMod 73703323) ^ 562 := by rw [pow_add]
          _ = 71307697 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 73703323) ^ 2249 = 65772137 := by
        calc
          (7 : ZMod 73703323) ^ 2249 = (7 : ZMod 73703323) ^ (1124 + 1124 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 1124 * (7 : ZMod 73703323) ^ 1124) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 65772137 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 73703323) ^ 4498 = 62582463 := by
        calc
          (7 : ZMod 73703323) ^ 4498 = (7 : ZMod 73703323) ^ (2249 + 2249) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 2249 * (7 : ZMod 73703323) ^ 2249 := by rw [pow_add]
          _ = 62582463 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 73703323) ^ 8996 = 14475507 := by
        calc
          (7 : ZMod 73703323) ^ 8996 = (7 : ZMod 73703323) ^ (4498 + 4498) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 4498 * (7 : ZMod 73703323) ^ 4498 := by rw [pow_add]
          _ = 14475507 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 73703323) ^ 17993 = 54574725 := by
        calc
          (7 : ZMod 73703323) ^ 17993 = (7 : ZMod 73703323) ^ (8996 + 8996 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 8996 * (7 : ZMod 73703323) ^ 8996) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 54574725 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 73703323) ^ 35987 = 58404443 := by
        calc
          (7 : ZMod 73703323) ^ 35987 = (7 : ZMod 73703323) ^ (17993 + 17993 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 17993 * (7 : ZMod 73703323) ^ 17993) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 58404443 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 73703323) ^ 71975 = 22459256 := by
        calc
          (7 : ZMod 73703323) ^ 71975 = (7 : ZMod 73703323) ^ (35987 + 35987 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 35987 * (7 : ZMod 73703323) ^ 35987) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 22459256 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 73703323) ^ 143951 = 54556852 := by
        calc
          (7 : ZMod 73703323) ^ 143951 = (7 : ZMod 73703323) ^ (71975 + 71975 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 71975 * (7 : ZMod 73703323) ^ 71975) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 54556852 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 73703323) ^ 287903 = 38260146 := by
        calc
          (7 : ZMod 73703323) ^ 287903 = (7 : ZMod 73703323) ^ (143951 + 143951 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 143951 * (7 : ZMod 73703323) ^ 143951) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 38260146 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 73703323) ^ 575807 = 43781629 := by
        calc
          (7 : ZMod 73703323) ^ 575807 = (7 : ZMod 73703323) ^ (287903 + 287903 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 287903 * (7 : ZMod 73703323) ^ 287903) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 43781629 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 73703323) ^ 1151614 = 46039994 := by
        calc
          (7 : ZMod 73703323) ^ 1151614 = (7 : ZMod 73703323) ^ (575807 + 575807) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 575807 * (7 : ZMod 73703323) ^ 575807 := by rw [pow_add]
          _ = 46039994 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 73703323) ^ 2303228 = 11236316 := by
        calc
          (7 : ZMod 73703323) ^ 2303228 = (7 : ZMod 73703323) ^ (1151614 + 1151614) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 1151614 * (7 : ZMod 73703323) ^ 1151614 := by rw [pow_add]
          _ = 11236316 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 73703323) ^ 4606457 = 32854307 := by
        calc
          (7 : ZMod 73703323) ^ 4606457 = (7 : ZMod 73703323) ^ (2303228 + 2303228 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 2303228 * (7 : ZMod 73703323) ^ 2303228) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 32854307 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 73703323) ^ 9212915 = 14393353 := by
        calc
          (7 : ZMod 73703323) ^ 9212915 = (7 : ZMod 73703323) ^ (4606457 + 4606457 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 4606457 * (7 : ZMod 73703323) ^ 4606457) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 14393353 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 73703323) ^ 18425830 = 67347997 := by
        calc
          (7 : ZMod 73703323) ^ 18425830 = (7 : ZMod 73703323) ^ (9212915 + 9212915) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 9212915 * (7 : ZMod 73703323) ^ 9212915 := by rw [pow_add]
          _ = 67347997 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 73703323) ^ 36851661 = 73703322 := by
        calc
          (7 : ZMod 73703323) ^ 36851661 = (7 : ZMod 73703323) ^ (18425830 + 18425830 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 18425830 * (7 : ZMod 73703323) ^ 18425830) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 73703322 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 73703323) ^ 73703322 = 1 := by
        calc
          (7 : ZMod 73703323) ^ 73703322 = (7 : ZMod 73703323) ^ (36851661 + 36851661) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 36851661 * (7 : ZMod 73703323) ^ 36851661 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (11, 1), (41, 1), (1297, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (11, 1), (41, 1), (1297, 1)] : List FactorBlock).map factorBlockValue).prod = 73703323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 73703323) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 73703323) ^ 2 = 49 := by
        calc
          (7 : ZMod 73703323) ^ 2 = (7 : ZMod 73703323) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 1 * (7 : ZMod 73703323) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 73703323) ^ 4 = 2401 := by
        calc
          (7 : ZMod 73703323) ^ 4 = (7 : ZMod 73703323) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 2 * (7 : ZMod 73703323) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 73703323) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 73703323) ^ 8 = (7 : ZMod 73703323) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 4 * (7 : ZMod 73703323) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 73703323) ^ 17 = 52272400 := by
        calc
          (7 : ZMod 73703323) ^ 17 = (7 : ZMod 73703323) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 8 * (7 : ZMod 73703323) ^ 8) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 52272400 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 73703323) ^ 35 = 19507496 := by
        calc
          (7 : ZMod 73703323) ^ 35 = (7 : ZMod 73703323) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 17 * (7 : ZMod 73703323) ^ 17) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 19507496 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 73703323) ^ 70 = 56196044 := by
        calc
          (7 : ZMod 73703323) ^ 70 = (7 : ZMod 73703323) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 35 * (7 : ZMod 73703323) ^ 35 := by rw [pow_add]
          _ = 56196044 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 73703323) ^ 140 = 41559674 := by
        calc
          (7 : ZMod 73703323) ^ 140 = (7 : ZMod 73703323) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 70 * (7 : ZMod 73703323) ^ 70 := by rw [pow_add]
          _ = 41559674 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 73703323) ^ 281 = 71215291 := by
        calc
          (7 : ZMod 73703323) ^ 281 = (7 : ZMod 73703323) ^ (140 + 140 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 140 * (7 : ZMod 73703323) ^ 140) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 71215291 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 73703323) ^ 562 = 34837577 := by
        calc
          (7 : ZMod 73703323) ^ 562 = (7 : ZMod 73703323) ^ (281 + 281) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 281 * (7 : ZMod 73703323) ^ 281 := by rw [pow_add]
          _ = 34837577 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 73703323) ^ 1124 = 71307697 := by
        calc
          (7 : ZMod 73703323) ^ 1124 = (7 : ZMod 73703323) ^ (562 + 562) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 562 * (7 : ZMod 73703323) ^ 562 := by rw [pow_add]
          _ = 71307697 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 73703323) ^ 2249 = 65772137 := by
        calc
          (7 : ZMod 73703323) ^ 2249 = (7 : ZMod 73703323) ^ (1124 + 1124 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 1124 * (7 : ZMod 73703323) ^ 1124) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 65772137 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 73703323) ^ 4498 = 62582463 := by
        calc
          (7 : ZMod 73703323) ^ 4498 = (7 : ZMod 73703323) ^ (2249 + 2249) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 2249 * (7 : ZMod 73703323) ^ 2249 := by rw [pow_add]
          _ = 62582463 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 73703323) ^ 8996 = 14475507 := by
        calc
          (7 : ZMod 73703323) ^ 8996 = (7 : ZMod 73703323) ^ (4498 + 4498) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 4498 * (7 : ZMod 73703323) ^ 4498 := by rw [pow_add]
          _ = 14475507 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 73703323) ^ 17993 = 54574725 := by
        calc
          (7 : ZMod 73703323) ^ 17993 = (7 : ZMod 73703323) ^ (8996 + 8996 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 8996 * (7 : ZMod 73703323) ^ 8996) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 54574725 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 73703323) ^ 35987 = 58404443 := by
        calc
          (7 : ZMod 73703323) ^ 35987 = (7 : ZMod 73703323) ^ (17993 + 17993 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 17993 * (7 : ZMod 73703323) ^ 17993) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 58404443 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 73703323) ^ 71975 = 22459256 := by
        calc
          (7 : ZMod 73703323) ^ 71975 = (7 : ZMod 73703323) ^ (35987 + 35987 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 35987 * (7 : ZMod 73703323) ^ 35987) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 22459256 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 73703323) ^ 143951 = 54556852 := by
        calc
          (7 : ZMod 73703323) ^ 143951 = (7 : ZMod 73703323) ^ (71975 + 71975 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 71975 * (7 : ZMod 73703323) ^ 71975) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 54556852 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 73703323) ^ 287903 = 38260146 := by
        calc
          (7 : ZMod 73703323) ^ 287903 = (7 : ZMod 73703323) ^ (143951 + 143951 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 143951 * (7 : ZMod 73703323) ^ 143951) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 38260146 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 73703323) ^ 575807 = 43781629 := by
        calc
          (7 : ZMod 73703323) ^ 575807 = (7 : ZMod 73703323) ^ (287903 + 287903 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 287903 * (7 : ZMod 73703323) ^ 287903) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 43781629 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 73703323) ^ 1151614 = 46039994 := by
        calc
          (7 : ZMod 73703323) ^ 1151614 = (7 : ZMod 73703323) ^ (575807 + 575807) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 575807 * (7 : ZMod 73703323) ^ 575807 := by rw [pow_add]
          _ = 46039994 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 73703323) ^ 2303228 = 11236316 := by
        calc
          (7 : ZMod 73703323) ^ 2303228 = (7 : ZMod 73703323) ^ (1151614 + 1151614) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 1151614 * (7 : ZMod 73703323) ^ 1151614 := by rw [pow_add]
          _ = 11236316 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 73703323) ^ 4606457 = 32854307 := by
        calc
          (7 : ZMod 73703323) ^ 4606457 = (7 : ZMod 73703323) ^ (2303228 + 2303228 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 2303228 * (7 : ZMod 73703323) ^ 2303228) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 32854307 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 73703323) ^ 9212915 = 14393353 := by
        calc
          (7 : ZMod 73703323) ^ 9212915 = (7 : ZMod 73703323) ^ (4606457 + 4606457 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 4606457 * (7 : ZMod 73703323) ^ 4606457) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 14393353 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 73703323) ^ 18425830 = 67347997 := by
        calc
          (7 : ZMod 73703323) ^ 18425830 = (7 : ZMod 73703323) ^ (9212915 + 9212915) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 9212915 * (7 : ZMod 73703323) ^ 9212915 := by rw [pow_add]
          _ = 67347997 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 73703323) ^ 36851661 = 73703322 := by
        calc
          (7 : ZMod 73703323) ^ 36851661 = (7 : ZMod 73703323) ^ (18425830 + 18425830 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 18425830 * (7 : ZMod 73703323) ^ 18425830) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 73703322 := by rw [factor_0_24]; decide
      change (7 : ZMod 73703323) ^ 36851661 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (7 : ZMod 73703323) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 73703323) ^ 2 = 49 := by
        calc
          (7 : ZMod 73703323) ^ 2 = (7 : ZMod 73703323) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 1 * (7 : ZMod 73703323) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 73703323) ^ 5 = 16807 := by
        calc
          (7 : ZMod 73703323) ^ 5 = (7 : ZMod 73703323) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 2 * (7 : ZMod 73703323) ^ 2) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 73703323) ^ 11 = 61040345 := by
        calc
          (7 : ZMod 73703323) ^ 11 = (7 : ZMod 73703323) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 5 * (7 : ZMod 73703323) ^ 5) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 61040345 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 73703323) ^ 23 = 64019803 := by
        calc
          (7 : ZMod 73703323) ^ 23 = (7 : ZMod 73703323) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 11 * (7 : ZMod 73703323) ^ 11) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 64019803 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 73703323) ^ 46 = 32837190 := by
        calc
          (7 : ZMod 73703323) ^ 46 = (7 : ZMod 73703323) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 23 * (7 : ZMod 73703323) ^ 23 := by rw [pow_add]
          _ = 32837190 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 73703323) ^ 93 = 71294095 := by
        calc
          (7 : ZMod 73703323) ^ 93 = (7 : ZMod 73703323) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 46 * (7 : ZMod 73703323) ^ 46) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 71294095 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 73703323) ^ 187 = 4911709 := by
        calc
          (7 : ZMod 73703323) ^ 187 = (7 : ZMod 73703323) ^ (93 + 93 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 93 * (7 : ZMod 73703323) ^ 93) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 4911709 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 73703323) ^ 374 = 18803029 := by
        calc
          (7 : ZMod 73703323) ^ 374 = (7 : ZMod 73703323) ^ (187 + 187) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 187 * (7 : ZMod 73703323) ^ 187 := by rw [pow_add]
          _ = 18803029 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 73703323) ^ 749 = 47305957 := by
        calc
          (7 : ZMod 73703323) ^ 749 = (7 : ZMod 73703323) ^ (374 + 374 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 374 * (7 : ZMod 73703323) ^ 374) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 47305957 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 73703323) ^ 1499 = 21894186 := by
        calc
          (7 : ZMod 73703323) ^ 1499 = (7 : ZMod 73703323) ^ (749 + 749 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 749 * (7 : ZMod 73703323) ^ 749) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 21894186 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 73703323) ^ 2998 = 23309046 := by
        calc
          (7 : ZMod 73703323) ^ 2998 = (7 : ZMod 73703323) ^ (1499 + 1499) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 1499 * (7 : ZMod 73703323) ^ 1499 := by rw [pow_add]
          _ = 23309046 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 73703323) ^ 5997 = 66860075 := by
        calc
          (7 : ZMod 73703323) ^ 5997 = (7 : ZMod 73703323) ^ (2998 + 2998 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 2998 * (7 : ZMod 73703323) ^ 2998) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 66860075 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 73703323) ^ 11995 = 32619428 := by
        calc
          (7 : ZMod 73703323) ^ 11995 = (7 : ZMod 73703323) ^ (5997 + 5997 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 5997 * (7 : ZMod 73703323) ^ 5997) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 32619428 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 73703323) ^ 23991 = 39046008 := by
        calc
          (7 : ZMod 73703323) ^ 23991 = (7 : ZMod 73703323) ^ (11995 + 11995 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 11995 * (7 : ZMod 73703323) ^ 11995) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 39046008 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 73703323) ^ 47983 = 130922 := by
        calc
          (7 : ZMod 73703323) ^ 47983 = (7 : ZMod 73703323) ^ (23991 + 23991 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 23991 * (7 : ZMod 73703323) ^ 23991) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 130922 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 73703323) ^ 95967 = 68684067 := by
        calc
          (7 : ZMod 73703323) ^ 95967 = (7 : ZMod 73703323) ^ (47983 + 47983 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 47983 * (7 : ZMod 73703323) ^ 47983) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 68684067 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 73703323) ^ 191935 = 58689391 := by
        calc
          (7 : ZMod 73703323) ^ 191935 = (7 : ZMod 73703323) ^ (95967 + 95967 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 95967 * (7 : ZMod 73703323) ^ 95967) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 58689391 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 73703323) ^ 383871 = 33329135 := by
        calc
          (7 : ZMod 73703323) ^ 383871 = (7 : ZMod 73703323) ^ (191935 + 191935 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 191935 * (7 : ZMod 73703323) ^ 191935) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 33329135 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 73703323) ^ 767742 = 35832014 := by
        calc
          (7 : ZMod 73703323) ^ 767742 = (7 : ZMod 73703323) ^ (383871 + 383871) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 383871 * (7 : ZMod 73703323) ^ 383871 := by rw [pow_add]
          _ = 35832014 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 73703323) ^ 1535485 = 61520974 := by
        calc
          (7 : ZMod 73703323) ^ 1535485 = (7 : ZMod 73703323) ^ (767742 + 767742 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 767742 * (7 : ZMod 73703323) ^ 767742) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 61520974 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 73703323) ^ 3070971 = 36962273 := by
        calc
          (7 : ZMod 73703323) ^ 3070971 = (7 : ZMod 73703323) ^ (1535485 + 1535485 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 1535485 * (7 : ZMod 73703323) ^ 1535485) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 36962273 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 73703323) ^ 6141943 = 56343692 := by
        calc
          (7 : ZMod 73703323) ^ 6141943 = (7 : ZMod 73703323) ^ (3070971 + 3070971 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 3070971 * (7 : ZMod 73703323) ^ 3070971) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 56343692 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 73703323) ^ 12283887 = 71048317 := by
        calc
          (7 : ZMod 73703323) ^ 12283887 = (7 : ZMod 73703323) ^ (6141943 + 6141943 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 6141943 * (7 : ZMod 73703323) ^ 6141943) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 71048317 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 73703323) ^ 24567774 = 71048316 := by
        calc
          (7 : ZMod 73703323) ^ 24567774 = (7 : ZMod 73703323) ^ (12283887 + 12283887) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 12283887 * (7 : ZMod 73703323) ^ 12283887 := by rw [pow_add]
          _ = 71048316 := by rw [factor_1_23]; decide
      change (7 : ZMod 73703323) ^ 24567774 ≠ 1
      rw [factor_1_24]
      decide
    ·
      have factor_2_0 : (7 : ZMod 73703323) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 73703323) ^ 2 = 49 := by
        calc
          (7 : ZMod 73703323) ^ 2 = (7 : ZMod 73703323) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 1 * (7 : ZMod 73703323) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 73703323) ^ 5 = 16807 := by
        calc
          (7 : ZMod 73703323) ^ 5 = (7 : ZMod 73703323) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 2 * (7 : ZMod 73703323) ^ 2) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 73703323) ^ 10 = 61365280 := by
        calc
          (7 : ZMod 73703323) ^ 10 = (7 : ZMod 73703323) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 5 * (7 : ZMod 73703323) ^ 5 := by rw [pow_add]
          _ = 61365280 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 73703323) ^ 20 = 19525711 := by
        calc
          (7 : ZMod 73703323) ^ 20 = (7 : ZMod 73703323) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 10 * (7 : ZMod 73703323) ^ 10 := by rw [pow_add]
          _ = 19525711 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 73703323) ^ 40 = 30104568 := by
        calc
          (7 : ZMod 73703323) ^ 40 = (7 : ZMod 73703323) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 20 * (7 : ZMod 73703323) ^ 20 := by rw [pow_add]
          _ = 30104568 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 73703323) ^ 80 = 63156008 := by
        calc
          (7 : ZMod 73703323) ^ 80 = (7 : ZMod 73703323) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 40 * (7 : ZMod 73703323) ^ 40 := by rw [pow_add]
          _ = 63156008 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 73703323) ^ 160 = 47962746 := by
        calc
          (7 : ZMod 73703323) ^ 160 = (7 : ZMod 73703323) ^ (80 + 80) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 80 * (7 : ZMod 73703323) ^ 80 := by rw [pow_add]
          _ = 47962746 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 73703323) ^ 321 = 20875220 := by
        calc
          (7 : ZMod 73703323) ^ 321 = (7 : ZMod 73703323) ^ (160 + 160 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 160 * (7 : ZMod 73703323) ^ 160) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 20875220 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 73703323) ^ 642 = 6534781 := by
        calc
          (7 : ZMod 73703323) ^ 642 = (7 : ZMod 73703323) ^ (321 + 321) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 321 * (7 : ZMod 73703323) ^ 321 := by rw [pow_add]
          _ = 6534781 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 73703323) ^ 1285 = 33811986 := by
        calc
          (7 : ZMod 73703323) ^ 1285 = (7 : ZMod 73703323) ^ (642 + 642 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 642 * (7 : ZMod 73703323) ^ 642) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 33811986 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 73703323) ^ 2570 = 49593205 := by
        calc
          (7 : ZMod 73703323) ^ 2570 = (7 : ZMod 73703323) ^ (1285 + 1285) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 1285 * (7 : ZMod 73703323) ^ 1285 := by rw [pow_add]
          _ = 49593205 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 73703323) ^ 5141 = 55113481 := by
        calc
          (7 : ZMod 73703323) ^ 5141 = (7 : ZMod 73703323) ^ (2570 + 2570 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 2570 * (7 : ZMod 73703323) ^ 2570) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 55113481 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 73703323) ^ 10282 = 21009520 := by
        calc
          (7 : ZMod 73703323) ^ 10282 = (7 : ZMod 73703323) ^ (5141 + 5141) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 5141 * (7 : ZMod 73703323) ^ 5141 := by rw [pow_add]
          _ = 21009520 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 73703323) ^ 20564 = 15802098 := by
        calc
          (7 : ZMod 73703323) ^ 20564 = (7 : ZMod 73703323) ^ (10282 + 10282) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 10282 * (7 : ZMod 73703323) ^ 10282 := by rw [pow_add]
          _ = 15802098 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 73703323) ^ 41129 = 6419347 := by
        calc
          (7 : ZMod 73703323) ^ 41129 = (7 : ZMod 73703323) ^ (20564 + 20564 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 20564 * (7 : ZMod 73703323) ^ 20564) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 6419347 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 73703323) ^ 82258 = 45797171 := by
        calc
          (7 : ZMod 73703323) ^ 82258 = (7 : ZMod 73703323) ^ (41129 + 41129) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 41129 * (7 : ZMod 73703323) ^ 41129 := by rw [pow_add]
          _ = 45797171 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 73703323) ^ 164516 = 28649662 := by
        calc
          (7 : ZMod 73703323) ^ 164516 = (7 : ZMod 73703323) ^ (82258 + 82258) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 82258 * (7 : ZMod 73703323) ^ 82258 := by rw [pow_add]
          _ = 28649662 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 73703323) ^ 329032 = 32452258 := by
        calc
          (7 : ZMod 73703323) ^ 329032 = (7 : ZMod 73703323) ^ (164516 + 164516) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 164516 * (7 : ZMod 73703323) ^ 164516 := by rw [pow_add]
          _ = 32452258 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 73703323) ^ 658065 = 22446503 := by
        calc
          (7 : ZMod 73703323) ^ 658065 = (7 : ZMod 73703323) ^ (329032 + 329032 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 329032 * (7 : ZMod 73703323) ^ 329032) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 22446503 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 73703323) ^ 1316130 = 73172342 := by
        calc
          (7 : ZMod 73703323) ^ 1316130 = (7 : ZMod 73703323) ^ (658065 + 658065) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 658065 * (7 : ZMod 73703323) ^ 658065 := by rw [pow_add]
          _ = 73172342 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 73703323) ^ 2632261 = 31876556 := by
        calc
          (7 : ZMod 73703323) ^ 2632261 = (7 : ZMod 73703323) ^ (1316130 + 1316130 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 1316130 * (7 : ZMod 73703323) ^ 1316130) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 31876556 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 73703323) ^ 5264523 = 6722004 := by
        calc
          (7 : ZMod 73703323) ^ 5264523 = (7 : ZMod 73703323) ^ (2632261 + 2632261 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 2632261 * (7 : ZMod 73703323) ^ 2632261) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 6722004 := by rw [factor_2_21]; decide
      have factor_2_23 : (7 : ZMod 73703323) ^ 10529046 = 41544406 := by
        calc
          (7 : ZMod 73703323) ^ 10529046 = (7 : ZMod 73703323) ^ (5264523 + 5264523) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 5264523 * (7 : ZMod 73703323) ^ 5264523 := by rw [pow_add]
          _ = 41544406 := by rw [factor_2_22]; decide
      change (7 : ZMod 73703323) ^ 10529046 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (7 : ZMod 73703323) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 73703323) ^ 3 = 343 := by
        calc
          (7 : ZMod 73703323) ^ 3 = (7 : ZMod 73703323) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 1 * (7 : ZMod 73703323) ^ 1) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 73703323) ^ 6 = 117649 := by
        calc
          (7 : ZMod 73703323) ^ 6 = (7 : ZMod 73703323) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 3 * (7 : ZMod 73703323) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 73703323) ^ 12 = 58765800 := by
        calc
          (7 : ZMod 73703323) ^ 12 = (7 : ZMod 73703323) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 6 * (7 : ZMod 73703323) ^ 6 := by rw [pow_add]
          _ = 58765800 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 73703323) ^ 25 = 41430781 := by
        calc
          (7 : ZMod 73703323) ^ 25 = (7 : ZMod 73703323) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 12 * (7 : ZMod 73703323) ^ 12) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 41430781 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 73703323) ^ 51 = 4169706 := by
        calc
          (7 : ZMod 73703323) ^ 51 = (7 : ZMod 73703323) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 25 * (7 : ZMod 73703323) ^ 25) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 4169706 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 73703323) ^ 102 = 55340705 := by
        calc
          (7 : ZMod 73703323) ^ 102 = (7 : ZMod 73703323) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 51 * (7 : ZMod 73703323) ^ 51 := by rw [pow_add]
          _ = 55340705 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 73703323) ^ 204 = 38904609 := by
        calc
          (7 : ZMod 73703323) ^ 204 = (7 : ZMod 73703323) ^ (102 + 102) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 102 * (7 : ZMod 73703323) ^ 102 := by rw [pow_add]
          _ = 38904609 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 73703323) ^ 408 = 34744478 := by
        calc
          (7 : ZMod 73703323) ^ 408 = (7 : ZMod 73703323) ^ (204 + 204) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 204 * (7 : ZMod 73703323) ^ 204 := by rw [pow_add]
          _ = 34744478 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 73703323) ^ 817 = 35647222 := by
        calc
          (7 : ZMod 73703323) ^ 817 = (7 : ZMod 73703323) ^ (408 + 408 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 408 * (7 : ZMod 73703323) ^ 408) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 35647222 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 73703323) ^ 1635 = 6701997 := by
        calc
          (7 : ZMod 73703323) ^ 1635 = (7 : ZMod 73703323) ^ (817 + 817 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 817 * (7 : ZMod 73703323) ^ 817) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 6701997 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 73703323) ^ 3271 = 2444585 := by
        calc
          (7 : ZMod 73703323) ^ 3271 = (7 : ZMod 73703323) ^ (1635 + 1635 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 1635 * (7 : ZMod 73703323) ^ 1635) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 2444585 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 73703323) ^ 6543 = 28313819 := by
        calc
          (7 : ZMod 73703323) ^ 6543 = (7 : ZMod 73703323) ^ (3271 + 3271 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 3271 * (7 : ZMod 73703323) ^ 3271) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 28313819 := by rw [factor_3_11]; decide
      have factor_3_13 : (7 : ZMod 73703323) ^ 13086 = 49137270 := by
        calc
          (7 : ZMod 73703323) ^ 13086 = (7 : ZMod 73703323) ^ (6543 + 6543) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 6543 * (7 : ZMod 73703323) ^ 6543 := by rw [pow_add]
          _ = 49137270 := by rw [factor_3_12]; decide
      have factor_3_14 : (7 : ZMod 73703323) ^ 26173 = 12551661 := by
        calc
          (7 : ZMod 73703323) ^ 26173 = (7 : ZMod 73703323) ^ (13086 + 13086 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 13086 * (7 : ZMod 73703323) ^ 13086) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 12551661 := by rw [factor_3_13]; decide
      have factor_3_15 : (7 : ZMod 73703323) ^ 52346 = 24296886 := by
        calc
          (7 : ZMod 73703323) ^ 52346 = (7 : ZMod 73703323) ^ (26173 + 26173) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 26173 * (7 : ZMod 73703323) ^ 26173 := by rw [pow_add]
          _ = 24296886 := by rw [factor_3_14]; decide
      have factor_3_16 : (7 : ZMod 73703323) ^ 104692 = 37493493 := by
        calc
          (7 : ZMod 73703323) ^ 104692 = (7 : ZMod 73703323) ^ (52346 + 52346) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 52346 * (7 : ZMod 73703323) ^ 52346 := by rw [pow_add]
          _ = 37493493 := by rw [factor_3_15]; decide
      have factor_3_17 : (7 : ZMod 73703323) ^ 209384 = 38227976 := by
        calc
          (7 : ZMod 73703323) ^ 209384 = (7 : ZMod 73703323) ^ (104692 + 104692) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 104692 * (7 : ZMod 73703323) ^ 104692 := by rw [pow_add]
          _ = 38227976 := by rw [factor_3_16]; decide
      have factor_3_18 : (7 : ZMod 73703323) ^ 418768 = 10924318 := by
        calc
          (7 : ZMod 73703323) ^ 418768 = (7 : ZMod 73703323) ^ (209384 + 209384) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 209384 * (7 : ZMod 73703323) ^ 209384 := by rw [pow_add]
          _ = 10924318 := by rw [factor_3_17]; decide
      have factor_3_19 : (7 : ZMod 73703323) ^ 837537 = 58451624 := by
        calc
          (7 : ZMod 73703323) ^ 837537 = (7 : ZMod 73703323) ^ (418768 + 418768 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 418768 * (7 : ZMod 73703323) ^ 418768) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 58451624 := by rw [factor_3_18]; decide
      have factor_3_20 : (7 : ZMod 73703323) ^ 1675075 = 11896717 := by
        calc
          (7 : ZMod 73703323) ^ 1675075 = (7 : ZMod 73703323) ^ (837537 + 837537 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 837537 * (7 : ZMod 73703323) ^ 837537) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 11896717 := by rw [factor_3_19]; decide
      have factor_3_21 : (7 : ZMod 73703323) ^ 3350151 = 38044380 := by
        calc
          (7 : ZMod 73703323) ^ 3350151 = (7 : ZMod 73703323) ^ (1675075 + 1675075 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 1675075 * (7 : ZMod 73703323) ^ 1675075) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 38044380 := by rw [factor_3_20]; decide
      have factor_3_22 : (7 : ZMod 73703323) ^ 6700302 = 48008850 := by
        calc
          (7 : ZMod 73703323) ^ 6700302 = (7 : ZMod 73703323) ^ (3350151 + 3350151) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 3350151 * (7 : ZMod 73703323) ^ 3350151 := by rw [pow_add]
          _ = 48008850 := by rw [factor_3_21]; decide
      change (7 : ZMod 73703323) ^ 6700302 ≠ 1
      rw [factor_3_22]
      decide
    ·
      have factor_4_0 : (7 : ZMod 73703323) ^ 1 = 7 := by norm_num
      have factor_4_1 : (7 : ZMod 73703323) ^ 3 = 343 := by
        calc
          (7 : ZMod 73703323) ^ 3 = (7 : ZMod 73703323) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 1 * (7 : ZMod 73703323) ^ 1) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_4_0]; decide
      have factor_4_2 : (7 : ZMod 73703323) ^ 6 = 117649 := by
        calc
          (7 : ZMod 73703323) ^ 6 = (7 : ZMod 73703323) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 3 * (7 : ZMod 73703323) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_4_1]; decide
      have factor_4_3 : (7 : ZMod 73703323) ^ 13 = 42843985 := by
        calc
          (7 : ZMod 73703323) ^ 13 = (7 : ZMod 73703323) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 6 * (7 : ZMod 73703323) ^ 6) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 42843985 := by rw [factor_4_2]; decide
      have factor_4_4 : (7 : ZMod 73703323) ^ 27 = 40118548 := by
        calc
          (7 : ZMod 73703323) ^ 27 = (7 : ZMod 73703323) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 13 * (7 : ZMod 73703323) ^ 13) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 40118548 := by rw [factor_4_3]; decide
      have factor_4_5 : (7 : ZMod 73703323) ^ 54 = 29846021 := by
        calc
          (7 : ZMod 73703323) ^ 54 = (7 : ZMod 73703323) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 27 * (7 : ZMod 73703323) ^ 27 := by rw [pow_add]
          _ = 29846021 := by rw [factor_4_4]; decide
      have factor_4_6 : (7 : ZMod 73703323) ^ 109 = 42297566 := by
        calc
          (7 : ZMod 73703323) ^ 109 = (7 : ZMod 73703323) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 54 * (7 : ZMod 73703323) ^ 54) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 42297566 := by rw [factor_4_5]; decide
      have factor_4_7 : (7 : ZMod 73703323) ^ 219 = 24319270 := by
        calc
          (7 : ZMod 73703323) ^ 219 = (7 : ZMod 73703323) ^ (109 + 109 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 109 * (7 : ZMod 73703323) ^ 109) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 24319270 := by rw [factor_4_6]; decide
      have factor_4_8 : (7 : ZMod 73703323) ^ 438 = 31965302 := by
        calc
          (7 : ZMod 73703323) ^ 438 = (7 : ZMod 73703323) ^ (219 + 219) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 219 * (7 : ZMod 73703323) ^ 219 := by rw [pow_add]
          _ = 31965302 := by rw [factor_4_7]; decide
      have factor_4_9 : (7 : ZMod 73703323) ^ 877 = 67919534 := by
        calc
          (7 : ZMod 73703323) ^ 877 = (7 : ZMod 73703323) ^ (438 + 438 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 438 * (7 : ZMod 73703323) ^ 438) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 67919534 := by rw [factor_4_8]; decide
      have factor_4_10 : (7 : ZMod 73703323) ^ 1755 = 25552719 := by
        calc
          (7 : ZMod 73703323) ^ 1755 = (7 : ZMod 73703323) ^ (877 + 877 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 877 * (7 : ZMod 73703323) ^ 877) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 25552719 := by rw [factor_4_9]; decide
      have factor_4_11 : (7 : ZMod 73703323) ^ 3511 = 25282031 := by
        calc
          (7 : ZMod 73703323) ^ 3511 = (7 : ZMod 73703323) ^ (1755 + 1755 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 1755 * (7 : ZMod 73703323) ^ 1755) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 25282031 := by rw [factor_4_10]; decide
      have factor_4_12 : (7 : ZMod 73703323) ^ 7022 = 4562588 := by
        calc
          (7 : ZMod 73703323) ^ 7022 = (7 : ZMod 73703323) ^ (3511 + 3511) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 3511 * (7 : ZMod 73703323) ^ 3511 := by rw [pow_add]
          _ = 4562588 := by rw [factor_4_11]; decide
      have factor_4_13 : (7 : ZMod 73703323) ^ 14044 = 489686 := by
        calc
          (7 : ZMod 73703323) ^ 14044 = (7 : ZMod 73703323) ^ (7022 + 7022) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 7022 * (7 : ZMod 73703323) ^ 7022 := by rw [pow_add]
          _ = 489686 := by rw [factor_4_12]; decide
      have factor_4_14 : (7 : ZMod 73703323) ^ 28088 = 35468877 := by
        calc
          (7 : ZMod 73703323) ^ 28088 = (7 : ZMod 73703323) ^ (14044 + 14044) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 14044 * (7 : ZMod 73703323) ^ 14044 := by rw [pow_add]
          _ = 35468877 := by rw [factor_4_13]; decide
      have factor_4_15 : (7 : ZMod 73703323) ^ 56176 = 26090682 := by
        calc
          (7 : ZMod 73703323) ^ 56176 = (7 : ZMod 73703323) ^ (28088 + 28088) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 28088 * (7 : ZMod 73703323) ^ 28088 := by rw [pow_add]
          _ = 26090682 := by rw [factor_4_14]; decide
      have factor_4_16 : (7 : ZMod 73703323) ^ 112352 = 17107093 := by
        calc
          (7 : ZMod 73703323) ^ 112352 = (7 : ZMod 73703323) ^ (56176 + 56176) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 56176 * (7 : ZMod 73703323) ^ 56176 := by rw [pow_add]
          _ = 17107093 := by rw [factor_4_15]; decide
      have factor_4_17 : (7 : ZMod 73703323) ^ 224705 = 31287373 := by
        calc
          (7 : ZMod 73703323) ^ 224705 = (7 : ZMod 73703323) ^ (112352 + 112352 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 112352 * (7 : ZMod 73703323) ^ 112352) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 31287373 := by rw [factor_4_16]; decide
      have factor_4_18 : (7 : ZMod 73703323) ^ 449410 = 33011223 := by
        calc
          (7 : ZMod 73703323) ^ 449410 = (7 : ZMod 73703323) ^ (224705 + 224705) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 224705 * (7 : ZMod 73703323) ^ 224705 := by rw [pow_add]
          _ = 33011223 := by rw [factor_4_17]; decide
      have factor_4_19 : (7 : ZMod 73703323) ^ 898821 = 26261621 := by
        calc
          (7 : ZMod 73703323) ^ 898821 = (7 : ZMod 73703323) ^ (449410 + 449410 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 449410 * (7 : ZMod 73703323) ^ 449410) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 26261621 := by rw [factor_4_18]; decide
      have factor_4_20 : (7 : ZMod 73703323) ^ 1797642 = 9950950 := by
        calc
          (7 : ZMod 73703323) ^ 1797642 = (7 : ZMod 73703323) ^ (898821 + 898821) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 898821 * (7 : ZMod 73703323) ^ 898821 := by rw [pow_add]
          _ = 9950950 := by rw [factor_4_19]; decide
      change (7 : ZMod 73703323) ^ 1797642 ≠ 1
      rw [factor_4_20]
      decide
    ·
      have factor_5_0 : (7 : ZMod 73703323) ^ 1 = 7 := by norm_num
      have factor_5_1 : (7 : ZMod 73703323) ^ 3 = 343 := by
        calc
          (7 : ZMod 73703323) ^ 3 = (7 : ZMod 73703323) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 1 * (7 : ZMod 73703323) ^ 1) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_5_0]; decide
      have factor_5_2 : (7 : ZMod 73703323) ^ 6 = 117649 := by
        calc
          (7 : ZMod 73703323) ^ 6 = (7 : ZMod 73703323) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 3 * (7 : ZMod 73703323) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_5_1]; decide
      have factor_5_3 : (7 : ZMod 73703323) ^ 13 = 42843985 := by
        calc
          (7 : ZMod 73703323) ^ 13 = (7 : ZMod 73703323) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 6 * (7 : ZMod 73703323) ^ 6) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 42843985 := by rw [factor_5_2]; decide
      have factor_5_4 : (7 : ZMod 73703323) ^ 27 = 40118548 := by
        calc
          (7 : ZMod 73703323) ^ 27 = (7 : ZMod 73703323) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 13 * (7 : ZMod 73703323) ^ 13) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 40118548 := by rw [factor_5_3]; decide
      have factor_5_5 : (7 : ZMod 73703323) ^ 55 = 61515501 := by
        calc
          (7 : ZMod 73703323) ^ 55 = (7 : ZMod 73703323) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 27 * (7 : ZMod 73703323) ^ 27) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 61515501 := by rw [factor_5_4]; decide
      have factor_5_6 : (7 : ZMod 73703323) ^ 110 = 1269670 := by
        calc
          (7 : ZMod 73703323) ^ 110 = (7 : ZMod 73703323) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 55 * (7 : ZMod 73703323) ^ 55 := by rw [pow_add]
          _ = 1269670 := by rw [factor_5_5]; decide
      have factor_5_7 : (7 : ZMod 73703323) ^ 221 = 12391062 := by
        calc
          (7 : ZMod 73703323) ^ 221 = (7 : ZMod 73703323) ^ (110 + 110 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 110 * (7 : ZMod 73703323) ^ 110) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 12391062 := by rw [factor_5_6]; decide
      have factor_5_8 : (7 : ZMod 73703323) ^ 443 = 17309367 := by
        calc
          (7 : ZMod 73703323) ^ 443 = (7 : ZMod 73703323) ^ (221 + 221 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 221 * (7 : ZMod 73703323) ^ 221) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 17309367 := by rw [factor_5_7]; decide
      have factor_5_9 : (7 : ZMod 73703323) ^ 887 = 48209805 := by
        calc
          (7 : ZMod 73703323) ^ 887 = (7 : ZMod 73703323) ^ (443 + 443 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 443 * (7 : ZMod 73703323) ^ 443) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 48209805 := by rw [factor_5_8]; decide
      have factor_5_10 : (7 : ZMod 73703323) ^ 1775 = 66596417 := by
        calc
          (7 : ZMod 73703323) ^ 1775 = (7 : ZMod 73703323) ^ (887 + 887 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 887 * (7 : ZMod 73703323) ^ 887) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 66596417 := by rw [factor_5_9]; decide
      have factor_5_11 : (7 : ZMod 73703323) ^ 3551 = 33532454 := by
        calc
          (7 : ZMod 73703323) ^ 3551 = (7 : ZMod 73703323) ^ (1775 + 1775 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 1775 * (7 : ZMod 73703323) ^ 1775) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 33532454 := by rw [factor_5_10]; decide
      have factor_5_12 : (7 : ZMod 73703323) ^ 7103 = 36329575 := by
        calc
          (7 : ZMod 73703323) ^ 7103 = (7 : ZMod 73703323) ^ (3551 + 3551 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 3551 * (7 : ZMod 73703323) ^ 3551) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 36329575 := by rw [factor_5_11]; decide
      have factor_5_13 : (7 : ZMod 73703323) ^ 14206 = 37850859 := by
        calc
          (7 : ZMod 73703323) ^ 14206 = (7 : ZMod 73703323) ^ (7103 + 7103) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 7103 * (7 : ZMod 73703323) ^ 7103 := by rw [pow_add]
          _ = 37850859 := by rw [factor_5_12]; decide
      have factor_5_14 : (7 : ZMod 73703323) ^ 28413 = 54588707 := by
        calc
          (7 : ZMod 73703323) ^ 28413 = (7 : ZMod 73703323) ^ (14206 + 14206 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = ((7 : ZMod 73703323) ^ 14206 * (7 : ZMod 73703323) ^ 14206) * (7 : ZMod 73703323) := by rw [pow_succ, pow_add]
          _ = 54588707 := by rw [factor_5_13]; decide
      have factor_5_15 : (7 : ZMod 73703323) ^ 56826 = 19862755 := by
        calc
          (7 : ZMod 73703323) ^ 56826 = (7 : ZMod 73703323) ^ (28413 + 28413) :=
            congrArg (fun n : ℕ => (7 : ZMod 73703323) ^ n) (by norm_num)
          _ = (7 : ZMod 73703323) ^ 28413 * (7 : ZMod 73703323) ^ 28413 := by rw [pow_add]
          _ = 19862755 := by rw [factor_5_14]; decide
      change (7 : ZMod 73703323) ^ 56826 ≠ 1
      rw [factor_5_15]
      decide

#print axioms prime_lucas_73703323

end TotientTailPeriodKiller
end Erdos249257
