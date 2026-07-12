import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_17026712993 : Nat.Prime 17026712993 := by
  apply lucas_primality 17026712993 (3 : ZMod 17026712993)
  ·
      have fermat_0 : (3 : ZMod 17026712993) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 17026712993) ^ 3 = 27 := by
        calc
          (3 : ZMod 17026712993) ^ 3 = (3 : ZMod 17026712993) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 1 * (3 : ZMod 17026712993) ^ 1) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 17026712993) ^ 7 = 2187 := by
        calc
          (3 : ZMod 17026712993) ^ 7 = (3 : ZMod 17026712993) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 3 * (3 : ZMod 17026712993) ^ 3) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 17026712993) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 17026712993) ^ 15 = (3 : ZMod 17026712993) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 7 * (3 : ZMod 17026712993) ^ 7) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 17026712993) ^ 31 = 12355749879 := by
        calc
          (3 : ZMod 17026712993) ^ 31 = (3 : ZMod 17026712993) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 15 * (3 : ZMod 17026712993) ^ 15) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 12355749879 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 17026712993) ^ 63 = 9259125187 := by
        calc
          (3 : ZMod 17026712993) ^ 63 = (3 : ZMod 17026712993) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 31 * (3 : ZMod 17026712993) ^ 31) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 9259125187 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 17026712993) ^ 126 = 13001841805 := by
        calc
          (3 : ZMod 17026712993) ^ 126 = (3 : ZMod 17026712993) ^ (63 + 63) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 63 * (3 : ZMod 17026712993) ^ 63 := by rw [pow_add]
          _ = 13001841805 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 17026712993) ^ 253 = 15203027485 := by
        calc
          (3 : ZMod 17026712993) ^ 253 = (3 : ZMod 17026712993) ^ (126 + 126 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 126 * (3 : ZMod 17026712993) ^ 126) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 15203027485 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 17026712993) ^ 507 = 3878236403 := by
        calc
          (3 : ZMod 17026712993) ^ 507 = (3 : ZMod 17026712993) ^ (253 + 253 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 253 * (3 : ZMod 17026712993) ^ 253) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 3878236403 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 17026712993) ^ 1014 = 16443499570 := by
        calc
          (3 : ZMod 17026712993) ^ 1014 = (3 : ZMod 17026712993) ^ (507 + 507) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 507 * (3 : ZMod 17026712993) ^ 507 := by rw [pow_add]
          _ = 16443499570 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 17026712993) ^ 2029 = 5277422928 := by
        calc
          (3 : ZMod 17026712993) ^ 2029 = (3 : ZMod 17026712993) ^ (1014 + 1014 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 1014 * (3 : ZMod 17026712993) ^ 1014) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 5277422928 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 17026712993) ^ 4059 = 15932970485 := by
        calc
          (3 : ZMod 17026712993) ^ 4059 = (3 : ZMod 17026712993) ^ (2029 + 2029 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 2029 * (3 : ZMod 17026712993) ^ 2029) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 15932970485 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 17026712993) ^ 8118 = 13877113117 := by
        calc
          (3 : ZMod 17026712993) ^ 8118 = (3 : ZMod 17026712993) ^ (4059 + 4059) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 4059 * (3 : ZMod 17026712993) ^ 4059 := by rw [pow_add]
          _ = 13877113117 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 17026712993) ^ 16237 = 7072675010 := by
        calc
          (3 : ZMod 17026712993) ^ 16237 = (3 : ZMod 17026712993) ^ (8118 + 8118 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 8118 * (3 : ZMod 17026712993) ^ 8118) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 7072675010 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 17026712993) ^ 32475 = 16212396716 := by
        calc
          (3 : ZMod 17026712993) ^ 32475 = (3 : ZMod 17026712993) ^ (16237 + 16237 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 16237 * (3 : ZMod 17026712993) ^ 16237) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 16212396716 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 17026712993) ^ 64951 = 8791413166 := by
        calc
          (3 : ZMod 17026712993) ^ 64951 = (3 : ZMod 17026712993) ^ (32475 + 32475 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 32475 * (3 : ZMod 17026712993) ^ 32475) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 8791413166 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 17026712993) ^ 129903 = 4656128495 := by
        calc
          (3 : ZMod 17026712993) ^ 129903 = (3 : ZMod 17026712993) ^ (64951 + 64951 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 64951 * (3 : ZMod 17026712993) ^ 64951) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 4656128495 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 17026712993) ^ 259807 = 3901983380 := by
        calc
          (3 : ZMod 17026712993) ^ 259807 = (3 : ZMod 17026712993) ^ (129903 + 129903 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 129903 * (3 : ZMod 17026712993) ^ 129903) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 3901983380 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 17026712993) ^ 519614 = 7238719498 := by
        calc
          (3 : ZMod 17026712993) ^ 519614 = (3 : ZMod 17026712993) ^ (259807 + 259807) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 259807 * (3 : ZMod 17026712993) ^ 259807 := by rw [pow_add]
          _ = 7238719498 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 17026712993) ^ 1039228 = 14414434073 := by
        calc
          (3 : ZMod 17026712993) ^ 1039228 = (3 : ZMod 17026712993) ^ (519614 + 519614) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 519614 * (3 : ZMod 17026712993) ^ 519614 := by rw [pow_add]
          _ = 14414434073 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 17026712993) ^ 2078456 = 13459634834 := by
        calc
          (3 : ZMod 17026712993) ^ 2078456 = (3 : ZMod 17026712993) ^ (1039228 + 1039228) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 1039228 * (3 : ZMod 17026712993) ^ 1039228 := by rw [pow_add]
          _ = 13459634834 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 17026712993) ^ 4156912 = 11909568687 := by
        calc
          (3 : ZMod 17026712993) ^ 4156912 = (3 : ZMod 17026712993) ^ (2078456 + 2078456) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 2078456 * (3 : ZMod 17026712993) ^ 2078456 := by rw [pow_add]
          _ = 11909568687 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 17026712993) ^ 8313824 = 5481402806 := by
        calc
          (3 : ZMod 17026712993) ^ 8313824 = (3 : ZMod 17026712993) ^ (4156912 + 4156912) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 4156912 * (3 : ZMod 17026712993) ^ 4156912 := by rw [pow_add]
          _ = 5481402806 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 17026712993) ^ 16627649 = 8440890316 := by
        calc
          (3 : ZMod 17026712993) ^ 16627649 = (3 : ZMod 17026712993) ^ (8313824 + 8313824 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 8313824 * (3 : ZMod 17026712993) ^ 8313824) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 8440890316 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 17026712993) ^ 33255298 = 15318418251 := by
        calc
          (3 : ZMod 17026712993) ^ 33255298 = (3 : ZMod 17026712993) ^ (16627649 + 16627649) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 16627649 * (3 : ZMod 17026712993) ^ 16627649 := by rw [pow_add]
          _ = 15318418251 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 17026712993) ^ 66510597 = 3459555881 := by
        calc
          (3 : ZMod 17026712993) ^ 66510597 = (3 : ZMod 17026712993) ^ (33255298 + 33255298 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 33255298 * (3 : ZMod 17026712993) ^ 33255298) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 3459555881 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 17026712993) ^ 133021195 = 8403528898 := by
        calc
          (3 : ZMod 17026712993) ^ 133021195 = (3 : ZMod 17026712993) ^ (66510597 + 66510597 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 66510597 * (3 : ZMod 17026712993) ^ 66510597) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 8403528898 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 17026712993) ^ 266042390 = 16090384901 := by
        calc
          (3 : ZMod 17026712993) ^ 266042390 = (3 : ZMod 17026712993) ^ (133021195 + 133021195) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 133021195 * (3 : ZMod 17026712993) ^ 133021195 := by rw [pow_add]
          _ = 16090384901 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 17026712993) ^ 532084781 = 7790188363 := by
        calc
          (3 : ZMod 17026712993) ^ 532084781 = (3 : ZMod 17026712993) ^ (266042390 + 266042390 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 266042390 * (3 : ZMod 17026712993) ^ 266042390) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 7790188363 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 17026712993) ^ 1064169562 = 9735660195 := by
        calc
          (3 : ZMod 17026712993) ^ 1064169562 = (3 : ZMod 17026712993) ^ (532084781 + 532084781) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 532084781 * (3 : ZMod 17026712993) ^ 532084781 := by rw [pow_add]
          _ = 9735660195 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 17026712993) ^ 2128339124 = 11265349801 := by
        calc
          (3 : ZMod 17026712993) ^ 2128339124 = (3 : ZMod 17026712993) ^ (1064169562 + 1064169562) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 1064169562 * (3 : ZMod 17026712993) ^ 1064169562 := by rw [pow_add]
          _ = 11265349801 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 17026712993) ^ 4256678248 = 683342389 := by
        calc
          (3 : ZMod 17026712993) ^ 4256678248 = (3 : ZMod 17026712993) ^ (2128339124 + 2128339124) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 2128339124 * (3 : ZMod 17026712993) ^ 2128339124 := by rw [pow_add]
          _ = 683342389 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 17026712993) ^ 8513356496 = 17026712992 := by
        calc
          (3 : ZMod 17026712993) ^ 8513356496 = (3 : ZMod 17026712993) ^ (4256678248 + 4256678248) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 4256678248 * (3 : ZMod 17026712993) ^ 4256678248 := by rw [pow_add]
          _ = 17026712992 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 17026712993) ^ 17026712992 = 1 := by
        calc
          (3 : ZMod 17026712993) ^ 17026712992 = (3 : ZMod 17026712993) ^ (8513356496 + 8513356496) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 8513356496 * (3 : ZMod 17026712993) ^ 8513356496 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (2521, 1), (211061, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (2521, 1), (211061, 1)] : List FactorBlock).map factorBlockValue).prod = 17026712993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 17026712993) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 17026712993) ^ 3 = 27 := by
        calc
          (3 : ZMod 17026712993) ^ 3 = (3 : ZMod 17026712993) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 1 * (3 : ZMod 17026712993) ^ 1) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 17026712993) ^ 7 = 2187 := by
        calc
          (3 : ZMod 17026712993) ^ 7 = (3 : ZMod 17026712993) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 3 * (3 : ZMod 17026712993) ^ 3) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 17026712993) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 17026712993) ^ 15 = (3 : ZMod 17026712993) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 7 * (3 : ZMod 17026712993) ^ 7) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 17026712993) ^ 31 = 12355749879 := by
        calc
          (3 : ZMod 17026712993) ^ 31 = (3 : ZMod 17026712993) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 15 * (3 : ZMod 17026712993) ^ 15) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 12355749879 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 17026712993) ^ 63 = 9259125187 := by
        calc
          (3 : ZMod 17026712993) ^ 63 = (3 : ZMod 17026712993) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 31 * (3 : ZMod 17026712993) ^ 31) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 9259125187 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 17026712993) ^ 126 = 13001841805 := by
        calc
          (3 : ZMod 17026712993) ^ 126 = (3 : ZMod 17026712993) ^ (63 + 63) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 63 * (3 : ZMod 17026712993) ^ 63 := by rw [pow_add]
          _ = 13001841805 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 17026712993) ^ 253 = 15203027485 := by
        calc
          (3 : ZMod 17026712993) ^ 253 = (3 : ZMod 17026712993) ^ (126 + 126 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 126 * (3 : ZMod 17026712993) ^ 126) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 15203027485 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 17026712993) ^ 507 = 3878236403 := by
        calc
          (3 : ZMod 17026712993) ^ 507 = (3 : ZMod 17026712993) ^ (253 + 253 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 253 * (3 : ZMod 17026712993) ^ 253) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 3878236403 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 17026712993) ^ 1014 = 16443499570 := by
        calc
          (3 : ZMod 17026712993) ^ 1014 = (3 : ZMod 17026712993) ^ (507 + 507) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 507 * (3 : ZMod 17026712993) ^ 507 := by rw [pow_add]
          _ = 16443499570 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 17026712993) ^ 2029 = 5277422928 := by
        calc
          (3 : ZMod 17026712993) ^ 2029 = (3 : ZMod 17026712993) ^ (1014 + 1014 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 1014 * (3 : ZMod 17026712993) ^ 1014) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 5277422928 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 17026712993) ^ 4059 = 15932970485 := by
        calc
          (3 : ZMod 17026712993) ^ 4059 = (3 : ZMod 17026712993) ^ (2029 + 2029 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 2029 * (3 : ZMod 17026712993) ^ 2029) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 15932970485 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 17026712993) ^ 8118 = 13877113117 := by
        calc
          (3 : ZMod 17026712993) ^ 8118 = (3 : ZMod 17026712993) ^ (4059 + 4059) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 4059 * (3 : ZMod 17026712993) ^ 4059 := by rw [pow_add]
          _ = 13877113117 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 17026712993) ^ 16237 = 7072675010 := by
        calc
          (3 : ZMod 17026712993) ^ 16237 = (3 : ZMod 17026712993) ^ (8118 + 8118 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 8118 * (3 : ZMod 17026712993) ^ 8118) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 7072675010 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 17026712993) ^ 32475 = 16212396716 := by
        calc
          (3 : ZMod 17026712993) ^ 32475 = (3 : ZMod 17026712993) ^ (16237 + 16237 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 16237 * (3 : ZMod 17026712993) ^ 16237) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 16212396716 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 17026712993) ^ 64951 = 8791413166 := by
        calc
          (3 : ZMod 17026712993) ^ 64951 = (3 : ZMod 17026712993) ^ (32475 + 32475 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 32475 * (3 : ZMod 17026712993) ^ 32475) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 8791413166 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 17026712993) ^ 129903 = 4656128495 := by
        calc
          (3 : ZMod 17026712993) ^ 129903 = (3 : ZMod 17026712993) ^ (64951 + 64951 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 64951 * (3 : ZMod 17026712993) ^ 64951) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 4656128495 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 17026712993) ^ 259807 = 3901983380 := by
        calc
          (3 : ZMod 17026712993) ^ 259807 = (3 : ZMod 17026712993) ^ (129903 + 129903 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 129903 * (3 : ZMod 17026712993) ^ 129903) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 3901983380 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 17026712993) ^ 519614 = 7238719498 := by
        calc
          (3 : ZMod 17026712993) ^ 519614 = (3 : ZMod 17026712993) ^ (259807 + 259807) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 259807 * (3 : ZMod 17026712993) ^ 259807 := by rw [pow_add]
          _ = 7238719498 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 17026712993) ^ 1039228 = 14414434073 := by
        calc
          (3 : ZMod 17026712993) ^ 1039228 = (3 : ZMod 17026712993) ^ (519614 + 519614) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 519614 * (3 : ZMod 17026712993) ^ 519614 := by rw [pow_add]
          _ = 14414434073 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 17026712993) ^ 2078456 = 13459634834 := by
        calc
          (3 : ZMod 17026712993) ^ 2078456 = (3 : ZMod 17026712993) ^ (1039228 + 1039228) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 1039228 * (3 : ZMod 17026712993) ^ 1039228 := by rw [pow_add]
          _ = 13459634834 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 17026712993) ^ 4156912 = 11909568687 := by
        calc
          (3 : ZMod 17026712993) ^ 4156912 = (3 : ZMod 17026712993) ^ (2078456 + 2078456) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 2078456 * (3 : ZMod 17026712993) ^ 2078456 := by rw [pow_add]
          _ = 11909568687 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 17026712993) ^ 8313824 = 5481402806 := by
        calc
          (3 : ZMod 17026712993) ^ 8313824 = (3 : ZMod 17026712993) ^ (4156912 + 4156912) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 4156912 * (3 : ZMod 17026712993) ^ 4156912 := by rw [pow_add]
          _ = 5481402806 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 17026712993) ^ 16627649 = 8440890316 := by
        calc
          (3 : ZMod 17026712993) ^ 16627649 = (3 : ZMod 17026712993) ^ (8313824 + 8313824 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 8313824 * (3 : ZMod 17026712993) ^ 8313824) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 8440890316 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 17026712993) ^ 33255298 = 15318418251 := by
        calc
          (3 : ZMod 17026712993) ^ 33255298 = (3 : ZMod 17026712993) ^ (16627649 + 16627649) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 16627649 * (3 : ZMod 17026712993) ^ 16627649 := by rw [pow_add]
          _ = 15318418251 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 17026712993) ^ 66510597 = 3459555881 := by
        calc
          (3 : ZMod 17026712993) ^ 66510597 = (3 : ZMod 17026712993) ^ (33255298 + 33255298 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 33255298 * (3 : ZMod 17026712993) ^ 33255298) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 3459555881 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 17026712993) ^ 133021195 = 8403528898 := by
        calc
          (3 : ZMod 17026712993) ^ 133021195 = (3 : ZMod 17026712993) ^ (66510597 + 66510597 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 66510597 * (3 : ZMod 17026712993) ^ 66510597) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 8403528898 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 17026712993) ^ 266042390 = 16090384901 := by
        calc
          (3 : ZMod 17026712993) ^ 266042390 = (3 : ZMod 17026712993) ^ (133021195 + 133021195) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 133021195 * (3 : ZMod 17026712993) ^ 133021195 := by rw [pow_add]
          _ = 16090384901 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 17026712993) ^ 532084781 = 7790188363 := by
        calc
          (3 : ZMod 17026712993) ^ 532084781 = (3 : ZMod 17026712993) ^ (266042390 + 266042390 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 266042390 * (3 : ZMod 17026712993) ^ 266042390) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 7790188363 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 17026712993) ^ 1064169562 = 9735660195 := by
        calc
          (3 : ZMod 17026712993) ^ 1064169562 = (3 : ZMod 17026712993) ^ (532084781 + 532084781) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 532084781 * (3 : ZMod 17026712993) ^ 532084781 := by rw [pow_add]
          _ = 9735660195 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 17026712993) ^ 2128339124 = 11265349801 := by
        calc
          (3 : ZMod 17026712993) ^ 2128339124 = (3 : ZMod 17026712993) ^ (1064169562 + 1064169562) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 1064169562 * (3 : ZMod 17026712993) ^ 1064169562 := by rw [pow_add]
          _ = 11265349801 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 17026712993) ^ 4256678248 = 683342389 := by
        calc
          (3 : ZMod 17026712993) ^ 4256678248 = (3 : ZMod 17026712993) ^ (2128339124 + 2128339124) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 2128339124 * (3 : ZMod 17026712993) ^ 2128339124 := by rw [pow_add]
          _ = 683342389 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 17026712993) ^ 8513356496 = 17026712992 := by
        calc
          (3 : ZMod 17026712993) ^ 8513356496 = (3 : ZMod 17026712993) ^ (4256678248 + 4256678248) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 4256678248 * (3 : ZMod 17026712993) ^ 4256678248 := by rw [pow_add]
          _ = 17026712992 := by rw [factor_0_31]; decide
      change (3 : ZMod 17026712993) ^ 8513356496 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (3 : ZMod 17026712993) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 17026712993) ^ 3 = 27 := by
        calc
          (3 : ZMod 17026712993) ^ 3 = (3 : ZMod 17026712993) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 1 * (3 : ZMod 17026712993) ^ 1) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 17026712993) ^ 6 = 729 := by
        calc
          (3 : ZMod 17026712993) ^ 6 = (3 : ZMod 17026712993) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 3 * (3 : ZMod 17026712993) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 17026712993) ^ 12 = 531441 := by
        calc
          (3 : ZMod 17026712993) ^ 12 = (3 : ZMod 17026712993) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 6 * (3 : ZMod 17026712993) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 17026712993) ^ 25 = 12979672786 := by
        calc
          (3 : ZMod 17026712993) ^ 25 = (3 : ZMod 17026712993) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 12 * (3 : ZMod 17026712993) ^ 12) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 12979672786 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 17026712993) ^ 51 = 4455808582 := by
        calc
          (3 : ZMod 17026712993) ^ 51 = (3 : ZMod 17026712993) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 25 * (3 : ZMod 17026712993) ^ 25) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 4455808582 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 17026712993) ^ 103 = 3535886611 := by
        calc
          (3 : ZMod 17026712993) ^ 103 = (3 : ZMod 17026712993) ^ (51 + 51 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 51 * (3 : ZMod 17026712993) ^ 51) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 3535886611 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 17026712993) ^ 206 = 3171083370 := by
        calc
          (3 : ZMod 17026712993) ^ 206 = (3 : ZMod 17026712993) ^ (103 + 103) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 103 * (3 : ZMod 17026712993) ^ 103 := by rw [pow_add]
          _ = 3171083370 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 17026712993) ^ 412 = 5521186815 := by
        calc
          (3 : ZMod 17026712993) ^ 412 = (3 : ZMod 17026712993) ^ (206 + 206) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 206 * (3 : ZMod 17026712993) ^ 206 := by rw [pow_add]
          _ = 5521186815 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 17026712993) ^ 824 = 2478375498 := by
        calc
          (3 : ZMod 17026712993) ^ 824 = (3 : ZMod 17026712993) ^ (412 + 412) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 412 * (3 : ZMod 17026712993) ^ 412 := by rw [pow_add]
          _ = 2478375498 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 17026712993) ^ 1648 = 10148552896 := by
        calc
          (3 : ZMod 17026712993) ^ 1648 = (3 : ZMod 17026712993) ^ (824 + 824) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 824 * (3 : ZMod 17026712993) ^ 824 := by rw [pow_add]
          _ = 10148552896 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 17026712993) ^ 3297 = 15271044494 := by
        calc
          (3 : ZMod 17026712993) ^ 3297 = (3 : ZMod 17026712993) ^ (1648 + 1648 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 1648 * (3 : ZMod 17026712993) ^ 1648) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 15271044494 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 17026712993) ^ 6595 = 8295296098 := by
        calc
          (3 : ZMod 17026712993) ^ 6595 = (3 : ZMod 17026712993) ^ (3297 + 3297 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 3297 * (3 : ZMod 17026712993) ^ 3297) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 8295296098 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 17026712993) ^ 13191 = 6086638152 := by
        calc
          (3 : ZMod 17026712993) ^ 13191 = (3 : ZMod 17026712993) ^ (6595 + 6595 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 6595 * (3 : ZMod 17026712993) ^ 6595) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 6086638152 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 17026712993) ^ 26382 = 2983693761 := by
        calc
          (3 : ZMod 17026712993) ^ 26382 = (3 : ZMod 17026712993) ^ (13191 + 13191) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 13191 * (3 : ZMod 17026712993) ^ 13191 := by rw [pow_add]
          _ = 2983693761 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 17026712993) ^ 52765 = 12679745629 := by
        calc
          (3 : ZMod 17026712993) ^ 52765 = (3 : ZMod 17026712993) ^ (26382 + 26382 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 26382 * (3 : ZMod 17026712993) ^ 26382) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 12679745629 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 17026712993) ^ 105530 = 5605106824 := by
        calc
          (3 : ZMod 17026712993) ^ 105530 = (3 : ZMod 17026712993) ^ (52765 + 52765) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 52765 * (3 : ZMod 17026712993) ^ 52765 := by rw [pow_add]
          _ = 5605106824 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 17026712993) ^ 211061 = 6472492337 := by
        calc
          (3 : ZMod 17026712993) ^ 211061 = (3 : ZMod 17026712993) ^ (105530 + 105530 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 105530 * (3 : ZMod 17026712993) ^ 105530) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 6472492337 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 17026712993) ^ 422122 = 15399248556 := by
        calc
          (3 : ZMod 17026712993) ^ 422122 = (3 : ZMod 17026712993) ^ (211061 + 211061) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 211061 * (3 : ZMod 17026712993) ^ 211061 := by rw [pow_add]
          _ = 15399248556 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 17026712993) ^ 844244 = 10403847584 := by
        calc
          (3 : ZMod 17026712993) ^ 844244 = (3 : ZMod 17026712993) ^ (422122 + 422122) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 422122 * (3 : ZMod 17026712993) ^ 422122 := by rw [pow_add]
          _ = 10403847584 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 17026712993) ^ 1688488 = 10801596750 := by
        calc
          (3 : ZMod 17026712993) ^ 1688488 = (3 : ZMod 17026712993) ^ (844244 + 844244) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 844244 * (3 : ZMod 17026712993) ^ 844244 := by rw [pow_add]
          _ = 10801596750 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 17026712993) ^ 3376976 = 13664559352 := by
        calc
          (3 : ZMod 17026712993) ^ 3376976 = (3 : ZMod 17026712993) ^ (1688488 + 1688488) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 1688488 * (3 : ZMod 17026712993) ^ 1688488 := by rw [pow_add]
          _ = 13664559352 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 17026712993) ^ 6753952 = 4201643290 := by
        calc
          (3 : ZMod 17026712993) ^ 6753952 = (3 : ZMod 17026712993) ^ (3376976 + 3376976) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 3376976 * (3 : ZMod 17026712993) ^ 3376976 := by rw [pow_add]
          _ = 4201643290 := by rw [factor_1_21]; decide
      change (3 : ZMod 17026712993) ^ 6753952 ≠ 1
      rw [factor_1_22]
      decide
    ·
      have factor_2_0 : (3 : ZMod 17026712993) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 17026712993) ^ 2 = 9 := by
        calc
          (3 : ZMod 17026712993) ^ 2 = (3 : ZMod 17026712993) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 1 * (3 : ZMod 17026712993) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 17026712993) ^ 4 = 81 := by
        calc
          (3 : ZMod 17026712993) ^ 4 = (3 : ZMod 17026712993) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 2 * (3 : ZMod 17026712993) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 17026712993) ^ 9 = 19683 := by
        calc
          (3 : ZMod 17026712993) ^ 9 = (3 : ZMod 17026712993) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 4 * (3 : ZMod 17026712993) ^ 4) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 17026712993) ^ 19 = 1162261467 := by
        calc
          (3 : ZMod 17026712993) ^ 19 = (3 : ZMod 17026712993) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 9 * (3 : ZMod 17026712993) ^ 9) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 1162261467 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 17026712993) ^ 39 = 1894396446 := by
        calc
          (3 : ZMod 17026712993) ^ 39 = (3 : ZMod 17026712993) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 19 * (3 : ZMod 17026712993) ^ 19) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 1894396446 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 17026712993) ^ 78 = 8488299147 := by
        calc
          (3 : ZMod 17026712993) ^ 78 = (3 : ZMod 17026712993) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 39 * (3 : ZMod 17026712993) ^ 39 := by rw [pow_add]
          _ = 8488299147 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 17026712993) ^ 157 = 2370297088 := by
        calc
          (3 : ZMod 17026712993) ^ 157 = (3 : ZMod 17026712993) ^ (78 + 78 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 78 * (3 : ZMod 17026712993) ^ 78) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 2370297088 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 17026712993) ^ 315 = 6372216915 := by
        calc
          (3 : ZMod 17026712993) ^ 315 = (3 : ZMod 17026712993) ^ (157 + 157 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 157 * (3 : ZMod 17026712993) ^ 157) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 6372216915 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 17026712993) ^ 630 = 14025530783 := by
        calc
          (3 : ZMod 17026712993) ^ 630 = (3 : ZMod 17026712993) ^ (315 + 315) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 315 * (3 : ZMod 17026712993) ^ 315 := by rw [pow_add]
          _ = 14025530783 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 17026712993) ^ 1260 = 6622854085 := by
        calc
          (3 : ZMod 17026712993) ^ 1260 = (3 : ZMod 17026712993) ^ (630 + 630) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 630 * (3 : ZMod 17026712993) ^ 630 := by rw [pow_add]
          _ = 6622854085 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 17026712993) ^ 2521 = 13766406093 := by
        calc
          (3 : ZMod 17026712993) ^ 2521 = (3 : ZMod 17026712993) ^ (1260 + 1260 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = ((3 : ZMod 17026712993) ^ 1260 * (3 : ZMod 17026712993) ^ 1260) * (3 : ZMod 17026712993) := by rw [pow_succ, pow_add]
          _ = 13766406093 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 17026712993) ^ 5042 = 12549501704 := by
        calc
          (3 : ZMod 17026712993) ^ 5042 = (3 : ZMod 17026712993) ^ (2521 + 2521) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 2521 * (3 : ZMod 17026712993) ^ 2521 := by rw [pow_add]
          _ = 12549501704 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 17026712993) ^ 10084 = 15972543776 := by
        calc
          (3 : ZMod 17026712993) ^ 10084 = (3 : ZMod 17026712993) ^ (5042 + 5042) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 5042 * (3 : ZMod 17026712993) ^ 5042 := by rw [pow_add]
          _ = 15972543776 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 17026712993) ^ 20168 = 436094085 := by
        calc
          (3 : ZMod 17026712993) ^ 20168 = (3 : ZMod 17026712993) ^ (10084 + 10084) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 10084 * (3 : ZMod 17026712993) ^ 10084 := by rw [pow_add]
          _ = 436094085 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 17026712993) ^ 40336 = 2054963976 := by
        calc
          (3 : ZMod 17026712993) ^ 40336 = (3 : ZMod 17026712993) ^ (20168 + 20168) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 20168 * (3 : ZMod 17026712993) ^ 20168 := by rw [pow_add]
          _ = 2054963976 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 17026712993) ^ 80672 = 5854441225 := by
        calc
          (3 : ZMod 17026712993) ^ 80672 = (3 : ZMod 17026712993) ^ (40336 + 40336) :=
            congrArg (fun n : ℕ => (3 : ZMod 17026712993) ^ n) (by norm_num)
          _ = (3 : ZMod 17026712993) ^ 40336 * (3 : ZMod 17026712993) ^ 40336 := by rw [pow_add]
          _ = 5854441225 := by rw [factor_2_15]; decide
      change (3 : ZMod 17026712993) ^ 80672 ≠ 1
      rw [factor_2_16]
      decide

#print axioms prime_lucas_17026712993

end TotientTailPeriodKiller
end Erdos249257
