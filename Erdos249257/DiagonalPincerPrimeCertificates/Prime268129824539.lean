import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_268129824539 : Nat.Prime 268129824539 := by
  apply lucas_primality 268129824539 (2 : ZMod 268129824539)
  ·
      have fermat_0 : (2 : ZMod 268129824539) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 268129824539) ^ 3 = 8 := by
        calc
          (2 : ZMod 268129824539) ^ 3 = (2 : ZMod 268129824539) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 1 * (2 : ZMod 268129824539) ^ 1) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 268129824539) ^ 7 = 128 := by
        calc
          (2 : ZMod 268129824539) ^ 7 = (2 : ZMod 268129824539) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 3 * (2 : ZMod 268129824539) ^ 3) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 268129824539) ^ 15 = 32768 := by
        calc
          (2 : ZMod 268129824539) ^ 15 = (2 : ZMod 268129824539) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 7 * (2 : ZMod 268129824539) ^ 7) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 268129824539) ^ 31 = 2147483648 := by
        calc
          (2 : ZMod 268129824539) ^ 31 = (2 : ZMod 268129824539) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 15 * (2 : ZMod 268129824539) ^ 15) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 2147483648 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 268129824539) ^ 62 = 239630259815 := by
        calc
          (2 : ZMod 268129824539) ^ 62 = (2 : ZMod 268129824539) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 31 * (2 : ZMod 268129824539) ^ 31 := by rw [pow_add]
          _ = 239630259815 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 268129824539) ^ 124 = 49495345705 := by
        calc
          (2 : ZMod 268129824539) ^ 124 = (2 : ZMod 268129824539) ^ (62 + 62) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 62 * (2 : ZMod 268129824539) ^ 62 := by rw [pow_add]
          _ = 49495345705 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 268129824539) ^ 249 = 116797964670 := by
        calc
          (2 : ZMod 268129824539) ^ 249 = (2 : ZMod 268129824539) ^ (124 + 124 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 124 * (2 : ZMod 268129824539) ^ 124) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 116797964670 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 268129824539) ^ 499 = 197042278516 := by
        calc
          (2 : ZMod 268129824539) ^ 499 = (2 : ZMod 268129824539) ^ (249 + 249 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 249 * (2 : ZMod 268129824539) ^ 249) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 197042278516 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 268129824539) ^ 998 = 150451920689 := by
        calc
          (2 : ZMod 268129824539) ^ 998 = (2 : ZMod 268129824539) ^ (499 + 499) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 499 * (2 : ZMod 268129824539) ^ 499 := by rw [pow_add]
          _ = 150451920689 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 268129824539) ^ 1997 = 22326903940 := by
        calc
          (2 : ZMod 268129824539) ^ 1997 = (2 : ZMod 268129824539) ^ (998 + 998 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 998 * (2 : ZMod 268129824539) ^ 998) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 22326903940 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 268129824539) ^ 3995 = 151954718251 := by
        calc
          (2 : ZMod 268129824539) ^ 3995 = (2 : ZMod 268129824539) ^ (1997 + 1997 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 1997 * (2 : ZMod 268129824539) ^ 1997) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 151954718251 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 268129824539) ^ 7990 = 222718492634 := by
        calc
          (2 : ZMod 268129824539) ^ 7990 = (2 : ZMod 268129824539) ^ (3995 + 3995) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 3995 * (2 : ZMod 268129824539) ^ 3995 := by rw [pow_add]
          _ = 222718492634 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 268129824539) ^ 15981 = 170226746130 := by
        calc
          (2 : ZMod 268129824539) ^ 15981 = (2 : ZMod 268129824539) ^ (7990 + 7990 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 7990 * (2 : ZMod 268129824539) ^ 7990) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 170226746130 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 268129824539) ^ 31963 = 58553306053 := by
        calc
          (2 : ZMod 268129824539) ^ 31963 = (2 : ZMod 268129824539) ^ (15981 + 15981 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 15981 * (2 : ZMod 268129824539) ^ 15981) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 58553306053 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 268129824539) ^ 63927 = 247656647089 := by
        calc
          (2 : ZMod 268129824539) ^ 63927 = (2 : ZMod 268129824539) ^ (31963 + 31963 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 31963 * (2 : ZMod 268129824539) ^ 31963) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 247656647089 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 268129824539) ^ 127854 = 138614049585 := by
        calc
          (2 : ZMod 268129824539) ^ 127854 = (2 : ZMod 268129824539) ^ (63927 + 63927) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 63927 * (2 : ZMod 268129824539) ^ 63927 := by rw [pow_add]
          _ = 138614049585 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 268129824539) ^ 255708 = 127362453891 := by
        calc
          (2 : ZMod 268129824539) ^ 255708 = (2 : ZMod 268129824539) ^ (127854 + 127854) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 127854 * (2 : ZMod 268129824539) ^ 127854 := by rw [pow_add]
          _ = 127362453891 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 268129824539) ^ 511417 = 80151482876 := by
        calc
          (2 : ZMod 268129824539) ^ 511417 = (2 : ZMod 268129824539) ^ (255708 + 255708 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 255708 * (2 : ZMod 268129824539) ^ 255708) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 80151482876 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 268129824539) ^ 1022834 = 119656301686 := by
        calc
          (2 : ZMod 268129824539) ^ 1022834 = (2 : ZMod 268129824539) ^ (511417 + 511417) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 511417 * (2 : ZMod 268129824539) ^ 511417 := by rw [pow_add]
          _ = 119656301686 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 268129824539) ^ 2045668 = 16579928606 := by
        calc
          (2 : ZMod 268129824539) ^ 2045668 = (2 : ZMod 268129824539) ^ (1022834 + 1022834) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 1022834 * (2 : ZMod 268129824539) ^ 1022834 := by rw [pow_add]
          _ = 16579928606 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 268129824539) ^ 4091336 = 162545091657 := by
        calc
          (2 : ZMod 268129824539) ^ 4091336 = (2 : ZMod 268129824539) ^ (2045668 + 2045668) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 2045668 * (2 : ZMod 268129824539) ^ 2045668 := by rw [pow_add]
          _ = 162545091657 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 268129824539) ^ 8182672 = 140623872880 := by
        calc
          (2 : ZMod 268129824539) ^ 8182672 = (2 : ZMod 268129824539) ^ (4091336 + 4091336) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 4091336 * (2 : ZMod 268129824539) ^ 4091336 := by rw [pow_add]
          _ = 140623872880 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 268129824539) ^ 16365345 = 19312211655 := by
        calc
          (2 : ZMod 268129824539) ^ 16365345 = (2 : ZMod 268129824539) ^ (8182672 + 8182672 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 8182672 * (2 : ZMod 268129824539) ^ 8182672) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 19312211655 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 268129824539) ^ 32730691 = 74978602357 := by
        calc
          (2 : ZMod 268129824539) ^ 32730691 = (2 : ZMod 268129824539) ^ (16365345 + 16365345 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 16365345 * (2 : ZMod 268129824539) ^ 16365345) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 74978602357 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 268129824539) ^ 65461382 = 250537246759 := by
        calc
          (2 : ZMod 268129824539) ^ 65461382 = (2 : ZMod 268129824539) ^ (32730691 + 32730691) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 32730691 * (2 : ZMod 268129824539) ^ 32730691 := by rw [pow_add]
          _ = 250537246759 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 268129824539) ^ 130922765 = 93981021865 := by
        calc
          (2 : ZMod 268129824539) ^ 130922765 = (2 : ZMod 268129824539) ^ (65461382 + 65461382 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 65461382 * (2 : ZMod 268129824539) ^ 65461382) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 93981021865 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 268129824539) ^ 261845531 = 209623321987 := by
        calc
          (2 : ZMod 268129824539) ^ 261845531 = (2 : ZMod 268129824539) ^ (130922765 + 130922765 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 130922765 * (2 : ZMod 268129824539) ^ 130922765) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 209623321987 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 268129824539) ^ 523691063 = 75592883483 := by
        calc
          (2 : ZMod 268129824539) ^ 523691063 = (2 : ZMod 268129824539) ^ (261845531 + 261845531 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 261845531 * (2 : ZMod 268129824539) ^ 261845531) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 75592883483 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 268129824539) ^ 1047382127 = 77261879196 := by
        calc
          (2 : ZMod 268129824539) ^ 1047382127 = (2 : ZMod 268129824539) ^ (523691063 + 523691063 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 523691063 * (2 : ZMod 268129824539) ^ 523691063) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 77261879196 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 268129824539) ^ 2094764254 = 161725042220 := by
        calc
          (2 : ZMod 268129824539) ^ 2094764254 = (2 : ZMod 268129824539) ^ (1047382127 + 1047382127) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 1047382127 * (2 : ZMod 268129824539) ^ 1047382127 := by rw [pow_add]
          _ = 161725042220 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 268129824539) ^ 4189528508 = 10347961665 := by
        calc
          (2 : ZMod 268129824539) ^ 4189528508 = (2 : ZMod 268129824539) ^ (2094764254 + 2094764254) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 2094764254 * (2 : ZMod 268129824539) ^ 2094764254 := by rw [pow_add]
          _ = 10347961665 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 268129824539) ^ 8379057016 = 248333829104 := by
        calc
          (2 : ZMod 268129824539) ^ 8379057016 = (2 : ZMod 268129824539) ^ (4189528508 + 4189528508) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 4189528508 * (2 : ZMod 268129824539) ^ 4189528508 := by rw [pow_add]
          _ = 248333829104 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 268129824539) ^ 16758114033 = 103635421658 := by
        calc
          (2 : ZMod 268129824539) ^ 16758114033 = (2 : ZMod 268129824539) ^ (8379057016 + 8379057016 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 8379057016 * (2 : ZMod 268129824539) ^ 8379057016) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 103635421658 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 268129824539) ^ 33516228067 = 81695216006 := by
        calc
          (2 : ZMod 268129824539) ^ 33516228067 = (2 : ZMod 268129824539) ^ (16758114033 + 16758114033 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 16758114033 * (2 : ZMod 268129824539) ^ 16758114033) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 81695216006 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 268129824539) ^ 67032456134 = 124195612826 := by
        calc
          (2 : ZMod 268129824539) ^ 67032456134 = (2 : ZMod 268129824539) ^ (33516228067 + 33516228067) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 33516228067 * (2 : ZMod 268129824539) ^ 33516228067 := by rw [pow_add]
          _ = 124195612826 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 268129824539) ^ 134064912269 = 268129824538 := by
        calc
          (2 : ZMod 268129824539) ^ 134064912269 = (2 : ZMod 268129824539) ^ (67032456134 + 67032456134 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 67032456134 * (2 : ZMod 268129824539) ^ 67032456134) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 268129824538 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 268129824539) ^ 268129824538 = 1 := by
        calc
          (2 : ZMod 268129824539) ^ 268129824538 = (2 : ZMod 268129824539) ^ (134064912269 + 134064912269) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 134064912269 * (2 : ZMod 268129824539) ^ 134064912269 := by rw [pow_add]
          _ = 1 := by rw [fermat_36]; decide
      simpa using fermat_37
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (41, 1), (101, 1), (32375009, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (41, 1), (101, 1), (32375009, 1)] : List FactorBlock).map factorBlockValue).prod = 268129824539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 268129824539) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 268129824539) ^ 3 = 8 := by
        calc
          (2 : ZMod 268129824539) ^ 3 = (2 : ZMod 268129824539) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 1 * (2 : ZMod 268129824539) ^ 1) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 268129824539) ^ 7 = 128 := by
        calc
          (2 : ZMod 268129824539) ^ 7 = (2 : ZMod 268129824539) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 3 * (2 : ZMod 268129824539) ^ 3) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 268129824539) ^ 15 = 32768 := by
        calc
          (2 : ZMod 268129824539) ^ 15 = (2 : ZMod 268129824539) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 7 * (2 : ZMod 268129824539) ^ 7) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 268129824539) ^ 31 = 2147483648 := by
        calc
          (2 : ZMod 268129824539) ^ 31 = (2 : ZMod 268129824539) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 15 * (2 : ZMod 268129824539) ^ 15) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 2147483648 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 268129824539) ^ 62 = 239630259815 := by
        calc
          (2 : ZMod 268129824539) ^ 62 = (2 : ZMod 268129824539) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 31 * (2 : ZMod 268129824539) ^ 31 := by rw [pow_add]
          _ = 239630259815 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 268129824539) ^ 124 = 49495345705 := by
        calc
          (2 : ZMod 268129824539) ^ 124 = (2 : ZMod 268129824539) ^ (62 + 62) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 62 * (2 : ZMod 268129824539) ^ 62 := by rw [pow_add]
          _ = 49495345705 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 268129824539) ^ 249 = 116797964670 := by
        calc
          (2 : ZMod 268129824539) ^ 249 = (2 : ZMod 268129824539) ^ (124 + 124 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 124 * (2 : ZMod 268129824539) ^ 124) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 116797964670 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 268129824539) ^ 499 = 197042278516 := by
        calc
          (2 : ZMod 268129824539) ^ 499 = (2 : ZMod 268129824539) ^ (249 + 249 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 249 * (2 : ZMod 268129824539) ^ 249) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 197042278516 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 268129824539) ^ 998 = 150451920689 := by
        calc
          (2 : ZMod 268129824539) ^ 998 = (2 : ZMod 268129824539) ^ (499 + 499) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 499 * (2 : ZMod 268129824539) ^ 499 := by rw [pow_add]
          _ = 150451920689 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 268129824539) ^ 1997 = 22326903940 := by
        calc
          (2 : ZMod 268129824539) ^ 1997 = (2 : ZMod 268129824539) ^ (998 + 998 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 998 * (2 : ZMod 268129824539) ^ 998) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 22326903940 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 268129824539) ^ 3995 = 151954718251 := by
        calc
          (2 : ZMod 268129824539) ^ 3995 = (2 : ZMod 268129824539) ^ (1997 + 1997 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 1997 * (2 : ZMod 268129824539) ^ 1997) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 151954718251 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 268129824539) ^ 7990 = 222718492634 := by
        calc
          (2 : ZMod 268129824539) ^ 7990 = (2 : ZMod 268129824539) ^ (3995 + 3995) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 3995 * (2 : ZMod 268129824539) ^ 3995 := by rw [pow_add]
          _ = 222718492634 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 268129824539) ^ 15981 = 170226746130 := by
        calc
          (2 : ZMod 268129824539) ^ 15981 = (2 : ZMod 268129824539) ^ (7990 + 7990 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 7990 * (2 : ZMod 268129824539) ^ 7990) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 170226746130 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 268129824539) ^ 31963 = 58553306053 := by
        calc
          (2 : ZMod 268129824539) ^ 31963 = (2 : ZMod 268129824539) ^ (15981 + 15981 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 15981 * (2 : ZMod 268129824539) ^ 15981) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 58553306053 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 268129824539) ^ 63927 = 247656647089 := by
        calc
          (2 : ZMod 268129824539) ^ 63927 = (2 : ZMod 268129824539) ^ (31963 + 31963 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 31963 * (2 : ZMod 268129824539) ^ 31963) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 247656647089 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 268129824539) ^ 127854 = 138614049585 := by
        calc
          (2 : ZMod 268129824539) ^ 127854 = (2 : ZMod 268129824539) ^ (63927 + 63927) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 63927 * (2 : ZMod 268129824539) ^ 63927 := by rw [pow_add]
          _ = 138614049585 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 268129824539) ^ 255708 = 127362453891 := by
        calc
          (2 : ZMod 268129824539) ^ 255708 = (2 : ZMod 268129824539) ^ (127854 + 127854) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 127854 * (2 : ZMod 268129824539) ^ 127854 := by rw [pow_add]
          _ = 127362453891 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 268129824539) ^ 511417 = 80151482876 := by
        calc
          (2 : ZMod 268129824539) ^ 511417 = (2 : ZMod 268129824539) ^ (255708 + 255708 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 255708 * (2 : ZMod 268129824539) ^ 255708) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 80151482876 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 268129824539) ^ 1022834 = 119656301686 := by
        calc
          (2 : ZMod 268129824539) ^ 1022834 = (2 : ZMod 268129824539) ^ (511417 + 511417) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 511417 * (2 : ZMod 268129824539) ^ 511417 := by rw [pow_add]
          _ = 119656301686 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 268129824539) ^ 2045668 = 16579928606 := by
        calc
          (2 : ZMod 268129824539) ^ 2045668 = (2 : ZMod 268129824539) ^ (1022834 + 1022834) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 1022834 * (2 : ZMod 268129824539) ^ 1022834 := by rw [pow_add]
          _ = 16579928606 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 268129824539) ^ 4091336 = 162545091657 := by
        calc
          (2 : ZMod 268129824539) ^ 4091336 = (2 : ZMod 268129824539) ^ (2045668 + 2045668) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 2045668 * (2 : ZMod 268129824539) ^ 2045668 := by rw [pow_add]
          _ = 162545091657 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 268129824539) ^ 8182672 = 140623872880 := by
        calc
          (2 : ZMod 268129824539) ^ 8182672 = (2 : ZMod 268129824539) ^ (4091336 + 4091336) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 4091336 * (2 : ZMod 268129824539) ^ 4091336 := by rw [pow_add]
          _ = 140623872880 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 268129824539) ^ 16365345 = 19312211655 := by
        calc
          (2 : ZMod 268129824539) ^ 16365345 = (2 : ZMod 268129824539) ^ (8182672 + 8182672 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 8182672 * (2 : ZMod 268129824539) ^ 8182672) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 19312211655 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 268129824539) ^ 32730691 = 74978602357 := by
        calc
          (2 : ZMod 268129824539) ^ 32730691 = (2 : ZMod 268129824539) ^ (16365345 + 16365345 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 16365345 * (2 : ZMod 268129824539) ^ 16365345) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 74978602357 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 268129824539) ^ 65461382 = 250537246759 := by
        calc
          (2 : ZMod 268129824539) ^ 65461382 = (2 : ZMod 268129824539) ^ (32730691 + 32730691) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 32730691 * (2 : ZMod 268129824539) ^ 32730691 := by rw [pow_add]
          _ = 250537246759 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 268129824539) ^ 130922765 = 93981021865 := by
        calc
          (2 : ZMod 268129824539) ^ 130922765 = (2 : ZMod 268129824539) ^ (65461382 + 65461382 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 65461382 * (2 : ZMod 268129824539) ^ 65461382) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 93981021865 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 268129824539) ^ 261845531 = 209623321987 := by
        calc
          (2 : ZMod 268129824539) ^ 261845531 = (2 : ZMod 268129824539) ^ (130922765 + 130922765 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 130922765 * (2 : ZMod 268129824539) ^ 130922765) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 209623321987 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 268129824539) ^ 523691063 = 75592883483 := by
        calc
          (2 : ZMod 268129824539) ^ 523691063 = (2 : ZMod 268129824539) ^ (261845531 + 261845531 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 261845531 * (2 : ZMod 268129824539) ^ 261845531) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 75592883483 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 268129824539) ^ 1047382127 = 77261879196 := by
        calc
          (2 : ZMod 268129824539) ^ 1047382127 = (2 : ZMod 268129824539) ^ (523691063 + 523691063 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 523691063 * (2 : ZMod 268129824539) ^ 523691063) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 77261879196 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 268129824539) ^ 2094764254 = 161725042220 := by
        calc
          (2 : ZMod 268129824539) ^ 2094764254 = (2 : ZMod 268129824539) ^ (1047382127 + 1047382127) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 1047382127 * (2 : ZMod 268129824539) ^ 1047382127 := by rw [pow_add]
          _ = 161725042220 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 268129824539) ^ 4189528508 = 10347961665 := by
        calc
          (2 : ZMod 268129824539) ^ 4189528508 = (2 : ZMod 268129824539) ^ (2094764254 + 2094764254) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 2094764254 * (2 : ZMod 268129824539) ^ 2094764254 := by rw [pow_add]
          _ = 10347961665 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 268129824539) ^ 8379057016 = 248333829104 := by
        calc
          (2 : ZMod 268129824539) ^ 8379057016 = (2 : ZMod 268129824539) ^ (4189528508 + 4189528508) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 4189528508 * (2 : ZMod 268129824539) ^ 4189528508 := by rw [pow_add]
          _ = 248333829104 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 268129824539) ^ 16758114033 = 103635421658 := by
        calc
          (2 : ZMod 268129824539) ^ 16758114033 = (2 : ZMod 268129824539) ^ (8379057016 + 8379057016 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 8379057016 * (2 : ZMod 268129824539) ^ 8379057016) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 103635421658 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 268129824539) ^ 33516228067 = 81695216006 := by
        calc
          (2 : ZMod 268129824539) ^ 33516228067 = (2 : ZMod 268129824539) ^ (16758114033 + 16758114033 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 16758114033 * (2 : ZMod 268129824539) ^ 16758114033) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 81695216006 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 268129824539) ^ 67032456134 = 124195612826 := by
        calc
          (2 : ZMod 268129824539) ^ 67032456134 = (2 : ZMod 268129824539) ^ (33516228067 + 33516228067) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 33516228067 * (2 : ZMod 268129824539) ^ 33516228067 := by rw [pow_add]
          _ = 124195612826 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 268129824539) ^ 134064912269 = 268129824538 := by
        calc
          (2 : ZMod 268129824539) ^ 134064912269 = (2 : ZMod 268129824539) ^ (67032456134 + 67032456134 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 67032456134 * (2 : ZMod 268129824539) ^ 67032456134) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 268129824538 := by rw [factor_0_35]; decide
      change (2 : ZMod 268129824539) ^ 134064912269 ≠ 1
      rw [factor_0_36]
      decide
    ·
      have factor_1_0 : (2 : ZMod 268129824539) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 268129824539) ^ 3 = 8 := by
        calc
          (2 : ZMod 268129824539) ^ 3 = (2 : ZMod 268129824539) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 1 * (2 : ZMod 268129824539) ^ 1) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 268129824539) ^ 6 = 64 := by
        calc
          (2 : ZMod 268129824539) ^ 6 = (2 : ZMod 268129824539) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 3 * (2 : ZMod 268129824539) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 268129824539) ^ 12 = 4096 := by
        calc
          (2 : ZMod 268129824539) ^ 12 = (2 : ZMod 268129824539) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 6 * (2 : ZMod 268129824539) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 268129824539) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 268129824539) ^ 24 = (2 : ZMod 268129824539) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 12 * (2 : ZMod 268129824539) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 268129824539) ^ 48 = 206790769245 := by
        calc
          (2 : ZMod 268129824539) ^ 48 = (2 : ZMod 268129824539) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 24 * (2 : ZMod 268129824539) ^ 24 := by rw [pow_add]
          _ = 206790769245 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 268129824539) ^ 97 = 257780767423 := by
        calc
          (2 : ZMod 268129824539) ^ 97 = (2 : ZMod 268129824539) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 48 * (2 : ZMod 268129824539) ^ 48) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 257780767423 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 268129824539) ^ 194 = 28421301034 := by
        calc
          (2 : ZMod 268129824539) ^ 194 = (2 : ZMod 268129824539) ^ (97 + 97) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 97 * (2 : ZMod 268129824539) ^ 97 := by rw [pow_add]
          _ = 28421301034 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 268129824539) ^ 389 = 256453388654 := by
        calc
          (2 : ZMod 268129824539) ^ 389 = (2 : ZMod 268129824539) ^ (194 + 194 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 194 * (2 : ZMod 268129824539) ^ 194) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 256453388654 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 268129824539) ^ 779 = 248046601512 := by
        calc
          (2 : ZMod 268129824539) ^ 779 = (2 : ZMod 268129824539) ^ (389 + 389 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 389 * (2 : ZMod 268129824539) ^ 389) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 248046601512 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 268129824539) ^ 1559 = 169654319583 := by
        calc
          (2 : ZMod 268129824539) ^ 1559 = (2 : ZMod 268129824539) ^ (779 + 779 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 779 * (2 : ZMod 268129824539) ^ 779) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 169654319583 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 268129824539) ^ 3118 = 221425014574 := by
        calc
          (2 : ZMod 268129824539) ^ 3118 = (2 : ZMod 268129824539) ^ (1559 + 1559) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 1559 * (2 : ZMod 268129824539) ^ 1559 := by rw [pow_add]
          _ = 221425014574 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 268129824539) ^ 6236 = 89719200691 := by
        calc
          (2 : ZMod 268129824539) ^ 6236 = (2 : ZMod 268129824539) ^ (3118 + 3118) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 3118 * (2 : ZMod 268129824539) ^ 3118 := by rw [pow_add]
          _ = 89719200691 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 268129824539) ^ 12473 = 235998256458 := by
        calc
          (2 : ZMod 268129824539) ^ 12473 = (2 : ZMod 268129824539) ^ (6236 + 6236 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 6236 * (2 : ZMod 268129824539) ^ 6236) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 235998256458 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 268129824539) ^ 24947 = 14581536102 := by
        calc
          (2 : ZMod 268129824539) ^ 24947 = (2 : ZMod 268129824539) ^ (12473 + 12473 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 12473 * (2 : ZMod 268129824539) ^ 12473) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 14581536102 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 268129824539) ^ 49894 = 177445733117 := by
        calc
          (2 : ZMod 268129824539) ^ 49894 = (2 : ZMod 268129824539) ^ (24947 + 24947) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 24947 * (2 : ZMod 268129824539) ^ 24947 := by rw [pow_add]
          _ = 177445733117 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 268129824539) ^ 99788 = 175266064594 := by
        calc
          (2 : ZMod 268129824539) ^ 99788 = (2 : ZMod 268129824539) ^ (49894 + 49894) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 49894 * (2 : ZMod 268129824539) ^ 49894 := by rw [pow_add]
          _ = 175266064594 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 268129824539) ^ 199577 = 84028453037 := by
        calc
          (2 : ZMod 268129824539) ^ 199577 = (2 : ZMod 268129824539) ^ (99788 + 99788 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 99788 * (2 : ZMod 268129824539) ^ 99788) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 84028453037 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 268129824539) ^ 399154 = 126868982667 := by
        calc
          (2 : ZMod 268129824539) ^ 399154 = (2 : ZMod 268129824539) ^ (199577 + 199577) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 199577 * (2 : ZMod 268129824539) ^ 199577 := by rw [pow_add]
          _ = 126868982667 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 268129824539) ^ 798309 = 258737056518 := by
        calc
          (2 : ZMod 268129824539) ^ 798309 = (2 : ZMod 268129824539) ^ (399154 + 399154 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 399154 * (2 : ZMod 268129824539) ^ 399154) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 258737056518 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 268129824539) ^ 1596619 = 87843238059 := by
        calc
          (2 : ZMod 268129824539) ^ 1596619 = (2 : ZMod 268129824539) ^ (798309 + 798309 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 798309 * (2 : ZMod 268129824539) ^ 798309) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 87843238059 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 268129824539) ^ 3193238 = 49855416736 := by
        calc
          (2 : ZMod 268129824539) ^ 3193238 = (2 : ZMod 268129824539) ^ (1596619 + 1596619) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 1596619 * (2 : ZMod 268129824539) ^ 1596619 := by rw [pow_add]
          _ = 49855416736 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 268129824539) ^ 6386476 = 265442678495 := by
        calc
          (2 : ZMod 268129824539) ^ 6386476 = (2 : ZMod 268129824539) ^ (3193238 + 3193238) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 3193238 * (2 : ZMod 268129824539) ^ 3193238 := by rw [pow_add]
          _ = 265442678495 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 268129824539) ^ 12772952 = 258510984901 := by
        calc
          (2 : ZMod 268129824539) ^ 12772952 = (2 : ZMod 268129824539) ^ (6386476 + 6386476) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 6386476 * (2 : ZMod 268129824539) ^ 6386476 := by rw [pow_add]
          _ = 258510984901 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 268129824539) ^ 25545905 = 103504058889 := by
        calc
          (2 : ZMod 268129824539) ^ 25545905 = (2 : ZMod 268129824539) ^ (12772952 + 12772952 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 12772952 * (2 : ZMod 268129824539) ^ 12772952) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 103504058889 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 268129824539) ^ 51091811 = 96512779596 := by
        calc
          (2 : ZMod 268129824539) ^ 51091811 = (2 : ZMod 268129824539) ^ (25545905 + 25545905 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 25545905 * (2 : ZMod 268129824539) ^ 25545905) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 96512779596 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 268129824539) ^ 102183622 = 106204441491 := by
        calc
          (2 : ZMod 268129824539) ^ 102183622 = (2 : ZMod 268129824539) ^ (51091811 + 51091811) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 51091811 * (2 : ZMod 268129824539) ^ 51091811 := by rw [pow_add]
          _ = 106204441491 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 268129824539) ^ 204367244 = 188761555233 := by
        calc
          (2 : ZMod 268129824539) ^ 204367244 = (2 : ZMod 268129824539) ^ (102183622 + 102183622) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 102183622 * (2 : ZMod 268129824539) ^ 102183622 := by rw [pow_add]
          _ = 188761555233 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 268129824539) ^ 408734488 = 264577982010 := by
        calc
          (2 : ZMod 268129824539) ^ 408734488 = (2 : ZMod 268129824539) ^ (204367244 + 204367244) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 204367244 * (2 : ZMod 268129824539) ^ 204367244 := by rw [pow_add]
          _ = 264577982010 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 268129824539) ^ 817468977 = 37857221757 := by
        calc
          (2 : ZMod 268129824539) ^ 817468977 = (2 : ZMod 268129824539) ^ (408734488 + 408734488 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 408734488 * (2 : ZMod 268129824539) ^ 408734488) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 37857221757 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 268129824539) ^ 1634937954 = 160688868731 := by
        calc
          (2 : ZMod 268129824539) ^ 1634937954 = (2 : ZMod 268129824539) ^ (817468977 + 817468977) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 817468977 * (2 : ZMod 268129824539) ^ 817468977 := by rw [pow_add]
          _ = 160688868731 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 268129824539) ^ 3269875909 = 44700843827 := by
        calc
          (2 : ZMod 268129824539) ^ 3269875909 = (2 : ZMod 268129824539) ^ (1634937954 + 1634937954 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 1634937954 * (2 : ZMod 268129824539) ^ 1634937954) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 44700843827 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 268129824539) ^ 6539751818 = 128379079909 := by
        calc
          (2 : ZMod 268129824539) ^ 6539751818 = (2 : ZMod 268129824539) ^ (3269875909 + 3269875909) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 3269875909 * (2 : ZMod 268129824539) ^ 3269875909 := by rw [pow_add]
          _ = 128379079909 := by rw [factor_1_31]; decide
      change (2 : ZMod 268129824539) ^ 6539751818 ≠ 1
      rw [factor_1_32]
      decide
    ·
      have factor_2_0 : (2 : ZMod 268129824539) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 268129824539) ^ 2 = 4 := by
        calc
          (2 : ZMod 268129824539) ^ 2 = (2 : ZMod 268129824539) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 1 * (2 : ZMod 268129824539) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 268129824539) ^ 4 = 16 := by
        calc
          (2 : ZMod 268129824539) ^ 4 = (2 : ZMod 268129824539) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 2 * (2 : ZMod 268129824539) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 268129824539) ^ 9 = 512 := by
        calc
          (2 : ZMod 268129824539) ^ 9 = (2 : ZMod 268129824539) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 4 * (2 : ZMod 268129824539) ^ 4) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 268129824539) ^ 19 = 524288 := by
        calc
          (2 : ZMod 268129824539) ^ 19 = (2 : ZMod 268129824539) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 9 * (2 : ZMod 268129824539) ^ 9) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 268129824539) ^ 39 = 13496164810 := by
        calc
          (2 : ZMod 268129824539) ^ 39 = (2 : ZMod 268129824539) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 19 * (2 : ZMod 268129824539) ^ 19) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 13496164810 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 268129824539) ^ 79 = 89767973220 := by
        calc
          (2 : ZMod 268129824539) ^ 79 = (2 : ZMod 268129824539) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 39 * (2 : ZMod 268129824539) ^ 39) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 89767973220 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 268129824539) ^ 158 = 232994264173 := by
        calc
          (2 : ZMod 268129824539) ^ 158 = (2 : ZMod 268129824539) ^ (79 + 79) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 79 * (2 : ZMod 268129824539) ^ 79 := by rw [pow_add]
          _ = 232994264173 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 268129824539) ^ 316 = 93508798788 := by
        calc
          (2 : ZMod 268129824539) ^ 316 = (2 : ZMod 268129824539) ^ (158 + 158) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 158 * (2 : ZMod 268129824539) ^ 158 := by rw [pow_add]
          _ = 93508798788 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 268129824539) ^ 632 = 97895465244 := by
        calc
          (2 : ZMod 268129824539) ^ 632 = (2 : ZMod 268129824539) ^ (316 + 316) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 316 * (2 : ZMod 268129824539) ^ 316 := by rw [pow_add]
          _ = 97895465244 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 268129824539) ^ 1265 = 242040010940 := by
        calc
          (2 : ZMod 268129824539) ^ 1265 = (2 : ZMod 268129824539) ^ (632 + 632 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 632 * (2 : ZMod 268129824539) ^ 632) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 242040010940 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 268129824539) ^ 2531 = 45236323686 := by
        calc
          (2 : ZMod 268129824539) ^ 2531 = (2 : ZMod 268129824539) ^ (1265 + 1265 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 1265 * (2 : ZMod 268129824539) ^ 1265) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 45236323686 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 268129824539) ^ 5063 = 122773629702 := by
        calc
          (2 : ZMod 268129824539) ^ 5063 = (2 : ZMod 268129824539) ^ (2531 + 2531 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 2531 * (2 : ZMod 268129824539) ^ 2531) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 122773629702 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 268129824539) ^ 10127 = 36800916950 := by
        calc
          (2 : ZMod 268129824539) ^ 10127 = (2 : ZMod 268129824539) ^ (5063 + 5063 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 5063 * (2 : ZMod 268129824539) ^ 5063) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 36800916950 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 268129824539) ^ 20254 = 253050803914 := by
        calc
          (2 : ZMod 268129824539) ^ 20254 = (2 : ZMod 268129824539) ^ (10127 + 10127) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 10127 * (2 : ZMod 268129824539) ^ 10127 := by rw [pow_add]
          _ = 253050803914 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 268129824539) ^ 40508 = 142107130982 := by
        calc
          (2 : ZMod 268129824539) ^ 40508 = (2 : ZMod 268129824539) ^ (20254 + 20254) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 20254 * (2 : ZMod 268129824539) ^ 20254 := by rw [pow_add]
          _ = 142107130982 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 268129824539) ^ 81016 = 104939248942 := by
        calc
          (2 : ZMod 268129824539) ^ 81016 = (2 : ZMod 268129824539) ^ (40508 + 40508) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 40508 * (2 : ZMod 268129824539) ^ 40508 := by rw [pow_add]
          _ = 104939248942 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 268129824539) ^ 162033 = 115265494822 := by
        calc
          (2 : ZMod 268129824539) ^ 162033 = (2 : ZMod 268129824539) ^ (81016 + 81016 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 81016 * (2 : ZMod 268129824539) ^ 81016) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 115265494822 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 268129824539) ^ 324066 = 115750669304 := by
        calc
          (2 : ZMod 268129824539) ^ 324066 = (2 : ZMod 268129824539) ^ (162033 + 162033) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 162033 * (2 : ZMod 268129824539) ^ 162033 := by rw [pow_add]
          _ = 115750669304 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 268129824539) ^ 648132 = 186581794080 := by
        calc
          (2 : ZMod 268129824539) ^ 648132 = (2 : ZMod 268129824539) ^ (324066 + 324066) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 324066 * (2 : ZMod 268129824539) ^ 324066 := by rw [pow_add]
          _ = 186581794080 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 268129824539) ^ 1296265 = 19215028903 := by
        calc
          (2 : ZMod 268129824539) ^ 1296265 = (2 : ZMod 268129824539) ^ (648132 + 648132 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 648132 * (2 : ZMod 268129824539) ^ 648132) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 19215028903 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 268129824539) ^ 2592530 = 9852422484 := by
        calc
          (2 : ZMod 268129824539) ^ 2592530 = (2 : ZMod 268129824539) ^ (1296265 + 1296265) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 1296265 * (2 : ZMod 268129824539) ^ 1296265 := by rw [pow_add]
          _ = 9852422484 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 268129824539) ^ 5185060 = 54353439809 := by
        calc
          (2 : ZMod 268129824539) ^ 5185060 = (2 : ZMod 268129824539) ^ (2592530 + 2592530) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 2592530 * (2 : ZMod 268129824539) ^ 2592530 := by rw [pow_add]
          _ = 54353439809 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 268129824539) ^ 10370120 = 110196238727 := by
        calc
          (2 : ZMod 268129824539) ^ 10370120 = (2 : ZMod 268129824539) ^ (5185060 + 5185060) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 5185060 * (2 : ZMod 268129824539) ^ 5185060 := by rw [pow_add]
          _ = 110196238727 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 268129824539) ^ 20740240 = 101088241169 := by
        calc
          (2 : ZMod 268129824539) ^ 20740240 = (2 : ZMod 268129824539) ^ (10370120 + 10370120) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 10370120 * (2 : ZMod 268129824539) ^ 10370120 := by rw [pow_add]
          _ = 101088241169 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 268129824539) ^ 41480480 = 19071369611 := by
        calc
          (2 : ZMod 268129824539) ^ 41480480 = (2 : ZMod 268129824539) ^ (20740240 + 20740240) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 20740240 * (2 : ZMod 268129824539) ^ 20740240 := by rw [pow_add]
          _ = 19071369611 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 268129824539) ^ 82960960 = 69017201650 := by
        calc
          (2 : ZMod 268129824539) ^ 82960960 = (2 : ZMod 268129824539) ^ (41480480 + 41480480) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 41480480 * (2 : ZMod 268129824539) ^ 41480480 := by rw [pow_add]
          _ = 69017201650 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 268129824539) ^ 165921921 = 11782729514 := by
        calc
          (2 : ZMod 268129824539) ^ 165921921 = (2 : ZMod 268129824539) ^ (82960960 + 82960960 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 82960960 * (2 : ZMod 268129824539) ^ 82960960) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 11782729514 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 268129824539) ^ 331843842 = 38360487130 := by
        calc
          (2 : ZMod 268129824539) ^ 331843842 = (2 : ZMod 268129824539) ^ (165921921 + 165921921) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 165921921 * (2 : ZMod 268129824539) ^ 165921921 := by rw [pow_add]
          _ = 38360487130 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 268129824539) ^ 663687684 = 35269693735 := by
        calc
          (2 : ZMod 268129824539) ^ 663687684 = (2 : ZMod 268129824539) ^ (331843842 + 331843842) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 331843842 * (2 : ZMod 268129824539) ^ 331843842 := by rw [pow_add]
          _ = 35269693735 := by rw [factor_2_28]; decide
      have factor_2_30 : (2 : ZMod 268129824539) ^ 1327375369 = 105788260619 := by
        calc
          (2 : ZMod 268129824539) ^ 1327375369 = (2 : ZMod 268129824539) ^ (663687684 + 663687684 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 663687684 * (2 : ZMod 268129824539) ^ 663687684) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 105788260619 := by rw [factor_2_29]; decide
      have factor_2_31 : (2 : ZMod 268129824539) ^ 2654750738 = 238824234838 := by
        calc
          (2 : ZMod 268129824539) ^ 2654750738 = (2 : ZMod 268129824539) ^ (1327375369 + 1327375369) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 1327375369 * (2 : ZMod 268129824539) ^ 1327375369 := by rw [pow_add]
          _ = 238824234838 := by rw [factor_2_30]; decide
      change (2 : ZMod 268129824539) ^ 2654750738 ≠ 1
      rw [factor_2_31]
      decide
    ·
      have factor_3_0 : (2 : ZMod 268129824539) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 268129824539) ^ 2 = 4 := by
        calc
          (2 : ZMod 268129824539) ^ 2 = (2 : ZMod 268129824539) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 1 * (2 : ZMod 268129824539) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 268129824539) ^ 4 = 16 := by
        calc
          (2 : ZMod 268129824539) ^ 4 = (2 : ZMod 268129824539) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 2 * (2 : ZMod 268129824539) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 268129824539) ^ 8 = 256 := by
        calc
          (2 : ZMod 268129824539) ^ 8 = (2 : ZMod 268129824539) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 4 * (2 : ZMod 268129824539) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 268129824539) ^ 16 = 65536 := by
        calc
          (2 : ZMod 268129824539) ^ 16 = (2 : ZMod 268129824539) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 8 * (2 : ZMod 268129824539) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 268129824539) ^ 32 = 4294967296 := by
        calc
          (2 : ZMod 268129824539) ^ 32 = (2 : ZMod 268129824539) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 16 * (2 : ZMod 268129824539) ^ 16 := by rw [pow_add]
          _ = 4294967296 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 268129824539) ^ 64 = 154131565643 := by
        calc
          (2 : ZMod 268129824539) ^ 64 = (2 : ZMod 268129824539) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 32 * (2 : ZMod 268129824539) ^ 32 := by rw [pow_add]
          _ = 154131565643 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 268129824539) ^ 129 = 243201939865 := by
        calc
          (2 : ZMod 268129824539) ^ 129 = (2 : ZMod 268129824539) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 64 * (2 : ZMod 268129824539) ^ 64) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 243201939865 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 268129824539) ^ 258 = 7607038843 := by
        calc
          (2 : ZMod 268129824539) ^ 258 = (2 : ZMod 268129824539) ^ (129 + 129) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 129 * (2 : ZMod 268129824539) ^ 129 := by rw [pow_add]
          _ = 7607038843 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 268129824539) ^ 517 = 117270631727 := by
        calc
          (2 : ZMod 268129824539) ^ 517 = (2 : ZMod 268129824539) ^ (258 + 258 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 258 * (2 : ZMod 268129824539) ^ 258) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 117270631727 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 268129824539) ^ 1035 = 135108760000 := by
        calc
          (2 : ZMod 268129824539) ^ 1035 = (2 : ZMod 268129824539) ^ (517 + 517 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 517 * (2 : ZMod 268129824539) ^ 517) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 135108760000 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 268129824539) ^ 2070 = 214435604735 := by
        calc
          (2 : ZMod 268129824539) ^ 2070 = (2 : ZMod 268129824539) ^ (1035 + 1035) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 1035 * (2 : ZMod 268129824539) ^ 1035 := by rw [pow_add]
          _ = 214435604735 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 268129824539) ^ 4141 = 239888025801 := by
        calc
          (2 : ZMod 268129824539) ^ 4141 = (2 : ZMod 268129824539) ^ (2070 + 2070 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = ((2 : ZMod 268129824539) ^ 2070 * (2 : ZMod 268129824539) ^ 2070) * (2 : ZMod 268129824539) := by rw [pow_succ, pow_add]
          _ = 239888025801 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 268129824539) ^ 8282 = 213920506654 := by
        calc
          (2 : ZMod 268129824539) ^ 8282 = (2 : ZMod 268129824539) ^ (4141 + 4141) :=
            congrArg (fun n : ℕ => (2 : ZMod 268129824539) ^ n) (by norm_num)
          _ = (2 : ZMod 268129824539) ^ 4141 * (2 : ZMod 268129824539) ^ 4141 := by rw [pow_add]
          _ = 213920506654 := by rw [factor_3_12]; decide
      change (2 : ZMod 268129824539) ^ 8282 ≠ 1
      rw [factor_3_13]
      decide

#print axioms prime_lucas_268129824539

end TotientTailPeriodKiller
end Erdos249257
