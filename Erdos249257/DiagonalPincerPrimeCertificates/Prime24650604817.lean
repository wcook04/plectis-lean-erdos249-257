import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_24650604817 : Nat.Prime 24650604817 := by
  apply lucas_primality 24650604817 (10 : ZMod 24650604817)
  ·
      have fermat_0 : (10 : ZMod 24650604817) ^ 1 = 10 := by norm_num
      have fermat_1 : (10 : ZMod 24650604817) ^ 2 = 100 := by
        calc
          (10 : ZMod 24650604817) ^ 2 = (10 : ZMod 24650604817) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 1 * (10 : ZMod 24650604817) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [fermat_0]; decide
      have fermat_2 : (10 : ZMod 24650604817) ^ 5 = 100000 := by
        calc
          (10 : ZMod 24650604817) ^ 5 = (10 : ZMod 24650604817) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 2 * (10 : ZMod 24650604817) ^ 2) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 100000 := by rw [fermat_1]; decide
      have fermat_3 : (10 : ZMod 24650604817) ^ 11 = 1397580732 := by
        calc
          (10 : ZMod 24650604817) ^ 11 = (10 : ZMod 24650604817) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 5 * (10 : ZMod 24650604817) ^ 5) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 1397580732 := by rw [fermat_2]; decide
      have fermat_4 : (10 : ZMod 24650604817) ^ 22 = 13971406800 := by
        calc
          (10 : ZMod 24650604817) ^ 22 = (10 : ZMod 24650604817) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 11 * (10 : ZMod 24650604817) ^ 11 := by rw [pow_add]
          _ = 13971406800 := by rw [fermat_3]; decide
      have fermat_5 : (10 : ZMod 24650604817) ^ 45 = 14040974383 := by
        calc
          (10 : ZMod 24650604817) ^ 45 = (10 : ZMod 24650604817) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 22 * (10 : ZMod 24650604817) ^ 22) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 14040974383 := by rw [fermat_4]; decide
      have fermat_6 : (10 : ZMod 24650604817) ^ 91 = 18299757861 := by
        calc
          (10 : ZMod 24650604817) ^ 91 = (10 : ZMod 24650604817) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 45 * (10 : ZMod 24650604817) ^ 45) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 18299757861 := by rw [fermat_5]; decide
      have fermat_7 : (10 : ZMod 24650604817) ^ 183 = 4736076284 := by
        calc
          (10 : ZMod 24650604817) ^ 183 = (10 : ZMod 24650604817) ^ (91 + 91 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 91 * (10 : ZMod 24650604817) ^ 91) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 4736076284 := by rw [fermat_6]; decide
      have fermat_8 : (10 : ZMod 24650604817) ^ 367 = 2048034586 := by
        calc
          (10 : ZMod 24650604817) ^ 367 = (10 : ZMod 24650604817) ^ (183 + 183 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 183 * (10 : ZMod 24650604817) ^ 183) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 2048034586 := by rw [fermat_7]; decide
      have fermat_9 : (10 : ZMod 24650604817) ^ 734 = 14476059632 := by
        calc
          (10 : ZMod 24650604817) ^ 734 = (10 : ZMod 24650604817) ^ (367 + 367) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 367 * (10 : ZMod 24650604817) ^ 367 := by rw [pow_add]
          _ = 14476059632 := by rw [fermat_8]; decide
      have fermat_10 : (10 : ZMod 24650604817) ^ 1469 = 5216851162 := by
        calc
          (10 : ZMod 24650604817) ^ 1469 = (10 : ZMod 24650604817) ^ (734 + 734 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 734 * (10 : ZMod 24650604817) ^ 734) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 5216851162 := by rw [fermat_9]; decide
      have fermat_11 : (10 : ZMod 24650604817) ^ 2938 = 5573705960 := by
        calc
          (10 : ZMod 24650604817) ^ 2938 = (10 : ZMod 24650604817) ^ (1469 + 1469) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 1469 * (10 : ZMod 24650604817) ^ 1469 := by rw [pow_add]
          _ = 5573705960 := by rw [fermat_10]; decide
      have fermat_12 : (10 : ZMod 24650604817) ^ 5877 = 6620648079 := by
        calc
          (10 : ZMod 24650604817) ^ 5877 = (10 : ZMod 24650604817) ^ (2938 + 2938 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 2938 * (10 : ZMod 24650604817) ^ 2938) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 6620648079 := by rw [fermat_11]; decide
      have fermat_13 : (10 : ZMod 24650604817) ^ 11754 = 6303166688 := by
        calc
          (10 : ZMod 24650604817) ^ 11754 = (10 : ZMod 24650604817) ^ (5877 + 5877) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 5877 * (10 : ZMod 24650604817) ^ 5877 := by rw [pow_add]
          _ = 6303166688 := by rw [fermat_12]; decide
      have fermat_14 : (10 : ZMod 24650604817) ^ 23508 = 7487722687 := by
        calc
          (10 : ZMod 24650604817) ^ 23508 = (10 : ZMod 24650604817) ^ (11754 + 11754) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 11754 * (10 : ZMod 24650604817) ^ 11754 := by rw [pow_add]
          _ = 7487722687 := by rw [fermat_13]; decide
      have fermat_15 : (10 : ZMod 24650604817) ^ 47017 = 17680997926 := by
        calc
          (10 : ZMod 24650604817) ^ 47017 = (10 : ZMod 24650604817) ^ (23508 + 23508 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 23508 * (10 : ZMod 24650604817) ^ 23508) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 17680997926 := by rw [fermat_14]; decide
      have fermat_16 : (10 : ZMod 24650604817) ^ 94034 = 14942744437 := by
        calc
          (10 : ZMod 24650604817) ^ 94034 = (10 : ZMod 24650604817) ^ (47017 + 47017) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 47017 * (10 : ZMod 24650604817) ^ 47017 := by rw [pow_add]
          _ = 14942744437 := by rw [fermat_15]; decide
      have fermat_17 : (10 : ZMod 24650604817) ^ 188069 = 1625580405 := by
        calc
          (10 : ZMod 24650604817) ^ 188069 = (10 : ZMod 24650604817) ^ (94034 + 94034 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 94034 * (10 : ZMod 24650604817) ^ 94034) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 1625580405 := by rw [fermat_16]; decide
      have fermat_18 : (10 : ZMod 24650604817) ^ 376138 = 21102252524 := by
        calc
          (10 : ZMod 24650604817) ^ 376138 = (10 : ZMod 24650604817) ^ (188069 + 188069) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 188069 * (10 : ZMod 24650604817) ^ 188069 := by rw [pow_add]
          _ = 21102252524 := by rw [fermat_17]; decide
      have fermat_19 : (10 : ZMod 24650604817) ^ 752276 = 4351821002 := by
        calc
          (10 : ZMod 24650604817) ^ 752276 = (10 : ZMod 24650604817) ^ (376138 + 376138) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 376138 * (10 : ZMod 24650604817) ^ 376138 := by rw [pow_add]
          _ = 4351821002 := by rw [fermat_18]; decide
      have fermat_20 : (10 : ZMod 24650604817) ^ 1504553 = 23469990442 := by
        calc
          (10 : ZMod 24650604817) ^ 1504553 = (10 : ZMod 24650604817) ^ (752276 + 752276 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 752276 * (10 : ZMod 24650604817) ^ 752276) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 23469990442 := by rw [fermat_19]; decide
      have fermat_21 : (10 : ZMod 24650604817) ^ 3009107 = 8546419004 := by
        calc
          (10 : ZMod 24650604817) ^ 3009107 = (10 : ZMod 24650604817) ^ (1504553 + 1504553 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 1504553 * (10 : ZMod 24650604817) ^ 1504553) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 8546419004 := by rw [fermat_20]; decide
      have fermat_22 : (10 : ZMod 24650604817) ^ 6018214 = 11131857733 := by
        calc
          (10 : ZMod 24650604817) ^ 6018214 = (10 : ZMod 24650604817) ^ (3009107 + 3009107) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 3009107 * (10 : ZMod 24650604817) ^ 3009107 := by rw [pow_add]
          _ = 11131857733 := by rw [fermat_21]; decide
      have fermat_23 : (10 : ZMod 24650604817) ^ 12036428 = 15833935920 := by
        calc
          (10 : ZMod 24650604817) ^ 12036428 = (10 : ZMod 24650604817) ^ (6018214 + 6018214) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 6018214 * (10 : ZMod 24650604817) ^ 6018214 := by rw [pow_add]
          _ = 15833935920 := by rw [fermat_22]; decide
      have fermat_24 : (10 : ZMod 24650604817) ^ 24072856 = 24320947468 := by
        calc
          (10 : ZMod 24650604817) ^ 24072856 = (10 : ZMod 24650604817) ^ (12036428 + 12036428) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 12036428 * (10 : ZMod 24650604817) ^ 12036428 := by rw [pow_add]
          _ = 24320947468 := by rw [fermat_23]; decide
      have fermat_25 : (10 : ZMod 24650604817) ^ 48145712 = 1570416477 := by
        calc
          (10 : ZMod 24650604817) ^ 48145712 = (10 : ZMod 24650604817) ^ (24072856 + 24072856) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 24072856 * (10 : ZMod 24650604817) ^ 24072856 := by rw [pow_add]
          _ = 1570416477 := by rw [fermat_24]; decide
      have fermat_26 : (10 : ZMod 24650604817) ^ 96291425 = 5752512581 := by
        calc
          (10 : ZMod 24650604817) ^ 96291425 = (10 : ZMod 24650604817) ^ (48145712 + 48145712 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 48145712 * (10 : ZMod 24650604817) ^ 48145712) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 5752512581 := by rw [fermat_25]; decide
      have fermat_27 : (10 : ZMod 24650604817) ^ 192582850 = 19795036859 := by
        calc
          (10 : ZMod 24650604817) ^ 192582850 = (10 : ZMod 24650604817) ^ (96291425 + 96291425) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 96291425 * (10 : ZMod 24650604817) ^ 96291425 := by rw [pow_add]
          _ = 19795036859 := by rw [fermat_26]; decide
      have fermat_28 : (10 : ZMod 24650604817) ^ 385165700 = 19010164225 := by
        calc
          (10 : ZMod 24650604817) ^ 385165700 = (10 : ZMod 24650604817) ^ (192582850 + 192582850) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 192582850 * (10 : ZMod 24650604817) ^ 192582850 := by rw [pow_add]
          _ = 19010164225 := by rw [fermat_27]; decide
      have fermat_29 : (10 : ZMod 24650604817) ^ 770331400 = 24506308410 := by
        calc
          (10 : ZMod 24650604817) ^ 770331400 = (10 : ZMod 24650604817) ^ (385165700 + 385165700) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 385165700 * (10 : ZMod 24650604817) ^ 385165700 := by rw [pow_add]
          _ = 24506308410 := by rw [fermat_28]; decide
      have fermat_30 : (10 : ZMod 24650604817) ^ 1540662801 = 17216284597 := by
        calc
          (10 : ZMod 24650604817) ^ 1540662801 = (10 : ZMod 24650604817) ^ (770331400 + 770331400 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 770331400 * (10 : ZMod 24650604817) ^ 770331400) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 17216284597 := by rw [fermat_29]; decide
      have fermat_31 : (10 : ZMod 24650604817) ^ 3081325602 = 17401919120 := by
        calc
          (10 : ZMod 24650604817) ^ 3081325602 = (10 : ZMod 24650604817) ^ (1540662801 + 1540662801) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 1540662801 * (10 : ZMod 24650604817) ^ 1540662801 := by rw [pow_add]
          _ = 17401919120 := by rw [fermat_30]; decide
      have fermat_32 : (10 : ZMod 24650604817) ^ 6162651204 = 6968765145 := by
        calc
          (10 : ZMod 24650604817) ^ 6162651204 = (10 : ZMod 24650604817) ^ (3081325602 + 3081325602) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 3081325602 * (10 : ZMod 24650604817) ^ 3081325602 := by rw [pow_add]
          _ = 6968765145 := by rw [fermat_31]; decide
      have fermat_33 : (10 : ZMod 24650604817) ^ 12325302408 = 24650604816 := by
        calc
          (10 : ZMod 24650604817) ^ 12325302408 = (10 : ZMod 24650604817) ^ (6162651204 + 6162651204) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 6162651204 * (10 : ZMod 24650604817) ^ 6162651204 := by rw [pow_add]
          _ = 24650604816 := by rw [fermat_32]; decide
      have fermat_34 : (10 : ZMod 24650604817) ^ 24650604816 = 1 := by
        calc
          (10 : ZMod 24650604817) ^ 24650604816 = (10 : ZMod 24650604817) ^ (12325302408 + 12325302408) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 12325302408 * (10 : ZMod 24650604817) ^ 12325302408 := by rw [pow_add]
          _ = 1 := by rw [fermat_33]; decide
      simpa using fermat_34
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5059, 1), (101513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5059, 1), (101513, 1)] : List FactorBlock).map factorBlockValue).prod = 24650604817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (10 : ZMod 24650604817) ^ 1 = 10 := by norm_num
      have factor_0_1 : (10 : ZMod 24650604817) ^ 2 = 100 := by
        calc
          (10 : ZMod 24650604817) ^ 2 = (10 : ZMod 24650604817) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 1 * (10 : ZMod 24650604817) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_0_0]; decide
      have factor_0_2 : (10 : ZMod 24650604817) ^ 5 = 100000 := by
        calc
          (10 : ZMod 24650604817) ^ 5 = (10 : ZMod 24650604817) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 2 * (10 : ZMod 24650604817) ^ 2) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 100000 := by rw [factor_0_1]; decide
      have factor_0_3 : (10 : ZMod 24650604817) ^ 11 = 1397580732 := by
        calc
          (10 : ZMod 24650604817) ^ 11 = (10 : ZMod 24650604817) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 5 * (10 : ZMod 24650604817) ^ 5) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 1397580732 := by rw [factor_0_2]; decide
      have factor_0_4 : (10 : ZMod 24650604817) ^ 22 = 13971406800 := by
        calc
          (10 : ZMod 24650604817) ^ 22 = (10 : ZMod 24650604817) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 11 * (10 : ZMod 24650604817) ^ 11 := by rw [pow_add]
          _ = 13971406800 := by rw [factor_0_3]; decide
      have factor_0_5 : (10 : ZMod 24650604817) ^ 45 = 14040974383 := by
        calc
          (10 : ZMod 24650604817) ^ 45 = (10 : ZMod 24650604817) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 22 * (10 : ZMod 24650604817) ^ 22) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 14040974383 := by rw [factor_0_4]; decide
      have factor_0_6 : (10 : ZMod 24650604817) ^ 91 = 18299757861 := by
        calc
          (10 : ZMod 24650604817) ^ 91 = (10 : ZMod 24650604817) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 45 * (10 : ZMod 24650604817) ^ 45) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 18299757861 := by rw [factor_0_5]; decide
      have factor_0_7 : (10 : ZMod 24650604817) ^ 183 = 4736076284 := by
        calc
          (10 : ZMod 24650604817) ^ 183 = (10 : ZMod 24650604817) ^ (91 + 91 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 91 * (10 : ZMod 24650604817) ^ 91) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 4736076284 := by rw [factor_0_6]; decide
      have factor_0_8 : (10 : ZMod 24650604817) ^ 367 = 2048034586 := by
        calc
          (10 : ZMod 24650604817) ^ 367 = (10 : ZMod 24650604817) ^ (183 + 183 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 183 * (10 : ZMod 24650604817) ^ 183) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 2048034586 := by rw [factor_0_7]; decide
      have factor_0_9 : (10 : ZMod 24650604817) ^ 734 = 14476059632 := by
        calc
          (10 : ZMod 24650604817) ^ 734 = (10 : ZMod 24650604817) ^ (367 + 367) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 367 * (10 : ZMod 24650604817) ^ 367 := by rw [pow_add]
          _ = 14476059632 := by rw [factor_0_8]; decide
      have factor_0_10 : (10 : ZMod 24650604817) ^ 1469 = 5216851162 := by
        calc
          (10 : ZMod 24650604817) ^ 1469 = (10 : ZMod 24650604817) ^ (734 + 734 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 734 * (10 : ZMod 24650604817) ^ 734) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 5216851162 := by rw [factor_0_9]; decide
      have factor_0_11 : (10 : ZMod 24650604817) ^ 2938 = 5573705960 := by
        calc
          (10 : ZMod 24650604817) ^ 2938 = (10 : ZMod 24650604817) ^ (1469 + 1469) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 1469 * (10 : ZMod 24650604817) ^ 1469 := by rw [pow_add]
          _ = 5573705960 := by rw [factor_0_10]; decide
      have factor_0_12 : (10 : ZMod 24650604817) ^ 5877 = 6620648079 := by
        calc
          (10 : ZMod 24650604817) ^ 5877 = (10 : ZMod 24650604817) ^ (2938 + 2938 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 2938 * (10 : ZMod 24650604817) ^ 2938) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 6620648079 := by rw [factor_0_11]; decide
      have factor_0_13 : (10 : ZMod 24650604817) ^ 11754 = 6303166688 := by
        calc
          (10 : ZMod 24650604817) ^ 11754 = (10 : ZMod 24650604817) ^ (5877 + 5877) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 5877 * (10 : ZMod 24650604817) ^ 5877 := by rw [pow_add]
          _ = 6303166688 := by rw [factor_0_12]; decide
      have factor_0_14 : (10 : ZMod 24650604817) ^ 23508 = 7487722687 := by
        calc
          (10 : ZMod 24650604817) ^ 23508 = (10 : ZMod 24650604817) ^ (11754 + 11754) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 11754 * (10 : ZMod 24650604817) ^ 11754 := by rw [pow_add]
          _ = 7487722687 := by rw [factor_0_13]; decide
      have factor_0_15 : (10 : ZMod 24650604817) ^ 47017 = 17680997926 := by
        calc
          (10 : ZMod 24650604817) ^ 47017 = (10 : ZMod 24650604817) ^ (23508 + 23508 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 23508 * (10 : ZMod 24650604817) ^ 23508) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 17680997926 := by rw [factor_0_14]; decide
      have factor_0_16 : (10 : ZMod 24650604817) ^ 94034 = 14942744437 := by
        calc
          (10 : ZMod 24650604817) ^ 94034 = (10 : ZMod 24650604817) ^ (47017 + 47017) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 47017 * (10 : ZMod 24650604817) ^ 47017 := by rw [pow_add]
          _ = 14942744437 := by rw [factor_0_15]; decide
      have factor_0_17 : (10 : ZMod 24650604817) ^ 188069 = 1625580405 := by
        calc
          (10 : ZMod 24650604817) ^ 188069 = (10 : ZMod 24650604817) ^ (94034 + 94034 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 94034 * (10 : ZMod 24650604817) ^ 94034) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 1625580405 := by rw [factor_0_16]; decide
      have factor_0_18 : (10 : ZMod 24650604817) ^ 376138 = 21102252524 := by
        calc
          (10 : ZMod 24650604817) ^ 376138 = (10 : ZMod 24650604817) ^ (188069 + 188069) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 188069 * (10 : ZMod 24650604817) ^ 188069 := by rw [pow_add]
          _ = 21102252524 := by rw [factor_0_17]; decide
      have factor_0_19 : (10 : ZMod 24650604817) ^ 752276 = 4351821002 := by
        calc
          (10 : ZMod 24650604817) ^ 752276 = (10 : ZMod 24650604817) ^ (376138 + 376138) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 376138 * (10 : ZMod 24650604817) ^ 376138 := by rw [pow_add]
          _ = 4351821002 := by rw [factor_0_18]; decide
      have factor_0_20 : (10 : ZMod 24650604817) ^ 1504553 = 23469990442 := by
        calc
          (10 : ZMod 24650604817) ^ 1504553 = (10 : ZMod 24650604817) ^ (752276 + 752276 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 752276 * (10 : ZMod 24650604817) ^ 752276) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 23469990442 := by rw [factor_0_19]; decide
      have factor_0_21 : (10 : ZMod 24650604817) ^ 3009107 = 8546419004 := by
        calc
          (10 : ZMod 24650604817) ^ 3009107 = (10 : ZMod 24650604817) ^ (1504553 + 1504553 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 1504553 * (10 : ZMod 24650604817) ^ 1504553) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 8546419004 := by rw [factor_0_20]; decide
      have factor_0_22 : (10 : ZMod 24650604817) ^ 6018214 = 11131857733 := by
        calc
          (10 : ZMod 24650604817) ^ 6018214 = (10 : ZMod 24650604817) ^ (3009107 + 3009107) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 3009107 * (10 : ZMod 24650604817) ^ 3009107 := by rw [pow_add]
          _ = 11131857733 := by rw [factor_0_21]; decide
      have factor_0_23 : (10 : ZMod 24650604817) ^ 12036428 = 15833935920 := by
        calc
          (10 : ZMod 24650604817) ^ 12036428 = (10 : ZMod 24650604817) ^ (6018214 + 6018214) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 6018214 * (10 : ZMod 24650604817) ^ 6018214 := by rw [pow_add]
          _ = 15833935920 := by rw [factor_0_22]; decide
      have factor_0_24 : (10 : ZMod 24650604817) ^ 24072856 = 24320947468 := by
        calc
          (10 : ZMod 24650604817) ^ 24072856 = (10 : ZMod 24650604817) ^ (12036428 + 12036428) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 12036428 * (10 : ZMod 24650604817) ^ 12036428 := by rw [pow_add]
          _ = 24320947468 := by rw [factor_0_23]; decide
      have factor_0_25 : (10 : ZMod 24650604817) ^ 48145712 = 1570416477 := by
        calc
          (10 : ZMod 24650604817) ^ 48145712 = (10 : ZMod 24650604817) ^ (24072856 + 24072856) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 24072856 * (10 : ZMod 24650604817) ^ 24072856 := by rw [pow_add]
          _ = 1570416477 := by rw [factor_0_24]; decide
      have factor_0_26 : (10 : ZMod 24650604817) ^ 96291425 = 5752512581 := by
        calc
          (10 : ZMod 24650604817) ^ 96291425 = (10 : ZMod 24650604817) ^ (48145712 + 48145712 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 48145712 * (10 : ZMod 24650604817) ^ 48145712) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 5752512581 := by rw [factor_0_25]; decide
      have factor_0_27 : (10 : ZMod 24650604817) ^ 192582850 = 19795036859 := by
        calc
          (10 : ZMod 24650604817) ^ 192582850 = (10 : ZMod 24650604817) ^ (96291425 + 96291425) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 96291425 * (10 : ZMod 24650604817) ^ 96291425 := by rw [pow_add]
          _ = 19795036859 := by rw [factor_0_26]; decide
      have factor_0_28 : (10 : ZMod 24650604817) ^ 385165700 = 19010164225 := by
        calc
          (10 : ZMod 24650604817) ^ 385165700 = (10 : ZMod 24650604817) ^ (192582850 + 192582850) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 192582850 * (10 : ZMod 24650604817) ^ 192582850 := by rw [pow_add]
          _ = 19010164225 := by rw [factor_0_27]; decide
      have factor_0_29 : (10 : ZMod 24650604817) ^ 770331400 = 24506308410 := by
        calc
          (10 : ZMod 24650604817) ^ 770331400 = (10 : ZMod 24650604817) ^ (385165700 + 385165700) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 385165700 * (10 : ZMod 24650604817) ^ 385165700 := by rw [pow_add]
          _ = 24506308410 := by rw [factor_0_28]; decide
      have factor_0_30 : (10 : ZMod 24650604817) ^ 1540662801 = 17216284597 := by
        calc
          (10 : ZMod 24650604817) ^ 1540662801 = (10 : ZMod 24650604817) ^ (770331400 + 770331400 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 770331400 * (10 : ZMod 24650604817) ^ 770331400) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 17216284597 := by rw [factor_0_29]; decide
      have factor_0_31 : (10 : ZMod 24650604817) ^ 3081325602 = 17401919120 := by
        calc
          (10 : ZMod 24650604817) ^ 3081325602 = (10 : ZMod 24650604817) ^ (1540662801 + 1540662801) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 1540662801 * (10 : ZMod 24650604817) ^ 1540662801 := by rw [pow_add]
          _ = 17401919120 := by rw [factor_0_30]; decide
      have factor_0_32 : (10 : ZMod 24650604817) ^ 6162651204 = 6968765145 := by
        calc
          (10 : ZMod 24650604817) ^ 6162651204 = (10 : ZMod 24650604817) ^ (3081325602 + 3081325602) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 3081325602 * (10 : ZMod 24650604817) ^ 3081325602 := by rw [pow_add]
          _ = 6968765145 := by rw [factor_0_31]; decide
      have factor_0_33 : (10 : ZMod 24650604817) ^ 12325302408 = 24650604816 := by
        calc
          (10 : ZMod 24650604817) ^ 12325302408 = (10 : ZMod 24650604817) ^ (6162651204 + 6162651204) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 6162651204 * (10 : ZMod 24650604817) ^ 6162651204 := by rw [pow_add]
          _ = 24650604816 := by rw [factor_0_32]; decide
      change (10 : ZMod 24650604817) ^ 12325302408 ≠ 1
      rw [factor_0_33]
      decide
    ·
      have factor_1_0 : (10 : ZMod 24650604817) ^ 1 = 10 := by norm_num
      have factor_1_1 : (10 : ZMod 24650604817) ^ 3 = 1000 := by
        calc
          (10 : ZMod 24650604817) ^ 3 = (10 : ZMod 24650604817) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 1 * (10 : ZMod 24650604817) ^ 1) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_1_0]; decide
      have factor_1_2 : (10 : ZMod 24650604817) ^ 7 = 10000000 := by
        calc
          (10 : ZMod 24650604817) ^ 7 = (10 : ZMod 24650604817) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 3 * (10 : ZMod 24650604817) ^ 3) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 10000000 := by rw [factor_1_1]; decide
      have factor_1_3 : (10 : ZMod 24650604817) ^ 15 = 23564993578 := by
        calc
          (10 : ZMod 24650604817) ^ 15 = (10 : ZMod 24650604817) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 7 * (10 : ZMod 24650604817) ^ 7) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 23564993578 := by rw [factor_1_2]; decide
      have factor_1_4 : (10 : ZMod 24650604817) ^ 30 = 10736907152 := by
        calc
          (10 : ZMod 24650604817) ^ 30 = (10 : ZMod 24650604817) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 15 * (10 : ZMod 24650604817) ^ 15 := by rw [pow_add]
          _ = 10736907152 := by rw [factor_1_3]; decide
      have factor_1_5 : (10 : ZMod 24650604817) ^ 61 = 20567899167 := by
        calc
          (10 : ZMod 24650604817) ^ 61 = (10 : ZMod 24650604817) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 30 * (10 : ZMod 24650604817) ^ 30) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 20567899167 := by rw [factor_1_4]; decide
      have factor_1_6 : (10 : ZMod 24650604817) ^ 122 = 3407670162 := by
        calc
          (10 : ZMod 24650604817) ^ 122 = (10 : ZMod 24650604817) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 61 * (10 : ZMod 24650604817) ^ 61 := by rw [pow_add]
          _ = 3407670162 := by rw [factor_1_5]; decide
      have factor_1_7 : (10 : ZMod 24650604817) ^ 244 = 8678868360 := by
        calc
          (10 : ZMod 24650604817) ^ 244 = (10 : ZMod 24650604817) ^ (122 + 122) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 122 * (10 : ZMod 24650604817) ^ 122 := by rw [pow_add]
          _ = 8678868360 := by rw [factor_1_6]; decide
      have factor_1_8 : (10 : ZMod 24650604817) ^ 489 = 13865120214 := by
        calc
          (10 : ZMod 24650604817) ^ 489 = (10 : ZMod 24650604817) ^ (244 + 244 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 244 * (10 : ZMod 24650604817) ^ 244) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 13865120214 := by rw [factor_1_7]; decide
      have factor_1_9 : (10 : ZMod 24650604817) ^ 979 = 9024648879 := by
        calc
          (10 : ZMod 24650604817) ^ 979 = (10 : ZMod 24650604817) ^ (489 + 489 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 489 * (10 : ZMod 24650604817) ^ 489) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 9024648879 := by rw [factor_1_8]; decide
      have factor_1_10 : (10 : ZMod 24650604817) ^ 1959 = 4273061461 := by
        calc
          (10 : ZMod 24650604817) ^ 1959 = (10 : ZMod 24650604817) ^ (979 + 979 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 979 * (10 : ZMod 24650604817) ^ 979) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 4273061461 := by rw [factor_1_9]; decide
      have factor_1_11 : (10 : ZMod 24650604817) ^ 3918 = 15063517088 := by
        calc
          (10 : ZMod 24650604817) ^ 3918 = (10 : ZMod 24650604817) ^ (1959 + 1959) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 1959 * (10 : ZMod 24650604817) ^ 1959 := by rw [pow_add]
          _ = 15063517088 := by rw [factor_1_10]; decide
      have factor_1_12 : (10 : ZMod 24650604817) ^ 7836 = 12779206910 := by
        calc
          (10 : ZMod 24650604817) ^ 7836 = (10 : ZMod 24650604817) ^ (3918 + 3918) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 3918 * (10 : ZMod 24650604817) ^ 3918 := by rw [pow_add]
          _ = 12779206910 := by rw [factor_1_11]; decide
      have factor_1_13 : (10 : ZMod 24650604817) ^ 15672 = 3620317821 := by
        calc
          (10 : ZMod 24650604817) ^ 15672 = (10 : ZMod 24650604817) ^ (7836 + 7836) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 7836 * (10 : ZMod 24650604817) ^ 7836 := by rw [pow_add]
          _ = 3620317821 := by rw [factor_1_12]; decide
      have factor_1_14 : (10 : ZMod 24650604817) ^ 31344 = 7926064002 := by
        calc
          (10 : ZMod 24650604817) ^ 31344 = (10 : ZMod 24650604817) ^ (15672 + 15672) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 15672 * (10 : ZMod 24650604817) ^ 15672 := by rw [pow_add]
          _ = 7926064002 := by rw [factor_1_13]; decide
      have factor_1_15 : (10 : ZMod 24650604817) ^ 62689 = 680650680 := by
        calc
          (10 : ZMod 24650604817) ^ 62689 = (10 : ZMod 24650604817) ^ (31344 + 31344 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 31344 * (10 : ZMod 24650604817) ^ 31344) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 680650680 := by rw [factor_1_14]; decide
      have factor_1_16 : (10 : ZMod 24650604817) ^ 125379 = 4126168629 := by
        calc
          (10 : ZMod 24650604817) ^ 125379 = (10 : ZMod 24650604817) ^ (62689 + 62689 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 62689 * (10 : ZMod 24650604817) ^ 62689) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 4126168629 := by rw [factor_1_15]; decide
      have factor_1_17 : (10 : ZMod 24650604817) ^ 250758 = 2701324698 := by
        calc
          (10 : ZMod 24650604817) ^ 250758 = (10 : ZMod 24650604817) ^ (125379 + 125379) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 125379 * (10 : ZMod 24650604817) ^ 125379 := by rw [pow_add]
          _ = 2701324698 := by rw [factor_1_16]; decide
      have factor_1_18 : (10 : ZMod 24650604817) ^ 501517 = 12329155055 := by
        calc
          (10 : ZMod 24650604817) ^ 501517 = (10 : ZMod 24650604817) ^ (250758 + 250758 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 250758 * (10 : ZMod 24650604817) ^ 250758) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 12329155055 := by rw [factor_1_17]; decide
      have factor_1_19 : (10 : ZMod 24650604817) ^ 1003035 = 19884238874 := by
        calc
          (10 : ZMod 24650604817) ^ 1003035 = (10 : ZMod 24650604817) ^ (501517 + 501517 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 501517 * (10 : ZMod 24650604817) ^ 501517) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 19884238874 := by rw [factor_1_18]; decide
      have factor_1_20 : (10 : ZMod 24650604817) ^ 2006071 = 3201716953 := by
        calc
          (10 : ZMod 24650604817) ^ 2006071 = (10 : ZMod 24650604817) ^ (1003035 + 1003035 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 1003035 * (10 : ZMod 24650604817) ^ 1003035) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 3201716953 := by rw [factor_1_19]; decide
      have factor_1_21 : (10 : ZMod 24650604817) ^ 4012142 = 14360042003 := by
        calc
          (10 : ZMod 24650604817) ^ 4012142 = (10 : ZMod 24650604817) ^ (2006071 + 2006071) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 2006071 * (10 : ZMod 24650604817) ^ 2006071 := by rw [pow_add]
          _ = 14360042003 := by rw [factor_1_20]; decide
      have factor_1_22 : (10 : ZMod 24650604817) ^ 8024285 = 22846183711 := by
        calc
          (10 : ZMod 24650604817) ^ 8024285 = (10 : ZMod 24650604817) ^ (4012142 + 4012142 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 4012142 * (10 : ZMod 24650604817) ^ 4012142) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 22846183711 := by rw [factor_1_21]; decide
      have factor_1_23 : (10 : ZMod 24650604817) ^ 16048570 = 4046759155 := by
        calc
          (10 : ZMod 24650604817) ^ 16048570 = (10 : ZMod 24650604817) ^ (8024285 + 8024285) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 8024285 * (10 : ZMod 24650604817) ^ 8024285 := by rw [pow_add]
          _ = 4046759155 := by rw [factor_1_22]; decide
      have factor_1_24 : (10 : ZMod 24650604817) ^ 32097141 = 14770183119 := by
        calc
          (10 : ZMod 24650604817) ^ 32097141 = (10 : ZMod 24650604817) ^ (16048570 + 16048570 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 16048570 * (10 : ZMod 24650604817) ^ 16048570) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 14770183119 := by rw [factor_1_23]; decide
      have factor_1_25 : (10 : ZMod 24650604817) ^ 64194283 = 20762768582 := by
        calc
          (10 : ZMod 24650604817) ^ 64194283 = (10 : ZMod 24650604817) ^ (32097141 + 32097141 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 32097141 * (10 : ZMod 24650604817) ^ 32097141) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 20762768582 := by rw [factor_1_24]; decide
      have factor_1_26 : (10 : ZMod 24650604817) ^ 128388566 = 8778829653 := by
        calc
          (10 : ZMod 24650604817) ^ 128388566 = (10 : ZMod 24650604817) ^ (64194283 + 64194283) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 64194283 * (10 : ZMod 24650604817) ^ 64194283 := by rw [pow_add]
          _ = 8778829653 := by rw [factor_1_25]; decide
      have factor_1_27 : (10 : ZMod 24650604817) ^ 256777133 = 21014395307 := by
        calc
          (10 : ZMod 24650604817) ^ 256777133 = (10 : ZMod 24650604817) ^ (128388566 + 128388566 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 128388566 * (10 : ZMod 24650604817) ^ 128388566) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 21014395307 := by rw [factor_1_26]; decide
      have factor_1_28 : (10 : ZMod 24650604817) ^ 513554267 = 10139329844 := by
        calc
          (10 : ZMod 24650604817) ^ 513554267 = (10 : ZMod 24650604817) ^ (256777133 + 256777133 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 256777133 * (10 : ZMod 24650604817) ^ 256777133) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 10139329844 := by rw [factor_1_27]; decide
      have factor_1_29 : (10 : ZMod 24650604817) ^ 1027108534 = 8330945997 := by
        calc
          (10 : ZMod 24650604817) ^ 1027108534 = (10 : ZMod 24650604817) ^ (513554267 + 513554267) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 513554267 * (10 : ZMod 24650604817) ^ 513554267 := by rw [pow_add]
          _ = 8330945997 := by rw [factor_1_28]; decide
      have factor_1_30 : (10 : ZMod 24650604817) ^ 2054217068 = 12893811631 := by
        calc
          (10 : ZMod 24650604817) ^ 2054217068 = (10 : ZMod 24650604817) ^ (1027108534 + 1027108534) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 1027108534 * (10 : ZMod 24650604817) ^ 1027108534 := by rw [pow_add]
          _ = 12893811631 := by rw [factor_1_29]; decide
      have factor_1_31 : (10 : ZMod 24650604817) ^ 4108434136 = 22437530352 := by
        calc
          (10 : ZMod 24650604817) ^ 4108434136 = (10 : ZMod 24650604817) ^ (2054217068 + 2054217068) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 2054217068 * (10 : ZMod 24650604817) ^ 2054217068 := by rw [pow_add]
          _ = 22437530352 := by rw [factor_1_30]; decide
      have factor_1_32 : (10 : ZMod 24650604817) ^ 8216868272 = 22437530351 := by
        calc
          (10 : ZMod 24650604817) ^ 8216868272 = (10 : ZMod 24650604817) ^ (4108434136 + 4108434136) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 4108434136 * (10 : ZMod 24650604817) ^ 4108434136 := by rw [pow_add]
          _ = 22437530351 := by rw [factor_1_31]; decide
      change (10 : ZMod 24650604817) ^ 8216868272 ≠ 1
      rw [factor_1_32]
      decide
    ·
      have factor_2_0 : (10 : ZMod 24650604817) ^ 1 = 10 := by norm_num
      have factor_2_1 : (10 : ZMod 24650604817) ^ 2 = 100 := by
        calc
          (10 : ZMod 24650604817) ^ 2 = (10 : ZMod 24650604817) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 1 * (10 : ZMod 24650604817) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_2_0]; decide
      have factor_2_2 : (10 : ZMod 24650604817) ^ 4 = 10000 := by
        calc
          (10 : ZMod 24650604817) ^ 4 = (10 : ZMod 24650604817) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 2 * (10 : ZMod 24650604817) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [factor_2_1]; decide
      have factor_2_3 : (10 : ZMod 24650604817) ^ 9 = 1000000000 := by
        calc
          (10 : ZMod 24650604817) ^ 9 = (10 : ZMod 24650604817) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 4 * (10 : ZMod 24650604817) ^ 4) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 1000000000 := by rw [factor_2_2]; decide
      have factor_2_4 : (10 : ZMod 24650604817) ^ 18 = 23665977765 := by
        calc
          (10 : ZMod 24650604817) ^ 18 = (10 : ZMod 24650604817) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 9 * (10 : ZMod 24650604817) ^ 9 := by rw [pow_add]
          _ = 23665977765 := by rw [factor_2_3]; decide
      have factor_2_5 : (10 : ZMod 24650604817) ^ 37 = 9757301388 := by
        calc
          (10 : ZMod 24650604817) ^ 37 = (10 : ZMod 24650604817) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 18 * (10 : ZMod 24650604817) ^ 18) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 9757301388 := by rw [factor_2_4]; decide
      have factor_2_6 : (10 : ZMod 24650604817) ^ 74 = 18593323255 := by
        calc
          (10 : ZMod 24650604817) ^ 74 = (10 : ZMod 24650604817) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 37 * (10 : ZMod 24650604817) ^ 37 := by rw [pow_add]
          _ = 18593323255 := by rw [factor_2_5]; decide
      have factor_2_7 : (10 : ZMod 24650604817) ^ 148 = 4304629299 := by
        calc
          (10 : ZMod 24650604817) ^ 148 = (10 : ZMod 24650604817) ^ (74 + 74) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 74 * (10 : ZMod 24650604817) ^ 74 := by rw [pow_add]
          _ = 4304629299 := by rw [factor_2_6]; decide
      have factor_2_8 : (10 : ZMod 24650604817) ^ 297 = 14391590975 := by
        calc
          (10 : ZMod 24650604817) ^ 297 = (10 : ZMod 24650604817) ^ (148 + 148 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 148 * (10 : ZMod 24650604817) ^ 148) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 14391590975 := by rw [factor_2_7]; decide
      have factor_2_9 : (10 : ZMod 24650604817) ^ 594 = 7069331407 := by
        calc
          (10 : ZMod 24650604817) ^ 594 = (10 : ZMod 24650604817) ^ (297 + 297) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 297 * (10 : ZMod 24650604817) ^ 297 := by rw [pow_add]
          _ = 7069331407 := by rw [factor_2_8]; decide
      have factor_2_10 : (10 : ZMod 24650604817) ^ 1189 = 13149333677 := by
        calc
          (10 : ZMod 24650604817) ^ 1189 = (10 : ZMod 24650604817) ^ (594 + 594 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 594 * (10 : ZMod 24650604817) ^ 594) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 13149333677 := by rw [factor_2_9]; decide
      have factor_2_11 : (10 : ZMod 24650604817) ^ 2379 = 3607819731 := by
        calc
          (10 : ZMod 24650604817) ^ 2379 = (10 : ZMod 24650604817) ^ (1189 + 1189 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 1189 * (10 : ZMod 24650604817) ^ 1189) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 3607819731 := by rw [factor_2_10]; decide
      have factor_2_12 : (10 : ZMod 24650604817) ^ 4758 = 3862212000 := by
        calc
          (10 : ZMod 24650604817) ^ 4758 = (10 : ZMod 24650604817) ^ (2379 + 2379) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 2379 * (10 : ZMod 24650604817) ^ 2379 := by rw [pow_add]
          _ = 3862212000 := by rw [factor_2_11]; decide
      have factor_2_13 : (10 : ZMod 24650604817) ^ 9516 = 20142748246 := by
        calc
          (10 : ZMod 24650604817) ^ 9516 = (10 : ZMod 24650604817) ^ (4758 + 4758) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 4758 * (10 : ZMod 24650604817) ^ 4758 := by rw [pow_add]
          _ = 20142748246 := by rw [factor_2_12]; decide
      have factor_2_14 : (10 : ZMod 24650604817) ^ 19033 = 10601569971 := by
        calc
          (10 : ZMod 24650604817) ^ 19033 = (10 : ZMod 24650604817) ^ (9516 + 9516 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 9516 * (10 : ZMod 24650604817) ^ 9516) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 10601569971 := by rw [factor_2_13]; decide
      have factor_2_15 : (10 : ZMod 24650604817) ^ 38067 = 20552211686 := by
        calc
          (10 : ZMod 24650604817) ^ 38067 = (10 : ZMod 24650604817) ^ (19033 + 19033 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 19033 * (10 : ZMod 24650604817) ^ 19033) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 20552211686 := by rw [factor_2_14]; decide
      have factor_2_16 : (10 : ZMod 24650604817) ^ 76134 = 126316474 := by
        calc
          (10 : ZMod 24650604817) ^ 76134 = (10 : ZMod 24650604817) ^ (38067 + 38067) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 38067 * (10 : ZMod 24650604817) ^ 38067 := by rw [pow_add]
          _ = 126316474 := by rw [factor_2_15]; decide
      have factor_2_17 : (10 : ZMod 24650604817) ^ 152269 = 7226634709 := by
        calc
          (10 : ZMod 24650604817) ^ 152269 = (10 : ZMod 24650604817) ^ (76134 + 76134 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 76134 * (10 : ZMod 24650604817) ^ 76134) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 7226634709 := by rw [factor_2_16]; decide
      have factor_2_18 : (10 : ZMod 24650604817) ^ 304539 = 11385483750 := by
        calc
          (10 : ZMod 24650604817) ^ 304539 = (10 : ZMod 24650604817) ^ (152269 + 152269 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 152269 * (10 : ZMod 24650604817) ^ 152269) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 11385483750 := by rw [factor_2_17]; decide
      have factor_2_19 : (10 : ZMod 24650604817) ^ 609078 = 4973720757 := by
        calc
          (10 : ZMod 24650604817) ^ 609078 = (10 : ZMod 24650604817) ^ (304539 + 304539) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 304539 * (10 : ZMod 24650604817) ^ 304539 := by rw [pow_add]
          _ = 4973720757 := by rw [factor_2_18]; decide
      have factor_2_20 : (10 : ZMod 24650604817) ^ 1218156 = 13569572224 := by
        calc
          (10 : ZMod 24650604817) ^ 1218156 = (10 : ZMod 24650604817) ^ (609078 + 609078) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 609078 * (10 : ZMod 24650604817) ^ 609078 := by rw [pow_add]
          _ = 13569572224 := by rw [factor_2_19]; decide
      have factor_2_21 : (10 : ZMod 24650604817) ^ 2436312 = 2428961816 := by
        calc
          (10 : ZMod 24650604817) ^ 2436312 = (10 : ZMod 24650604817) ^ (1218156 + 1218156) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 1218156 * (10 : ZMod 24650604817) ^ 1218156 := by rw [pow_add]
          _ = 2428961816 := by rw [factor_2_20]; decide
      have factor_2_22 : (10 : ZMod 24650604817) ^ 4872624 = 9482397430 := by
        calc
          (10 : ZMod 24650604817) ^ 4872624 = (10 : ZMod 24650604817) ^ (2436312 + 2436312) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 2436312 * (10 : ZMod 24650604817) ^ 2436312 := by rw [pow_add]
          _ = 9482397430 := by rw [factor_2_21]; decide
      change (10 : ZMod 24650604817) ^ 4872624 ≠ 1
      rw [factor_2_22]
      decide
    ·
      have factor_3_0 : (10 : ZMod 24650604817) ^ 1 = 10 := by norm_num
      have factor_3_1 : (10 : ZMod 24650604817) ^ 3 = 1000 := by
        calc
          (10 : ZMod 24650604817) ^ 3 = (10 : ZMod 24650604817) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 1 * (10 : ZMod 24650604817) ^ 1) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_3_0]; decide
      have factor_3_2 : (10 : ZMod 24650604817) ^ 7 = 10000000 := by
        calc
          (10 : ZMod 24650604817) ^ 7 = (10 : ZMod 24650604817) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 3 * (10 : ZMod 24650604817) ^ 3) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 10000000 := by rw [factor_3_1]; decide
      have factor_3_3 : (10 : ZMod 24650604817) ^ 14 = 17146862248 := by
        calc
          (10 : ZMod 24650604817) ^ 14 = (10 : ZMod 24650604817) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 7 * (10 : ZMod 24650604817) ^ 7 := by rw [pow_add]
          _ = 17146862248 := by rw [factor_3_2]; decide
      have factor_3_4 : (10 : ZMod 24650604817) ^ 29 = 10933932642 := by
        calc
          (10 : ZMod 24650604817) ^ 29 = (10 : ZMod 24650604817) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 14 * (10 : ZMod 24650604817) ^ 14) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 10933932642 := by rw [factor_3_3]; decide
      have factor_3_5 : (10 : ZMod 24650604817) ^ 59 = 12284475352 := by
        calc
          (10 : ZMod 24650604817) ^ 59 = (10 : ZMod 24650604817) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 29 * (10 : ZMod 24650604817) ^ 29) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 12284475352 := by rw [factor_3_4]; decide
      have factor_3_6 : (10 : ZMod 24650604817) ^ 118 = 17783287082 := by
        calc
          (10 : ZMod 24650604817) ^ 118 = (10 : ZMod 24650604817) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 59 * (10 : ZMod 24650604817) ^ 59 := by rw [pow_add]
          _ = 17783287082 := by rw [factor_3_5]; decide
      have factor_3_7 : (10 : ZMod 24650604817) ^ 237 = 22434319107 := by
        calc
          (10 : ZMod 24650604817) ^ 237 = (10 : ZMod 24650604817) ^ (118 + 118 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 118 * (10 : ZMod 24650604817) ^ 118) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 22434319107 := by rw [factor_3_6]; decide
      have factor_3_8 : (10 : ZMod 24650604817) ^ 474 = 14414216971 := by
        calc
          (10 : ZMod 24650604817) ^ 474 = (10 : ZMod 24650604817) ^ (237 + 237) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 237 * (10 : ZMod 24650604817) ^ 237 := by rw [pow_add]
          _ = 14414216971 := by rw [factor_3_7]; decide
      have factor_3_9 : (10 : ZMod 24650604817) ^ 948 = 9167386532 := by
        calc
          (10 : ZMod 24650604817) ^ 948 = (10 : ZMod 24650604817) ^ (474 + 474) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 474 * (10 : ZMod 24650604817) ^ 474 := by rw [pow_add]
          _ = 9167386532 := by rw [factor_3_8]; decide
      have factor_3_10 : (10 : ZMod 24650604817) ^ 1897 = 4424824556 := by
        calc
          (10 : ZMod 24650604817) ^ 1897 = (10 : ZMod 24650604817) ^ (948 + 948 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 948 * (10 : ZMod 24650604817) ^ 948) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 4424824556 := by rw [factor_3_9]; decide
      have factor_3_11 : (10 : ZMod 24650604817) ^ 3794 = 20144967931 := by
        calc
          (10 : ZMod 24650604817) ^ 3794 = (10 : ZMod 24650604817) ^ (1897 + 1897) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 1897 * (10 : ZMod 24650604817) ^ 1897 := by rw [pow_add]
          _ = 20144967931 := by rw [factor_3_10]; decide
      have factor_3_12 : (10 : ZMod 24650604817) ^ 7588 = 23177891400 := by
        calc
          (10 : ZMod 24650604817) ^ 7588 = (10 : ZMod 24650604817) ^ (3794 + 3794) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 3794 * (10 : ZMod 24650604817) ^ 3794 := by rw [pow_add]
          _ = 23177891400 := by rw [factor_3_11]; decide
      have factor_3_13 : (10 : ZMod 24650604817) ^ 15177 = 3301083625 := by
        calc
          (10 : ZMod 24650604817) ^ 15177 = (10 : ZMod 24650604817) ^ (7588 + 7588 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = ((10 : ZMod 24650604817) ^ 7588 * (10 : ZMod 24650604817) ^ 7588) * (10 : ZMod 24650604817) := by rw [pow_succ, pow_add]
          _ = 3301083625 := by rw [factor_3_12]; decide
      have factor_3_14 : (10 : ZMod 24650604817) ^ 30354 = 21371867832 := by
        calc
          (10 : ZMod 24650604817) ^ 30354 = (10 : ZMod 24650604817) ^ (15177 + 15177) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 15177 * (10 : ZMod 24650604817) ^ 15177 := by rw [pow_add]
          _ = 21371867832 := by rw [factor_3_13]; decide
      have factor_3_15 : (10 : ZMod 24650604817) ^ 60708 = 3271042078 := by
        calc
          (10 : ZMod 24650604817) ^ 60708 = (10 : ZMod 24650604817) ^ (30354 + 30354) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 30354 * (10 : ZMod 24650604817) ^ 30354 := by rw [pow_add]
          _ = 3271042078 := by rw [factor_3_14]; decide
      have factor_3_16 : (10 : ZMod 24650604817) ^ 121416 = 23553218078 := by
        calc
          (10 : ZMod 24650604817) ^ 121416 = (10 : ZMod 24650604817) ^ (60708 + 60708) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 60708 * (10 : ZMod 24650604817) ^ 60708 := by rw [pow_add]
          _ = 23553218078 := by rw [factor_3_15]; decide
      have factor_3_17 : (10 : ZMod 24650604817) ^ 242832 = 6217630382 := by
        calc
          (10 : ZMod 24650604817) ^ 242832 = (10 : ZMod 24650604817) ^ (121416 + 121416) :=
            congrArg (fun n : ℕ => (10 : ZMod 24650604817) ^ n) (by norm_num)
          _ = (10 : ZMod 24650604817) ^ 121416 * (10 : ZMod 24650604817) ^ 121416 := by rw [pow_add]
          _ = 6217630382 := by rw [factor_3_16]; decide
      change (10 : ZMod 24650604817) ^ 242832 ≠ 1
      rw [factor_3_17]
      decide

#print axioms prime_lucas_24650604817

end TotientTailPeriodKiller
end Erdos249257
