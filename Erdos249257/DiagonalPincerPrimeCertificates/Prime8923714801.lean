import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_8923714801 : Nat.Prime 8923714801 := by
  apply lucas_primality 8923714801 (29 : ZMod 8923714801)
  ·
      have fermat_0 : (29 : ZMod 8923714801) ^ 1 = 29 := by norm_num
      have fermat_1 : (29 : ZMod 8923714801) ^ 2 = 841 := by
        calc
          (29 : ZMod 8923714801) ^ 2 = (29 : ZMod 8923714801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1 * (29 : ZMod 8923714801) ^ 1 := by rw [pow_add]
          _ = 841 := by rw [fermat_0]; decide
      have fermat_2 : (29 : ZMod 8923714801) ^ 4 = 707281 := by
        calc
          (29 : ZMod 8923714801) ^ 4 = (29 : ZMod 8923714801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 2 * (29 : ZMod 8923714801) ^ 2 := by rw [pow_add]
          _ = 707281 := by rw [fermat_1]; decide
      have fermat_3 : (29 : ZMod 8923714801) ^ 8 = 518384105 := by
        calc
          (29 : ZMod 8923714801) ^ 8 = (29 : ZMod 8923714801) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 4 * (29 : ZMod 8923714801) ^ 4 := by rw [pow_add]
          _ = 518384105 := by rw [fermat_2]; decide
      have fermat_4 : (29 : ZMod 8923714801) ^ 16 = 7738008173 := by
        calc
          (29 : ZMod 8923714801) ^ 16 = (29 : ZMod 8923714801) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 8 * (29 : ZMod 8923714801) ^ 8 := by rw [pow_add]
          _ = 7738008173 := by rw [fermat_3]; decide
      have fermat_5 : (29 : ZMod 8923714801) ^ 33 = 6858984872 := by
        calc
          (29 : ZMod 8923714801) ^ 33 = (29 : ZMod 8923714801) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 16 * (29 : ZMod 8923714801) ^ 16) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6858984872 := by rw [fermat_4]; decide
      have fermat_6 : (29 : ZMod 8923714801) ^ 66 = 5936144901 := by
        calc
          (29 : ZMod 8923714801) ^ 66 = (29 : ZMod 8923714801) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 33 * (29 : ZMod 8923714801) ^ 33 := by rw [pow_add]
          _ = 5936144901 := by rw [fermat_5]; decide
      have fermat_7 : (29 : ZMod 8923714801) ^ 132 = 2110373267 := by
        calc
          (29 : ZMod 8923714801) ^ 132 = (29 : ZMod 8923714801) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 66 * (29 : ZMod 8923714801) ^ 66 := by rw [pow_add]
          _ = 2110373267 := by rw [fermat_6]; decide
      have fermat_8 : (29 : ZMod 8923714801) ^ 265 = 8090996823 := by
        calc
          (29 : ZMod 8923714801) ^ 265 = (29 : ZMod 8923714801) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 132 * (29 : ZMod 8923714801) ^ 132) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 8090996823 := by rw [fermat_7]; decide
      have fermat_9 : (29 : ZMod 8923714801) ^ 531 = 3820241427 := by
        calc
          (29 : ZMod 8923714801) ^ 531 = (29 : ZMod 8923714801) ^ (265 + 265 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 265 * (29 : ZMod 8923714801) ^ 265) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 3820241427 := by rw [fermat_8]; decide
      have fermat_10 : (29 : ZMod 8923714801) ^ 1063 = 4842739166 := by
        calc
          (29 : ZMod 8923714801) ^ 1063 = (29 : ZMod 8923714801) ^ (531 + 531 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 531 * (29 : ZMod 8923714801) ^ 531) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 4842739166 := by rw [fermat_9]; decide
      have fermat_11 : (29 : ZMod 8923714801) ^ 2127 = 4002219232 := by
        calc
          (29 : ZMod 8923714801) ^ 2127 = (29 : ZMod 8923714801) ^ (1063 + 1063 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 1063 * (29 : ZMod 8923714801) ^ 1063) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 4002219232 := by rw [fermat_10]; decide
      have fermat_12 : (29 : ZMod 8923714801) ^ 4255 = 6581772807 := by
        calc
          (29 : ZMod 8923714801) ^ 4255 = (29 : ZMod 8923714801) ^ (2127 + 2127 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 2127 * (29 : ZMod 8923714801) ^ 2127) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6581772807 := by rw [fermat_11]; decide
      have fermat_13 : (29 : ZMod 8923714801) ^ 8510 = 6208722181 := by
        calc
          (29 : ZMod 8923714801) ^ 8510 = (29 : ZMod 8923714801) ^ (4255 + 4255) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 4255 * (29 : ZMod 8923714801) ^ 4255 := by rw [pow_add]
          _ = 6208722181 := by rw [fermat_12]; decide
      have fermat_14 : (29 : ZMod 8923714801) ^ 17020 = 828546380 := by
        calc
          (29 : ZMod 8923714801) ^ 17020 = (29 : ZMod 8923714801) ^ (8510 + 8510) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 8510 * (29 : ZMod 8923714801) ^ 8510 := by rw [pow_add]
          _ = 828546380 := by rw [fermat_13]; decide
      have fermat_15 : (29 : ZMod 8923714801) ^ 34041 = 3613328694 := by
        calc
          (29 : ZMod 8923714801) ^ 34041 = (29 : ZMod 8923714801) ^ (17020 + 17020 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 17020 * (29 : ZMod 8923714801) ^ 17020) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 3613328694 := by rw [fermat_14]; decide
      have fermat_16 : (29 : ZMod 8923714801) ^ 68082 = 3138324447 := by
        calc
          (29 : ZMod 8923714801) ^ 68082 = (29 : ZMod 8923714801) ^ (34041 + 34041) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 34041 * (29 : ZMod 8923714801) ^ 34041 := by rw [pow_add]
          _ = 3138324447 := by rw [fermat_15]; decide
      have fermat_17 : (29 : ZMod 8923714801) ^ 136165 = 176762252 := by
        calc
          (29 : ZMod 8923714801) ^ 136165 = (29 : ZMod 8923714801) ^ (68082 + 68082 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 68082 * (29 : ZMod 8923714801) ^ 68082) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 176762252 := by rw [fermat_16]; decide
      have fermat_18 : (29 : ZMod 8923714801) ^ 272330 = 5540496572 := by
        calc
          (29 : ZMod 8923714801) ^ 272330 = (29 : ZMod 8923714801) ^ (136165 + 136165) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 136165 * (29 : ZMod 8923714801) ^ 136165 := by rw [pow_add]
          _ = 5540496572 := by rw [fermat_17]; decide
      have fermat_19 : (29 : ZMod 8923714801) ^ 544660 = 206131798 := by
        calc
          (29 : ZMod 8923714801) ^ 544660 = (29 : ZMod 8923714801) ^ (272330 + 272330) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 272330 * (29 : ZMod 8923714801) ^ 272330 := by rw [pow_add]
          _ = 206131798 := by rw [fermat_18]; decide
      have fermat_20 : (29 : ZMod 8923714801) ^ 1089320 = 5503177299 := by
        calc
          (29 : ZMod 8923714801) ^ 1089320 = (29 : ZMod 8923714801) ^ (544660 + 544660) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 544660 * (29 : ZMod 8923714801) ^ 544660 := by rw [pow_add]
          _ = 5503177299 := by rw [fermat_19]; decide
      have fermat_21 : (29 : ZMod 8923714801) ^ 2178641 = 5321716999 := by
        calc
          (29 : ZMod 8923714801) ^ 2178641 = (29 : ZMod 8923714801) ^ (1089320 + 1089320 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 1089320 * (29 : ZMod 8923714801) ^ 1089320) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 5321716999 := by rw [fermat_20]; decide
      have fermat_22 : (29 : ZMod 8923714801) ^ 4357282 = 3429713680 := by
        calc
          (29 : ZMod 8923714801) ^ 4357282 = (29 : ZMod 8923714801) ^ (2178641 + 2178641) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 2178641 * (29 : ZMod 8923714801) ^ 2178641 := by rw [pow_add]
          _ = 3429713680 := by rw [fermat_21]; decide
      have fermat_23 : (29 : ZMod 8923714801) ^ 8714565 = 1482514132 := by
        calc
          (29 : ZMod 8923714801) ^ 8714565 = (29 : ZMod 8923714801) ^ (4357282 + 4357282 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 4357282 * (29 : ZMod 8923714801) ^ 4357282) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 1482514132 := by rw [fermat_22]; decide
      have fermat_24 : (29 : ZMod 8923714801) ^ 17429130 = 1198182862 := by
        calc
          (29 : ZMod 8923714801) ^ 17429130 = (29 : ZMod 8923714801) ^ (8714565 + 8714565) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 8714565 * (29 : ZMod 8923714801) ^ 8714565 := by rw [pow_add]
          _ = 1198182862 := by rw [fermat_23]; decide
      have fermat_25 : (29 : ZMod 8923714801) ^ 34858260 = 2275638012 := by
        calc
          (29 : ZMod 8923714801) ^ 34858260 = (29 : ZMod 8923714801) ^ (17429130 + 17429130) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 17429130 * (29 : ZMod 8923714801) ^ 17429130 := by rw [pow_add]
          _ = 2275638012 := by rw [fermat_24]; decide
      have fermat_26 : (29 : ZMod 8923714801) ^ 69716521 = 1077199245 := by
        calc
          (29 : ZMod 8923714801) ^ 69716521 = (29 : ZMod 8923714801) ^ (34858260 + 34858260 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 34858260 * (29 : ZMod 8923714801) ^ 34858260) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 1077199245 := by rw [fermat_25]; decide
      have fermat_27 : (29 : ZMod 8923714801) ^ 139433043 = 2380971299 := by
        calc
          (29 : ZMod 8923714801) ^ 139433043 = (29 : ZMod 8923714801) ^ (69716521 + 69716521 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 69716521 * (29 : ZMod 8923714801) ^ 69716521) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2380971299 := by rw [fermat_26]; decide
      have fermat_28 : (29 : ZMod 8923714801) ^ 278866087 = 2977456161 := by
        calc
          (29 : ZMod 8923714801) ^ 278866087 = (29 : ZMod 8923714801) ^ (139433043 + 139433043 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 139433043 * (29 : ZMod 8923714801) ^ 139433043) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2977456161 := by rw [fermat_27]; decide
      have fermat_29 : (29 : ZMod 8923714801) ^ 557732175 = 6734827160 := by
        calc
          (29 : ZMod 8923714801) ^ 557732175 = (29 : ZMod 8923714801) ^ (278866087 + 278866087 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 278866087 * (29 : ZMod 8923714801) ^ 278866087) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6734827160 := by rw [fermat_28]; decide
      have fermat_30 : (29 : ZMod 8923714801) ^ 1115464350 = 5766071574 := by
        calc
          (29 : ZMod 8923714801) ^ 1115464350 = (29 : ZMod 8923714801) ^ (557732175 + 557732175) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 557732175 * (29 : ZMod 8923714801) ^ 557732175 := by rw [pow_add]
          _ = 5766071574 := by rw [fermat_29]; decide
      have fermat_31 : (29 : ZMod 8923714801) ^ 2230928700 = 4406144164 := by
        calc
          (29 : ZMod 8923714801) ^ 2230928700 = (29 : ZMod 8923714801) ^ (1115464350 + 1115464350) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1115464350 * (29 : ZMod 8923714801) ^ 1115464350 := by rw [pow_add]
          _ = 4406144164 := by rw [fermat_30]; decide
      have fermat_32 : (29 : ZMod 8923714801) ^ 4461857400 = 8923714800 := by
        calc
          (29 : ZMod 8923714801) ^ 4461857400 = (29 : ZMod 8923714801) ^ (2230928700 + 2230928700) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 2230928700 * (29 : ZMod 8923714801) ^ 2230928700 := by rw [pow_add]
          _ = 8923714800 := by rw [fermat_31]; decide
      have fermat_33 : (29 : ZMod 8923714801) ^ 8923714800 = 1 := by
        calc
          (29 : ZMod 8923714801) ^ 8923714800 = (29 : ZMod 8923714801) ^ (4461857400 + 4461857400) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 4461857400 * (29 : ZMod 8923714801) ^ 4461857400 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 8923714801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (29 : ZMod 8923714801) ^ 1 = 29 := by norm_num
      have factor_0_1 : (29 : ZMod 8923714801) ^ 2 = 841 := by
        calc
          (29 : ZMod 8923714801) ^ 2 = (29 : ZMod 8923714801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1 * (29 : ZMod 8923714801) ^ 1 := by rw [pow_add]
          _ = 841 := by rw [factor_0_0]; decide
      have factor_0_2 : (29 : ZMod 8923714801) ^ 4 = 707281 := by
        calc
          (29 : ZMod 8923714801) ^ 4 = (29 : ZMod 8923714801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 2 * (29 : ZMod 8923714801) ^ 2 := by rw [pow_add]
          _ = 707281 := by rw [factor_0_1]; decide
      have factor_0_3 : (29 : ZMod 8923714801) ^ 8 = 518384105 := by
        calc
          (29 : ZMod 8923714801) ^ 8 = (29 : ZMod 8923714801) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 4 * (29 : ZMod 8923714801) ^ 4 := by rw [pow_add]
          _ = 518384105 := by rw [factor_0_2]; decide
      have factor_0_4 : (29 : ZMod 8923714801) ^ 16 = 7738008173 := by
        calc
          (29 : ZMod 8923714801) ^ 16 = (29 : ZMod 8923714801) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 8 * (29 : ZMod 8923714801) ^ 8 := by rw [pow_add]
          _ = 7738008173 := by rw [factor_0_3]; decide
      have factor_0_5 : (29 : ZMod 8923714801) ^ 33 = 6858984872 := by
        calc
          (29 : ZMod 8923714801) ^ 33 = (29 : ZMod 8923714801) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 16 * (29 : ZMod 8923714801) ^ 16) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6858984872 := by rw [factor_0_4]; decide
      have factor_0_6 : (29 : ZMod 8923714801) ^ 66 = 5936144901 := by
        calc
          (29 : ZMod 8923714801) ^ 66 = (29 : ZMod 8923714801) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 33 * (29 : ZMod 8923714801) ^ 33 := by rw [pow_add]
          _ = 5936144901 := by rw [factor_0_5]; decide
      have factor_0_7 : (29 : ZMod 8923714801) ^ 132 = 2110373267 := by
        calc
          (29 : ZMod 8923714801) ^ 132 = (29 : ZMod 8923714801) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 66 * (29 : ZMod 8923714801) ^ 66 := by rw [pow_add]
          _ = 2110373267 := by rw [factor_0_6]; decide
      have factor_0_8 : (29 : ZMod 8923714801) ^ 265 = 8090996823 := by
        calc
          (29 : ZMod 8923714801) ^ 265 = (29 : ZMod 8923714801) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 132 * (29 : ZMod 8923714801) ^ 132) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 8090996823 := by rw [factor_0_7]; decide
      have factor_0_9 : (29 : ZMod 8923714801) ^ 531 = 3820241427 := by
        calc
          (29 : ZMod 8923714801) ^ 531 = (29 : ZMod 8923714801) ^ (265 + 265 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 265 * (29 : ZMod 8923714801) ^ 265) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 3820241427 := by rw [factor_0_8]; decide
      have factor_0_10 : (29 : ZMod 8923714801) ^ 1063 = 4842739166 := by
        calc
          (29 : ZMod 8923714801) ^ 1063 = (29 : ZMod 8923714801) ^ (531 + 531 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 531 * (29 : ZMod 8923714801) ^ 531) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 4842739166 := by rw [factor_0_9]; decide
      have factor_0_11 : (29 : ZMod 8923714801) ^ 2127 = 4002219232 := by
        calc
          (29 : ZMod 8923714801) ^ 2127 = (29 : ZMod 8923714801) ^ (1063 + 1063 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 1063 * (29 : ZMod 8923714801) ^ 1063) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 4002219232 := by rw [factor_0_10]; decide
      have factor_0_12 : (29 : ZMod 8923714801) ^ 4255 = 6581772807 := by
        calc
          (29 : ZMod 8923714801) ^ 4255 = (29 : ZMod 8923714801) ^ (2127 + 2127 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 2127 * (29 : ZMod 8923714801) ^ 2127) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6581772807 := by rw [factor_0_11]; decide
      have factor_0_13 : (29 : ZMod 8923714801) ^ 8510 = 6208722181 := by
        calc
          (29 : ZMod 8923714801) ^ 8510 = (29 : ZMod 8923714801) ^ (4255 + 4255) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 4255 * (29 : ZMod 8923714801) ^ 4255 := by rw [pow_add]
          _ = 6208722181 := by rw [factor_0_12]; decide
      have factor_0_14 : (29 : ZMod 8923714801) ^ 17020 = 828546380 := by
        calc
          (29 : ZMod 8923714801) ^ 17020 = (29 : ZMod 8923714801) ^ (8510 + 8510) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 8510 * (29 : ZMod 8923714801) ^ 8510 := by rw [pow_add]
          _ = 828546380 := by rw [factor_0_13]; decide
      have factor_0_15 : (29 : ZMod 8923714801) ^ 34041 = 3613328694 := by
        calc
          (29 : ZMod 8923714801) ^ 34041 = (29 : ZMod 8923714801) ^ (17020 + 17020 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 17020 * (29 : ZMod 8923714801) ^ 17020) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 3613328694 := by rw [factor_0_14]; decide
      have factor_0_16 : (29 : ZMod 8923714801) ^ 68082 = 3138324447 := by
        calc
          (29 : ZMod 8923714801) ^ 68082 = (29 : ZMod 8923714801) ^ (34041 + 34041) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 34041 * (29 : ZMod 8923714801) ^ 34041 := by rw [pow_add]
          _ = 3138324447 := by rw [factor_0_15]; decide
      have factor_0_17 : (29 : ZMod 8923714801) ^ 136165 = 176762252 := by
        calc
          (29 : ZMod 8923714801) ^ 136165 = (29 : ZMod 8923714801) ^ (68082 + 68082 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 68082 * (29 : ZMod 8923714801) ^ 68082) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 176762252 := by rw [factor_0_16]; decide
      have factor_0_18 : (29 : ZMod 8923714801) ^ 272330 = 5540496572 := by
        calc
          (29 : ZMod 8923714801) ^ 272330 = (29 : ZMod 8923714801) ^ (136165 + 136165) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 136165 * (29 : ZMod 8923714801) ^ 136165 := by rw [pow_add]
          _ = 5540496572 := by rw [factor_0_17]; decide
      have factor_0_19 : (29 : ZMod 8923714801) ^ 544660 = 206131798 := by
        calc
          (29 : ZMod 8923714801) ^ 544660 = (29 : ZMod 8923714801) ^ (272330 + 272330) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 272330 * (29 : ZMod 8923714801) ^ 272330 := by rw [pow_add]
          _ = 206131798 := by rw [factor_0_18]; decide
      have factor_0_20 : (29 : ZMod 8923714801) ^ 1089320 = 5503177299 := by
        calc
          (29 : ZMod 8923714801) ^ 1089320 = (29 : ZMod 8923714801) ^ (544660 + 544660) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 544660 * (29 : ZMod 8923714801) ^ 544660 := by rw [pow_add]
          _ = 5503177299 := by rw [factor_0_19]; decide
      have factor_0_21 : (29 : ZMod 8923714801) ^ 2178641 = 5321716999 := by
        calc
          (29 : ZMod 8923714801) ^ 2178641 = (29 : ZMod 8923714801) ^ (1089320 + 1089320 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 1089320 * (29 : ZMod 8923714801) ^ 1089320) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 5321716999 := by rw [factor_0_20]; decide
      have factor_0_22 : (29 : ZMod 8923714801) ^ 4357282 = 3429713680 := by
        calc
          (29 : ZMod 8923714801) ^ 4357282 = (29 : ZMod 8923714801) ^ (2178641 + 2178641) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 2178641 * (29 : ZMod 8923714801) ^ 2178641 := by rw [pow_add]
          _ = 3429713680 := by rw [factor_0_21]; decide
      have factor_0_23 : (29 : ZMod 8923714801) ^ 8714565 = 1482514132 := by
        calc
          (29 : ZMod 8923714801) ^ 8714565 = (29 : ZMod 8923714801) ^ (4357282 + 4357282 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 4357282 * (29 : ZMod 8923714801) ^ 4357282) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 1482514132 := by rw [factor_0_22]; decide
      have factor_0_24 : (29 : ZMod 8923714801) ^ 17429130 = 1198182862 := by
        calc
          (29 : ZMod 8923714801) ^ 17429130 = (29 : ZMod 8923714801) ^ (8714565 + 8714565) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 8714565 * (29 : ZMod 8923714801) ^ 8714565 := by rw [pow_add]
          _ = 1198182862 := by rw [factor_0_23]; decide
      have factor_0_25 : (29 : ZMod 8923714801) ^ 34858260 = 2275638012 := by
        calc
          (29 : ZMod 8923714801) ^ 34858260 = (29 : ZMod 8923714801) ^ (17429130 + 17429130) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 17429130 * (29 : ZMod 8923714801) ^ 17429130 := by rw [pow_add]
          _ = 2275638012 := by rw [factor_0_24]; decide
      have factor_0_26 : (29 : ZMod 8923714801) ^ 69716521 = 1077199245 := by
        calc
          (29 : ZMod 8923714801) ^ 69716521 = (29 : ZMod 8923714801) ^ (34858260 + 34858260 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 34858260 * (29 : ZMod 8923714801) ^ 34858260) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 1077199245 := by rw [factor_0_25]; decide
      have factor_0_27 : (29 : ZMod 8923714801) ^ 139433043 = 2380971299 := by
        calc
          (29 : ZMod 8923714801) ^ 139433043 = (29 : ZMod 8923714801) ^ (69716521 + 69716521 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 69716521 * (29 : ZMod 8923714801) ^ 69716521) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2380971299 := by rw [factor_0_26]; decide
      have factor_0_28 : (29 : ZMod 8923714801) ^ 278866087 = 2977456161 := by
        calc
          (29 : ZMod 8923714801) ^ 278866087 = (29 : ZMod 8923714801) ^ (139433043 + 139433043 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 139433043 * (29 : ZMod 8923714801) ^ 139433043) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2977456161 := by rw [factor_0_27]; decide
      have factor_0_29 : (29 : ZMod 8923714801) ^ 557732175 = 6734827160 := by
        calc
          (29 : ZMod 8923714801) ^ 557732175 = (29 : ZMod 8923714801) ^ (278866087 + 278866087 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 278866087 * (29 : ZMod 8923714801) ^ 278866087) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6734827160 := by rw [factor_0_28]; decide
      have factor_0_30 : (29 : ZMod 8923714801) ^ 1115464350 = 5766071574 := by
        calc
          (29 : ZMod 8923714801) ^ 1115464350 = (29 : ZMod 8923714801) ^ (557732175 + 557732175) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 557732175 * (29 : ZMod 8923714801) ^ 557732175 := by rw [pow_add]
          _ = 5766071574 := by rw [factor_0_29]; decide
      have factor_0_31 : (29 : ZMod 8923714801) ^ 2230928700 = 4406144164 := by
        calc
          (29 : ZMod 8923714801) ^ 2230928700 = (29 : ZMod 8923714801) ^ (1115464350 + 1115464350) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1115464350 * (29 : ZMod 8923714801) ^ 1115464350 := by rw [pow_add]
          _ = 4406144164 := by rw [factor_0_30]; decide
      have factor_0_32 : (29 : ZMod 8923714801) ^ 4461857400 = 8923714800 := by
        calc
          (29 : ZMod 8923714801) ^ 4461857400 = (29 : ZMod 8923714801) ^ (2230928700 + 2230928700) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 2230928700 * (29 : ZMod 8923714801) ^ 2230928700 := by rw [pow_add]
          _ = 8923714800 := by rw [factor_0_31]; decide
      change (29 : ZMod 8923714801) ^ 4461857400 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (29 : ZMod 8923714801) ^ 1 = 29 := by norm_num
      have factor_1_1 : (29 : ZMod 8923714801) ^ 2 = 841 := by
        calc
          (29 : ZMod 8923714801) ^ 2 = (29 : ZMod 8923714801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1 * (29 : ZMod 8923714801) ^ 1 := by rw [pow_add]
          _ = 841 := by rw [factor_1_0]; decide
      have factor_1_2 : (29 : ZMod 8923714801) ^ 5 = 20511149 := by
        calc
          (29 : ZMod 8923714801) ^ 5 = (29 : ZMod 8923714801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 2 * (29 : ZMod 8923714801) ^ 2) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 20511149 := by rw [factor_1_1]; decide
      have factor_1_3 : (29 : ZMod 8923714801) ^ 11 = 6889778629 := by
        calc
          (29 : ZMod 8923714801) ^ 11 = (29 : ZMod 8923714801) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 5 * (29 : ZMod 8923714801) ^ 5) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6889778629 := by rw [factor_1_2]; decide
      have factor_1_4 : (29 : ZMod 8923714801) ^ 22 = 5725229830 := by
        calc
          (29 : ZMod 8923714801) ^ 22 = (29 : ZMod 8923714801) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 11 * (29 : ZMod 8923714801) ^ 11 := by rw [pow_add]
          _ = 5725229830 := by rw [factor_1_3]; decide
      have factor_1_5 : (29 : ZMod 8923714801) ^ 44 = 3986691772 := by
        calc
          (29 : ZMod 8923714801) ^ 44 = (29 : ZMod 8923714801) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 22 * (29 : ZMod 8923714801) ^ 22 := by rw [pow_add]
          _ = 3986691772 := by rw [factor_1_4]; decide
      have factor_1_6 : (29 : ZMod 8923714801) ^ 88 = 1695427524 := by
        calc
          (29 : ZMod 8923714801) ^ 88 = (29 : ZMod 8923714801) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 44 * (29 : ZMod 8923714801) ^ 44 := by rw [pow_add]
          _ = 1695427524 := by rw [factor_1_5]; decide
      have factor_1_7 : (29 : ZMod 8923714801) ^ 177 = 2061899195 := by
        calc
          (29 : ZMod 8923714801) ^ 177 = (29 : ZMod 8923714801) ^ (88 + 88 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 88 * (29 : ZMod 8923714801) ^ 88) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2061899195 := by rw [factor_1_6]; decide
      have factor_1_8 : (29 : ZMod 8923714801) ^ 354 = 184256512 := by
        calc
          (29 : ZMod 8923714801) ^ 354 = (29 : ZMod 8923714801) ^ (177 + 177) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 177 * (29 : ZMod 8923714801) ^ 177 := by rw [pow_add]
          _ = 184256512 := by rw [factor_1_7]; decide
      have factor_1_9 : (29 : ZMod 8923714801) ^ 709 = 281445061 := by
        calc
          (29 : ZMod 8923714801) ^ 709 = (29 : ZMod 8923714801) ^ (354 + 354 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 354 * (29 : ZMod 8923714801) ^ 354) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 281445061 := by rw [factor_1_8]; decide
      have factor_1_10 : (29 : ZMod 8923714801) ^ 1418 = 3625076425 := by
        calc
          (29 : ZMod 8923714801) ^ 1418 = (29 : ZMod 8923714801) ^ (709 + 709) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 709 * (29 : ZMod 8923714801) ^ 709 := by rw [pow_add]
          _ = 3625076425 := by rw [factor_1_9]; decide
      have factor_1_11 : (29 : ZMod 8923714801) ^ 2836 = 2490872351 := by
        calc
          (29 : ZMod 8923714801) ^ 2836 = (29 : ZMod 8923714801) ^ (1418 + 1418) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1418 * (29 : ZMod 8923714801) ^ 1418 := by rw [pow_add]
          _ = 2490872351 := by rw [factor_1_10]; decide
      have factor_1_12 : (29 : ZMod 8923714801) ^ 5673 = 1421837734 := by
        calc
          (29 : ZMod 8923714801) ^ 5673 = (29 : ZMod 8923714801) ^ (2836 + 2836 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 2836 * (29 : ZMod 8923714801) ^ 2836) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 1421837734 := by rw [factor_1_11]; decide
      have factor_1_13 : (29 : ZMod 8923714801) ^ 11347 = 7664871115 := by
        calc
          (29 : ZMod 8923714801) ^ 11347 = (29 : ZMod 8923714801) ^ (5673 + 5673 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 5673 * (29 : ZMod 8923714801) ^ 5673) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 7664871115 := by rw [factor_1_12]; decide
      have factor_1_14 : (29 : ZMod 8923714801) ^ 22694 = 7332527011 := by
        calc
          (29 : ZMod 8923714801) ^ 22694 = (29 : ZMod 8923714801) ^ (11347 + 11347) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 11347 * (29 : ZMod 8923714801) ^ 11347 := by rw [pow_add]
          _ = 7332527011 := by rw [factor_1_13]; decide
      have factor_1_15 : (29 : ZMod 8923714801) ^ 45388 = 1610640569 := by
        calc
          (29 : ZMod 8923714801) ^ 45388 = (29 : ZMod 8923714801) ^ (22694 + 22694) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 22694 * (29 : ZMod 8923714801) ^ 22694 := by rw [pow_add]
          _ = 1610640569 := by rw [factor_1_14]; decide
      have factor_1_16 : (29 : ZMod 8923714801) ^ 90776 = 1521111774 := by
        calc
          (29 : ZMod 8923714801) ^ 90776 = (29 : ZMod 8923714801) ^ (45388 + 45388) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 45388 * (29 : ZMod 8923714801) ^ 45388 := by rw [pow_add]
          _ = 1521111774 := by rw [factor_1_15]; decide
      have factor_1_17 : (29 : ZMod 8923714801) ^ 181553 = 6175998384 := by
        calc
          (29 : ZMod 8923714801) ^ 181553 = (29 : ZMod 8923714801) ^ (90776 + 90776 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 90776 * (29 : ZMod 8923714801) ^ 90776) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6175998384 := by rw [factor_1_16]; decide
      have factor_1_18 : (29 : ZMod 8923714801) ^ 363106 = 4710868988 := by
        calc
          (29 : ZMod 8923714801) ^ 363106 = (29 : ZMod 8923714801) ^ (181553 + 181553) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 181553 * (29 : ZMod 8923714801) ^ 181553 := by rw [pow_add]
          _ = 4710868988 := by rw [factor_1_17]; decide
      have factor_1_19 : (29 : ZMod 8923714801) ^ 726213 = 4627633032 := by
        calc
          (29 : ZMod 8923714801) ^ 726213 = (29 : ZMod 8923714801) ^ (363106 + 363106 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 363106 * (29 : ZMod 8923714801) ^ 363106) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 4627633032 := by rw [factor_1_18]; decide
      have factor_1_20 : (29 : ZMod 8923714801) ^ 1452427 = 3554214590 := by
        calc
          (29 : ZMod 8923714801) ^ 1452427 = (29 : ZMod 8923714801) ^ (726213 + 726213 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 726213 * (29 : ZMod 8923714801) ^ 726213) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 3554214590 := by rw [factor_1_19]; decide
      have factor_1_21 : (29 : ZMod 8923714801) ^ 2904855 = 1435400399 := by
        calc
          (29 : ZMod 8923714801) ^ 2904855 = (29 : ZMod 8923714801) ^ (1452427 + 1452427 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 1452427 * (29 : ZMod 8923714801) ^ 1452427) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 1435400399 := by rw [factor_1_20]; decide
      have factor_1_22 : (29 : ZMod 8923714801) ^ 5809710 = 6172608890 := by
        calc
          (29 : ZMod 8923714801) ^ 5809710 = (29 : ZMod 8923714801) ^ (2904855 + 2904855) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 2904855 * (29 : ZMod 8923714801) ^ 2904855 := by rw [pow_add]
          _ = 6172608890 := by rw [factor_1_21]; decide
      have factor_1_23 : (29 : ZMod 8923714801) ^ 11619420 = 7562170803 := by
        calc
          (29 : ZMod 8923714801) ^ 11619420 = (29 : ZMod 8923714801) ^ (5809710 + 5809710) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 5809710 * (29 : ZMod 8923714801) ^ 5809710 := by rw [pow_add]
          _ = 7562170803 := by rw [factor_1_22]; decide
      have factor_1_24 : (29 : ZMod 8923714801) ^ 23238840 = 4323830776 := by
        calc
          (29 : ZMod 8923714801) ^ 23238840 = (29 : ZMod 8923714801) ^ (11619420 + 11619420) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 11619420 * (29 : ZMod 8923714801) ^ 11619420 := by rw [pow_add]
          _ = 4323830776 := by rw [factor_1_23]; decide
      have factor_1_25 : (29 : ZMod 8923714801) ^ 46477681 = 3003236449 := by
        calc
          (29 : ZMod 8923714801) ^ 46477681 = (29 : ZMod 8923714801) ^ (23238840 + 23238840 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 23238840 * (29 : ZMod 8923714801) ^ 23238840) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 3003236449 := by rw [factor_1_24]; decide
      have factor_1_26 : (29 : ZMod 8923714801) ^ 92955362 = 3669827358 := by
        calc
          (29 : ZMod 8923714801) ^ 92955362 = (29 : ZMod 8923714801) ^ (46477681 + 46477681) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 46477681 * (29 : ZMod 8923714801) ^ 46477681 := by rw [pow_add]
          _ = 3669827358 := by rw [factor_1_25]; decide
      have factor_1_27 : (29 : ZMod 8923714801) ^ 185910725 = 2260322353 := by
        calc
          (29 : ZMod 8923714801) ^ 185910725 = (29 : ZMod 8923714801) ^ (92955362 + 92955362 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 92955362 * (29 : ZMod 8923714801) ^ 92955362) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2260322353 := by rw [factor_1_26]; decide
      have factor_1_28 : (29 : ZMod 8923714801) ^ 371821450 = 5582794789 := by
        calc
          (29 : ZMod 8923714801) ^ 371821450 = (29 : ZMod 8923714801) ^ (185910725 + 185910725) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 185910725 * (29 : ZMod 8923714801) ^ 185910725 := by rw [pow_add]
          _ = 5582794789 := by rw [factor_1_27]; decide
      have factor_1_29 : (29 : ZMod 8923714801) ^ 743642900 = 7138213373 := by
        calc
          (29 : ZMod 8923714801) ^ 743642900 = (29 : ZMod 8923714801) ^ (371821450 + 371821450) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 371821450 * (29 : ZMod 8923714801) ^ 371821450 := by rw [pow_add]
          _ = 7138213373 := by rw [factor_1_28]; decide
      have factor_1_30 : (29 : ZMod 8923714801) ^ 1487285800 = 5583450741 := by
        calc
          (29 : ZMod 8923714801) ^ 1487285800 = (29 : ZMod 8923714801) ^ (743642900 + 743642900) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 743642900 * (29 : ZMod 8923714801) ^ 743642900 := by rw [pow_add]
          _ = 5583450741 := by rw [factor_1_29]; decide
      have factor_1_31 : (29 : ZMod 8923714801) ^ 2974571600 = 5583450740 := by
        calc
          (29 : ZMod 8923714801) ^ 2974571600 = (29 : ZMod 8923714801) ^ (1487285800 + 1487285800) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1487285800 * (29 : ZMod 8923714801) ^ 1487285800 := by rw [pow_add]
          _ = 5583450740 := by rw [factor_1_30]; decide
      change (29 : ZMod 8923714801) ^ 2974571600 ≠ 1
      rw [factor_1_31]
      decide
    ·
      have factor_2_0 : (29 : ZMod 8923714801) ^ 1 = 29 := by norm_num
      have factor_2_1 : (29 : ZMod 8923714801) ^ 3 = 24389 := by
        calc
          (29 : ZMod 8923714801) ^ 3 = (29 : ZMod 8923714801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 1 * (29 : ZMod 8923714801) ^ 1) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 24389 := by rw [factor_2_0]; decide
      have factor_2_2 : (29 : ZMod 8923714801) ^ 6 = 594823321 := by
        calc
          (29 : ZMod 8923714801) ^ 6 = (29 : ZMod 8923714801) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 3 * (29 : ZMod 8923714801) ^ 3 := by rw [pow_add]
          _ = 594823321 := by rw [factor_2_1]; decide
      have factor_2_3 : (29 : ZMod 8923714801) ^ 13 = 2812921140 := by
        calc
          (29 : ZMod 8923714801) ^ 13 = (29 : ZMod 8923714801) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 6 * (29 : ZMod 8923714801) ^ 6) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2812921140 := by rw [factor_2_2]; decide
      have factor_2_4 : (29 : ZMod 8923714801) ^ 26 = 5442998057 := by
        calc
          (29 : ZMod 8923714801) ^ 26 = (29 : ZMod 8923714801) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 13 * (29 : ZMod 8923714801) ^ 13 := by rw [pow_add]
          _ = 5442998057 := by rw [factor_2_3]; decide
      have factor_2_5 : (29 : ZMod 8923714801) ^ 53 = 2140478699 := by
        calc
          (29 : ZMod 8923714801) ^ 53 = (29 : ZMod 8923714801) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 26 * (29 : ZMod 8923714801) ^ 26) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2140478699 := by rw [factor_2_4]; decide
      have factor_2_6 : (29 : ZMod 8923714801) ^ 106 = 7366697034 := by
        calc
          (29 : ZMod 8923714801) ^ 106 = (29 : ZMod 8923714801) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 53 * (29 : ZMod 8923714801) ^ 53 := by rw [pow_add]
          _ = 7366697034 := by rw [factor_2_5]; decide
      have factor_2_7 : (29 : ZMod 8923714801) ^ 212 = 2857212832 := by
        calc
          (29 : ZMod 8923714801) ^ 212 = (29 : ZMod 8923714801) ^ (106 + 106) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 106 * (29 : ZMod 8923714801) ^ 106 := by rw [pow_add]
          _ = 2857212832 := by rw [factor_2_6]; decide
      have factor_2_8 : (29 : ZMod 8923714801) ^ 425 = 6600483236 := by
        calc
          (29 : ZMod 8923714801) ^ 425 = (29 : ZMod 8923714801) ^ (212 + 212 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 212 * (29 : ZMod 8923714801) ^ 212) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6600483236 := by rw [factor_2_7]; decide
      have factor_2_9 : (29 : ZMod 8923714801) ^ 851 = 5785619878 := by
        calc
          (29 : ZMod 8923714801) ^ 851 = (29 : ZMod 8923714801) ^ (425 + 425 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 425 * (29 : ZMod 8923714801) ^ 425) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 5785619878 := by rw [factor_2_8]; decide
      have factor_2_10 : (29 : ZMod 8923714801) ^ 1702 = 3332657218 := by
        calc
          (29 : ZMod 8923714801) ^ 1702 = (29 : ZMod 8923714801) ^ (851 + 851) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 851 * (29 : ZMod 8923714801) ^ 851 := by rw [pow_add]
          _ = 3332657218 := by rw [factor_2_9]; decide
      have factor_2_11 : (29 : ZMod 8923714801) ^ 3404 = 4426885262 := by
        calc
          (29 : ZMod 8923714801) ^ 3404 = (29 : ZMod 8923714801) ^ (1702 + 1702) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1702 * (29 : ZMod 8923714801) ^ 1702 := by rw [pow_add]
          _ = 4426885262 := by rw [factor_2_10]; decide
      have factor_2_12 : (29 : ZMod 8923714801) ^ 6808 = 8508283427 := by
        calc
          (29 : ZMod 8923714801) ^ 6808 = (29 : ZMod 8923714801) ^ (3404 + 3404) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 3404 * (29 : ZMod 8923714801) ^ 3404 := by rw [pow_add]
          _ = 8508283427 := by rw [factor_2_11]; decide
      have factor_2_13 : (29 : ZMod 8923714801) ^ 13616 = 1122841235 := by
        calc
          (29 : ZMod 8923714801) ^ 13616 = (29 : ZMod 8923714801) ^ (6808 + 6808) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 6808 * (29 : ZMod 8923714801) ^ 6808 := by rw [pow_add]
          _ = 1122841235 := by rw [factor_2_12]; decide
      have factor_2_14 : (29 : ZMod 8923714801) ^ 27233 = 7172055194 := by
        calc
          (29 : ZMod 8923714801) ^ 27233 = (29 : ZMod 8923714801) ^ (13616 + 13616 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 13616 * (29 : ZMod 8923714801) ^ 13616) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 7172055194 := by rw [factor_2_13]; decide
      have factor_2_15 : (29 : ZMod 8923714801) ^ 54466 = 3573206947 := by
        calc
          (29 : ZMod 8923714801) ^ 54466 = (29 : ZMod 8923714801) ^ (27233 + 27233) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 27233 * (29 : ZMod 8923714801) ^ 27233 := by rw [pow_add]
          _ = 3573206947 := by rw [factor_2_14]; decide
      have factor_2_16 : (29 : ZMod 8923714801) ^ 108932 = 360021268 := by
        calc
          (29 : ZMod 8923714801) ^ 108932 = (29 : ZMod 8923714801) ^ (54466 + 54466) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 54466 * (29 : ZMod 8923714801) ^ 54466 := by rw [pow_add]
          _ = 360021268 := by rw [factor_2_15]; decide
      have factor_2_17 : (29 : ZMod 8923714801) ^ 217864 = 6815041009 := by
        calc
          (29 : ZMod 8923714801) ^ 217864 = (29 : ZMod 8923714801) ^ (108932 + 108932) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 108932 * (29 : ZMod 8923714801) ^ 108932 := by rw [pow_add]
          _ = 6815041009 := by rw [factor_2_16]; decide
      have factor_2_18 : (29 : ZMod 8923714801) ^ 435728 = 3503007251 := by
        calc
          (29 : ZMod 8923714801) ^ 435728 = (29 : ZMod 8923714801) ^ (217864 + 217864) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 217864 * (29 : ZMod 8923714801) ^ 217864 := by rw [pow_add]
          _ = 3503007251 := by rw [factor_2_17]; decide
      have factor_2_19 : (29 : ZMod 8923714801) ^ 871456 = 2983465525 := by
        calc
          (29 : ZMod 8923714801) ^ 871456 = (29 : ZMod 8923714801) ^ (435728 + 435728) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 435728 * (29 : ZMod 8923714801) ^ 435728 := by rw [pow_add]
          _ = 2983465525 := by rw [factor_2_18]; decide
      have factor_2_20 : (29 : ZMod 8923714801) ^ 1742913 = 5026091516 := by
        calc
          (29 : ZMod 8923714801) ^ 1742913 = (29 : ZMod 8923714801) ^ (871456 + 871456 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 871456 * (29 : ZMod 8923714801) ^ 871456) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 5026091516 := by rw [factor_2_19]; decide
      have factor_2_21 : (29 : ZMod 8923714801) ^ 3485826 = 5788510900 := by
        calc
          (29 : ZMod 8923714801) ^ 3485826 = (29 : ZMod 8923714801) ^ (1742913 + 1742913) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1742913 * (29 : ZMod 8923714801) ^ 1742913 := by rw [pow_add]
          _ = 5788510900 := by rw [factor_2_20]; decide
      have factor_2_22 : (29 : ZMod 8923714801) ^ 6971652 = 4051433455 := by
        calc
          (29 : ZMod 8923714801) ^ 6971652 = (29 : ZMod 8923714801) ^ (3485826 + 3485826) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 3485826 * (29 : ZMod 8923714801) ^ 3485826 := by rw [pow_add]
          _ = 4051433455 := by rw [factor_2_21]; decide
      have factor_2_23 : (29 : ZMod 8923714801) ^ 13943304 = 6417536248 := by
        calc
          (29 : ZMod 8923714801) ^ 13943304 = (29 : ZMod 8923714801) ^ (6971652 + 6971652) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 6971652 * (29 : ZMod 8923714801) ^ 6971652 := by rw [pow_add]
          _ = 6417536248 := by rw [factor_2_22]; decide
      have factor_2_24 : (29 : ZMod 8923714801) ^ 27886608 = 3903095092 := by
        calc
          (29 : ZMod 8923714801) ^ 27886608 = (29 : ZMod 8923714801) ^ (13943304 + 13943304) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 13943304 * (29 : ZMod 8923714801) ^ 13943304 := by rw [pow_add]
          _ = 3903095092 := by rw [factor_2_23]; decide
      have factor_2_25 : (29 : ZMod 8923714801) ^ 55773217 = 2977084846 := by
        calc
          (29 : ZMod 8923714801) ^ 55773217 = (29 : ZMod 8923714801) ^ (27886608 + 27886608 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 27886608 * (29 : ZMod 8923714801) ^ 27886608) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2977084846 := by rw [factor_2_24]; decide
      have factor_2_26 : (29 : ZMod 8923714801) ^ 111546435 = 5556596485 := by
        calc
          (29 : ZMod 8923714801) ^ 111546435 = (29 : ZMod 8923714801) ^ (55773217 + 55773217 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 55773217 * (29 : ZMod 8923714801) ^ 55773217) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 5556596485 := by rw [factor_2_25]; decide
      have factor_2_27 : (29 : ZMod 8923714801) ^ 223092870 = 3523026779 := by
        calc
          (29 : ZMod 8923714801) ^ 223092870 = (29 : ZMod 8923714801) ^ (111546435 + 111546435) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 111546435 * (29 : ZMod 8923714801) ^ 111546435 := by rw [pow_add]
          _ = 3523026779 := by rw [factor_2_26]; decide
      have factor_2_28 : (29 : ZMod 8923714801) ^ 446185740 = 1887937508 := by
        calc
          (29 : ZMod 8923714801) ^ 446185740 = (29 : ZMod 8923714801) ^ (223092870 + 223092870) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 223092870 * (29 : ZMod 8923714801) ^ 223092870 := by rw [pow_add]
          _ = 1887937508 := by rw [factor_2_27]; decide
      have factor_2_29 : (29 : ZMod 8923714801) ^ 892371480 = 1065667503 := by
        calc
          (29 : ZMod 8923714801) ^ 892371480 = (29 : ZMod 8923714801) ^ (446185740 + 446185740) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 446185740 * (29 : ZMod 8923714801) ^ 446185740 := by rw [pow_add]
          _ = 1065667503 := by rw [factor_2_28]; decide
      have factor_2_30 : (29 : ZMod 8923714801) ^ 1784742960 = 3975255697 := by
        calc
          (29 : ZMod 8923714801) ^ 1784742960 = (29 : ZMod 8923714801) ^ (892371480 + 892371480) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 892371480 * (29 : ZMod 8923714801) ^ 892371480 := by rw [pow_add]
          _ = 3975255697 := by rw [factor_2_29]; decide
      change (29 : ZMod 8923714801) ^ 1784742960 ≠ 1
      rw [factor_2_30]
      decide
    ·
      have factor_3_0 : (29 : ZMod 8923714801) ^ 1 = 29 := by norm_num
      have factor_3_1 : (29 : ZMod 8923714801) ^ 2 = 841 := by
        calc
          (29 : ZMod 8923714801) ^ 2 = (29 : ZMod 8923714801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1 * (29 : ZMod 8923714801) ^ 1 := by rw [pow_add]
          _ = 841 := by rw [factor_3_0]; decide
      have factor_3_2 : (29 : ZMod 8923714801) ^ 4 = 707281 := by
        calc
          (29 : ZMod 8923714801) ^ 4 = (29 : ZMod 8923714801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 2 * (29 : ZMod 8923714801) ^ 2 := by rw [pow_add]
          _ = 707281 := by rw [factor_3_1]; decide
      have factor_3_3 : (29 : ZMod 8923714801) ^ 9 = 6109424244 := by
        calc
          (29 : ZMod 8923714801) ^ 9 = (29 : ZMod 8923714801) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 4 * (29 : ZMod 8923714801) ^ 4) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6109424244 := by rw [factor_3_2]; decide
      have factor_3_4 : (29 : ZMod 8923714801) ^ 18 = 2276783564 := by
        calc
          (29 : ZMod 8923714801) ^ 18 = (29 : ZMod 8923714801) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 9 * (29 : ZMod 8923714801) ^ 9 := by rw [pow_add]
          _ = 2276783564 := by rw [factor_3_3]; decide
      have factor_3_5 : (29 : ZMod 8923714801) ^ 37 = 3830840999 := by
        calc
          (29 : ZMod 8923714801) ^ 37 = (29 : ZMod 8923714801) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 18 * (29 : ZMod 8923714801) ^ 18) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 3830840999 := by rw [factor_3_4]; decide
      have factor_3_6 : (29 : ZMod 8923714801) ^ 75 = 1976073747 := by
        calc
          (29 : ZMod 8923714801) ^ 75 = (29 : ZMod 8923714801) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 37 * (29 : ZMod 8923714801) ^ 37) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 1976073747 := by rw [factor_3_5]; decide
      have factor_3_7 : (29 : ZMod 8923714801) ^ 151 = 372146992 := by
        calc
          (29 : ZMod 8923714801) ^ 151 = (29 : ZMod 8923714801) ^ (75 + 75 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 75 * (29 : ZMod 8923714801) ^ 75) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 372146992 := by rw [factor_3_6]; decide
      have factor_3_8 : (29 : ZMod 8923714801) ^ 303 = 8347756934 := by
        calc
          (29 : ZMod 8923714801) ^ 303 = (29 : ZMod 8923714801) ^ (151 + 151 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 151 * (29 : ZMod 8923714801) ^ 151) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 8347756934 := by rw [factor_3_7]; decide
      have factor_3_9 : (29 : ZMod 8923714801) ^ 607 = 8090192587 := by
        calc
          (29 : ZMod 8923714801) ^ 607 = (29 : ZMod 8923714801) ^ (303 + 303 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 303 * (29 : ZMod 8923714801) ^ 303) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 8090192587 := by rw [factor_3_8]; decide
      have factor_3_10 : (29 : ZMod 8923714801) ^ 1215 = 6636223023 := by
        calc
          (29 : ZMod 8923714801) ^ 1215 = (29 : ZMod 8923714801) ^ (607 + 607 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 607 * (29 : ZMod 8923714801) ^ 607) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6636223023 := by rw [factor_3_9]; decide
      have factor_3_11 : (29 : ZMod 8923714801) ^ 2431 = 5901667485 := by
        calc
          (29 : ZMod 8923714801) ^ 2431 = (29 : ZMod 8923714801) ^ (1215 + 1215 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 1215 * (29 : ZMod 8923714801) ^ 1215) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 5901667485 := by rw [factor_3_10]; decide
      have factor_3_12 : (29 : ZMod 8923714801) ^ 4863 = 6996109059 := by
        calc
          (29 : ZMod 8923714801) ^ 4863 = (29 : ZMod 8923714801) ^ (2431 + 2431 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 2431 * (29 : ZMod 8923714801) ^ 2431) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6996109059 := by rw [factor_3_11]; decide
      have factor_3_13 : (29 : ZMod 8923714801) ^ 9726 = 5059413321 := by
        calc
          (29 : ZMod 8923714801) ^ 9726 = (29 : ZMod 8923714801) ^ (4863 + 4863) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 4863 * (29 : ZMod 8923714801) ^ 4863 := by rw [pow_add]
          _ = 5059413321 := by rw [factor_3_12]; decide
      have factor_3_14 : (29 : ZMod 8923714801) ^ 19452 = 6955914471 := by
        calc
          (29 : ZMod 8923714801) ^ 19452 = (29 : ZMod 8923714801) ^ (9726 + 9726) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 9726 * (29 : ZMod 8923714801) ^ 9726 := by rw [pow_add]
          _ = 6955914471 := by rw [factor_3_13]; decide
      have factor_3_15 : (29 : ZMod 8923714801) ^ 38904 = 5561592598 := by
        calc
          (29 : ZMod 8923714801) ^ 38904 = (29 : ZMod 8923714801) ^ (19452 + 19452) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 19452 * (29 : ZMod 8923714801) ^ 19452 := by rw [pow_add]
          _ = 5561592598 := by rw [factor_3_14]; decide
      have factor_3_16 : (29 : ZMod 8923714801) ^ 77808 = 8380117627 := by
        calc
          (29 : ZMod 8923714801) ^ 77808 = (29 : ZMod 8923714801) ^ (38904 + 38904) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 38904 * (29 : ZMod 8923714801) ^ 38904 := by rw [pow_add]
          _ = 8380117627 := by rw [factor_3_15]; decide
      have factor_3_17 : (29 : ZMod 8923714801) ^ 155617 = 3231909718 := by
        calc
          (29 : ZMod 8923714801) ^ 155617 = (29 : ZMod 8923714801) ^ (77808 + 77808 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 77808 * (29 : ZMod 8923714801) ^ 77808) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 3231909718 := by rw [factor_3_16]; decide
      have factor_3_18 : (29 : ZMod 8923714801) ^ 311234 = 427048710 := by
        calc
          (29 : ZMod 8923714801) ^ 311234 = (29 : ZMod 8923714801) ^ (155617 + 155617) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 155617 * (29 : ZMod 8923714801) ^ 155617 := by rw [pow_add]
          _ = 427048710 := by rw [factor_3_17]; decide
      have factor_3_19 : (29 : ZMod 8923714801) ^ 622468 = 5565107077 := by
        calc
          (29 : ZMod 8923714801) ^ 622468 = (29 : ZMod 8923714801) ^ (311234 + 311234) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 311234 * (29 : ZMod 8923714801) ^ 311234 := by rw [pow_add]
          _ = 5565107077 := by rw [factor_3_18]; decide
      have factor_3_20 : (29 : ZMod 8923714801) ^ 1244937 = 7400258271 := by
        calc
          (29 : ZMod 8923714801) ^ 1244937 = (29 : ZMod 8923714801) ^ (622468 + 622468 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 622468 * (29 : ZMod 8923714801) ^ 622468) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 7400258271 := by rw [factor_3_19]; decide
      have factor_3_21 : (29 : ZMod 8923714801) ^ 2489875 = 897908736 := by
        calc
          (29 : ZMod 8923714801) ^ 2489875 = (29 : ZMod 8923714801) ^ (1244937 + 1244937 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 1244937 * (29 : ZMod 8923714801) ^ 1244937) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 897908736 := by rw [factor_3_20]; decide
      have factor_3_22 : (29 : ZMod 8923714801) ^ 4979751 = 2645053766 := by
        calc
          (29 : ZMod 8923714801) ^ 4979751 = (29 : ZMod 8923714801) ^ (2489875 + 2489875 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 2489875 * (29 : ZMod 8923714801) ^ 2489875) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2645053766 := by rw [factor_3_21]; decide
      have factor_3_23 : (29 : ZMod 8923714801) ^ 9959503 = 1931312833 := by
        calc
          (29 : ZMod 8923714801) ^ 9959503 = (29 : ZMod 8923714801) ^ (4979751 + 4979751 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 4979751 * (29 : ZMod 8923714801) ^ 4979751) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 1931312833 := by rw [factor_3_22]; decide
      have factor_3_24 : (29 : ZMod 8923714801) ^ 19919006 = 1121345173 := by
        calc
          (29 : ZMod 8923714801) ^ 19919006 = (29 : ZMod 8923714801) ^ (9959503 + 9959503) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 9959503 * (29 : ZMod 8923714801) ^ 9959503 := by rw [pow_add]
          _ = 1121345173 := by rw [factor_3_23]; decide
      have factor_3_25 : (29 : ZMod 8923714801) ^ 39838012 = 81542804 := by
        calc
          (29 : ZMod 8923714801) ^ 39838012 = (29 : ZMod 8923714801) ^ (19919006 + 19919006) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 19919006 * (29 : ZMod 8923714801) ^ 19919006 := by rw [pow_add]
          _ = 81542804 := by rw [factor_3_24]; decide
      have factor_3_26 : (29 : ZMod 8923714801) ^ 79676025 = 1473336415 := by
        calc
          (29 : ZMod 8923714801) ^ 79676025 = (29 : ZMod 8923714801) ^ (39838012 + 39838012 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 39838012 * (29 : ZMod 8923714801) ^ 39838012) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 1473336415 := by rw [factor_3_25]; decide
      have factor_3_27 : (29 : ZMod 8923714801) ^ 159352050 = 522839648 := by
        calc
          (29 : ZMod 8923714801) ^ 159352050 = (29 : ZMod 8923714801) ^ (79676025 + 79676025) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 79676025 * (29 : ZMod 8923714801) ^ 79676025 := by rw [pow_add]
          _ = 522839648 := by rw [factor_3_26]; decide
      have factor_3_28 : (29 : ZMod 8923714801) ^ 318704100 = 8709951177 := by
        calc
          (29 : ZMod 8923714801) ^ 318704100 = (29 : ZMod 8923714801) ^ (159352050 + 159352050) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 159352050 * (29 : ZMod 8923714801) ^ 159352050 := by rw [pow_add]
          _ = 8709951177 := by rw [factor_3_27]; decide
      have factor_3_29 : (29 : ZMod 8923714801) ^ 637408200 = 5851035164 := by
        calc
          (29 : ZMod 8923714801) ^ 637408200 = (29 : ZMod 8923714801) ^ (318704100 + 318704100) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 318704100 * (29 : ZMod 8923714801) ^ 318704100 := by rw [pow_add]
          _ = 5851035164 := by rw [factor_3_28]; decide
      have factor_3_30 : (29 : ZMod 8923714801) ^ 1274816400 = 1642130337 := by
        calc
          (29 : ZMod 8923714801) ^ 1274816400 = (29 : ZMod 8923714801) ^ (637408200 + 637408200) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 637408200 * (29 : ZMod 8923714801) ^ 637408200 := by rw [pow_add]
          _ = 1642130337 := by rw [factor_3_29]; decide
      change (29 : ZMod 8923714801) ^ 1274816400 ≠ 1
      rw [factor_3_30]
      decide
    ·
      have factor_4_0 : (29 : ZMod 8923714801) ^ 1 = 29 := by norm_num
      have factor_4_1 : (29 : ZMod 8923714801) ^ 3 = 24389 := by
        calc
          (29 : ZMod 8923714801) ^ 3 = (29 : ZMod 8923714801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 1 * (29 : ZMod 8923714801) ^ 1) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 24389 := by rw [factor_4_0]; decide
      have factor_4_2 : (29 : ZMod 8923714801) ^ 6 = 594823321 := by
        calc
          (29 : ZMod 8923714801) ^ 6 = (29 : ZMod 8923714801) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 3 * (29 : ZMod 8923714801) ^ 3 := by rw [pow_add]
          _ = 594823321 := by rw [factor_4_1]; decide
      have factor_4_3 : (29 : ZMod 8923714801) ^ 12 = 3481854619 := by
        calc
          (29 : ZMod 8923714801) ^ 12 = (29 : ZMod 8923714801) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 6 * (29 : ZMod 8923714801) ^ 6 := by rw [pow_add]
          _ = 3481854619 := by rw [factor_4_2]; decide
      have factor_4_4 : (29 : ZMod 8923714801) ^ 24 = 5036009291 := by
        calc
          (29 : ZMod 8923714801) ^ 24 = (29 : ZMod 8923714801) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 12 * (29 : ZMod 8923714801) ^ 12 := by rw [pow_add]
          _ = 5036009291 := by rw [factor_4_3]; decide
      have factor_4_5 : (29 : ZMod 8923714801) ^ 48 = 4864086753 := by
        calc
          (29 : ZMod 8923714801) ^ 48 = (29 : ZMod 8923714801) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 24 * (29 : ZMod 8923714801) ^ 24 := by rw [pow_add]
          _ = 4864086753 := by rw [factor_4_4]; decide
      have factor_4_6 : (29 : ZMod 8923714801) ^ 96 = 1255423988 := by
        calc
          (29 : ZMod 8923714801) ^ 96 = (29 : ZMod 8923714801) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 48 * (29 : ZMod 8923714801) ^ 48 := by rw [pow_add]
          _ = 1255423988 := by rw [factor_4_5]; decide
      have factor_4_7 : (29 : ZMod 8923714801) ^ 193 = 7404729408 := by
        calc
          (29 : ZMod 8923714801) ^ 193 = (29 : ZMod 8923714801) ^ (96 + 96 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 96 * (29 : ZMod 8923714801) ^ 96) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 7404729408 := by rw [factor_4_6]; decide
      have factor_4_8 : (29 : ZMod 8923714801) ^ 386 = 6058179946 := by
        calc
          (29 : ZMod 8923714801) ^ 386 = (29 : ZMod 8923714801) ^ (193 + 193) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 193 * (29 : ZMod 8923714801) ^ 193 := by rw [pow_add]
          _ = 6058179946 := by rw [factor_4_7]; decide
      have factor_4_9 : (29 : ZMod 8923714801) ^ 773 = 8194373606 := by
        calc
          (29 : ZMod 8923714801) ^ 773 = (29 : ZMod 8923714801) ^ (386 + 386 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 386 * (29 : ZMod 8923714801) ^ 386) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 8194373606 := by rw [factor_4_8]; decide
      have factor_4_10 : (29 : ZMod 8923714801) ^ 1547 = 996636721 := by
        calc
          (29 : ZMod 8923714801) ^ 1547 = (29 : ZMod 8923714801) ^ (773 + 773 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 773 * (29 : ZMod 8923714801) ^ 773) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 996636721 := by rw [factor_4_9]; decide
      have factor_4_11 : (29 : ZMod 8923714801) ^ 3094 = 6912555804 := by
        calc
          (29 : ZMod 8923714801) ^ 3094 = (29 : ZMod 8923714801) ^ (1547 + 1547) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1547 * (29 : ZMod 8923714801) ^ 1547 := by rw [pow_add]
          _ = 6912555804 := by rw [factor_4_10]; decide
      have factor_4_12 : (29 : ZMod 8923714801) ^ 6189 = 2123198654 := by
        calc
          (29 : ZMod 8923714801) ^ 6189 = (29 : ZMod 8923714801) ^ (3094 + 3094 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 3094 * (29 : ZMod 8923714801) ^ 3094) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2123198654 := by rw [factor_4_11]; decide
      have factor_4_13 : (29 : ZMod 8923714801) ^ 12378 = 7175424812 := by
        calc
          (29 : ZMod 8923714801) ^ 12378 = (29 : ZMod 8923714801) ^ (6189 + 6189) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 6189 * (29 : ZMod 8923714801) ^ 6189 := by rw [pow_add]
          _ = 7175424812 := by rw [factor_4_12]; decide
      have factor_4_14 : (29 : ZMod 8923714801) ^ 24757 = 5729581653 := by
        calc
          (29 : ZMod 8923714801) ^ 24757 = (29 : ZMod 8923714801) ^ (12378 + 12378 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 12378 * (29 : ZMod 8923714801) ^ 12378) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 5729581653 := by rw [factor_4_13]; decide
      have factor_4_15 : (29 : ZMod 8923714801) ^ 49514 = 8462606320 := by
        calc
          (29 : ZMod 8923714801) ^ 49514 = (29 : ZMod 8923714801) ^ (24757 + 24757) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 24757 * (29 : ZMod 8923714801) ^ 24757 := by rw [pow_add]
          _ = 8462606320 := by rw [factor_4_14]; decide
      have factor_4_16 : (29 : ZMod 8923714801) ^ 99029 = 6564975713 := by
        calc
          (29 : ZMod 8923714801) ^ 99029 = (29 : ZMod 8923714801) ^ (49514 + 49514 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 49514 * (29 : ZMod 8923714801) ^ 49514) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6564975713 := by rw [factor_4_15]; decide
      have factor_4_17 : (29 : ZMod 8923714801) ^ 198058 = 1132091804 := by
        calc
          (29 : ZMod 8923714801) ^ 198058 = (29 : ZMod 8923714801) ^ (99029 + 99029) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 99029 * (29 : ZMod 8923714801) ^ 99029 := by rw [pow_add]
          _ = 1132091804 := by rw [factor_4_16]; decide
      have factor_4_18 : (29 : ZMod 8923714801) ^ 396116 = 8705611128 := by
        calc
          (29 : ZMod 8923714801) ^ 396116 = (29 : ZMod 8923714801) ^ (198058 + 198058) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 198058 * (29 : ZMod 8923714801) ^ 198058 := by rw [pow_add]
          _ = 8705611128 := by rw [factor_4_17]; decide
      have factor_4_19 : (29 : ZMod 8923714801) ^ 792233 = 5190905653 := by
        calc
          (29 : ZMod 8923714801) ^ 792233 = (29 : ZMod 8923714801) ^ (396116 + 396116 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 396116 * (29 : ZMod 8923714801) ^ 396116) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 5190905653 := by rw [factor_4_18]; decide
      have factor_4_20 : (29 : ZMod 8923714801) ^ 1584466 = 5014812187 := by
        calc
          (29 : ZMod 8923714801) ^ 1584466 = (29 : ZMod 8923714801) ^ (792233 + 792233) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 792233 * (29 : ZMod 8923714801) ^ 792233 := by rw [pow_add]
          _ = 5014812187 := by rw [factor_4_19]; decide
      have factor_4_21 : (29 : ZMod 8923714801) ^ 3168932 = 6583337038 := by
        calc
          (29 : ZMod 8923714801) ^ 3168932 = (29 : ZMod 8923714801) ^ (1584466 + 1584466) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1584466 * (29 : ZMod 8923714801) ^ 1584466 := by rw [pow_add]
          _ = 6583337038 := by rw [factor_4_20]; decide
      have factor_4_22 : (29 : ZMod 8923714801) ^ 6337865 = 1080671131 := by
        calc
          (29 : ZMod 8923714801) ^ 6337865 = (29 : ZMod 8923714801) ^ (3168932 + 3168932 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 3168932 * (29 : ZMod 8923714801) ^ 3168932) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 1080671131 := by rw [factor_4_21]; decide
      have factor_4_23 : (29 : ZMod 8923714801) ^ 12675731 = 5626888174 := by
        calc
          (29 : ZMod 8923714801) ^ 12675731 = (29 : ZMod 8923714801) ^ (6337865 + 6337865 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 6337865 * (29 : ZMod 8923714801) ^ 6337865) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 5626888174 := by rw [factor_4_22]; decide
      have factor_4_24 : (29 : ZMod 8923714801) ^ 25351462 = 992712438 := by
        calc
          (29 : ZMod 8923714801) ^ 25351462 = (29 : ZMod 8923714801) ^ (12675731 + 12675731) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 12675731 * (29 : ZMod 8923714801) ^ 12675731 := by rw [pow_add]
          _ = 992712438 := by rw [factor_4_23]; decide
      have factor_4_25 : (29 : ZMod 8923714801) ^ 50702925 = 4968603767 := by
        calc
          (29 : ZMod 8923714801) ^ 50702925 = (29 : ZMod 8923714801) ^ (25351462 + 25351462 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 25351462 * (29 : ZMod 8923714801) ^ 25351462) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 4968603767 := by rw [factor_4_24]; decide
      have factor_4_26 : (29 : ZMod 8923714801) ^ 101405850 = 8705985680 := by
        calc
          (29 : ZMod 8923714801) ^ 101405850 = (29 : ZMod 8923714801) ^ (50702925 + 50702925) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 50702925 * (29 : ZMod 8923714801) ^ 50702925 := by rw [pow_add]
          _ = 8705985680 := by rw [factor_4_25]; decide
      have factor_4_27 : (29 : ZMod 8923714801) ^ 202811700 = 2418621883 := by
        calc
          (29 : ZMod 8923714801) ^ 202811700 = (29 : ZMod 8923714801) ^ (101405850 + 101405850) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 101405850 * (29 : ZMod 8923714801) ^ 101405850 := by rw [pow_add]
          _ = 2418621883 := by rw [factor_4_26]; decide
      have factor_4_28 : (29 : ZMod 8923714801) ^ 405623400 = 5793580358 := by
        calc
          (29 : ZMod 8923714801) ^ 405623400 = (29 : ZMod 8923714801) ^ (202811700 + 202811700) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 202811700 * (29 : ZMod 8923714801) ^ 202811700 := by rw [pow_add]
          _ = 5793580358 := by rw [factor_4_27]; decide
      have factor_4_29 : (29 : ZMod 8923714801) ^ 811246800 = 221917168 := by
        calc
          (29 : ZMod 8923714801) ^ 811246800 = (29 : ZMod 8923714801) ^ (405623400 + 405623400) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 405623400 * (29 : ZMod 8923714801) ^ 405623400 := by rw [pow_add]
          _ = 221917168 := by rw [factor_4_28]; decide
      change (29 : ZMod 8923714801) ^ 811246800 ≠ 1
      rw [factor_4_29]
      decide
    ·
      have factor_5_0 : (29 : ZMod 8923714801) ^ 1 = 29 := by norm_num
      have factor_5_1 : (29 : ZMod 8923714801) ^ 2 = 841 := by
        calc
          (29 : ZMod 8923714801) ^ 2 = (29 : ZMod 8923714801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1 * (29 : ZMod 8923714801) ^ 1 := by rw [pow_add]
          _ = 841 := by rw [factor_5_0]; decide
      have factor_5_2 : (29 : ZMod 8923714801) ^ 5 = 20511149 := by
        calc
          (29 : ZMod 8923714801) ^ 5 = (29 : ZMod 8923714801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 2 * (29 : ZMod 8923714801) ^ 2) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 20511149 := by rw [factor_5_1]; decide
      have factor_5_3 : (29 : ZMod 8923714801) ^ 10 = 7622721857 := by
        calc
          (29 : ZMod 8923714801) ^ 10 = (29 : ZMod 8923714801) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 5 * (29 : ZMod 8923714801) ^ 5 := by rw [pow_add]
          _ = 7622721857 := by rw [factor_5_2]; decide
      have factor_5_4 : (29 : ZMod 8923714801) ^ 20 = 5100009910 := by
        calc
          (29 : ZMod 8923714801) ^ 20 = (29 : ZMod 8923714801) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 10 * (29 : ZMod 8923714801) ^ 10 := by rw [pow_add]
          _ = 5100009910 := by rw [factor_5_3]; decide
      have factor_5_5 : (29 : ZMod 8923714801) ^ 40 = 8010872942 := by
        calc
          (29 : ZMod 8923714801) ^ 40 = (29 : ZMod 8923714801) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 20 * (29 : ZMod 8923714801) ^ 20 := by rw [pow_add]
          _ = 8010872942 := by rw [factor_5_4]; decide
      have factor_5_6 : (29 : ZMod 8923714801) ^ 81 = 8049285289 := by
        calc
          (29 : ZMod 8923714801) ^ 81 = (29 : ZMod 8923714801) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 40 * (29 : ZMod 8923714801) ^ 40) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 8049285289 := by rw [factor_5_5]; decide
      have factor_5_7 : (29 : ZMod 8923714801) ^ 163 = 6581885753 := by
        calc
          (29 : ZMod 8923714801) ^ 163 = (29 : ZMod 8923714801) ^ (81 + 81 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 81 * (29 : ZMod 8923714801) ^ 81) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6581885753 := by rw [factor_5_6]; decide
      have factor_5_8 : (29 : ZMod 8923714801) ^ 327 = 1433900171 := by
        calc
          (29 : ZMod 8923714801) ^ 327 = (29 : ZMod 8923714801) ^ (163 + 163 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 163 * (29 : ZMod 8923714801) ^ 163) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 1433900171 := by rw [factor_5_7]; decide
      have factor_5_9 : (29 : ZMod 8923714801) ^ 654 = 4815355708 := by
        calc
          (29 : ZMod 8923714801) ^ 654 = (29 : ZMod 8923714801) ^ (327 + 327) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 327 * (29 : ZMod 8923714801) ^ 327 := by rw [pow_add]
          _ = 4815355708 := by rw [factor_5_8]; decide
      have factor_5_10 : (29 : ZMod 8923714801) ^ 1309 = 1107432638 := by
        calc
          (29 : ZMod 8923714801) ^ 1309 = (29 : ZMod 8923714801) ^ (654 + 654 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 654 * (29 : ZMod 8923714801) ^ 654) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 1107432638 := by rw [factor_5_9]; decide
      have factor_5_11 : (29 : ZMod 8923714801) ^ 2618 = 5418715500 := by
        calc
          (29 : ZMod 8923714801) ^ 2618 = (29 : ZMod 8923714801) ^ (1309 + 1309) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1309 * (29 : ZMod 8923714801) ^ 1309 := by rw [pow_add]
          _ = 5418715500 := by rw [factor_5_10]; decide
      have factor_5_12 : (29 : ZMod 8923714801) ^ 5237 = 6623731686 := by
        calc
          (29 : ZMod 8923714801) ^ 5237 = (29 : ZMod 8923714801) ^ (2618 + 2618 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 2618 * (29 : ZMod 8923714801) ^ 2618) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6623731686 := by rw [factor_5_11]; decide
      have factor_5_13 : (29 : ZMod 8923714801) ^ 10474 = 4164668679 := by
        calc
          (29 : ZMod 8923714801) ^ 10474 = (29 : ZMod 8923714801) ^ (5237 + 5237) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 5237 * (29 : ZMod 8923714801) ^ 5237 := by rw [pow_add]
          _ = 4164668679 := by rw [factor_5_12]; decide
      have factor_5_14 : (29 : ZMod 8923714801) ^ 20948 = 5270198512 := by
        calc
          (29 : ZMod 8923714801) ^ 20948 = (29 : ZMod 8923714801) ^ (10474 + 10474) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 10474 * (29 : ZMod 8923714801) ^ 10474 := by rw [pow_add]
          _ = 5270198512 := by rw [factor_5_13]; decide
      have factor_5_15 : (29 : ZMod 8923714801) ^ 41896 = 8622268785 := by
        calc
          (29 : ZMod 8923714801) ^ 41896 = (29 : ZMod 8923714801) ^ (20948 + 20948) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 20948 * (29 : ZMod 8923714801) ^ 20948 := by rw [pow_add]
          _ = 8622268785 := by rw [factor_5_14]; decide
      have factor_5_16 : (29 : ZMod 8923714801) ^ 83793 = 4731233208 := by
        calc
          (29 : ZMod 8923714801) ^ 83793 = (29 : ZMod 8923714801) ^ (41896 + 41896 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 41896 * (29 : ZMod 8923714801) ^ 41896) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 4731233208 := by rw [factor_5_15]; decide
      have factor_5_17 : (29 : ZMod 8923714801) ^ 167587 = 6193831981 := by
        calc
          (29 : ZMod 8923714801) ^ 167587 = (29 : ZMod 8923714801) ^ (83793 + 83793 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 83793 * (29 : ZMod 8923714801) ^ 83793) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6193831981 := by rw [factor_5_16]; decide
      have factor_5_18 : (29 : ZMod 8923714801) ^ 335175 = 6014174379 := by
        calc
          (29 : ZMod 8923714801) ^ 335175 = (29 : ZMod 8923714801) ^ (167587 + 167587 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 167587 * (29 : ZMod 8923714801) ^ 167587) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6014174379 := by rw [factor_5_17]; decide
      have factor_5_19 : (29 : ZMod 8923714801) ^ 670351 = 2808384704 := by
        calc
          (29 : ZMod 8923714801) ^ 670351 = (29 : ZMod 8923714801) ^ (335175 + 335175 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 335175 * (29 : ZMod 8923714801) ^ 335175) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2808384704 := by rw [factor_5_18]; decide
      have factor_5_20 : (29 : ZMod 8923714801) ^ 1340702 = 4219477305 := by
        calc
          (29 : ZMod 8923714801) ^ 1340702 = (29 : ZMod 8923714801) ^ (670351 + 670351) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 670351 * (29 : ZMod 8923714801) ^ 670351 := by rw [pow_add]
          _ = 4219477305 := by rw [factor_5_19]; decide
      have factor_5_21 : (29 : ZMod 8923714801) ^ 2681404 = 1077915851 := by
        calc
          (29 : ZMod 8923714801) ^ 2681404 = (29 : ZMod 8923714801) ^ (1340702 + 1340702) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1340702 * (29 : ZMod 8923714801) ^ 1340702 := by rw [pow_add]
          _ = 1077915851 := by rw [factor_5_20]; decide
      have factor_5_22 : (29 : ZMod 8923714801) ^ 5362809 = 7282591165 := by
        calc
          (29 : ZMod 8923714801) ^ 5362809 = (29 : ZMod 8923714801) ^ (2681404 + 2681404 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 2681404 * (29 : ZMod 8923714801) ^ 2681404) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 7282591165 := by rw [factor_5_21]; decide
      have factor_5_23 : (29 : ZMod 8923714801) ^ 10725618 = 7088585808 := by
        calc
          (29 : ZMod 8923714801) ^ 10725618 = (29 : ZMod 8923714801) ^ (5362809 + 5362809) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 5362809 * (29 : ZMod 8923714801) ^ 5362809 := by rw [pow_add]
          _ = 7088585808 := by rw [factor_5_22]; decide
      have factor_5_24 : (29 : ZMod 8923714801) ^ 21451237 = 7422530717 := by
        calc
          (29 : ZMod 8923714801) ^ 21451237 = (29 : ZMod 8923714801) ^ (10725618 + 10725618 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 10725618 * (29 : ZMod 8923714801) ^ 10725618) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 7422530717 := by rw [factor_5_23]; decide
      have factor_5_25 : (29 : ZMod 8923714801) ^ 42902475 = 6907550381 := by
        calc
          (29 : ZMod 8923714801) ^ 42902475 = (29 : ZMod 8923714801) ^ (21451237 + 21451237 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 21451237 * (29 : ZMod 8923714801) ^ 21451237) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6907550381 := by rw [factor_5_24]; decide
      have factor_5_26 : (29 : ZMod 8923714801) ^ 85804950 = 3151657700 := by
        calc
          (29 : ZMod 8923714801) ^ 85804950 = (29 : ZMod 8923714801) ^ (42902475 + 42902475) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 42902475 * (29 : ZMod 8923714801) ^ 42902475 := by rw [pow_add]
          _ = 3151657700 := by rw [factor_5_25]; decide
      have factor_5_27 : (29 : ZMod 8923714801) ^ 171609900 = 5115682560 := by
        calc
          (29 : ZMod 8923714801) ^ 171609900 = (29 : ZMod 8923714801) ^ (85804950 + 85804950) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 85804950 * (29 : ZMod 8923714801) ^ 85804950 := by rw [pow_add]
          _ = 5115682560 := by rw [factor_5_26]; decide
      have factor_5_28 : (29 : ZMod 8923714801) ^ 343219800 = 883409901 := by
        calc
          (29 : ZMod 8923714801) ^ 343219800 = (29 : ZMod 8923714801) ^ (171609900 + 171609900) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 171609900 * (29 : ZMod 8923714801) ^ 171609900 := by rw [pow_add]
          _ = 883409901 := by rw [factor_5_27]; decide
      have factor_5_29 : (29 : ZMod 8923714801) ^ 686439600 = 7085977170 := by
        calc
          (29 : ZMod 8923714801) ^ 686439600 = (29 : ZMod 8923714801) ^ (343219800 + 343219800) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 343219800 * (29 : ZMod 8923714801) ^ 343219800 := by rw [pow_add]
          _ = 7085977170 := by rw [factor_5_28]; decide
      change (29 : ZMod 8923714801) ^ 686439600 ≠ 1
      rw [factor_5_29]
      decide
    ·
      have factor_6_0 : (29 : ZMod 8923714801) ^ 1 = 29 := by norm_num
      have factor_6_1 : (29 : ZMod 8923714801) ^ 3 = 24389 := by
        calc
          (29 : ZMod 8923714801) ^ 3 = (29 : ZMod 8923714801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 1 * (29 : ZMod 8923714801) ^ 1) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 24389 := by rw [factor_6_0]; decide
      have factor_6_2 : (29 : ZMod 8923714801) ^ 7 = 8326161508 := by
        calc
          (29 : ZMod 8923714801) ^ 7 = (29 : ZMod 8923714801) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 3 * (29 : ZMod 8923714801) ^ 3) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 8326161508 := by rw [factor_6_1]; decide
      have factor_6_3 : (29 : ZMod 8923714801) ^ 15 = 882256475 := by
        calc
          (29 : ZMod 8923714801) ^ 15 = (29 : ZMod 8923714801) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 7 * (29 : ZMod 8923714801) ^ 7) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 882256475 := by rw [factor_6_2]; decide
      have factor_6_4 : (29 : ZMod 8923714801) ^ 31 = 2300096768 := by
        calc
          (29 : ZMod 8923714801) ^ 31 = (29 : ZMod 8923714801) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 15 * (29 : ZMod 8923714801) ^ 15) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2300096768 := by rw [factor_6_3]; decide
      have factor_6_5 : (29 : ZMod 8923714801) ^ 62 = 3364565091 := by
        calc
          (29 : ZMod 8923714801) ^ 62 = (29 : ZMod 8923714801) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 31 * (29 : ZMod 8923714801) ^ 31 := by rw [pow_add]
          _ = 3364565091 := by rw [factor_6_4]; decide
      have factor_6_6 : (29 : ZMod 8923714801) ^ 125 = 5827251495 := by
        calc
          (29 : ZMod 8923714801) ^ 125 = (29 : ZMod 8923714801) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 62 * (29 : ZMod 8923714801) ^ 62) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 5827251495 := by rw [factor_6_5]; decide
      have factor_6_7 : (29 : ZMod 8923714801) ^ 250 = 3342306477 := by
        calc
          (29 : ZMod 8923714801) ^ 250 = (29 : ZMod 8923714801) ^ (125 + 125) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 125 * (29 : ZMod 8923714801) ^ 125 := by rw [pow_add]
          _ = 3342306477 := by rw [factor_6_6]; decide
      have factor_6_8 : (29 : ZMod 8923714801) ^ 500 = 2556659194 := by
        calc
          (29 : ZMod 8923714801) ^ 500 = (29 : ZMod 8923714801) ^ (250 + 250) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 250 * (29 : ZMod 8923714801) ^ 250 := by rw [pow_add]
          _ = 2556659194 := by rw [factor_6_7]; decide
      have factor_6_9 : (29 : ZMod 8923714801) ^ 1001 = 8144995505 := by
        calc
          (29 : ZMod 8923714801) ^ 1001 = (29 : ZMod 8923714801) ^ (500 + 500 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 500 * (29 : ZMod 8923714801) ^ 500) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 8144995505 := by rw [factor_6_8]; decide
      have factor_6_10 : (29 : ZMod 8923714801) ^ 2002 = 2259487834 := by
        calc
          (29 : ZMod 8923714801) ^ 2002 = (29 : ZMod 8923714801) ^ (1001 + 1001) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1001 * (29 : ZMod 8923714801) ^ 1001 := by rw [pow_add]
          _ = 2259487834 := by rw [factor_6_9]; decide
      have factor_6_11 : (29 : ZMod 8923714801) ^ 4004 = 4953721615 := by
        calc
          (29 : ZMod 8923714801) ^ 4004 = (29 : ZMod 8923714801) ^ (2002 + 2002) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 2002 * (29 : ZMod 8923714801) ^ 2002 := by rw [pow_add]
          _ = 4953721615 := by rw [factor_6_10]; decide
      have factor_6_12 : (29 : ZMod 8923714801) ^ 8009 = 7499439584 := by
        calc
          (29 : ZMod 8923714801) ^ 8009 = (29 : ZMod 8923714801) ^ (4004 + 4004 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 4004 * (29 : ZMod 8923714801) ^ 4004) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 7499439584 := by rw [factor_6_11]; decide
      have factor_6_13 : (29 : ZMod 8923714801) ^ 16019 = 12565589 := by
        calc
          (29 : ZMod 8923714801) ^ 16019 = (29 : ZMod 8923714801) ^ (8009 + 8009 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 8009 * (29 : ZMod 8923714801) ^ 8009) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 12565589 := by rw [factor_6_12]; decide
      have factor_6_14 : (29 : ZMod 8923714801) ^ 32038 = 6740942828 := by
        calc
          (29 : ZMod 8923714801) ^ 32038 = (29 : ZMod 8923714801) ^ (16019 + 16019) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 16019 * (29 : ZMod 8923714801) ^ 16019 := by rw [pow_add]
          _ = 6740942828 := by rw [factor_6_13]; decide
      have factor_6_15 : (29 : ZMod 8923714801) ^ 64077 = 5963701370 := by
        calc
          (29 : ZMod 8923714801) ^ 64077 = (29 : ZMod 8923714801) ^ (32038 + 32038 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 32038 * (29 : ZMod 8923714801) ^ 32038) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 5963701370 := by rw [factor_6_14]; decide
      have factor_6_16 : (29 : ZMod 8923714801) ^ 128155 = 7415848517 := by
        calc
          (29 : ZMod 8923714801) ^ 128155 = (29 : ZMod 8923714801) ^ (64077 + 64077 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 64077 * (29 : ZMod 8923714801) ^ 64077) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 7415848517 := by rw [factor_6_15]; decide
      have factor_6_17 : (29 : ZMod 8923714801) ^ 256310 = 867618464 := by
        calc
          (29 : ZMod 8923714801) ^ 256310 = (29 : ZMod 8923714801) ^ (128155 + 128155) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 128155 * (29 : ZMod 8923714801) ^ 128155 := by rw [pow_add]
          _ = 867618464 := by rw [factor_6_16]; decide
      have factor_6_18 : (29 : ZMod 8923714801) ^ 512621 = 8371917415 := by
        calc
          (29 : ZMod 8923714801) ^ 512621 = (29 : ZMod 8923714801) ^ (256310 + 256310 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 256310 * (29 : ZMod 8923714801) ^ 256310) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 8371917415 := by rw [factor_6_17]; decide
      have factor_6_19 : (29 : ZMod 8923714801) ^ 1025242 = 2572699437 := by
        calc
          (29 : ZMod 8923714801) ^ 1025242 = (29 : ZMod 8923714801) ^ (512621 + 512621) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 512621 * (29 : ZMod 8923714801) ^ 512621 := by rw [pow_add]
          _ = 2572699437 := by rw [factor_6_18]; decide
      have factor_6_20 : (29 : ZMod 8923714801) ^ 2050485 = 3212385359 := by
        calc
          (29 : ZMod 8923714801) ^ 2050485 = (29 : ZMod 8923714801) ^ (1025242 + 1025242 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 1025242 * (29 : ZMod 8923714801) ^ 1025242) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 3212385359 := by rw [factor_6_19]; decide
      have factor_6_21 : (29 : ZMod 8923714801) ^ 4100971 = 7977493287 := by
        calc
          (29 : ZMod 8923714801) ^ 4100971 = (29 : ZMod 8923714801) ^ (2050485 + 2050485 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 2050485 * (29 : ZMod 8923714801) ^ 2050485) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 7977493287 := by rw [factor_6_20]; decide
      have factor_6_22 : (29 : ZMod 8923714801) ^ 8201943 = 2059982434 := by
        calc
          (29 : ZMod 8923714801) ^ 8201943 = (29 : ZMod 8923714801) ^ (4100971 + 4100971 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 4100971 * (29 : ZMod 8923714801) ^ 4100971) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2059982434 := by rw [factor_6_21]; decide
      have factor_6_23 : (29 : ZMod 8923714801) ^ 16403887 = 6113564563 := by
        calc
          (29 : ZMod 8923714801) ^ 16403887 = (29 : ZMod 8923714801) ^ (8201943 + 8201943 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 8201943 * (29 : ZMod 8923714801) ^ 8201943) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6113564563 := by rw [factor_6_22]; decide
      have factor_6_24 : (29 : ZMod 8923714801) ^ 32807775 = 2256928076 := by
        calc
          (29 : ZMod 8923714801) ^ 32807775 = (29 : ZMod 8923714801) ^ (16403887 + 16403887 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 16403887 * (29 : ZMod 8923714801) ^ 16403887) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2256928076 := by rw [factor_6_23]; decide
      have factor_6_25 : (29 : ZMod 8923714801) ^ 65615550 = 4509196564 := by
        calc
          (29 : ZMod 8923714801) ^ 65615550 = (29 : ZMod 8923714801) ^ (32807775 + 32807775) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 32807775 * (29 : ZMod 8923714801) ^ 32807775 := by rw [pow_add]
          _ = 4509196564 := by rw [factor_6_24]; decide
      have factor_6_26 : (29 : ZMod 8923714801) ^ 131231100 = 8443120305 := by
        calc
          (29 : ZMod 8923714801) ^ 131231100 = (29 : ZMod 8923714801) ^ (65615550 + 65615550) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 65615550 * (29 : ZMod 8923714801) ^ 65615550 := by rw [pow_add]
          _ = 8443120305 := by rw [factor_6_25]; decide
      have factor_6_27 : (29 : ZMod 8923714801) ^ 262462200 = 5033008778 := by
        calc
          (29 : ZMod 8923714801) ^ 262462200 = (29 : ZMod 8923714801) ^ (131231100 + 131231100) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 131231100 * (29 : ZMod 8923714801) ^ 131231100 := by rw [pow_add]
          _ = 5033008778 := by rw [factor_6_26]; decide
      have factor_6_28 : (29 : ZMod 8923714801) ^ 524924400 = 3318230966 := by
        calc
          (29 : ZMod 8923714801) ^ 524924400 = (29 : ZMod 8923714801) ^ (262462200 + 262462200) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 262462200 * (29 : ZMod 8923714801) ^ 262462200 := by rw [pow_add]
          _ = 3318230966 := by rw [factor_6_27]; decide
      change (29 : ZMod 8923714801) ^ 524924400 ≠ 1
      rw [factor_6_28]
      decide
    ·
      have factor_7_0 : (29 : ZMod 8923714801) ^ 1 = 29 := by norm_num
      have factor_7_1 : (29 : ZMod 8923714801) ^ 3 = 24389 := by
        calc
          (29 : ZMod 8923714801) ^ 3 = (29 : ZMod 8923714801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 1 * (29 : ZMod 8923714801) ^ 1) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 24389 := by rw [factor_7_0]; decide
      have factor_7_2 : (29 : ZMod 8923714801) ^ 6 = 594823321 := by
        calc
          (29 : ZMod 8923714801) ^ 6 = (29 : ZMod 8923714801) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 3 * (29 : ZMod 8923714801) ^ 3 := by rw [pow_add]
          _ = 594823321 := by rw [factor_7_1]; decide
      have factor_7_3 : (29 : ZMod 8923714801) ^ 13 = 2812921140 := by
        calc
          (29 : ZMod 8923714801) ^ 13 = (29 : ZMod 8923714801) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 6 * (29 : ZMod 8923714801) ^ 6) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2812921140 := by rw [factor_7_2]; decide
      have factor_7_4 : (29 : ZMod 8923714801) ^ 27 = 6143792036 := by
        calc
          (29 : ZMod 8923714801) ^ 27 = (29 : ZMod 8923714801) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 13 * (29 : ZMod 8923714801) ^ 13) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6143792036 := by rw [factor_7_3]; decide
      have factor_7_5 : (29 : ZMod 8923714801) ^ 55 = 6475910858 := by
        calc
          (29 : ZMod 8923714801) ^ 55 = (29 : ZMod 8923714801) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 27 * (29 : ZMod 8923714801) ^ 27) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6475910858 := by rw [factor_7_4]; decide
      have factor_7_6 : (29 : ZMod 8923714801) ^ 111 = 2810093721 := by
        calc
          (29 : ZMod 8923714801) ^ 111 = (29 : ZMod 8923714801) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 55 * (29 : ZMod 8923714801) ^ 55) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2810093721 := by rw [factor_7_5]; decide
      have factor_7_7 : (29 : ZMod 8923714801) ^ 223 = 2048026243 := by
        calc
          (29 : ZMod 8923714801) ^ 223 = (29 : ZMod 8923714801) ^ (111 + 111 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 111 * (29 : ZMod 8923714801) ^ 111) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2048026243 := by rw [factor_7_6]; decide
      have factor_7_8 : (29 : ZMod 8923714801) ^ 447 = 7488359093 := by
        calc
          (29 : ZMod 8923714801) ^ 447 = (29 : ZMod 8923714801) ^ (223 + 223 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 223 * (29 : ZMod 8923714801) ^ 223) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 7488359093 := by rw [factor_7_7]; decide
      have factor_7_9 : (29 : ZMod 8923714801) ^ 895 = 6611471353 := by
        calc
          (29 : ZMod 8923714801) ^ 895 = (29 : ZMod 8923714801) ^ (447 + 447 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 447 * (29 : ZMod 8923714801) ^ 447) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6611471353 := by rw [factor_7_8]; decide
      have factor_7_10 : (29 : ZMod 8923714801) ^ 1791 = 6805746547 := by
        calc
          (29 : ZMod 8923714801) ^ 1791 = (29 : ZMod 8923714801) ^ (895 + 895 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 895 * (29 : ZMod 8923714801) ^ 895) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6805746547 := by rw [factor_7_9]; decide
      have factor_7_11 : (29 : ZMod 8923714801) ^ 3583 = 6268981920 := by
        calc
          (29 : ZMod 8923714801) ^ 3583 = (29 : ZMod 8923714801) ^ (1791 + 1791 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 1791 * (29 : ZMod 8923714801) ^ 1791) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6268981920 := by rw [factor_7_10]; decide
      have factor_7_12 : (29 : ZMod 8923714801) ^ 7166 = 6017439830 := by
        calc
          (29 : ZMod 8923714801) ^ 7166 = (29 : ZMod 8923714801) ^ (3583 + 3583) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 3583 * (29 : ZMod 8923714801) ^ 3583 := by rw [pow_add]
          _ = 6017439830 := by rw [factor_7_11]; decide
      have factor_7_13 : (29 : ZMod 8923714801) ^ 14333 = 5609495041 := by
        calc
          (29 : ZMod 8923714801) ^ 14333 = (29 : ZMod 8923714801) ^ (7166 + 7166 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 7166 * (29 : ZMod 8923714801) ^ 7166) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 5609495041 := by rw [factor_7_12]; decide
      have factor_7_14 : (29 : ZMod 8923714801) ^ 28666 = 6367528578 := by
        calc
          (29 : ZMod 8923714801) ^ 28666 = (29 : ZMod 8923714801) ^ (14333 + 14333) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 14333 * (29 : ZMod 8923714801) ^ 14333 := by rw [pow_add]
          _ = 6367528578 := by rw [factor_7_13]; decide
      have factor_7_15 : (29 : ZMod 8923714801) ^ 57332 = 605917589 := by
        calc
          (29 : ZMod 8923714801) ^ 57332 = (29 : ZMod 8923714801) ^ (28666 + 28666) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 28666 * (29 : ZMod 8923714801) ^ 28666 := by rw [pow_add]
          _ = 605917589 := by rw [factor_7_14]; decide
      have factor_7_16 : (29 : ZMod 8923714801) ^ 114665 = 2747420395 := by
        calc
          (29 : ZMod 8923714801) ^ 114665 = (29 : ZMod 8923714801) ^ (57332 + 57332 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 57332 * (29 : ZMod 8923714801) ^ 57332) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2747420395 := by rw [factor_7_15]; decide
      have factor_7_17 : (29 : ZMod 8923714801) ^ 229330 = 521437011 := by
        calc
          (29 : ZMod 8923714801) ^ 229330 = (29 : ZMod 8923714801) ^ (114665 + 114665) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 114665 * (29 : ZMod 8923714801) ^ 114665 := by rw [pow_add]
          _ = 521437011 := by rw [factor_7_16]; decide
      have factor_7_18 : (29 : ZMod 8923714801) ^ 458661 = 665592466 := by
        calc
          (29 : ZMod 8923714801) ^ 458661 = (29 : ZMod 8923714801) ^ (229330 + 229330 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 229330 * (29 : ZMod 8923714801) ^ 229330) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 665592466 := by rw [factor_7_17]; decide
      have factor_7_19 : (29 : ZMod 8923714801) ^ 917322 = 7052575860 := by
        calc
          (29 : ZMod 8923714801) ^ 917322 = (29 : ZMod 8923714801) ^ (458661 + 458661) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 458661 * (29 : ZMod 8923714801) ^ 458661 := by rw [pow_add]
          _ = 7052575860 := by rw [factor_7_18]; decide
      have factor_7_20 : (29 : ZMod 8923714801) ^ 1834645 = 2292793274 := by
        calc
          (29 : ZMod 8923714801) ^ 1834645 = (29 : ZMod 8923714801) ^ (917322 + 917322 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 917322 * (29 : ZMod 8923714801) ^ 917322) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2292793274 := by rw [factor_7_19]; decide
      have factor_7_21 : (29 : ZMod 8923714801) ^ 3669290 = 4276254532 := by
        calc
          (29 : ZMod 8923714801) ^ 3669290 = (29 : ZMod 8923714801) ^ (1834645 + 1834645) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1834645 * (29 : ZMod 8923714801) ^ 1834645 := by rw [pow_add]
          _ = 4276254532 := by rw [factor_7_20]; decide
      have factor_7_22 : (29 : ZMod 8923714801) ^ 7338581 = 4338862798 := by
        calc
          (29 : ZMod 8923714801) ^ 7338581 = (29 : ZMod 8923714801) ^ (3669290 + 3669290 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 3669290 * (29 : ZMod 8923714801) ^ 3669290) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 4338862798 := by rw [factor_7_21]; decide
      have factor_7_23 : (29 : ZMod 8923714801) ^ 14677162 = 1284538285 := by
        calc
          (29 : ZMod 8923714801) ^ 14677162 = (29 : ZMod 8923714801) ^ (7338581 + 7338581) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 7338581 * (29 : ZMod 8923714801) ^ 7338581 := by rw [pow_add]
          _ = 1284538285 := by rw [factor_7_22]; decide
      have factor_7_24 : (29 : ZMod 8923714801) ^ 29354325 = 3103866584 := by
        calc
          (29 : ZMod 8923714801) ^ 29354325 = (29 : ZMod 8923714801) ^ (14677162 + 14677162 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 14677162 * (29 : ZMod 8923714801) ^ 14677162) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 3103866584 := by rw [factor_7_23]; decide
      have factor_7_25 : (29 : ZMod 8923714801) ^ 58708650 = 1255103589 := by
        calc
          (29 : ZMod 8923714801) ^ 58708650 = (29 : ZMod 8923714801) ^ (29354325 + 29354325) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 29354325 * (29 : ZMod 8923714801) ^ 29354325 := by rw [pow_add]
          _ = 1255103589 := by rw [factor_7_24]; decide
      have factor_7_26 : (29 : ZMod 8923714801) ^ 117417300 = 1381496578 := by
        calc
          (29 : ZMod 8923714801) ^ 117417300 = (29 : ZMod 8923714801) ^ (58708650 + 58708650) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 58708650 * (29 : ZMod 8923714801) ^ 58708650 := by rw [pow_add]
          _ = 1381496578 := by rw [factor_7_25]; decide
      have factor_7_27 : (29 : ZMod 8923714801) ^ 234834600 = 640234477 := by
        calc
          (29 : ZMod 8923714801) ^ 234834600 = (29 : ZMod 8923714801) ^ (117417300 + 117417300) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 117417300 * (29 : ZMod 8923714801) ^ 117417300 := by rw [pow_add]
          _ = 640234477 := by rw [factor_7_26]; decide
      have factor_7_28 : (29 : ZMod 8923714801) ^ 469669200 = 1071000923 := by
        calc
          (29 : ZMod 8923714801) ^ 469669200 = (29 : ZMod 8923714801) ^ (234834600 + 234834600) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 234834600 * (29 : ZMod 8923714801) ^ 234834600 := by rw [pow_add]
          _ = 1071000923 := by rw [factor_7_27]; decide
      change (29 : ZMod 8923714801) ^ 469669200 ≠ 1
      rw [factor_7_28]
      decide
    ·
      have factor_8_0 : (29 : ZMod 8923714801) ^ 1 = 29 := by norm_num
      have factor_8_1 : (29 : ZMod 8923714801) ^ 2 = 841 := by
        calc
          (29 : ZMod 8923714801) ^ 2 = (29 : ZMod 8923714801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1 * (29 : ZMod 8923714801) ^ 1 := by rw [pow_add]
          _ = 841 := by rw [factor_8_0]; decide
      have factor_8_2 : (29 : ZMod 8923714801) ^ 5 = 20511149 := by
        calc
          (29 : ZMod 8923714801) ^ 5 = (29 : ZMod 8923714801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 2 * (29 : ZMod 8923714801) ^ 2) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 20511149 := by rw [factor_8_1]; decide
      have factor_8_3 : (29 : ZMod 8923714801) ^ 11 = 6889778629 := by
        calc
          (29 : ZMod 8923714801) ^ 11 = (29 : ZMod 8923714801) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 5 * (29 : ZMod 8923714801) ^ 5) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 6889778629 := by rw [factor_8_2]; decide
      have factor_8_4 : (29 : ZMod 8923714801) ^ 23 = 5404798652 := by
        calc
          (29 : ZMod 8923714801) ^ 23 = (29 : ZMod 8923714801) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 11 * (29 : ZMod 8923714801) ^ 11) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 5404798652 := by rw [factor_8_3]; decide
      have factor_8_5 : (29 : ZMod 8923714801) ^ 46 = 6414729877 := by
        calc
          (29 : ZMod 8923714801) ^ 46 = (29 : ZMod 8923714801) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 23 * (29 : ZMod 8923714801) ^ 23 := by rw [pow_add]
          _ = 6414729877 := by rw [factor_8_4]; decide
      have factor_8_6 : (29 : ZMod 8923714801) ^ 92 = 1650788267 := by
        calc
          (29 : ZMod 8923714801) ^ 92 = (29 : ZMod 8923714801) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 46 * (29 : ZMod 8923714801) ^ 46 := by rw [pow_add]
          _ = 1650788267 := by rw [factor_8_5]; decide
      have factor_8_7 : (29 : ZMod 8923714801) ^ 185 = 7852062878 := by
        calc
          (29 : ZMod 8923714801) ^ 185 = (29 : ZMod 8923714801) ^ (92 + 92 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 92 * (29 : ZMod 8923714801) ^ 92) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 7852062878 := by rw [factor_8_6]; decide
      have factor_8_8 : (29 : ZMod 8923714801) ^ 370 = 1882596088 := by
        calc
          (29 : ZMod 8923714801) ^ 370 = (29 : ZMod 8923714801) ^ (185 + 185) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 185 * (29 : ZMod 8923714801) ^ 185 := by rw [pow_add]
          _ = 1882596088 := by rw [factor_8_7]; decide
      have factor_8_9 : (29 : ZMod 8923714801) ^ 740 = 829416491 := by
        calc
          (29 : ZMod 8923714801) ^ 740 = (29 : ZMod 8923714801) ^ (370 + 370) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 370 * (29 : ZMod 8923714801) ^ 370 := by rw [pow_add]
          _ = 829416491 := by rw [factor_8_8]; decide
      have factor_8_10 : (29 : ZMod 8923714801) ^ 1480 = 7198659597 := by
        calc
          (29 : ZMod 8923714801) ^ 1480 = (29 : ZMod 8923714801) ^ (740 + 740) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 740 * (29 : ZMod 8923714801) ^ 740 := by rw [pow_add]
          _ = 7198659597 := by rw [factor_8_9]; decide
      have factor_8_11 : (29 : ZMod 8923714801) ^ 2960 = 730038095 := by
        calc
          (29 : ZMod 8923714801) ^ 2960 = (29 : ZMod 8923714801) ^ (1480 + 1480) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 1480 * (29 : ZMod 8923714801) ^ 1480 := by rw [pow_add]
          _ = 730038095 := by rw [factor_8_10]; decide
      have factor_8_12 : (29 : ZMod 8923714801) ^ 5920 = 5377983510 := by
        calc
          (29 : ZMod 8923714801) ^ 5920 = (29 : ZMod 8923714801) ^ (2960 + 2960) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 2960 * (29 : ZMod 8923714801) ^ 2960 := by rw [pow_add]
          _ = 5377983510 := by rw [factor_8_11]; decide
      have factor_8_13 : (29 : ZMod 8923714801) ^ 11840 = 5947382383 := by
        calc
          (29 : ZMod 8923714801) ^ 11840 = (29 : ZMod 8923714801) ^ (5920 + 5920) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 5920 * (29 : ZMod 8923714801) ^ 5920 := by rw [pow_add]
          _ = 5947382383 := by rw [factor_8_12]; decide
      have factor_8_14 : (29 : ZMod 8923714801) ^ 23680 = 5932867032 := by
        calc
          (29 : ZMod 8923714801) ^ 23680 = (29 : ZMod 8923714801) ^ (11840 + 11840) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 11840 * (29 : ZMod 8923714801) ^ 11840 := by rw [pow_add]
          _ = 5932867032 := by rw [factor_8_13]; decide
      have factor_8_15 : (29 : ZMod 8923714801) ^ 47361 = 5806275431 := by
        calc
          (29 : ZMod 8923714801) ^ 47361 = (29 : ZMod 8923714801) ^ (23680 + 23680 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 23680 * (29 : ZMod 8923714801) ^ 23680) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 5806275431 := by rw [factor_8_14]; decide
      have factor_8_16 : (29 : ZMod 8923714801) ^ 94723 = 322072493 := by
        calc
          (29 : ZMod 8923714801) ^ 94723 = (29 : ZMod 8923714801) ^ (47361 + 47361 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 47361 * (29 : ZMod 8923714801) ^ 47361) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 322072493 := by rw [factor_8_15]; decide
      have factor_8_17 : (29 : ZMod 8923714801) ^ 189447 = 7532954975 := by
        calc
          (29 : ZMod 8923714801) ^ 189447 = (29 : ZMod 8923714801) ^ (94723 + 94723 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 94723 * (29 : ZMod 8923714801) ^ 94723) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 7532954975 := by rw [factor_8_16]; decide
      have factor_8_18 : (29 : ZMod 8923714801) ^ 378894 = 3893504133 := by
        calc
          (29 : ZMod 8923714801) ^ 378894 = (29 : ZMod 8923714801) ^ (189447 + 189447) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 189447 * (29 : ZMod 8923714801) ^ 189447 := by rw [pow_add]
          _ = 3893504133 := by rw [factor_8_17]; decide
      have factor_8_19 : (29 : ZMod 8923714801) ^ 757788 = 5121836918 := by
        calc
          (29 : ZMod 8923714801) ^ 757788 = (29 : ZMod 8923714801) ^ (378894 + 378894) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 378894 * (29 : ZMod 8923714801) ^ 378894 := by rw [pow_add]
          _ = 5121836918 := by rw [factor_8_18]; decide
      have factor_8_20 : (29 : ZMod 8923714801) ^ 1515576 = 7853422585 := by
        calc
          (29 : ZMod 8923714801) ^ 1515576 = (29 : ZMod 8923714801) ^ (757788 + 757788) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 757788 * (29 : ZMod 8923714801) ^ 757788 := by rw [pow_add]
          _ = 7853422585 := by rw [factor_8_19]; decide
      have factor_8_21 : (29 : ZMod 8923714801) ^ 3031153 = 2541771106 := by
        calc
          (29 : ZMod 8923714801) ^ 3031153 = (29 : ZMod 8923714801) ^ (1515576 + 1515576 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 1515576 * (29 : ZMod 8923714801) ^ 1515576) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 2541771106 := by rw [factor_8_20]; decide
      have factor_8_22 : (29 : ZMod 8923714801) ^ 6062306 = 6233945793 := by
        calc
          (29 : ZMod 8923714801) ^ 6062306 = (29 : ZMod 8923714801) ^ (3031153 + 3031153) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 3031153 * (29 : ZMod 8923714801) ^ 3031153 := by rw [pow_add]
          _ = 6233945793 := by rw [factor_8_21]; decide
      have factor_8_23 : (29 : ZMod 8923714801) ^ 12124612 = 8357407447 := by
        calc
          (29 : ZMod 8923714801) ^ 12124612 = (29 : ZMod 8923714801) ^ (6062306 + 6062306) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 6062306 * (29 : ZMod 8923714801) ^ 6062306 := by rw [pow_add]
          _ = 8357407447 := by rw [factor_8_22]; decide
      have factor_8_24 : (29 : ZMod 8923714801) ^ 24249225 = 3312486206 := by
        calc
          (29 : ZMod 8923714801) ^ 24249225 = (29 : ZMod 8923714801) ^ (12124612 + 12124612 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = ((29 : ZMod 8923714801) ^ 12124612 * (29 : ZMod 8923714801) ^ 12124612) * (29 : ZMod 8923714801) := by rw [pow_succ, pow_add]
          _ = 3312486206 := by rw [factor_8_23]; decide
      have factor_8_25 : (29 : ZMod 8923714801) ^ 48498450 = 1660687142 := by
        calc
          (29 : ZMod 8923714801) ^ 48498450 = (29 : ZMod 8923714801) ^ (24249225 + 24249225) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 24249225 * (29 : ZMod 8923714801) ^ 24249225 := by rw [pow_add]
          _ = 1660687142 := by rw [factor_8_24]; decide
      have factor_8_26 : (29 : ZMod 8923714801) ^ 96996900 = 5341775299 := by
        calc
          (29 : ZMod 8923714801) ^ 96996900 = (29 : ZMod 8923714801) ^ (48498450 + 48498450) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 48498450 * (29 : ZMod 8923714801) ^ 48498450 := by rw [pow_add]
          _ = 5341775299 := by rw [factor_8_25]; decide
      have factor_8_27 : (29 : ZMod 8923714801) ^ 193993800 = 1457860991 := by
        calc
          (29 : ZMod 8923714801) ^ 193993800 = (29 : ZMod 8923714801) ^ (96996900 + 96996900) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 96996900 * (29 : ZMod 8923714801) ^ 96996900 := by rw [pow_add]
          _ = 1457860991 := by rw [factor_8_26]; decide
      have factor_8_28 : (29 : ZMod 8923714801) ^ 387987600 = 4641761560 := by
        calc
          (29 : ZMod 8923714801) ^ 387987600 = (29 : ZMod 8923714801) ^ (193993800 + 193993800) :=
            congrArg (fun n : ℕ => (29 : ZMod 8923714801) ^ n) (by norm_num)
          _ = (29 : ZMod 8923714801) ^ 193993800 * (29 : ZMod 8923714801) ^ 193993800 := by rw [pow_add]
          _ = 4641761560 := by rw [factor_8_27]; decide
      change (29 : ZMod 8923714801) ^ 387987600 ≠ 1
      rw [factor_8_28]
      decide

#print axioms prime_lucas_8923714801

end TotientTailPeriodKiller
end Erdos249257
