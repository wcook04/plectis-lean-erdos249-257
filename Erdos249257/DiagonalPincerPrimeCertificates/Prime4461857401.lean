import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_4461857401 : Nat.Prime 4461857401 := by
  apply lucas_primality 4461857401 (43 : ZMod 4461857401)
  ·
      have fermat_0 : (43 : ZMod 4461857401) ^ 1 = 43 := by norm_num
      have fermat_1 : (43 : ZMod 4461857401) ^ 2 = 1849 := by
        calc
          (43 : ZMod 4461857401) ^ 2 = (43 : ZMod 4461857401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 1 * (43 : ZMod 4461857401) ^ 1 := by rw [pow_add]
          _ = 1849 := by rw [fermat_0]; decide
      have fermat_2 : (43 : ZMod 4461857401) ^ 4 = 3418801 := by
        calc
          (43 : ZMod 4461857401) ^ 4 = (43 : ZMod 4461857401) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 2 * (43 : ZMod 4461857401) ^ 2 := by rw [pow_add]
          _ = 3418801 := by rw [fermat_1]; decide
      have fermat_3 : (43 : ZMod 4461857401) ^ 8 = 2595744382 := by
        calc
          (43 : ZMod 4461857401) ^ 8 = (43 : ZMod 4461857401) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 4 * (43 : ZMod 4461857401) ^ 4 := by rw [pow_add]
          _ = 2595744382 := by rw [fermat_2]; decide
      have fermat_4 : (43 : ZMod 4461857401) ^ 16 = 2561975800 := by
        calc
          (43 : ZMod 4461857401) ^ 16 = (43 : ZMod 4461857401) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 8 * (43 : ZMod 4461857401) ^ 8 := by rw [pow_add]
          _ = 2561975800 := by rw [fermat_3]; decide
      have fermat_5 : (43 : ZMod 4461857401) ^ 33 = 2501259270 := by
        calc
          (43 : ZMod 4461857401) ^ 33 = (43 : ZMod 4461857401) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 16 * (43 : ZMod 4461857401) ^ 16) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2501259270 := by rw [fermat_4]; decide
      have fermat_6 : (43 : ZMod 4461857401) ^ 66 = 3935018262 := by
        calc
          (43 : ZMod 4461857401) ^ 66 = (43 : ZMod 4461857401) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 33 * (43 : ZMod 4461857401) ^ 33 := by rw [pow_add]
          _ = 3935018262 := by rw [fermat_5]; decide
      have fermat_7 : (43 : ZMod 4461857401) ^ 132 = 1141070161 := by
        calc
          (43 : ZMod 4461857401) ^ 132 = (43 : ZMod 4461857401) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 66 * (43 : ZMod 4461857401) ^ 66 := by rw [pow_add]
          _ = 1141070161 := by rw [fermat_6]; decide
      have fermat_8 : (43 : ZMod 4461857401) ^ 265 = 3577996777 := by
        calc
          (43 : ZMod 4461857401) ^ 265 = (43 : ZMod 4461857401) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 132 * (43 : ZMod 4461857401) ^ 132) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3577996777 := by rw [fermat_7]; decide
      have fermat_9 : (43 : ZMod 4461857401) ^ 531 = 2511086895 := by
        calc
          (43 : ZMod 4461857401) ^ 531 = (43 : ZMod 4461857401) ^ (265 + 265 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 265 * (43 : ZMod 4461857401) ^ 265) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2511086895 := by rw [fermat_8]; decide
      have fermat_10 : (43 : ZMod 4461857401) ^ 1063 = 569858276 := by
        calc
          (43 : ZMod 4461857401) ^ 1063 = (43 : ZMod 4461857401) ^ (531 + 531 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 531 * (43 : ZMod 4461857401) ^ 531) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 569858276 := by rw [fermat_9]; decide
      have fermat_11 : (43 : ZMod 4461857401) ^ 2127 = 730381260 := by
        calc
          (43 : ZMod 4461857401) ^ 2127 = (43 : ZMod 4461857401) ^ (1063 + 1063 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 1063 * (43 : ZMod 4461857401) ^ 1063) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 730381260 := by rw [fermat_10]; decide
      have fermat_12 : (43 : ZMod 4461857401) ^ 4255 = 3751880813 := by
        calc
          (43 : ZMod 4461857401) ^ 4255 = (43 : ZMod 4461857401) ^ (2127 + 2127 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 2127 * (43 : ZMod 4461857401) ^ 2127) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3751880813 := by rw [fermat_11]; decide
      have fermat_13 : (43 : ZMod 4461857401) ^ 8510 = 3073817141 := by
        calc
          (43 : ZMod 4461857401) ^ 8510 = (43 : ZMod 4461857401) ^ (4255 + 4255) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 4255 * (43 : ZMod 4461857401) ^ 4255 := by rw [pow_add]
          _ = 3073817141 := by rw [fermat_12]; decide
      have fermat_14 : (43 : ZMod 4461857401) ^ 17020 = 1635578632 := by
        calc
          (43 : ZMod 4461857401) ^ 17020 = (43 : ZMod 4461857401) ^ (8510 + 8510) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 8510 * (43 : ZMod 4461857401) ^ 8510 := by rw [pow_add]
          _ = 1635578632 := by rw [fermat_13]; decide
      have fermat_15 : (43 : ZMod 4461857401) ^ 34041 = 2257829404 := by
        calc
          (43 : ZMod 4461857401) ^ 34041 = (43 : ZMod 4461857401) ^ (17020 + 17020 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 17020 * (43 : ZMod 4461857401) ^ 17020) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2257829404 := by rw [fermat_14]; decide
      have fermat_16 : (43 : ZMod 4461857401) ^ 68082 = 390749377 := by
        calc
          (43 : ZMod 4461857401) ^ 68082 = (43 : ZMod 4461857401) ^ (34041 + 34041) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 34041 * (43 : ZMod 4461857401) ^ 34041 := by rw [pow_add]
          _ = 390749377 := by rw [fermat_15]; decide
      have fermat_17 : (43 : ZMod 4461857401) ^ 136165 = 1053087908 := by
        calc
          (43 : ZMod 4461857401) ^ 136165 = (43 : ZMod 4461857401) ^ (68082 + 68082 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 68082 * (43 : ZMod 4461857401) ^ 68082) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1053087908 := by rw [fermat_16]; decide
      have fermat_18 : (43 : ZMod 4461857401) ^ 272330 = 2532724980 := by
        calc
          (43 : ZMod 4461857401) ^ 272330 = (43 : ZMod 4461857401) ^ (136165 + 136165) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 136165 * (43 : ZMod 4461857401) ^ 136165 := by rw [pow_add]
          _ = 2532724980 := by rw [fermat_17]; decide
      have fermat_19 : (43 : ZMod 4461857401) ^ 544660 = 461044124 := by
        calc
          (43 : ZMod 4461857401) ^ 544660 = (43 : ZMod 4461857401) ^ (272330 + 272330) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 272330 * (43 : ZMod 4461857401) ^ 272330 := by rw [pow_add]
          _ = 461044124 := by rw [fermat_18]; decide
      have fermat_20 : (43 : ZMod 4461857401) ^ 1089320 = 2392785646 := by
        calc
          (43 : ZMod 4461857401) ^ 1089320 = (43 : ZMod 4461857401) ^ (544660 + 544660) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 544660 * (43 : ZMod 4461857401) ^ 544660 := by rw [pow_add]
          _ = 2392785646 := by rw [fermat_19]; decide
      have fermat_21 : (43 : ZMod 4461857401) ^ 2178641 = 1486369375 := by
        calc
          (43 : ZMod 4461857401) ^ 2178641 = (43 : ZMod 4461857401) ^ (1089320 + 1089320 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 1089320 * (43 : ZMod 4461857401) ^ 1089320) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1486369375 := by rw [fermat_20]; decide
      have fermat_22 : (43 : ZMod 4461857401) ^ 4357282 = 1997724054 := by
        calc
          (43 : ZMod 4461857401) ^ 4357282 = (43 : ZMod 4461857401) ^ (2178641 + 2178641) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 2178641 * (43 : ZMod 4461857401) ^ 2178641 := by rw [pow_add]
          _ = 1997724054 := by rw [fermat_21]; decide
      have fermat_23 : (43 : ZMod 4461857401) ^ 8714565 = 2429051829 := by
        calc
          (43 : ZMod 4461857401) ^ 8714565 = (43 : ZMod 4461857401) ^ (4357282 + 4357282 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 4357282 * (43 : ZMod 4461857401) ^ 4357282) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2429051829 := by rw [fermat_22]; decide
      have fermat_24 : (43 : ZMod 4461857401) ^ 17429130 = 1860461356 := by
        calc
          (43 : ZMod 4461857401) ^ 17429130 = (43 : ZMod 4461857401) ^ (8714565 + 8714565) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 8714565 * (43 : ZMod 4461857401) ^ 8714565 := by rw [pow_add]
          _ = 1860461356 := by rw [fermat_23]; decide
      have fermat_25 : (43 : ZMod 4461857401) ^ 34858260 = 1234839683 := by
        calc
          (43 : ZMod 4461857401) ^ 34858260 = (43 : ZMod 4461857401) ^ (17429130 + 17429130) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 17429130 * (43 : ZMod 4461857401) ^ 17429130 := by rw [pow_add]
          _ = 1234839683 := by rw [fermat_24]; decide
      have fermat_26 : (43 : ZMod 4461857401) ^ 69716521 = 1975241778 := by
        calc
          (43 : ZMod 4461857401) ^ 69716521 = (43 : ZMod 4461857401) ^ (34858260 + 34858260 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 34858260 * (43 : ZMod 4461857401) ^ 34858260) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1975241778 := by rw [fermat_25]; decide
      have fermat_27 : (43 : ZMod 4461857401) ^ 139433043 = 80056184 := by
        calc
          (43 : ZMod 4461857401) ^ 139433043 = (43 : ZMod 4461857401) ^ (69716521 + 69716521 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 69716521 * (43 : ZMod 4461857401) ^ 69716521) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 80056184 := by rw [fermat_26]; decide
      have fermat_28 : (43 : ZMod 4461857401) ^ 278866087 = 1278688595 := by
        calc
          (43 : ZMod 4461857401) ^ 278866087 = (43 : ZMod 4461857401) ^ (139433043 + 139433043 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 139433043 * (43 : ZMod 4461857401) ^ 139433043) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1278688595 := by rw [fermat_27]; decide
      have fermat_29 : (43 : ZMod 4461857401) ^ 557732175 = 1142884759 := by
        calc
          (43 : ZMod 4461857401) ^ 557732175 = (43 : ZMod 4461857401) ^ (278866087 + 278866087 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 278866087 * (43 : ZMod 4461857401) ^ 278866087) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1142884759 := by rw [fermat_28]; decide
      have fermat_30 : (43 : ZMod 4461857401) ^ 1115464350 = 2022793677 := by
        calc
          (43 : ZMod 4461857401) ^ 1115464350 = (43 : ZMod 4461857401) ^ (557732175 + 557732175) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 557732175 * (43 : ZMod 4461857401) ^ 557732175 := by rw [pow_add]
          _ = 2022793677 := by rw [fermat_29]; decide
      have fermat_31 : (43 : ZMod 4461857401) ^ 2230928700 = 4461857400 := by
        calc
          (43 : ZMod 4461857401) ^ 2230928700 = (43 : ZMod 4461857401) ^ (1115464350 + 1115464350) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 1115464350 * (43 : ZMod 4461857401) ^ 1115464350 := by rw [pow_add]
          _ = 4461857400 := by rw [fermat_30]; decide
      have fermat_32 : (43 : ZMod 4461857401) ^ 4461857400 = 1 := by
        calc
          (43 : ZMod 4461857401) ^ 4461857400 = (43 : ZMod 4461857401) ^ (2230928700 + 2230928700) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 2230928700 * (43 : ZMod 4461857401) ^ 2230928700 := by rw [pow_add]
          _ = 1 := by rw [fermat_31]; decide
      simpa using fermat_32
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 4461857401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (43 : ZMod 4461857401) ^ 1 = 43 := by norm_num
      have factor_0_1 : (43 : ZMod 4461857401) ^ 2 = 1849 := by
        calc
          (43 : ZMod 4461857401) ^ 2 = (43 : ZMod 4461857401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 1 * (43 : ZMod 4461857401) ^ 1 := by rw [pow_add]
          _ = 1849 := by rw [factor_0_0]; decide
      have factor_0_2 : (43 : ZMod 4461857401) ^ 4 = 3418801 := by
        calc
          (43 : ZMod 4461857401) ^ 4 = (43 : ZMod 4461857401) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 2 * (43 : ZMod 4461857401) ^ 2 := by rw [pow_add]
          _ = 3418801 := by rw [factor_0_1]; decide
      have factor_0_3 : (43 : ZMod 4461857401) ^ 8 = 2595744382 := by
        calc
          (43 : ZMod 4461857401) ^ 8 = (43 : ZMod 4461857401) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 4 * (43 : ZMod 4461857401) ^ 4 := by rw [pow_add]
          _ = 2595744382 := by rw [factor_0_2]; decide
      have factor_0_4 : (43 : ZMod 4461857401) ^ 16 = 2561975800 := by
        calc
          (43 : ZMod 4461857401) ^ 16 = (43 : ZMod 4461857401) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 8 * (43 : ZMod 4461857401) ^ 8 := by rw [pow_add]
          _ = 2561975800 := by rw [factor_0_3]; decide
      have factor_0_5 : (43 : ZMod 4461857401) ^ 33 = 2501259270 := by
        calc
          (43 : ZMod 4461857401) ^ 33 = (43 : ZMod 4461857401) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 16 * (43 : ZMod 4461857401) ^ 16) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2501259270 := by rw [factor_0_4]; decide
      have factor_0_6 : (43 : ZMod 4461857401) ^ 66 = 3935018262 := by
        calc
          (43 : ZMod 4461857401) ^ 66 = (43 : ZMod 4461857401) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 33 * (43 : ZMod 4461857401) ^ 33 := by rw [pow_add]
          _ = 3935018262 := by rw [factor_0_5]; decide
      have factor_0_7 : (43 : ZMod 4461857401) ^ 132 = 1141070161 := by
        calc
          (43 : ZMod 4461857401) ^ 132 = (43 : ZMod 4461857401) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 66 * (43 : ZMod 4461857401) ^ 66 := by rw [pow_add]
          _ = 1141070161 := by rw [factor_0_6]; decide
      have factor_0_8 : (43 : ZMod 4461857401) ^ 265 = 3577996777 := by
        calc
          (43 : ZMod 4461857401) ^ 265 = (43 : ZMod 4461857401) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 132 * (43 : ZMod 4461857401) ^ 132) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3577996777 := by rw [factor_0_7]; decide
      have factor_0_9 : (43 : ZMod 4461857401) ^ 531 = 2511086895 := by
        calc
          (43 : ZMod 4461857401) ^ 531 = (43 : ZMod 4461857401) ^ (265 + 265 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 265 * (43 : ZMod 4461857401) ^ 265) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2511086895 := by rw [factor_0_8]; decide
      have factor_0_10 : (43 : ZMod 4461857401) ^ 1063 = 569858276 := by
        calc
          (43 : ZMod 4461857401) ^ 1063 = (43 : ZMod 4461857401) ^ (531 + 531 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 531 * (43 : ZMod 4461857401) ^ 531) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 569858276 := by rw [factor_0_9]; decide
      have factor_0_11 : (43 : ZMod 4461857401) ^ 2127 = 730381260 := by
        calc
          (43 : ZMod 4461857401) ^ 2127 = (43 : ZMod 4461857401) ^ (1063 + 1063 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 1063 * (43 : ZMod 4461857401) ^ 1063) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 730381260 := by rw [factor_0_10]; decide
      have factor_0_12 : (43 : ZMod 4461857401) ^ 4255 = 3751880813 := by
        calc
          (43 : ZMod 4461857401) ^ 4255 = (43 : ZMod 4461857401) ^ (2127 + 2127 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 2127 * (43 : ZMod 4461857401) ^ 2127) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3751880813 := by rw [factor_0_11]; decide
      have factor_0_13 : (43 : ZMod 4461857401) ^ 8510 = 3073817141 := by
        calc
          (43 : ZMod 4461857401) ^ 8510 = (43 : ZMod 4461857401) ^ (4255 + 4255) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 4255 * (43 : ZMod 4461857401) ^ 4255 := by rw [pow_add]
          _ = 3073817141 := by rw [factor_0_12]; decide
      have factor_0_14 : (43 : ZMod 4461857401) ^ 17020 = 1635578632 := by
        calc
          (43 : ZMod 4461857401) ^ 17020 = (43 : ZMod 4461857401) ^ (8510 + 8510) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 8510 * (43 : ZMod 4461857401) ^ 8510 := by rw [pow_add]
          _ = 1635578632 := by rw [factor_0_13]; decide
      have factor_0_15 : (43 : ZMod 4461857401) ^ 34041 = 2257829404 := by
        calc
          (43 : ZMod 4461857401) ^ 34041 = (43 : ZMod 4461857401) ^ (17020 + 17020 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 17020 * (43 : ZMod 4461857401) ^ 17020) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2257829404 := by rw [factor_0_14]; decide
      have factor_0_16 : (43 : ZMod 4461857401) ^ 68082 = 390749377 := by
        calc
          (43 : ZMod 4461857401) ^ 68082 = (43 : ZMod 4461857401) ^ (34041 + 34041) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 34041 * (43 : ZMod 4461857401) ^ 34041 := by rw [pow_add]
          _ = 390749377 := by rw [factor_0_15]; decide
      have factor_0_17 : (43 : ZMod 4461857401) ^ 136165 = 1053087908 := by
        calc
          (43 : ZMod 4461857401) ^ 136165 = (43 : ZMod 4461857401) ^ (68082 + 68082 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 68082 * (43 : ZMod 4461857401) ^ 68082) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1053087908 := by rw [factor_0_16]; decide
      have factor_0_18 : (43 : ZMod 4461857401) ^ 272330 = 2532724980 := by
        calc
          (43 : ZMod 4461857401) ^ 272330 = (43 : ZMod 4461857401) ^ (136165 + 136165) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 136165 * (43 : ZMod 4461857401) ^ 136165 := by rw [pow_add]
          _ = 2532724980 := by rw [factor_0_17]; decide
      have factor_0_19 : (43 : ZMod 4461857401) ^ 544660 = 461044124 := by
        calc
          (43 : ZMod 4461857401) ^ 544660 = (43 : ZMod 4461857401) ^ (272330 + 272330) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 272330 * (43 : ZMod 4461857401) ^ 272330 := by rw [pow_add]
          _ = 461044124 := by rw [factor_0_18]; decide
      have factor_0_20 : (43 : ZMod 4461857401) ^ 1089320 = 2392785646 := by
        calc
          (43 : ZMod 4461857401) ^ 1089320 = (43 : ZMod 4461857401) ^ (544660 + 544660) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 544660 * (43 : ZMod 4461857401) ^ 544660 := by rw [pow_add]
          _ = 2392785646 := by rw [factor_0_19]; decide
      have factor_0_21 : (43 : ZMod 4461857401) ^ 2178641 = 1486369375 := by
        calc
          (43 : ZMod 4461857401) ^ 2178641 = (43 : ZMod 4461857401) ^ (1089320 + 1089320 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 1089320 * (43 : ZMod 4461857401) ^ 1089320) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1486369375 := by rw [factor_0_20]; decide
      have factor_0_22 : (43 : ZMod 4461857401) ^ 4357282 = 1997724054 := by
        calc
          (43 : ZMod 4461857401) ^ 4357282 = (43 : ZMod 4461857401) ^ (2178641 + 2178641) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 2178641 * (43 : ZMod 4461857401) ^ 2178641 := by rw [pow_add]
          _ = 1997724054 := by rw [factor_0_21]; decide
      have factor_0_23 : (43 : ZMod 4461857401) ^ 8714565 = 2429051829 := by
        calc
          (43 : ZMod 4461857401) ^ 8714565 = (43 : ZMod 4461857401) ^ (4357282 + 4357282 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 4357282 * (43 : ZMod 4461857401) ^ 4357282) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2429051829 := by rw [factor_0_22]; decide
      have factor_0_24 : (43 : ZMod 4461857401) ^ 17429130 = 1860461356 := by
        calc
          (43 : ZMod 4461857401) ^ 17429130 = (43 : ZMod 4461857401) ^ (8714565 + 8714565) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 8714565 * (43 : ZMod 4461857401) ^ 8714565 := by rw [pow_add]
          _ = 1860461356 := by rw [factor_0_23]; decide
      have factor_0_25 : (43 : ZMod 4461857401) ^ 34858260 = 1234839683 := by
        calc
          (43 : ZMod 4461857401) ^ 34858260 = (43 : ZMod 4461857401) ^ (17429130 + 17429130) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 17429130 * (43 : ZMod 4461857401) ^ 17429130 := by rw [pow_add]
          _ = 1234839683 := by rw [factor_0_24]; decide
      have factor_0_26 : (43 : ZMod 4461857401) ^ 69716521 = 1975241778 := by
        calc
          (43 : ZMod 4461857401) ^ 69716521 = (43 : ZMod 4461857401) ^ (34858260 + 34858260 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 34858260 * (43 : ZMod 4461857401) ^ 34858260) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1975241778 := by rw [factor_0_25]; decide
      have factor_0_27 : (43 : ZMod 4461857401) ^ 139433043 = 80056184 := by
        calc
          (43 : ZMod 4461857401) ^ 139433043 = (43 : ZMod 4461857401) ^ (69716521 + 69716521 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 69716521 * (43 : ZMod 4461857401) ^ 69716521) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 80056184 := by rw [factor_0_26]; decide
      have factor_0_28 : (43 : ZMod 4461857401) ^ 278866087 = 1278688595 := by
        calc
          (43 : ZMod 4461857401) ^ 278866087 = (43 : ZMod 4461857401) ^ (139433043 + 139433043 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 139433043 * (43 : ZMod 4461857401) ^ 139433043) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1278688595 := by rw [factor_0_27]; decide
      have factor_0_29 : (43 : ZMod 4461857401) ^ 557732175 = 1142884759 := by
        calc
          (43 : ZMod 4461857401) ^ 557732175 = (43 : ZMod 4461857401) ^ (278866087 + 278866087 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 278866087 * (43 : ZMod 4461857401) ^ 278866087) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1142884759 := by rw [factor_0_28]; decide
      have factor_0_30 : (43 : ZMod 4461857401) ^ 1115464350 = 2022793677 := by
        calc
          (43 : ZMod 4461857401) ^ 1115464350 = (43 : ZMod 4461857401) ^ (557732175 + 557732175) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 557732175 * (43 : ZMod 4461857401) ^ 557732175 := by rw [pow_add]
          _ = 2022793677 := by rw [factor_0_29]; decide
      have factor_0_31 : (43 : ZMod 4461857401) ^ 2230928700 = 4461857400 := by
        calc
          (43 : ZMod 4461857401) ^ 2230928700 = (43 : ZMod 4461857401) ^ (1115464350 + 1115464350) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 1115464350 * (43 : ZMod 4461857401) ^ 1115464350 := by rw [pow_add]
          _ = 4461857400 := by rw [factor_0_30]; decide
      change (43 : ZMod 4461857401) ^ 2230928700 ≠ 1
      rw [factor_0_31]
      decide
    ·
      have factor_1_0 : (43 : ZMod 4461857401) ^ 1 = 43 := by norm_num
      have factor_1_1 : (43 : ZMod 4461857401) ^ 2 = 1849 := by
        calc
          (43 : ZMod 4461857401) ^ 2 = (43 : ZMod 4461857401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 1 * (43 : ZMod 4461857401) ^ 1 := by rw [pow_add]
          _ = 1849 := by rw [factor_1_0]; decide
      have factor_1_2 : (43 : ZMod 4461857401) ^ 5 = 147008443 := by
        calc
          (43 : ZMod 4461857401) ^ 5 = (43 : ZMod 4461857401) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 2 * (43 : ZMod 4461857401) ^ 2) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 147008443 := by rw [factor_1_1]; decide
      have factor_1_3 : (43 : ZMod 4461857401) ^ 11 = 1096353820 := by
        calc
          (43 : ZMod 4461857401) ^ 11 = (43 : ZMod 4461857401) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 5 * (43 : ZMod 4461857401) ^ 5) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1096353820 := by rw [factor_1_2]; decide
      have factor_1_4 : (43 : ZMod 4461857401) ^ 22 = 2366512126 := by
        calc
          (43 : ZMod 4461857401) ^ 22 = (43 : ZMod 4461857401) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 11 * (43 : ZMod 4461857401) ^ 11 := by rw [pow_add]
          _ = 2366512126 := by rw [factor_1_3]; decide
      have factor_1_5 : (43 : ZMod 4461857401) ^ 44 = 2739014898 := by
        calc
          (43 : ZMod 4461857401) ^ 44 = (43 : ZMod 4461857401) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 22 * (43 : ZMod 4461857401) ^ 22 := by rw [pow_add]
          _ = 2739014898 := by rw [factor_1_4]; decide
      have factor_1_6 : (43 : ZMod 4461857401) ^ 88 = 3035492231 := by
        calc
          (43 : ZMod 4461857401) ^ 88 = (43 : ZMod 4461857401) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 44 * (43 : ZMod 4461857401) ^ 44 := by rw [pow_add]
          _ = 3035492231 := by rw [factor_1_5]; decide
      have factor_1_7 : (43 : ZMod 4461857401) ^ 177 = 1887607045 := by
        calc
          (43 : ZMod 4461857401) ^ 177 = (43 : ZMod 4461857401) ^ (88 + 88 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 88 * (43 : ZMod 4461857401) ^ 88) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1887607045 := by rw [factor_1_6]; decide
      have factor_1_8 : (43 : ZMod 4461857401) ^ 354 = 995386135 := by
        calc
          (43 : ZMod 4461857401) ^ 354 = (43 : ZMod 4461857401) ^ (177 + 177) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 177 * (43 : ZMod 4461857401) ^ 177 := by rw [pow_add]
          _ = 995386135 := by rw [factor_1_7]; decide
      have factor_1_9 : (43 : ZMod 4461857401) ^ 709 = 2573397686 := by
        calc
          (43 : ZMod 4461857401) ^ 709 = (43 : ZMod 4461857401) ^ (354 + 354 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 354 * (43 : ZMod 4461857401) ^ 354) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2573397686 := by rw [factor_1_8]; decide
      have factor_1_10 : (43 : ZMod 4461857401) ^ 1418 = 1073070121 := by
        calc
          (43 : ZMod 4461857401) ^ 1418 = (43 : ZMod 4461857401) ^ (709 + 709) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 709 * (43 : ZMod 4461857401) ^ 709 := by rw [pow_add]
          _ = 1073070121 := by rw [factor_1_9]; decide
      have factor_1_11 : (43 : ZMod 4461857401) ^ 2836 = 3000710861 := by
        calc
          (43 : ZMod 4461857401) ^ 2836 = (43 : ZMod 4461857401) ^ (1418 + 1418) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 1418 * (43 : ZMod 4461857401) ^ 1418 := by rw [pow_add]
          _ = 3000710861 := by rw [factor_1_10]; decide
      have factor_1_12 : (43 : ZMod 4461857401) ^ 5673 = 1031703974 := by
        calc
          (43 : ZMod 4461857401) ^ 5673 = (43 : ZMod 4461857401) ^ (2836 + 2836 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 2836 * (43 : ZMod 4461857401) ^ 2836) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1031703974 := by rw [factor_1_11]; decide
      have factor_1_13 : (43 : ZMod 4461857401) ^ 11347 = 97455423 := by
        calc
          (43 : ZMod 4461857401) ^ 11347 = (43 : ZMod 4461857401) ^ (5673 + 5673 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 5673 * (43 : ZMod 4461857401) ^ 5673) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 97455423 := by rw [factor_1_12]; decide
      have factor_1_14 : (43 : ZMod 4461857401) ^ 22694 = 727908918 := by
        calc
          (43 : ZMod 4461857401) ^ 22694 = (43 : ZMod 4461857401) ^ (11347 + 11347) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 11347 * (43 : ZMod 4461857401) ^ 11347 := by rw [pow_add]
          _ = 727908918 := by rw [factor_1_13]; decide
      have factor_1_15 : (43 : ZMod 4461857401) ^ 45388 = 3811272419 := by
        calc
          (43 : ZMod 4461857401) ^ 45388 = (43 : ZMod 4461857401) ^ (22694 + 22694) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 22694 * (43 : ZMod 4461857401) ^ 22694 := by rw [pow_add]
          _ = 3811272419 := by rw [factor_1_14]; decide
      have factor_1_16 : (43 : ZMod 4461857401) ^ 90776 = 3869415502 := by
        calc
          (43 : ZMod 4461857401) ^ 90776 = (43 : ZMod 4461857401) ^ (45388 + 45388) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 45388 * (43 : ZMod 4461857401) ^ 45388 := by rw [pow_add]
          _ = 3869415502 := by rw [factor_1_15]; decide
      have factor_1_17 : (43 : ZMod 4461857401) ^ 181553 = 1223954459 := by
        calc
          (43 : ZMod 4461857401) ^ 181553 = (43 : ZMod 4461857401) ^ (90776 + 90776 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 90776 * (43 : ZMod 4461857401) ^ 90776) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1223954459 := by rw [factor_1_16]; decide
      have factor_1_18 : (43 : ZMod 4461857401) ^ 363106 = 229041601 := by
        calc
          (43 : ZMod 4461857401) ^ 363106 = (43 : ZMod 4461857401) ^ (181553 + 181553) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 181553 * (43 : ZMod 4461857401) ^ 181553 := by rw [pow_add]
          _ = 229041601 := by rw [factor_1_17]; decide
      have factor_1_19 : (43 : ZMod 4461857401) ^ 726213 = 2823737393 := by
        calc
          (43 : ZMod 4461857401) ^ 726213 = (43 : ZMod 4461857401) ^ (363106 + 363106 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 363106 * (43 : ZMod 4461857401) ^ 363106) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2823737393 := by rw [factor_1_18]; decide
      have factor_1_20 : (43 : ZMod 4461857401) ^ 1452427 = 2148564969 := by
        calc
          (43 : ZMod 4461857401) ^ 1452427 = (43 : ZMod 4461857401) ^ (726213 + 726213 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 726213 * (43 : ZMod 4461857401) ^ 726213) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2148564969 := by rw [factor_1_19]; decide
      have factor_1_21 : (43 : ZMod 4461857401) ^ 2904855 = 2668127946 := by
        calc
          (43 : ZMod 4461857401) ^ 2904855 = (43 : ZMod 4461857401) ^ (1452427 + 1452427 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 1452427 * (43 : ZMod 4461857401) ^ 1452427) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2668127946 := by rw [factor_1_20]; decide
      have factor_1_22 : (43 : ZMod 4461857401) ^ 5809710 = 1214197946 := by
        calc
          (43 : ZMod 4461857401) ^ 5809710 = (43 : ZMod 4461857401) ^ (2904855 + 2904855) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 2904855 * (43 : ZMod 4461857401) ^ 2904855 := by rw [pow_add]
          _ = 1214197946 := by rw [factor_1_21]; decide
      have factor_1_23 : (43 : ZMod 4461857401) ^ 11619420 = 827936018 := by
        calc
          (43 : ZMod 4461857401) ^ 11619420 = (43 : ZMod 4461857401) ^ (5809710 + 5809710) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 5809710 * (43 : ZMod 4461857401) ^ 5809710 := by rw [pow_add]
          _ = 827936018 := by rw [factor_1_22]; decide
      have factor_1_24 : (43 : ZMod 4461857401) ^ 23238840 = 1640613075 := by
        calc
          (43 : ZMod 4461857401) ^ 23238840 = (43 : ZMod 4461857401) ^ (11619420 + 11619420) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 11619420 * (43 : ZMod 4461857401) ^ 11619420 := by rw [pow_add]
          _ = 1640613075 := by rw [factor_1_23]; decide
      have factor_1_25 : (43 : ZMod 4461857401) ^ 46477681 = 926400099 := by
        calc
          (43 : ZMod 4461857401) ^ 46477681 = (43 : ZMod 4461857401) ^ (23238840 + 23238840 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 23238840 * (43 : ZMod 4461857401) ^ 23238840) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 926400099 := by rw [factor_1_24]; decide
      have factor_1_26 : (43 : ZMod 4461857401) ^ 92955362 = 3701510937 := by
        calc
          (43 : ZMod 4461857401) ^ 92955362 = (43 : ZMod 4461857401) ^ (46477681 + 46477681) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 46477681 * (43 : ZMod 4461857401) ^ 46477681 := by rw [pow_add]
          _ = 3701510937 := by rw [factor_1_25]; decide
      have factor_1_27 : (43 : ZMod 4461857401) ^ 185910725 = 2313160318 := by
        calc
          (43 : ZMod 4461857401) ^ 185910725 = (43 : ZMod 4461857401) ^ (92955362 + 92955362 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 92955362 * (43 : ZMod 4461857401) ^ 92955362) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2313160318 := by rw [factor_1_26]; decide
      have factor_1_28 : (43 : ZMod 4461857401) ^ 371821450 = 3672838436 := by
        calc
          (43 : ZMod 4461857401) ^ 371821450 = (43 : ZMod 4461857401) ^ (185910725 + 185910725) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 185910725 * (43 : ZMod 4461857401) ^ 185910725 := by rw [pow_add]
          _ = 3672838436 := by rw [factor_1_27]; decide
      have factor_1_29 : (43 : ZMod 4461857401) ^ 743642900 = 2059409123 := by
        calc
          (43 : ZMod 4461857401) ^ 743642900 = (43 : ZMod 4461857401) ^ (371821450 + 371821450) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 371821450 * (43 : ZMod 4461857401) ^ 371821450 := by rw [pow_add]
          _ = 2059409123 := by rw [factor_1_28]; decide
      have factor_1_30 : (43 : ZMod 4461857401) ^ 1487285800 = 2059409122 := by
        calc
          (43 : ZMod 4461857401) ^ 1487285800 = (43 : ZMod 4461857401) ^ (743642900 + 743642900) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 743642900 * (43 : ZMod 4461857401) ^ 743642900 := by rw [pow_add]
          _ = 2059409122 := by rw [factor_1_29]; decide
      change (43 : ZMod 4461857401) ^ 1487285800 ≠ 1
      rw [factor_1_30]
      decide
    ·
      have factor_2_0 : (43 : ZMod 4461857401) ^ 1 = 43 := by norm_num
      have factor_2_1 : (43 : ZMod 4461857401) ^ 3 = 79507 := by
        calc
          (43 : ZMod 4461857401) ^ 3 = (43 : ZMod 4461857401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 1 * (43 : ZMod 4461857401) ^ 1) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 79507 := by rw [factor_2_0]; decide
      have factor_2_2 : (43 : ZMod 4461857401) ^ 6 = 1859505648 := by
        calc
          (43 : ZMod 4461857401) ^ 6 = (43 : ZMod 4461857401) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 3 * (43 : ZMod 4461857401) ^ 3 := by rw [pow_add]
          _ = 1859505648 := by rw [factor_2_1]; decide
      have factor_2_3 : (43 : ZMod 4461857401) ^ 13 = 1474953126 := by
        calc
          (43 : ZMod 4461857401) ^ 13 = (43 : ZMod 4461857401) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 6 * (43 : ZMod 4461857401) ^ 6) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1474953126 := by rw [factor_2_2]; decide
      have factor_2_4 : (43 : ZMod 4461857401) ^ 26 = 1539936438 := by
        calc
          (43 : ZMod 4461857401) ^ 26 = (43 : ZMod 4461857401) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 13 * (43 : ZMod 4461857401) ^ 13 := by rw [pow_add]
          _ = 1539936438 := by rw [factor_2_3]; decide
      have factor_2_5 : (43 : ZMod 4461857401) ^ 53 = 4211402176 := by
        calc
          (43 : ZMod 4461857401) ^ 53 = (43 : ZMod 4461857401) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 26 * (43 : ZMod 4461857401) ^ 26) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 4211402176 := by rw [factor_2_4]; decide
      have factor_2_6 : (43 : ZMod 4461857401) ^ 106 = 3247224747 := by
        calc
          (43 : ZMod 4461857401) ^ 106 = (43 : ZMod 4461857401) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 53 * (43 : ZMod 4461857401) ^ 53 := by rw [pow_add]
          _ = 3247224747 := by rw [factor_2_5]; decide
      have factor_2_7 : (43 : ZMod 4461857401) ^ 212 = 1294315183 := by
        calc
          (43 : ZMod 4461857401) ^ 212 = (43 : ZMod 4461857401) ^ (106 + 106) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 106 * (43 : ZMod 4461857401) ^ 106 := by rw [pow_add]
          _ = 1294315183 := by rw [factor_2_6]; decide
      have factor_2_8 : (43 : ZMod 4461857401) ^ 425 = 673131516 := by
        calc
          (43 : ZMod 4461857401) ^ 425 = (43 : ZMod 4461857401) ^ (212 + 212 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 212 * (43 : ZMod 4461857401) ^ 212) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 673131516 := by rw [factor_2_7]; decide
      have factor_2_9 : (43 : ZMod 4461857401) ^ 851 = 2983490824 := by
        calc
          (43 : ZMod 4461857401) ^ 851 = (43 : ZMod 4461857401) ^ (425 + 425 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 425 * (43 : ZMod 4461857401) ^ 425) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2983490824 := by rw [factor_2_8]; decide
      have factor_2_10 : (43 : ZMod 4461857401) ^ 1702 = 106219715 := by
        calc
          (43 : ZMod 4461857401) ^ 1702 = (43 : ZMod 4461857401) ^ (851 + 851) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 851 * (43 : ZMod 4461857401) ^ 851 := by rw [pow_add]
          _ = 106219715 := by rw [factor_2_9]; decide
      have factor_2_11 : (43 : ZMod 4461857401) ^ 3404 = 434490941 := by
        calc
          (43 : ZMod 4461857401) ^ 3404 = (43 : ZMod 4461857401) ^ (1702 + 1702) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 1702 * (43 : ZMod 4461857401) ^ 1702 := by rw [pow_add]
          _ = 434490941 := by rw [factor_2_10]; decide
      have factor_2_12 : (43 : ZMod 4461857401) ^ 6808 = 4320686815 := by
        calc
          (43 : ZMod 4461857401) ^ 6808 = (43 : ZMod 4461857401) ^ (3404 + 3404) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 3404 * (43 : ZMod 4461857401) ^ 3404 := by rw [pow_add]
          _ = 4320686815 := by rw [factor_2_11]; decide
      have factor_2_13 : (43 : ZMod 4461857401) ^ 13616 = 2867859841 := by
        calc
          (43 : ZMod 4461857401) ^ 13616 = (43 : ZMod 4461857401) ^ (6808 + 6808) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 6808 * (43 : ZMod 4461857401) ^ 6808 := by rw [pow_add]
          _ = 2867859841 := by rw [factor_2_12]; decide
      have factor_2_14 : (43 : ZMod 4461857401) ^ 27233 = 1090131491 := by
        calc
          (43 : ZMod 4461857401) ^ 27233 = (43 : ZMod 4461857401) ^ (13616 + 13616 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 13616 * (43 : ZMod 4461857401) ^ 13616) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1090131491 := by rw [factor_2_13]; decide
      have factor_2_15 : (43 : ZMod 4461857401) ^ 54466 = 67070992 := by
        calc
          (43 : ZMod 4461857401) ^ 54466 = (43 : ZMod 4461857401) ^ (27233 + 27233) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 27233 * (43 : ZMod 4461857401) ^ 27233 := by rw [pow_add]
          _ = 67070992 := by rw [factor_2_14]; decide
      have factor_2_16 : (43 : ZMod 4461857401) ^ 108932 = 1946457448 := by
        calc
          (43 : ZMod 4461857401) ^ 108932 = (43 : ZMod 4461857401) ^ (54466 + 54466) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 54466 * (43 : ZMod 4461857401) ^ 54466 := by rw [pow_add]
          _ = 1946457448 := by rw [factor_2_15]; decide
      have factor_2_17 : (43 : ZMod 4461857401) ^ 217864 = 1221421789 := by
        calc
          (43 : ZMod 4461857401) ^ 217864 = (43 : ZMod 4461857401) ^ (108932 + 108932) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 108932 * (43 : ZMod 4461857401) ^ 108932 := by rw [pow_add]
          _ = 1221421789 := by rw [factor_2_16]; decide
      have factor_2_18 : (43 : ZMod 4461857401) ^ 435728 = 3874766303 := by
        calc
          (43 : ZMod 4461857401) ^ 435728 = (43 : ZMod 4461857401) ^ (217864 + 217864) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 217864 * (43 : ZMod 4461857401) ^ 217864 := by rw [pow_add]
          _ = 3874766303 := by rw [factor_2_17]; decide
      have factor_2_19 : (43 : ZMod 4461857401) ^ 871456 = 2996741971 := by
        calc
          (43 : ZMod 4461857401) ^ 871456 = (43 : ZMod 4461857401) ^ (435728 + 435728) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 435728 * (43 : ZMod 4461857401) ^ 435728 := by rw [pow_add]
          _ = 2996741971 := by rw [factor_2_18]; decide
      have factor_2_20 : (43 : ZMod 4461857401) ^ 1742913 = 1803123230 := by
        calc
          (43 : ZMod 4461857401) ^ 1742913 = (43 : ZMod 4461857401) ^ (871456 + 871456 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 871456 * (43 : ZMod 4461857401) ^ 871456) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1803123230 := by rw [factor_2_19]; decide
      have factor_2_21 : (43 : ZMod 4461857401) ^ 3485826 = 4063554785 := by
        calc
          (43 : ZMod 4461857401) ^ 3485826 = (43 : ZMod 4461857401) ^ (1742913 + 1742913) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 1742913 * (43 : ZMod 4461857401) ^ 1742913 := by rw [pow_add]
          _ = 4063554785 := by rw [factor_2_20]; decide
      have factor_2_22 : (43 : ZMod 4461857401) ^ 6971652 = 2067964042 := by
        calc
          (43 : ZMod 4461857401) ^ 6971652 = (43 : ZMod 4461857401) ^ (3485826 + 3485826) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 3485826 * (43 : ZMod 4461857401) ^ 3485826 := by rw [pow_add]
          _ = 2067964042 := by rw [factor_2_21]; decide
      have factor_2_23 : (43 : ZMod 4461857401) ^ 13943304 = 3825776360 := by
        calc
          (43 : ZMod 4461857401) ^ 13943304 = (43 : ZMod 4461857401) ^ (6971652 + 6971652) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 6971652 * (43 : ZMod 4461857401) ^ 6971652 := by rw [pow_add]
          _ = 3825776360 := by rw [factor_2_22]; decide
      have factor_2_24 : (43 : ZMod 4461857401) ^ 27886608 = 3288516161 := by
        calc
          (43 : ZMod 4461857401) ^ 27886608 = (43 : ZMod 4461857401) ^ (13943304 + 13943304) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 13943304 * (43 : ZMod 4461857401) ^ 13943304 := by rw [pow_add]
          _ = 3288516161 := by rw [factor_2_23]; decide
      have factor_2_25 : (43 : ZMod 4461857401) ^ 55773217 = 3959586705 := by
        calc
          (43 : ZMod 4461857401) ^ 55773217 = (43 : ZMod 4461857401) ^ (27886608 + 27886608 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 27886608 * (43 : ZMod 4461857401) ^ 27886608) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3959586705 := by rw [factor_2_24]; decide
      have factor_2_26 : (43 : ZMod 4461857401) ^ 111546435 = 4036387626 := by
        calc
          (43 : ZMod 4461857401) ^ 111546435 = (43 : ZMod 4461857401) ^ (55773217 + 55773217 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 55773217 * (43 : ZMod 4461857401) ^ 55773217) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 4036387626 := by rw [factor_2_25]; decide
      have factor_2_27 : (43 : ZMod 4461857401) ^ 223092870 = 796862862 := by
        calc
          (43 : ZMod 4461857401) ^ 223092870 = (43 : ZMod 4461857401) ^ (111546435 + 111546435) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 111546435 * (43 : ZMod 4461857401) ^ 111546435 := by rw [pow_add]
          _ = 796862862 := by rw [factor_2_26]; decide
      have factor_2_28 : (43 : ZMod 4461857401) ^ 446185740 = 2419304779 := by
        calc
          (43 : ZMod 4461857401) ^ 446185740 = (43 : ZMod 4461857401) ^ (223092870 + 223092870) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 223092870 * (43 : ZMod 4461857401) ^ 223092870 := by rw [pow_add]
          _ = 2419304779 := by rw [factor_2_27]; decide
      have factor_2_29 : (43 : ZMod 4461857401) ^ 892371480 = 1281969524 := by
        calc
          (43 : ZMod 4461857401) ^ 892371480 = (43 : ZMod 4461857401) ^ (446185740 + 446185740) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 446185740 * (43 : ZMod 4461857401) ^ 446185740 := by rw [pow_add]
          _ = 1281969524 := by rw [factor_2_28]; decide
      change (43 : ZMod 4461857401) ^ 892371480 ≠ 1
      rw [factor_2_29]
      decide
    ·
      have factor_3_0 : (43 : ZMod 4461857401) ^ 1 = 43 := by norm_num
      have factor_3_1 : (43 : ZMod 4461857401) ^ 2 = 1849 := by
        calc
          (43 : ZMod 4461857401) ^ 2 = (43 : ZMod 4461857401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 1 * (43 : ZMod 4461857401) ^ 1 := by rw [pow_add]
          _ = 1849 := by rw [factor_3_0]; decide
      have factor_3_2 : (43 : ZMod 4461857401) ^ 4 = 3418801 := by
        calc
          (43 : ZMod 4461857401) ^ 4 = (43 : ZMod 4461857401) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 2 * (43 : ZMod 4461857401) ^ 2 := by rw [pow_add]
          _ = 3418801 := by rw [factor_3_1]; decide
      have factor_3_3 : (43 : ZMod 4461857401) ^ 9 = 70573401 := by
        calc
          (43 : ZMod 4461857401) ^ 9 = (43 : ZMod 4461857401) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 4 * (43 : ZMod 4461857401) ^ 4) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 70573401 := by rw [factor_3_2]; decide
      have factor_3_4 : (43 : ZMod 4461857401) ^ 18 = 3062551739 := by
        calc
          (43 : ZMod 4461857401) ^ 18 = (43 : ZMod 4461857401) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 9 * (43 : ZMod 4461857401) ^ 9 := by rw [pow_add]
          _ = 3062551739 := by rw [factor_3_3]; decide
      have factor_3_5 : (43 : ZMod 4461857401) ^ 37 = 1819509735 := by
        calc
          (43 : ZMod 4461857401) ^ 37 = (43 : ZMod 4461857401) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 18 * (43 : ZMod 4461857401) ^ 18) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1819509735 := by rw [factor_3_4]; decide
      have factor_3_6 : (43 : ZMod 4461857401) ^ 75 = 1915829900 := by
        calc
          (43 : ZMod 4461857401) ^ 75 = (43 : ZMod 4461857401) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 37 * (43 : ZMod 4461857401) ^ 37) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1915829900 := by rw [factor_3_5]; decide
      have factor_3_7 : (43 : ZMod 4461857401) ^ 151 = 2106270456 := by
        calc
          (43 : ZMod 4461857401) ^ 151 = (43 : ZMod 4461857401) ^ (75 + 75 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 75 * (43 : ZMod 4461857401) ^ 75) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2106270456 := by rw [factor_3_6]; decide
      have factor_3_8 : (43 : ZMod 4461857401) ^ 303 = 2572420063 := by
        calc
          (43 : ZMod 4461857401) ^ 303 = (43 : ZMod 4461857401) ^ (151 + 151 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 151 * (43 : ZMod 4461857401) ^ 151) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2572420063 := by rw [factor_3_7]; decide
      have factor_3_9 : (43 : ZMod 4461857401) ^ 607 = 3050750215 := by
        calc
          (43 : ZMod 4461857401) ^ 607 = (43 : ZMod 4461857401) ^ (303 + 303 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 303 * (43 : ZMod 4461857401) ^ 303) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3050750215 := by rw [factor_3_8]; decide
      have factor_3_10 : (43 : ZMod 4461857401) ^ 1215 = 3861422372 := by
        calc
          (43 : ZMod 4461857401) ^ 1215 = (43 : ZMod 4461857401) ^ (607 + 607 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 607 * (43 : ZMod 4461857401) ^ 607) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3861422372 := by rw [factor_3_9]; decide
      have factor_3_11 : (43 : ZMod 4461857401) ^ 2431 = 2151211807 := by
        calc
          (43 : ZMod 4461857401) ^ 2431 = (43 : ZMod 4461857401) ^ (1215 + 1215 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 1215 * (43 : ZMod 4461857401) ^ 1215) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2151211807 := by rw [factor_3_10]; decide
      have factor_3_12 : (43 : ZMod 4461857401) ^ 4863 = 2600042284 := by
        calc
          (43 : ZMod 4461857401) ^ 4863 = (43 : ZMod 4461857401) ^ (2431 + 2431 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 2431 * (43 : ZMod 4461857401) ^ 2431) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2600042284 := by rw [factor_3_11]; decide
      have factor_3_13 : (43 : ZMod 4461857401) ^ 9726 = 3909666870 := by
        calc
          (43 : ZMod 4461857401) ^ 9726 = (43 : ZMod 4461857401) ^ (4863 + 4863) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 4863 * (43 : ZMod 4461857401) ^ 4863 := by rw [pow_add]
          _ = 3909666870 := by rw [factor_3_12]; decide
      have factor_3_14 : (43 : ZMod 4461857401) ^ 19452 = 2689525768 := by
        calc
          (43 : ZMod 4461857401) ^ 19452 = (43 : ZMod 4461857401) ^ (9726 + 9726) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 9726 * (43 : ZMod 4461857401) ^ 9726 := by rw [pow_add]
          _ = 2689525768 := by rw [factor_3_13]; decide
      have factor_3_15 : (43 : ZMod 4461857401) ^ 38904 = 953763643 := by
        calc
          (43 : ZMod 4461857401) ^ 38904 = (43 : ZMod 4461857401) ^ (19452 + 19452) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 19452 * (43 : ZMod 4461857401) ^ 19452 := by rw [pow_add]
          _ = 953763643 := by rw [factor_3_14]; decide
      have factor_3_16 : (43 : ZMod 4461857401) ^ 77808 = 492673173 := by
        calc
          (43 : ZMod 4461857401) ^ 77808 = (43 : ZMod 4461857401) ^ (38904 + 38904) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 38904 * (43 : ZMod 4461857401) ^ 38904 := by rw [pow_add]
          _ = 492673173 := by rw [factor_3_15]; decide
      have factor_3_17 : (43 : ZMod 4461857401) ^ 155617 = 869185477 := by
        calc
          (43 : ZMod 4461857401) ^ 155617 = (43 : ZMod 4461857401) ^ (77808 + 77808 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 77808 * (43 : ZMod 4461857401) ^ 77808) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 869185477 := by rw [factor_3_16]; decide
      have factor_3_18 : (43 : ZMod 4461857401) ^ 311234 = 2784585149 := by
        calc
          (43 : ZMod 4461857401) ^ 311234 = (43 : ZMod 4461857401) ^ (155617 + 155617) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 155617 * (43 : ZMod 4461857401) ^ 155617 := by rw [pow_add]
          _ = 2784585149 := by rw [factor_3_17]; decide
      have factor_3_19 : (43 : ZMod 4461857401) ^ 622468 = 4444558690 := by
        calc
          (43 : ZMod 4461857401) ^ 622468 = (43 : ZMod 4461857401) ^ (311234 + 311234) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 311234 * (43 : ZMod 4461857401) ^ 311234 := by rw [pow_add]
          _ = 4444558690 := by rw [factor_3_18]; decide
      have factor_3_20 : (43 : ZMod 4461857401) ^ 1244937 = 1738501503 := by
        calc
          (43 : ZMod 4461857401) ^ 1244937 = (43 : ZMod 4461857401) ^ (622468 + 622468 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 622468 * (43 : ZMod 4461857401) ^ 622468) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1738501503 := by rw [factor_3_19]; decide
      have factor_3_21 : (43 : ZMod 4461857401) ^ 2489875 = 4242700755 := by
        calc
          (43 : ZMod 4461857401) ^ 2489875 = (43 : ZMod 4461857401) ^ (1244937 + 1244937 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 1244937 * (43 : ZMod 4461857401) ^ 1244937) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 4242700755 := by rw [factor_3_20]; decide
      have factor_3_22 : (43 : ZMod 4461857401) ^ 4979751 = 1205692363 := by
        calc
          (43 : ZMod 4461857401) ^ 4979751 = (43 : ZMod 4461857401) ^ (2489875 + 2489875 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 2489875 * (43 : ZMod 4461857401) ^ 2489875) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1205692363 := by rw [factor_3_21]; decide
      have factor_3_23 : (43 : ZMod 4461857401) ^ 9959503 = 4078331332 := by
        calc
          (43 : ZMod 4461857401) ^ 9959503 = (43 : ZMod 4461857401) ^ (4979751 + 4979751 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 4979751 * (43 : ZMod 4461857401) ^ 4979751) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 4078331332 := by rw [factor_3_22]; decide
      have factor_3_24 : (43 : ZMod 4461857401) ^ 19919006 = 4177930567 := by
        calc
          (43 : ZMod 4461857401) ^ 19919006 = (43 : ZMod 4461857401) ^ (9959503 + 9959503) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 9959503 * (43 : ZMod 4461857401) ^ 9959503 := by rw [pow_add]
          _ = 4177930567 := by rw [factor_3_23]; decide
      have factor_3_25 : (43 : ZMod 4461857401) ^ 39838012 = 3561419893 := by
        calc
          (43 : ZMod 4461857401) ^ 39838012 = (43 : ZMod 4461857401) ^ (19919006 + 19919006) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 19919006 * (43 : ZMod 4461857401) ^ 19919006 := by rw [pow_add]
          _ = 3561419893 := by rw [factor_3_24]; decide
      have factor_3_26 : (43 : ZMod 4461857401) ^ 79676025 = 2695231738 := by
        calc
          (43 : ZMod 4461857401) ^ 79676025 = (43 : ZMod 4461857401) ^ (39838012 + 39838012 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 39838012 * (43 : ZMod 4461857401) ^ 39838012) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2695231738 := by rw [factor_3_25]; decide
      have factor_3_27 : (43 : ZMod 4461857401) ^ 159352050 = 996221258 := by
        calc
          (43 : ZMod 4461857401) ^ 159352050 = (43 : ZMod 4461857401) ^ (79676025 + 79676025) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 79676025 * (43 : ZMod 4461857401) ^ 79676025 := by rw [pow_add]
          _ = 996221258 := by rw [factor_3_26]; decide
      have factor_3_28 : (43 : ZMod 4461857401) ^ 318704100 = 3691619853 := by
        calc
          (43 : ZMod 4461857401) ^ 318704100 = (43 : ZMod 4461857401) ^ (159352050 + 159352050) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 159352050 * (43 : ZMod 4461857401) ^ 159352050 := by rw [pow_add]
          _ = 3691619853 := by rw [factor_3_27]; decide
      have factor_3_29 : (43 : ZMod 4461857401) ^ 637408200 = 3843519023 := by
        calc
          (43 : ZMod 4461857401) ^ 637408200 = (43 : ZMod 4461857401) ^ (318704100 + 318704100) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 318704100 * (43 : ZMod 4461857401) ^ 318704100 := by rw [pow_add]
          _ = 3843519023 := by rw [factor_3_28]; decide
      change (43 : ZMod 4461857401) ^ 637408200 ≠ 1
      rw [factor_3_29]
      decide
    ·
      have factor_4_0 : (43 : ZMod 4461857401) ^ 1 = 43 := by norm_num
      have factor_4_1 : (43 : ZMod 4461857401) ^ 3 = 79507 := by
        calc
          (43 : ZMod 4461857401) ^ 3 = (43 : ZMod 4461857401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 1 * (43 : ZMod 4461857401) ^ 1) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 79507 := by rw [factor_4_0]; decide
      have factor_4_2 : (43 : ZMod 4461857401) ^ 6 = 1859505648 := by
        calc
          (43 : ZMod 4461857401) ^ 6 = (43 : ZMod 4461857401) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 3 * (43 : ZMod 4461857401) ^ 3 := by rw [pow_add]
          _ = 1859505648 := by rw [factor_4_1]; decide
      have factor_4_3 : (43 : ZMod 4461857401) ^ 12 = 2524640250 := by
        calc
          (43 : ZMod 4461857401) ^ 12 = (43 : ZMod 4461857401) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 6 * (43 : ZMod 4461857401) ^ 6 := by rw [pow_add]
          _ = 2524640250 := by rw [factor_4_2]; decide
      have factor_4_4 : (43 : ZMod 4461857401) ^ 24 = 3060667994 := by
        calc
          (43 : ZMod 4461857401) ^ 24 = (43 : ZMod 4461857401) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 12 * (43 : ZMod 4461857401) ^ 12 := by rw [pow_add]
          _ = 3060667994 := by rw [factor_4_3]; decide
      have factor_4_5 : (43 : ZMod 4461857401) ^ 48 = 2126244588 := by
        calc
          (43 : ZMod 4461857401) ^ 48 = (43 : ZMod 4461857401) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 24 * (43 : ZMod 4461857401) ^ 24 := by rw [pow_add]
          _ = 2126244588 := by rw [factor_4_4]; decide
      have factor_4_6 : (43 : ZMod 4461857401) ^ 96 = 3255567008 := by
        calc
          (43 : ZMod 4461857401) ^ 96 = (43 : ZMod 4461857401) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 48 * (43 : ZMod 4461857401) ^ 48 := by rw [pow_add]
          _ = 3255567008 := by rw [factor_4_5]; decide
      have factor_4_7 : (43 : ZMod 4461857401) ^ 193 = 2660394447 := by
        calc
          (43 : ZMod 4461857401) ^ 193 = (43 : ZMod 4461857401) ^ (96 + 96 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 96 * (43 : ZMod 4461857401) ^ 96) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2660394447 := by rw [factor_4_6]; decide
      have factor_4_8 : (43 : ZMod 4461857401) ^ 386 = 688998682 := by
        calc
          (43 : ZMod 4461857401) ^ 386 = (43 : ZMod 4461857401) ^ (193 + 193) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 193 * (43 : ZMod 4461857401) ^ 193 := by rw [pow_add]
          _ = 688998682 := by rw [factor_4_7]; decide
      have factor_4_9 : (43 : ZMod 4461857401) ^ 773 = 4155903028 := by
        calc
          (43 : ZMod 4461857401) ^ 773 = (43 : ZMod 4461857401) ^ (386 + 386 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 386 * (43 : ZMod 4461857401) ^ 386) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 4155903028 := by rw [factor_4_8]; decide
      have factor_4_10 : (43 : ZMod 4461857401) ^ 1547 = 3919744634 := by
        calc
          (43 : ZMod 4461857401) ^ 1547 = (43 : ZMod 4461857401) ^ (773 + 773 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 773 * (43 : ZMod 4461857401) ^ 773) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3919744634 := by rw [factor_4_9]; decide
      have factor_4_11 : (43 : ZMod 4461857401) ^ 3094 = 4305612142 := by
        calc
          (43 : ZMod 4461857401) ^ 3094 = (43 : ZMod 4461857401) ^ (1547 + 1547) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 1547 * (43 : ZMod 4461857401) ^ 1547 := by rw [pow_add]
          _ = 4305612142 := by rw [factor_4_10]; decide
      have factor_4_12 : (43 : ZMod 4461857401) ^ 6189 = 253042330 := by
        calc
          (43 : ZMod 4461857401) ^ 6189 = (43 : ZMod 4461857401) ^ (3094 + 3094 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 3094 * (43 : ZMod 4461857401) ^ 3094) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 253042330 := by rw [factor_4_11]; decide
      have factor_4_13 : (43 : ZMod 4461857401) ^ 12378 = 715890280 := by
        calc
          (43 : ZMod 4461857401) ^ 12378 = (43 : ZMod 4461857401) ^ (6189 + 6189) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 6189 * (43 : ZMod 4461857401) ^ 6189 := by rw [pow_add]
          _ = 715890280 := by rw [factor_4_12]; decide
      have factor_4_14 : (43 : ZMod 4461857401) ^ 24757 = 262118691 := by
        calc
          (43 : ZMod 4461857401) ^ 24757 = (43 : ZMod 4461857401) ^ (12378 + 12378 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 12378 * (43 : ZMod 4461857401) ^ 12378) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 262118691 := by rw [factor_4_13]; decide
      have factor_4_15 : (43 : ZMod 4461857401) ^ 49514 = 2499666515 := by
        calc
          (43 : ZMod 4461857401) ^ 49514 = (43 : ZMod 4461857401) ^ (24757 + 24757) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 24757 * (43 : ZMod 4461857401) ^ 24757 := by rw [pow_add]
          _ = 2499666515 := by rw [factor_4_14]; decide
      have factor_4_16 : (43 : ZMod 4461857401) ^ 99029 = 2747035642 := by
        calc
          (43 : ZMod 4461857401) ^ 99029 = (43 : ZMod 4461857401) ^ (49514 + 49514 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 49514 * (43 : ZMod 4461857401) ^ 49514) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2747035642 := by rw [factor_4_15]; decide
      have factor_4_17 : (43 : ZMod 4461857401) ^ 198058 = 1421125532 := by
        calc
          (43 : ZMod 4461857401) ^ 198058 = (43 : ZMod 4461857401) ^ (99029 + 99029) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 99029 * (43 : ZMod 4461857401) ^ 99029 := by rw [pow_add]
          _ = 1421125532 := by rw [factor_4_16]; decide
      have factor_4_18 : (43 : ZMod 4461857401) ^ 396116 = 338932914 := by
        calc
          (43 : ZMod 4461857401) ^ 396116 = (43 : ZMod 4461857401) ^ (198058 + 198058) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 198058 * (43 : ZMod 4461857401) ^ 198058 := by rw [pow_add]
          _ = 338932914 := by rw [factor_4_17]; decide
      have factor_4_19 : (43 : ZMod 4461857401) ^ 792233 = 3297944229 := by
        calc
          (43 : ZMod 4461857401) ^ 792233 = (43 : ZMod 4461857401) ^ (396116 + 396116 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 396116 * (43 : ZMod 4461857401) ^ 396116) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3297944229 := by rw [factor_4_18]; decide
      have factor_4_20 : (43 : ZMod 4461857401) ^ 1584466 = 801365207 := by
        calc
          (43 : ZMod 4461857401) ^ 1584466 = (43 : ZMod 4461857401) ^ (792233 + 792233) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 792233 * (43 : ZMod 4461857401) ^ 792233 := by rw [pow_add]
          _ = 801365207 := by rw [factor_4_19]; decide
      have factor_4_21 : (43 : ZMod 4461857401) ^ 3168932 = 826454453 := by
        calc
          (43 : ZMod 4461857401) ^ 3168932 = (43 : ZMod 4461857401) ^ (1584466 + 1584466) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 1584466 * (43 : ZMod 4461857401) ^ 1584466 := by rw [pow_add]
          _ = 826454453 := by rw [factor_4_20]; decide
      have factor_4_22 : (43 : ZMod 4461857401) ^ 6337865 = 3581807584 := by
        calc
          (43 : ZMod 4461857401) ^ 6337865 = (43 : ZMod 4461857401) ^ (3168932 + 3168932 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 3168932 * (43 : ZMod 4461857401) ^ 3168932) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3581807584 := by rw [factor_4_21]; decide
      have factor_4_23 : (43 : ZMod 4461857401) ^ 12675731 = 1733685346 := by
        calc
          (43 : ZMod 4461857401) ^ 12675731 = (43 : ZMod 4461857401) ^ (6337865 + 6337865 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 6337865 * (43 : ZMod 4461857401) ^ 6337865) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1733685346 := by rw [factor_4_22]; decide
      have factor_4_24 : (43 : ZMod 4461857401) ^ 25351462 = 2500556965 := by
        calc
          (43 : ZMod 4461857401) ^ 25351462 = (43 : ZMod 4461857401) ^ (12675731 + 12675731) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 12675731 * (43 : ZMod 4461857401) ^ 12675731 := by rw [pow_add]
          _ = 2500556965 := by rw [factor_4_23]; decide
      have factor_4_25 : (43 : ZMod 4461857401) ^ 50702925 = 2480379713 := by
        calc
          (43 : ZMod 4461857401) ^ 50702925 = (43 : ZMod 4461857401) ^ (25351462 + 25351462 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 25351462 * (43 : ZMod 4461857401) ^ 25351462) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2480379713 := by rw [factor_4_24]; decide
      have factor_4_26 : (43 : ZMod 4461857401) ^ 101405850 = 2539136240 := by
        calc
          (43 : ZMod 4461857401) ^ 101405850 = (43 : ZMod 4461857401) ^ (50702925 + 50702925) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 50702925 * (43 : ZMod 4461857401) ^ 50702925 := by rw [pow_add]
          _ = 2539136240 := by rw [factor_4_25]; decide
      have factor_4_27 : (43 : ZMod 4461857401) ^ 202811700 = 4143951148 := by
        calc
          (43 : ZMod 4461857401) ^ 202811700 = (43 : ZMod 4461857401) ^ (101405850 + 101405850) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 101405850 * (43 : ZMod 4461857401) ^ 101405850 := by rw [pow_add]
          _ = 4143951148 := by rw [factor_4_26]; decide
      have factor_4_28 : (43 : ZMod 4461857401) ^ 405623400 = 403801066 := by
        calc
          (43 : ZMod 4461857401) ^ 405623400 = (43 : ZMod 4461857401) ^ (202811700 + 202811700) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 202811700 * (43 : ZMod 4461857401) ^ 202811700 := by rw [pow_add]
          _ = 403801066 := by rw [factor_4_27]; decide
      change (43 : ZMod 4461857401) ^ 405623400 ≠ 1
      rw [factor_4_28]
      decide
    ·
      have factor_5_0 : (43 : ZMod 4461857401) ^ 1 = 43 := by norm_num
      have factor_5_1 : (43 : ZMod 4461857401) ^ 2 = 1849 := by
        calc
          (43 : ZMod 4461857401) ^ 2 = (43 : ZMod 4461857401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 1 * (43 : ZMod 4461857401) ^ 1 := by rw [pow_add]
          _ = 1849 := by rw [factor_5_0]; decide
      have factor_5_2 : (43 : ZMod 4461857401) ^ 5 = 147008443 := by
        calc
          (43 : ZMod 4461857401) ^ 5 = (43 : ZMod 4461857401) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 2 * (43 : ZMod 4461857401) ^ 2) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 147008443 := by rw [factor_5_1]; decide
      have factor_5_3 : (43 : ZMod 4461857401) ^ 10 = 3034656243 := by
        calc
          (43 : ZMod 4461857401) ^ 10 = (43 : ZMod 4461857401) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 5 * (43 : ZMod 4461857401) ^ 5 := by rw [pow_add]
          _ = 3034656243 := by rw [factor_5_2]; decide
      have factor_5_4 : (43 : ZMod 4461857401) ^ 20 = 561123542 := by
        calc
          (43 : ZMod 4461857401) ^ 20 = (43 : ZMod 4461857401) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 10 * (43 : ZMod 4461857401) ^ 10 := by rw [pow_add]
          _ = 561123542 := by rw [factor_5_3]; decide
      have factor_5_5 : (43 : ZMod 4461857401) ^ 40 = 1419845423 := by
        calc
          (43 : ZMod 4461857401) ^ 40 = (43 : ZMod 4461857401) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 20 * (43 : ZMod 4461857401) ^ 20 := by rw [pow_add]
          _ = 1419845423 := by rw [factor_5_4]; decide
      have factor_5_6 : (43 : ZMod 4461857401) ^ 81 = 315078878 := by
        calc
          (43 : ZMod 4461857401) ^ 81 = (43 : ZMod 4461857401) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 40 * (43 : ZMod 4461857401) ^ 40) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 315078878 := by rw [factor_5_5]; decide
      have factor_5_7 : (43 : ZMod 4461857401) ^ 163 = 1766928900 := by
        calc
          (43 : ZMod 4461857401) ^ 163 = (43 : ZMod 4461857401) ^ (81 + 81 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 81 * (43 : ZMod 4461857401) ^ 81) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1766928900 := by rw [factor_5_6]; decide
      have factor_5_8 : (43 : ZMod 4461857401) ^ 327 = 3287574470 := by
        calc
          (43 : ZMod 4461857401) ^ 327 = (43 : ZMod 4461857401) ^ (163 + 163 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 163 * (43 : ZMod 4461857401) ^ 163) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3287574470 := by rw [factor_5_7]; decide
      have factor_5_9 : (43 : ZMod 4461857401) ^ 654 = 3556563006 := by
        calc
          (43 : ZMod 4461857401) ^ 654 = (43 : ZMod 4461857401) ^ (327 + 327) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 327 * (43 : ZMod 4461857401) ^ 327 := by rw [pow_add]
          _ = 3556563006 := by rw [factor_5_8]; decide
      have factor_5_10 : (43 : ZMod 4461857401) ^ 1309 = 1579190775 := by
        calc
          (43 : ZMod 4461857401) ^ 1309 = (43 : ZMod 4461857401) ^ (654 + 654 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 654 * (43 : ZMod 4461857401) ^ 654) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1579190775 := by rw [factor_5_9]; decide
      have factor_5_11 : (43 : ZMod 4461857401) ^ 2618 = 3232469858 := by
        calc
          (43 : ZMod 4461857401) ^ 2618 = (43 : ZMod 4461857401) ^ (1309 + 1309) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 1309 * (43 : ZMod 4461857401) ^ 1309 := by rw [pow_add]
          _ = 3232469858 := by rw [factor_5_10]; decide
      have factor_5_12 : (43 : ZMod 4461857401) ^ 5237 = 2832546811 := by
        calc
          (43 : ZMod 4461857401) ^ 5237 = (43 : ZMod 4461857401) ^ (2618 + 2618 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 2618 * (43 : ZMod 4461857401) ^ 2618) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2832546811 := by rw [factor_5_11]; decide
      have factor_5_13 : (43 : ZMod 4461857401) ^ 10474 = 3352237002 := by
        calc
          (43 : ZMod 4461857401) ^ 10474 = (43 : ZMod 4461857401) ^ (5237 + 5237) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 5237 * (43 : ZMod 4461857401) ^ 5237 := by rw [pow_add]
          _ = 3352237002 := by rw [factor_5_12]; decide
      have factor_5_14 : (43 : ZMod 4461857401) ^ 20948 = 430799035 := by
        calc
          (43 : ZMod 4461857401) ^ 20948 = (43 : ZMod 4461857401) ^ (10474 + 10474) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 10474 * (43 : ZMod 4461857401) ^ 10474 := by rw [pow_add]
          _ = 430799035 := by rw [factor_5_13]; decide
      have factor_5_15 : (43 : ZMod 4461857401) ^ 41896 = 33661331 := by
        calc
          (43 : ZMod 4461857401) ^ 41896 = (43 : ZMod 4461857401) ^ (20948 + 20948) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 20948 * (43 : ZMod 4461857401) ^ 20948 := by rw [pow_add]
          _ = 33661331 := by rw [factor_5_14]; decide
      have factor_5_16 : (43 : ZMod 4461857401) ^ 83793 = 1964578907 := by
        calc
          (43 : ZMod 4461857401) ^ 83793 = (43 : ZMod 4461857401) ^ (41896 + 41896 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 41896 * (43 : ZMod 4461857401) ^ 41896) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1964578907 := by rw [factor_5_15]; decide
      have factor_5_17 : (43 : ZMod 4461857401) ^ 167587 = 1655660890 := by
        calc
          (43 : ZMod 4461857401) ^ 167587 = (43 : ZMod 4461857401) ^ (83793 + 83793 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 83793 * (43 : ZMod 4461857401) ^ 83793) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1655660890 := by rw [factor_5_16]; decide
      have factor_5_18 : (43 : ZMod 4461857401) ^ 335175 = 1766483932 := by
        calc
          (43 : ZMod 4461857401) ^ 335175 = (43 : ZMod 4461857401) ^ (167587 + 167587 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 167587 * (43 : ZMod 4461857401) ^ 167587) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1766483932 := by rw [factor_5_17]; decide
      have factor_5_19 : (43 : ZMod 4461857401) ^ 670351 = 2129602710 := by
        calc
          (43 : ZMod 4461857401) ^ 670351 = (43 : ZMod 4461857401) ^ (335175 + 335175 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 335175 * (43 : ZMod 4461857401) ^ 335175) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2129602710 := by rw [factor_5_18]; decide
      have factor_5_20 : (43 : ZMod 4461857401) ^ 1340702 = 2724628091 := by
        calc
          (43 : ZMod 4461857401) ^ 1340702 = (43 : ZMod 4461857401) ^ (670351 + 670351) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 670351 * (43 : ZMod 4461857401) ^ 670351 := by rw [pow_add]
          _ = 2724628091 := by rw [factor_5_19]; decide
      have factor_5_21 : (43 : ZMod 4461857401) ^ 2681404 = 2580539271 := by
        calc
          (43 : ZMod 4461857401) ^ 2681404 = (43 : ZMod 4461857401) ^ (1340702 + 1340702) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 1340702 * (43 : ZMod 4461857401) ^ 1340702 := by rw [pow_add]
          _ = 2580539271 := by rw [factor_5_20]; decide
      have factor_5_22 : (43 : ZMod 4461857401) ^ 5362809 = 3911853071 := by
        calc
          (43 : ZMod 4461857401) ^ 5362809 = (43 : ZMod 4461857401) ^ (2681404 + 2681404 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 2681404 * (43 : ZMod 4461857401) ^ 2681404) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3911853071 := by rw [factor_5_21]; decide
      have factor_5_23 : (43 : ZMod 4461857401) ^ 10725618 = 347907955 := by
        calc
          (43 : ZMod 4461857401) ^ 10725618 = (43 : ZMod 4461857401) ^ (5362809 + 5362809) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 5362809 * (43 : ZMod 4461857401) ^ 5362809 := by rw [pow_add]
          _ = 347907955 := by rw [factor_5_22]; decide
      have factor_5_24 : (43 : ZMod 4461857401) ^ 21451237 = 2224598820 := by
        calc
          (43 : ZMod 4461857401) ^ 21451237 = (43 : ZMod 4461857401) ^ (10725618 + 10725618 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 10725618 * (43 : ZMod 4461857401) ^ 10725618) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2224598820 := by rw [factor_5_23]; decide
      have factor_5_25 : (43 : ZMod 4461857401) ^ 42902475 = 1607703662 := by
        calc
          (43 : ZMod 4461857401) ^ 42902475 = (43 : ZMod 4461857401) ^ (21451237 + 21451237 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 21451237 * (43 : ZMod 4461857401) ^ 21451237) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1607703662 := by rw [factor_5_24]; decide
      have factor_5_26 : (43 : ZMod 4461857401) ^ 85804950 = 4400822666 := by
        calc
          (43 : ZMod 4461857401) ^ 85804950 = (43 : ZMod 4461857401) ^ (42902475 + 42902475) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 42902475 * (43 : ZMod 4461857401) ^ 42902475 := by rw [pow_add]
          _ = 4400822666 := by rw [factor_5_25]; decide
      have factor_5_27 : (43 : ZMod 4461857401) ^ 171609900 = 2899423518 := by
        calc
          (43 : ZMod 4461857401) ^ 171609900 = (43 : ZMod 4461857401) ^ (85804950 + 85804950) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 85804950 * (43 : ZMod 4461857401) ^ 85804950 := by rw [pow_add]
          _ = 2899423518 := by rw [factor_5_26]; decide
      have factor_5_28 : (43 : ZMod 4461857401) ^ 343219800 = 725133765 := by
        calc
          (43 : ZMod 4461857401) ^ 343219800 = (43 : ZMod 4461857401) ^ (171609900 + 171609900) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 171609900 * (43 : ZMod 4461857401) ^ 171609900 := by rw [pow_add]
          _ = 725133765 := by rw [factor_5_27]; decide
      change (43 : ZMod 4461857401) ^ 343219800 ≠ 1
      rw [factor_5_28]
      decide
    ·
      have factor_6_0 : (43 : ZMod 4461857401) ^ 1 = 43 := by norm_num
      have factor_6_1 : (43 : ZMod 4461857401) ^ 3 = 79507 := by
        calc
          (43 : ZMod 4461857401) ^ 3 = (43 : ZMod 4461857401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 1 * (43 : ZMod 4461857401) ^ 1) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 79507 := by rw [factor_6_0]; decide
      have factor_6_2 : (43 : ZMod 4461857401) ^ 7 = 4107167047 := by
        calc
          (43 : ZMod 4461857401) ^ 7 = (43 : ZMod 4461857401) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 3 * (43 : ZMod 4461857401) ^ 3) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 4107167047 := by rw [factor_6_1]; decide
      have factor_6_3 : (43 : ZMod 4461857401) ^ 15 = 993457963 := by
        calc
          (43 : ZMod 4461857401) ^ 15 = (43 : ZMod 4461857401) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 7 * (43 : ZMod 4461857401) ^ 7) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 993457963 := by rw [factor_6_2]; decide
      have factor_6_4 : (43 : ZMod 4461857401) ^ 31 = 3097384697 := by
        calc
          (43 : ZMod 4461857401) ^ 31 = (43 : ZMod 4461857401) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 15 * (43 : ZMod 4461857401) ^ 15) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3097384697 := by rw [factor_6_3]; decide
      have factor_6_5 : (43 : ZMod 4461857401) ^ 62 = 1517010037 := by
        calc
          (43 : ZMod 4461857401) ^ 62 = (43 : ZMod 4461857401) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 31 * (43 : ZMod 4461857401) ^ 31 := by rw [pow_add]
          _ = 1517010037 := by rw [factor_6_4]; decide
      have factor_6_6 : (43 : ZMod 4461857401) ^ 125 = 1942950350 := by
        calc
          (43 : ZMod 4461857401) ^ 125 = (43 : ZMod 4461857401) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 62 * (43 : ZMod 4461857401) ^ 62) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1942950350 := by rw [factor_6_5]; decide
      have factor_6_7 : (43 : ZMod 4461857401) ^ 250 = 3032336928 := by
        calc
          (43 : ZMod 4461857401) ^ 250 = (43 : ZMod 4461857401) ^ (125 + 125) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 125 * (43 : ZMod 4461857401) ^ 125 := by rw [pow_add]
          _ = 3032336928 := by rw [factor_6_6]; decide
      have factor_6_8 : (43 : ZMod 4461857401) ^ 500 = 2743111357 := by
        calc
          (43 : ZMod 4461857401) ^ 500 = (43 : ZMod 4461857401) ^ (250 + 250) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 250 * (43 : ZMod 4461857401) ^ 250 := by rw [pow_add]
          _ = 2743111357 := by rw [factor_6_7]; decide
      have factor_6_9 : (43 : ZMod 4461857401) ^ 1001 = 3181741150 := by
        calc
          (43 : ZMod 4461857401) ^ 1001 = (43 : ZMod 4461857401) ^ (500 + 500 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 500 * (43 : ZMod 4461857401) ^ 500) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3181741150 := by rw [factor_6_8]; decide
      have factor_6_10 : (43 : ZMod 4461857401) ^ 2002 = 2573245763 := by
        calc
          (43 : ZMod 4461857401) ^ 2002 = (43 : ZMod 4461857401) ^ (1001 + 1001) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 1001 * (43 : ZMod 4461857401) ^ 1001 := by rw [pow_add]
          _ = 2573245763 := by rw [factor_6_9]; decide
      have factor_6_11 : (43 : ZMod 4461857401) ^ 4004 = 3451318934 := by
        calc
          (43 : ZMod 4461857401) ^ 4004 = (43 : ZMod 4461857401) ^ (2002 + 2002) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 2002 * (43 : ZMod 4461857401) ^ 2002 := by rw [pow_add]
          _ = 3451318934 := by rw [factor_6_10]; decide
      have factor_6_12 : (43 : ZMod 4461857401) ^ 8009 = 1823717704 := by
        calc
          (43 : ZMod 4461857401) ^ 8009 = (43 : ZMod 4461857401) ^ (4004 + 4004 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 4004 * (43 : ZMod 4461857401) ^ 4004) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1823717704 := by rw [factor_6_11]; decide
      have factor_6_13 : (43 : ZMod 4461857401) ^ 16019 = 3328716524 := by
        calc
          (43 : ZMod 4461857401) ^ 16019 = (43 : ZMod 4461857401) ^ (8009 + 8009 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 8009 * (43 : ZMod 4461857401) ^ 8009) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3328716524 := by rw [factor_6_12]; decide
      have factor_6_14 : (43 : ZMod 4461857401) ^ 32038 = 4369000150 := by
        calc
          (43 : ZMod 4461857401) ^ 32038 = (43 : ZMod 4461857401) ^ (16019 + 16019) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 16019 * (43 : ZMod 4461857401) ^ 16019 := by rw [pow_add]
          _ = 4369000150 := by rw [factor_6_13]; decide
      have factor_6_15 : (43 : ZMod 4461857401) ^ 64077 = 3942488822 := by
        calc
          (43 : ZMod 4461857401) ^ 64077 = (43 : ZMod 4461857401) ^ (32038 + 32038 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 32038 * (43 : ZMod 4461857401) ^ 32038) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3942488822 := by rw [factor_6_14]; decide
      have factor_6_16 : (43 : ZMod 4461857401) ^ 128155 = 2089453620 := by
        calc
          (43 : ZMod 4461857401) ^ 128155 = (43 : ZMod 4461857401) ^ (64077 + 64077 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 64077 * (43 : ZMod 4461857401) ^ 64077) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2089453620 := by rw [factor_6_15]; decide
      have factor_6_17 : (43 : ZMod 4461857401) ^ 256310 = 1035885686 := by
        calc
          (43 : ZMod 4461857401) ^ 256310 = (43 : ZMod 4461857401) ^ (128155 + 128155) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 128155 * (43 : ZMod 4461857401) ^ 128155 := by rw [pow_add]
          _ = 1035885686 := by rw [factor_6_16]; decide
      have factor_6_18 : (43 : ZMod 4461857401) ^ 512621 = 3424143367 := by
        calc
          (43 : ZMod 4461857401) ^ 512621 = (43 : ZMod 4461857401) ^ (256310 + 256310 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 256310 * (43 : ZMod 4461857401) ^ 256310) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3424143367 := by rw [factor_6_17]; decide
      have factor_6_19 : (43 : ZMod 4461857401) ^ 1025242 = 1824151985 := by
        calc
          (43 : ZMod 4461857401) ^ 1025242 = (43 : ZMod 4461857401) ^ (512621 + 512621) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 512621 * (43 : ZMod 4461857401) ^ 512621 := by rw [pow_add]
          _ = 1824151985 := by rw [factor_6_18]; decide
      have factor_6_20 : (43 : ZMod 4461857401) ^ 2050485 = 2091421787 := by
        calc
          (43 : ZMod 4461857401) ^ 2050485 = (43 : ZMod 4461857401) ^ (1025242 + 1025242 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 1025242 * (43 : ZMod 4461857401) ^ 1025242) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2091421787 := by rw [factor_6_19]; decide
      have factor_6_21 : (43 : ZMod 4461857401) ^ 4100971 = 1285349357 := by
        calc
          (43 : ZMod 4461857401) ^ 4100971 = (43 : ZMod 4461857401) ^ (2050485 + 2050485 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 2050485 * (43 : ZMod 4461857401) ^ 2050485) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1285349357 := by rw [factor_6_20]; decide
      have factor_6_22 : (43 : ZMod 4461857401) ^ 8201943 = 2060673267 := by
        calc
          (43 : ZMod 4461857401) ^ 8201943 = (43 : ZMod 4461857401) ^ (4100971 + 4100971 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 4100971 * (43 : ZMod 4461857401) ^ 4100971) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2060673267 := by rw [factor_6_21]; decide
      have factor_6_23 : (43 : ZMod 4461857401) ^ 16403887 = 571273112 := by
        calc
          (43 : ZMod 4461857401) ^ 16403887 = (43 : ZMod 4461857401) ^ (8201943 + 8201943 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 8201943 * (43 : ZMod 4461857401) ^ 8201943) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 571273112 := by rw [factor_6_22]; decide
      have factor_6_24 : (43 : ZMod 4461857401) ^ 32807775 = 1018129624 := by
        calc
          (43 : ZMod 4461857401) ^ 32807775 = (43 : ZMod 4461857401) ^ (16403887 + 16403887 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 16403887 * (43 : ZMod 4461857401) ^ 16403887) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1018129624 := by rw [factor_6_23]; decide
      have factor_6_25 : (43 : ZMod 4461857401) ^ 65615550 = 1668670910 := by
        calc
          (43 : ZMod 4461857401) ^ 65615550 = (43 : ZMod 4461857401) ^ (32807775 + 32807775) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 32807775 * (43 : ZMod 4461857401) ^ 32807775 := by rw [pow_add]
          _ = 1668670910 := by rw [factor_6_24]; decide
      have factor_6_26 : (43 : ZMod 4461857401) ^ 131231100 = 3430264025 := by
        calc
          (43 : ZMod 4461857401) ^ 131231100 = (43 : ZMod 4461857401) ^ (65615550 + 65615550) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 65615550 * (43 : ZMod 4461857401) ^ 65615550 := by rw [pow_add]
          _ = 3430264025 := by rw [factor_6_25]; decide
      have factor_6_27 : (43 : ZMod 4461857401) ^ 262462200 = 988160226 := by
        calc
          (43 : ZMod 4461857401) ^ 262462200 = (43 : ZMod 4461857401) ^ (131231100 + 131231100) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 131231100 * (43 : ZMod 4461857401) ^ 131231100 := by rw [pow_add]
          _ = 988160226 := by rw [factor_6_26]; decide
      change (43 : ZMod 4461857401) ^ 262462200 ≠ 1
      rw [factor_6_27]
      decide
    ·
      have factor_7_0 : (43 : ZMod 4461857401) ^ 1 = 43 := by norm_num
      have factor_7_1 : (43 : ZMod 4461857401) ^ 3 = 79507 := by
        calc
          (43 : ZMod 4461857401) ^ 3 = (43 : ZMod 4461857401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 1 * (43 : ZMod 4461857401) ^ 1) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 79507 := by rw [factor_7_0]; decide
      have factor_7_2 : (43 : ZMod 4461857401) ^ 6 = 1859505648 := by
        calc
          (43 : ZMod 4461857401) ^ 6 = (43 : ZMod 4461857401) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 3 * (43 : ZMod 4461857401) ^ 3 := by rw [pow_add]
          _ = 1859505648 := by rw [factor_7_1]; decide
      have factor_7_3 : (43 : ZMod 4461857401) ^ 13 = 1474953126 := by
        calc
          (43 : ZMod 4461857401) ^ 13 = (43 : ZMod 4461857401) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 6 * (43 : ZMod 4461857401) ^ 6) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1474953126 := by rw [factor_7_2]; decide
      have factor_7_4 : (43 : ZMod 4461857401) ^ 27 = 3751263220 := by
        calc
          (43 : ZMod 4461857401) ^ 27 = (43 : ZMod 4461857401) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 13 * (43 : ZMod 4461857401) ^ 13) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3751263220 := by rw [factor_7_3]; decide
      have factor_7_5 : (43 : ZMod 4461857401) ^ 55 = 941458679 := by
        calc
          (43 : ZMod 4461857401) ^ 55 = (43 : ZMod 4461857401) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 27 * (43 : ZMod 4461857401) ^ 27) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 941458679 := by rw [factor_7_4]; decide
      have factor_7_6 : (43 : ZMod 4461857401) ^ 111 = 2359247768 := by
        calc
          (43 : ZMod 4461857401) ^ 111 = (43 : ZMod 4461857401) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 55 * (43 : ZMod 4461857401) ^ 55) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2359247768 := by rw [factor_7_5]; decide
      have factor_7_7 : (43 : ZMod 4461857401) ^ 223 = 1059409331 := by
        calc
          (43 : ZMod 4461857401) ^ 223 = (43 : ZMod 4461857401) ^ (111 + 111 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 111 * (43 : ZMod 4461857401) ^ 111) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1059409331 := by rw [factor_7_6]; decide
      have factor_7_8 : (43 : ZMod 4461857401) ^ 447 = 4051652666 := by
        calc
          (43 : ZMod 4461857401) ^ 447 = (43 : ZMod 4461857401) ^ (223 + 223 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 223 * (43 : ZMod 4461857401) ^ 223) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 4051652666 := by rw [factor_7_7]; decide
      have factor_7_9 : (43 : ZMod 4461857401) ^ 895 = 2692901148 := by
        calc
          (43 : ZMod 4461857401) ^ 895 = (43 : ZMod 4461857401) ^ (447 + 447 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 447 * (43 : ZMod 4461857401) ^ 447) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2692901148 := by rw [factor_7_8]; decide
      have factor_7_10 : (43 : ZMod 4461857401) ^ 1791 = 244287808 := by
        calc
          (43 : ZMod 4461857401) ^ 1791 = (43 : ZMod 4461857401) ^ (895 + 895 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 895 * (43 : ZMod 4461857401) ^ 895) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 244287808 := by rw [factor_7_9]; decide
      have factor_7_11 : (43 : ZMod 4461857401) ^ 3583 = 3033304155 := by
        calc
          (43 : ZMod 4461857401) ^ 3583 = (43 : ZMod 4461857401) ^ (1791 + 1791 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 1791 * (43 : ZMod 4461857401) ^ 1791) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3033304155 := by rw [factor_7_10]; decide
      have factor_7_12 : (43 : ZMod 4461857401) ^ 7166 = 2892897308 := by
        calc
          (43 : ZMod 4461857401) ^ 7166 = (43 : ZMod 4461857401) ^ (3583 + 3583) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 3583 * (43 : ZMod 4461857401) ^ 3583 := by rw [pow_add]
          _ = 2892897308 := by rw [factor_7_11]; decide
      have factor_7_13 : (43 : ZMod 4461857401) ^ 14333 = 2403093591 := by
        calc
          (43 : ZMod 4461857401) ^ 14333 = (43 : ZMod 4461857401) ^ (7166 + 7166 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 7166 * (43 : ZMod 4461857401) ^ 7166) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2403093591 := by rw [factor_7_12]; decide
      have factor_7_14 : (43 : ZMod 4461857401) ^ 28666 = 568676099 := by
        calc
          (43 : ZMod 4461857401) ^ 28666 = (43 : ZMod 4461857401) ^ (14333 + 14333) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 14333 * (43 : ZMod 4461857401) ^ 14333 := by rw [pow_add]
          _ = 568676099 := by rw [factor_7_13]; decide
      have factor_7_15 : (43 : ZMod 4461857401) ^ 57332 = 3665975456 := by
        calc
          (43 : ZMod 4461857401) ^ 57332 = (43 : ZMod 4461857401) ^ (28666 + 28666) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 28666 * (43 : ZMod 4461857401) ^ 28666 := by rw [pow_add]
          _ = 3665975456 := by rw [factor_7_14]; decide
      have factor_7_16 : (43 : ZMod 4461857401) ^ 114665 = 3142427207 := by
        calc
          (43 : ZMod 4461857401) ^ 114665 = (43 : ZMod 4461857401) ^ (57332 + 57332 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 57332 * (43 : ZMod 4461857401) ^ 57332) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3142427207 := by rw [factor_7_15]; decide
      have factor_7_17 : (43 : ZMod 4461857401) ^ 229330 = 3444376493 := by
        calc
          (43 : ZMod 4461857401) ^ 229330 = (43 : ZMod 4461857401) ^ (114665 + 114665) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 114665 * (43 : ZMod 4461857401) ^ 114665 := by rw [pow_add]
          _ = 3444376493 := by rw [factor_7_16]; decide
      have factor_7_18 : (43 : ZMod 4461857401) ^ 458661 = 3041054996 := by
        calc
          (43 : ZMod 4461857401) ^ 458661 = (43 : ZMod 4461857401) ^ (229330 + 229330 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 229330 * (43 : ZMod 4461857401) ^ 229330) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3041054996 := by rw [factor_7_17]; decide
      have factor_7_19 : (43 : ZMod 4461857401) ^ 917322 = 485848527 := by
        calc
          (43 : ZMod 4461857401) ^ 917322 = (43 : ZMod 4461857401) ^ (458661 + 458661) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 458661 * (43 : ZMod 4461857401) ^ 458661 := by rw [pow_add]
          _ = 485848527 := by rw [factor_7_18]; decide
      have factor_7_20 : (43 : ZMod 4461857401) ^ 1834645 = 2979163799 := by
        calc
          (43 : ZMod 4461857401) ^ 1834645 = (43 : ZMod 4461857401) ^ (917322 + 917322 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 917322 * (43 : ZMod 4461857401) ^ 917322) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2979163799 := by rw [factor_7_19]; decide
      have factor_7_21 : (43 : ZMod 4461857401) ^ 3669290 = 1051693610 := by
        calc
          (43 : ZMod 4461857401) ^ 3669290 = (43 : ZMod 4461857401) ^ (1834645 + 1834645) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 1834645 * (43 : ZMod 4461857401) ^ 1834645 := by rw [pow_add]
          _ = 1051693610 := by rw [factor_7_20]; decide
      have factor_7_22 : (43 : ZMod 4461857401) ^ 7338581 = 3294296808 := by
        calc
          (43 : ZMod 4461857401) ^ 7338581 = (43 : ZMod 4461857401) ^ (3669290 + 3669290 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 3669290 * (43 : ZMod 4461857401) ^ 3669290) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3294296808 := by rw [factor_7_21]; decide
      have factor_7_23 : (43 : ZMod 4461857401) ^ 14677162 = 4228494570 := by
        calc
          (43 : ZMod 4461857401) ^ 14677162 = (43 : ZMod 4461857401) ^ (7338581 + 7338581) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 7338581 * (43 : ZMod 4461857401) ^ 7338581 := by rw [pow_add]
          _ = 4228494570 := by rw [factor_7_22]; decide
      have factor_7_24 : (43 : ZMod 4461857401) ^ 29354325 = 3726340361 := by
        calc
          (43 : ZMod 4461857401) ^ 29354325 = (43 : ZMod 4461857401) ^ (14677162 + 14677162 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 14677162 * (43 : ZMod 4461857401) ^ 14677162) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3726340361 := by rw [factor_7_23]; decide
      have factor_7_25 : (43 : ZMod 4461857401) ^ 58708650 = 4400973539 := by
        calc
          (43 : ZMod 4461857401) ^ 58708650 = (43 : ZMod 4461857401) ^ (29354325 + 29354325) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 29354325 * (43 : ZMod 4461857401) ^ 29354325 := by rw [pow_add]
          _ = 4400973539 := by rw [factor_7_24]; decide
      have factor_7_26 : (43 : ZMod 4461857401) ^ 117417300 = 451145259 := by
        calc
          (43 : ZMod 4461857401) ^ 117417300 = (43 : ZMod 4461857401) ^ (58708650 + 58708650) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 58708650 * (43 : ZMod 4461857401) ^ 58708650 := by rw [pow_add]
          _ = 451145259 := by rw [factor_7_25]; decide
      have factor_7_27 : (43 : ZMod 4461857401) ^ 234834600 = 2132735091 := by
        calc
          (43 : ZMod 4461857401) ^ 234834600 = (43 : ZMod 4461857401) ^ (117417300 + 117417300) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 117417300 * (43 : ZMod 4461857401) ^ 117417300 := by rw [pow_add]
          _ = 2132735091 := by rw [factor_7_26]; decide
      change (43 : ZMod 4461857401) ^ 234834600 ≠ 1
      rw [factor_7_27]
      decide
    ·
      have factor_8_0 : (43 : ZMod 4461857401) ^ 1 = 43 := by norm_num
      have factor_8_1 : (43 : ZMod 4461857401) ^ 2 = 1849 := by
        calc
          (43 : ZMod 4461857401) ^ 2 = (43 : ZMod 4461857401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 1 * (43 : ZMod 4461857401) ^ 1 := by rw [pow_add]
          _ = 1849 := by rw [factor_8_0]; decide
      have factor_8_2 : (43 : ZMod 4461857401) ^ 5 = 147008443 := by
        calc
          (43 : ZMod 4461857401) ^ 5 = (43 : ZMod 4461857401) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 2 * (43 : ZMod 4461857401) ^ 2) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 147008443 := by rw [factor_8_1]; decide
      have factor_8_3 : (43 : ZMod 4461857401) ^ 11 = 1096353820 := by
        calc
          (43 : ZMod 4461857401) ^ 11 = (43 : ZMod 4461857401) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 5 * (43 : ZMod 4461857401) ^ 5) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 1096353820 := by rw [factor_8_2]; decide
      have factor_8_4 : (43 : ZMod 4461857401) ^ 23 = 3599158596 := by
        calc
          (43 : ZMod 4461857401) ^ 23 = (43 : ZMod 4461857401) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 11 * (43 : ZMod 4461857401) ^ 11) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3599158596 := by rw [factor_8_3]; decide
      have factor_8_5 : (43 : ZMod 4461857401) ^ 46 = 230396267 := by
        calc
          (43 : ZMod 4461857401) ^ 46 = (43 : ZMod 4461857401) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 23 * (43 : ZMod 4461857401) ^ 23 := by rw [pow_add]
          _ = 230396267 := by rw [factor_8_4]; decide
      have factor_8_6 : (43 : ZMod 4461857401) ^ 92 = 3444854552 := by
        calc
          (43 : ZMod 4461857401) ^ 92 = (43 : ZMod 4461857401) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 46 * (43 : ZMod 4461857401) ^ 46 := by rw [pow_add]
          _ = 3444854552 := by rw [factor_8_5]; decide
      have factor_8_7 : (43 : ZMod 4461857401) ^ 185 = 2209584900 := by
        calc
          (43 : ZMod 4461857401) ^ 185 = (43 : ZMod 4461857401) ^ (92 + 92 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 92 * (43 : ZMod 4461857401) ^ 92) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2209584900 := by rw [factor_8_6]; decide
      have factor_8_8 : (43 : ZMod 4461857401) ^ 370 = 1063677350 := by
        calc
          (43 : ZMod 4461857401) ^ 370 = (43 : ZMod 4461857401) ^ (185 + 185) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 185 * (43 : ZMod 4461857401) ^ 185 := by rw [pow_add]
          _ = 1063677350 := by rw [factor_8_7]; decide
      have factor_8_9 : (43 : ZMod 4461857401) ^ 740 = 2257079642 := by
        calc
          (43 : ZMod 4461857401) ^ 740 = (43 : ZMod 4461857401) ^ (370 + 370) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 370 * (43 : ZMod 4461857401) ^ 370 := by rw [pow_add]
          _ = 2257079642 := by rw [factor_8_8]; decide
      have factor_8_10 : (43 : ZMod 4461857401) ^ 1480 = 1742020802 := by
        calc
          (43 : ZMod 4461857401) ^ 1480 = (43 : ZMod 4461857401) ^ (740 + 740) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 740 * (43 : ZMod 4461857401) ^ 740 := by rw [pow_add]
          _ = 1742020802 := by rw [factor_8_9]; decide
      have factor_8_11 : (43 : ZMod 4461857401) ^ 2960 = 4007546684 := by
        calc
          (43 : ZMod 4461857401) ^ 2960 = (43 : ZMod 4461857401) ^ (1480 + 1480) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 1480 * (43 : ZMod 4461857401) ^ 1480 := by rw [pow_add]
          _ = 4007546684 := by rw [factor_8_10]; decide
      have factor_8_12 : (43 : ZMod 4461857401) ^ 5920 = 3809502125 := by
        calc
          (43 : ZMod 4461857401) ^ 5920 = (43 : ZMod 4461857401) ^ (2960 + 2960) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 2960 * (43 : ZMod 4461857401) ^ 2960 := by rw [pow_add]
          _ = 3809502125 := by rw [factor_8_11]; decide
      have factor_8_13 : (43 : ZMod 4461857401) ^ 11840 = 2774062597 := by
        calc
          (43 : ZMod 4461857401) ^ 11840 = (43 : ZMod 4461857401) ^ (5920 + 5920) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 5920 * (43 : ZMod 4461857401) ^ 5920 := by rw [pow_add]
          _ = 2774062597 := by rw [factor_8_12]; decide
      have factor_8_14 : (43 : ZMod 4461857401) ^ 23680 = 2435910048 := by
        calc
          (43 : ZMod 4461857401) ^ 23680 = (43 : ZMod 4461857401) ^ (11840 + 11840) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 11840 * (43 : ZMod 4461857401) ^ 11840 := by rw [pow_add]
          _ = 2435910048 := by rw [factor_8_13]; decide
      have factor_8_15 : (43 : ZMod 4461857401) ^ 47361 = 4051693068 := by
        calc
          (43 : ZMod 4461857401) ^ 47361 = (43 : ZMod 4461857401) ^ (23680 + 23680 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 23680 * (43 : ZMod 4461857401) ^ 23680) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 4051693068 := by rw [factor_8_14]; decide
      have factor_8_16 : (43 : ZMod 4461857401) ^ 94723 = 2410973922 := by
        calc
          (43 : ZMod 4461857401) ^ 94723 = (43 : ZMod 4461857401) ^ (47361 + 47361 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 47361 * (43 : ZMod 4461857401) ^ 47361) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2410973922 := by rw [factor_8_15]; decide
      have factor_8_17 : (43 : ZMod 4461857401) ^ 189447 = 3894318472 := by
        calc
          (43 : ZMod 4461857401) ^ 189447 = (43 : ZMod 4461857401) ^ (94723 + 94723 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 94723 * (43 : ZMod 4461857401) ^ 94723) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 3894318472 := by rw [factor_8_16]; decide
      have factor_8_18 : (43 : ZMod 4461857401) ^ 378894 = 3150623677 := by
        calc
          (43 : ZMod 4461857401) ^ 378894 = (43 : ZMod 4461857401) ^ (189447 + 189447) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 189447 * (43 : ZMod 4461857401) ^ 189447 := by rw [pow_add]
          _ = 3150623677 := by rw [factor_8_17]; decide
      have factor_8_19 : (43 : ZMod 4461857401) ^ 757788 = 3467324385 := by
        calc
          (43 : ZMod 4461857401) ^ 757788 = (43 : ZMod 4461857401) ^ (378894 + 378894) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 378894 * (43 : ZMod 4461857401) ^ 378894 := by rw [pow_add]
          _ = 3467324385 := by rw [factor_8_18]; decide
      have factor_8_20 : (43 : ZMod 4461857401) ^ 1515576 = 492589790 := by
        calc
          (43 : ZMod 4461857401) ^ 1515576 = (43 : ZMod 4461857401) ^ (757788 + 757788) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 757788 * (43 : ZMod 4461857401) ^ 757788 := by rw [pow_add]
          _ = 492589790 := by rw [factor_8_19]; decide
      have factor_8_21 : (43 : ZMod 4461857401) ^ 3031153 = 2037168570 := by
        calc
          (43 : ZMod 4461857401) ^ 3031153 = (43 : ZMod 4461857401) ^ (1515576 + 1515576 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 1515576 * (43 : ZMod 4461857401) ^ 1515576) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 2037168570 := by rw [factor_8_20]; decide
      have factor_8_22 : (43 : ZMod 4461857401) ^ 6062306 = 4203131475 := by
        calc
          (43 : ZMod 4461857401) ^ 6062306 = (43 : ZMod 4461857401) ^ (3031153 + 3031153) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 3031153 * (43 : ZMod 4461857401) ^ 3031153 := by rw [pow_add]
          _ = 4203131475 := by rw [factor_8_21]; decide
      have factor_8_23 : (43 : ZMod 4461857401) ^ 12124612 = 4350764357 := by
        calc
          (43 : ZMod 4461857401) ^ 12124612 = (43 : ZMod 4461857401) ^ (6062306 + 6062306) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 6062306 * (43 : ZMod 4461857401) ^ 6062306 := by rw [pow_add]
          _ = 4350764357 := by rw [factor_8_22]; decide
      have factor_8_24 : (43 : ZMod 4461857401) ^ 24249225 = 56156440 := by
        calc
          (43 : ZMod 4461857401) ^ 24249225 = (43 : ZMod 4461857401) ^ (12124612 + 12124612 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = ((43 : ZMod 4461857401) ^ 12124612 * (43 : ZMod 4461857401) ^ 12124612) * (43 : ZMod 4461857401) := by rw [pow_succ, pow_add]
          _ = 56156440 := by rw [factor_8_23]; decide
      have factor_8_25 : (43 : ZMod 4461857401) ^ 48498450 = 3103309622 := by
        calc
          (43 : ZMod 4461857401) ^ 48498450 = (43 : ZMod 4461857401) ^ (24249225 + 24249225) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 24249225 * (43 : ZMod 4461857401) ^ 24249225 := by rw [pow_add]
          _ = 3103309622 := by rw [factor_8_24]; decide
      have factor_8_26 : (43 : ZMod 4461857401) ^ 96996900 = 2024050776 := by
        calc
          (43 : ZMod 4461857401) ^ 96996900 = (43 : ZMod 4461857401) ^ (48498450 + 48498450) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 48498450 * (43 : ZMod 4461857401) ^ 48498450 := by rw [pow_add]
          _ = 2024050776 := by rw [factor_8_25]; decide
      have factor_8_27 : (43 : ZMod 4461857401) ^ 193993800 = 3700266275 := by
        calc
          (43 : ZMod 4461857401) ^ 193993800 = (43 : ZMod 4461857401) ^ (96996900 + 96996900) :=
            congrArg (fun n : ℕ => (43 : ZMod 4461857401) ^ n) (by norm_num)
          _ = (43 : ZMod 4461857401) ^ 96996900 * (43 : ZMod 4461857401) ^ 96996900 := by rw [pow_add]
          _ = 3700266275 := by rw [factor_8_26]; decide
      change (43 : ZMod 4461857401) ^ 193993800 ≠ 1
      rw [factor_8_27]
      decide

#print axioms prime_lucas_4461857401

end TotientTailPeriodKiller
end Erdos249257
