import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_7996526947 : Nat.Prime 7996526947 := by
  apply lucas_primality 7996526947 (2 : ZMod 7996526947)
  ·
      have fermat_0 : (2 : ZMod 7996526947) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 7996526947) ^ 3 = 8 := by
        calc
          (2 : ZMod 7996526947) ^ 3 = (2 : ZMod 7996526947) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 1 * (2 : ZMod 7996526947) ^ 1) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 7996526947) ^ 7 = 128 := by
        calc
          (2 : ZMod 7996526947) ^ 7 = (2 : ZMod 7996526947) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 3 * (2 : ZMod 7996526947) ^ 3) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 7996526947) ^ 14 = 16384 := by
        calc
          (2 : ZMod 7996526947) ^ 14 = (2 : ZMod 7996526947) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 7 * (2 : ZMod 7996526947) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 7996526947) ^ 29 = 536870912 := by
        calc
          (2 : ZMod 7996526947) ^ 29 = (2 : ZMod 7996526947) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 14 * (2 : ZMod 7996526947) ^ 14) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 536870912 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 7996526947) ^ 59 = 839104658 := by
        calc
          (2 : ZMod 7996526947) ^ 59 = (2 : ZMod 7996526947) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 29 * (2 : ZMod 7996526947) ^ 29) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 839104658 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 7996526947) ^ 119 = 4896037099 := by
        calc
          (2 : ZMod 7996526947) ^ 119 = (2 : ZMod 7996526947) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 59 * (2 : ZMod 7996526947) ^ 59) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 4896037099 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 7996526947) ^ 238 = 1612137466 := by
        calc
          (2 : ZMod 7996526947) ^ 238 = (2 : ZMod 7996526947) ^ (119 + 119) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 119 * (2 : ZMod 7996526947) ^ 119 := by rw [pow_add]
          _ = 1612137466 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 7996526947) ^ 476 = 1865169656 := by
        calc
          (2 : ZMod 7996526947) ^ 476 = (2 : ZMod 7996526947) ^ (238 + 238) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 238 * (2 : ZMod 7996526947) ^ 238 := by rw [pow_add]
          _ = 1865169656 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 7996526947) ^ 953 = 7634438007 := by
        calc
          (2 : ZMod 7996526947) ^ 953 = (2 : ZMod 7996526947) ^ (476 + 476 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 476 * (2 : ZMod 7996526947) ^ 476) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 7634438007 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 7996526947) ^ 1906 = 7490784951 := by
        calc
          (2 : ZMod 7996526947) ^ 1906 = (2 : ZMod 7996526947) ^ (953 + 953) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 953 * (2 : ZMod 7996526947) ^ 953 := by rw [pow_add]
          _ = 7490784951 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 7996526947) ^ 3813 = 5491267221 := by
        calc
          (2 : ZMod 7996526947) ^ 3813 = (2 : ZMod 7996526947) ^ (1906 + 1906 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 1906 * (2 : ZMod 7996526947) ^ 1906) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 5491267221 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 7996526947) ^ 7626 = 5863060060 := by
        calc
          (2 : ZMod 7996526947) ^ 7626 = (2 : ZMod 7996526947) ^ (3813 + 3813) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 3813 * (2 : ZMod 7996526947) ^ 3813 := by rw [pow_add]
          _ = 5863060060 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 7996526947) ^ 15252 = 4803243959 := by
        calc
          (2 : ZMod 7996526947) ^ 15252 = (2 : ZMod 7996526947) ^ (7626 + 7626) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 7626 * (2 : ZMod 7996526947) ^ 7626 := by rw [pow_add]
          _ = 4803243959 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 7996526947) ^ 30504 = 4721090428 := by
        calc
          (2 : ZMod 7996526947) ^ 30504 = (2 : ZMod 7996526947) ^ (15252 + 15252) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 15252 * (2 : ZMod 7996526947) ^ 15252 := by rw [pow_add]
          _ = 4721090428 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 7996526947) ^ 61008 = 3237970255 := by
        calc
          (2 : ZMod 7996526947) ^ 61008 = (2 : ZMod 7996526947) ^ (30504 + 30504) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 30504 * (2 : ZMod 7996526947) ^ 30504 := by rw [pow_add]
          _ = 3237970255 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 7996526947) ^ 122017 = 2082731035 := by
        calc
          (2 : ZMod 7996526947) ^ 122017 = (2 : ZMod 7996526947) ^ (61008 + 61008 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 61008 * (2 : ZMod 7996526947) ^ 61008) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 2082731035 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 7996526947) ^ 244034 = 563033329 := by
        calc
          (2 : ZMod 7996526947) ^ 244034 = (2 : ZMod 7996526947) ^ (122017 + 122017) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 122017 * (2 : ZMod 7996526947) ^ 122017 := by rw [pow_add]
          _ = 563033329 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 7996526947) ^ 488069 = 7790401238 := by
        calc
          (2 : ZMod 7996526947) ^ 488069 = (2 : ZMod 7996526947) ^ (244034 + 244034 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 244034 * (2 : ZMod 7996526947) ^ 244034) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 7790401238 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 7996526947) ^ 976138 = 5220742627 := by
        calc
          (2 : ZMod 7996526947) ^ 976138 = (2 : ZMod 7996526947) ^ (488069 + 488069) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 488069 * (2 : ZMod 7996526947) ^ 488069 := by rw [pow_add]
          _ = 5220742627 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 7996526947) ^ 1952277 = 5646173262 := by
        calc
          (2 : ZMod 7996526947) ^ 1952277 = (2 : ZMod 7996526947) ^ (976138 + 976138 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 976138 * (2 : ZMod 7996526947) ^ 976138) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 5646173262 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 7996526947) ^ 3904554 = 3802826461 := by
        calc
          (2 : ZMod 7996526947) ^ 3904554 = (2 : ZMod 7996526947) ^ (1952277 + 1952277) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 1952277 * (2 : ZMod 7996526947) ^ 1952277 := by rw [pow_add]
          _ = 3802826461 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 7996526947) ^ 7809108 = 985483824 := by
        calc
          (2 : ZMod 7996526947) ^ 7809108 = (2 : ZMod 7996526947) ^ (3904554 + 3904554) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 3904554 * (2 : ZMod 7996526947) ^ 3904554 := by rw [pow_add]
          _ = 985483824 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 7996526947) ^ 15618216 = 1725447089 := by
        calc
          (2 : ZMod 7996526947) ^ 15618216 = (2 : ZMod 7996526947) ^ (7809108 + 7809108) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 7809108 * (2 : ZMod 7996526947) ^ 7809108 := by rw [pow_add]
          _ = 1725447089 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 7996526947) ^ 31236433 = 1844527117 := by
        calc
          (2 : ZMod 7996526947) ^ 31236433 = (2 : ZMod 7996526947) ^ (15618216 + 15618216 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 15618216 * (2 : ZMod 7996526947) ^ 15618216) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 1844527117 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 7996526947) ^ 62472866 = 4322613174 := by
        calc
          (2 : ZMod 7996526947) ^ 62472866 = (2 : ZMod 7996526947) ^ (31236433 + 31236433) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 31236433 * (2 : ZMod 7996526947) ^ 31236433 := by rw [pow_add]
          _ = 4322613174 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 7996526947) ^ 124945733 = 3762349439 := by
        calc
          (2 : ZMod 7996526947) ^ 124945733 = (2 : ZMod 7996526947) ^ (62472866 + 62472866 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 62472866 * (2 : ZMod 7996526947) ^ 62472866) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 3762349439 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 7996526947) ^ 249891467 = 3900325607 := by
        calc
          (2 : ZMod 7996526947) ^ 249891467 = (2 : ZMod 7996526947) ^ (124945733 + 124945733 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 124945733 * (2 : ZMod 7996526947) ^ 124945733) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 3900325607 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 7996526947) ^ 499782934 = 1617304006 := by
        calc
          (2 : ZMod 7996526947) ^ 499782934 = (2 : ZMod 7996526947) ^ (249891467 + 249891467) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 249891467 * (2 : ZMod 7996526947) ^ 249891467 := by rw [pow_add]
          _ = 1617304006 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 7996526947) ^ 999565868 = 7054557891 := by
        calc
          (2 : ZMod 7996526947) ^ 999565868 = (2 : ZMod 7996526947) ^ (499782934 + 499782934) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 499782934 * (2 : ZMod 7996526947) ^ 499782934 := by rw [pow_add]
          _ = 7054557891 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 7996526947) ^ 1999131736 = 5229116488 := by
        calc
          (2 : ZMod 7996526947) ^ 1999131736 = (2 : ZMod 7996526947) ^ (999565868 + 999565868) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 999565868 * (2 : ZMod 7996526947) ^ 999565868 := by rw [pow_add]
          _ = 5229116488 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 7996526947) ^ 3998263473 = 7996526946 := by
        calc
          (2 : ZMod 7996526947) ^ 3998263473 = (2 : ZMod 7996526947) ^ (1999131736 + 1999131736 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 1999131736 * (2 : ZMod 7996526947) ^ 1999131736) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 7996526946 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 7996526947) ^ 7996526946 = 1 := by
        calc
          (2 : ZMod 7996526947) ^ 7996526946 = (2 : ZMod 7996526947) ^ (3998263473 + 3998263473) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 3998263473 * (2 : ZMod 7996526947) ^ 3998263473 := by rw [pow_add]
          _ = 1 := by rw [fermat_31]; decide
      simpa using fermat_32
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (17, 1), (4129, 1), (6329, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (17, 1), (4129, 1), (6329, 1)] : List FactorBlock).map factorBlockValue).prod = 7996526947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 7996526947) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 7996526947) ^ 3 = 8 := by
        calc
          (2 : ZMod 7996526947) ^ 3 = (2 : ZMod 7996526947) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 1 * (2 : ZMod 7996526947) ^ 1) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 7996526947) ^ 7 = 128 := by
        calc
          (2 : ZMod 7996526947) ^ 7 = (2 : ZMod 7996526947) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 3 * (2 : ZMod 7996526947) ^ 3) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 7996526947) ^ 14 = 16384 := by
        calc
          (2 : ZMod 7996526947) ^ 14 = (2 : ZMod 7996526947) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 7 * (2 : ZMod 7996526947) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 7996526947) ^ 29 = 536870912 := by
        calc
          (2 : ZMod 7996526947) ^ 29 = (2 : ZMod 7996526947) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 14 * (2 : ZMod 7996526947) ^ 14) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 536870912 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 7996526947) ^ 59 = 839104658 := by
        calc
          (2 : ZMod 7996526947) ^ 59 = (2 : ZMod 7996526947) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 29 * (2 : ZMod 7996526947) ^ 29) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 839104658 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 7996526947) ^ 119 = 4896037099 := by
        calc
          (2 : ZMod 7996526947) ^ 119 = (2 : ZMod 7996526947) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 59 * (2 : ZMod 7996526947) ^ 59) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 4896037099 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 7996526947) ^ 238 = 1612137466 := by
        calc
          (2 : ZMod 7996526947) ^ 238 = (2 : ZMod 7996526947) ^ (119 + 119) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 119 * (2 : ZMod 7996526947) ^ 119 := by rw [pow_add]
          _ = 1612137466 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 7996526947) ^ 476 = 1865169656 := by
        calc
          (2 : ZMod 7996526947) ^ 476 = (2 : ZMod 7996526947) ^ (238 + 238) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 238 * (2 : ZMod 7996526947) ^ 238 := by rw [pow_add]
          _ = 1865169656 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 7996526947) ^ 953 = 7634438007 := by
        calc
          (2 : ZMod 7996526947) ^ 953 = (2 : ZMod 7996526947) ^ (476 + 476 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 476 * (2 : ZMod 7996526947) ^ 476) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 7634438007 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 7996526947) ^ 1906 = 7490784951 := by
        calc
          (2 : ZMod 7996526947) ^ 1906 = (2 : ZMod 7996526947) ^ (953 + 953) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 953 * (2 : ZMod 7996526947) ^ 953 := by rw [pow_add]
          _ = 7490784951 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 7996526947) ^ 3813 = 5491267221 := by
        calc
          (2 : ZMod 7996526947) ^ 3813 = (2 : ZMod 7996526947) ^ (1906 + 1906 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 1906 * (2 : ZMod 7996526947) ^ 1906) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 5491267221 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 7996526947) ^ 7626 = 5863060060 := by
        calc
          (2 : ZMod 7996526947) ^ 7626 = (2 : ZMod 7996526947) ^ (3813 + 3813) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 3813 * (2 : ZMod 7996526947) ^ 3813 := by rw [pow_add]
          _ = 5863060060 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 7996526947) ^ 15252 = 4803243959 := by
        calc
          (2 : ZMod 7996526947) ^ 15252 = (2 : ZMod 7996526947) ^ (7626 + 7626) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 7626 * (2 : ZMod 7996526947) ^ 7626 := by rw [pow_add]
          _ = 4803243959 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 7996526947) ^ 30504 = 4721090428 := by
        calc
          (2 : ZMod 7996526947) ^ 30504 = (2 : ZMod 7996526947) ^ (15252 + 15252) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 15252 * (2 : ZMod 7996526947) ^ 15252 := by rw [pow_add]
          _ = 4721090428 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 7996526947) ^ 61008 = 3237970255 := by
        calc
          (2 : ZMod 7996526947) ^ 61008 = (2 : ZMod 7996526947) ^ (30504 + 30504) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 30504 * (2 : ZMod 7996526947) ^ 30504 := by rw [pow_add]
          _ = 3237970255 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 7996526947) ^ 122017 = 2082731035 := by
        calc
          (2 : ZMod 7996526947) ^ 122017 = (2 : ZMod 7996526947) ^ (61008 + 61008 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 61008 * (2 : ZMod 7996526947) ^ 61008) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 2082731035 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 7996526947) ^ 244034 = 563033329 := by
        calc
          (2 : ZMod 7996526947) ^ 244034 = (2 : ZMod 7996526947) ^ (122017 + 122017) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 122017 * (2 : ZMod 7996526947) ^ 122017 := by rw [pow_add]
          _ = 563033329 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 7996526947) ^ 488069 = 7790401238 := by
        calc
          (2 : ZMod 7996526947) ^ 488069 = (2 : ZMod 7996526947) ^ (244034 + 244034 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 244034 * (2 : ZMod 7996526947) ^ 244034) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 7790401238 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 7996526947) ^ 976138 = 5220742627 := by
        calc
          (2 : ZMod 7996526947) ^ 976138 = (2 : ZMod 7996526947) ^ (488069 + 488069) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 488069 * (2 : ZMod 7996526947) ^ 488069 := by rw [pow_add]
          _ = 5220742627 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 7996526947) ^ 1952277 = 5646173262 := by
        calc
          (2 : ZMod 7996526947) ^ 1952277 = (2 : ZMod 7996526947) ^ (976138 + 976138 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 976138 * (2 : ZMod 7996526947) ^ 976138) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 5646173262 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 7996526947) ^ 3904554 = 3802826461 := by
        calc
          (2 : ZMod 7996526947) ^ 3904554 = (2 : ZMod 7996526947) ^ (1952277 + 1952277) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 1952277 * (2 : ZMod 7996526947) ^ 1952277 := by rw [pow_add]
          _ = 3802826461 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 7996526947) ^ 7809108 = 985483824 := by
        calc
          (2 : ZMod 7996526947) ^ 7809108 = (2 : ZMod 7996526947) ^ (3904554 + 3904554) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 3904554 * (2 : ZMod 7996526947) ^ 3904554 := by rw [pow_add]
          _ = 985483824 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 7996526947) ^ 15618216 = 1725447089 := by
        calc
          (2 : ZMod 7996526947) ^ 15618216 = (2 : ZMod 7996526947) ^ (7809108 + 7809108) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 7809108 * (2 : ZMod 7996526947) ^ 7809108 := by rw [pow_add]
          _ = 1725447089 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 7996526947) ^ 31236433 = 1844527117 := by
        calc
          (2 : ZMod 7996526947) ^ 31236433 = (2 : ZMod 7996526947) ^ (15618216 + 15618216 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 15618216 * (2 : ZMod 7996526947) ^ 15618216) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 1844527117 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 7996526947) ^ 62472866 = 4322613174 := by
        calc
          (2 : ZMod 7996526947) ^ 62472866 = (2 : ZMod 7996526947) ^ (31236433 + 31236433) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 31236433 * (2 : ZMod 7996526947) ^ 31236433 := by rw [pow_add]
          _ = 4322613174 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 7996526947) ^ 124945733 = 3762349439 := by
        calc
          (2 : ZMod 7996526947) ^ 124945733 = (2 : ZMod 7996526947) ^ (62472866 + 62472866 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 62472866 * (2 : ZMod 7996526947) ^ 62472866) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 3762349439 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 7996526947) ^ 249891467 = 3900325607 := by
        calc
          (2 : ZMod 7996526947) ^ 249891467 = (2 : ZMod 7996526947) ^ (124945733 + 124945733 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 124945733 * (2 : ZMod 7996526947) ^ 124945733) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 3900325607 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 7996526947) ^ 499782934 = 1617304006 := by
        calc
          (2 : ZMod 7996526947) ^ 499782934 = (2 : ZMod 7996526947) ^ (249891467 + 249891467) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 249891467 * (2 : ZMod 7996526947) ^ 249891467 := by rw [pow_add]
          _ = 1617304006 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 7996526947) ^ 999565868 = 7054557891 := by
        calc
          (2 : ZMod 7996526947) ^ 999565868 = (2 : ZMod 7996526947) ^ (499782934 + 499782934) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 499782934 * (2 : ZMod 7996526947) ^ 499782934 := by rw [pow_add]
          _ = 7054557891 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 7996526947) ^ 1999131736 = 5229116488 := by
        calc
          (2 : ZMod 7996526947) ^ 1999131736 = (2 : ZMod 7996526947) ^ (999565868 + 999565868) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 999565868 * (2 : ZMod 7996526947) ^ 999565868 := by rw [pow_add]
          _ = 5229116488 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 7996526947) ^ 3998263473 = 7996526946 := by
        calc
          (2 : ZMod 7996526947) ^ 3998263473 = (2 : ZMod 7996526947) ^ (1999131736 + 1999131736 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 1999131736 * (2 : ZMod 7996526947) ^ 1999131736) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 7996526946 := by rw [factor_0_30]; decide
      change (2 : ZMod 7996526947) ^ 3998263473 ≠ 1
      rw [factor_0_31]
      decide
    ·
      have factor_1_0 : (2 : ZMod 7996526947) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 7996526947) ^ 2 = 4 := by
        calc
          (2 : ZMod 7996526947) ^ 2 = (2 : ZMod 7996526947) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 1 * (2 : ZMod 7996526947) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 7996526947) ^ 4 = 16 := by
        calc
          (2 : ZMod 7996526947) ^ 4 = (2 : ZMod 7996526947) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 2 * (2 : ZMod 7996526947) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 7996526947) ^ 9 = 512 := by
        calc
          (2 : ZMod 7996526947) ^ 9 = (2 : ZMod 7996526947) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 4 * (2 : ZMod 7996526947) ^ 4) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 7996526947) ^ 19 = 524288 := by
        calc
          (2 : ZMod 7996526947) ^ 19 = (2 : ZMod 7996526947) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 9 * (2 : ZMod 7996526947) ^ 9) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 7996526947) ^ 39 = 5991981492 := by
        calc
          (2 : ZMod 7996526947) ^ 39 = (2 : ZMod 7996526947) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 19 * (2 : ZMod 7996526947) ^ 19) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 5991981492 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 7996526947) ^ 79 = 7145888598 := by
        calc
          (2 : ZMod 7996526947) ^ 79 = (2 : ZMod 7996526947) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 39 * (2 : ZMod 7996526947) ^ 39) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 7145888598 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 7996526947) ^ 158 = 4613741400 := by
        calc
          (2 : ZMod 7996526947) ^ 158 = (2 : ZMod 7996526947) ^ (79 + 79) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 79 * (2 : ZMod 7996526947) ^ 79 := by rw [pow_add]
          _ = 4613741400 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 7996526947) ^ 317 = 4341868531 := by
        calc
          (2 : ZMod 7996526947) ^ 317 = (2 : ZMod 7996526947) ^ (158 + 158 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 158 * (2 : ZMod 7996526947) ^ 158) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 4341868531 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 7996526947) ^ 635 = 6609397270 := by
        calc
          (2 : ZMod 7996526947) ^ 635 = (2 : ZMod 7996526947) ^ (317 + 317 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 317 * (2 : ZMod 7996526947) ^ 317) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 6609397270 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 7996526947) ^ 1271 = 1498638329 := by
        calc
          (2 : ZMod 7996526947) ^ 1271 = (2 : ZMod 7996526947) ^ (635 + 635 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 635 * (2 : ZMod 7996526947) ^ 635) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 1498638329 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 7996526947) ^ 2542 = 148101649 := by
        calc
          (2 : ZMod 7996526947) ^ 2542 = (2 : ZMod 7996526947) ^ (1271 + 1271) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 1271 * (2 : ZMod 7996526947) ^ 1271 := by rw [pow_add]
          _ = 148101649 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 7996526947) ^ 5084 = 857664710 := by
        calc
          (2 : ZMod 7996526947) ^ 5084 = (2 : ZMod 7996526947) ^ (2542 + 2542) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 2542 * (2 : ZMod 7996526947) ^ 2542 := by rw [pow_add]
          _ = 857664710 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 7996526947) ^ 10168 = 3815993137 := by
        calc
          (2 : ZMod 7996526947) ^ 10168 = (2 : ZMod 7996526947) ^ (5084 + 5084) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 5084 * (2 : ZMod 7996526947) ^ 5084 := by rw [pow_add]
          _ = 3815993137 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 7996526947) ^ 20336 = 2758098458 := by
        calc
          (2 : ZMod 7996526947) ^ 20336 = (2 : ZMod 7996526947) ^ (10168 + 10168) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 10168 * (2 : ZMod 7996526947) ^ 10168 := by rw [pow_add]
          _ = 2758098458 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 7996526947) ^ 40672 = 126744798 := by
        calc
          (2 : ZMod 7996526947) ^ 40672 = (2 : ZMod 7996526947) ^ (20336 + 20336) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 20336 * (2 : ZMod 7996526947) ^ 20336 := by rw [pow_add]
          _ = 126744798 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 7996526947) ^ 81344 = 4843178610 := by
        calc
          (2 : ZMod 7996526947) ^ 81344 = (2 : ZMod 7996526947) ^ (40672 + 40672) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 40672 * (2 : ZMod 7996526947) ^ 40672 := by rw [pow_add]
          _ = 4843178610 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 7996526947) ^ 162689 = 6126359968 := by
        calc
          (2 : ZMod 7996526947) ^ 162689 = (2 : ZMod 7996526947) ^ (81344 + 81344 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 81344 * (2 : ZMod 7996526947) ^ 81344) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 6126359968 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 7996526947) ^ 325379 = 5627689211 := by
        calc
          (2 : ZMod 7996526947) ^ 325379 = (2 : ZMod 7996526947) ^ (162689 + 162689 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 162689 * (2 : ZMod 7996526947) ^ 162689) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 5627689211 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 7996526947) ^ 650759 = 720270412 := by
        calc
          (2 : ZMod 7996526947) ^ 650759 = (2 : ZMod 7996526947) ^ (325379 + 325379 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 325379 * (2 : ZMod 7996526947) ^ 325379) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 720270412 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 7996526947) ^ 1301518 = 3134226688 := by
        calc
          (2 : ZMod 7996526947) ^ 1301518 = (2 : ZMod 7996526947) ^ (650759 + 650759) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 650759 * (2 : ZMod 7996526947) ^ 650759 := by rw [pow_add]
          _ = 3134226688 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 7996526947) ^ 2603036 = 6577557975 := by
        calc
          (2 : ZMod 7996526947) ^ 2603036 = (2 : ZMod 7996526947) ^ (1301518 + 1301518) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 1301518 * (2 : ZMod 7996526947) ^ 1301518 := by rw [pow_add]
          _ = 6577557975 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 7996526947) ^ 5206072 = 3422705521 := by
        calc
          (2 : ZMod 7996526947) ^ 5206072 = (2 : ZMod 7996526947) ^ (2603036 + 2603036) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 2603036 * (2 : ZMod 7996526947) ^ 2603036 := by rw [pow_add]
          _ = 3422705521 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 7996526947) ^ 10412144 = 2608162755 := by
        calc
          (2 : ZMod 7996526947) ^ 10412144 = (2 : ZMod 7996526947) ^ (5206072 + 5206072) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 5206072 * (2 : ZMod 7996526947) ^ 5206072 := by rw [pow_add]
          _ = 2608162755 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 7996526947) ^ 20824288 = 1200855709 := by
        calc
          (2 : ZMod 7996526947) ^ 20824288 = (2 : ZMod 7996526947) ^ (10412144 + 10412144) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 10412144 * (2 : ZMod 7996526947) ^ 10412144 := by rw [pow_add]
          _ = 1200855709 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 7996526947) ^ 41648577 = 6347283220 := by
        calc
          (2 : ZMod 7996526947) ^ 41648577 = (2 : ZMod 7996526947) ^ (20824288 + 20824288 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 20824288 * (2 : ZMod 7996526947) ^ 20824288) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 6347283220 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 7996526947) ^ 83297155 = 92406526 := by
        calc
          (2 : ZMod 7996526947) ^ 83297155 = (2 : ZMod 7996526947) ^ (41648577 + 41648577 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 41648577 * (2 : ZMod 7996526947) ^ 41648577) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 92406526 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 7996526947) ^ 166594311 = 5382931756 := by
        calc
          (2 : ZMod 7996526947) ^ 166594311 = (2 : ZMod 7996526947) ^ (83297155 + 83297155 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 83297155 * (2 : ZMod 7996526947) ^ 83297155) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 5382931756 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 7996526947) ^ 333188622 = 3351258259 := by
        calc
          (2 : ZMod 7996526947) ^ 333188622 = (2 : ZMod 7996526947) ^ (166594311 + 166594311) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 166594311 * (2 : ZMod 7996526947) ^ 166594311 := by rw [pow_add]
          _ = 3351258259 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 7996526947) ^ 666377245 = 5709183164 := by
        calc
          (2 : ZMod 7996526947) ^ 666377245 = (2 : ZMod 7996526947) ^ (333188622 + 333188622 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 333188622 * (2 : ZMod 7996526947) ^ 333188622) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 5709183164 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 7996526947) ^ 1332754491 = 6843403565 := by
        calc
          (2 : ZMod 7996526947) ^ 1332754491 = (2 : ZMod 7996526947) ^ (666377245 + 666377245 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 666377245 * (2 : ZMod 7996526947) ^ 666377245) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 6843403565 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 7996526947) ^ 2665508982 = 6843403564 := by
        calc
          (2 : ZMod 7996526947) ^ 2665508982 = (2 : ZMod 7996526947) ^ (1332754491 + 1332754491) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 1332754491 * (2 : ZMod 7996526947) ^ 1332754491 := by rw [pow_add]
          _ = 6843403564 := by rw [factor_1_30]; decide
      change (2 : ZMod 7996526947) ^ 2665508982 ≠ 1
      rw [factor_1_31]
      decide
    ·
      have factor_2_0 : (2 : ZMod 7996526947) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 7996526947) ^ 3 = 8 := by
        calc
          (2 : ZMod 7996526947) ^ 3 = (2 : ZMod 7996526947) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 1 * (2 : ZMod 7996526947) ^ 1) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 7996526947) ^ 7 = 128 := by
        calc
          (2 : ZMod 7996526947) ^ 7 = (2 : ZMod 7996526947) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 3 * (2 : ZMod 7996526947) ^ 3) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 7996526947) ^ 14 = 16384 := by
        calc
          (2 : ZMod 7996526947) ^ 14 = (2 : ZMod 7996526947) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 7 * (2 : ZMod 7996526947) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 7996526947) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 7996526947) ^ 28 = (2 : ZMod 7996526947) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 14 * (2 : ZMod 7996526947) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 7996526947) ^ 56 = 2104019819 := by
        calc
          (2 : ZMod 7996526947) ^ 56 = (2 : ZMod 7996526947) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 28 * (2 : ZMod 7996526947) ^ 28 := by rw [pow_add]
          _ = 2104019819 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 7996526947) ^ 112 = 2474692094 := by
        calc
          (2 : ZMod 7996526947) ^ 112 = (2 : ZMod 7996526947) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 56 * (2 : ZMod 7996526947) ^ 56 := by rw [pow_add]
          _ = 2474692094 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 7996526947) ^ 224 = 4717775977 := by
        calc
          (2 : ZMod 7996526947) ^ 224 = (2 : ZMod 7996526947) ^ (112 + 112) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 112 * (2 : ZMod 7996526947) ^ 112 := by rw [pow_add]
          _ = 4717775977 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 7996526947) ^ 448 = 3483787707 := by
        calc
          (2 : ZMod 7996526947) ^ 448 = (2 : ZMod 7996526947) ^ (224 + 224) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 224 * (2 : ZMod 7996526947) ^ 224 := by rw [pow_add]
          _ = 3483787707 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 7996526947) ^ 897 = 4974556122 := by
        calc
          (2 : ZMod 7996526947) ^ 897 = (2 : ZMod 7996526947) ^ (448 + 448 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 448 * (2 : ZMod 7996526947) ^ 448) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 4974556122 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 7996526947) ^ 1794 = 4632718928 := by
        calc
          (2 : ZMod 7996526947) ^ 1794 = (2 : ZMod 7996526947) ^ (897 + 897) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 897 * (2 : ZMod 7996526947) ^ 897 := by rw [pow_add]
          _ = 4632718928 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 7996526947) ^ 3588 = 2262014464 := by
        calc
          (2 : ZMod 7996526947) ^ 3588 = (2 : ZMod 7996526947) ^ (1794 + 1794) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 1794 * (2 : ZMod 7996526947) ^ 1794 := by rw [pow_add]
          _ = 2262014464 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 7996526947) ^ 7177 = 2985622935 := by
        calc
          (2 : ZMod 7996526947) ^ 7177 = (2 : ZMod 7996526947) ^ (3588 + 3588 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 3588 * (2 : ZMod 7996526947) ^ 3588) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 2985622935 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 7996526947) ^ 14354 = 7866191953 := by
        calc
          (2 : ZMod 7996526947) ^ 14354 = (2 : ZMod 7996526947) ^ (7177 + 7177) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 7177 * (2 : ZMod 7996526947) ^ 7177 := by rw [pow_add]
          _ = 7866191953 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 7996526947) ^ 28709 = 1098169363 := by
        calc
          (2 : ZMod 7996526947) ^ 28709 = (2 : ZMod 7996526947) ^ (14354 + 14354 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 14354 * (2 : ZMod 7996526947) ^ 14354) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 1098169363 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 7996526947) ^ 57419 = 3038608934 := by
        calc
          (2 : ZMod 7996526947) ^ 57419 = (2 : ZMod 7996526947) ^ (28709 + 28709 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 28709 * (2 : ZMod 7996526947) ^ 28709) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 3038608934 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 7996526947) ^ 114839 = 5262382406 := by
        calc
          (2 : ZMod 7996526947) ^ 114839 = (2 : ZMod 7996526947) ^ (57419 + 57419 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 57419 * (2 : ZMod 7996526947) ^ 57419) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 5262382406 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 7996526947) ^ 229679 = 7404961573 := by
        calc
          (2 : ZMod 7996526947) ^ 229679 = (2 : ZMod 7996526947) ^ (114839 + 114839 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 114839 * (2 : ZMod 7996526947) ^ 114839) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 7404961573 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 7996526947) ^ 459359 = 3767200687 := by
        calc
          (2 : ZMod 7996526947) ^ 459359 = (2 : ZMod 7996526947) ^ (229679 + 229679 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 229679 * (2 : ZMod 7996526947) ^ 229679) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 3767200687 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 7996526947) ^ 918718 = 1663588769 := by
        calc
          (2 : ZMod 7996526947) ^ 918718 = (2 : ZMod 7996526947) ^ (459359 + 459359) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 459359 * (2 : ZMod 7996526947) ^ 459359 := by rw [pow_add]
          _ = 1663588769 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 7996526947) ^ 1837437 = 2832845710 := by
        calc
          (2 : ZMod 7996526947) ^ 1837437 = (2 : ZMod 7996526947) ^ (918718 + 918718 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 918718 * (2 : ZMod 7996526947) ^ 918718) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 2832845710 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 7996526947) ^ 3674874 = 2520908190 := by
        calc
          (2 : ZMod 7996526947) ^ 3674874 = (2 : ZMod 7996526947) ^ (1837437 + 1837437) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 1837437 * (2 : ZMod 7996526947) ^ 1837437 := by rw [pow_add]
          _ = 2520908190 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 7996526947) ^ 7349749 = 3246860297 := by
        calc
          (2 : ZMod 7996526947) ^ 7349749 = (2 : ZMod 7996526947) ^ (3674874 + 3674874 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 3674874 * (2 : ZMod 7996526947) ^ 3674874) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 3246860297 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 7996526947) ^ 14699498 = 3749228071 := by
        calc
          (2 : ZMod 7996526947) ^ 14699498 = (2 : ZMod 7996526947) ^ (7349749 + 7349749) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 7349749 * (2 : ZMod 7996526947) ^ 7349749 := by rw [pow_add]
          _ = 3749228071 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 7996526947) ^ 29398996 = 1640728631 := by
        calc
          (2 : ZMod 7996526947) ^ 29398996 = (2 : ZMod 7996526947) ^ (14699498 + 14699498) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 14699498 * (2 : ZMod 7996526947) ^ 14699498 := by rw [pow_add]
          _ = 1640728631 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 7996526947) ^ 58797992 = 2347085670 := by
        calc
          (2 : ZMod 7996526947) ^ 58797992 = (2 : ZMod 7996526947) ^ (29398996 + 29398996) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 29398996 * (2 : ZMod 7996526947) ^ 29398996 := by rw [pow_add]
          _ = 2347085670 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 7996526947) ^ 117595984 = 2149491598 := by
        calc
          (2 : ZMod 7996526947) ^ 117595984 = (2 : ZMod 7996526947) ^ (58797992 + 58797992) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 58797992 * (2 : ZMod 7996526947) ^ 58797992 := by rw [pow_add]
          _ = 2149491598 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 7996526947) ^ 235191969 = 3046376126 := by
        calc
          (2 : ZMod 7996526947) ^ 235191969 = (2 : ZMod 7996526947) ^ (117595984 + 117595984 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 117595984 * (2 : ZMod 7996526947) ^ 117595984) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 3046376126 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 7996526947) ^ 470383938 = 1291853739 := by
        calc
          (2 : ZMod 7996526947) ^ 470383938 = (2 : ZMod 7996526947) ^ (235191969 + 235191969) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 235191969 * (2 : ZMod 7996526947) ^ 235191969 := by rw [pow_add]
          _ = 1291853739 := by rw [factor_2_27]; decide
      change (2 : ZMod 7996526947) ^ 470383938 ≠ 1
      rw [factor_2_28]
      decide
    ·
      have factor_3_0 : (2 : ZMod 7996526947) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 7996526947) ^ 3 = 8 := by
        calc
          (2 : ZMod 7996526947) ^ 3 = (2 : ZMod 7996526947) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 1 * (2 : ZMod 7996526947) ^ 1) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 7996526947) ^ 7 = 128 := by
        calc
          (2 : ZMod 7996526947) ^ 7 = (2 : ZMod 7996526947) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 3 * (2 : ZMod 7996526947) ^ 3) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 7996526947) ^ 14 = 16384 := by
        calc
          (2 : ZMod 7996526947) ^ 14 = (2 : ZMod 7996526947) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 7 * (2 : ZMod 7996526947) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 7996526947) ^ 29 = 536870912 := by
        calc
          (2 : ZMod 7996526947) ^ 29 = (2 : ZMod 7996526947) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 14 * (2 : ZMod 7996526947) ^ 14) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 536870912 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 7996526947) ^ 59 = 839104658 := by
        calc
          (2 : ZMod 7996526947) ^ 59 = (2 : ZMod 7996526947) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 29 * (2 : ZMod 7996526947) ^ 29) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 839104658 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 7996526947) ^ 118 = 6446282023 := by
        calc
          (2 : ZMod 7996526947) ^ 118 = (2 : ZMod 7996526947) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 59 * (2 : ZMod 7996526947) ^ 59 := by rw [pow_add]
          _ = 6446282023 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 7996526947) ^ 236 = 4401297840 := by
        calc
          (2 : ZMod 7996526947) ^ 236 = (2 : ZMod 7996526947) ^ (118 + 118) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 118 * (2 : ZMod 7996526947) ^ 118 := by rw [pow_add]
          _ = 4401297840 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 7996526947) ^ 472 = 4114836577 := by
        calc
          (2 : ZMod 7996526947) ^ 472 = (2 : ZMod 7996526947) ^ (236 + 236) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 236 * (2 : ZMod 7996526947) ^ 236 := by rw [pow_add]
          _ = 4114836577 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 7996526947) ^ 945 = 1123097192 := by
        calc
          (2 : ZMod 7996526947) ^ 945 = (2 : ZMod 7996526947) ^ (472 + 472 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 472 * (2 : ZMod 7996526947) ^ 472) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 1123097192 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 7996526947) ^ 1891 = 6521566174 := by
        calc
          (2 : ZMod 7996526947) ^ 1891 = (2 : ZMod 7996526947) ^ (945 + 945 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 945 * (2 : ZMod 7996526947) ^ 945) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 6521566174 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 7996526947) ^ 3782 = 5463030233 := by
        calc
          (2 : ZMod 7996526947) ^ 3782 = (2 : ZMod 7996526947) ^ (1891 + 1891) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 1891 * (2 : ZMod 7996526947) ^ 1891 := by rw [pow_add]
          _ = 5463030233 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 7996526947) ^ 7565 = 3538093188 := by
        calc
          (2 : ZMod 7996526947) ^ 7565 = (2 : ZMod 7996526947) ^ (3782 + 3782 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 3782 * (2 : ZMod 7996526947) ^ 3782) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 3538093188 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 7996526947) ^ 15130 = 7857566593 := by
        calc
          (2 : ZMod 7996526947) ^ 15130 = (2 : ZMod 7996526947) ^ (7565 + 7565) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 7565 * (2 : ZMod 7996526947) ^ 7565 := by rw [pow_add]
          _ = 7857566593 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 7996526947) ^ 30260 = 6694824451 := by
        calc
          (2 : ZMod 7996526947) ^ 30260 = (2 : ZMod 7996526947) ^ (15130 + 15130) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 15130 * (2 : ZMod 7996526947) ^ 15130 := by rw [pow_add]
          _ = 6694824451 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 7996526947) ^ 60521 = 1928344416 := by
        calc
          (2 : ZMod 7996526947) ^ 60521 = (2 : ZMod 7996526947) ^ (30260 + 30260 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 30260 * (2 : ZMod 7996526947) ^ 30260) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 1928344416 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 7996526947) ^ 121042 = 3588396809 := by
        calc
          (2 : ZMod 7996526947) ^ 121042 = (2 : ZMod 7996526947) ^ (60521 + 60521) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 60521 * (2 : ZMod 7996526947) ^ 60521 := by rw [pow_add]
          _ = 3588396809 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 7996526947) ^ 242084 = 6408623912 := by
        calc
          (2 : ZMod 7996526947) ^ 242084 = (2 : ZMod 7996526947) ^ (121042 + 121042) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 121042 * (2 : ZMod 7996526947) ^ 121042 := by rw [pow_add]
          _ = 6408623912 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 7996526947) ^ 484168 = 7110342107 := by
        calc
          (2 : ZMod 7996526947) ^ 484168 = (2 : ZMod 7996526947) ^ (242084 + 242084) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 242084 * (2 : ZMod 7996526947) ^ 242084 := by rw [pow_add]
          _ = 7110342107 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 7996526947) ^ 968337 = 1035806839 := by
        calc
          (2 : ZMod 7996526947) ^ 968337 = (2 : ZMod 7996526947) ^ (484168 + 484168 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 484168 * (2 : ZMod 7996526947) ^ 484168) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 1035806839 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 7996526947) ^ 1936674 = 4014672740 := by
        calc
          (2 : ZMod 7996526947) ^ 1936674 = (2 : ZMod 7996526947) ^ (968337 + 968337) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 968337 * (2 : ZMod 7996526947) ^ 968337 := by rw [pow_add]
          _ = 4014672740 := by rw [factor_3_19]; decide
      change (2 : ZMod 7996526947) ^ 1936674 ≠ 1
      rw [factor_3_20]
      decide
    ·
      have factor_4_0 : (2 : ZMod 7996526947) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 7996526947) ^ 2 = 4 := by
        calc
          (2 : ZMod 7996526947) ^ 2 = (2 : ZMod 7996526947) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 1 * (2 : ZMod 7996526947) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 7996526947) ^ 4 = 16 := by
        calc
          (2 : ZMod 7996526947) ^ 4 = (2 : ZMod 7996526947) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 2 * (2 : ZMod 7996526947) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 7996526947) ^ 9 = 512 := by
        calc
          (2 : ZMod 7996526947) ^ 9 = (2 : ZMod 7996526947) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 4 * (2 : ZMod 7996526947) ^ 4) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 7996526947) ^ 19 = 524288 := by
        calc
          (2 : ZMod 7996526947) ^ 19 = (2 : ZMod 7996526947) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 9 * (2 : ZMod 7996526947) ^ 9) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 7996526947) ^ 38 = 2995990746 := by
        calc
          (2 : ZMod 7996526947) ^ 38 = (2 : ZMod 7996526947) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 19 * (2 : ZMod 7996526947) ^ 19 := by rw [pow_add]
          _ = 2995990746 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 7996526947) ^ 77 = 5784735623 := by
        calc
          (2 : ZMod 7996526947) ^ 77 = (2 : ZMod 7996526947) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 38 * (2 : ZMod 7996526947) ^ 38) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 5784735623 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 7996526947) ^ 154 = 4286622311 := by
        calc
          (2 : ZMod 7996526947) ^ 154 = (2 : ZMod 7996526947) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 77 * (2 : ZMod 7996526947) ^ 77 := by rw [pow_add]
          _ = 4286622311 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 7996526947) ^ 308 = 7239714541 := by
        calc
          (2 : ZMod 7996526947) ^ 308 = (2 : ZMod 7996526947) ^ (154 + 154) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 154 * (2 : ZMod 7996526947) ^ 154 := by rw [pow_add]
          _ = 7239714541 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 7996526947) ^ 616 = 5277231102 := by
        calc
          (2 : ZMod 7996526947) ^ 616 = (2 : ZMod 7996526947) ^ (308 + 308) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 308 * (2 : ZMod 7996526947) ^ 308 := by rw [pow_add]
          _ = 5277231102 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 7996526947) ^ 1233 = 7076507925 := by
        calc
          (2 : ZMod 7996526947) ^ 1233 = (2 : ZMod 7996526947) ^ (616 + 616 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 616 * (2 : ZMod 7996526947) ^ 616) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 7076507925 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 7996526947) ^ 2467 = 1282095736 := by
        calc
          (2 : ZMod 7996526947) ^ 2467 = (2 : ZMod 7996526947) ^ (1233 + 1233 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 1233 * (2 : ZMod 7996526947) ^ 1233) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 1282095736 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 7996526947) ^ 4935 = 5036745389 := by
        calc
          (2 : ZMod 7996526947) ^ 4935 = (2 : ZMod 7996526947) ^ (2467 + 2467 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 2467 * (2 : ZMod 7996526947) ^ 2467) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 5036745389 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 7996526947) ^ 9870 = 1108335032 := by
        calc
          (2 : ZMod 7996526947) ^ 9870 = (2 : ZMod 7996526947) ^ (4935 + 4935) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 4935 * (2 : ZMod 7996526947) ^ 4935 := by rw [pow_add]
          _ = 1108335032 := by rw [factor_4_12]; decide
      have factor_4_14 : (2 : ZMod 7996526947) ^ 19741 = 1810905896 := by
        calc
          (2 : ZMod 7996526947) ^ 19741 = (2 : ZMod 7996526947) ^ (9870 + 9870 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 9870 * (2 : ZMod 7996526947) ^ 9870) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 1810905896 := by rw [factor_4_13]; decide
      have factor_4_15 : (2 : ZMod 7996526947) ^ 39483 = 2281652780 := by
        calc
          (2 : ZMod 7996526947) ^ 39483 = (2 : ZMod 7996526947) ^ (19741 + 19741 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 19741 * (2 : ZMod 7996526947) ^ 19741) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 2281652780 := by rw [factor_4_14]; decide
      have factor_4_16 : (2 : ZMod 7996526947) ^ 78967 = 2014561789 := by
        calc
          (2 : ZMod 7996526947) ^ 78967 = (2 : ZMod 7996526947) ^ (39483 + 39483 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 39483 * (2 : ZMod 7996526947) ^ 39483) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 2014561789 := by rw [factor_4_15]; decide
      have factor_4_17 : (2 : ZMod 7996526947) ^ 157934 = 418032423 := by
        calc
          (2 : ZMod 7996526947) ^ 157934 = (2 : ZMod 7996526947) ^ (78967 + 78967) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 78967 * (2 : ZMod 7996526947) ^ 78967 := by rw [pow_add]
          _ = 418032423 := by rw [factor_4_16]; decide
      have factor_4_18 : (2 : ZMod 7996526947) ^ 315868 = 4608854804 := by
        calc
          (2 : ZMod 7996526947) ^ 315868 = (2 : ZMod 7996526947) ^ (157934 + 157934) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 157934 * (2 : ZMod 7996526947) ^ 157934 := by rw [pow_add]
          _ = 4608854804 := by rw [factor_4_17]; decide
      have factor_4_19 : (2 : ZMod 7996526947) ^ 631737 = 5797869906 := by
        calc
          (2 : ZMod 7996526947) ^ 631737 = (2 : ZMod 7996526947) ^ (315868 + 315868 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = ((2 : ZMod 7996526947) ^ 315868 * (2 : ZMod 7996526947) ^ 315868) * (2 : ZMod 7996526947) := by rw [pow_succ, pow_add]
          _ = 5797869906 := by rw [factor_4_18]; decide
      have factor_4_20 : (2 : ZMod 7996526947) ^ 1263474 = 7969569801 := by
        calc
          (2 : ZMod 7996526947) ^ 1263474 = (2 : ZMod 7996526947) ^ (631737 + 631737) :=
            congrArg (fun n : ℕ => (2 : ZMod 7996526947) ^ n) (by norm_num)
          _ = (2 : ZMod 7996526947) ^ 631737 * (2 : ZMod 7996526947) ^ 631737 := by rw [pow_add]
          _ = 7969569801 := by rw [factor_4_19]; decide
      change (2 : ZMod 7996526947) ^ 1263474 ≠ 1
      rw [factor_4_20]
      decide

#print axioms prime_lucas_7996526947

end TotientTailPeriodKiller
end Erdos249257
