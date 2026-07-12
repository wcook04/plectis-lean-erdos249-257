import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_3580310791 : Nat.Prime 3580310791 := by
  apply lucas_primality 3580310791 (3 : ZMod 3580310791)
  ·
      have fermat_0 : (3 : ZMod 3580310791) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 3580310791) ^ 3 = 27 := by
        calc
          (3 : ZMod 3580310791) ^ 3 = (3 : ZMod 3580310791) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 1 * (3 : ZMod 3580310791) ^ 1) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 3580310791) ^ 6 = 729 := by
        calc
          (3 : ZMod 3580310791) ^ 6 = (3 : ZMod 3580310791) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 3 * (3 : ZMod 3580310791) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 3580310791) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 3580310791) ^ 13 = (3 : ZMod 3580310791) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 6 * (3 : ZMod 3580310791) ^ 6) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 3580310791) ^ 26 = 3425477510 := by
        calc
          (3 : ZMod 3580310791) ^ 26 = (3 : ZMod 3580310791) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 13 * (3 : ZMod 3580310791) ^ 13 := by rw [pow_add]
          _ = 3425477510 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 3580310791) ^ 53 = 1074532942 := by
        calc
          (3 : ZMod 3580310791) ^ 53 = (3 : ZMod 3580310791) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 26 * (3 : ZMod 3580310791) ^ 26) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1074532942 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 3580310791) ^ 106 = 39243596 := by
        calc
          (3 : ZMod 3580310791) ^ 106 = (3 : ZMod 3580310791) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 53 * (3 : ZMod 3580310791) ^ 53 := by rw [pow_add]
          _ = 39243596 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 3580310791) ^ 213 = 3223895608 := by
        calc
          (3 : ZMod 3580310791) ^ 213 = (3 : ZMod 3580310791) ^ (106 + 106 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 106 * (3 : ZMod 3580310791) ^ 106) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 3223895608 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 3580310791) ^ 426 = 3544053802 := by
        calc
          (3 : ZMod 3580310791) ^ 426 = (3 : ZMod 3580310791) ^ (213 + 213) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 213 * (3 : ZMod 3580310791) ^ 213 := by rw [pow_add]
          _ = 3544053802 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 3580310791) ^ 853 = 2578373445 := by
        calc
          (3 : ZMod 3580310791) ^ 853 = (3 : ZMod 3580310791) ^ (426 + 426 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 426 * (3 : ZMod 3580310791) ^ 426) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 2578373445 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 3580310791) ^ 1707 = 1458587412 := by
        calc
          (3 : ZMod 3580310791) ^ 1707 = (3 : ZMod 3580310791) ^ (853 + 853 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 853 * (3 : ZMod 3580310791) ^ 853) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1458587412 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 3580310791) ^ 3414 = 1102470735 := by
        calc
          (3 : ZMod 3580310791) ^ 3414 = (3 : ZMod 3580310791) ^ (1707 + 1707) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 1707 * (3 : ZMod 3580310791) ^ 1707 := by rw [pow_add]
          _ = 1102470735 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 3580310791) ^ 6828 = 1772653526 := by
        calc
          (3 : ZMod 3580310791) ^ 6828 = (3 : ZMod 3580310791) ^ (3414 + 3414) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 3414 * (3 : ZMod 3580310791) ^ 3414 := by rw [pow_add]
          _ = 1772653526 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 3580310791) ^ 13657 = 1363424587 := by
        calc
          (3 : ZMod 3580310791) ^ 13657 = (3 : ZMod 3580310791) ^ (6828 + 6828 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 6828 * (3 : ZMod 3580310791) ^ 6828) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1363424587 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 3580310791) ^ 27315 = 471760625 := by
        calc
          (3 : ZMod 3580310791) ^ 27315 = (3 : ZMod 3580310791) ^ (13657 + 13657 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 13657 * (3 : ZMod 3580310791) ^ 13657) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 471760625 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 3580310791) ^ 54631 = 461226084 := by
        calc
          (3 : ZMod 3580310791) ^ 54631 = (3 : ZMod 3580310791) ^ (27315 + 27315 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 27315 * (3 : ZMod 3580310791) ^ 27315) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 461226084 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 3580310791) ^ 109262 = 251631466 := by
        calc
          (3 : ZMod 3580310791) ^ 109262 = (3 : ZMod 3580310791) ^ (54631 + 54631) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 54631 * (3 : ZMod 3580310791) ^ 54631 := by rw [pow_add]
          _ = 251631466 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 3580310791) ^ 218524 = 430572059 := by
        calc
          (3 : ZMod 3580310791) ^ 218524 = (3 : ZMod 3580310791) ^ (109262 + 109262) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 109262 * (3 : ZMod 3580310791) ^ 109262 := by rw [pow_add]
          _ = 430572059 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 3580310791) ^ 437049 = 1669756735 := by
        calc
          (3 : ZMod 3580310791) ^ 437049 = (3 : ZMod 3580310791) ^ (218524 + 218524 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 218524 * (3 : ZMod 3580310791) ^ 218524) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1669756735 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 3580310791) ^ 874099 = 396335738 := by
        calc
          (3 : ZMod 3580310791) ^ 874099 = (3 : ZMod 3580310791) ^ (437049 + 437049 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 437049 * (3 : ZMod 3580310791) ^ 437049) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 396335738 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 3580310791) ^ 1748198 = 2198600085 := by
        calc
          (3 : ZMod 3580310791) ^ 1748198 = (3 : ZMod 3580310791) ^ (874099 + 874099) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 874099 * (3 : ZMod 3580310791) ^ 874099 := by rw [pow_add]
          _ = 2198600085 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 3580310791) ^ 3496397 = 1280796253 := by
        calc
          (3 : ZMod 3580310791) ^ 3496397 = (3 : ZMod 3580310791) ^ (1748198 + 1748198 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 1748198 * (3 : ZMod 3580310791) ^ 1748198) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1280796253 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 3580310791) ^ 6992794 = 2395865580 := by
        calc
          (3 : ZMod 3580310791) ^ 6992794 = (3 : ZMod 3580310791) ^ (3496397 + 3496397) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 3496397 * (3 : ZMod 3580310791) ^ 3496397 := by rw [pow_add]
          _ = 2395865580 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 3580310791) ^ 13985589 = 121424305 := by
        calc
          (3 : ZMod 3580310791) ^ 13985589 = (3 : ZMod 3580310791) ^ (6992794 + 6992794 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 6992794 * (3 : ZMod 3580310791) ^ 6992794) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 121424305 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 3580310791) ^ 27971178 = 2375274176 := by
        calc
          (3 : ZMod 3580310791) ^ 27971178 = (3 : ZMod 3580310791) ^ (13985589 + 13985589) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 13985589 * (3 : ZMod 3580310791) ^ 13985589 := by rw [pow_add]
          _ = 2375274176 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 3580310791) ^ 55942356 = 1820154151 := by
        calc
          (3 : ZMod 3580310791) ^ 55942356 = (3 : ZMod 3580310791) ^ (27971178 + 27971178) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 27971178 * (3 : ZMod 3580310791) ^ 27971178 := by rw [pow_add]
          _ = 1820154151 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 3580310791) ^ 111884712 = 788065464 := by
        calc
          (3 : ZMod 3580310791) ^ 111884712 = (3 : ZMod 3580310791) ^ (55942356 + 55942356) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 55942356 * (3 : ZMod 3580310791) ^ 55942356 := by rw [pow_add]
          _ = 788065464 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 3580310791) ^ 223769424 = 3281697541 := by
        calc
          (3 : ZMod 3580310791) ^ 223769424 = (3 : ZMod 3580310791) ^ (111884712 + 111884712) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 111884712 * (3 : ZMod 3580310791) ^ 111884712 := by rw [pow_add]
          _ = 3281697541 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 3580310791) ^ 447538848 = 2292084707 := by
        calc
          (3 : ZMod 3580310791) ^ 447538848 = (3 : ZMod 3580310791) ^ (223769424 + 223769424) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 223769424 * (3 : ZMod 3580310791) ^ 223769424 := by rw [pow_add]
          _ = 2292084707 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 3580310791) ^ 895077697 = 3545011059 := by
        calc
          (3 : ZMod 3580310791) ^ 895077697 = (3 : ZMod 3580310791) ^ (447538848 + 447538848 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 447538848 * (3 : ZMod 3580310791) ^ 447538848) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 3545011059 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 3580310791) ^ 1790155395 = 3580310790 := by
        calc
          (3 : ZMod 3580310791) ^ 1790155395 = (3 : ZMod 3580310791) ^ (895077697 + 895077697 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 895077697 * (3 : ZMod 3580310791) ^ 895077697) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 3580310790 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 3580310791) ^ 3580310790 = 1 := by
        calc
          (3 : ZMod 3580310791) ^ 3580310790 = (3 : ZMod 3580310791) ^ (1790155395 + 1790155395) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 1790155395 * (3 : ZMod 3580310791) ^ 1790155395 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (299107, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (299107, 1)] : List FactorBlock).map factorBlockValue).prod = 3580310791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 3580310791) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 3580310791) ^ 3 = 27 := by
        calc
          (3 : ZMod 3580310791) ^ 3 = (3 : ZMod 3580310791) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 1 * (3 : ZMod 3580310791) ^ 1) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 3580310791) ^ 6 = 729 := by
        calc
          (3 : ZMod 3580310791) ^ 6 = (3 : ZMod 3580310791) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 3 * (3 : ZMod 3580310791) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 3580310791) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 3580310791) ^ 13 = (3 : ZMod 3580310791) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 6 * (3 : ZMod 3580310791) ^ 6) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 3580310791) ^ 26 = 3425477510 := by
        calc
          (3 : ZMod 3580310791) ^ 26 = (3 : ZMod 3580310791) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 13 * (3 : ZMod 3580310791) ^ 13 := by rw [pow_add]
          _ = 3425477510 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 3580310791) ^ 53 = 1074532942 := by
        calc
          (3 : ZMod 3580310791) ^ 53 = (3 : ZMod 3580310791) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 26 * (3 : ZMod 3580310791) ^ 26) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1074532942 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 3580310791) ^ 106 = 39243596 := by
        calc
          (3 : ZMod 3580310791) ^ 106 = (3 : ZMod 3580310791) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 53 * (3 : ZMod 3580310791) ^ 53 := by rw [pow_add]
          _ = 39243596 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 3580310791) ^ 213 = 3223895608 := by
        calc
          (3 : ZMod 3580310791) ^ 213 = (3 : ZMod 3580310791) ^ (106 + 106 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 106 * (3 : ZMod 3580310791) ^ 106) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 3223895608 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 3580310791) ^ 426 = 3544053802 := by
        calc
          (3 : ZMod 3580310791) ^ 426 = (3 : ZMod 3580310791) ^ (213 + 213) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 213 * (3 : ZMod 3580310791) ^ 213 := by rw [pow_add]
          _ = 3544053802 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 3580310791) ^ 853 = 2578373445 := by
        calc
          (3 : ZMod 3580310791) ^ 853 = (3 : ZMod 3580310791) ^ (426 + 426 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 426 * (3 : ZMod 3580310791) ^ 426) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 2578373445 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 3580310791) ^ 1707 = 1458587412 := by
        calc
          (3 : ZMod 3580310791) ^ 1707 = (3 : ZMod 3580310791) ^ (853 + 853 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 853 * (3 : ZMod 3580310791) ^ 853) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1458587412 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 3580310791) ^ 3414 = 1102470735 := by
        calc
          (3 : ZMod 3580310791) ^ 3414 = (3 : ZMod 3580310791) ^ (1707 + 1707) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 1707 * (3 : ZMod 3580310791) ^ 1707 := by rw [pow_add]
          _ = 1102470735 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 3580310791) ^ 6828 = 1772653526 := by
        calc
          (3 : ZMod 3580310791) ^ 6828 = (3 : ZMod 3580310791) ^ (3414 + 3414) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 3414 * (3 : ZMod 3580310791) ^ 3414 := by rw [pow_add]
          _ = 1772653526 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 3580310791) ^ 13657 = 1363424587 := by
        calc
          (3 : ZMod 3580310791) ^ 13657 = (3 : ZMod 3580310791) ^ (6828 + 6828 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 6828 * (3 : ZMod 3580310791) ^ 6828) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1363424587 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 3580310791) ^ 27315 = 471760625 := by
        calc
          (3 : ZMod 3580310791) ^ 27315 = (3 : ZMod 3580310791) ^ (13657 + 13657 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 13657 * (3 : ZMod 3580310791) ^ 13657) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 471760625 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 3580310791) ^ 54631 = 461226084 := by
        calc
          (3 : ZMod 3580310791) ^ 54631 = (3 : ZMod 3580310791) ^ (27315 + 27315 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 27315 * (3 : ZMod 3580310791) ^ 27315) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 461226084 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 3580310791) ^ 109262 = 251631466 := by
        calc
          (3 : ZMod 3580310791) ^ 109262 = (3 : ZMod 3580310791) ^ (54631 + 54631) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 54631 * (3 : ZMod 3580310791) ^ 54631 := by rw [pow_add]
          _ = 251631466 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 3580310791) ^ 218524 = 430572059 := by
        calc
          (3 : ZMod 3580310791) ^ 218524 = (3 : ZMod 3580310791) ^ (109262 + 109262) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 109262 * (3 : ZMod 3580310791) ^ 109262 := by rw [pow_add]
          _ = 430572059 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 3580310791) ^ 437049 = 1669756735 := by
        calc
          (3 : ZMod 3580310791) ^ 437049 = (3 : ZMod 3580310791) ^ (218524 + 218524 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 218524 * (3 : ZMod 3580310791) ^ 218524) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1669756735 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 3580310791) ^ 874099 = 396335738 := by
        calc
          (3 : ZMod 3580310791) ^ 874099 = (3 : ZMod 3580310791) ^ (437049 + 437049 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 437049 * (3 : ZMod 3580310791) ^ 437049) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 396335738 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 3580310791) ^ 1748198 = 2198600085 := by
        calc
          (3 : ZMod 3580310791) ^ 1748198 = (3 : ZMod 3580310791) ^ (874099 + 874099) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 874099 * (3 : ZMod 3580310791) ^ 874099 := by rw [pow_add]
          _ = 2198600085 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 3580310791) ^ 3496397 = 1280796253 := by
        calc
          (3 : ZMod 3580310791) ^ 3496397 = (3 : ZMod 3580310791) ^ (1748198 + 1748198 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 1748198 * (3 : ZMod 3580310791) ^ 1748198) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1280796253 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 3580310791) ^ 6992794 = 2395865580 := by
        calc
          (3 : ZMod 3580310791) ^ 6992794 = (3 : ZMod 3580310791) ^ (3496397 + 3496397) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 3496397 * (3 : ZMod 3580310791) ^ 3496397 := by rw [pow_add]
          _ = 2395865580 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 3580310791) ^ 13985589 = 121424305 := by
        calc
          (3 : ZMod 3580310791) ^ 13985589 = (3 : ZMod 3580310791) ^ (6992794 + 6992794 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 6992794 * (3 : ZMod 3580310791) ^ 6992794) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 121424305 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 3580310791) ^ 27971178 = 2375274176 := by
        calc
          (3 : ZMod 3580310791) ^ 27971178 = (3 : ZMod 3580310791) ^ (13985589 + 13985589) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 13985589 * (3 : ZMod 3580310791) ^ 13985589 := by rw [pow_add]
          _ = 2375274176 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 3580310791) ^ 55942356 = 1820154151 := by
        calc
          (3 : ZMod 3580310791) ^ 55942356 = (3 : ZMod 3580310791) ^ (27971178 + 27971178) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 27971178 * (3 : ZMod 3580310791) ^ 27971178 := by rw [pow_add]
          _ = 1820154151 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 3580310791) ^ 111884712 = 788065464 := by
        calc
          (3 : ZMod 3580310791) ^ 111884712 = (3 : ZMod 3580310791) ^ (55942356 + 55942356) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 55942356 * (3 : ZMod 3580310791) ^ 55942356 := by rw [pow_add]
          _ = 788065464 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 3580310791) ^ 223769424 = 3281697541 := by
        calc
          (3 : ZMod 3580310791) ^ 223769424 = (3 : ZMod 3580310791) ^ (111884712 + 111884712) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 111884712 * (3 : ZMod 3580310791) ^ 111884712 := by rw [pow_add]
          _ = 3281697541 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 3580310791) ^ 447538848 = 2292084707 := by
        calc
          (3 : ZMod 3580310791) ^ 447538848 = (3 : ZMod 3580310791) ^ (223769424 + 223769424) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 223769424 * (3 : ZMod 3580310791) ^ 223769424 := by rw [pow_add]
          _ = 2292084707 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 3580310791) ^ 895077697 = 3545011059 := by
        calc
          (3 : ZMod 3580310791) ^ 895077697 = (3 : ZMod 3580310791) ^ (447538848 + 447538848 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 447538848 * (3 : ZMod 3580310791) ^ 447538848) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 3545011059 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 3580310791) ^ 1790155395 = 3580310790 := by
        calc
          (3 : ZMod 3580310791) ^ 1790155395 = (3 : ZMod 3580310791) ^ (895077697 + 895077697 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 895077697 * (3 : ZMod 3580310791) ^ 895077697) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 3580310790 := by rw [factor_0_29]; decide
      change (3 : ZMod 3580310791) ^ 1790155395 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (3 : ZMod 3580310791) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 3580310791) ^ 2 = 9 := by
        calc
          (3 : ZMod 3580310791) ^ 2 = (3 : ZMod 3580310791) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 1 * (3 : ZMod 3580310791) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 3580310791) ^ 4 = 81 := by
        calc
          (3 : ZMod 3580310791) ^ 4 = (3 : ZMod 3580310791) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 2 * (3 : ZMod 3580310791) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 3580310791) ^ 8 = 6561 := by
        calc
          (3 : ZMod 3580310791) ^ 8 = (3 : ZMod 3580310791) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 4 * (3 : ZMod 3580310791) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 3580310791) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 3580310791) ^ 17 = (3 : ZMod 3580310791) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 8 * (3 : ZMod 3580310791) ^ 8) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 3580310791) ^ 35 = 2841324009 := by
        calc
          (3 : ZMod 3580310791) ^ 35 = (3 : ZMod 3580310791) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 17 * (3 : ZMod 3580310791) ^ 17) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 2841324009 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 3580310791) ^ 71 = 1928671372 := by
        calc
          (3 : ZMod 3580310791) ^ 71 = (3 : ZMod 3580310791) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 35 * (3 : ZMod 3580310791) ^ 35) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1928671372 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 3580310791) ^ 142 = 2350193919 := by
        calc
          (3 : ZMod 3580310791) ^ 142 = (3 : ZMod 3580310791) ^ (71 + 71) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 71 * (3 : ZMod 3580310791) ^ 71 := by rw [pow_add]
          _ = 2350193919 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 3580310791) ^ 284 = 179757267 := by
        calc
          (3 : ZMod 3580310791) ^ 284 = (3 : ZMod 3580310791) ^ (142 + 142) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 142 * (3 : ZMod 3580310791) ^ 142 := by rw [pow_add]
          _ = 179757267 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 3580310791) ^ 569 = 555257657 := by
        calc
          (3 : ZMod 3580310791) ^ 569 = (3 : ZMod 3580310791) ^ (284 + 284 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 284 * (3 : ZMod 3580310791) ^ 284) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 555257657 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 3580310791) ^ 1138 = 2392569646 := by
        calc
          (3 : ZMod 3580310791) ^ 1138 = (3 : ZMod 3580310791) ^ (569 + 569) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 569 * (3 : ZMod 3580310791) ^ 569 := by rw [pow_add]
          _ = 2392569646 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 3580310791) ^ 2276 = 376673854 := by
        calc
          (3 : ZMod 3580310791) ^ 2276 = (3 : ZMod 3580310791) ^ (1138 + 1138) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 1138 * (3 : ZMod 3580310791) ^ 1138 := by rw [pow_add]
          _ = 376673854 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 3580310791) ^ 4552 = 1152723140 := by
        calc
          (3 : ZMod 3580310791) ^ 4552 = (3 : ZMod 3580310791) ^ (2276 + 2276) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 2276 * (3 : ZMod 3580310791) ^ 2276 := by rw [pow_add]
          _ = 1152723140 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 3580310791) ^ 9105 = 106431410 := by
        calc
          (3 : ZMod 3580310791) ^ 9105 = (3 : ZMod 3580310791) ^ (4552 + 4552 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 4552 * (3 : ZMod 3580310791) ^ 4552) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 106431410 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 3580310791) ^ 18210 = 3551956139 := by
        calc
          (3 : ZMod 3580310791) ^ 18210 = (3 : ZMod 3580310791) ^ (9105 + 9105) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 9105 * (3 : ZMod 3580310791) ^ 9105 := by rw [pow_add]
          _ = 3551956139 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 3580310791) ^ 36420 = 2439746517 := by
        calc
          (3 : ZMod 3580310791) ^ 36420 = (3 : ZMod 3580310791) ^ (18210 + 18210) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 18210 * (3 : ZMod 3580310791) ^ 18210 := by rw [pow_add]
          _ = 2439746517 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 3580310791) ^ 72841 = 3530466662 := by
        calc
          (3 : ZMod 3580310791) ^ 72841 = (3 : ZMod 3580310791) ^ (36420 + 36420 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 36420 * (3 : ZMod 3580310791) ^ 36420) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 3530466662 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 3580310791) ^ 145683 = 3178452464 := by
        calc
          (3 : ZMod 3580310791) ^ 145683 = (3 : ZMod 3580310791) ^ (72841 + 72841 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 72841 * (3 : ZMod 3580310791) ^ 72841) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 3178452464 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 3580310791) ^ 291366 = 3414401215 := by
        calc
          (3 : ZMod 3580310791) ^ 291366 = (3 : ZMod 3580310791) ^ (145683 + 145683) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 145683 * (3 : ZMod 3580310791) ^ 145683 := by rw [pow_add]
          _ = 3414401215 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 3580310791) ^ 582732 = 3099119171 := by
        calc
          (3 : ZMod 3580310791) ^ 582732 = (3 : ZMod 3580310791) ^ (291366 + 291366) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 291366 * (3 : ZMod 3580310791) ^ 291366 := by rw [pow_add]
          _ = 3099119171 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 3580310791) ^ 1165465 = 654198346 := by
        calc
          (3 : ZMod 3580310791) ^ 1165465 = (3 : ZMod 3580310791) ^ (582732 + 582732 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 582732 * (3 : ZMod 3580310791) ^ 582732) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 654198346 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 3580310791) ^ 2330931 = 432996963 := by
        calc
          (3 : ZMod 3580310791) ^ 2330931 = (3 : ZMod 3580310791) ^ (1165465 + 1165465 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 1165465 * (3 : ZMod 3580310791) ^ 1165465) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 432996963 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 3580310791) ^ 4661863 = 205324712 := by
        calc
          (3 : ZMod 3580310791) ^ 4661863 = (3 : ZMod 3580310791) ^ (2330931 + 2330931 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 2330931 * (3 : ZMod 3580310791) ^ 2330931) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 205324712 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 3580310791) ^ 9323726 = 2607331333 := by
        calc
          (3 : ZMod 3580310791) ^ 9323726 = (3 : ZMod 3580310791) ^ (4661863 + 4661863) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 4661863 * (3 : ZMod 3580310791) ^ 4661863 := by rw [pow_add]
          _ = 2607331333 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 3580310791) ^ 18647452 = 2188255644 := by
        calc
          (3 : ZMod 3580310791) ^ 18647452 = (3 : ZMod 3580310791) ^ (9323726 + 9323726) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 9323726 * (3 : ZMod 3580310791) ^ 9323726 := by rw [pow_add]
          _ = 2188255644 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 3580310791) ^ 37294904 = 1810056243 := by
        calc
          (3 : ZMod 3580310791) ^ 37294904 = (3 : ZMod 3580310791) ^ (18647452 + 18647452) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 18647452 * (3 : ZMod 3580310791) ^ 18647452 := by rw [pow_add]
          _ = 1810056243 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 3580310791) ^ 74589808 = 1387527907 := by
        calc
          (3 : ZMod 3580310791) ^ 74589808 = (3 : ZMod 3580310791) ^ (37294904 + 37294904) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 37294904 * (3 : ZMod 3580310791) ^ 37294904 := by rw [pow_add]
          _ = 1387527907 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 3580310791) ^ 149179616 = 2292359877 := by
        calc
          (3 : ZMod 3580310791) ^ 149179616 = (3 : ZMod 3580310791) ^ (74589808 + 74589808) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 74589808 * (3 : ZMod 3580310791) ^ 74589808 := by rw [pow_add]
          _ = 2292359877 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 3580310791) ^ 298359232 = 1772505529 := by
        calc
          (3 : ZMod 3580310791) ^ 298359232 = (3 : ZMod 3580310791) ^ (149179616 + 149179616) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 149179616 * (3 : ZMod 3580310791) ^ 149179616 := by rw [pow_add]
          _ = 1772505529 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 3580310791) ^ 596718465 = 1843104994 := by
        calc
          (3 : ZMod 3580310791) ^ 596718465 = (3 : ZMod 3580310791) ^ (298359232 + 298359232 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 298359232 * (3 : ZMod 3580310791) ^ 298359232) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1843104994 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 3580310791) ^ 1193436930 = 1843104993 := by
        calc
          (3 : ZMod 3580310791) ^ 1193436930 = (3 : ZMod 3580310791) ^ (596718465 + 596718465) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 596718465 * (3 : ZMod 3580310791) ^ 596718465 := by rw [pow_add]
          _ = 1843104993 := by rw [factor_1_29]; decide
      change (3 : ZMod 3580310791) ^ 1193436930 ≠ 1
      rw [factor_1_30]
      decide
    ·
      have factor_2_0 : (3 : ZMod 3580310791) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 3580310791) ^ 2 = 9 := by
        calc
          (3 : ZMod 3580310791) ^ 2 = (3 : ZMod 3580310791) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 1 * (3 : ZMod 3580310791) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 3580310791) ^ 5 = 243 := by
        calc
          (3 : ZMod 3580310791) ^ 5 = (3 : ZMod 3580310791) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 2 * (3 : ZMod 3580310791) ^ 2) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 3580310791) ^ 10 = 59049 := by
        calc
          (3 : ZMod 3580310791) ^ 10 = (3 : ZMod 3580310791) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 5 * (3 : ZMod 3580310791) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 3580310791) ^ 21 = 3299731621 := by
        calc
          (3 : ZMod 3580310791) ^ 21 = (3 : ZMod 3580310791) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 10 * (3 : ZMod 3580310791) ^ 10) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 3299731621 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 3580310791) ^ 42 = 2136385298 := by
        calc
          (3 : ZMod 3580310791) ^ 42 = (3 : ZMod 3580310791) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 21 * (3 : ZMod 3580310791) ^ 21 := by rw [pow_add]
          _ = 2136385298 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 3580310791) ^ 85 = 801439029 := by
        calc
          (3 : ZMod 3580310791) ^ 85 = (3 : ZMod 3580310791) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 42 * (3 : ZMod 3580310791) ^ 42) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 801439029 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 3580310791) ^ 170 = 1480328696 := by
        calc
          (3 : ZMod 3580310791) ^ 170 = (3 : ZMod 3580310791) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 85 * (3 : ZMod 3580310791) ^ 85 := by rw [pow_add]
          _ = 1480328696 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 3580310791) ^ 341 = 2375042564 := by
        calc
          (3 : ZMod 3580310791) ^ 341 = (3 : ZMod 3580310791) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 170 * (3 : ZMod 3580310791) ^ 170) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 2375042564 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 3580310791) ^ 682 = 965443571 := by
        calc
          (3 : ZMod 3580310791) ^ 682 = (3 : ZMod 3580310791) ^ (341 + 341) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 341 * (3 : ZMod 3580310791) ^ 341 := by rw [pow_add]
          _ = 965443571 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 3580310791) ^ 1365 = 429786059 := by
        calc
          (3 : ZMod 3580310791) ^ 1365 = (3 : ZMod 3580310791) ^ (682 + 682 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 682 * (3 : ZMod 3580310791) ^ 682) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 429786059 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 3580310791) ^ 2731 = 3052260229 := by
        calc
          (3 : ZMod 3580310791) ^ 2731 = (3 : ZMod 3580310791) ^ (1365 + 1365 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 1365 * (3 : ZMod 3580310791) ^ 1365) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 3052260229 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 3580310791) ^ 5463 = 529367383 := by
        calc
          (3 : ZMod 3580310791) ^ 5463 = (3 : ZMod 3580310791) ^ (2731 + 2731 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 2731 * (3 : ZMod 3580310791) ^ 2731) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 529367383 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 3580310791) ^ 10926 = 3308422317 := by
        calc
          (3 : ZMod 3580310791) ^ 10926 = (3 : ZMod 3580310791) ^ (5463 + 5463) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 5463 * (3 : ZMod 3580310791) ^ 5463 := by rw [pow_add]
          _ = 3308422317 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 3580310791) ^ 21852 = 3034775341 := by
        calc
          (3 : ZMod 3580310791) ^ 21852 = (3 : ZMod 3580310791) ^ (10926 + 10926) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 10926 * (3 : ZMod 3580310791) ^ 10926 := by rw [pow_add]
          _ = 3034775341 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 3580310791) ^ 43704 = 67411221 := by
        calc
          (3 : ZMod 3580310791) ^ 43704 = (3 : ZMod 3580310791) ^ (21852 + 21852) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 21852 * (3 : ZMod 3580310791) ^ 21852 := by rw [pow_add]
          _ = 67411221 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 3580310791) ^ 87409 = 725336794 := by
        calc
          (3 : ZMod 3580310791) ^ 87409 = (3 : ZMod 3580310791) ^ (43704 + 43704 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 43704 * (3 : ZMod 3580310791) ^ 43704) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 725336794 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 3580310791) ^ 174819 = 1697458514 := by
        calc
          (3 : ZMod 3580310791) ^ 174819 = (3 : ZMod 3580310791) ^ (87409 + 87409 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 87409 * (3 : ZMod 3580310791) ^ 87409) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1697458514 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 3580310791) ^ 349639 = 758210368 := by
        calc
          (3 : ZMod 3580310791) ^ 349639 = (3 : ZMod 3580310791) ^ (174819 + 174819 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 174819 * (3 : ZMod 3580310791) ^ 174819) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 758210368 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 3580310791) ^ 699279 = 2859675392 := by
        calc
          (3 : ZMod 3580310791) ^ 699279 = (3 : ZMod 3580310791) ^ (349639 + 349639 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 349639 * (3 : ZMod 3580310791) ^ 349639) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 2859675392 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 3580310791) ^ 1398558 = 1792872122 := by
        calc
          (3 : ZMod 3580310791) ^ 1398558 = (3 : ZMod 3580310791) ^ (699279 + 699279) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 699279 * (3 : ZMod 3580310791) ^ 699279 := by rw [pow_add]
          _ = 1792872122 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 3580310791) ^ 2797117 = 271618165 := by
        calc
          (3 : ZMod 3580310791) ^ 2797117 = (3 : ZMod 3580310791) ^ (1398558 + 1398558 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 1398558 * (3 : ZMod 3580310791) ^ 1398558) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 271618165 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 3580310791) ^ 5594235 = 1154453770 := by
        calc
          (3 : ZMod 3580310791) ^ 5594235 = (3 : ZMod 3580310791) ^ (2797117 + 2797117 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 2797117 * (3 : ZMod 3580310791) ^ 2797117) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1154453770 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 3580310791) ^ 11188471 = 2403661311 := by
        calc
          (3 : ZMod 3580310791) ^ 11188471 = (3 : ZMod 3580310791) ^ (5594235 + 5594235 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 5594235 * (3 : ZMod 3580310791) ^ 5594235) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 2403661311 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 3580310791) ^ 22376942 = 3474463701 := by
        calc
          (3 : ZMod 3580310791) ^ 22376942 = (3 : ZMod 3580310791) ^ (11188471 + 11188471) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 11188471 * (3 : ZMod 3580310791) ^ 11188471 := by rw [pow_add]
          _ = 3474463701 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 3580310791) ^ 44753884 = 1265879543 := by
        calc
          (3 : ZMod 3580310791) ^ 44753884 = (3 : ZMod 3580310791) ^ (22376942 + 22376942) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 22376942 * (3 : ZMod 3580310791) ^ 22376942 := by rw [pow_add]
          _ = 1265879543 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 3580310791) ^ 89507769 = 1467136285 := by
        calc
          (3 : ZMod 3580310791) ^ 89507769 = (3 : ZMod 3580310791) ^ (44753884 + 44753884 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 44753884 * (3 : ZMod 3580310791) ^ 44753884) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1467136285 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 3580310791) ^ 179015539 = 2332776752 := by
        calc
          (3 : ZMod 3580310791) ^ 179015539 = (3 : ZMod 3580310791) ^ (89507769 + 89507769 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 89507769 * (3 : ZMod 3580310791) ^ 89507769) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 2332776752 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 3580310791) ^ 358031079 = 2556205517 := by
        calc
          (3 : ZMod 3580310791) ^ 358031079 = (3 : ZMod 3580310791) ^ (179015539 + 179015539 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 179015539 * (3 : ZMod 3580310791) ^ 179015539) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 2556205517 := by rw [factor_2_27]; decide
      have factor_2_29 : (3 : ZMod 3580310791) ^ 716062158 = 1657317156 := by
        calc
          (3 : ZMod 3580310791) ^ 716062158 = (3 : ZMod 3580310791) ^ (358031079 + 358031079) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 358031079 * (3 : ZMod 3580310791) ^ 358031079 := by rw [pow_add]
          _ = 1657317156 := by rw [factor_2_28]; decide
      change (3 : ZMod 3580310791) ^ 716062158 ≠ 1
      rw [factor_2_29]
      decide
    ·
      have factor_3_0 : (3 : ZMod 3580310791) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 3580310791) ^ 3 = 27 := by
        calc
          (3 : ZMod 3580310791) ^ 3 = (3 : ZMod 3580310791) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 1 * (3 : ZMod 3580310791) ^ 1) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 3580310791) ^ 7 = 2187 := by
        calc
          (3 : ZMod 3580310791) ^ 7 = (3 : ZMod 3580310791) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 3 * (3 : ZMod 3580310791) ^ 3) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 3580310791) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 3580310791) ^ 15 = (3 : ZMod 3580310791) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 7 * (3 : ZMod 3580310791) ^ 7) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 3580310791) ^ 30 = 1779747403 := by
        calc
          (3 : ZMod 3580310791) ^ 30 = (3 : ZMod 3580310791) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 15 * (3 : ZMod 3580310791) ^ 15 := by rw [pow_add]
          _ = 1779747403 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 3580310791) ^ 60 = 1319665258 := by
        calc
          (3 : ZMod 3580310791) ^ 60 = (3 : ZMod 3580310791) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 30 * (3 : ZMod 3580310791) ^ 30 := by rw [pow_add]
          _ = 1319665258 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 3580310791) ^ 121 = 2169073465 := by
        calc
          (3 : ZMod 3580310791) ^ 121 = (3 : ZMod 3580310791) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 60 * (3 : ZMod 3580310791) ^ 60) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 2169073465 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 3580310791) ^ 243 = 1170528841 := by
        calc
          (3 : ZMod 3580310791) ^ 243 = (3 : ZMod 3580310791) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 121 * (3 : ZMod 3580310791) ^ 121) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1170528841 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 3580310791) ^ 487 = 2635945700 := by
        calc
          (3 : ZMod 3580310791) ^ 487 = (3 : ZMod 3580310791) ^ (243 + 243 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 243 * (3 : ZMod 3580310791) ^ 243) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 2635945700 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 3580310791) ^ 975 = 1554814255 := by
        calc
          (3 : ZMod 3580310791) ^ 975 = (3 : ZMod 3580310791) ^ (487 + 487 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 487 * (3 : ZMod 3580310791) ^ 487) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1554814255 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 3580310791) ^ 1951 = 659520972 := by
        calc
          (3 : ZMod 3580310791) ^ 1951 = (3 : ZMod 3580310791) ^ (975 + 975 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 975 * (3 : ZMod 3580310791) ^ 975) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 659520972 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 3580310791) ^ 3902 = 260428614 := by
        calc
          (3 : ZMod 3580310791) ^ 3902 = (3 : ZMod 3580310791) ^ (1951 + 1951) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 1951 * (3 : ZMod 3580310791) ^ 1951 := by rw [pow_add]
          _ = 260428614 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 3580310791) ^ 7804 = 468825101 := by
        calc
          (3 : ZMod 3580310791) ^ 7804 = (3 : ZMod 3580310791) ^ (3902 + 3902) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 3902 * (3 : ZMod 3580310791) ^ 3902 := by rw [pow_add]
          _ = 468825101 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 3580310791) ^ 15608 = 2381166058 := by
        calc
          (3 : ZMod 3580310791) ^ 15608 = (3 : ZMod 3580310791) ^ (7804 + 7804) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 7804 * (3 : ZMod 3580310791) ^ 7804 := by rw [pow_add]
          _ = 2381166058 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 3580310791) ^ 31217 = 516435173 := by
        calc
          (3 : ZMod 3580310791) ^ 31217 = (3 : ZMod 3580310791) ^ (15608 + 15608 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 15608 * (3 : ZMod 3580310791) ^ 15608) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 516435173 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 3580310791) ^ 62435 = 2203089637 := by
        calc
          (3 : ZMod 3580310791) ^ 62435 = (3 : ZMod 3580310791) ^ (31217 + 31217 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 31217 * (3 : ZMod 3580310791) ^ 31217) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 2203089637 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 3580310791) ^ 124871 = 1209067060 := by
        calc
          (3 : ZMod 3580310791) ^ 124871 = (3 : ZMod 3580310791) ^ (62435 + 62435 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 62435 * (3 : ZMod 3580310791) ^ 62435) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1209067060 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 3580310791) ^ 249742 = 435634479 := by
        calc
          (3 : ZMod 3580310791) ^ 249742 = (3 : ZMod 3580310791) ^ (124871 + 124871) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 124871 * (3 : ZMod 3580310791) ^ 124871 := by rw [pow_add]
          _ = 435634479 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 3580310791) ^ 499485 = 1362084138 := by
        calc
          (3 : ZMod 3580310791) ^ 499485 = (3 : ZMod 3580310791) ^ (249742 + 249742 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 249742 * (3 : ZMod 3580310791) ^ 249742) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1362084138 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 3580310791) ^ 998970 = 2321882003 := by
        calc
          (3 : ZMod 3580310791) ^ 998970 = (3 : ZMod 3580310791) ^ (499485 + 499485) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 499485 * (3 : ZMod 3580310791) ^ 499485 := by rw [pow_add]
          _ = 2321882003 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 3580310791) ^ 1997941 = 870383218 := by
        calc
          (3 : ZMod 3580310791) ^ 1997941 = (3 : ZMod 3580310791) ^ (998970 + 998970 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 998970 * (3 : ZMod 3580310791) ^ 998970) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 870383218 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 3580310791) ^ 3995882 = 2908570905 := by
        calc
          (3 : ZMod 3580310791) ^ 3995882 = (3 : ZMod 3580310791) ^ (1997941 + 1997941) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 1997941 * (3 : ZMod 3580310791) ^ 1997941 := by rw [pow_add]
          _ = 2908570905 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 3580310791) ^ 7991765 = 382009404 := by
        calc
          (3 : ZMod 3580310791) ^ 7991765 = (3 : ZMod 3580310791) ^ (3995882 + 3995882 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 3995882 * (3 : ZMod 3580310791) ^ 3995882) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 382009404 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 3580310791) ^ 15983530 = 1141559874 := by
        calc
          (3 : ZMod 3580310791) ^ 15983530 = (3 : ZMod 3580310791) ^ (7991765 + 7991765) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 7991765 * (3 : ZMod 3580310791) ^ 7991765 := by rw [pow_add]
          _ = 1141559874 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 3580310791) ^ 31967060 = 2042485396 := by
        calc
          (3 : ZMod 3580310791) ^ 31967060 = (3 : ZMod 3580310791) ^ (15983530 + 15983530) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 15983530 * (3 : ZMod 3580310791) ^ 15983530 := by rw [pow_add]
          _ = 2042485396 := by rw [factor_3_23]; decide
      have factor_3_25 : (3 : ZMod 3580310791) ^ 63934121 = 1634125787 := by
        calc
          (3 : ZMod 3580310791) ^ 63934121 = (3 : ZMod 3580310791) ^ (31967060 + 31967060 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 31967060 * (3 : ZMod 3580310791) ^ 31967060) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1634125787 := by rw [factor_3_24]; decide
      have factor_3_26 : (3 : ZMod 3580310791) ^ 127868242 = 3421084765 := by
        calc
          (3 : ZMod 3580310791) ^ 127868242 = (3 : ZMod 3580310791) ^ (63934121 + 63934121) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 63934121 * (3 : ZMod 3580310791) ^ 63934121 := by rw [pow_add]
          _ = 3421084765 := by rw [factor_3_25]; decide
      have factor_3_27 : (3 : ZMod 3580310791) ^ 255736485 = 2239800653 := by
        calc
          (3 : ZMod 3580310791) ^ 255736485 = (3 : ZMod 3580310791) ^ (127868242 + 127868242 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 127868242 * (3 : ZMod 3580310791) ^ 127868242) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 2239800653 := by rw [factor_3_26]; decide
      have factor_3_28 : (3 : ZMod 3580310791) ^ 511472970 = 2798323177 := by
        calc
          (3 : ZMod 3580310791) ^ 511472970 = (3 : ZMod 3580310791) ^ (255736485 + 255736485) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 255736485 * (3 : ZMod 3580310791) ^ 255736485 := by rw [pow_add]
          _ = 2798323177 := by rw [factor_3_27]; decide
      change (3 : ZMod 3580310791) ^ 511472970 ≠ 1
      rw [factor_3_28]
      decide
    ·
      have factor_4_0 : (3 : ZMod 3580310791) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 3580310791) ^ 2 = 9 := by
        calc
          (3 : ZMod 3580310791) ^ 2 = (3 : ZMod 3580310791) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 1 * (3 : ZMod 3580310791) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 3580310791) ^ 5 = 243 := by
        calc
          (3 : ZMod 3580310791) ^ 5 = (3 : ZMod 3580310791) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 2 * (3 : ZMod 3580310791) ^ 2) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 3580310791) ^ 11 = 177147 := by
        calc
          (3 : ZMod 3580310791) ^ 11 = (3 : ZMod 3580310791) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 5 * (3 : ZMod 3580310791) ^ 5) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 3580310791) ^ 22 = 2738573281 := by
        calc
          (3 : ZMod 3580310791) ^ 22 = (3 : ZMod 3580310791) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 11 * (3 : ZMod 3580310791) ^ 11 := by rw [pow_add]
          _ = 2738573281 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 3580310791) ^ 44 = 1325913727 := by
        calc
          (3 : ZMod 3580310791) ^ 44 = (3 : ZMod 3580310791) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 22 * (3 : ZMod 3580310791) ^ 22 := by rw [pow_add]
          _ = 1325913727 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 3580310791) ^ 89 = 470967111 := by
        calc
          (3 : ZMod 3580310791) ^ 89 = (3 : ZMod 3580310791) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 44 * (3 : ZMod 3580310791) ^ 44) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 470967111 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 3580310791) ^ 179 = 740506210 := by
        calc
          (3 : ZMod 3580310791) ^ 179 = (3 : ZMod 3580310791) ^ (89 + 89 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 89 * (3 : ZMod 3580310791) ^ 89) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 740506210 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 3580310791) ^ 359 = 2569762889 := by
        calc
          (3 : ZMod 3580310791) ^ 359 = (3 : ZMod 3580310791) ^ (179 + 179 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 179 * (3 : ZMod 3580310791) ^ 179) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 2569762889 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 3580310791) ^ 718 = 2692603467 := by
        calc
          (3 : ZMod 3580310791) ^ 718 = (3 : ZMod 3580310791) ^ (359 + 359) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 359 * (3 : ZMod 3580310791) ^ 359 := by rw [pow_add]
          _ = 2692603467 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 3580310791) ^ 1437 = 1102522998 := by
        calc
          (3 : ZMod 3580310791) ^ 1437 = (3 : ZMod 3580310791) ^ (718 + 718 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 718 * (3 : ZMod 3580310791) ^ 718) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1102522998 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 3580310791) ^ 2875 = 2109763373 := by
        calc
          (3 : ZMod 3580310791) ^ 2875 = (3 : ZMod 3580310791) ^ (1437 + 1437 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 1437 * (3 : ZMod 3580310791) ^ 1437) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 2109763373 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 3580310791) ^ 5750 = 169666928 := by
        calc
          (3 : ZMod 3580310791) ^ 5750 = (3 : ZMod 3580310791) ^ (2875 + 2875) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 2875 * (3 : ZMod 3580310791) ^ 2875 := by rw [pow_add]
          _ = 169666928 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 3580310791) ^ 11501 = 1547997954 := by
        calc
          (3 : ZMod 3580310791) ^ 11501 = (3 : ZMod 3580310791) ^ (5750 + 5750 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 5750 * (3 : ZMod 3580310791) ^ 5750) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1547997954 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 3580310791) ^ 23002 = 3249497181 := by
        calc
          (3 : ZMod 3580310791) ^ 23002 = (3 : ZMod 3580310791) ^ (11501 + 11501) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 11501 * (3 : ZMod 3580310791) ^ 11501 := by rw [pow_add]
          _ = 3249497181 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 3580310791) ^ 46005 = 2325122758 := by
        calc
          (3 : ZMod 3580310791) ^ 46005 = (3 : ZMod 3580310791) ^ (23002 + 23002 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 23002 * (3 : ZMod 3580310791) ^ 23002) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 2325122758 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 3580310791) ^ 92010 = 2596025511 := by
        calc
          (3 : ZMod 3580310791) ^ 92010 = (3 : ZMod 3580310791) ^ (46005 + 46005) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 46005 * (3 : ZMod 3580310791) ^ 46005 := by rw [pow_add]
          _ = 2596025511 := by rw [factor_4_15]; decide
      have factor_4_17 : (3 : ZMod 3580310791) ^ 184020 = 2146551725 := by
        calc
          (3 : ZMod 3580310791) ^ 184020 = (3 : ZMod 3580310791) ^ (92010 + 92010) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 92010 * (3 : ZMod 3580310791) ^ 92010 := by rw [pow_add]
          _ = 2146551725 := by rw [factor_4_16]; decide
      have factor_4_18 : (3 : ZMod 3580310791) ^ 368041 = 3480726821 := by
        calc
          (3 : ZMod 3580310791) ^ 368041 = (3 : ZMod 3580310791) ^ (184020 + 184020 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 184020 * (3 : ZMod 3580310791) ^ 184020) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 3480726821 := by rw [factor_4_17]; decide
      have factor_4_19 : (3 : ZMod 3580310791) ^ 736083 = 818340174 := by
        calc
          (3 : ZMod 3580310791) ^ 736083 = (3 : ZMod 3580310791) ^ (368041 + 368041 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 368041 * (3 : ZMod 3580310791) ^ 368041) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 818340174 := by rw [factor_4_18]; decide
      have factor_4_20 : (3 : ZMod 3580310791) ^ 1472167 = 672532448 := by
        calc
          (3 : ZMod 3580310791) ^ 1472167 = (3 : ZMod 3580310791) ^ (736083 + 736083 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 736083 * (3 : ZMod 3580310791) ^ 736083) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 672532448 := by rw [factor_4_19]; decide
      have factor_4_21 : (3 : ZMod 3580310791) ^ 2944334 = 1152662769 := by
        calc
          (3 : ZMod 3580310791) ^ 2944334 = (3 : ZMod 3580310791) ^ (1472167 + 1472167) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 1472167 * (3 : ZMod 3580310791) ^ 1472167 := by rw [pow_add]
          _ = 1152662769 := by rw [factor_4_20]; decide
      have factor_4_22 : (3 : ZMod 3580310791) ^ 5888669 = 592741113 := by
        calc
          (3 : ZMod 3580310791) ^ 5888669 = (3 : ZMod 3580310791) ^ (2944334 + 2944334 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 2944334 * (3 : ZMod 3580310791) ^ 2944334) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 592741113 := by rw [factor_4_21]; decide
      have factor_4_23 : (3 : ZMod 3580310791) ^ 11777338 = 3207885368 := by
        calc
          (3 : ZMod 3580310791) ^ 11777338 = (3 : ZMod 3580310791) ^ (5888669 + 5888669) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 5888669 * (3 : ZMod 3580310791) ^ 5888669 := by rw [pow_add]
          _ = 3207885368 := by rw [factor_4_22]; decide
      have factor_4_24 : (3 : ZMod 3580310791) ^ 23554676 = 3440939952 := by
        calc
          (3 : ZMod 3580310791) ^ 23554676 = (3 : ZMod 3580310791) ^ (11777338 + 11777338) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 11777338 * (3 : ZMod 3580310791) ^ 11777338 := by rw [pow_add]
          _ = 3440939952 := by rw [factor_4_23]; decide
      have factor_4_25 : (3 : ZMod 3580310791) ^ 47109352 = 2851948740 := by
        calc
          (3 : ZMod 3580310791) ^ 47109352 = (3 : ZMod 3580310791) ^ (23554676 + 23554676) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 23554676 * (3 : ZMod 3580310791) ^ 23554676 := by rw [pow_add]
          _ = 2851948740 := by rw [factor_4_24]; decide
      have factor_4_26 : (3 : ZMod 3580310791) ^ 94218705 = 1413429591 := by
        calc
          (3 : ZMod 3580310791) ^ 94218705 = (3 : ZMod 3580310791) ^ (47109352 + 47109352 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 47109352 * (3 : ZMod 3580310791) ^ 47109352) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1413429591 := by rw [factor_4_25]; decide
      have factor_4_27 : (3 : ZMod 3580310791) ^ 188437410 = 1579192530 := by
        calc
          (3 : ZMod 3580310791) ^ 188437410 = (3 : ZMod 3580310791) ^ (94218705 + 94218705) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 94218705 * (3 : ZMod 3580310791) ^ 94218705 := by rw [pow_add]
          _ = 1579192530 := by rw [factor_4_26]; decide
      change (3 : ZMod 3580310791) ^ 188437410 ≠ 1
      rw [factor_4_27]
      decide
    ·
      have factor_5_0 : (3 : ZMod 3580310791) ^ 1 = 3 := by norm_num
      have factor_5_1 : (3 : ZMod 3580310791) ^ 2 = 9 := by
        calc
          (3 : ZMod 3580310791) ^ 2 = (3 : ZMod 3580310791) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 1 * (3 : ZMod 3580310791) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_5_0]; decide
      have factor_5_2 : (3 : ZMod 3580310791) ^ 5 = 243 := by
        calc
          (3 : ZMod 3580310791) ^ 5 = (3 : ZMod 3580310791) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 2 * (3 : ZMod 3580310791) ^ 2) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_5_1]; decide
      have factor_5_3 : (3 : ZMod 3580310791) ^ 11 = 177147 := by
        calc
          (3 : ZMod 3580310791) ^ 11 = (3 : ZMod 3580310791) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 5 * (3 : ZMod 3580310791) ^ 5) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_5_2]; decide
      have factor_5_4 : (3 : ZMod 3580310791) ^ 23 = 1055098261 := by
        calc
          (3 : ZMod 3580310791) ^ 23 = (3 : ZMod 3580310791) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 11 * (3 : ZMod 3580310791) ^ 11) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 1055098261 := by rw [factor_5_3]; decide
      have factor_5_5 : (3 : ZMod 3580310791) ^ 46 = 1192291170 := by
        calc
          (3 : ZMod 3580310791) ^ 46 = (3 : ZMod 3580310791) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 23 * (3 : ZMod 3580310791) ^ 23 := by rw [pow_add]
          _ = 1192291170 := by rw [factor_5_4]; decide
      have factor_5_6 : (3 : ZMod 3580310791) ^ 93 = 2345228081 := by
        calc
          (3 : ZMod 3580310791) ^ 93 = (3 : ZMod 3580310791) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 46 * (3 : ZMod 3580310791) ^ 46) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 2345228081 := by rw [factor_5_5]; decide
      have factor_5_7 : (3 : ZMod 3580310791) ^ 187 = 3559811214 := by
        calc
          (3 : ZMod 3580310791) ^ 187 = (3 : ZMod 3580310791) ^ (93 + 93 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 93 * (3 : ZMod 3580310791) ^ 93) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 3559811214 := by rw [factor_5_6]; decide
      have factor_5_8 : (3 : ZMod 3580310791) ^ 374 = 838706886 := by
        calc
          (3 : ZMod 3580310791) ^ 374 = (3 : ZMod 3580310791) ^ (187 + 187) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 187 * (3 : ZMod 3580310791) ^ 187 := by rw [pow_add]
          _ = 838706886 := by rw [factor_5_7]; decide
      have factor_5_9 : (3 : ZMod 3580310791) ^ 748 = 1391834618 := by
        calc
          (3 : ZMod 3580310791) ^ 748 = (3 : ZMod 3580310791) ^ (374 + 374) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 374 * (3 : ZMod 3580310791) ^ 374 := by rw [pow_add]
          _ = 1391834618 := by rw [factor_5_8]; decide
      have factor_5_10 : (3 : ZMod 3580310791) ^ 1496 = 16335701 := by
        calc
          (3 : ZMod 3580310791) ^ 1496 = (3 : ZMod 3580310791) ^ (748 + 748) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 748 * (3 : ZMod 3580310791) ^ 748 := by rw [pow_add]
          _ = 16335701 := by rw [factor_5_9]; decide
      have factor_5_11 : (3 : ZMod 3580310791) ^ 2992 = 242665007 := by
        calc
          (3 : ZMod 3580310791) ^ 2992 = (3 : ZMod 3580310791) ^ (1496 + 1496) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 1496 * (3 : ZMod 3580310791) ^ 1496 := by rw [pow_add]
          _ = 242665007 := by rw [factor_5_10]; decide
      have factor_5_12 : (3 : ZMod 3580310791) ^ 5985 = 2325160585 := by
        calc
          (3 : ZMod 3580310791) ^ 5985 = (3 : ZMod 3580310791) ^ (2992 + 2992 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = ((3 : ZMod 3580310791) ^ 2992 * (3 : ZMod 3580310791) ^ 2992) * (3 : ZMod 3580310791) := by rw [pow_succ, pow_add]
          _ = 2325160585 := by rw [factor_5_11]; decide
      have factor_5_13 : (3 : ZMod 3580310791) ^ 11970 = 1034257760 := by
        calc
          (3 : ZMod 3580310791) ^ 11970 = (3 : ZMod 3580310791) ^ (5985 + 5985) :=
            congrArg (fun n : ℕ => (3 : ZMod 3580310791) ^ n) (by norm_num)
          _ = (3 : ZMod 3580310791) ^ 5985 * (3 : ZMod 3580310791) ^ 5985 := by rw [pow_add]
          _ = 1034257760 := by rw [factor_5_12]; decide
      change (3 : ZMod 3580310791) ^ 11970 ≠ 1
      rw [factor_5_13]
      decide

#print axioms prime_lucas_3580310791

end TotientTailPeriodKiller
end Erdos249257
