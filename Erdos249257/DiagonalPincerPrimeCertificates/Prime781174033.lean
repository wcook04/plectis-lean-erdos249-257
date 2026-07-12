import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_781174033 : Nat.Prime 781174033 := by
  apply lucas_primality 781174033 (7 : ZMod 781174033)
  ·
      have fermat_0 : (7 : ZMod 781174033) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 781174033) ^ 2 = 49 := by
        calc
          (7 : ZMod 781174033) ^ 2 = (7 : ZMod 781174033) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 1 * (7 : ZMod 781174033) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 781174033) ^ 5 = 16807 := by
        calc
          (7 : ZMod 781174033) ^ 5 = (7 : ZMod 781174033) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 2 * (7 : ZMod 781174033) ^ 2) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 781174033) ^ 11 = 414978677 := by
        calc
          (7 : ZMod 781174033) ^ 11 = (7 : ZMod 781174033) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 5 * (7 : ZMod 781174033) ^ 5) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 414978677 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 781174033) ^ 23 = 349139496 := by
        calc
          (7 : ZMod 781174033) ^ 23 = (7 : ZMod 781174033) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 11 * (7 : ZMod 781174033) ^ 11) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 349139496 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 781174033) ^ 46 = 539679419 := by
        calc
          (7 : ZMod 781174033) ^ 46 = (7 : ZMod 781174033) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 23 * (7 : ZMod 781174033) ^ 23 := by rw [pow_add]
          _ = 539679419 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 781174033) ^ 93 = 257574361 := by
        calc
          (7 : ZMod 781174033) ^ 93 = (7 : ZMod 781174033) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 46 * (7 : ZMod 781174033) ^ 46) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 257574361 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 781174033) ^ 186 = 142475949 := by
        calc
          (7 : ZMod 781174033) ^ 186 = (7 : ZMod 781174033) ^ (93 + 93) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 93 * (7 : ZMod 781174033) ^ 93 := by rw [pow_add]
          _ = 142475949 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 781174033) ^ 372 = 571898752 := by
        calc
          (7 : ZMod 781174033) ^ 372 = (7 : ZMod 781174033) ^ (186 + 186) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 186 * (7 : ZMod 781174033) ^ 186 := by rw [pow_add]
          _ = 571898752 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 781174033) ^ 744 = 728063999 := by
        calc
          (7 : ZMod 781174033) ^ 744 = (7 : ZMod 781174033) ^ (372 + 372) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 372 * (7 : ZMod 781174033) ^ 372 := by rw [pow_add]
          _ = 728063999 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 781174033) ^ 1489 = 100381596 := by
        calc
          (7 : ZMod 781174033) ^ 1489 = (7 : ZMod 781174033) ^ (744 + 744 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 744 * (7 : ZMod 781174033) ^ 744) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 100381596 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 781174033) ^ 2979 = 565555680 := by
        calc
          (7 : ZMod 781174033) ^ 2979 = (7 : ZMod 781174033) ^ (1489 + 1489 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 1489 * (7 : ZMod 781174033) ^ 1489) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 565555680 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 781174033) ^ 5959 = 675601538 := by
        calc
          (7 : ZMod 781174033) ^ 5959 = (7 : ZMod 781174033) ^ (2979 + 2979 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 2979 * (7 : ZMod 781174033) ^ 2979) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 675601538 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 781174033) ^ 11919 = 583241993 := by
        calc
          (7 : ZMod 781174033) ^ 11919 = (7 : ZMod 781174033) ^ (5959 + 5959 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 5959 * (7 : ZMod 781174033) ^ 5959) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 583241993 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 781174033) ^ 23839 = 627106028 := by
        calc
          (7 : ZMod 781174033) ^ 23839 = (7 : ZMod 781174033) ^ (11919 + 11919 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 11919 * (7 : ZMod 781174033) ^ 11919) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 627106028 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 781174033) ^ 47679 = 243992227 := by
        calc
          (7 : ZMod 781174033) ^ 47679 = (7 : ZMod 781174033) ^ (23839 + 23839 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 23839 * (7 : ZMod 781174033) ^ 23839) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 243992227 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 781174033) ^ 95358 = 84044574 := by
        calc
          (7 : ZMod 781174033) ^ 95358 = (7 : ZMod 781174033) ^ (47679 + 47679) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 47679 * (7 : ZMod 781174033) ^ 47679 := by rw [pow_add]
          _ = 84044574 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 781174033) ^ 190716 = 761046658 := by
        calc
          (7 : ZMod 781174033) ^ 190716 = (7 : ZMod 781174033) ^ (95358 + 95358) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 95358 * (7 : ZMod 781174033) ^ 95358 := by rw [pow_add]
          _ = 761046658 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 781174033) ^ 381432 = 620269089 := by
        calc
          (7 : ZMod 781174033) ^ 381432 = (7 : ZMod 781174033) ^ (190716 + 190716) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 190716 * (7 : ZMod 781174033) ^ 190716 := by rw [pow_add]
          _ = 620269089 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 781174033) ^ 762865 = 161435736 := by
        calc
          (7 : ZMod 781174033) ^ 762865 = (7 : ZMod 781174033) ^ (381432 + 381432 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 381432 * (7 : ZMod 781174033) ^ 381432) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 161435736 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 781174033) ^ 1525730 = 15877016 := by
        calc
          (7 : ZMod 781174033) ^ 1525730 = (7 : ZMod 781174033) ^ (762865 + 762865) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 762865 * (7 : ZMod 781174033) ^ 762865 := by rw [pow_add]
          _ = 15877016 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 781174033) ^ 3051461 = 151485643 := by
        calc
          (7 : ZMod 781174033) ^ 3051461 = (7 : ZMod 781174033) ^ (1525730 + 1525730 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 1525730 * (7 : ZMod 781174033) ^ 1525730) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 151485643 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 781174033) ^ 6102922 = 404477905 := by
        calc
          (7 : ZMod 781174033) ^ 6102922 = (7 : ZMod 781174033) ^ (3051461 + 3051461) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 3051461 * (7 : ZMod 781174033) ^ 3051461 := by rw [pow_add]
          _ = 404477905 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 781174033) ^ 12205844 = 352482660 := by
        calc
          (7 : ZMod 781174033) ^ 12205844 = (7 : ZMod 781174033) ^ (6102922 + 6102922) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 6102922 * (7 : ZMod 781174033) ^ 6102922 := by rw [pow_add]
          _ = 352482660 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 781174033) ^ 24411688 = 173765606 := by
        calc
          (7 : ZMod 781174033) ^ 24411688 = (7 : ZMod 781174033) ^ (12205844 + 12205844) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 12205844 * (7 : ZMod 781174033) ^ 12205844 := by rw [pow_add]
          _ = 173765606 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 781174033) ^ 48823377 = 420108886 := by
        calc
          (7 : ZMod 781174033) ^ 48823377 = (7 : ZMod 781174033) ^ (24411688 + 24411688 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 24411688 * (7 : ZMod 781174033) ^ 24411688) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 420108886 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 781174033) ^ 97646754 = 338344082 := by
        calc
          (7 : ZMod 781174033) ^ 97646754 = (7 : ZMod 781174033) ^ (48823377 + 48823377) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 48823377 * (7 : ZMod 781174033) ^ 48823377 := by rw [pow_add]
          _ = 338344082 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 781174033) ^ 195293508 = 366503940 := by
        calc
          (7 : ZMod 781174033) ^ 195293508 = (7 : ZMod 781174033) ^ (97646754 + 97646754) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 97646754 * (7 : ZMod 781174033) ^ 97646754 := by rw [pow_add]
          _ = 366503940 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 781174033) ^ 390587016 = 781174032 := by
        calc
          (7 : ZMod 781174033) ^ 390587016 = (7 : ZMod 781174033) ^ (195293508 + 195293508) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 195293508 * (7 : ZMod 781174033) ^ 195293508 := by rw [pow_add]
          _ = 781174032 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 781174033) ^ 781174032 = 1 := by
        calc
          (7 : ZMod 781174033) ^ 781174032 = (7 : ZMod 781174033) ^ (390587016 + 390587016) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 390587016 * (7 : ZMod 781174033) ^ 390587016 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (16274459, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (16274459, 1)] : List FactorBlock).map factorBlockValue).prod = 781174033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 781174033) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 781174033) ^ 2 = 49 := by
        calc
          (7 : ZMod 781174033) ^ 2 = (7 : ZMod 781174033) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 1 * (7 : ZMod 781174033) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 781174033) ^ 5 = 16807 := by
        calc
          (7 : ZMod 781174033) ^ 5 = (7 : ZMod 781174033) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 2 * (7 : ZMod 781174033) ^ 2) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 781174033) ^ 11 = 414978677 := by
        calc
          (7 : ZMod 781174033) ^ 11 = (7 : ZMod 781174033) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 5 * (7 : ZMod 781174033) ^ 5) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 414978677 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 781174033) ^ 23 = 349139496 := by
        calc
          (7 : ZMod 781174033) ^ 23 = (7 : ZMod 781174033) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 11 * (7 : ZMod 781174033) ^ 11) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 349139496 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 781174033) ^ 46 = 539679419 := by
        calc
          (7 : ZMod 781174033) ^ 46 = (7 : ZMod 781174033) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 23 * (7 : ZMod 781174033) ^ 23 := by rw [pow_add]
          _ = 539679419 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 781174033) ^ 93 = 257574361 := by
        calc
          (7 : ZMod 781174033) ^ 93 = (7 : ZMod 781174033) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 46 * (7 : ZMod 781174033) ^ 46) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 257574361 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 781174033) ^ 186 = 142475949 := by
        calc
          (7 : ZMod 781174033) ^ 186 = (7 : ZMod 781174033) ^ (93 + 93) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 93 * (7 : ZMod 781174033) ^ 93 := by rw [pow_add]
          _ = 142475949 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 781174033) ^ 372 = 571898752 := by
        calc
          (7 : ZMod 781174033) ^ 372 = (7 : ZMod 781174033) ^ (186 + 186) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 186 * (7 : ZMod 781174033) ^ 186 := by rw [pow_add]
          _ = 571898752 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 781174033) ^ 744 = 728063999 := by
        calc
          (7 : ZMod 781174033) ^ 744 = (7 : ZMod 781174033) ^ (372 + 372) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 372 * (7 : ZMod 781174033) ^ 372 := by rw [pow_add]
          _ = 728063999 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 781174033) ^ 1489 = 100381596 := by
        calc
          (7 : ZMod 781174033) ^ 1489 = (7 : ZMod 781174033) ^ (744 + 744 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 744 * (7 : ZMod 781174033) ^ 744) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 100381596 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 781174033) ^ 2979 = 565555680 := by
        calc
          (7 : ZMod 781174033) ^ 2979 = (7 : ZMod 781174033) ^ (1489 + 1489 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 1489 * (7 : ZMod 781174033) ^ 1489) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 565555680 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 781174033) ^ 5959 = 675601538 := by
        calc
          (7 : ZMod 781174033) ^ 5959 = (7 : ZMod 781174033) ^ (2979 + 2979 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 2979 * (7 : ZMod 781174033) ^ 2979) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 675601538 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 781174033) ^ 11919 = 583241993 := by
        calc
          (7 : ZMod 781174033) ^ 11919 = (7 : ZMod 781174033) ^ (5959 + 5959 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 5959 * (7 : ZMod 781174033) ^ 5959) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 583241993 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 781174033) ^ 23839 = 627106028 := by
        calc
          (7 : ZMod 781174033) ^ 23839 = (7 : ZMod 781174033) ^ (11919 + 11919 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 11919 * (7 : ZMod 781174033) ^ 11919) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 627106028 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 781174033) ^ 47679 = 243992227 := by
        calc
          (7 : ZMod 781174033) ^ 47679 = (7 : ZMod 781174033) ^ (23839 + 23839 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 23839 * (7 : ZMod 781174033) ^ 23839) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 243992227 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 781174033) ^ 95358 = 84044574 := by
        calc
          (7 : ZMod 781174033) ^ 95358 = (7 : ZMod 781174033) ^ (47679 + 47679) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 47679 * (7 : ZMod 781174033) ^ 47679 := by rw [pow_add]
          _ = 84044574 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 781174033) ^ 190716 = 761046658 := by
        calc
          (7 : ZMod 781174033) ^ 190716 = (7 : ZMod 781174033) ^ (95358 + 95358) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 95358 * (7 : ZMod 781174033) ^ 95358 := by rw [pow_add]
          _ = 761046658 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 781174033) ^ 381432 = 620269089 := by
        calc
          (7 : ZMod 781174033) ^ 381432 = (7 : ZMod 781174033) ^ (190716 + 190716) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 190716 * (7 : ZMod 781174033) ^ 190716 := by rw [pow_add]
          _ = 620269089 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 781174033) ^ 762865 = 161435736 := by
        calc
          (7 : ZMod 781174033) ^ 762865 = (7 : ZMod 781174033) ^ (381432 + 381432 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 381432 * (7 : ZMod 781174033) ^ 381432) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 161435736 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 781174033) ^ 1525730 = 15877016 := by
        calc
          (7 : ZMod 781174033) ^ 1525730 = (7 : ZMod 781174033) ^ (762865 + 762865) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 762865 * (7 : ZMod 781174033) ^ 762865 := by rw [pow_add]
          _ = 15877016 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 781174033) ^ 3051461 = 151485643 := by
        calc
          (7 : ZMod 781174033) ^ 3051461 = (7 : ZMod 781174033) ^ (1525730 + 1525730 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 1525730 * (7 : ZMod 781174033) ^ 1525730) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 151485643 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 781174033) ^ 6102922 = 404477905 := by
        calc
          (7 : ZMod 781174033) ^ 6102922 = (7 : ZMod 781174033) ^ (3051461 + 3051461) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 3051461 * (7 : ZMod 781174033) ^ 3051461 := by rw [pow_add]
          _ = 404477905 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 781174033) ^ 12205844 = 352482660 := by
        calc
          (7 : ZMod 781174033) ^ 12205844 = (7 : ZMod 781174033) ^ (6102922 + 6102922) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 6102922 * (7 : ZMod 781174033) ^ 6102922 := by rw [pow_add]
          _ = 352482660 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 781174033) ^ 24411688 = 173765606 := by
        calc
          (7 : ZMod 781174033) ^ 24411688 = (7 : ZMod 781174033) ^ (12205844 + 12205844) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 12205844 * (7 : ZMod 781174033) ^ 12205844 := by rw [pow_add]
          _ = 173765606 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 781174033) ^ 48823377 = 420108886 := by
        calc
          (7 : ZMod 781174033) ^ 48823377 = (7 : ZMod 781174033) ^ (24411688 + 24411688 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 24411688 * (7 : ZMod 781174033) ^ 24411688) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 420108886 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 781174033) ^ 97646754 = 338344082 := by
        calc
          (7 : ZMod 781174033) ^ 97646754 = (7 : ZMod 781174033) ^ (48823377 + 48823377) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 48823377 * (7 : ZMod 781174033) ^ 48823377 := by rw [pow_add]
          _ = 338344082 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 781174033) ^ 195293508 = 366503940 := by
        calc
          (7 : ZMod 781174033) ^ 195293508 = (7 : ZMod 781174033) ^ (97646754 + 97646754) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 97646754 * (7 : ZMod 781174033) ^ 97646754 := by rw [pow_add]
          _ = 366503940 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 781174033) ^ 390587016 = 781174032 := by
        calc
          (7 : ZMod 781174033) ^ 390587016 = (7 : ZMod 781174033) ^ (195293508 + 195293508) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 195293508 * (7 : ZMod 781174033) ^ 195293508 := by rw [pow_add]
          _ = 781174032 := by rw [factor_0_27]; decide
      change (7 : ZMod 781174033) ^ 390587016 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (7 : ZMod 781174033) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 781174033) ^ 3 = 343 := by
        calc
          (7 : ZMod 781174033) ^ 3 = (7 : ZMod 781174033) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 1 * (7 : ZMod 781174033) ^ 1) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 781174033) ^ 7 = 823543 := by
        calc
          (7 : ZMod 781174033) ^ 7 = (7 : ZMod 781174033) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 3 * (7 : ZMod 781174033) ^ 3) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 781174033) ^ 15 = 366911402 := by
        calc
          (7 : ZMod 781174033) ^ 15 = (7 : ZMod 781174033) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 7 * (7 : ZMod 781174033) ^ 7) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 366911402 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 781174033) ^ 31 = 603260773 := by
        calc
          (7 : ZMod 781174033) ^ 31 = (7 : ZMod 781174033) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 15 * (7 : ZMod 781174033) ^ 15) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 603260773 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 781174033) ^ 62 = 12413448 := by
        calc
          (7 : ZMod 781174033) ^ 62 = (7 : ZMod 781174033) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 31 * (7 : ZMod 781174033) ^ 31 := by rw [pow_add]
          _ = 12413448 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 781174033) ^ 124 = 82673157 := by
        calc
          (7 : ZMod 781174033) ^ 124 = (7 : ZMod 781174033) ^ (62 + 62) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 62 * (7 : ZMod 781174033) ^ 62 := by rw [pow_add]
          _ = 82673157 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 781174033) ^ 248 = 714748502 := by
        calc
          (7 : ZMod 781174033) ^ 248 = (7 : ZMod 781174033) ^ (124 + 124) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 124 * (7 : ZMod 781174033) ^ 124 := by rw [pow_add]
          _ = 714748502 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 781174033) ^ 496 = 569944147 := by
        calc
          (7 : ZMod 781174033) ^ 496 = (7 : ZMod 781174033) ^ (248 + 248) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 248 * (7 : ZMod 781174033) ^ 248 := by rw [pow_add]
          _ = 569944147 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 781174033) ^ 993 = 273820651 := by
        calc
          (7 : ZMod 781174033) ^ 993 = (7 : ZMod 781174033) ^ (496 + 496 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 496 * (7 : ZMod 781174033) ^ 496) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 273820651 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 781174033) ^ 1986 = 447621718 := by
        calc
          (7 : ZMod 781174033) ^ 1986 = (7 : ZMod 781174033) ^ (993 + 993) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 993 * (7 : ZMod 781174033) ^ 993 := by rw [pow_add]
          _ = 447621718 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 781174033) ^ 3973 = 746304334 := by
        calc
          (7 : ZMod 781174033) ^ 3973 = (7 : ZMod 781174033) ^ (1986 + 1986 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 1986 * (7 : ZMod 781174033) ^ 1986) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 746304334 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 781174033) ^ 7946 = 88334167 := by
        calc
          (7 : ZMod 781174033) ^ 7946 = (7 : ZMod 781174033) ^ (3973 + 3973) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 3973 * (7 : ZMod 781174033) ^ 3973 := by rw [pow_add]
          _ = 88334167 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 781174033) ^ 15893 = 387475992 := by
        calc
          (7 : ZMod 781174033) ^ 15893 = (7 : ZMod 781174033) ^ (7946 + 7946 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 7946 * (7 : ZMod 781174033) ^ 7946) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 387475992 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 781174033) ^ 31786 = 313051255 := by
        calc
          (7 : ZMod 781174033) ^ 31786 = (7 : ZMod 781174033) ^ (15893 + 15893) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 15893 * (7 : ZMod 781174033) ^ 15893 := by rw [pow_add]
          _ = 313051255 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 781174033) ^ 63572 = 621272522 := by
        calc
          (7 : ZMod 781174033) ^ 63572 = (7 : ZMod 781174033) ^ (31786 + 31786) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 31786 * (7 : ZMod 781174033) ^ 31786 := by rw [pow_add]
          _ = 621272522 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 781174033) ^ 127144 = 778542972 := by
        calc
          (7 : ZMod 781174033) ^ 127144 = (7 : ZMod 781174033) ^ (63572 + 63572) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 63572 * (7 : ZMod 781174033) ^ 63572 := by rw [pow_add]
          _ = 778542972 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 781174033) ^ 254288 = 498879308 := by
        calc
          (7 : ZMod 781174033) ^ 254288 = (7 : ZMod 781174033) ^ (127144 + 127144) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 127144 * (7 : ZMod 781174033) ^ 127144 := by rw [pow_add]
          _ = 498879308 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 781174033) ^ 508576 = 486247531 := by
        calc
          (7 : ZMod 781174033) ^ 508576 = (7 : ZMod 781174033) ^ (254288 + 254288) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 254288 * (7 : ZMod 781174033) ^ 254288 := by rw [pow_add]
          _ = 486247531 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 781174033) ^ 1017153 = 568607194 := by
        calc
          (7 : ZMod 781174033) ^ 1017153 = (7 : ZMod 781174033) ^ (508576 + 508576 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 508576 * (7 : ZMod 781174033) ^ 508576) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 568607194 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 781174033) ^ 2034307 = 718321658 := by
        calc
          (7 : ZMod 781174033) ^ 2034307 = (7 : ZMod 781174033) ^ (1017153 + 1017153 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 1017153 * (7 : ZMod 781174033) ^ 1017153) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 718321658 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 781174033) ^ 4068614 = 523038635 := by
        calc
          (7 : ZMod 781174033) ^ 4068614 = (7 : ZMod 781174033) ^ (2034307 + 2034307) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 2034307 * (7 : ZMod 781174033) ^ 2034307 := by rw [pow_add]
          _ = 523038635 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 781174033) ^ 8137229 = 309614114 := by
        calc
          (7 : ZMod 781174033) ^ 8137229 = (7 : ZMod 781174033) ^ (4068614 + 4068614 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 4068614 * (7 : ZMod 781174033) ^ 4068614) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 309614114 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 781174033) ^ 16274459 = 211589801 := by
        calc
          (7 : ZMod 781174033) ^ 16274459 = (7 : ZMod 781174033) ^ (8137229 + 8137229 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 8137229 * (7 : ZMod 781174033) ^ 8137229) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 211589801 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 781174033) ^ 32548918 = 12550596 := by
        calc
          (7 : ZMod 781174033) ^ 32548918 = (7 : ZMod 781174033) ^ (16274459 + 16274459) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 16274459 * (7 : ZMod 781174033) ^ 16274459 := by rw [pow_add]
          _ = 12550596 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 781174033) ^ 65097836 = 746767063 := by
        calc
          (7 : ZMod 781174033) ^ 65097836 = (7 : ZMod 781174033) ^ (32548918 + 32548918) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 32548918 * (7 : ZMod 781174033) ^ 32548918 := by rw [pow_add]
          _ = 746767063 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 781174033) ^ 130195672 = 22182654 := by
        calc
          (7 : ZMod 781174033) ^ 130195672 = (7 : ZMod 781174033) ^ (65097836 + 65097836) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 65097836 * (7 : ZMod 781174033) ^ 65097836 := by rw [pow_add]
          _ = 22182654 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 781174033) ^ 260391344 = 22182653 := by
        calc
          (7 : ZMod 781174033) ^ 260391344 = (7 : ZMod 781174033) ^ (130195672 + 130195672) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 130195672 * (7 : ZMod 781174033) ^ 130195672 := by rw [pow_add]
          _ = 22182653 := by rw [factor_1_26]; decide
      change (7 : ZMod 781174033) ^ 260391344 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (7 : ZMod 781174033) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 781174033) ^ 3 = 343 := by
        calc
          (7 : ZMod 781174033) ^ 3 = (7 : ZMod 781174033) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = ((7 : ZMod 781174033) ^ 1 * (7 : ZMod 781174033) ^ 1) * (7 : ZMod 781174033) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 781174033) ^ 6 = 117649 := by
        calc
          (7 : ZMod 781174033) ^ 6 = (7 : ZMod 781174033) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 3 * (7 : ZMod 781174033) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 781174033) ^ 12 = 561328640 := by
        calc
          (7 : ZMod 781174033) ^ 12 = (7 : ZMod 781174033) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 6 * (7 : ZMod 781174033) ^ 6 := by rw [pow_add]
          _ = 561328640 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 781174033) ^ 24 = 100454373 := by
        calc
          (7 : ZMod 781174033) ^ 24 = (7 : ZMod 781174033) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 12 * (7 : ZMod 781174033) ^ 12 := by rw [pow_add]
          _ = 100454373 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 781174033) ^ 48 = 665548442 := by
        calc
          (7 : ZMod 781174033) ^ 48 = (7 : ZMod 781174033) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (7 : ZMod 781174033) ^ n) (by norm_num)
          _ = (7 : ZMod 781174033) ^ 24 * (7 : ZMod 781174033) ^ 24 := by rw [pow_add]
          _ = 665548442 := by rw [factor_2_4]; decide
      change (7 : ZMod 781174033) ^ 48 ≠ 1
      rw [factor_2_5]
      decide

#print axioms prime_lucas_781174033

end TotientTailPeriodKiller
end Erdos249257
