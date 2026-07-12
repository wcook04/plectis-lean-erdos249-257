import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1252706023 : Nat.Prime 1252706023 := by
  apply lucas_primality 1252706023 (6 : ZMod 1252706023)
  ·
      have fermat_0 : (6 : ZMod 1252706023) ^ 1 = 6 := by norm_num
      have fermat_1 : (6 : ZMod 1252706023) ^ 2 = 36 := by
        calc
          (6 : ZMod 1252706023) ^ 2 = (6 : ZMod 1252706023) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 1 * (6 : ZMod 1252706023) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [fermat_0]; decide
      have fermat_2 : (6 : ZMod 1252706023) ^ 4 = 1296 := by
        calc
          (6 : ZMod 1252706023) ^ 4 = (6 : ZMod 1252706023) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 2 * (6 : ZMod 1252706023) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [fermat_1]; decide
      have fermat_3 : (6 : ZMod 1252706023) ^ 9 = 10077696 := by
        calc
          (6 : ZMod 1252706023) ^ 9 = (6 : ZMod 1252706023) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 4 * (6 : ZMod 1252706023) ^ 4) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 10077696 := by rw [fermat_2]; decide
      have fermat_4 : (6 : ZMod 1252706023) ^ 18 = 573971760 := by
        calc
          (6 : ZMod 1252706023) ^ 18 = (6 : ZMod 1252706023) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 9 * (6 : ZMod 1252706023) ^ 9 := by rw [pow_add]
          _ = 573971760 := by rw [fermat_3]; decide
      have fermat_5 : (6 : ZMod 1252706023) ^ 37 = 499415838 := by
        calc
          (6 : ZMod 1252706023) ^ 37 = (6 : ZMod 1252706023) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 18 * (6 : ZMod 1252706023) ^ 18) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 499415838 := by rw [fermat_4]; decide
      have fermat_6 : (6 : ZMod 1252706023) ^ 74 = 1112260015 := by
        calc
          (6 : ZMod 1252706023) ^ 74 = (6 : ZMod 1252706023) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 37 * (6 : ZMod 1252706023) ^ 37 := by rw [pow_add]
          _ = 1112260015 := by rw [fermat_5]; decide
      have fermat_7 : (6 : ZMod 1252706023) ^ 149 = 612475466 := by
        calc
          (6 : ZMod 1252706023) ^ 149 = (6 : ZMod 1252706023) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 74 * (6 : ZMod 1252706023) ^ 74) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 612475466 := by rw [fermat_6]; decide
      have fermat_8 : (6 : ZMod 1252706023) ^ 298 = 569129148 := by
        calc
          (6 : ZMod 1252706023) ^ 298 = (6 : ZMod 1252706023) ^ (149 + 149) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 149 * (6 : ZMod 1252706023) ^ 149 := by rw [pow_add]
          _ = 569129148 := by rw [fermat_7]; decide
      have fermat_9 : (6 : ZMod 1252706023) ^ 597 = 222705127 := by
        calc
          (6 : ZMod 1252706023) ^ 597 = (6 : ZMod 1252706023) ^ (298 + 298 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 298 * (6 : ZMod 1252706023) ^ 298) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 222705127 := by rw [fermat_8]; decide
      have fermat_10 : (6 : ZMod 1252706023) ^ 1194 = 787774125 := by
        calc
          (6 : ZMod 1252706023) ^ 1194 = (6 : ZMod 1252706023) ^ (597 + 597) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 597 * (6 : ZMod 1252706023) ^ 597 := by rw [pow_add]
          _ = 787774125 := by rw [fermat_9]; decide
      have fermat_11 : (6 : ZMod 1252706023) ^ 2389 = 398278255 := by
        calc
          (6 : ZMod 1252706023) ^ 2389 = (6 : ZMod 1252706023) ^ (1194 + 1194 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 1194 * (6 : ZMod 1252706023) ^ 1194) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 398278255 := by rw [fermat_10]; decide
      have fermat_12 : (6 : ZMod 1252706023) ^ 4778 = 891753412 := by
        calc
          (6 : ZMod 1252706023) ^ 4778 = (6 : ZMod 1252706023) ^ (2389 + 2389) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 2389 * (6 : ZMod 1252706023) ^ 2389 := by rw [pow_add]
          _ = 891753412 := by rw [fermat_11]; decide
      have fermat_13 : (6 : ZMod 1252706023) ^ 9557 = 241751355 := by
        calc
          (6 : ZMod 1252706023) ^ 9557 = (6 : ZMod 1252706023) ^ (4778 + 4778 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 4778 * (6 : ZMod 1252706023) ^ 4778) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 241751355 := by rw [fermat_12]; decide
      have fermat_14 : (6 : ZMod 1252706023) ^ 19114 = 912238577 := by
        calc
          (6 : ZMod 1252706023) ^ 19114 = (6 : ZMod 1252706023) ^ (9557 + 9557) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 9557 * (6 : ZMod 1252706023) ^ 9557 := by rw [pow_add]
          _ = 912238577 := by rw [fermat_13]; decide
      have fermat_15 : (6 : ZMod 1252706023) ^ 38229 = 1055821394 := by
        calc
          (6 : ZMod 1252706023) ^ 38229 = (6 : ZMod 1252706023) ^ (19114 + 19114 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 19114 * (6 : ZMod 1252706023) ^ 19114) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 1055821394 := by rw [fermat_14]; decide
      have fermat_16 : (6 : ZMod 1252706023) ^ 76459 = 322771465 := by
        calc
          (6 : ZMod 1252706023) ^ 76459 = (6 : ZMod 1252706023) ^ (38229 + 38229 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 38229 * (6 : ZMod 1252706023) ^ 38229) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 322771465 := by rw [fermat_15]; decide
      have fermat_17 : (6 : ZMod 1252706023) ^ 152918 = 702966994 := by
        calc
          (6 : ZMod 1252706023) ^ 152918 = (6 : ZMod 1252706023) ^ (76459 + 76459) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 76459 * (6 : ZMod 1252706023) ^ 76459 := by rw [pow_add]
          _ = 702966994 := by rw [fermat_16]; decide
      have fermat_18 : (6 : ZMod 1252706023) ^ 305836 = 737609598 := by
        calc
          (6 : ZMod 1252706023) ^ 305836 = (6 : ZMod 1252706023) ^ (152918 + 152918) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 152918 * (6 : ZMod 1252706023) ^ 152918 := by rw [pow_add]
          _ = 737609598 := by rw [fermat_17]; decide
      have fermat_19 : (6 : ZMod 1252706023) ^ 611672 = 52952752 := by
        calc
          (6 : ZMod 1252706023) ^ 611672 = (6 : ZMod 1252706023) ^ (305836 + 305836) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 305836 * (6 : ZMod 1252706023) ^ 305836 := by rw [pow_add]
          _ = 52952752 := by rw [fermat_18]; decide
      have fermat_20 : (6 : ZMod 1252706023) ^ 1223345 = 264866793 := by
        calc
          (6 : ZMod 1252706023) ^ 1223345 = (6 : ZMod 1252706023) ^ (611672 + 611672 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 611672 * (6 : ZMod 1252706023) ^ 611672) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 264866793 := by rw [fermat_19]; decide
      have fermat_21 : (6 : ZMod 1252706023) ^ 2446691 = 891629763 := by
        calc
          (6 : ZMod 1252706023) ^ 2446691 = (6 : ZMod 1252706023) ^ (1223345 + 1223345 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 1223345 * (6 : ZMod 1252706023) ^ 1223345) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 891629763 := by rw [fermat_20]; decide
      have fermat_22 : (6 : ZMod 1252706023) ^ 4893382 = 961668019 := by
        calc
          (6 : ZMod 1252706023) ^ 4893382 = (6 : ZMod 1252706023) ^ (2446691 + 2446691) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 2446691 * (6 : ZMod 1252706023) ^ 2446691 := by rw [pow_add]
          _ = 961668019 := by rw [fermat_21]; decide
      have fermat_23 : (6 : ZMod 1252706023) ^ 9786765 = 242009651 := by
        calc
          (6 : ZMod 1252706023) ^ 9786765 = (6 : ZMod 1252706023) ^ (4893382 + 4893382 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 4893382 * (6 : ZMod 1252706023) ^ 4893382) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 242009651 := by rw [fermat_22]; decide
      have fermat_24 : (6 : ZMod 1252706023) ^ 19573531 = 906090963 := by
        calc
          (6 : ZMod 1252706023) ^ 19573531 = (6 : ZMod 1252706023) ^ (9786765 + 9786765 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 9786765 * (6 : ZMod 1252706023) ^ 9786765) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 906090963 := by rw [fermat_23]; decide
      have fermat_25 : (6 : ZMod 1252706023) ^ 39147063 = 1175692268 := by
        calc
          (6 : ZMod 1252706023) ^ 39147063 = (6 : ZMod 1252706023) ^ (19573531 + 19573531 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 19573531 * (6 : ZMod 1252706023) ^ 19573531) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 1175692268 := by rw [fermat_24]; decide
      have fermat_26 : (6 : ZMod 1252706023) ^ 78294126 = 150933190 := by
        calc
          (6 : ZMod 1252706023) ^ 78294126 = (6 : ZMod 1252706023) ^ (39147063 + 39147063) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 39147063 * (6 : ZMod 1252706023) ^ 39147063 := by rw [pow_add]
          _ = 150933190 := by rw [fermat_25]; decide
      have fermat_27 : (6 : ZMod 1252706023) ^ 156588252 = 519750338 := by
        calc
          (6 : ZMod 1252706023) ^ 156588252 = (6 : ZMod 1252706023) ^ (78294126 + 78294126) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 78294126 * (6 : ZMod 1252706023) ^ 78294126 := by rw [pow_add]
          _ = 519750338 := by rw [fermat_26]; decide
      have fermat_28 : (6 : ZMod 1252706023) ^ 313176505 = 547490786 := by
        calc
          (6 : ZMod 1252706023) ^ 313176505 = (6 : ZMod 1252706023) ^ (156588252 + 156588252 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 156588252 * (6 : ZMod 1252706023) ^ 156588252) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 547490786 := by rw [fermat_27]; decide
      have fermat_29 : (6 : ZMod 1252706023) ^ 626353011 = 1252706022 := by
        calc
          (6 : ZMod 1252706023) ^ 626353011 = (6 : ZMod 1252706023) ^ (313176505 + 313176505 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 313176505 * (6 : ZMod 1252706023) ^ 313176505) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 1252706022 := by rw [fermat_28]; decide
      have fermat_30 : (6 : ZMod 1252706023) ^ 1252706022 = 1 := by
        calc
          (6 : ZMod 1252706023) ^ 1252706022 = (6 : ZMod 1252706023) ^ (626353011 + 626353011) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 626353011 * (6 : ZMod 1252706023) ^ 626353011 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (113, 1), (615883, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (113, 1), (615883, 1)] : List FactorBlock).map factorBlockValue).prod = 1252706023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (6 : ZMod 1252706023) ^ 1 = 6 := by norm_num
      have factor_0_1 : (6 : ZMod 1252706023) ^ 2 = 36 := by
        calc
          (6 : ZMod 1252706023) ^ 2 = (6 : ZMod 1252706023) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 1 * (6 : ZMod 1252706023) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_0_0]; decide
      have factor_0_2 : (6 : ZMod 1252706023) ^ 4 = 1296 := by
        calc
          (6 : ZMod 1252706023) ^ 4 = (6 : ZMod 1252706023) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 2 * (6 : ZMod 1252706023) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_0_1]; decide
      have factor_0_3 : (6 : ZMod 1252706023) ^ 9 = 10077696 := by
        calc
          (6 : ZMod 1252706023) ^ 9 = (6 : ZMod 1252706023) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 4 * (6 : ZMod 1252706023) ^ 4) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 10077696 := by rw [factor_0_2]; decide
      have factor_0_4 : (6 : ZMod 1252706023) ^ 18 = 573971760 := by
        calc
          (6 : ZMod 1252706023) ^ 18 = (6 : ZMod 1252706023) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 9 * (6 : ZMod 1252706023) ^ 9 := by rw [pow_add]
          _ = 573971760 := by rw [factor_0_3]; decide
      have factor_0_5 : (6 : ZMod 1252706023) ^ 37 = 499415838 := by
        calc
          (6 : ZMod 1252706023) ^ 37 = (6 : ZMod 1252706023) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 18 * (6 : ZMod 1252706023) ^ 18) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 499415838 := by rw [factor_0_4]; decide
      have factor_0_6 : (6 : ZMod 1252706023) ^ 74 = 1112260015 := by
        calc
          (6 : ZMod 1252706023) ^ 74 = (6 : ZMod 1252706023) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 37 * (6 : ZMod 1252706023) ^ 37 := by rw [pow_add]
          _ = 1112260015 := by rw [factor_0_5]; decide
      have factor_0_7 : (6 : ZMod 1252706023) ^ 149 = 612475466 := by
        calc
          (6 : ZMod 1252706023) ^ 149 = (6 : ZMod 1252706023) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 74 * (6 : ZMod 1252706023) ^ 74) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 612475466 := by rw [factor_0_6]; decide
      have factor_0_8 : (6 : ZMod 1252706023) ^ 298 = 569129148 := by
        calc
          (6 : ZMod 1252706023) ^ 298 = (6 : ZMod 1252706023) ^ (149 + 149) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 149 * (6 : ZMod 1252706023) ^ 149 := by rw [pow_add]
          _ = 569129148 := by rw [factor_0_7]; decide
      have factor_0_9 : (6 : ZMod 1252706023) ^ 597 = 222705127 := by
        calc
          (6 : ZMod 1252706023) ^ 597 = (6 : ZMod 1252706023) ^ (298 + 298 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 298 * (6 : ZMod 1252706023) ^ 298) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 222705127 := by rw [factor_0_8]; decide
      have factor_0_10 : (6 : ZMod 1252706023) ^ 1194 = 787774125 := by
        calc
          (6 : ZMod 1252706023) ^ 1194 = (6 : ZMod 1252706023) ^ (597 + 597) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 597 * (6 : ZMod 1252706023) ^ 597 := by rw [pow_add]
          _ = 787774125 := by rw [factor_0_9]; decide
      have factor_0_11 : (6 : ZMod 1252706023) ^ 2389 = 398278255 := by
        calc
          (6 : ZMod 1252706023) ^ 2389 = (6 : ZMod 1252706023) ^ (1194 + 1194 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 1194 * (6 : ZMod 1252706023) ^ 1194) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 398278255 := by rw [factor_0_10]; decide
      have factor_0_12 : (6 : ZMod 1252706023) ^ 4778 = 891753412 := by
        calc
          (6 : ZMod 1252706023) ^ 4778 = (6 : ZMod 1252706023) ^ (2389 + 2389) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 2389 * (6 : ZMod 1252706023) ^ 2389 := by rw [pow_add]
          _ = 891753412 := by rw [factor_0_11]; decide
      have factor_0_13 : (6 : ZMod 1252706023) ^ 9557 = 241751355 := by
        calc
          (6 : ZMod 1252706023) ^ 9557 = (6 : ZMod 1252706023) ^ (4778 + 4778 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 4778 * (6 : ZMod 1252706023) ^ 4778) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 241751355 := by rw [factor_0_12]; decide
      have factor_0_14 : (6 : ZMod 1252706023) ^ 19114 = 912238577 := by
        calc
          (6 : ZMod 1252706023) ^ 19114 = (6 : ZMod 1252706023) ^ (9557 + 9557) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 9557 * (6 : ZMod 1252706023) ^ 9557 := by rw [pow_add]
          _ = 912238577 := by rw [factor_0_13]; decide
      have factor_0_15 : (6 : ZMod 1252706023) ^ 38229 = 1055821394 := by
        calc
          (6 : ZMod 1252706023) ^ 38229 = (6 : ZMod 1252706023) ^ (19114 + 19114 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 19114 * (6 : ZMod 1252706023) ^ 19114) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 1055821394 := by rw [factor_0_14]; decide
      have factor_0_16 : (6 : ZMod 1252706023) ^ 76459 = 322771465 := by
        calc
          (6 : ZMod 1252706023) ^ 76459 = (6 : ZMod 1252706023) ^ (38229 + 38229 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 38229 * (6 : ZMod 1252706023) ^ 38229) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 322771465 := by rw [factor_0_15]; decide
      have factor_0_17 : (6 : ZMod 1252706023) ^ 152918 = 702966994 := by
        calc
          (6 : ZMod 1252706023) ^ 152918 = (6 : ZMod 1252706023) ^ (76459 + 76459) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 76459 * (6 : ZMod 1252706023) ^ 76459 := by rw [pow_add]
          _ = 702966994 := by rw [factor_0_16]; decide
      have factor_0_18 : (6 : ZMod 1252706023) ^ 305836 = 737609598 := by
        calc
          (6 : ZMod 1252706023) ^ 305836 = (6 : ZMod 1252706023) ^ (152918 + 152918) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 152918 * (6 : ZMod 1252706023) ^ 152918 := by rw [pow_add]
          _ = 737609598 := by rw [factor_0_17]; decide
      have factor_0_19 : (6 : ZMod 1252706023) ^ 611672 = 52952752 := by
        calc
          (6 : ZMod 1252706023) ^ 611672 = (6 : ZMod 1252706023) ^ (305836 + 305836) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 305836 * (6 : ZMod 1252706023) ^ 305836 := by rw [pow_add]
          _ = 52952752 := by rw [factor_0_18]; decide
      have factor_0_20 : (6 : ZMod 1252706023) ^ 1223345 = 264866793 := by
        calc
          (6 : ZMod 1252706023) ^ 1223345 = (6 : ZMod 1252706023) ^ (611672 + 611672 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 611672 * (6 : ZMod 1252706023) ^ 611672) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 264866793 := by rw [factor_0_19]; decide
      have factor_0_21 : (6 : ZMod 1252706023) ^ 2446691 = 891629763 := by
        calc
          (6 : ZMod 1252706023) ^ 2446691 = (6 : ZMod 1252706023) ^ (1223345 + 1223345 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 1223345 * (6 : ZMod 1252706023) ^ 1223345) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 891629763 := by rw [factor_0_20]; decide
      have factor_0_22 : (6 : ZMod 1252706023) ^ 4893382 = 961668019 := by
        calc
          (6 : ZMod 1252706023) ^ 4893382 = (6 : ZMod 1252706023) ^ (2446691 + 2446691) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 2446691 * (6 : ZMod 1252706023) ^ 2446691 := by rw [pow_add]
          _ = 961668019 := by rw [factor_0_21]; decide
      have factor_0_23 : (6 : ZMod 1252706023) ^ 9786765 = 242009651 := by
        calc
          (6 : ZMod 1252706023) ^ 9786765 = (6 : ZMod 1252706023) ^ (4893382 + 4893382 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 4893382 * (6 : ZMod 1252706023) ^ 4893382) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 242009651 := by rw [factor_0_22]; decide
      have factor_0_24 : (6 : ZMod 1252706023) ^ 19573531 = 906090963 := by
        calc
          (6 : ZMod 1252706023) ^ 19573531 = (6 : ZMod 1252706023) ^ (9786765 + 9786765 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 9786765 * (6 : ZMod 1252706023) ^ 9786765) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 906090963 := by rw [factor_0_23]; decide
      have factor_0_25 : (6 : ZMod 1252706023) ^ 39147063 = 1175692268 := by
        calc
          (6 : ZMod 1252706023) ^ 39147063 = (6 : ZMod 1252706023) ^ (19573531 + 19573531 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 19573531 * (6 : ZMod 1252706023) ^ 19573531) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 1175692268 := by rw [factor_0_24]; decide
      have factor_0_26 : (6 : ZMod 1252706023) ^ 78294126 = 150933190 := by
        calc
          (6 : ZMod 1252706023) ^ 78294126 = (6 : ZMod 1252706023) ^ (39147063 + 39147063) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 39147063 * (6 : ZMod 1252706023) ^ 39147063 := by rw [pow_add]
          _ = 150933190 := by rw [factor_0_25]; decide
      have factor_0_27 : (6 : ZMod 1252706023) ^ 156588252 = 519750338 := by
        calc
          (6 : ZMod 1252706023) ^ 156588252 = (6 : ZMod 1252706023) ^ (78294126 + 78294126) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 78294126 * (6 : ZMod 1252706023) ^ 78294126 := by rw [pow_add]
          _ = 519750338 := by rw [factor_0_26]; decide
      have factor_0_28 : (6 : ZMod 1252706023) ^ 313176505 = 547490786 := by
        calc
          (6 : ZMod 1252706023) ^ 313176505 = (6 : ZMod 1252706023) ^ (156588252 + 156588252 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 156588252 * (6 : ZMod 1252706023) ^ 156588252) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 547490786 := by rw [factor_0_27]; decide
      have factor_0_29 : (6 : ZMod 1252706023) ^ 626353011 = 1252706022 := by
        calc
          (6 : ZMod 1252706023) ^ 626353011 = (6 : ZMod 1252706023) ^ (313176505 + 313176505 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 313176505 * (6 : ZMod 1252706023) ^ 313176505) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 1252706022 := by rw [factor_0_28]; decide
      change (6 : ZMod 1252706023) ^ 626353011 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (6 : ZMod 1252706023) ^ 1 = 6 := by norm_num
      have factor_1_1 : (6 : ZMod 1252706023) ^ 3 = 216 := by
        calc
          (6 : ZMod 1252706023) ^ 3 = (6 : ZMod 1252706023) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 1 * (6 : ZMod 1252706023) ^ 1) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_1_0]; decide
      have factor_1_2 : (6 : ZMod 1252706023) ^ 6 = 46656 := by
        calc
          (6 : ZMod 1252706023) ^ 6 = (6 : ZMod 1252706023) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 3 * (6 : ZMod 1252706023) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [factor_1_1]; decide
      have factor_1_3 : (6 : ZMod 1252706023) ^ 12 = 924076313 := by
        calc
          (6 : ZMod 1252706023) ^ 12 = (6 : ZMod 1252706023) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 6 * (6 : ZMod 1252706023) ^ 6 := by rw [pow_add]
          _ = 924076313 := by rw [factor_1_2]; decide
      have factor_1_4 : (6 : ZMod 1252706023) ^ 24 = 129780889 := by
        calc
          (6 : ZMod 1252706023) ^ 24 = (6 : ZMod 1252706023) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 12 * (6 : ZMod 1252706023) ^ 12 := by rw [pow_add]
          _ = 129780889 := by rw [factor_1_3]; decide
      have factor_1_5 : (6 : ZMod 1252706023) ^ 49 = 484188729 := by
        calc
          (6 : ZMod 1252706023) ^ 49 = (6 : ZMod 1252706023) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 24 * (6 : ZMod 1252706023) ^ 24) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 484188729 := by rw [factor_1_4]; decide
      have factor_1_6 : (6 : ZMod 1252706023) ^ 99 = 1005326266 := by
        calc
          (6 : ZMod 1252706023) ^ 99 = (6 : ZMod 1252706023) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 49 * (6 : ZMod 1252706023) ^ 49) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 1005326266 := by rw [factor_1_5]; decide
      have factor_1_7 : (6 : ZMod 1252706023) ^ 199 = 566295928 := by
        calc
          (6 : ZMod 1252706023) ^ 199 = (6 : ZMod 1252706023) ^ (99 + 99 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 99 * (6 : ZMod 1252706023) ^ 99) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 566295928 := by rw [factor_1_6]; decide
      have factor_1_8 : (6 : ZMod 1252706023) ^ 398 = 1027685751 := by
        calc
          (6 : ZMod 1252706023) ^ 398 = (6 : ZMod 1252706023) ^ (199 + 199) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 199 * (6 : ZMod 1252706023) ^ 199 := by rw [pow_add]
          _ = 1027685751 := by rw [factor_1_7]; decide
      have factor_1_9 : (6 : ZMod 1252706023) ^ 796 = 913322676 := by
        calc
          (6 : ZMod 1252706023) ^ 796 = (6 : ZMod 1252706023) ^ (398 + 398) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 398 * (6 : ZMod 1252706023) ^ 398 := by rw [pow_add]
          _ = 913322676 := by rw [factor_1_8]; decide
      have factor_1_10 : (6 : ZMod 1252706023) ^ 1592 = 24075032 := by
        calc
          (6 : ZMod 1252706023) ^ 1592 = (6 : ZMod 1252706023) ^ (796 + 796) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 796 * (6 : ZMod 1252706023) ^ 796 := by rw [pow_add]
          _ = 24075032 := by rw [factor_1_9]; decide
      have factor_1_11 : (6 : ZMod 1252706023) ^ 3185 = 793531752 := by
        calc
          (6 : ZMod 1252706023) ^ 3185 = (6 : ZMod 1252706023) ^ (1592 + 1592 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 1592 * (6 : ZMod 1252706023) ^ 1592) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 793531752 := by rw [factor_1_10]; decide
      have factor_1_12 : (6 : ZMod 1252706023) ^ 6371 = 142462316 := by
        calc
          (6 : ZMod 1252706023) ^ 6371 = (6 : ZMod 1252706023) ^ (3185 + 3185 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 3185 * (6 : ZMod 1252706023) ^ 3185) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 142462316 := by rw [factor_1_11]; decide
      have factor_1_13 : (6 : ZMod 1252706023) ^ 12743 = 500716745 := by
        calc
          (6 : ZMod 1252706023) ^ 12743 = (6 : ZMod 1252706023) ^ (6371 + 6371 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 6371 * (6 : ZMod 1252706023) ^ 6371) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 500716745 := by rw [factor_1_12]; decide
      have factor_1_14 : (6 : ZMod 1252706023) ^ 25486 = 71628628 := by
        calc
          (6 : ZMod 1252706023) ^ 25486 = (6 : ZMod 1252706023) ^ (12743 + 12743) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 12743 * (6 : ZMod 1252706023) ^ 12743 := by rw [pow_add]
          _ = 71628628 := by rw [factor_1_13]; decide
      have factor_1_15 : (6 : ZMod 1252706023) ^ 50972 = 1146296181 := by
        calc
          (6 : ZMod 1252706023) ^ 50972 = (6 : ZMod 1252706023) ^ (25486 + 25486) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 25486 * (6 : ZMod 1252706023) ^ 25486 := by rw [pow_add]
          _ = 1146296181 := by rw [factor_1_14]; decide
      have factor_1_16 : (6 : ZMod 1252706023) ^ 101945 = 408688896 := by
        calc
          (6 : ZMod 1252706023) ^ 101945 = (6 : ZMod 1252706023) ^ (50972 + 50972 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 50972 * (6 : ZMod 1252706023) ^ 50972) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 408688896 := by rw [factor_1_15]; decide
      have factor_1_17 : (6 : ZMod 1252706023) ^ 203890 = 1248853889 := by
        calc
          (6 : ZMod 1252706023) ^ 203890 = (6 : ZMod 1252706023) ^ (101945 + 101945) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 101945 * (6 : ZMod 1252706023) ^ 101945 := by rw [pow_add]
          _ = 1248853889 := by rw [factor_1_16]; decide
      have factor_1_18 : (6 : ZMod 1252706023) ^ 407781 = 42951057 := by
        calc
          (6 : ZMod 1252706023) ^ 407781 = (6 : ZMod 1252706023) ^ (203890 + 203890 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 203890 * (6 : ZMod 1252706023) ^ 203890) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 42951057 := by rw [factor_1_17]; decide
      have factor_1_19 : (6 : ZMod 1252706023) ^ 815563 = 942704277 := by
        calc
          (6 : ZMod 1252706023) ^ 815563 = (6 : ZMod 1252706023) ^ (407781 + 407781 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 407781 * (6 : ZMod 1252706023) ^ 407781) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 942704277 := by rw [factor_1_18]; decide
      have factor_1_20 : (6 : ZMod 1252706023) ^ 1631127 = 683325754 := by
        calc
          (6 : ZMod 1252706023) ^ 1631127 = (6 : ZMod 1252706023) ^ (815563 + 815563 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 815563 * (6 : ZMod 1252706023) ^ 815563) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 683325754 := by rw [factor_1_19]; decide
      have factor_1_21 : (6 : ZMod 1252706023) ^ 3262255 = 157710290 := by
        calc
          (6 : ZMod 1252706023) ^ 3262255 = (6 : ZMod 1252706023) ^ (1631127 + 1631127 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 1631127 * (6 : ZMod 1252706023) ^ 1631127) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 157710290 := by rw [factor_1_20]; decide
      have factor_1_22 : (6 : ZMod 1252706023) ^ 6524510 = 1113448065 := by
        calc
          (6 : ZMod 1252706023) ^ 6524510 = (6 : ZMod 1252706023) ^ (3262255 + 3262255) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 3262255 * (6 : ZMod 1252706023) ^ 3262255 := by rw [pow_add]
          _ = 1113448065 := by rw [factor_1_21]; decide
      have factor_1_23 : (6 : ZMod 1252706023) ^ 13049021 = 1374581 := by
        calc
          (6 : ZMod 1252706023) ^ 13049021 = (6 : ZMod 1252706023) ^ (6524510 + 6524510 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 6524510 * (6 : ZMod 1252706023) ^ 6524510) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 1374581 := by rw [factor_1_22]; decide
      have factor_1_24 : (6 : ZMod 1252706023) ^ 26098042 = 392242877 := by
        calc
          (6 : ZMod 1252706023) ^ 26098042 = (6 : ZMod 1252706023) ^ (13049021 + 13049021) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 13049021 * (6 : ZMod 1252706023) ^ 13049021 := by rw [pow_add]
          _ = 392242877 := by rw [factor_1_23]; decide
      have factor_1_25 : (6 : ZMod 1252706023) ^ 52196084 = 783524006 := by
        calc
          (6 : ZMod 1252706023) ^ 52196084 = (6 : ZMod 1252706023) ^ (26098042 + 26098042) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 26098042 * (6 : ZMod 1252706023) ^ 26098042 := by rw [pow_add]
          _ = 783524006 := by rw [factor_1_24]; decide
      have factor_1_26 : (6 : ZMod 1252706023) ^ 104392168 = 437219312 := by
        calc
          (6 : ZMod 1252706023) ^ 104392168 = (6 : ZMod 1252706023) ^ (52196084 + 52196084) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 52196084 * (6 : ZMod 1252706023) ^ 52196084 := by rw [pow_add]
          _ = 437219312 := by rw [factor_1_25]; decide
      have factor_1_27 : (6 : ZMod 1252706023) ^ 208784337 = 981445795 := by
        calc
          (6 : ZMod 1252706023) ^ 208784337 = (6 : ZMod 1252706023) ^ (104392168 + 104392168 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 104392168 * (6 : ZMod 1252706023) ^ 104392168) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 981445795 := by rw [factor_1_26]; decide
      have factor_1_28 : (6 : ZMod 1252706023) ^ 417568674 = 981445794 := by
        calc
          (6 : ZMod 1252706023) ^ 417568674 = (6 : ZMod 1252706023) ^ (208784337 + 208784337) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 208784337 * (6 : ZMod 1252706023) ^ 208784337 := by rw [pow_add]
          _ = 981445794 := by rw [factor_1_27]; decide
      change (6 : ZMod 1252706023) ^ 417568674 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (6 : ZMod 1252706023) ^ 1 = 6 := by norm_num
      have factor_2_1 : (6 : ZMod 1252706023) ^ 2 = 36 := by
        calc
          (6 : ZMod 1252706023) ^ 2 = (6 : ZMod 1252706023) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 1 * (6 : ZMod 1252706023) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_2_0]; decide
      have factor_2_2 : (6 : ZMod 1252706023) ^ 5 = 7776 := by
        calc
          (6 : ZMod 1252706023) ^ 5 = (6 : ZMod 1252706023) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 2 * (6 : ZMod 1252706023) ^ 2) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_2_1]; decide
      have factor_2_3 : (6 : ZMod 1252706023) ^ 10 = 60466176 := by
        calc
          (6 : ZMod 1252706023) ^ 10 = (6 : ZMod 1252706023) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 5 * (6 : ZMod 1252706023) ^ 5 := by rw [pow_add]
          _ = 60466176 := by rw [factor_2_2]; decide
      have factor_2_4 : (6 : ZMod 1252706023) ^ 21 = 1212709906 := by
        calc
          (6 : ZMod 1252706023) ^ 21 = (6 : ZMod 1252706023) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 10 * (6 : ZMod 1252706023) ^ 10) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 1212709906 := by rw [factor_2_3]; decide
      have factor_2_5 : (6 : ZMod 1252706023) ^ 42 = 68884988 := by
        calc
          (6 : ZMod 1252706023) ^ 42 = (6 : ZMod 1252706023) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 21 * (6 : ZMod 1252706023) ^ 21 := by rw [pow_add]
          _ = 68884988 := by rw [factor_2_4]; decide
      have factor_2_6 : (6 : ZMod 1252706023) ^ 84 = 142060145 := by
        calc
          (6 : ZMod 1252706023) ^ 84 = (6 : ZMod 1252706023) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 42 * (6 : ZMod 1252706023) ^ 42 := by rw [pow_add]
          _ = 142060145 := by rw [factor_2_5]; decide
      have factor_2_7 : (6 : ZMod 1252706023) ^ 169 = 973117185 := by
        calc
          (6 : ZMod 1252706023) ^ 169 = (6 : ZMod 1252706023) ^ (84 + 84 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 84 * (6 : ZMod 1252706023) ^ 84) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 973117185 := by rw [factor_2_6]; decide
      have factor_2_8 : (6 : ZMod 1252706023) ^ 338 = 204282740 := by
        calc
          (6 : ZMod 1252706023) ^ 338 = (6 : ZMod 1252706023) ^ (169 + 169) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 169 * (6 : ZMod 1252706023) ^ 169 := by rw [pow_add]
          _ = 204282740 := by rw [factor_2_7]; decide
      have factor_2_9 : (6 : ZMod 1252706023) ^ 676 = 778409841 := by
        calc
          (6 : ZMod 1252706023) ^ 676 = (6 : ZMod 1252706023) ^ (338 + 338) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 338 * (6 : ZMod 1252706023) ^ 338 := by rw [pow_add]
          _ = 778409841 := by rw [factor_2_8]; decide
      have factor_2_10 : (6 : ZMod 1252706023) ^ 1353 = 519606141 := by
        calc
          (6 : ZMod 1252706023) ^ 1353 = (6 : ZMod 1252706023) ^ (676 + 676 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 676 * (6 : ZMod 1252706023) ^ 676) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 519606141 := by rw [factor_2_9]; decide
      have factor_2_11 : (6 : ZMod 1252706023) ^ 2706 = 83363124 := by
        calc
          (6 : ZMod 1252706023) ^ 2706 = (6 : ZMod 1252706023) ^ (1353 + 1353) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 1353 * (6 : ZMod 1252706023) ^ 1353 := by rw [pow_add]
          _ = 83363124 := by rw [factor_2_10]; decide
      have factor_2_12 : (6 : ZMod 1252706023) ^ 5413 = 1126900657 := by
        calc
          (6 : ZMod 1252706023) ^ 5413 = (6 : ZMod 1252706023) ^ (2706 + 2706 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 2706 * (6 : ZMod 1252706023) ^ 2706) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 1126900657 := by rw [factor_2_11]; decide
      have factor_2_13 : (6 : ZMod 1252706023) ^ 10826 = 317660413 := by
        calc
          (6 : ZMod 1252706023) ^ 10826 = (6 : ZMod 1252706023) ^ (5413 + 5413) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 5413 * (6 : ZMod 1252706023) ^ 5413 := by rw [pow_add]
          _ = 317660413 := by rw [factor_2_12]; decide
      have factor_2_14 : (6 : ZMod 1252706023) ^ 21652 = 823557602 := by
        calc
          (6 : ZMod 1252706023) ^ 21652 = (6 : ZMod 1252706023) ^ (10826 + 10826) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 10826 * (6 : ZMod 1252706023) ^ 10826 := by rw [pow_add]
          _ = 823557602 := by rw [factor_2_13]; decide
      have factor_2_15 : (6 : ZMod 1252706023) ^ 43304 = 1158541374 := by
        calc
          (6 : ZMod 1252706023) ^ 43304 = (6 : ZMod 1252706023) ^ (21652 + 21652) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 21652 * (6 : ZMod 1252706023) ^ 21652 := by rw [pow_add]
          _ = 1158541374 := by rw [factor_2_14]; decide
      have factor_2_16 : (6 : ZMod 1252706023) ^ 86608 = 934227198 := by
        calc
          (6 : ZMod 1252706023) ^ 86608 = (6 : ZMod 1252706023) ^ (43304 + 43304) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 43304 * (6 : ZMod 1252706023) ^ 43304 := by rw [pow_add]
          _ = 934227198 := by rw [factor_2_15]; decide
      have factor_2_17 : (6 : ZMod 1252706023) ^ 173217 = 1118693148 := by
        calc
          (6 : ZMod 1252706023) ^ 173217 = (6 : ZMod 1252706023) ^ (86608 + 86608 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 86608 * (6 : ZMod 1252706023) ^ 86608) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 1118693148 := by rw [factor_2_16]; decide
      have factor_2_18 : (6 : ZMod 1252706023) ^ 346434 = 702081573 := by
        calc
          (6 : ZMod 1252706023) ^ 346434 = (6 : ZMod 1252706023) ^ (173217 + 173217) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 173217 * (6 : ZMod 1252706023) ^ 173217 := by rw [pow_add]
          _ = 702081573 := by rw [factor_2_17]; decide
      have factor_2_19 : (6 : ZMod 1252706023) ^ 692868 = 1076397145 := by
        calc
          (6 : ZMod 1252706023) ^ 692868 = (6 : ZMod 1252706023) ^ (346434 + 346434) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 346434 * (6 : ZMod 1252706023) ^ 346434 := by rw [pow_add]
          _ = 1076397145 := by rw [factor_2_18]; decide
      have factor_2_20 : (6 : ZMod 1252706023) ^ 1385736 = 333465710 := by
        calc
          (6 : ZMod 1252706023) ^ 1385736 = (6 : ZMod 1252706023) ^ (692868 + 692868) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 692868 * (6 : ZMod 1252706023) ^ 692868 := by rw [pow_add]
          _ = 333465710 := by rw [factor_2_19]; decide
      have factor_2_21 : (6 : ZMod 1252706023) ^ 2771473 = 967045887 := by
        calc
          (6 : ZMod 1252706023) ^ 2771473 = (6 : ZMod 1252706023) ^ (1385736 + 1385736 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 1385736 * (6 : ZMod 1252706023) ^ 1385736) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 967045887 := by rw [factor_2_20]; decide
      have factor_2_22 : (6 : ZMod 1252706023) ^ 5542947 = 778436193 := by
        calc
          (6 : ZMod 1252706023) ^ 5542947 = (6 : ZMod 1252706023) ^ (2771473 + 2771473 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 2771473 * (6 : ZMod 1252706023) ^ 2771473) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 778436193 := by rw [factor_2_21]; decide
      have factor_2_23 : (6 : ZMod 1252706023) ^ 11085894 = 597388753 := by
        calc
          (6 : ZMod 1252706023) ^ 11085894 = (6 : ZMod 1252706023) ^ (5542947 + 5542947) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 5542947 * (6 : ZMod 1252706023) ^ 5542947 := by rw [pow_add]
          _ = 597388753 := by rw [factor_2_22]; decide
      change (6 : ZMod 1252706023) ^ 11085894 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (6 : ZMod 1252706023) ^ 1 = 6 := by norm_num
      have factor_3_1 : (6 : ZMod 1252706023) ^ 3 = 216 := by
        calc
          (6 : ZMod 1252706023) ^ 3 = (6 : ZMod 1252706023) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 1 * (6 : ZMod 1252706023) ^ 1) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_3_0]; decide
      have factor_3_2 : (6 : ZMod 1252706023) ^ 7 = 279936 := by
        calc
          (6 : ZMod 1252706023) ^ 7 = (6 : ZMod 1252706023) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 3 * (6 : ZMod 1252706023) ^ 3) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 279936 := by rw [factor_3_1]; decide
      have factor_3_3 : (6 : ZMod 1252706023) ^ 15 = 420225951 := by
        calc
          (6 : ZMod 1252706023) ^ 15 = (6 : ZMod 1252706023) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 7 * (6 : ZMod 1252706023) ^ 7) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 420225951 := by rw [factor_3_2]; decide
      have factor_3_4 : (6 : ZMod 1252706023) ^ 31 = 615570081 := by
        calc
          (6 : ZMod 1252706023) ^ 31 = (6 : ZMod 1252706023) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 15 * (6 : ZMod 1252706023) ^ 15) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 615570081 := by rw [factor_3_3]; decide
      have factor_3_5 : (6 : ZMod 1252706023) ^ 63 = 688563339 := by
        calc
          (6 : ZMod 1252706023) ^ 63 = (6 : ZMod 1252706023) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 31 * (6 : ZMod 1252706023) ^ 31) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 688563339 := by rw [factor_3_4]; decide
      have factor_3_6 : (6 : ZMod 1252706023) ^ 127 = 845431716 := by
        calc
          (6 : ZMod 1252706023) ^ 127 = (6 : ZMod 1252706023) ^ (63 + 63 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 63 * (6 : ZMod 1252706023) ^ 63) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 845431716 := by rw [factor_3_5]; decide
      have factor_3_7 : (6 : ZMod 1252706023) ^ 254 = 776019683 := by
        calc
          (6 : ZMod 1252706023) ^ 254 = (6 : ZMod 1252706023) ^ (127 + 127) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 127 * (6 : ZMod 1252706023) ^ 127 := by rw [pow_add]
          _ = 776019683 := by rw [factor_3_6]; decide
      have factor_3_8 : (6 : ZMod 1252706023) ^ 508 = 445513678 := by
        calc
          (6 : ZMod 1252706023) ^ 508 = (6 : ZMod 1252706023) ^ (254 + 254) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 254 * (6 : ZMod 1252706023) ^ 254 := by rw [pow_add]
          _ = 445513678 := by rw [factor_3_7]; decide
      have factor_3_9 : (6 : ZMod 1252706023) ^ 1017 = 867317073 := by
        calc
          (6 : ZMod 1252706023) ^ 1017 = (6 : ZMod 1252706023) ^ (508 + 508 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = ((6 : ZMod 1252706023) ^ 508 * (6 : ZMod 1252706023) ^ 508) * (6 : ZMod 1252706023) := by rw [pow_succ, pow_add]
          _ = 867317073 := by rw [factor_3_8]; decide
      have factor_3_10 : (6 : ZMod 1252706023) ^ 2034 = 952676442 := by
        calc
          (6 : ZMod 1252706023) ^ 2034 = (6 : ZMod 1252706023) ^ (1017 + 1017) :=
            congrArg (fun n : ℕ => (6 : ZMod 1252706023) ^ n) (by norm_num)
          _ = (6 : ZMod 1252706023) ^ 1017 * (6 : ZMod 1252706023) ^ 1017 := by rw [pow_add]
          _ = 952676442 := by rw [factor_3_9]; decide
      change (6 : ZMod 1252706023) ^ 2034 ≠ 1
      rw [factor_3_10]
      decide

#print axioms prime_lucas_1252706023

end TotientTailPeriodKiller
end Erdos249257
