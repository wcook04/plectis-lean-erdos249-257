import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_104258953 : Nat.Prime 104258953 := by
  apply lucas_primality 104258953 (13 : ZMod 104258953)
  ·
      have fermat_0 : (13 : ZMod 104258953) ^ 1 = 13 := by norm_num
      have fermat_1 : (13 : ZMod 104258953) ^ 3 = 2197 := by
        calc
          (13 : ZMod 104258953) ^ 3 = (13 : ZMod 104258953) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 1 * (13 : ZMod 104258953) ^ 1) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [fermat_0]; decide
      have fermat_2 : (13 : ZMod 104258953) ^ 6 = 4826809 := by
        calc
          (13 : ZMod 104258953) ^ 6 = (13 : ZMod 104258953) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 3 * (13 : ZMod 104258953) ^ 3 := by rw [pow_add]
          _ = 4826809 := by rw [fermat_1]; decide
      have fermat_3 : (13 : ZMod 104258953) ^ 12 = 66708242 := by
        calc
          (13 : ZMod 104258953) ^ 12 = (13 : ZMod 104258953) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 6 * (13 : ZMod 104258953) ^ 6 := by rw [pow_add]
          _ = 66708242 := by rw [fermat_2]; decide
      have fermat_4 : (13 : ZMod 104258953) ^ 24 = 56773559 := by
        calc
          (13 : ZMod 104258953) ^ 24 = (13 : ZMod 104258953) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 12 * (13 : ZMod 104258953) ^ 12 := by rw [pow_add]
          _ = 56773559 := by rw [fermat_3]; decide
      have fermat_5 : (13 : ZMod 104258953) ^ 49 = 52379070 := by
        calc
          (13 : ZMod 104258953) ^ 49 = (13 : ZMod 104258953) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 24 * (13 : ZMod 104258953) ^ 24) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 52379070 := by rw [fermat_4]; decide
      have fermat_6 : (13 : ZMod 104258953) ^ 99 = 54545460 := by
        calc
          (13 : ZMod 104258953) ^ 99 = (13 : ZMod 104258953) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 49 * (13 : ZMod 104258953) ^ 49) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 54545460 := by rw [fermat_5]; decide
      have fermat_7 : (13 : ZMod 104258953) ^ 198 = 12723829 := by
        calc
          (13 : ZMod 104258953) ^ 198 = (13 : ZMod 104258953) ^ (99 + 99) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 99 * (13 : ZMod 104258953) ^ 99 := by rw [pow_add]
          _ = 12723829 := by rw [fermat_6]; decide
      have fermat_8 : (13 : ZMod 104258953) ^ 397 = 51325691 := by
        calc
          (13 : ZMod 104258953) ^ 397 = (13 : ZMod 104258953) ^ (198 + 198 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 198 * (13 : ZMod 104258953) ^ 198) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 51325691 := by rw [fermat_7]; decide
      have fermat_9 : (13 : ZMod 104258953) ^ 795 = 5889621 := by
        calc
          (13 : ZMod 104258953) ^ 795 = (13 : ZMod 104258953) ^ (397 + 397 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 397 * (13 : ZMod 104258953) ^ 397) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 5889621 := by rw [fermat_8]; decide
      have fermat_10 : (13 : ZMod 104258953) ^ 1590 = 56306823 := by
        calc
          (13 : ZMod 104258953) ^ 1590 = (13 : ZMod 104258953) ^ (795 + 795) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 795 * (13 : ZMod 104258953) ^ 795 := by rw [pow_add]
          _ = 56306823 := by rw [fermat_9]; decide
      have fermat_11 : (13 : ZMod 104258953) ^ 3181 = 101873444 := by
        calc
          (13 : ZMod 104258953) ^ 3181 = (13 : ZMod 104258953) ^ (1590 + 1590 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 1590 * (13 : ZMod 104258953) ^ 1590) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 101873444 := by rw [fermat_10]; decide
      have fermat_12 : (13 : ZMod 104258953) ^ 6363 = 91731561 := by
        calc
          (13 : ZMod 104258953) ^ 6363 = (13 : ZMod 104258953) ^ (3181 + 3181 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 3181 * (13 : ZMod 104258953) ^ 3181) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 91731561 := by rw [fermat_11]; decide
      have fermat_13 : (13 : ZMod 104258953) ^ 12726 = 74095273 := by
        calc
          (13 : ZMod 104258953) ^ 12726 = (13 : ZMod 104258953) ^ (6363 + 6363) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 6363 * (13 : ZMod 104258953) ^ 6363 := by rw [pow_add]
          _ = 74095273 := by rw [fermat_12]; decide
      have fermat_14 : (13 : ZMod 104258953) ^ 25453 = 87458243 := by
        calc
          (13 : ZMod 104258953) ^ 25453 = (13 : ZMod 104258953) ^ (12726 + 12726 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 12726 * (13 : ZMod 104258953) ^ 12726) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 87458243 := by rw [fermat_13]; decide
      have fermat_15 : (13 : ZMod 104258953) ^ 50907 = 1602656 := by
        calc
          (13 : ZMod 104258953) ^ 50907 = (13 : ZMod 104258953) ^ (25453 + 25453 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 25453 * (13 : ZMod 104258953) ^ 25453) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 1602656 := by rw [fermat_14]; decide
      have fermat_16 : (13 : ZMod 104258953) ^ 101815 = 87723823 := by
        calc
          (13 : ZMod 104258953) ^ 101815 = (13 : ZMod 104258953) ^ (50907 + 50907 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 50907 * (13 : ZMod 104258953) ^ 50907) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 87723823 := by rw [fermat_15]; decide
      have fermat_17 : (13 : ZMod 104258953) ^ 203630 = 73367499 := by
        calc
          (13 : ZMod 104258953) ^ 203630 = (13 : ZMod 104258953) ^ (101815 + 101815) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 101815 * (13 : ZMod 104258953) ^ 101815 := by rw [pow_add]
          _ = 73367499 := by rw [fermat_16]; decide
      have fermat_18 : (13 : ZMod 104258953) ^ 407261 = 79330910 := by
        calc
          (13 : ZMod 104258953) ^ 407261 = (13 : ZMod 104258953) ^ (203630 + 203630 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 203630 * (13 : ZMod 104258953) ^ 203630) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 79330910 := by rw [fermat_17]; decide
      have fermat_19 : (13 : ZMod 104258953) ^ 814523 = 57336473 := by
        calc
          (13 : ZMod 104258953) ^ 814523 = (13 : ZMod 104258953) ^ (407261 + 407261 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 407261 * (13 : ZMod 104258953) ^ 407261) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 57336473 := by rw [fermat_18]; decide
      have fermat_20 : (13 : ZMod 104258953) ^ 1629046 = 37240718 := by
        calc
          (13 : ZMod 104258953) ^ 1629046 = (13 : ZMod 104258953) ^ (814523 + 814523) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 814523 * (13 : ZMod 104258953) ^ 814523 := by rw [pow_add]
          _ = 37240718 := by rw [fermat_19]; decide
      have fermat_21 : (13 : ZMod 104258953) ^ 3258092 = 30514843 := by
        calc
          (13 : ZMod 104258953) ^ 3258092 = (13 : ZMod 104258953) ^ (1629046 + 1629046) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 1629046 * (13 : ZMod 104258953) ^ 1629046 := by rw [pow_add]
          _ = 30514843 := by rw [fermat_20]; decide
      have fermat_22 : (13 : ZMod 104258953) ^ 6516184 = 63201156 := by
        calc
          (13 : ZMod 104258953) ^ 6516184 = (13 : ZMod 104258953) ^ (3258092 + 3258092) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 3258092 * (13 : ZMod 104258953) ^ 3258092 := by rw [pow_add]
          _ = 63201156 := by rw [fermat_21]; decide
      have fermat_23 : (13 : ZMod 104258953) ^ 13032369 = 76857619 := by
        calc
          (13 : ZMod 104258953) ^ 13032369 = (13 : ZMod 104258953) ^ (6516184 + 6516184 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 6516184 * (13 : ZMod 104258953) ^ 6516184) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 76857619 := by rw [fermat_22]; decide
      have fermat_24 : (13 : ZMod 104258953) ^ 26064738 = 56652555 := by
        calc
          (13 : ZMod 104258953) ^ 26064738 = (13 : ZMod 104258953) ^ (13032369 + 13032369) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 13032369 * (13 : ZMod 104258953) ^ 13032369 := by rw [pow_add]
          _ = 56652555 := by rw [fermat_23]; decide
      have fermat_25 : (13 : ZMod 104258953) ^ 52129476 = 104258952 := by
        calc
          (13 : ZMod 104258953) ^ 52129476 = (13 : ZMod 104258953) ^ (26064738 + 26064738) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 26064738 * (13 : ZMod 104258953) ^ 26064738 := by rw [pow_add]
          _ = 104258952 := by rw [fermat_24]; decide
      have fermat_26 : (13 : ZMod 104258953) ^ 104258952 = 1 := by
        calc
          (13 : ZMod 104258953) ^ 104258952 = (13 : ZMod 104258953) ^ (52129476 + 52129476) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 52129476 * (13 : ZMod 104258953) ^ 52129476 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (7, 1), (31, 1), (6673, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (7, 1), (31, 1), (6673, 1)] : List FactorBlock).map factorBlockValue).prod = 104258953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (13 : ZMod 104258953) ^ 1 = 13 := by norm_num
      have factor_0_1 : (13 : ZMod 104258953) ^ 3 = 2197 := by
        calc
          (13 : ZMod 104258953) ^ 3 = (13 : ZMod 104258953) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 1 * (13 : ZMod 104258953) ^ 1) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_0_0]; decide
      have factor_0_2 : (13 : ZMod 104258953) ^ 6 = 4826809 := by
        calc
          (13 : ZMod 104258953) ^ 6 = (13 : ZMod 104258953) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 3 * (13 : ZMod 104258953) ^ 3 := by rw [pow_add]
          _ = 4826809 := by rw [factor_0_1]; decide
      have factor_0_3 : (13 : ZMod 104258953) ^ 12 = 66708242 := by
        calc
          (13 : ZMod 104258953) ^ 12 = (13 : ZMod 104258953) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 6 * (13 : ZMod 104258953) ^ 6 := by rw [pow_add]
          _ = 66708242 := by rw [factor_0_2]; decide
      have factor_0_4 : (13 : ZMod 104258953) ^ 24 = 56773559 := by
        calc
          (13 : ZMod 104258953) ^ 24 = (13 : ZMod 104258953) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 12 * (13 : ZMod 104258953) ^ 12 := by rw [pow_add]
          _ = 56773559 := by rw [factor_0_3]; decide
      have factor_0_5 : (13 : ZMod 104258953) ^ 49 = 52379070 := by
        calc
          (13 : ZMod 104258953) ^ 49 = (13 : ZMod 104258953) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 24 * (13 : ZMod 104258953) ^ 24) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 52379070 := by rw [factor_0_4]; decide
      have factor_0_6 : (13 : ZMod 104258953) ^ 99 = 54545460 := by
        calc
          (13 : ZMod 104258953) ^ 99 = (13 : ZMod 104258953) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 49 * (13 : ZMod 104258953) ^ 49) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 54545460 := by rw [factor_0_5]; decide
      have factor_0_7 : (13 : ZMod 104258953) ^ 198 = 12723829 := by
        calc
          (13 : ZMod 104258953) ^ 198 = (13 : ZMod 104258953) ^ (99 + 99) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 99 * (13 : ZMod 104258953) ^ 99 := by rw [pow_add]
          _ = 12723829 := by rw [factor_0_6]; decide
      have factor_0_8 : (13 : ZMod 104258953) ^ 397 = 51325691 := by
        calc
          (13 : ZMod 104258953) ^ 397 = (13 : ZMod 104258953) ^ (198 + 198 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 198 * (13 : ZMod 104258953) ^ 198) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 51325691 := by rw [factor_0_7]; decide
      have factor_0_9 : (13 : ZMod 104258953) ^ 795 = 5889621 := by
        calc
          (13 : ZMod 104258953) ^ 795 = (13 : ZMod 104258953) ^ (397 + 397 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 397 * (13 : ZMod 104258953) ^ 397) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 5889621 := by rw [factor_0_8]; decide
      have factor_0_10 : (13 : ZMod 104258953) ^ 1590 = 56306823 := by
        calc
          (13 : ZMod 104258953) ^ 1590 = (13 : ZMod 104258953) ^ (795 + 795) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 795 * (13 : ZMod 104258953) ^ 795 := by rw [pow_add]
          _ = 56306823 := by rw [factor_0_9]; decide
      have factor_0_11 : (13 : ZMod 104258953) ^ 3181 = 101873444 := by
        calc
          (13 : ZMod 104258953) ^ 3181 = (13 : ZMod 104258953) ^ (1590 + 1590 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 1590 * (13 : ZMod 104258953) ^ 1590) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 101873444 := by rw [factor_0_10]; decide
      have factor_0_12 : (13 : ZMod 104258953) ^ 6363 = 91731561 := by
        calc
          (13 : ZMod 104258953) ^ 6363 = (13 : ZMod 104258953) ^ (3181 + 3181 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 3181 * (13 : ZMod 104258953) ^ 3181) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 91731561 := by rw [factor_0_11]; decide
      have factor_0_13 : (13 : ZMod 104258953) ^ 12726 = 74095273 := by
        calc
          (13 : ZMod 104258953) ^ 12726 = (13 : ZMod 104258953) ^ (6363 + 6363) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 6363 * (13 : ZMod 104258953) ^ 6363 := by rw [pow_add]
          _ = 74095273 := by rw [factor_0_12]; decide
      have factor_0_14 : (13 : ZMod 104258953) ^ 25453 = 87458243 := by
        calc
          (13 : ZMod 104258953) ^ 25453 = (13 : ZMod 104258953) ^ (12726 + 12726 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 12726 * (13 : ZMod 104258953) ^ 12726) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 87458243 := by rw [factor_0_13]; decide
      have factor_0_15 : (13 : ZMod 104258953) ^ 50907 = 1602656 := by
        calc
          (13 : ZMod 104258953) ^ 50907 = (13 : ZMod 104258953) ^ (25453 + 25453 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 25453 * (13 : ZMod 104258953) ^ 25453) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 1602656 := by rw [factor_0_14]; decide
      have factor_0_16 : (13 : ZMod 104258953) ^ 101815 = 87723823 := by
        calc
          (13 : ZMod 104258953) ^ 101815 = (13 : ZMod 104258953) ^ (50907 + 50907 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 50907 * (13 : ZMod 104258953) ^ 50907) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 87723823 := by rw [factor_0_15]; decide
      have factor_0_17 : (13 : ZMod 104258953) ^ 203630 = 73367499 := by
        calc
          (13 : ZMod 104258953) ^ 203630 = (13 : ZMod 104258953) ^ (101815 + 101815) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 101815 * (13 : ZMod 104258953) ^ 101815 := by rw [pow_add]
          _ = 73367499 := by rw [factor_0_16]; decide
      have factor_0_18 : (13 : ZMod 104258953) ^ 407261 = 79330910 := by
        calc
          (13 : ZMod 104258953) ^ 407261 = (13 : ZMod 104258953) ^ (203630 + 203630 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 203630 * (13 : ZMod 104258953) ^ 203630) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 79330910 := by rw [factor_0_17]; decide
      have factor_0_19 : (13 : ZMod 104258953) ^ 814523 = 57336473 := by
        calc
          (13 : ZMod 104258953) ^ 814523 = (13 : ZMod 104258953) ^ (407261 + 407261 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 407261 * (13 : ZMod 104258953) ^ 407261) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 57336473 := by rw [factor_0_18]; decide
      have factor_0_20 : (13 : ZMod 104258953) ^ 1629046 = 37240718 := by
        calc
          (13 : ZMod 104258953) ^ 1629046 = (13 : ZMod 104258953) ^ (814523 + 814523) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 814523 * (13 : ZMod 104258953) ^ 814523 := by rw [pow_add]
          _ = 37240718 := by rw [factor_0_19]; decide
      have factor_0_21 : (13 : ZMod 104258953) ^ 3258092 = 30514843 := by
        calc
          (13 : ZMod 104258953) ^ 3258092 = (13 : ZMod 104258953) ^ (1629046 + 1629046) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 1629046 * (13 : ZMod 104258953) ^ 1629046 := by rw [pow_add]
          _ = 30514843 := by rw [factor_0_20]; decide
      have factor_0_22 : (13 : ZMod 104258953) ^ 6516184 = 63201156 := by
        calc
          (13 : ZMod 104258953) ^ 6516184 = (13 : ZMod 104258953) ^ (3258092 + 3258092) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 3258092 * (13 : ZMod 104258953) ^ 3258092 := by rw [pow_add]
          _ = 63201156 := by rw [factor_0_21]; decide
      have factor_0_23 : (13 : ZMod 104258953) ^ 13032369 = 76857619 := by
        calc
          (13 : ZMod 104258953) ^ 13032369 = (13 : ZMod 104258953) ^ (6516184 + 6516184 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 6516184 * (13 : ZMod 104258953) ^ 6516184) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 76857619 := by rw [factor_0_22]; decide
      have factor_0_24 : (13 : ZMod 104258953) ^ 26064738 = 56652555 := by
        calc
          (13 : ZMod 104258953) ^ 26064738 = (13 : ZMod 104258953) ^ (13032369 + 13032369) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 13032369 * (13 : ZMod 104258953) ^ 13032369 := by rw [pow_add]
          _ = 56652555 := by rw [factor_0_23]; decide
      have factor_0_25 : (13 : ZMod 104258953) ^ 52129476 = 104258952 := by
        calc
          (13 : ZMod 104258953) ^ 52129476 = (13 : ZMod 104258953) ^ (26064738 + 26064738) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 26064738 * (13 : ZMod 104258953) ^ 26064738 := by rw [pow_add]
          _ = 104258952 := by rw [factor_0_24]; decide
      change (13 : ZMod 104258953) ^ 52129476 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (13 : ZMod 104258953) ^ 1 = 13 := by norm_num
      have factor_1_1 : (13 : ZMod 104258953) ^ 2 = 169 := by
        calc
          (13 : ZMod 104258953) ^ 2 = (13 : ZMod 104258953) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 1 * (13 : ZMod 104258953) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_1_0]; decide
      have factor_1_2 : (13 : ZMod 104258953) ^ 4 = 28561 := by
        calc
          (13 : ZMod 104258953) ^ 4 = (13 : ZMod 104258953) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 2 * (13 : ZMod 104258953) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_1_1]; decide
      have factor_1_3 : (13 : ZMod 104258953) ^ 8 = 85918050 := by
        calc
          (13 : ZMod 104258953) ^ 8 = (13 : ZMod 104258953) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 4 * (13 : ZMod 104258953) ^ 4 := by rw [pow_add]
          _ = 85918050 := by rw [factor_1_2]; decide
      have factor_1_4 : (13 : ZMod 104258953) ^ 16 = 25992640 := by
        calc
          (13 : ZMod 104258953) ^ 16 = (13 : ZMod 104258953) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 8 * (13 : ZMod 104258953) ^ 8 := by rw [pow_add]
          _ = 25992640 := by rw [factor_1_3]; decide
      have factor_1_5 : (13 : ZMod 104258953) ^ 33 = 87925976 := by
        calc
          (13 : ZMod 104258953) ^ 33 = (13 : ZMod 104258953) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 16 * (13 : ZMod 104258953) ^ 16) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 87925976 := by rw [factor_1_4]; decide
      have factor_1_6 : (13 : ZMod 104258953) ^ 66 = 5748865 := by
        calc
          (13 : ZMod 104258953) ^ 66 = (13 : ZMod 104258953) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 33 * (13 : ZMod 104258953) ^ 33 := by rw [pow_add]
          _ = 5748865 := by rw [factor_1_5]; decide
      have factor_1_7 : (13 : ZMod 104258953) ^ 132 = 90499896 := by
        calc
          (13 : ZMod 104258953) ^ 132 = (13 : ZMod 104258953) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 66 * (13 : ZMod 104258953) ^ 66 := by rw [pow_add]
          _ = 90499896 := by rw [factor_1_6]; decide
      have factor_1_8 : (13 : ZMod 104258953) ^ 265 = 91703697 := by
        calc
          (13 : ZMod 104258953) ^ 265 = (13 : ZMod 104258953) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 132 * (13 : ZMod 104258953) ^ 132) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 91703697 := by rw [factor_1_7]; decide
      have factor_1_9 : (13 : ZMod 104258953) ^ 530 = 24978233 := by
        calc
          (13 : ZMod 104258953) ^ 530 = (13 : ZMod 104258953) ^ (265 + 265) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 265 * (13 : ZMod 104258953) ^ 265 := by rw [pow_add]
          _ = 24978233 := by rw [factor_1_8]; decide
      have factor_1_10 : (13 : ZMod 104258953) ^ 1060 = 67276227 := by
        calc
          (13 : ZMod 104258953) ^ 1060 = (13 : ZMod 104258953) ^ (530 + 530) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 530 * (13 : ZMod 104258953) ^ 530 := by rw [pow_add]
          _ = 67276227 := by rw [factor_1_9]; decide
      have factor_1_11 : (13 : ZMod 104258953) ^ 2121 = 14431034 := by
        calc
          (13 : ZMod 104258953) ^ 2121 = (13 : ZMod 104258953) ^ (1060 + 1060 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 1060 * (13 : ZMod 104258953) ^ 1060) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 14431034 := by rw [factor_1_10]; decide
      have factor_1_12 : (13 : ZMod 104258953) ^ 4242 = 90165481 := by
        calc
          (13 : ZMod 104258953) ^ 4242 = (13 : ZMod 104258953) ^ (2121 + 2121) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 2121 * (13 : ZMod 104258953) ^ 2121 := by rw [pow_add]
          _ = 90165481 := by rw [factor_1_11]; decide
      have factor_1_13 : (13 : ZMod 104258953) ^ 8484 = 32216471 := by
        calc
          (13 : ZMod 104258953) ^ 8484 = (13 : ZMod 104258953) ^ (4242 + 4242) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 4242 * (13 : ZMod 104258953) ^ 4242 := by rw [pow_add]
          _ = 32216471 := by rw [factor_1_12]; decide
      have factor_1_14 : (13 : ZMod 104258953) ^ 16969 = 88792216 := by
        calc
          (13 : ZMod 104258953) ^ 16969 = (13 : ZMod 104258953) ^ (8484 + 8484 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 8484 * (13 : ZMod 104258953) ^ 8484) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 88792216 := by rw [factor_1_13]; decide
      have factor_1_15 : (13 : ZMod 104258953) ^ 33938 = 79465635 := by
        calc
          (13 : ZMod 104258953) ^ 33938 = (13 : ZMod 104258953) ^ (16969 + 16969) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 16969 * (13 : ZMod 104258953) ^ 16969 := by rw [pow_add]
          _ = 79465635 := by rw [factor_1_14]; decide
      have factor_1_16 : (13 : ZMod 104258953) ^ 67876 = 19999137 := by
        calc
          (13 : ZMod 104258953) ^ 67876 = (13 : ZMod 104258953) ^ (33938 + 33938) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 33938 * (13 : ZMod 104258953) ^ 33938 := by rw [pow_add]
          _ = 19999137 := by rw [factor_1_15]; decide
      have factor_1_17 : (13 : ZMod 104258953) ^ 135753 = 41070873 := by
        calc
          (13 : ZMod 104258953) ^ 135753 = (13 : ZMod 104258953) ^ (67876 + 67876 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 67876 * (13 : ZMod 104258953) ^ 67876) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 41070873 := by rw [factor_1_16]; decide
      have factor_1_18 : (13 : ZMod 104258953) ^ 271507 = 65853161 := by
        calc
          (13 : ZMod 104258953) ^ 271507 = (13 : ZMod 104258953) ^ (135753 + 135753 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 135753 * (13 : ZMod 104258953) ^ 135753) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 65853161 := by rw [factor_1_17]; decide
      have factor_1_19 : (13 : ZMod 104258953) ^ 543015 = 82068640 := by
        calc
          (13 : ZMod 104258953) ^ 543015 = (13 : ZMod 104258953) ^ (271507 + 271507 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 271507 * (13 : ZMod 104258953) ^ 271507) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 82068640 := by rw [factor_1_18]; decide
      have factor_1_20 : (13 : ZMod 104258953) ^ 1086030 = 64707666 := by
        calc
          (13 : ZMod 104258953) ^ 1086030 = (13 : ZMod 104258953) ^ (543015 + 543015) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 543015 * (13 : ZMod 104258953) ^ 543015 := by rw [pow_add]
          _ = 64707666 := by rw [factor_1_19]; decide
      have factor_1_21 : (13 : ZMod 104258953) ^ 2172061 = 67264187 := by
        calc
          (13 : ZMod 104258953) ^ 2172061 = (13 : ZMod 104258953) ^ (1086030 + 1086030 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 1086030 * (13 : ZMod 104258953) ^ 1086030) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 67264187 := by rw [factor_1_20]; decide
      have factor_1_22 : (13 : ZMod 104258953) ^ 4344123 = 76417647 := by
        calc
          (13 : ZMod 104258953) ^ 4344123 = (13 : ZMod 104258953) ^ (2172061 + 2172061 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 2172061 * (13 : ZMod 104258953) ^ 2172061) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 76417647 := by rw [factor_1_21]; decide
      have factor_1_23 : (13 : ZMod 104258953) ^ 8688246 = 7299463 := by
        calc
          (13 : ZMod 104258953) ^ 8688246 = (13 : ZMod 104258953) ^ (4344123 + 4344123) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 4344123 * (13 : ZMod 104258953) ^ 4344123 := by rw [pow_add]
          _ = 7299463 := by rw [factor_1_22]; decide
      have factor_1_24 : (13 : ZMod 104258953) ^ 17376492 = 100862954 := by
        calc
          (13 : ZMod 104258953) ^ 17376492 = (13 : ZMod 104258953) ^ (8688246 + 8688246) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 8688246 * (13 : ZMod 104258953) ^ 8688246 := by rw [pow_add]
          _ = 100862954 := by rw [factor_1_23]; decide
      have factor_1_25 : (13 : ZMod 104258953) ^ 34752984 = 100862953 := by
        calc
          (13 : ZMod 104258953) ^ 34752984 = (13 : ZMod 104258953) ^ (17376492 + 17376492) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 17376492 * (13 : ZMod 104258953) ^ 17376492 := by rw [pow_add]
          _ = 100862953 := by rw [factor_1_24]; decide
      change (13 : ZMod 104258953) ^ 34752984 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (13 : ZMod 104258953) ^ 1 = 13 := by norm_num
      have factor_2_1 : (13 : ZMod 104258953) ^ 3 = 2197 := by
        calc
          (13 : ZMod 104258953) ^ 3 = (13 : ZMod 104258953) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 1 * (13 : ZMod 104258953) ^ 1) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_2_0]; decide
      have factor_2_2 : (13 : ZMod 104258953) ^ 7 = 62748517 := by
        calc
          (13 : ZMod 104258953) ^ 7 = (13 : ZMod 104258953) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 3 * (13 : ZMod 104258953) ^ 3) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 62748517 := by rw [factor_2_1]; decide
      have factor_2_3 : (13 : ZMod 104258953) ^ 14 = 13725974 := by
        calc
          (13 : ZMod 104258953) ^ 14 = (13 : ZMod 104258953) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 7 * (13 : ZMod 104258953) ^ 7 := by rw [pow_add]
          _ = 13725974 := by rw [factor_2_2]; decide
      have factor_2_4 : (13 : ZMod 104258953) ^ 28 = 74381543 := by
        calc
          (13 : ZMod 104258953) ^ 28 = (13 : ZMod 104258953) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 14 * (13 : ZMod 104258953) ^ 14 := by rw [pow_add]
          _ = 74381543 := by rw [factor_2_3]; decide
      have factor_2_5 : (13 : ZMod 104258953) ^ 56 = 102705562 := by
        calc
          (13 : ZMod 104258953) ^ 56 = (13 : ZMod 104258953) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 28 * (13 : ZMod 104258953) ^ 28 := by rw [pow_add]
          _ = 102705562 := by rw [factor_2_4]; decide
      have factor_2_6 : (13 : ZMod 104258953) ^ 113 = 81524719 := by
        calc
          (13 : ZMod 104258953) ^ 113 = (13 : ZMod 104258953) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 56 * (13 : ZMod 104258953) ^ 56) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 81524719 := by rw [factor_2_5]; decide
      have factor_2_7 : (13 : ZMod 104258953) ^ 227 = 21902698 := by
        calc
          (13 : ZMod 104258953) ^ 227 = (13 : ZMod 104258953) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 113 * (13 : ZMod 104258953) ^ 113) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 21902698 := by rw [factor_2_6]; decide
      have factor_2_8 : (13 : ZMod 104258953) ^ 454 = 103873915 := by
        calc
          (13 : ZMod 104258953) ^ 454 = (13 : ZMod 104258953) ^ (227 + 227) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 227 * (13 : ZMod 104258953) ^ 227 := by rw [pow_add]
          _ = 103873915 := by rw [factor_2_7]; decide
      have factor_2_9 : (13 : ZMod 104258953) ^ 909 = 78652567 := by
        calc
          (13 : ZMod 104258953) ^ 909 = (13 : ZMod 104258953) ^ (454 + 454 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 454 * (13 : ZMod 104258953) ^ 454) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 78652567 := by rw [factor_2_8]; decide
      have factor_2_10 : (13 : ZMod 104258953) ^ 1818 = 50608077 := by
        calc
          (13 : ZMod 104258953) ^ 1818 = (13 : ZMod 104258953) ^ (909 + 909) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 909 * (13 : ZMod 104258953) ^ 909 := by rw [pow_add]
          _ = 50608077 := by rw [factor_2_9]; decide
      have factor_2_11 : (13 : ZMod 104258953) ^ 3636 = 81617262 := by
        calc
          (13 : ZMod 104258953) ^ 3636 = (13 : ZMod 104258953) ^ (1818 + 1818) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 1818 * (13 : ZMod 104258953) ^ 1818 := by rw [pow_add]
          _ = 81617262 := by rw [factor_2_10]; decide
      have factor_2_12 : (13 : ZMod 104258953) ^ 7272 = 103526643 := by
        calc
          (13 : ZMod 104258953) ^ 7272 = (13 : ZMod 104258953) ^ (3636 + 3636) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 3636 * (13 : ZMod 104258953) ^ 3636 := by rw [pow_add]
          _ = 103526643 := by rw [factor_2_11]; decide
      have factor_2_13 : (13 : ZMod 104258953) ^ 14545 = 25500096 := by
        calc
          (13 : ZMod 104258953) ^ 14545 = (13 : ZMod 104258953) ^ (7272 + 7272 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 7272 * (13 : ZMod 104258953) ^ 7272) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 25500096 := by rw [factor_2_12]; decide
      have factor_2_14 : (13 : ZMod 104258953) ^ 29090 = 42605503 := by
        calc
          (13 : ZMod 104258953) ^ 29090 = (13 : ZMod 104258953) ^ (14545 + 14545) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 14545 * (13 : ZMod 104258953) ^ 14545 := by rw [pow_add]
          _ = 42605503 := by rw [factor_2_13]; decide
      have factor_2_15 : (13 : ZMod 104258953) ^ 58180 = 26241293 := by
        calc
          (13 : ZMod 104258953) ^ 58180 = (13 : ZMod 104258953) ^ (29090 + 29090) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 29090 * (13 : ZMod 104258953) ^ 29090 := by rw [pow_add]
          _ = 26241293 := by rw [factor_2_14]; decide
      have factor_2_16 : (13 : ZMod 104258953) ^ 116360 = 95895569 := by
        calc
          (13 : ZMod 104258953) ^ 116360 = (13 : ZMod 104258953) ^ (58180 + 58180) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 58180 * (13 : ZMod 104258953) ^ 58180 := by rw [pow_add]
          _ = 95895569 := by rw [factor_2_15]; decide
      have factor_2_17 : (13 : ZMod 104258953) ^ 232720 = 7212239 := by
        calc
          (13 : ZMod 104258953) ^ 232720 = (13 : ZMod 104258953) ^ (116360 + 116360) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 116360 * (13 : ZMod 104258953) ^ 116360 := by rw [pow_add]
          _ = 7212239 := by rw [factor_2_16]; decide
      have factor_2_18 : (13 : ZMod 104258953) ^ 465441 = 49106826 := by
        calc
          (13 : ZMod 104258953) ^ 465441 = (13 : ZMod 104258953) ^ (232720 + 232720 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 232720 * (13 : ZMod 104258953) ^ 232720) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 49106826 := by rw [factor_2_17]; decide
      have factor_2_19 : (13 : ZMod 104258953) ^ 930883 = 19380320 := by
        calc
          (13 : ZMod 104258953) ^ 930883 = (13 : ZMod 104258953) ^ (465441 + 465441 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 465441 * (13 : ZMod 104258953) ^ 465441) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 19380320 := by rw [factor_2_18]; decide
      have factor_2_20 : (13 : ZMod 104258953) ^ 1861767 = 43930683 := by
        calc
          (13 : ZMod 104258953) ^ 1861767 = (13 : ZMod 104258953) ^ (930883 + 930883 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 930883 * (13 : ZMod 104258953) ^ 930883) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 43930683 := by rw [factor_2_19]; decide
      have factor_2_21 : (13 : ZMod 104258953) ^ 3723534 = 62915778 := by
        calc
          (13 : ZMod 104258953) ^ 3723534 = (13 : ZMod 104258953) ^ (1861767 + 1861767) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 1861767 * (13 : ZMod 104258953) ^ 1861767 := by rw [pow_add]
          _ = 62915778 := by rw [factor_2_20]; decide
      have factor_2_22 : (13 : ZMod 104258953) ^ 7447068 = 40188216 := by
        calc
          (13 : ZMod 104258953) ^ 7447068 = (13 : ZMod 104258953) ^ (3723534 + 3723534) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 3723534 * (13 : ZMod 104258953) ^ 3723534 := by rw [pow_add]
          _ = 40188216 := by rw [factor_2_21]; decide
      have factor_2_23 : (13 : ZMod 104258953) ^ 14894136 = 61612411 := by
        calc
          (13 : ZMod 104258953) ^ 14894136 = (13 : ZMod 104258953) ^ (7447068 + 7447068) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 7447068 * (13 : ZMod 104258953) ^ 7447068 := by rw [pow_add]
          _ = 61612411 := by rw [factor_2_22]; decide
      change (13 : ZMod 104258953) ^ 14894136 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (13 : ZMod 104258953) ^ 1 = 13 := by norm_num
      have factor_3_1 : (13 : ZMod 104258953) ^ 3 = 2197 := by
        calc
          (13 : ZMod 104258953) ^ 3 = (13 : ZMod 104258953) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 1 * (13 : ZMod 104258953) ^ 1) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_3_0]; decide
      have factor_3_2 : (13 : ZMod 104258953) ^ 6 = 4826809 := by
        calc
          (13 : ZMod 104258953) ^ 6 = (13 : ZMod 104258953) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 3 * (13 : ZMod 104258953) ^ 3 := by rw [pow_add]
          _ = 4826809 := by rw [factor_3_1]; decide
      have factor_3_3 : (13 : ZMod 104258953) ^ 12 = 66708242 := by
        calc
          (13 : ZMod 104258953) ^ 12 = (13 : ZMod 104258953) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 6 * (13 : ZMod 104258953) ^ 6 := by rw [pow_add]
          _ = 66708242 := by rw [factor_3_2]; decide
      have factor_3_4 : (13 : ZMod 104258953) ^ 25 = 8243596 := by
        calc
          (13 : ZMod 104258953) ^ 25 = (13 : ZMod 104258953) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 12 * (13 : ZMod 104258953) ^ 12) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 8243596 := by rw [factor_3_3]; decide
      have factor_3_5 : (13 : ZMod 104258953) ^ 51 = 94310778 := by
        calc
          (13 : ZMod 104258953) ^ 51 = (13 : ZMod 104258953) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 25 * (13 : ZMod 104258953) ^ 25) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 94310778 := by rw [factor_3_4]; decide
      have factor_3_6 : (13 : ZMod 104258953) ^ 102 = 42838623 := by
        calc
          (13 : ZMod 104258953) ^ 102 = (13 : ZMod 104258953) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 51 * (13 : ZMod 104258953) ^ 51 := by rw [pow_add]
          _ = 42838623 := by rw [factor_3_5]; decide
      have factor_3_7 : (13 : ZMod 104258953) ^ 205 = 100419389 := by
        calc
          (13 : ZMod 104258953) ^ 205 = (13 : ZMod 104258953) ^ (102 + 102 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 102 * (13 : ZMod 104258953) ^ 102) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 100419389 := by rw [factor_3_6]; decide
      have factor_3_8 : (13 : ZMod 104258953) ^ 410 = 35755896 := by
        calc
          (13 : ZMod 104258953) ^ 410 = (13 : ZMod 104258953) ^ (205 + 205) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 205 * (13 : ZMod 104258953) ^ 205 := by rw [pow_add]
          _ = 35755896 := by rw [factor_3_7]; decide
      have factor_3_9 : (13 : ZMod 104258953) ^ 821 = 26358009 := by
        calc
          (13 : ZMod 104258953) ^ 821 = (13 : ZMod 104258953) ^ (410 + 410 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 410 * (13 : ZMod 104258953) ^ 410) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 26358009 := by rw [factor_3_8]; decide
      have factor_3_10 : (13 : ZMod 104258953) ^ 1642 = 91839349 := by
        calc
          (13 : ZMod 104258953) ^ 1642 = (13 : ZMod 104258953) ^ (821 + 821) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 821 * (13 : ZMod 104258953) ^ 821 := by rw [pow_add]
          _ = 91839349 := by rw [factor_3_9]; decide
      have factor_3_11 : (13 : ZMod 104258953) ^ 3284 = 29947248 := by
        calc
          (13 : ZMod 104258953) ^ 3284 = (13 : ZMod 104258953) ^ (1642 + 1642) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 1642 * (13 : ZMod 104258953) ^ 1642 := by rw [pow_add]
          _ = 29947248 := by rw [factor_3_10]; decide
      have factor_3_12 : (13 : ZMod 104258953) ^ 6568 = 63888444 := by
        calc
          (13 : ZMod 104258953) ^ 6568 = (13 : ZMod 104258953) ^ (3284 + 3284) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 3284 * (13 : ZMod 104258953) ^ 3284 := by rw [pow_add]
          _ = 63888444 := by rw [factor_3_11]; decide
      have factor_3_13 : (13 : ZMod 104258953) ^ 13137 = 85325991 := by
        calc
          (13 : ZMod 104258953) ^ 13137 = (13 : ZMod 104258953) ^ (6568 + 6568 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 6568 * (13 : ZMod 104258953) ^ 6568) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 85325991 := by rw [factor_3_12]; decide
      have factor_3_14 : (13 : ZMod 104258953) ^ 26274 = 69167071 := by
        calc
          (13 : ZMod 104258953) ^ 26274 = (13 : ZMod 104258953) ^ (13137 + 13137) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 13137 * (13 : ZMod 104258953) ^ 13137 := by rw [pow_add]
          _ = 69167071 := by rw [factor_3_13]; decide
      have factor_3_15 : (13 : ZMod 104258953) ^ 52549 = 36625865 := by
        calc
          (13 : ZMod 104258953) ^ 52549 = (13 : ZMod 104258953) ^ (26274 + 26274 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 26274 * (13 : ZMod 104258953) ^ 26274) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 36625865 := by rw [factor_3_14]; decide
      have factor_3_16 : (13 : ZMod 104258953) ^ 105099 = 11773568 := by
        calc
          (13 : ZMod 104258953) ^ 105099 = (13 : ZMod 104258953) ^ (52549 + 52549 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 52549 * (13 : ZMod 104258953) ^ 52549) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 11773568 := by rw [factor_3_15]; decide
      have factor_3_17 : (13 : ZMod 104258953) ^ 210199 = 77525684 := by
        calc
          (13 : ZMod 104258953) ^ 210199 = (13 : ZMod 104258953) ^ (105099 + 105099 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 105099 * (13 : ZMod 104258953) ^ 105099) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 77525684 := by rw [factor_3_16]; decide
      have factor_3_18 : (13 : ZMod 104258953) ^ 420399 = 10343812 := by
        calc
          (13 : ZMod 104258953) ^ 420399 = (13 : ZMod 104258953) ^ (210199 + 210199 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 210199 * (13 : ZMod 104258953) ^ 210199) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 10343812 := by rw [factor_3_17]; decide
      have factor_3_19 : (13 : ZMod 104258953) ^ 840798 = 51541483 := by
        calc
          (13 : ZMod 104258953) ^ 840798 = (13 : ZMod 104258953) ^ (420399 + 420399) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 420399 * (13 : ZMod 104258953) ^ 420399 := by rw [pow_add]
          _ = 51541483 := by rw [factor_3_18]; decide
      have factor_3_20 : (13 : ZMod 104258953) ^ 1681596 = 91862109 := by
        calc
          (13 : ZMod 104258953) ^ 1681596 = (13 : ZMod 104258953) ^ (840798 + 840798) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 840798 * (13 : ZMod 104258953) ^ 840798 := by rw [pow_add]
          _ = 91862109 := by rw [factor_3_19]; decide
      have factor_3_21 : (13 : ZMod 104258953) ^ 3363192 = 82598122 := by
        calc
          (13 : ZMod 104258953) ^ 3363192 = (13 : ZMod 104258953) ^ (1681596 + 1681596) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 1681596 * (13 : ZMod 104258953) ^ 1681596 := by rw [pow_add]
          _ = 82598122 := by rw [factor_3_20]; decide
      change (13 : ZMod 104258953) ^ 3363192 ≠ 1
      rw [factor_3_21]
      decide
    ·
      have factor_4_0 : (13 : ZMod 104258953) ^ 1 = 13 := by norm_num
      have factor_4_1 : (13 : ZMod 104258953) ^ 3 = 2197 := by
        calc
          (13 : ZMod 104258953) ^ 3 = (13 : ZMod 104258953) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 1 * (13 : ZMod 104258953) ^ 1) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_4_0]; decide
      have factor_4_2 : (13 : ZMod 104258953) ^ 7 = 62748517 := by
        calc
          (13 : ZMod 104258953) ^ 7 = (13 : ZMod 104258953) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 3 * (13 : ZMod 104258953) ^ 3) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 62748517 := by rw [factor_4_1]; decide
      have factor_4_3 : (13 : ZMod 104258953) ^ 15 = 74178709 := by
        calc
          (13 : ZMod 104258953) ^ 15 = (13 : ZMod 104258953) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 7 * (13 : ZMod 104258953) ^ 7) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 74178709 := by rw [factor_4_2]; decide
      have factor_4_4 : (13 : ZMod 104258953) ^ 30 = 59406407 := by
        calc
          (13 : ZMod 104258953) ^ 30 = (13 : ZMod 104258953) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 15 * (13 : ZMod 104258953) ^ 15 := by rw [pow_add]
          _ = 59406407 := by rw [factor_4_3]; decide
      have factor_4_5 : (13 : ZMod 104258953) ^ 61 = 101582386 := by
        calc
          (13 : ZMod 104258953) ^ 61 = (13 : ZMod 104258953) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 30 * (13 : ZMod 104258953) ^ 30) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 101582386 := by rw [factor_4_4]; decide
      have factor_4_6 : (13 : ZMod 104258953) ^ 122 = 65468000 := by
        calc
          (13 : ZMod 104258953) ^ 122 = (13 : ZMod 104258953) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 61 * (13 : ZMod 104258953) ^ 61 := by rw [pow_add]
          _ = 65468000 := by rw [factor_4_5]; decide
      have factor_4_7 : (13 : ZMod 104258953) ^ 244 = 52203015 := by
        calc
          (13 : ZMod 104258953) ^ 244 = (13 : ZMod 104258953) ^ (122 + 122) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 122 * (13 : ZMod 104258953) ^ 122 := by rw [pow_add]
          _ = 52203015 := by rw [factor_4_6]; decide
      have factor_4_8 : (13 : ZMod 104258953) ^ 488 = 64639641 := by
        calc
          (13 : ZMod 104258953) ^ 488 = (13 : ZMod 104258953) ^ (244 + 244) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 244 * (13 : ZMod 104258953) ^ 244 := by rw [pow_add]
          _ = 64639641 := by rw [factor_4_7]; decide
      have factor_4_9 : (13 : ZMod 104258953) ^ 976 = 32814492 := by
        calc
          (13 : ZMod 104258953) ^ 976 = (13 : ZMod 104258953) ^ (488 + 488) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 488 * (13 : ZMod 104258953) ^ 488 := by rw [pow_add]
          _ = 32814492 := by rw [factor_4_8]; decide
      have factor_4_10 : (13 : ZMod 104258953) ^ 1953 = 99818682 := by
        calc
          (13 : ZMod 104258953) ^ 1953 = (13 : ZMod 104258953) ^ (976 + 976 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = ((13 : ZMod 104258953) ^ 976 * (13 : ZMod 104258953) ^ 976) * (13 : ZMod 104258953) := by rw [pow_succ, pow_add]
          _ = 99818682 := by rw [factor_4_9]; decide
      have factor_4_11 : (13 : ZMod 104258953) ^ 3906 = 12987423 := by
        calc
          (13 : ZMod 104258953) ^ 3906 = (13 : ZMod 104258953) ^ (1953 + 1953) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 1953 * (13 : ZMod 104258953) ^ 1953 := by rw [pow_add]
          _ = 12987423 := by rw [factor_4_10]; decide
      have factor_4_12 : (13 : ZMod 104258953) ^ 7812 = 102766845 := by
        calc
          (13 : ZMod 104258953) ^ 7812 = (13 : ZMod 104258953) ^ (3906 + 3906) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 3906 * (13 : ZMod 104258953) ^ 3906 := by rw [pow_add]
          _ = 102766845 := by rw [factor_4_11]; decide
      have factor_4_13 : (13 : ZMod 104258953) ^ 15624 = 40601302 := by
        calc
          (13 : ZMod 104258953) ^ 15624 = (13 : ZMod 104258953) ^ (7812 + 7812) :=
            congrArg (fun n : ℕ => (13 : ZMod 104258953) ^ n) (by norm_num)
          _ = (13 : ZMod 104258953) ^ 7812 * (13 : ZMod 104258953) ^ 7812 := by rw [pow_add]
          _ = 40601302 := by rw [factor_4_12]; decide
      change (13 : ZMod 104258953) ^ 15624 ≠ 1
      rw [factor_4_13]
      decide

#print axioms prime_lucas_104258953

end TotientTailPeriodKiller
end Erdos249257
