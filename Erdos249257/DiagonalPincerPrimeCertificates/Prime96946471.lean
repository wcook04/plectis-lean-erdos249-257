import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_96946471 : Nat.Prime 96946471 := by
  apply lucas_primality 96946471 (17 : ZMod 96946471)
  ·
      have fermat_0 : (17 : ZMod 96946471) ^ 1 = 17 := by norm_num
      have fermat_1 : (17 : ZMod 96946471) ^ 2 = 289 := by
        calc
          (17 : ZMod 96946471) ^ 2 = (17 : ZMod 96946471) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 1 * (17 : ZMod 96946471) ^ 1 := by rw [pow_add]
          _ = 289 := by rw [fermat_0]; decide
      have fermat_2 : (17 : ZMod 96946471) ^ 5 = 1419857 := by
        calc
          (17 : ZMod 96946471) ^ 5 = (17 : ZMod 96946471) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 2 * (17 : ZMod 96946471) ^ 2) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 1419857 := by rw [fermat_1]; decide
      have fermat_3 : (17 : ZMod 96946471) ^ 11 = 58505010 := by
        calc
          (17 : ZMod 96946471) ^ 11 = (17 : ZMod 96946471) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 5 * (17 : ZMod 96946471) ^ 5) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 58505010 := by rw [fermat_2]; decide
      have fermat_4 : (17 : ZMod 96946471) ^ 23 = 36392399 := by
        calc
          (17 : ZMod 96946471) ^ 23 = (17 : ZMod 96946471) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 11 * (17 : ZMod 96946471) ^ 11) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 36392399 := by rw [fermat_3]; decide
      have fermat_5 : (17 : ZMod 96946471) ^ 46 = 24206465 := by
        calc
          (17 : ZMod 96946471) ^ 46 = (17 : ZMod 96946471) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 23 * (17 : ZMod 96946471) ^ 23 := by rw [pow_add]
          _ = 24206465 := by rw [fermat_4]; decide
      have fermat_6 : (17 : ZMod 96946471) ^ 92 = 42729248 := by
        calc
          (17 : ZMod 96946471) ^ 92 = (17 : ZMod 96946471) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 46 * (17 : ZMod 96946471) ^ 46 := by rw [pow_add]
          _ = 42729248 := by rw [fermat_5]; decide
      have fermat_7 : (17 : ZMod 96946471) ^ 184 = 11947228 := by
        calc
          (17 : ZMod 96946471) ^ 184 = (17 : ZMod 96946471) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 92 * (17 : ZMod 96946471) ^ 92 := by rw [pow_add]
          _ = 11947228 := by rw [fermat_6]; decide
      have fermat_8 : (17 : ZMod 96946471) ^ 369 = 3189133 := by
        calc
          (17 : ZMod 96946471) ^ 369 = (17 : ZMod 96946471) ^ (184 + 184 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 184 * (17 : ZMod 96946471) ^ 184) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 3189133 := by rw [fermat_7]; decide
      have fermat_9 : (17 : ZMod 96946471) ^ 739 = 9521408 := by
        calc
          (17 : ZMod 96946471) ^ 739 = (17 : ZMod 96946471) ^ (369 + 369 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 369 * (17 : ZMod 96946471) ^ 369) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 9521408 := by rw [fermat_8]; decide
      have fermat_10 : (17 : ZMod 96946471) ^ 1479 = 80630709 := by
        calc
          (17 : ZMod 96946471) ^ 1479 = (17 : ZMod 96946471) ^ (739 + 739 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 739 * (17 : ZMod 96946471) ^ 739) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 80630709 := by rw [fermat_9]; decide
      have fermat_11 : (17 : ZMod 96946471) ^ 2958 = 35225867 := by
        calc
          (17 : ZMod 96946471) ^ 2958 = (17 : ZMod 96946471) ^ (1479 + 1479) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 1479 * (17 : ZMod 96946471) ^ 1479 := by rw [pow_add]
          _ = 35225867 := by rw [fermat_10]; decide
      have fermat_12 : (17 : ZMod 96946471) ^ 5917 = 64052549 := by
        calc
          (17 : ZMod 96946471) ^ 5917 = (17 : ZMod 96946471) ^ (2958 + 2958 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 2958 * (17 : ZMod 96946471) ^ 2958) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 64052549 := by rw [fermat_11]; decide
      have fermat_13 : (17 : ZMod 96946471) ^ 11834 = 42465242 := by
        calc
          (17 : ZMod 96946471) ^ 11834 = (17 : ZMod 96946471) ^ (5917 + 5917) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 5917 * (17 : ZMod 96946471) ^ 5917 := by rw [pow_add]
          _ = 42465242 := by rw [fermat_12]; decide
      have fermat_14 : (17 : ZMod 96946471) ^ 23668 = 27531701 := by
        calc
          (17 : ZMod 96946471) ^ 23668 = (17 : ZMod 96946471) ^ (11834 + 11834) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 11834 * (17 : ZMod 96946471) ^ 11834 := by rw [pow_add]
          _ = 27531701 := by rw [fermat_13]; decide
      have fermat_15 : (17 : ZMod 96946471) ^ 47337 = 44822270 := by
        calc
          (17 : ZMod 96946471) ^ 47337 = (17 : ZMod 96946471) ^ (23668 + 23668 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 23668 * (17 : ZMod 96946471) ^ 23668) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 44822270 := by rw [fermat_14]; decide
      have fermat_16 : (17 : ZMod 96946471) ^ 94674 = 15235134 := by
        calc
          (17 : ZMod 96946471) ^ 94674 = (17 : ZMod 96946471) ^ (47337 + 47337) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 47337 * (17 : ZMod 96946471) ^ 47337 := by rw [pow_add]
          _ = 15235134 := by rw [fermat_15]; decide
      have fermat_17 : (17 : ZMod 96946471) ^ 189348 = 67129756 := by
        calc
          (17 : ZMod 96946471) ^ 189348 = (17 : ZMod 96946471) ^ (94674 + 94674) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 94674 * (17 : ZMod 96946471) ^ 94674 := by rw [pow_add]
          _ = 67129756 := by rw [fermat_16]; decide
      have fermat_18 : (17 : ZMod 96946471) ^ 378697 = 24075775 := by
        calc
          (17 : ZMod 96946471) ^ 378697 = (17 : ZMod 96946471) ^ (189348 + 189348 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 189348 * (17 : ZMod 96946471) ^ 189348) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 24075775 := by rw [fermat_17]; decide
      have fermat_19 : (17 : ZMod 96946471) ^ 757394 = 88688096 := by
        calc
          (17 : ZMod 96946471) ^ 757394 = (17 : ZMod 96946471) ^ (378697 + 378697) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 378697 * (17 : ZMod 96946471) ^ 378697 := by rw [pow_add]
          _ = 88688096 := by rw [fermat_18]; decide
      have fermat_20 : (17 : ZMod 96946471) ^ 1514788 = 78649777 := by
        calc
          (17 : ZMod 96946471) ^ 1514788 = (17 : ZMod 96946471) ^ (757394 + 757394) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 757394 * (17 : ZMod 96946471) ^ 757394 := by rw [pow_add]
          _ = 78649777 := by rw [fermat_19]; decide
      have fermat_21 : (17 : ZMod 96946471) ^ 3029577 = 74980120 := by
        calc
          (17 : ZMod 96946471) ^ 3029577 = (17 : ZMod 96946471) ^ (1514788 + 1514788 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 1514788 * (17 : ZMod 96946471) ^ 1514788) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 74980120 := by rw [fermat_20]; decide
      have fermat_22 : (17 : ZMod 96946471) ^ 6059154 = 54991066 := by
        calc
          (17 : ZMod 96946471) ^ 6059154 = (17 : ZMod 96946471) ^ (3029577 + 3029577) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 3029577 * (17 : ZMod 96946471) ^ 3029577 := by rw [pow_add]
          _ = 54991066 := by rw [fermat_21]; decide
      have fermat_23 : (17 : ZMod 96946471) ^ 12118308 = 1178206 := by
        calc
          (17 : ZMod 96946471) ^ 12118308 = (17 : ZMod 96946471) ^ (6059154 + 6059154) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 6059154 * (17 : ZMod 96946471) ^ 6059154 := by rw [pow_add]
          _ = 1178206 := by rw [fermat_22]; decide
      have fermat_24 : (17 : ZMod 96946471) ^ 24236617 = 72516121 := by
        calc
          (17 : ZMod 96946471) ^ 24236617 = (17 : ZMod 96946471) ^ (12118308 + 12118308 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 12118308 * (17 : ZMod 96946471) ^ 12118308) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 72516121 := by rw [fermat_23]; decide
      have fermat_25 : (17 : ZMod 96946471) ^ 48473235 = 96946470 := by
        calc
          (17 : ZMod 96946471) ^ 48473235 = (17 : ZMod 96946471) ^ (24236617 + 24236617 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 24236617 * (17 : ZMod 96946471) ^ 24236617) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 96946470 := by rw [fermat_24]; decide
      have fermat_26 : (17 : ZMod 96946471) ^ 96946470 = 1 := by
        calc
          (17 : ZMod 96946471) ^ 96946470 = (17 : ZMod 96946471) ^ (48473235 + 48473235) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 48473235 * (17 : ZMod 96946471) ^ 48473235 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 4), (5, 1), (119687, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 4), (5, 1), (119687, 1)] : List FactorBlock).map factorBlockValue).prod = 96946471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (17 : ZMod 96946471) ^ 1 = 17 := by norm_num
      have factor_0_1 : (17 : ZMod 96946471) ^ 2 = 289 := by
        calc
          (17 : ZMod 96946471) ^ 2 = (17 : ZMod 96946471) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 1 * (17 : ZMod 96946471) ^ 1 := by rw [pow_add]
          _ = 289 := by rw [factor_0_0]; decide
      have factor_0_2 : (17 : ZMod 96946471) ^ 5 = 1419857 := by
        calc
          (17 : ZMod 96946471) ^ 5 = (17 : ZMod 96946471) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 2 * (17 : ZMod 96946471) ^ 2) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 1419857 := by rw [factor_0_1]; decide
      have factor_0_3 : (17 : ZMod 96946471) ^ 11 = 58505010 := by
        calc
          (17 : ZMod 96946471) ^ 11 = (17 : ZMod 96946471) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 5 * (17 : ZMod 96946471) ^ 5) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 58505010 := by rw [factor_0_2]; decide
      have factor_0_4 : (17 : ZMod 96946471) ^ 23 = 36392399 := by
        calc
          (17 : ZMod 96946471) ^ 23 = (17 : ZMod 96946471) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 11 * (17 : ZMod 96946471) ^ 11) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 36392399 := by rw [factor_0_3]; decide
      have factor_0_5 : (17 : ZMod 96946471) ^ 46 = 24206465 := by
        calc
          (17 : ZMod 96946471) ^ 46 = (17 : ZMod 96946471) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 23 * (17 : ZMod 96946471) ^ 23 := by rw [pow_add]
          _ = 24206465 := by rw [factor_0_4]; decide
      have factor_0_6 : (17 : ZMod 96946471) ^ 92 = 42729248 := by
        calc
          (17 : ZMod 96946471) ^ 92 = (17 : ZMod 96946471) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 46 * (17 : ZMod 96946471) ^ 46 := by rw [pow_add]
          _ = 42729248 := by rw [factor_0_5]; decide
      have factor_0_7 : (17 : ZMod 96946471) ^ 184 = 11947228 := by
        calc
          (17 : ZMod 96946471) ^ 184 = (17 : ZMod 96946471) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 92 * (17 : ZMod 96946471) ^ 92 := by rw [pow_add]
          _ = 11947228 := by rw [factor_0_6]; decide
      have factor_0_8 : (17 : ZMod 96946471) ^ 369 = 3189133 := by
        calc
          (17 : ZMod 96946471) ^ 369 = (17 : ZMod 96946471) ^ (184 + 184 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 184 * (17 : ZMod 96946471) ^ 184) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 3189133 := by rw [factor_0_7]; decide
      have factor_0_9 : (17 : ZMod 96946471) ^ 739 = 9521408 := by
        calc
          (17 : ZMod 96946471) ^ 739 = (17 : ZMod 96946471) ^ (369 + 369 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 369 * (17 : ZMod 96946471) ^ 369) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 9521408 := by rw [factor_0_8]; decide
      have factor_0_10 : (17 : ZMod 96946471) ^ 1479 = 80630709 := by
        calc
          (17 : ZMod 96946471) ^ 1479 = (17 : ZMod 96946471) ^ (739 + 739 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 739 * (17 : ZMod 96946471) ^ 739) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 80630709 := by rw [factor_0_9]; decide
      have factor_0_11 : (17 : ZMod 96946471) ^ 2958 = 35225867 := by
        calc
          (17 : ZMod 96946471) ^ 2958 = (17 : ZMod 96946471) ^ (1479 + 1479) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 1479 * (17 : ZMod 96946471) ^ 1479 := by rw [pow_add]
          _ = 35225867 := by rw [factor_0_10]; decide
      have factor_0_12 : (17 : ZMod 96946471) ^ 5917 = 64052549 := by
        calc
          (17 : ZMod 96946471) ^ 5917 = (17 : ZMod 96946471) ^ (2958 + 2958 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 2958 * (17 : ZMod 96946471) ^ 2958) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 64052549 := by rw [factor_0_11]; decide
      have factor_0_13 : (17 : ZMod 96946471) ^ 11834 = 42465242 := by
        calc
          (17 : ZMod 96946471) ^ 11834 = (17 : ZMod 96946471) ^ (5917 + 5917) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 5917 * (17 : ZMod 96946471) ^ 5917 := by rw [pow_add]
          _ = 42465242 := by rw [factor_0_12]; decide
      have factor_0_14 : (17 : ZMod 96946471) ^ 23668 = 27531701 := by
        calc
          (17 : ZMod 96946471) ^ 23668 = (17 : ZMod 96946471) ^ (11834 + 11834) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 11834 * (17 : ZMod 96946471) ^ 11834 := by rw [pow_add]
          _ = 27531701 := by rw [factor_0_13]; decide
      have factor_0_15 : (17 : ZMod 96946471) ^ 47337 = 44822270 := by
        calc
          (17 : ZMod 96946471) ^ 47337 = (17 : ZMod 96946471) ^ (23668 + 23668 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 23668 * (17 : ZMod 96946471) ^ 23668) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 44822270 := by rw [factor_0_14]; decide
      have factor_0_16 : (17 : ZMod 96946471) ^ 94674 = 15235134 := by
        calc
          (17 : ZMod 96946471) ^ 94674 = (17 : ZMod 96946471) ^ (47337 + 47337) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 47337 * (17 : ZMod 96946471) ^ 47337 := by rw [pow_add]
          _ = 15235134 := by rw [factor_0_15]; decide
      have factor_0_17 : (17 : ZMod 96946471) ^ 189348 = 67129756 := by
        calc
          (17 : ZMod 96946471) ^ 189348 = (17 : ZMod 96946471) ^ (94674 + 94674) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 94674 * (17 : ZMod 96946471) ^ 94674 := by rw [pow_add]
          _ = 67129756 := by rw [factor_0_16]; decide
      have factor_0_18 : (17 : ZMod 96946471) ^ 378697 = 24075775 := by
        calc
          (17 : ZMod 96946471) ^ 378697 = (17 : ZMod 96946471) ^ (189348 + 189348 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 189348 * (17 : ZMod 96946471) ^ 189348) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 24075775 := by rw [factor_0_17]; decide
      have factor_0_19 : (17 : ZMod 96946471) ^ 757394 = 88688096 := by
        calc
          (17 : ZMod 96946471) ^ 757394 = (17 : ZMod 96946471) ^ (378697 + 378697) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 378697 * (17 : ZMod 96946471) ^ 378697 := by rw [pow_add]
          _ = 88688096 := by rw [factor_0_18]; decide
      have factor_0_20 : (17 : ZMod 96946471) ^ 1514788 = 78649777 := by
        calc
          (17 : ZMod 96946471) ^ 1514788 = (17 : ZMod 96946471) ^ (757394 + 757394) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 757394 * (17 : ZMod 96946471) ^ 757394 := by rw [pow_add]
          _ = 78649777 := by rw [factor_0_19]; decide
      have factor_0_21 : (17 : ZMod 96946471) ^ 3029577 = 74980120 := by
        calc
          (17 : ZMod 96946471) ^ 3029577 = (17 : ZMod 96946471) ^ (1514788 + 1514788 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 1514788 * (17 : ZMod 96946471) ^ 1514788) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 74980120 := by rw [factor_0_20]; decide
      have factor_0_22 : (17 : ZMod 96946471) ^ 6059154 = 54991066 := by
        calc
          (17 : ZMod 96946471) ^ 6059154 = (17 : ZMod 96946471) ^ (3029577 + 3029577) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 3029577 * (17 : ZMod 96946471) ^ 3029577 := by rw [pow_add]
          _ = 54991066 := by rw [factor_0_21]; decide
      have factor_0_23 : (17 : ZMod 96946471) ^ 12118308 = 1178206 := by
        calc
          (17 : ZMod 96946471) ^ 12118308 = (17 : ZMod 96946471) ^ (6059154 + 6059154) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 6059154 * (17 : ZMod 96946471) ^ 6059154 := by rw [pow_add]
          _ = 1178206 := by rw [factor_0_22]; decide
      have factor_0_24 : (17 : ZMod 96946471) ^ 24236617 = 72516121 := by
        calc
          (17 : ZMod 96946471) ^ 24236617 = (17 : ZMod 96946471) ^ (12118308 + 12118308 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 12118308 * (17 : ZMod 96946471) ^ 12118308) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 72516121 := by rw [factor_0_23]; decide
      have factor_0_25 : (17 : ZMod 96946471) ^ 48473235 = 96946470 := by
        calc
          (17 : ZMod 96946471) ^ 48473235 = (17 : ZMod 96946471) ^ (24236617 + 24236617 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 24236617 * (17 : ZMod 96946471) ^ 24236617) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 96946470 := by rw [factor_0_24]; decide
      change (17 : ZMod 96946471) ^ 48473235 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (17 : ZMod 96946471) ^ 1 = 17 := by norm_num
      have factor_1_1 : (17 : ZMod 96946471) ^ 3 = 4913 := by
        calc
          (17 : ZMod 96946471) ^ 3 = (17 : ZMod 96946471) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 1 * (17 : ZMod 96946471) ^ 1) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 4913 := by rw [factor_1_0]; decide
      have factor_1_2 : (17 : ZMod 96946471) ^ 7 = 22552789 := by
        calc
          (17 : ZMod 96946471) ^ 7 = (17 : ZMod 96946471) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 3 * (17 : ZMod 96946471) ^ 3) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 22552789 := by rw [factor_1_1]; decide
      have factor_1_3 : (17 : ZMod 96946471) ^ 15 = 3962397 := by
        calc
          (17 : ZMod 96946471) ^ 15 = (17 : ZMod 96946471) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 7 * (17 : ZMod 96946471) ^ 7) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 3962397 := by rw [factor_1_2]; decide
      have factor_1_4 : (17 : ZMod 96946471) ^ 30 = 12060688 := by
        calc
          (17 : ZMod 96946471) ^ 30 = (17 : ZMod 96946471) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 15 * (17 : ZMod 96946471) ^ 15 := by rw [pow_add]
          _ = 12060688 := by rw [factor_1_3]; decide
      have factor_1_5 : (17 : ZMod 96946471) ^ 61 = 82069219 := by
        calc
          (17 : ZMod 96946471) ^ 61 = (17 : ZMod 96946471) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 30 * (17 : ZMod 96946471) ^ 30) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 82069219 := by rw [factor_1_4]; decide
      have factor_1_6 : (17 : ZMod 96946471) ^ 123 = 26206056 := by
        calc
          (17 : ZMod 96946471) ^ 123 = (17 : ZMod 96946471) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 61 * (17 : ZMod 96946471) ^ 61) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 26206056 := by rw [factor_1_5]; decide
      have factor_1_7 : (17 : ZMod 96946471) ^ 246 = 10194714 := by
        calc
          (17 : ZMod 96946471) ^ 246 = (17 : ZMod 96946471) ^ (123 + 123) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 123 * (17 : ZMod 96946471) ^ 123 := by rw [pow_add]
          _ = 10194714 := by rw [factor_1_6]; decide
      have factor_1_8 : (17 : ZMod 96946471) ^ 493 = 86004365 := by
        calc
          (17 : ZMod 96946471) ^ 493 = (17 : ZMod 96946471) ^ (246 + 246 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 246 * (17 : ZMod 96946471) ^ 246) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 86004365 := by rw [factor_1_7]; decide
      have factor_1_9 : (17 : ZMod 96946471) ^ 986 = 16458468 := by
        calc
          (17 : ZMod 96946471) ^ 986 = (17 : ZMod 96946471) ^ (493 + 493) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 493 * (17 : ZMod 96946471) ^ 493 := by rw [pow_add]
          _ = 16458468 := by rw [factor_1_8]; decide
      have factor_1_10 : (17 : ZMod 96946471) ^ 1972 = 28945323 := by
        calc
          (17 : ZMod 96946471) ^ 1972 = (17 : ZMod 96946471) ^ (986 + 986) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 986 * (17 : ZMod 96946471) ^ 986 := by rw [pow_add]
          _ = 28945323 := by rw [factor_1_9]; decide
      have factor_1_11 : (17 : ZMod 96946471) ^ 3944 = 59379890 := by
        calc
          (17 : ZMod 96946471) ^ 3944 = (17 : ZMod 96946471) ^ (1972 + 1972) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 1972 * (17 : ZMod 96946471) ^ 1972 := by rw [pow_add]
          _ = 59379890 := by rw [factor_1_10]; decide
      have factor_1_12 : (17 : ZMod 96946471) ^ 7889 = 54956018 := by
        calc
          (17 : ZMod 96946471) ^ 7889 = (17 : ZMod 96946471) ^ (3944 + 3944 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 3944 * (17 : ZMod 96946471) ^ 3944) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 54956018 := by rw [factor_1_11]; decide
      have factor_1_13 : (17 : ZMod 96946471) ^ 15779 = 69827194 := by
        calc
          (17 : ZMod 96946471) ^ 15779 = (17 : ZMod 96946471) ^ (7889 + 7889 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 7889 * (17 : ZMod 96946471) ^ 7889) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 69827194 := by rw [factor_1_12]; decide
      have factor_1_14 : (17 : ZMod 96946471) ^ 31558 = 60595471 := by
        calc
          (17 : ZMod 96946471) ^ 31558 = (17 : ZMod 96946471) ^ (15779 + 15779) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 15779 * (17 : ZMod 96946471) ^ 15779 := by rw [pow_add]
          _ = 60595471 := by rw [factor_1_13]; decide
      have factor_1_15 : (17 : ZMod 96946471) ^ 63116 = 65406408 := by
        calc
          (17 : ZMod 96946471) ^ 63116 = (17 : ZMod 96946471) ^ (31558 + 31558) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 31558 * (17 : ZMod 96946471) ^ 31558 := by rw [pow_add]
          _ = 65406408 := by rw [factor_1_14]; decide
      have factor_1_16 : (17 : ZMod 96946471) ^ 126232 = 79395289 := by
        calc
          (17 : ZMod 96946471) ^ 126232 = (17 : ZMod 96946471) ^ (63116 + 63116) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 63116 * (17 : ZMod 96946471) ^ 63116 := by rw [pow_add]
          _ = 79395289 := by rw [factor_1_15]; decide
      have factor_1_17 : (17 : ZMod 96946471) ^ 252464 = 68067580 := by
        calc
          (17 : ZMod 96946471) ^ 252464 = (17 : ZMod 96946471) ^ (126232 + 126232) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 126232 * (17 : ZMod 96946471) ^ 126232 := by rw [pow_add]
          _ = 68067580 := by rw [factor_1_16]; decide
      have factor_1_18 : (17 : ZMod 96946471) ^ 504929 = 44562817 := by
        calc
          (17 : ZMod 96946471) ^ 504929 = (17 : ZMod 96946471) ^ (252464 + 252464 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 252464 * (17 : ZMod 96946471) ^ 252464) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 44562817 := by rw [factor_1_17]; decide
      have factor_1_19 : (17 : ZMod 96946471) ^ 1009859 = 28853455 := by
        calc
          (17 : ZMod 96946471) ^ 1009859 = (17 : ZMod 96946471) ^ (504929 + 504929 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 504929 * (17 : ZMod 96946471) ^ 504929) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 28853455 := by rw [factor_1_18]; decide
      have factor_1_20 : (17 : ZMod 96946471) ^ 2019718 = 56405727 := by
        calc
          (17 : ZMod 96946471) ^ 2019718 = (17 : ZMod 96946471) ^ (1009859 + 1009859) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 1009859 * (17 : ZMod 96946471) ^ 1009859 := by rw [pow_add]
          _ = 56405727 := by rw [factor_1_19]; decide
      have factor_1_21 : (17 : ZMod 96946471) ^ 4039436 = 78327517 := by
        calc
          (17 : ZMod 96946471) ^ 4039436 = (17 : ZMod 96946471) ^ (2019718 + 2019718) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 2019718 * (17 : ZMod 96946471) ^ 2019718 := by rw [pow_add]
          _ = 78327517 := by rw [factor_1_20]; decide
      have factor_1_22 : (17 : ZMod 96946471) ^ 8078872 = 88354063 := by
        calc
          (17 : ZMod 96946471) ^ 8078872 = (17 : ZMod 96946471) ^ (4039436 + 4039436) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 4039436 * (17 : ZMod 96946471) ^ 4039436 := by rw [pow_add]
          _ = 88354063 := by rw [factor_1_21]; decide
      have factor_1_23 : (17 : ZMod 96946471) ^ 16157745 = 73152458 := by
        calc
          (17 : ZMod 96946471) ^ 16157745 = (17 : ZMod 96946471) ^ (8078872 + 8078872 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 8078872 * (17 : ZMod 96946471) ^ 8078872) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 73152458 := by rw [factor_1_22]; decide
      have factor_1_24 : (17 : ZMod 96946471) ^ 32315490 = 73152457 := by
        calc
          (17 : ZMod 96946471) ^ 32315490 = (17 : ZMod 96946471) ^ (16157745 + 16157745) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 16157745 * (17 : ZMod 96946471) ^ 16157745 := by rw [pow_add]
          _ = 73152457 := by rw [factor_1_23]; decide
      change (17 : ZMod 96946471) ^ 32315490 ≠ 1
      rw [factor_1_24]
      decide
    ·
      have factor_2_0 : (17 : ZMod 96946471) ^ 1 = 17 := by norm_num
      have factor_2_1 : (17 : ZMod 96946471) ^ 2 = 289 := by
        calc
          (17 : ZMod 96946471) ^ 2 = (17 : ZMod 96946471) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 1 * (17 : ZMod 96946471) ^ 1 := by rw [pow_add]
          _ = 289 := by rw [factor_2_0]; decide
      have factor_2_2 : (17 : ZMod 96946471) ^ 4 = 83521 := by
        calc
          (17 : ZMod 96946471) ^ 4 = (17 : ZMod 96946471) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 2 * (17 : ZMod 96946471) ^ 2 := by rw [pow_add]
          _ = 83521 := by rw [factor_2_1]; decide
      have factor_2_3 : (17 : ZMod 96946471) ^ 9 = 22342464 := by
        calc
          (17 : ZMod 96946471) ^ 9 = (17 : ZMod 96946471) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 4 * (17 : ZMod 96946471) ^ 4) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 22342464 := by rw [factor_2_2]; decide
      have factor_2_4 : (17 : ZMod 96946471) ^ 18 = 77962261 := by
        calc
          (17 : ZMod 96946471) ^ 18 = (17 : ZMod 96946471) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 9 * (17 : ZMod 96946471) ^ 9 := by rw [pow_add]
          _ = 77962261 := by rw [factor_2_3]; decide
      have factor_2_5 : (17 : ZMod 96946471) ^ 36 = 75291593 := by
        calc
          (17 : ZMod 96946471) ^ 36 = (17 : ZMod 96946471) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 18 * (17 : ZMod 96946471) ^ 18 := by rw [pow_add]
          _ = 75291593 := by rw [factor_2_4]; decide
      have factor_2_6 : (17 : ZMod 96946471) ^ 73 = 93766117 := by
        calc
          (17 : ZMod 96946471) ^ 73 = (17 : ZMod 96946471) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 36 * (17 : ZMod 96946471) ^ 36) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 93766117 := by rw [factor_2_5]; decide
      have factor_2_7 : (17 : ZMod 96946471) ^ 147 = 65267693 := by
        calc
          (17 : ZMod 96946471) ^ 147 = (17 : ZMod 96946471) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 73 * (17 : ZMod 96946471) ^ 73) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 65267693 := by rw [factor_2_6]; decide
      have factor_2_8 : (17 : ZMod 96946471) ^ 295 = 91848011 := by
        calc
          (17 : ZMod 96946471) ^ 295 = (17 : ZMod 96946471) ^ (147 + 147 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 147 * (17 : ZMod 96946471) ^ 147) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 91848011 := by rw [factor_2_7]; decide
      have factor_2_9 : (17 : ZMod 96946471) ^ 591 = 49061464 := by
        calc
          (17 : ZMod 96946471) ^ 591 = (17 : ZMod 96946471) ^ (295 + 295 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 295 * (17 : ZMod 96946471) ^ 295) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 49061464 := by rw [factor_2_8]; decide
      have factor_2_10 : (17 : ZMod 96946471) ^ 1183 = 14168301 := by
        calc
          (17 : ZMod 96946471) ^ 1183 = (17 : ZMod 96946471) ^ (591 + 591 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 591 * (17 : ZMod 96946471) ^ 591) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 14168301 := by rw [factor_2_9]; decide
      have factor_2_11 : (17 : ZMod 96946471) ^ 2366 = 94193987 := by
        calc
          (17 : ZMod 96946471) ^ 2366 = (17 : ZMod 96946471) ^ (1183 + 1183) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 1183 * (17 : ZMod 96946471) ^ 1183 := by rw [pow_add]
          _ = 94193987 := by rw [factor_2_10]; decide
      have factor_2_12 : (17 : ZMod 96946471) ^ 4733 = 17973787 := by
        calc
          (17 : ZMod 96946471) ^ 4733 = (17 : ZMod 96946471) ^ (2366 + 2366 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 2366 * (17 : ZMod 96946471) ^ 2366) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 17973787 := by rw [factor_2_11]; decide
      have factor_2_13 : (17 : ZMod 96946471) ^ 9467 = 22255831 := by
        calc
          (17 : ZMod 96946471) ^ 9467 = (17 : ZMod 96946471) ^ (4733 + 4733 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 4733 * (17 : ZMod 96946471) ^ 4733) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 22255831 := by rw [factor_2_12]; decide
      have factor_2_14 : (17 : ZMod 96946471) ^ 18934 = 1580289 := by
        calc
          (17 : ZMod 96946471) ^ 18934 = (17 : ZMod 96946471) ^ (9467 + 9467) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 9467 * (17 : ZMod 96946471) ^ 9467 := by rw [pow_add]
          _ = 1580289 := by rw [factor_2_13]; decide
      have factor_2_15 : (17 : ZMod 96946471) ^ 37869 = 12651892 := by
        calc
          (17 : ZMod 96946471) ^ 37869 = (17 : ZMod 96946471) ^ (18934 + 18934 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 18934 * (17 : ZMod 96946471) ^ 18934) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 12651892 := by rw [factor_2_14]; decide
      have factor_2_16 : (17 : ZMod 96946471) ^ 75739 = 95713499 := by
        calc
          (17 : ZMod 96946471) ^ 75739 = (17 : ZMod 96946471) ^ (37869 + 37869 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 37869 * (17 : ZMod 96946471) ^ 37869) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 95713499 := by rw [factor_2_15]; decide
      have factor_2_17 : (17 : ZMod 96946471) ^ 151478 = 2341033 := by
        calc
          (17 : ZMod 96946471) ^ 151478 = (17 : ZMod 96946471) ^ (75739 + 75739) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 75739 * (17 : ZMod 96946471) ^ 75739 := by rw [pow_add]
          _ = 2341033 := by rw [factor_2_16]; decide
      have factor_2_18 : (17 : ZMod 96946471) ^ 302957 = 3006564 := by
        calc
          (17 : ZMod 96946471) ^ 302957 = (17 : ZMod 96946471) ^ (151478 + 151478 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 151478 * (17 : ZMod 96946471) ^ 151478) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 3006564 := by rw [factor_2_17]; decide
      have factor_2_19 : (17 : ZMod 96946471) ^ 605915 = 21495648 := by
        calc
          (17 : ZMod 96946471) ^ 605915 = (17 : ZMod 96946471) ^ (302957 + 302957 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 302957 * (17 : ZMod 96946471) ^ 302957) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 21495648 := by rw [factor_2_18]; decide
      have factor_2_20 : (17 : ZMod 96946471) ^ 1211830 = 5986189 := by
        calc
          (17 : ZMod 96946471) ^ 1211830 = (17 : ZMod 96946471) ^ (605915 + 605915) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 605915 * (17 : ZMod 96946471) ^ 605915 := by rw [pow_add]
          _ = 5986189 := by rw [factor_2_19]; decide
      have factor_2_21 : (17 : ZMod 96946471) ^ 2423661 = 59587014 := by
        calc
          (17 : ZMod 96946471) ^ 2423661 = (17 : ZMod 96946471) ^ (1211830 + 1211830 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 1211830 * (17 : ZMod 96946471) ^ 1211830) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 59587014 := by rw [factor_2_20]; decide
      have factor_2_22 : (17 : ZMod 96946471) ^ 4847323 = 44447047 := by
        calc
          (17 : ZMod 96946471) ^ 4847323 = (17 : ZMod 96946471) ^ (2423661 + 2423661 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 2423661 * (17 : ZMod 96946471) ^ 2423661) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 44447047 := by rw [factor_2_21]; decide
      have factor_2_23 : (17 : ZMod 96946471) ^ 9694647 = 67263036 := by
        calc
          (17 : ZMod 96946471) ^ 9694647 = (17 : ZMod 96946471) ^ (4847323 + 4847323 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 4847323 * (17 : ZMod 96946471) ^ 4847323) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 67263036 := by rw [factor_2_22]; decide
      have factor_2_24 : (17 : ZMod 96946471) ^ 19389294 = 71265690 := by
        calc
          (17 : ZMod 96946471) ^ 19389294 = (17 : ZMod 96946471) ^ (9694647 + 9694647) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 9694647 * (17 : ZMod 96946471) ^ 9694647 := by rw [pow_add]
          _ = 71265690 := by rw [factor_2_23]; decide
      change (17 : ZMod 96946471) ^ 19389294 ≠ 1
      rw [factor_2_24]
      decide
    ·
      have factor_3_0 : (17 : ZMod 96946471) ^ 1 = 17 := by norm_num
      have factor_3_1 : (17 : ZMod 96946471) ^ 3 = 4913 := by
        calc
          (17 : ZMod 96946471) ^ 3 = (17 : ZMod 96946471) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 1 * (17 : ZMod 96946471) ^ 1) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 4913 := by rw [factor_3_0]; decide
      have factor_3_2 : (17 : ZMod 96946471) ^ 6 = 24137569 := by
        calc
          (17 : ZMod 96946471) ^ 6 = (17 : ZMod 96946471) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 3 * (17 : ZMod 96946471) ^ 3 := by rw [pow_add]
          _ = 24137569 := by rw [factor_3_1]; decide
      have factor_3_3 : (17 : ZMod 96946471) ^ 12 = 25120460 := by
        calc
          (17 : ZMod 96946471) ^ 12 = (17 : ZMod 96946471) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 6 * (17 : ZMod 96946471) ^ 6 := by rw [pow_add]
          _ = 25120460 := by rw [factor_3_2]; decide
      have factor_3_4 : (17 : ZMod 96946471) ^ 25 = 47184443 := by
        calc
          (17 : ZMod 96946471) ^ 25 = (17 : ZMod 96946471) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 12 * (17 : ZMod 96946471) ^ 12) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 47184443 := by rw [factor_3_3]; decide
      have factor_3_5 : (17 : ZMod 96946471) ^ 50 = 26457031 := by
        calc
          (17 : ZMod 96946471) ^ 50 = (17 : ZMod 96946471) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 25 * (17 : ZMod 96946471) ^ 25 := by rw [pow_add]
          _ = 26457031 := by rw [factor_3_4]; decide
      have factor_3_6 : (17 : ZMod 96946471) ^ 101 = 92926941 := by
        calc
          (17 : ZMod 96946471) ^ 101 = (17 : ZMod 96946471) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 50 * (17 : ZMod 96946471) ^ 50) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 92926941 := by rw [factor_3_5]; decide
      have factor_3_7 : (17 : ZMod 96946471) ^ 202 = 7296395 := by
        calc
          (17 : ZMod 96946471) ^ 202 = (17 : ZMod 96946471) ^ (101 + 101) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 101 * (17 : ZMod 96946471) ^ 101 := by rw [pow_add]
          _ = 7296395 := by rw [factor_3_6]; decide
      have factor_3_8 : (17 : ZMod 96946471) ^ 405 = 17308431 := by
        calc
          (17 : ZMod 96946471) ^ 405 = (17 : ZMod 96946471) ^ (202 + 202 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = ((17 : ZMod 96946471) ^ 202 * (17 : ZMod 96946471) ^ 202) * (17 : ZMod 96946471) := by rw [pow_succ, pow_add]
          _ = 17308431 := by rw [factor_3_7]; decide
      have factor_3_9 : (17 : ZMod 96946471) ^ 810 = 28766394 := by
        calc
          (17 : ZMod 96946471) ^ 810 = (17 : ZMod 96946471) ^ (405 + 405) :=
            congrArg (fun n : ℕ => (17 : ZMod 96946471) ^ n) (by norm_num)
          _ = (17 : ZMod 96946471) ^ 405 * (17 : ZMod 96946471) ^ 405 := by rw [pow_add]
          _ = 28766394 := by rw [factor_3_8]; decide
      change (17 : ZMod 96946471) ^ 810 ≠ 1
      rw [factor_3_9]
      decide

#print axioms prime_lucas_96946471

end TotientTailPeriodKiller
end Erdos249257
