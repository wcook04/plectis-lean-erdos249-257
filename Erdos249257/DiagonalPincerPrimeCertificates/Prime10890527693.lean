import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_10890527693 : Nat.Prime 10890527693 := by
  apply lucas_primality 10890527693 (2 : ZMod 10890527693)
  ·
      have fermat_0 : (2 : ZMod 10890527693) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 10890527693) ^ 2 = 4 := by
        calc
          (2 : ZMod 10890527693) ^ 2 = (2 : ZMod 10890527693) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 1 * (2 : ZMod 10890527693) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 10890527693) ^ 5 = 32 := by
        calc
          (2 : ZMod 10890527693) ^ 5 = (2 : ZMod 10890527693) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 2 * (2 : ZMod 10890527693) ^ 2) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 10890527693) ^ 10 = 1024 := by
        calc
          (2 : ZMod 10890527693) ^ 10 = (2 : ZMod 10890527693) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 5 * (2 : ZMod 10890527693) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 10890527693) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 10890527693) ^ 20 = (2 : ZMod 10890527693) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 10 * (2 : ZMod 10890527693) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 10890527693) ^ 40 = 10458858476 := by
        calc
          (2 : ZMod 10890527693) ^ 40 = (2 : ZMod 10890527693) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 20 * (2 : ZMod 10890527693) ^ 20 := by rw [pow_add]
          _ = 10458858476 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 10890527693) ^ 81 = 1962292156 := by
        calc
          (2 : ZMod 10890527693) ^ 81 = (2 : ZMod 10890527693) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 40 * (2 : ZMod 10890527693) ^ 40) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 1962292156 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 10890527693) ^ 162 = 1744908951 := by
        calc
          (2 : ZMod 10890527693) ^ 162 = (2 : ZMod 10890527693) ^ (81 + 81) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 81 * (2 : ZMod 10890527693) ^ 81 := by rw [pow_add]
          _ = 1744908951 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 10890527693) ^ 324 = 1542546166 := by
        calc
          (2 : ZMod 10890527693) ^ 324 = (2 : ZMod 10890527693) ^ (162 + 162) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 162 * (2 : ZMod 10890527693) ^ 162 := by rw [pow_add]
          _ = 1542546166 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 10890527693) ^ 649 = 3367522001 := by
        calc
          (2 : ZMod 10890527693) ^ 649 = (2 : ZMod 10890527693) ^ (324 + 324 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 324 * (2 : ZMod 10890527693) ^ 324) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 3367522001 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 10890527693) ^ 1298 = 6523682797 := by
        calc
          (2 : ZMod 10890527693) ^ 1298 = (2 : ZMod 10890527693) ^ (649 + 649) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 649 * (2 : ZMod 10890527693) ^ 649 := by rw [pow_add]
          _ = 6523682797 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 10890527693) ^ 2596 = 881992599 := by
        calc
          (2 : ZMod 10890527693) ^ 2596 = (2 : ZMod 10890527693) ^ (1298 + 1298) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 1298 * (2 : ZMod 10890527693) ^ 1298 := by rw [pow_add]
          _ = 881992599 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 10890527693) ^ 5193 = 3216272609 := by
        calc
          (2 : ZMod 10890527693) ^ 5193 = (2 : ZMod 10890527693) ^ (2596 + 2596 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 2596 * (2 : ZMod 10890527693) ^ 2596) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 3216272609 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 10890527693) ^ 10386 = 1033914226 := by
        calc
          (2 : ZMod 10890527693) ^ 10386 = (2 : ZMod 10890527693) ^ (5193 + 5193) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 5193 * (2 : ZMod 10890527693) ^ 5193 := by rw [pow_add]
          _ = 1033914226 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 10890527693) ^ 20772 = 7734272107 := by
        calc
          (2 : ZMod 10890527693) ^ 20772 = (2 : ZMod 10890527693) ^ (10386 + 10386) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 10386 * (2 : ZMod 10890527693) ^ 10386 := by rw [pow_add]
          _ = 7734272107 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 10890527693) ^ 41544 = 2750062085 := by
        calc
          (2 : ZMod 10890527693) ^ 41544 = (2 : ZMod 10890527693) ^ (20772 + 20772) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 20772 * (2 : ZMod 10890527693) ^ 20772 := by rw [pow_add]
          _ = 2750062085 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 10890527693) ^ 83088 = 5593087275 := by
        calc
          (2 : ZMod 10890527693) ^ 83088 = (2 : ZMod 10890527693) ^ (41544 + 41544) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 41544 * (2 : ZMod 10890527693) ^ 41544 := by rw [pow_add]
          _ = 5593087275 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 10890527693) ^ 166176 = 6599079733 := by
        calc
          (2 : ZMod 10890527693) ^ 166176 = (2 : ZMod 10890527693) ^ (83088 + 83088) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 83088 * (2 : ZMod 10890527693) ^ 83088 := by rw [pow_add]
          _ = 6599079733 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 10890527693) ^ 332352 = 4616446862 := by
        calc
          (2 : ZMod 10890527693) ^ 332352 = (2 : ZMod 10890527693) ^ (166176 + 166176) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 166176 * (2 : ZMod 10890527693) ^ 166176 := by rw [pow_add]
          _ = 4616446862 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 10890527693) ^ 664705 = 2612850402 := by
        calc
          (2 : ZMod 10890527693) ^ 664705 = (2 : ZMod 10890527693) ^ (332352 + 332352 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 332352 * (2 : ZMod 10890527693) ^ 332352) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 2612850402 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 10890527693) ^ 1329410 = 3759535080 := by
        calc
          (2 : ZMod 10890527693) ^ 1329410 = (2 : ZMod 10890527693) ^ (664705 + 664705) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 664705 * (2 : ZMod 10890527693) ^ 664705 := by rw [pow_add]
          _ = 3759535080 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 10890527693) ^ 2658820 = 6129614731 := by
        calc
          (2 : ZMod 10890527693) ^ 2658820 = (2 : ZMod 10890527693) ^ (1329410 + 1329410) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 1329410 * (2 : ZMod 10890527693) ^ 1329410 := by rw [pow_add]
          _ = 6129614731 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 10890527693) ^ 5317640 = 8169860733 := by
        calc
          (2 : ZMod 10890527693) ^ 5317640 = (2 : ZMod 10890527693) ^ (2658820 + 2658820) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 2658820 * (2 : ZMod 10890527693) ^ 2658820 := by rw [pow_add]
          _ = 8169860733 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 10890527693) ^ 10635280 = 7875744471 := by
        calc
          (2 : ZMod 10890527693) ^ 10635280 = (2 : ZMod 10890527693) ^ (5317640 + 5317640) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 5317640 * (2 : ZMod 10890527693) ^ 5317640 := by rw [pow_add]
          _ = 7875744471 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 10890527693) ^ 21270561 = 3415124351 := by
        calc
          (2 : ZMod 10890527693) ^ 21270561 = (2 : ZMod 10890527693) ^ (10635280 + 10635280 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 10635280 * (2 : ZMod 10890527693) ^ 10635280) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 3415124351 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 10890527693) ^ 42541123 = 748325885 := by
        calc
          (2 : ZMod 10890527693) ^ 42541123 = (2 : ZMod 10890527693) ^ (21270561 + 21270561 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 21270561 * (2 : ZMod 10890527693) ^ 21270561) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 748325885 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 10890527693) ^ 85082247 = 9276929439 := by
        calc
          (2 : ZMod 10890527693) ^ 85082247 = (2 : ZMod 10890527693) ^ (42541123 + 42541123 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 42541123 * (2 : ZMod 10890527693) ^ 42541123) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 9276929439 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 10890527693) ^ 170164495 = 3357691900 := by
        calc
          (2 : ZMod 10890527693) ^ 170164495 = (2 : ZMod 10890527693) ^ (85082247 + 85082247 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 85082247 * (2 : ZMod 10890527693) ^ 85082247) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 3357691900 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 10890527693) ^ 340328990 = 7222005206 := by
        calc
          (2 : ZMod 10890527693) ^ 340328990 = (2 : ZMod 10890527693) ^ (170164495 + 170164495) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 170164495 * (2 : ZMod 10890527693) ^ 170164495 := by rw [pow_add]
          _ = 7222005206 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 10890527693) ^ 680657980 = 4923569598 := by
        calc
          (2 : ZMod 10890527693) ^ 680657980 = (2 : ZMod 10890527693) ^ (340328990 + 340328990) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 340328990 * (2 : ZMod 10890527693) ^ 340328990 := by rw [pow_add]
          _ = 4923569598 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 10890527693) ^ 1361315961 = 5327665080 := by
        calc
          (2 : ZMod 10890527693) ^ 1361315961 = (2 : ZMod 10890527693) ^ (680657980 + 680657980 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 680657980 * (2 : ZMod 10890527693) ^ 680657980) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 5327665080 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 10890527693) ^ 2722631923 = 10655330159 := by
        calc
          (2 : ZMod 10890527693) ^ 2722631923 = (2 : ZMod 10890527693) ^ (1361315961 + 1361315961 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 1361315961 * (2 : ZMod 10890527693) ^ 1361315961) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 10655330159 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 10890527693) ^ 5445263846 = 10890527692 := by
        calc
          (2 : ZMod 10890527693) ^ 5445263846 = (2 : ZMod 10890527693) ^ (2722631923 + 2722631923) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 2722631923 * (2 : ZMod 10890527693) ^ 2722631923 := by rw [pow_add]
          _ = 10890527692 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 10890527693) ^ 10890527692 = 1 := by
        calc
          (2 : ZMod 10890527693) ^ 10890527692 = (2 : ZMod 10890527693) ^ (5445263846 + 5445263846) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 5445263846 * (2 : ZMod 10890527693) ^ 5445263846 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (17, 1), (19, 1), (23, 1), (33317, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (17, 1), (19, 1), (23, 1), (33317, 1)] : List FactorBlock).map factorBlockValue).prod = 10890527693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 10890527693) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 10890527693) ^ 2 = 4 := by
        calc
          (2 : ZMod 10890527693) ^ 2 = (2 : ZMod 10890527693) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 1 * (2 : ZMod 10890527693) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 10890527693) ^ 5 = 32 := by
        calc
          (2 : ZMod 10890527693) ^ 5 = (2 : ZMod 10890527693) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 2 * (2 : ZMod 10890527693) ^ 2) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 10890527693) ^ 10 = 1024 := by
        calc
          (2 : ZMod 10890527693) ^ 10 = (2 : ZMod 10890527693) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 5 * (2 : ZMod 10890527693) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 10890527693) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 10890527693) ^ 20 = (2 : ZMod 10890527693) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 10 * (2 : ZMod 10890527693) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 10890527693) ^ 40 = 10458858476 := by
        calc
          (2 : ZMod 10890527693) ^ 40 = (2 : ZMod 10890527693) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 20 * (2 : ZMod 10890527693) ^ 20 := by rw [pow_add]
          _ = 10458858476 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 10890527693) ^ 81 = 1962292156 := by
        calc
          (2 : ZMod 10890527693) ^ 81 = (2 : ZMod 10890527693) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 40 * (2 : ZMod 10890527693) ^ 40) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 1962292156 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 10890527693) ^ 162 = 1744908951 := by
        calc
          (2 : ZMod 10890527693) ^ 162 = (2 : ZMod 10890527693) ^ (81 + 81) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 81 * (2 : ZMod 10890527693) ^ 81 := by rw [pow_add]
          _ = 1744908951 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 10890527693) ^ 324 = 1542546166 := by
        calc
          (2 : ZMod 10890527693) ^ 324 = (2 : ZMod 10890527693) ^ (162 + 162) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 162 * (2 : ZMod 10890527693) ^ 162 := by rw [pow_add]
          _ = 1542546166 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 10890527693) ^ 649 = 3367522001 := by
        calc
          (2 : ZMod 10890527693) ^ 649 = (2 : ZMod 10890527693) ^ (324 + 324 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 324 * (2 : ZMod 10890527693) ^ 324) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 3367522001 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 10890527693) ^ 1298 = 6523682797 := by
        calc
          (2 : ZMod 10890527693) ^ 1298 = (2 : ZMod 10890527693) ^ (649 + 649) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 649 * (2 : ZMod 10890527693) ^ 649 := by rw [pow_add]
          _ = 6523682797 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 10890527693) ^ 2596 = 881992599 := by
        calc
          (2 : ZMod 10890527693) ^ 2596 = (2 : ZMod 10890527693) ^ (1298 + 1298) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 1298 * (2 : ZMod 10890527693) ^ 1298 := by rw [pow_add]
          _ = 881992599 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 10890527693) ^ 5193 = 3216272609 := by
        calc
          (2 : ZMod 10890527693) ^ 5193 = (2 : ZMod 10890527693) ^ (2596 + 2596 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 2596 * (2 : ZMod 10890527693) ^ 2596) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 3216272609 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 10890527693) ^ 10386 = 1033914226 := by
        calc
          (2 : ZMod 10890527693) ^ 10386 = (2 : ZMod 10890527693) ^ (5193 + 5193) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 5193 * (2 : ZMod 10890527693) ^ 5193 := by rw [pow_add]
          _ = 1033914226 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 10890527693) ^ 20772 = 7734272107 := by
        calc
          (2 : ZMod 10890527693) ^ 20772 = (2 : ZMod 10890527693) ^ (10386 + 10386) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 10386 * (2 : ZMod 10890527693) ^ 10386 := by rw [pow_add]
          _ = 7734272107 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 10890527693) ^ 41544 = 2750062085 := by
        calc
          (2 : ZMod 10890527693) ^ 41544 = (2 : ZMod 10890527693) ^ (20772 + 20772) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 20772 * (2 : ZMod 10890527693) ^ 20772 := by rw [pow_add]
          _ = 2750062085 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 10890527693) ^ 83088 = 5593087275 := by
        calc
          (2 : ZMod 10890527693) ^ 83088 = (2 : ZMod 10890527693) ^ (41544 + 41544) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 41544 * (2 : ZMod 10890527693) ^ 41544 := by rw [pow_add]
          _ = 5593087275 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 10890527693) ^ 166176 = 6599079733 := by
        calc
          (2 : ZMod 10890527693) ^ 166176 = (2 : ZMod 10890527693) ^ (83088 + 83088) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 83088 * (2 : ZMod 10890527693) ^ 83088 := by rw [pow_add]
          _ = 6599079733 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 10890527693) ^ 332352 = 4616446862 := by
        calc
          (2 : ZMod 10890527693) ^ 332352 = (2 : ZMod 10890527693) ^ (166176 + 166176) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 166176 * (2 : ZMod 10890527693) ^ 166176 := by rw [pow_add]
          _ = 4616446862 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 10890527693) ^ 664705 = 2612850402 := by
        calc
          (2 : ZMod 10890527693) ^ 664705 = (2 : ZMod 10890527693) ^ (332352 + 332352 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 332352 * (2 : ZMod 10890527693) ^ 332352) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 2612850402 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 10890527693) ^ 1329410 = 3759535080 := by
        calc
          (2 : ZMod 10890527693) ^ 1329410 = (2 : ZMod 10890527693) ^ (664705 + 664705) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 664705 * (2 : ZMod 10890527693) ^ 664705 := by rw [pow_add]
          _ = 3759535080 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 10890527693) ^ 2658820 = 6129614731 := by
        calc
          (2 : ZMod 10890527693) ^ 2658820 = (2 : ZMod 10890527693) ^ (1329410 + 1329410) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 1329410 * (2 : ZMod 10890527693) ^ 1329410 := by rw [pow_add]
          _ = 6129614731 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 10890527693) ^ 5317640 = 8169860733 := by
        calc
          (2 : ZMod 10890527693) ^ 5317640 = (2 : ZMod 10890527693) ^ (2658820 + 2658820) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 2658820 * (2 : ZMod 10890527693) ^ 2658820 := by rw [pow_add]
          _ = 8169860733 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 10890527693) ^ 10635280 = 7875744471 := by
        calc
          (2 : ZMod 10890527693) ^ 10635280 = (2 : ZMod 10890527693) ^ (5317640 + 5317640) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 5317640 * (2 : ZMod 10890527693) ^ 5317640 := by rw [pow_add]
          _ = 7875744471 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 10890527693) ^ 21270561 = 3415124351 := by
        calc
          (2 : ZMod 10890527693) ^ 21270561 = (2 : ZMod 10890527693) ^ (10635280 + 10635280 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 10635280 * (2 : ZMod 10890527693) ^ 10635280) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 3415124351 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 10890527693) ^ 42541123 = 748325885 := by
        calc
          (2 : ZMod 10890527693) ^ 42541123 = (2 : ZMod 10890527693) ^ (21270561 + 21270561 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 21270561 * (2 : ZMod 10890527693) ^ 21270561) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 748325885 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 10890527693) ^ 85082247 = 9276929439 := by
        calc
          (2 : ZMod 10890527693) ^ 85082247 = (2 : ZMod 10890527693) ^ (42541123 + 42541123 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 42541123 * (2 : ZMod 10890527693) ^ 42541123) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 9276929439 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 10890527693) ^ 170164495 = 3357691900 := by
        calc
          (2 : ZMod 10890527693) ^ 170164495 = (2 : ZMod 10890527693) ^ (85082247 + 85082247 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 85082247 * (2 : ZMod 10890527693) ^ 85082247) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 3357691900 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 10890527693) ^ 340328990 = 7222005206 := by
        calc
          (2 : ZMod 10890527693) ^ 340328990 = (2 : ZMod 10890527693) ^ (170164495 + 170164495) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 170164495 * (2 : ZMod 10890527693) ^ 170164495 := by rw [pow_add]
          _ = 7222005206 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 10890527693) ^ 680657980 = 4923569598 := by
        calc
          (2 : ZMod 10890527693) ^ 680657980 = (2 : ZMod 10890527693) ^ (340328990 + 340328990) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 340328990 * (2 : ZMod 10890527693) ^ 340328990 := by rw [pow_add]
          _ = 4923569598 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 10890527693) ^ 1361315961 = 5327665080 := by
        calc
          (2 : ZMod 10890527693) ^ 1361315961 = (2 : ZMod 10890527693) ^ (680657980 + 680657980 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 680657980 * (2 : ZMod 10890527693) ^ 680657980) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 5327665080 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 10890527693) ^ 2722631923 = 10655330159 := by
        calc
          (2 : ZMod 10890527693) ^ 2722631923 = (2 : ZMod 10890527693) ^ (1361315961 + 1361315961 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 1361315961 * (2 : ZMod 10890527693) ^ 1361315961) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 10655330159 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 10890527693) ^ 5445263846 = 10890527692 := by
        calc
          (2 : ZMod 10890527693) ^ 5445263846 = (2 : ZMod 10890527693) ^ (2722631923 + 2722631923) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 2722631923 * (2 : ZMod 10890527693) ^ 2722631923 := by rw [pow_add]
          _ = 10890527692 := by rw [factor_0_31]; decide
      change (2 : ZMod 10890527693) ^ 5445263846 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (2 : ZMod 10890527693) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 10890527693) ^ 3 = 8 := by
        calc
          (2 : ZMod 10890527693) ^ 3 = (2 : ZMod 10890527693) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 1 * (2 : ZMod 10890527693) ^ 1) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 10890527693) ^ 7 = 128 := by
        calc
          (2 : ZMod 10890527693) ^ 7 = (2 : ZMod 10890527693) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 3 * (2 : ZMod 10890527693) ^ 3) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 10890527693) ^ 14 = 16384 := by
        calc
          (2 : ZMod 10890527693) ^ 14 = (2 : ZMod 10890527693) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 7 * (2 : ZMod 10890527693) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 10890527693) ^ 29 = 536870912 := by
        calc
          (2 : ZMod 10890527693) ^ 29 = (2 : ZMod 10890527693) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 14 * (2 : ZMod 10890527693) ^ 14) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 536870912 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 10890527693) ^ 59 = 7956073430 := by
        calc
          (2 : ZMod 10890527693) ^ 59 = (2 : ZMod 10890527693) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 29 * (2 : ZMod 10890527693) ^ 29) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 7956073430 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 10890527693) ^ 118 = 9272434544 := by
        calc
          (2 : ZMod 10890527693) ^ 118 = (2 : ZMod 10890527693) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 59 * (2 : ZMod 10890527693) ^ 59 := by rw [pow_add]
          _ = 9272434544 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 10890527693) ^ 236 = 2654979445 := by
        calc
          (2 : ZMod 10890527693) ^ 236 = (2 : ZMod 10890527693) ^ (118 + 118) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 118 * (2 : ZMod 10890527693) ^ 118 := by rw [pow_add]
          _ = 2654979445 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 10890527693) ^ 472 = 1241816639 := by
        calc
          (2 : ZMod 10890527693) ^ 472 = (2 : ZMod 10890527693) ^ (236 + 236) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 236 * (2 : ZMod 10890527693) ^ 236 := by rw [pow_add]
          _ = 1241816639 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 10890527693) ^ 944 = 9421949542 := by
        calc
          (2 : ZMod 10890527693) ^ 944 = (2 : ZMod 10890527693) ^ (472 + 472) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 472 * (2 : ZMod 10890527693) ^ 472 := by rw [pow_add]
          _ = 9421949542 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 10890527693) ^ 1888 = 5039810468 := by
        calc
          (2 : ZMod 10890527693) ^ 1888 = (2 : ZMod 10890527693) ^ (944 + 944) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 944 * (2 : ZMod 10890527693) ^ 944 := by rw [pow_add]
          _ = 5039810468 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 10890527693) ^ 3776 = 122291190 := by
        calc
          (2 : ZMod 10890527693) ^ 3776 = (2 : ZMod 10890527693) ^ (1888 + 1888) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 1888 * (2 : ZMod 10890527693) ^ 1888 := by rw [pow_add]
          _ = 122291190 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 10890527693) ^ 7553 = 2301847736 := by
        calc
          (2 : ZMod 10890527693) ^ 7553 = (2 : ZMod 10890527693) ^ (3776 + 3776 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 3776 * (2 : ZMod 10890527693) ^ 3776) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 2301847736 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 10890527693) ^ 15106 = 2433942933 := by
        calc
          (2 : ZMod 10890527693) ^ 15106 = (2 : ZMod 10890527693) ^ (7553 + 7553) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 7553 * (2 : ZMod 10890527693) ^ 7553 := by rw [pow_add]
          _ = 2433942933 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 10890527693) ^ 30213 = 7453736491 := by
        calc
          (2 : ZMod 10890527693) ^ 30213 = (2 : ZMod 10890527693) ^ (15106 + 15106 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 15106 * (2 : ZMod 10890527693) ^ 15106) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 7453736491 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 10890527693) ^ 60427 = 10502987276 := by
        calc
          (2 : ZMod 10890527693) ^ 60427 = (2 : ZMod 10890527693) ^ (30213 + 30213 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 30213 * (2 : ZMod 10890527693) ^ 30213) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 10502987276 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 10890527693) ^ 120855 = 9457045325 := by
        calc
          (2 : ZMod 10890527693) ^ 120855 = (2 : ZMod 10890527693) ^ (60427 + 60427 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 60427 * (2 : ZMod 10890527693) ^ 60427) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 9457045325 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 10890527693) ^ 241710 = 6967818287 := by
        calc
          (2 : ZMod 10890527693) ^ 241710 = (2 : ZMod 10890527693) ^ (120855 + 120855) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 120855 * (2 : ZMod 10890527693) ^ 120855 := by rw [pow_add]
          _ = 6967818287 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 10890527693) ^ 483421 = 6028118109 := by
        calc
          (2 : ZMod 10890527693) ^ 483421 = (2 : ZMod 10890527693) ^ (241710 + 241710 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 241710 * (2 : ZMod 10890527693) ^ 241710) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 6028118109 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 10890527693) ^ 966843 = 815856124 := by
        calc
          (2 : ZMod 10890527693) ^ 966843 = (2 : ZMod 10890527693) ^ (483421 + 483421 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 483421 * (2 : ZMod 10890527693) ^ 483421) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 815856124 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 10890527693) ^ 1933687 = 7304164672 := by
        calc
          (2 : ZMod 10890527693) ^ 1933687 = (2 : ZMod 10890527693) ^ (966843 + 966843 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 966843 * (2 : ZMod 10890527693) ^ 966843) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 7304164672 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 10890527693) ^ 3867374 = 4960698997 := by
        calc
          (2 : ZMod 10890527693) ^ 3867374 = (2 : ZMod 10890527693) ^ (1933687 + 1933687) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 1933687 * (2 : ZMod 10890527693) ^ 1933687 := by rw [pow_add]
          _ = 4960698997 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 10890527693) ^ 7734749 = 5733654110 := by
        calc
          (2 : ZMod 10890527693) ^ 7734749 = (2 : ZMod 10890527693) ^ (3867374 + 3867374 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 3867374 * (2 : ZMod 10890527693) ^ 3867374) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 5733654110 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 10890527693) ^ 15469499 = 3120827121 := by
        calc
          (2 : ZMod 10890527693) ^ 15469499 = (2 : ZMod 10890527693) ^ (7734749 + 7734749 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 7734749 * (2 : ZMod 10890527693) ^ 7734749) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 3120827121 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 10890527693) ^ 30938999 = 9582535020 := by
        calc
          (2 : ZMod 10890527693) ^ 30938999 = (2 : ZMod 10890527693) ^ (15469499 + 15469499 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 15469499 * (2 : ZMod 10890527693) ^ 15469499) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 9582535020 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 10890527693) ^ 61877998 = 9307023942 := by
        calc
          (2 : ZMod 10890527693) ^ 61877998 = (2 : ZMod 10890527693) ^ (30938999 + 30938999) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 30938999 * (2 : ZMod 10890527693) ^ 30938999 := by rw [pow_add]
          _ = 9307023942 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 10890527693) ^ 123755996 = 4239076115 := by
        calc
          (2 : ZMod 10890527693) ^ 123755996 = (2 : ZMod 10890527693) ^ (61877998 + 61877998) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 61877998 * (2 : ZMod 10890527693) ^ 61877998 := by rw [pow_add]
          _ = 4239076115 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 10890527693) ^ 247511993 = 1118506921 := by
        calc
          (2 : ZMod 10890527693) ^ 247511993 = (2 : ZMod 10890527693) ^ (123755996 + 123755996 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 123755996 * (2 : ZMod 10890527693) ^ 123755996) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 1118506921 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 10890527693) ^ 495023986 = 10556784710 := by
        calc
          (2 : ZMod 10890527693) ^ 495023986 = (2 : ZMod 10890527693) ^ (247511993 + 247511993) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 247511993 * (2 : ZMod 10890527693) ^ 247511993 := by rw [pow_add]
          _ = 10556784710 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 10890527693) ^ 990047972 = 3828759155 := by
        calc
          (2 : ZMod 10890527693) ^ 990047972 = (2 : ZMod 10890527693) ^ (495023986 + 495023986) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 495023986 * (2 : ZMod 10890527693) ^ 495023986 := by rw [pow_add]
          _ = 3828759155 := by rw [factor_1_28]; decide
      change (2 : ZMod 10890527693) ^ 990047972 ≠ 1
      rw [factor_1_29]
      decide
    ·
      have factor_2_0 : (2 : ZMod 10890527693) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 10890527693) ^ 2 = 4 := by
        calc
          (2 : ZMod 10890527693) ^ 2 = (2 : ZMod 10890527693) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 1 * (2 : ZMod 10890527693) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 10890527693) ^ 4 = 16 := by
        calc
          (2 : ZMod 10890527693) ^ 4 = (2 : ZMod 10890527693) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 2 * (2 : ZMod 10890527693) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 10890527693) ^ 9 = 512 := by
        calc
          (2 : ZMod 10890527693) ^ 9 = (2 : ZMod 10890527693) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 4 * (2 : ZMod 10890527693) ^ 4) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 10890527693) ^ 19 = 524288 := by
        calc
          (2 : ZMod 10890527693) ^ 19 = (2 : ZMod 10890527693) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 9 * (2 : ZMod 10890527693) ^ 9) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 10890527693) ^ 38 = 2614714619 := by
        calc
          (2 : ZMod 10890527693) ^ 38 = (2 : ZMod 10890527693) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 19 * (2 : ZMod 10890527693) ^ 19 := by rw [pow_add]
          _ = 2614714619 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 10890527693) ^ 76 = 6867901438 := by
        calc
          (2 : ZMod 10890527693) ^ 76 = (2 : ZMod 10890527693) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 38 * (2 : ZMod 10890527693) ^ 38 := by rw [pow_add]
          _ = 6867901438 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 10890527693) ^ 152 = 139962665 := by
        calc
          (2 : ZMod 10890527693) ^ 152 = (2 : ZMod 10890527693) ^ (76 + 76) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 76 * (2 : ZMod 10890527693) ^ 76 := by rw [pow_add]
          _ = 139962665 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 10890527693) ^ 305 = 7972184616 := by
        calc
          (2 : ZMod 10890527693) ^ 305 = (2 : ZMod 10890527693) ^ (152 + 152 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 152 * (2 : ZMod 10890527693) ^ 152) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 7972184616 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 10890527693) ^ 610 = 6050897488 := by
        calc
          (2 : ZMod 10890527693) ^ 610 = (2 : ZMod 10890527693) ^ (305 + 305) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 305 * (2 : ZMod 10890527693) ^ 305 := by rw [pow_add]
          _ = 6050897488 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 10890527693) ^ 1221 = 7071788078 := by
        calc
          (2 : ZMod 10890527693) ^ 1221 = (2 : ZMod 10890527693) ^ (610 + 610 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 610 * (2 : ZMod 10890527693) ^ 610) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 7071788078 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 10890527693) ^ 2443 = 6779900462 := by
        calc
          (2 : ZMod 10890527693) ^ 2443 = (2 : ZMod 10890527693) ^ (1221 + 1221 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 1221 * (2 : ZMod 10890527693) ^ 1221) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 6779900462 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 10890527693) ^ 4887 = 7099751965 := by
        calc
          (2 : ZMod 10890527693) ^ 4887 = (2 : ZMod 10890527693) ^ (2443 + 2443 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 2443 * (2 : ZMod 10890527693) ^ 2443) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 7099751965 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 10890527693) ^ 9775 = 6319787415 := by
        calc
          (2 : ZMod 10890527693) ^ 9775 = (2 : ZMod 10890527693) ^ (4887 + 4887 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 4887 * (2 : ZMod 10890527693) ^ 4887) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 6319787415 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 10890527693) ^ 19550 = 1716838543 := by
        calc
          (2 : ZMod 10890527693) ^ 19550 = (2 : ZMod 10890527693) ^ (9775 + 9775) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 9775 * (2 : ZMod 10890527693) ^ 9775 := by rw [pow_add]
          _ = 1716838543 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 10890527693) ^ 39100 = 8847710468 := by
        calc
          (2 : ZMod 10890527693) ^ 39100 = (2 : ZMod 10890527693) ^ (19550 + 19550) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 19550 * (2 : ZMod 10890527693) ^ 19550 := by rw [pow_add]
          _ = 8847710468 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 10890527693) ^ 78200 = 5070448495 := by
        calc
          (2 : ZMod 10890527693) ^ 78200 = (2 : ZMod 10890527693) ^ (39100 + 39100) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 39100 * (2 : ZMod 10890527693) ^ 39100 := by rw [pow_add]
          _ = 5070448495 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 10890527693) ^ 156401 = 2117898034 := by
        calc
          (2 : ZMod 10890527693) ^ 156401 = (2 : ZMod 10890527693) ^ (78200 + 78200 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 78200 * (2 : ZMod 10890527693) ^ 78200) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 2117898034 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 10890527693) ^ 312802 = 8379625262 := by
        calc
          (2 : ZMod 10890527693) ^ 312802 = (2 : ZMod 10890527693) ^ (156401 + 156401) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 156401 * (2 : ZMod 10890527693) ^ 156401 := by rw [pow_add]
          _ = 8379625262 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 10890527693) ^ 625604 = 9239212347 := by
        calc
          (2 : ZMod 10890527693) ^ 625604 = (2 : ZMod 10890527693) ^ (312802 + 312802) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 312802 * (2 : ZMod 10890527693) ^ 312802 := by rw [pow_add]
          _ = 9239212347 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 10890527693) ^ 1251209 = 3751613349 := by
        calc
          (2 : ZMod 10890527693) ^ 1251209 = (2 : ZMod 10890527693) ^ (625604 + 625604 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 625604 * (2 : ZMod 10890527693) ^ 625604) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 3751613349 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 10890527693) ^ 2502419 = 10586488609 := by
        calc
          (2 : ZMod 10890527693) ^ 2502419 = (2 : ZMod 10890527693) ^ (1251209 + 1251209 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 1251209 * (2 : ZMod 10890527693) ^ 1251209) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 10586488609 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 10890527693) ^ 5004838 = 7174938072 := by
        calc
          (2 : ZMod 10890527693) ^ 5004838 = (2 : ZMod 10890527693) ^ (2502419 + 2502419) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 2502419 * (2 : ZMod 10890527693) ^ 2502419 := by rw [pow_add]
          _ = 7174938072 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 10890527693) ^ 10009676 = 2555171404 := by
        calc
          (2 : ZMod 10890527693) ^ 10009676 = (2 : ZMod 10890527693) ^ (5004838 + 5004838) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 5004838 * (2 : ZMod 10890527693) ^ 5004838 := by rw [pow_add]
          _ = 2555171404 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 10890527693) ^ 20019352 = 5864200107 := by
        calc
          (2 : ZMod 10890527693) ^ 20019352 = (2 : ZMod 10890527693) ^ (10009676 + 10009676) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 10009676 * (2 : ZMod 10890527693) ^ 10009676 := by rw [pow_add]
          _ = 5864200107 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 10890527693) ^ 40038704 = 3520282663 := by
        calc
          (2 : ZMod 10890527693) ^ 40038704 = (2 : ZMod 10890527693) ^ (20019352 + 20019352) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 20019352 * (2 : ZMod 10890527693) ^ 20019352 := by rw [pow_add]
          _ = 3520282663 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 10890527693) ^ 80077409 = 3482004923 := by
        calc
          (2 : ZMod 10890527693) ^ 80077409 = (2 : ZMod 10890527693) ^ (40038704 + 40038704 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 40038704 * (2 : ZMod 10890527693) ^ 40038704) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 3482004923 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 10890527693) ^ 160154819 = 2503835659 := by
        calc
          (2 : ZMod 10890527693) ^ 160154819 = (2 : ZMod 10890527693) ^ (80077409 + 80077409 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 80077409 * (2 : ZMod 10890527693) ^ 80077409) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 2503835659 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 10890527693) ^ 320309638 = 4331570420 := by
        calc
          (2 : ZMod 10890527693) ^ 320309638 = (2 : ZMod 10890527693) ^ (160154819 + 160154819) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 160154819 * (2 : ZMod 10890527693) ^ 160154819 := by rw [pow_add]
          _ = 4331570420 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 10890527693) ^ 640619276 = 5484698792 := by
        calc
          (2 : ZMod 10890527693) ^ 640619276 = (2 : ZMod 10890527693) ^ (320309638 + 320309638) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 320309638 * (2 : ZMod 10890527693) ^ 320309638 := by rw [pow_add]
          _ = 5484698792 := by rw [factor_2_28]; decide
      change (2 : ZMod 10890527693) ^ 640619276 ≠ 1
      rw [factor_2_29]
      decide
    ·
      have factor_3_0 : (2 : ZMod 10890527693) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 10890527693) ^ 2 = 4 := by
        calc
          (2 : ZMod 10890527693) ^ 2 = (2 : ZMod 10890527693) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 1 * (2 : ZMod 10890527693) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 10890527693) ^ 4 = 16 := by
        calc
          (2 : ZMod 10890527693) ^ 4 = (2 : ZMod 10890527693) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 2 * (2 : ZMod 10890527693) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 10890527693) ^ 8 = 256 := by
        calc
          (2 : ZMod 10890527693) ^ 8 = (2 : ZMod 10890527693) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 4 * (2 : ZMod 10890527693) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 10890527693) ^ 17 = 131072 := by
        calc
          (2 : ZMod 10890527693) ^ 17 = (2 : ZMod 10890527693) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 8 * (2 : ZMod 10890527693) ^ 8) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 10890527693) ^ 34 = 6289341491 := by
        calc
          (2 : ZMod 10890527693) ^ 34 = (2 : ZMod 10890527693) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 17 * (2 : ZMod 10890527693) ^ 17 := by rw [pow_add]
          _ = 6289341491 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 10890527693) ^ 68 = 452238978 := by
        calc
          (2 : ZMod 10890527693) ^ 68 = (2 : ZMod 10890527693) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 34 * (2 : ZMod 10890527693) ^ 34 := by rw [pow_add]
          _ = 452238978 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 10890527693) ^ 136 = 1752663201 := by
        calc
          (2 : ZMod 10890527693) ^ 136 = (2 : ZMod 10890527693) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 68 * (2 : ZMod 10890527693) ^ 68 := by rw [pow_add]
          _ = 1752663201 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 10890527693) ^ 273 = 8911273101 := by
        calc
          (2 : ZMod 10890527693) ^ 273 = (2 : ZMod 10890527693) ^ (136 + 136 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 136 * (2 : ZMod 10890527693) ^ 136) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 8911273101 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 10890527693) ^ 546 = 1609272305 := by
        calc
          (2 : ZMod 10890527693) ^ 546 = (2 : ZMod 10890527693) ^ (273 + 273) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 273 * (2 : ZMod 10890527693) ^ 273 := by rw [pow_add]
          _ = 1609272305 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 10890527693) ^ 1093 = 10651790416 := by
        calc
          (2 : ZMod 10890527693) ^ 1093 = (2 : ZMod 10890527693) ^ (546 + 546 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 546 * (2 : ZMod 10890527693) ^ 546) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 10651790416 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 10890527693) ^ 2186 = 8762808466 := by
        calc
          (2 : ZMod 10890527693) ^ 2186 = (2 : ZMod 10890527693) ^ (1093 + 1093) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 1093 * (2 : ZMod 10890527693) ^ 1093 := by rw [pow_add]
          _ = 8762808466 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 10890527693) ^ 4373 = 6466315472 := by
        calc
          (2 : ZMod 10890527693) ^ 4373 = (2 : ZMod 10890527693) ^ (2186 + 2186 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 2186 * (2 : ZMod 10890527693) ^ 2186) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 6466315472 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 10890527693) ^ 8746 = 3956835184 := by
        calc
          (2 : ZMod 10890527693) ^ 8746 = (2 : ZMod 10890527693) ^ (4373 + 4373) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 4373 * (2 : ZMod 10890527693) ^ 4373 := by rw [pow_add]
          _ = 3956835184 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 10890527693) ^ 17492 = 7198576460 := by
        calc
          (2 : ZMod 10890527693) ^ 17492 = (2 : ZMod 10890527693) ^ (8746 + 8746) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 8746 * (2 : ZMod 10890527693) ^ 8746 := by rw [pow_add]
          _ = 7198576460 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 10890527693) ^ 34984 = 3524765410 := by
        calc
          (2 : ZMod 10890527693) ^ 34984 = (2 : ZMod 10890527693) ^ (17492 + 17492) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 17492 * (2 : ZMod 10890527693) ^ 17492 := by rw [pow_add]
          _ = 3524765410 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 10890527693) ^ 69968 = 6306624464 := by
        calc
          (2 : ZMod 10890527693) ^ 69968 = (2 : ZMod 10890527693) ^ (34984 + 34984) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 34984 * (2 : ZMod 10890527693) ^ 34984 := by rw [pow_add]
          _ = 6306624464 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 10890527693) ^ 139937 = 9869780984 := by
        calc
          (2 : ZMod 10890527693) ^ 139937 = (2 : ZMod 10890527693) ^ (69968 + 69968 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 69968 * (2 : ZMod 10890527693) ^ 69968) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 9869780984 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 10890527693) ^ 279875 = 4057934845 := by
        calc
          (2 : ZMod 10890527693) ^ 279875 = (2 : ZMod 10890527693) ^ (139937 + 139937 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 139937 * (2 : ZMod 10890527693) ^ 139937) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 4057934845 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 10890527693) ^ 559751 = 10690078004 := by
        calc
          (2 : ZMod 10890527693) ^ 559751 = (2 : ZMod 10890527693) ^ (279875 + 279875 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 279875 * (2 : ZMod 10890527693) ^ 279875) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 10690078004 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 10890527693) ^ 1119503 = 8174932663 := by
        calc
          (2 : ZMod 10890527693) ^ 1119503 = (2 : ZMod 10890527693) ^ (559751 + 559751 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 559751 * (2 : ZMod 10890527693) ^ 559751) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 8174932663 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 10890527693) ^ 2239006 = 679165767 := by
        calc
          (2 : ZMod 10890527693) ^ 2239006 = (2 : ZMod 10890527693) ^ (1119503 + 1119503) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 1119503 * (2 : ZMod 10890527693) ^ 1119503 := by rw [pow_add]
          _ = 679165767 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 10890527693) ^ 4478013 = 794860699 := by
        calc
          (2 : ZMod 10890527693) ^ 4478013 = (2 : ZMod 10890527693) ^ (2239006 + 2239006 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 2239006 * (2 : ZMod 10890527693) ^ 2239006) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 794860699 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 10890527693) ^ 8956026 = 10721431188 := by
        calc
          (2 : ZMod 10890527693) ^ 8956026 = (2 : ZMod 10890527693) ^ (4478013 + 4478013) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 4478013 * (2 : ZMod 10890527693) ^ 4478013 := by rw [pow_add]
          _ = 10721431188 := by rw [factor_3_22]; decide
      have factor_3_24 : (2 : ZMod 10890527693) ^ 17912052 = 3018858875 := by
        calc
          (2 : ZMod 10890527693) ^ 17912052 = (2 : ZMod 10890527693) ^ (8956026 + 8956026) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 8956026 * (2 : ZMod 10890527693) ^ 8956026 := by rw [pow_add]
          _ = 3018858875 := by rw [factor_3_23]; decide
      have factor_3_25 : (2 : ZMod 10890527693) ^ 35824104 = 9325042503 := by
        calc
          (2 : ZMod 10890527693) ^ 35824104 = (2 : ZMod 10890527693) ^ (17912052 + 17912052) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 17912052 * (2 : ZMod 10890527693) ^ 17912052 := by rw [pow_add]
          _ = 9325042503 := by rw [factor_3_24]; decide
      have factor_3_26 : (2 : ZMod 10890527693) ^ 71648208 = 3176895329 := by
        calc
          (2 : ZMod 10890527693) ^ 71648208 = (2 : ZMod 10890527693) ^ (35824104 + 35824104) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 35824104 * (2 : ZMod 10890527693) ^ 35824104 := by rw [pow_add]
          _ = 3176895329 := by rw [factor_3_25]; decide
      have factor_3_27 : (2 : ZMod 10890527693) ^ 143296417 = 889444111 := by
        calc
          (2 : ZMod 10890527693) ^ 143296417 = (2 : ZMod 10890527693) ^ (71648208 + 71648208 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 71648208 * (2 : ZMod 10890527693) ^ 71648208) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 889444111 := by rw [factor_3_26]; decide
      have factor_3_28 : (2 : ZMod 10890527693) ^ 286592834 = 3083849635 := by
        calc
          (2 : ZMod 10890527693) ^ 286592834 = (2 : ZMod 10890527693) ^ (143296417 + 143296417) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 143296417 * (2 : ZMod 10890527693) ^ 143296417 := by rw [pow_add]
          _ = 3083849635 := by rw [factor_3_27]; decide
      have factor_3_29 : (2 : ZMod 10890527693) ^ 573185668 = 6656301721 := by
        calc
          (2 : ZMod 10890527693) ^ 573185668 = (2 : ZMod 10890527693) ^ (286592834 + 286592834) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 286592834 * (2 : ZMod 10890527693) ^ 286592834 := by rw [pow_add]
          _ = 6656301721 := by rw [factor_3_28]; decide
      change (2 : ZMod 10890527693) ^ 573185668 ≠ 1
      rw [factor_3_29]
      decide
    ·
      have factor_4_0 : (2 : ZMod 10890527693) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 10890527693) ^ 3 = 8 := by
        calc
          (2 : ZMod 10890527693) ^ 3 = (2 : ZMod 10890527693) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 1 * (2 : ZMod 10890527693) ^ 1) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 10890527693) ^ 7 = 128 := by
        calc
          (2 : ZMod 10890527693) ^ 7 = (2 : ZMod 10890527693) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 3 * (2 : ZMod 10890527693) ^ 3) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 10890527693) ^ 14 = 16384 := by
        calc
          (2 : ZMod 10890527693) ^ 14 = (2 : ZMod 10890527693) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 7 * (2 : ZMod 10890527693) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 10890527693) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 10890527693) ^ 28 = (2 : ZMod 10890527693) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 14 * (2 : ZMod 10890527693) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 10890527693) ^ 56 = 3717141102 := by
        calc
          (2 : ZMod 10890527693) ^ 56 = (2 : ZMod 10890527693) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 28 * (2 : ZMod 10890527693) ^ 28 := by rw [pow_add]
          _ = 3717141102 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 10890527693) ^ 112 = 2867513713 := by
        calc
          (2 : ZMod 10890527693) ^ 112 = (2 : ZMod 10890527693) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 56 * (2 : ZMod 10890527693) ^ 56 := by rw [pow_add]
          _ = 2867513713 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 10890527693) ^ 225 = 10503636315 := by
        calc
          (2 : ZMod 10890527693) ^ 225 = (2 : ZMod 10890527693) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 112 * (2 : ZMod 10890527693) ^ 112) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 10503636315 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 10890527693) ^ 451 = 8521213066 := by
        calc
          (2 : ZMod 10890527693) ^ 451 = (2 : ZMod 10890527693) ^ (225 + 225 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 225 * (2 : ZMod 10890527693) ^ 225) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 8521213066 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 10890527693) ^ 903 = 9138527973 := by
        calc
          (2 : ZMod 10890527693) ^ 903 = (2 : ZMod 10890527693) ^ (451 + 451 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 451 * (2 : ZMod 10890527693) ^ 451) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 9138527973 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 10890527693) ^ 1806 = 1880727905 := by
        calc
          (2 : ZMod 10890527693) ^ 1806 = (2 : ZMod 10890527693) ^ (903 + 903) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 903 * (2 : ZMod 10890527693) ^ 903 := by rw [pow_add]
          _ = 1880727905 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 10890527693) ^ 3612 = 1012686529 := by
        calc
          (2 : ZMod 10890527693) ^ 3612 = (2 : ZMod 10890527693) ^ (1806 + 1806) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 1806 * (2 : ZMod 10890527693) ^ 1806 := by rw [pow_add]
          _ = 1012686529 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 10890527693) ^ 7225 = 10682289883 := by
        calc
          (2 : ZMod 10890527693) ^ 7225 = (2 : ZMod 10890527693) ^ (3612 + 3612 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 3612 * (2 : ZMod 10890527693) ^ 3612) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 10682289883 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 10890527693) ^ 14450 = 8040462605 := by
        calc
          (2 : ZMod 10890527693) ^ 14450 = (2 : ZMod 10890527693) ^ (7225 + 7225) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 7225 * (2 : ZMod 10890527693) ^ 7225 := by rw [pow_add]
          _ = 8040462605 := by rw [factor_4_12]; decide
      have factor_4_14 : (2 : ZMod 10890527693) ^ 28900 = 10070783802 := by
        calc
          (2 : ZMod 10890527693) ^ 28900 = (2 : ZMod 10890527693) ^ (14450 + 14450) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 14450 * (2 : ZMod 10890527693) ^ 14450 := by rw [pow_add]
          _ = 10070783802 := by rw [factor_4_13]; decide
      have factor_4_15 : (2 : ZMod 10890527693) ^ 57800 = 8763043843 := by
        calc
          (2 : ZMod 10890527693) ^ 57800 = (2 : ZMod 10890527693) ^ (28900 + 28900) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 28900 * (2 : ZMod 10890527693) ^ 28900 := by rw [pow_add]
          _ = 8763043843 := by rw [factor_4_14]; decide
      have factor_4_16 : (2 : ZMod 10890527693) ^ 115600 = 6349372531 := by
        calc
          (2 : ZMod 10890527693) ^ 115600 = (2 : ZMod 10890527693) ^ (57800 + 57800) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 57800 * (2 : ZMod 10890527693) ^ 57800 := by rw [pow_add]
          _ = 6349372531 := by rw [factor_4_15]; decide
      have factor_4_17 : (2 : ZMod 10890527693) ^ 231201 = 1903825727 := by
        calc
          (2 : ZMod 10890527693) ^ 231201 = (2 : ZMod 10890527693) ^ (115600 + 115600 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 115600 * (2 : ZMod 10890527693) ^ 115600) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 1903825727 := by rw [factor_4_16]; decide
      have factor_4_18 : (2 : ZMod 10890527693) ^ 462403 = 5946622796 := by
        calc
          (2 : ZMod 10890527693) ^ 462403 = (2 : ZMod 10890527693) ^ (231201 + 231201 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 231201 * (2 : ZMod 10890527693) ^ 231201) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 5946622796 := by rw [factor_4_17]; decide
      have factor_4_19 : (2 : ZMod 10890527693) ^ 924807 = 6725153081 := by
        calc
          (2 : ZMod 10890527693) ^ 924807 = (2 : ZMod 10890527693) ^ (462403 + 462403 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 462403 * (2 : ZMod 10890527693) ^ 462403) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 6725153081 := by rw [factor_4_18]; decide
      have factor_4_20 : (2 : ZMod 10890527693) ^ 1849614 = 8035212556 := by
        calc
          (2 : ZMod 10890527693) ^ 1849614 = (2 : ZMod 10890527693) ^ (924807 + 924807) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 924807 * (2 : ZMod 10890527693) ^ 924807 := by rw [pow_add]
          _ = 8035212556 := by rw [factor_4_19]; decide
      have factor_4_21 : (2 : ZMod 10890527693) ^ 3699228 = 10638283767 := by
        calc
          (2 : ZMod 10890527693) ^ 3699228 = (2 : ZMod 10890527693) ^ (1849614 + 1849614) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 1849614 * (2 : ZMod 10890527693) ^ 1849614 := by rw [pow_add]
          _ = 10638283767 := by rw [factor_4_20]; decide
      have factor_4_22 : (2 : ZMod 10890527693) ^ 7398456 = 4961867188 := by
        calc
          (2 : ZMod 10890527693) ^ 7398456 = (2 : ZMod 10890527693) ^ (3699228 + 3699228) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 3699228 * (2 : ZMod 10890527693) ^ 3699228 := by rw [pow_add]
          _ = 4961867188 := by rw [factor_4_21]; decide
      have factor_4_23 : (2 : ZMod 10890527693) ^ 14796912 = 2435199217 := by
        calc
          (2 : ZMod 10890527693) ^ 14796912 = (2 : ZMod 10890527693) ^ (7398456 + 7398456) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 7398456 * (2 : ZMod 10890527693) ^ 7398456 := by rw [pow_add]
          _ = 2435199217 := by rw [factor_4_22]; decide
      have factor_4_24 : (2 : ZMod 10890527693) ^ 29593825 = 9674903053 := by
        calc
          (2 : ZMod 10890527693) ^ 29593825 = (2 : ZMod 10890527693) ^ (14796912 + 14796912 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 14796912 * (2 : ZMod 10890527693) ^ 14796912) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 9674903053 := by rw [factor_4_23]; decide
      have factor_4_25 : (2 : ZMod 10890527693) ^ 59187650 = 4685740658 := by
        calc
          (2 : ZMod 10890527693) ^ 59187650 = (2 : ZMod 10890527693) ^ (29593825 + 29593825) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 29593825 * (2 : ZMod 10890527693) ^ 29593825 := by rw [pow_add]
          _ = 4685740658 := by rw [factor_4_24]; decide
      have factor_4_26 : (2 : ZMod 10890527693) ^ 118375301 = 9228294836 := by
        calc
          (2 : ZMod 10890527693) ^ 118375301 = (2 : ZMod 10890527693) ^ (59187650 + 59187650 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 59187650 * (2 : ZMod 10890527693) ^ 59187650) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 9228294836 := by rw [factor_4_25]; decide
      have factor_4_27 : (2 : ZMod 10890527693) ^ 236750602 = 8787908960 := by
        calc
          (2 : ZMod 10890527693) ^ 236750602 = (2 : ZMod 10890527693) ^ (118375301 + 118375301) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 118375301 * (2 : ZMod 10890527693) ^ 118375301 := by rw [pow_add]
          _ = 8787908960 := by rw [factor_4_26]; decide
      have factor_4_28 : (2 : ZMod 10890527693) ^ 473501204 = 1351809401 := by
        calc
          (2 : ZMod 10890527693) ^ 473501204 = (2 : ZMod 10890527693) ^ (236750602 + 236750602) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 236750602 * (2 : ZMod 10890527693) ^ 236750602 := by rw [pow_add]
          _ = 1351809401 := by rw [factor_4_27]; decide
      change (2 : ZMod 10890527693) ^ 473501204 ≠ 1
      rw [factor_4_28]
      decide
    ·
      have factor_5_0 : (2 : ZMod 10890527693) ^ 1 = 2 := by norm_num
      have factor_5_1 : (2 : ZMod 10890527693) ^ 2 = 4 := by
        calc
          (2 : ZMod 10890527693) ^ 2 = (2 : ZMod 10890527693) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 1 * (2 : ZMod 10890527693) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_5_0]; decide
      have factor_5_2 : (2 : ZMod 10890527693) ^ 4 = 16 := by
        calc
          (2 : ZMod 10890527693) ^ 4 = (2 : ZMod 10890527693) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 2 * (2 : ZMod 10890527693) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_5_1]; decide
      have factor_5_3 : (2 : ZMod 10890527693) ^ 9 = 512 := by
        calc
          (2 : ZMod 10890527693) ^ 9 = (2 : ZMod 10890527693) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 4 * (2 : ZMod 10890527693) ^ 4) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_5_2]; decide
      have factor_5_4 : (2 : ZMod 10890527693) ^ 19 = 524288 := by
        calc
          (2 : ZMod 10890527693) ^ 19 = (2 : ZMod 10890527693) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 9 * (2 : ZMod 10890527693) ^ 9) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_5_3]; decide
      have factor_5_5 : (2 : ZMod 10890527693) ^ 39 = 5229429238 := by
        calc
          (2 : ZMod 10890527693) ^ 39 = (2 : ZMod 10890527693) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 19 * (2 : ZMod 10890527693) ^ 19) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 5229429238 := by rw [factor_5_4]; decide
      have factor_5_6 : (2 : ZMod 10890527693) ^ 79 = 490573039 := by
        calc
          (2 : ZMod 10890527693) ^ 79 = (2 : ZMod 10890527693) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 39 * (2 : ZMod 10890527693) ^ 39) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 490573039 := by rw [factor_5_5]; decide
      have factor_5_7 : (2 : ZMod 10890527693) ^ 159 = 7024693427 := by
        calc
          (2 : ZMod 10890527693) ^ 159 = (2 : ZMod 10890527693) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 79 * (2 : ZMod 10890527693) ^ 79) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 7024693427 := by rw [factor_5_6]; decide
      have factor_5_8 : (2 : ZMod 10890527693) ^ 319 = 6174126395 := by
        calc
          (2 : ZMod 10890527693) ^ 319 = (2 : ZMod 10890527693) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 159 * (2 : ZMod 10890527693) ^ 159) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 6174126395 := by rw [factor_5_7]; decide
      have factor_5_9 : (2 : ZMod 10890527693) ^ 638 = 6696553656 := by
        calc
          (2 : ZMod 10890527693) ^ 638 = (2 : ZMod 10890527693) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 319 * (2 : ZMod 10890527693) ^ 319 := by rw [pow_add]
          _ = 6696553656 := by rw [factor_5_8]; decide
      have factor_5_10 : (2 : ZMod 10890527693) ^ 1276 = 6074987761 := by
        calc
          (2 : ZMod 10890527693) ^ 1276 = (2 : ZMod 10890527693) ^ (638 + 638) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 638 * (2 : ZMod 10890527693) ^ 638 := by rw [pow_add]
          _ = 6074987761 := by rw [factor_5_9]; decide
      have factor_5_11 : (2 : ZMod 10890527693) ^ 2553 = 704514587 := by
        calc
          (2 : ZMod 10890527693) ^ 2553 = (2 : ZMod 10890527693) ^ (1276 + 1276 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 1276 * (2 : ZMod 10890527693) ^ 1276) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 704514587 := by rw [factor_5_10]; decide
      have factor_5_12 : (2 : ZMod 10890527693) ^ 5107 = 9870188964 := by
        calc
          (2 : ZMod 10890527693) ^ 5107 = (2 : ZMod 10890527693) ^ (2553 + 2553 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 2553 * (2 : ZMod 10890527693) ^ 2553) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 9870188964 := by rw [factor_5_11]; decide
      have factor_5_13 : (2 : ZMod 10890527693) ^ 10214 = 7856225888 := by
        calc
          (2 : ZMod 10890527693) ^ 10214 = (2 : ZMod 10890527693) ^ (5107 + 5107) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 5107 * (2 : ZMod 10890527693) ^ 5107 := by rw [pow_add]
          _ = 7856225888 := by rw [factor_5_12]; decide
      have factor_5_14 : (2 : ZMod 10890527693) ^ 20429 = 2043361921 := by
        calc
          (2 : ZMod 10890527693) ^ 20429 = (2 : ZMod 10890527693) ^ (10214 + 10214 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 10214 * (2 : ZMod 10890527693) ^ 10214) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 2043361921 := by rw [factor_5_13]; decide
      have factor_5_15 : (2 : ZMod 10890527693) ^ 40859 = 1380713244 := by
        calc
          (2 : ZMod 10890527693) ^ 40859 = (2 : ZMod 10890527693) ^ (20429 + 20429 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 20429 * (2 : ZMod 10890527693) ^ 20429) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 1380713244 := by rw [factor_5_14]; decide
      have factor_5_16 : (2 : ZMod 10890527693) ^ 81719 = 1910790875 := by
        calc
          (2 : ZMod 10890527693) ^ 81719 = (2 : ZMod 10890527693) ^ (40859 + 40859 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = ((2 : ZMod 10890527693) ^ 40859 * (2 : ZMod 10890527693) ^ 40859) * (2 : ZMod 10890527693) := by rw [pow_succ, pow_add]
          _ = 1910790875 := by rw [factor_5_15]; decide
      have factor_5_17 : (2 : ZMod 10890527693) ^ 163438 = 2239023333 := by
        calc
          (2 : ZMod 10890527693) ^ 163438 = (2 : ZMod 10890527693) ^ (81719 + 81719) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 81719 * (2 : ZMod 10890527693) ^ 81719 := by rw [pow_add]
          _ = 2239023333 := by rw [factor_5_16]; decide
      have factor_5_18 : (2 : ZMod 10890527693) ^ 326876 = 2919041135 := by
        calc
          (2 : ZMod 10890527693) ^ 326876 = (2 : ZMod 10890527693) ^ (163438 + 163438) :=
            congrArg (fun n : ℕ => (2 : ZMod 10890527693) ^ n) (by norm_num)
          _ = (2 : ZMod 10890527693) ^ 163438 * (2 : ZMod 10890527693) ^ 163438 := by rw [pow_add]
          _ = 2919041135 := by rw [factor_5_17]; decide
      change (2 : ZMod 10890527693) ^ 326876 ≠ 1
      rw [factor_5_18]
      decide

#print axioms prime_lucas_10890527693

end TotientTailPeriodKiller
end Erdos249257
