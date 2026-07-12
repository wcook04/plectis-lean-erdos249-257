import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_59567237 : Nat.Prime 59567237 := by
  apply lucas_primality 59567237 (2 : ZMod 59567237)
  ·
      have fermat_0 : (2 : ZMod 59567237) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 59567237) ^ 3 = 8 := by
        calc
          (2 : ZMod 59567237) ^ 3 = (2 : ZMod 59567237) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 1 * (2 : ZMod 59567237) ^ 1) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 59567237) ^ 7 = 128 := by
        calc
          (2 : ZMod 59567237) ^ 7 = (2 : ZMod 59567237) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 3 * (2 : ZMod 59567237) ^ 3) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 59567237) ^ 14 = 16384 := by
        calc
          (2 : ZMod 59567237) ^ 14 = (2 : ZMod 59567237) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 7 * (2 : ZMod 59567237) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 59567237) ^ 28 = 30166508 := by
        calc
          (2 : ZMod 59567237) ^ 28 = (2 : ZMod 59567237) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 14 * (2 : ZMod 59567237) ^ 14 := by rw [pow_add]
          _ = 30166508 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 59567237) ^ 56 = 54074381 := by
        calc
          (2 : ZMod 59567237) ^ 56 = (2 : ZMod 59567237) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 28 * (2 : ZMod 59567237) ^ 28 := by rw [pow_add]
          _ = 54074381 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 59567237) ^ 113 = 12513258 := by
        calc
          (2 : ZMod 59567237) ^ 113 = (2 : ZMod 59567237) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 56 * (2 : ZMod 59567237) ^ 56) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 12513258 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 59567237) ^ 227 = 59065606 := by
        calc
          (2 : ZMod 59567237) ^ 227 = (2 : ZMod 59567237) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 113 * (2 : ZMod 59567237) ^ 113) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 59065606 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 59567237) ^ 454 = 21651073 := by
        calc
          (2 : ZMod 59567237) ^ 454 = (2 : ZMod 59567237) ^ (227 + 227) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 227 * (2 : ZMod 59567237) ^ 227 := by rw [pow_add]
          _ = 21651073 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 59567237) ^ 908 = 3802580 := by
        calc
          (2 : ZMod 59567237) ^ 908 = (2 : ZMod 59567237) ^ (454 + 454) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 454 * (2 : ZMod 59567237) ^ 454 := by rw [pow_add]
          _ = 3802580 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 59567237) ^ 1817 = 50556144 := by
        calc
          (2 : ZMod 59567237) ^ 1817 = (2 : ZMod 59567237) ^ (908 + 908 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 908 * (2 : ZMod 59567237) ^ 908) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 50556144 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 59567237) ^ 3635 = 6262510 := by
        calc
          (2 : ZMod 59567237) ^ 3635 = (2 : ZMod 59567237) ^ (1817 + 1817 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 1817 * (2 : ZMod 59567237) ^ 1817) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 6262510 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 59567237) ^ 7271 = 44453074 := by
        calc
          (2 : ZMod 59567237) ^ 7271 = (2 : ZMod 59567237) ^ (3635 + 3635 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 3635 * (2 : ZMod 59567237) ^ 3635) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 44453074 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 59567237) ^ 14542 = 11552286 := by
        calc
          (2 : ZMod 59567237) ^ 14542 = (2 : ZMod 59567237) ^ (7271 + 7271) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 7271 * (2 : ZMod 59567237) ^ 7271 := by rw [pow_add]
          _ = 11552286 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 59567237) ^ 29085 = 20652119 := by
        calc
          (2 : ZMod 59567237) ^ 29085 = (2 : ZMod 59567237) ^ (14542 + 14542 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 14542 * (2 : ZMod 59567237) ^ 14542) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 20652119 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 59567237) ^ 58171 = 49176066 := by
        calc
          (2 : ZMod 59567237) ^ 58171 = (2 : ZMod 59567237) ^ (29085 + 29085 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 29085 * (2 : ZMod 59567237) ^ 29085) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 49176066 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 59567237) ^ 116342 = 36018844 := by
        calc
          (2 : ZMod 59567237) ^ 116342 = (2 : ZMod 59567237) ^ (58171 + 58171) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 58171 * (2 : ZMod 59567237) ^ 58171 := by rw [pow_add]
          _ = 36018844 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 59567237) ^ 232684 = 35302303 := by
        calc
          (2 : ZMod 59567237) ^ 232684 = (2 : ZMod 59567237) ^ (116342 + 116342) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 116342 * (2 : ZMod 59567237) ^ 116342 := by rw [pow_add]
          _ = 35302303 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 59567237) ^ 465369 = 57898372 := by
        calc
          (2 : ZMod 59567237) ^ 465369 = (2 : ZMod 59567237) ^ (232684 + 232684 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 232684 * (2 : ZMod 59567237) ^ 232684) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 57898372 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 59567237) ^ 930738 = 44222290 := by
        calc
          (2 : ZMod 59567237) ^ 930738 = (2 : ZMod 59567237) ^ (465369 + 465369) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 465369 * (2 : ZMod 59567237) ^ 465369 := by rw [pow_add]
          _ = 44222290 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 59567237) ^ 1861476 = 16723393 := by
        calc
          (2 : ZMod 59567237) ^ 1861476 = (2 : ZMod 59567237) ^ (930738 + 930738) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 930738 * (2 : ZMod 59567237) ^ 930738 := by rw [pow_add]
          _ = 16723393 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 59567237) ^ 3722952 = 2548755 := by
        calc
          (2 : ZMod 59567237) ^ 3722952 = (2 : ZMod 59567237) ^ (1861476 + 1861476) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 1861476 * (2 : ZMod 59567237) ^ 1861476 := by rw [pow_add]
          _ = 2548755 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 59567237) ^ 7445904 = 47018990 := by
        calc
          (2 : ZMod 59567237) ^ 7445904 = (2 : ZMod 59567237) ^ (3722952 + 3722952) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 3722952 * (2 : ZMod 59567237) ^ 3722952 := by rw [pow_add]
          _ = 47018990 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 59567237) ^ 14891809 = 34470742 := by
        calc
          (2 : ZMod 59567237) ^ 14891809 = (2 : ZMod 59567237) ^ (7445904 + 7445904 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 7445904 * (2 : ZMod 59567237) ^ 7445904) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 34470742 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 59567237) ^ 29783618 = 59567236 := by
        calc
          (2 : ZMod 59567237) ^ 29783618 = (2 : ZMod 59567237) ^ (14891809 + 14891809) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 14891809 * (2 : ZMod 59567237) ^ 14891809 := by rw [pow_add]
          _ = 59567236 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 59567237) ^ 59567236 = 1 := by
        calc
          (2 : ZMod 59567237) ^ 59567236 = (2 : ZMod 59567237) ^ (29783618 + 29783618) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 29783618 * (2 : ZMod 59567237) ^ 29783618 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (47, 1), (316847, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (47, 1), (316847, 1)] : List FactorBlock).map factorBlockValue).prod = 59567237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 59567237) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 59567237) ^ 3 = 8 := by
        calc
          (2 : ZMod 59567237) ^ 3 = (2 : ZMod 59567237) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 1 * (2 : ZMod 59567237) ^ 1) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 59567237) ^ 7 = 128 := by
        calc
          (2 : ZMod 59567237) ^ 7 = (2 : ZMod 59567237) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 3 * (2 : ZMod 59567237) ^ 3) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 59567237) ^ 14 = 16384 := by
        calc
          (2 : ZMod 59567237) ^ 14 = (2 : ZMod 59567237) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 7 * (2 : ZMod 59567237) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 59567237) ^ 28 = 30166508 := by
        calc
          (2 : ZMod 59567237) ^ 28 = (2 : ZMod 59567237) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 14 * (2 : ZMod 59567237) ^ 14 := by rw [pow_add]
          _ = 30166508 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 59567237) ^ 56 = 54074381 := by
        calc
          (2 : ZMod 59567237) ^ 56 = (2 : ZMod 59567237) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 28 * (2 : ZMod 59567237) ^ 28 := by rw [pow_add]
          _ = 54074381 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 59567237) ^ 113 = 12513258 := by
        calc
          (2 : ZMod 59567237) ^ 113 = (2 : ZMod 59567237) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 56 * (2 : ZMod 59567237) ^ 56) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 12513258 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 59567237) ^ 227 = 59065606 := by
        calc
          (2 : ZMod 59567237) ^ 227 = (2 : ZMod 59567237) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 113 * (2 : ZMod 59567237) ^ 113) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 59065606 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 59567237) ^ 454 = 21651073 := by
        calc
          (2 : ZMod 59567237) ^ 454 = (2 : ZMod 59567237) ^ (227 + 227) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 227 * (2 : ZMod 59567237) ^ 227 := by rw [pow_add]
          _ = 21651073 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 59567237) ^ 908 = 3802580 := by
        calc
          (2 : ZMod 59567237) ^ 908 = (2 : ZMod 59567237) ^ (454 + 454) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 454 * (2 : ZMod 59567237) ^ 454 := by rw [pow_add]
          _ = 3802580 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 59567237) ^ 1817 = 50556144 := by
        calc
          (2 : ZMod 59567237) ^ 1817 = (2 : ZMod 59567237) ^ (908 + 908 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 908 * (2 : ZMod 59567237) ^ 908) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 50556144 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 59567237) ^ 3635 = 6262510 := by
        calc
          (2 : ZMod 59567237) ^ 3635 = (2 : ZMod 59567237) ^ (1817 + 1817 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 1817 * (2 : ZMod 59567237) ^ 1817) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 6262510 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 59567237) ^ 7271 = 44453074 := by
        calc
          (2 : ZMod 59567237) ^ 7271 = (2 : ZMod 59567237) ^ (3635 + 3635 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 3635 * (2 : ZMod 59567237) ^ 3635) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 44453074 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 59567237) ^ 14542 = 11552286 := by
        calc
          (2 : ZMod 59567237) ^ 14542 = (2 : ZMod 59567237) ^ (7271 + 7271) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 7271 * (2 : ZMod 59567237) ^ 7271 := by rw [pow_add]
          _ = 11552286 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 59567237) ^ 29085 = 20652119 := by
        calc
          (2 : ZMod 59567237) ^ 29085 = (2 : ZMod 59567237) ^ (14542 + 14542 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 14542 * (2 : ZMod 59567237) ^ 14542) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 20652119 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 59567237) ^ 58171 = 49176066 := by
        calc
          (2 : ZMod 59567237) ^ 58171 = (2 : ZMod 59567237) ^ (29085 + 29085 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 29085 * (2 : ZMod 59567237) ^ 29085) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 49176066 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 59567237) ^ 116342 = 36018844 := by
        calc
          (2 : ZMod 59567237) ^ 116342 = (2 : ZMod 59567237) ^ (58171 + 58171) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 58171 * (2 : ZMod 59567237) ^ 58171 := by rw [pow_add]
          _ = 36018844 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 59567237) ^ 232684 = 35302303 := by
        calc
          (2 : ZMod 59567237) ^ 232684 = (2 : ZMod 59567237) ^ (116342 + 116342) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 116342 * (2 : ZMod 59567237) ^ 116342 := by rw [pow_add]
          _ = 35302303 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 59567237) ^ 465369 = 57898372 := by
        calc
          (2 : ZMod 59567237) ^ 465369 = (2 : ZMod 59567237) ^ (232684 + 232684 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 232684 * (2 : ZMod 59567237) ^ 232684) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 57898372 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 59567237) ^ 930738 = 44222290 := by
        calc
          (2 : ZMod 59567237) ^ 930738 = (2 : ZMod 59567237) ^ (465369 + 465369) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 465369 * (2 : ZMod 59567237) ^ 465369 := by rw [pow_add]
          _ = 44222290 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 59567237) ^ 1861476 = 16723393 := by
        calc
          (2 : ZMod 59567237) ^ 1861476 = (2 : ZMod 59567237) ^ (930738 + 930738) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 930738 * (2 : ZMod 59567237) ^ 930738 := by rw [pow_add]
          _ = 16723393 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 59567237) ^ 3722952 = 2548755 := by
        calc
          (2 : ZMod 59567237) ^ 3722952 = (2 : ZMod 59567237) ^ (1861476 + 1861476) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 1861476 * (2 : ZMod 59567237) ^ 1861476 := by rw [pow_add]
          _ = 2548755 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 59567237) ^ 7445904 = 47018990 := by
        calc
          (2 : ZMod 59567237) ^ 7445904 = (2 : ZMod 59567237) ^ (3722952 + 3722952) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 3722952 * (2 : ZMod 59567237) ^ 3722952 := by rw [pow_add]
          _ = 47018990 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 59567237) ^ 14891809 = 34470742 := by
        calc
          (2 : ZMod 59567237) ^ 14891809 = (2 : ZMod 59567237) ^ (7445904 + 7445904 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 7445904 * (2 : ZMod 59567237) ^ 7445904) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 34470742 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 59567237) ^ 29783618 = 59567236 := by
        calc
          (2 : ZMod 59567237) ^ 29783618 = (2 : ZMod 59567237) ^ (14891809 + 14891809) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 14891809 * (2 : ZMod 59567237) ^ 14891809 := by rw [pow_add]
          _ = 59567236 := by rw [factor_0_23]; decide
      change (2 : ZMod 59567237) ^ 29783618 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (2 : ZMod 59567237) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 59567237) ^ 2 = 4 := by
        calc
          (2 : ZMod 59567237) ^ 2 = (2 : ZMod 59567237) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 1 * (2 : ZMod 59567237) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 59567237) ^ 4 = 16 := by
        calc
          (2 : ZMod 59567237) ^ 4 = (2 : ZMod 59567237) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 2 * (2 : ZMod 59567237) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 59567237) ^ 9 = 512 := by
        calc
          (2 : ZMod 59567237) ^ 9 = (2 : ZMod 59567237) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 4 * (2 : ZMod 59567237) ^ 4) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 59567237) ^ 19 = 524288 := by
        calc
          (2 : ZMod 59567237) ^ 19 = (2 : ZMod 59567237) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 9 * (2 : ZMod 59567237) ^ 9) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 59567237) ^ 38 = 34675426 := by
        calc
          (2 : ZMod 59567237) ^ 38 = (2 : ZMod 59567237) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 19 * (2 : ZMod 59567237) ^ 19 := by rw [pow_add]
          _ = 34675426 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 59567237) ^ 77 = 56181133 := by
        calc
          (2 : ZMod 59567237) ^ 77 = (2 : ZMod 59567237) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 38 * (2 : ZMod 59567237) ^ 38) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 56181133 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 59567237) ^ 154 = 19819345 := by
        calc
          (2 : ZMod 59567237) ^ 154 = (2 : ZMod 59567237) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 77 * (2 : ZMod 59567237) ^ 77 := by rw [pow_add]
          _ = 19819345 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 59567237) ^ 309 = 2584312 := by
        calc
          (2 : ZMod 59567237) ^ 309 = (2 : ZMod 59567237) ^ (154 + 154 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 154 * (2 : ZMod 59567237) ^ 154) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 2584312 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 59567237) ^ 618 = 49468141 := by
        calc
          (2 : ZMod 59567237) ^ 618 = (2 : ZMod 59567237) ^ (309 + 309) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 309 * (2 : ZMod 59567237) ^ 309 := by rw [pow_add]
          _ = 49468141 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 59567237) ^ 1237 = 4037944 := by
        calc
          (2 : ZMod 59567237) ^ 1237 = (2 : ZMod 59567237) ^ (618 + 618 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 618 * (2 : ZMod 59567237) ^ 618) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 4037944 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 59567237) ^ 2475 = 18733096 := by
        calc
          (2 : ZMod 59567237) ^ 2475 = (2 : ZMod 59567237) ^ (1237 + 1237 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 1237 * (2 : ZMod 59567237) ^ 1237) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 18733096 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 59567237) ^ 4950 = 5436457 := by
        calc
          (2 : ZMod 59567237) ^ 4950 = (2 : ZMod 59567237) ^ (2475 + 2475) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 2475 * (2 : ZMod 59567237) ^ 2475 := by rw [pow_add]
          _ = 5436457 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 59567237) ^ 9901 = 11402436 := by
        calc
          (2 : ZMod 59567237) ^ 9901 = (2 : ZMod 59567237) ^ (4950 + 4950 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 4950 * (2 : ZMod 59567237) ^ 4950) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 11402436 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 59567237) ^ 19802 = 44685780 := by
        calc
          (2 : ZMod 59567237) ^ 19802 = (2 : ZMod 59567237) ^ (9901 + 9901) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 9901 * (2 : ZMod 59567237) ^ 9901 := by rw [pow_add]
          _ = 44685780 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 59567237) ^ 39605 = 57974163 := by
        calc
          (2 : ZMod 59567237) ^ 39605 = (2 : ZMod 59567237) ^ (19802 + 19802 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 19802 * (2 : ZMod 59567237) ^ 19802) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 57974163 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 59567237) ^ 79211 = 45274182 := by
        calc
          (2 : ZMod 59567237) ^ 79211 = (2 : ZMod 59567237) ^ (39605 + 39605 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 39605 * (2 : ZMod 59567237) ^ 39605) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 45274182 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 59567237) ^ 158423 = 24809731 := by
        calc
          (2 : ZMod 59567237) ^ 158423 = (2 : ZMod 59567237) ^ (79211 + 79211 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 79211 * (2 : ZMod 59567237) ^ 79211) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 24809731 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 59567237) ^ 316847 = 35065540 := by
        calc
          (2 : ZMod 59567237) ^ 316847 = (2 : ZMod 59567237) ^ (158423 + 158423 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 158423 * (2 : ZMod 59567237) ^ 158423) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 35065540 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 59567237) ^ 633694 = 6987981 := by
        calc
          (2 : ZMod 59567237) ^ 633694 = (2 : ZMod 59567237) ^ (316847 + 316847) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 316847 * (2 : ZMod 59567237) ^ 316847 := by rw [pow_add]
          _ = 6987981 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 59567237) ^ 1267388 = 27610212 := by
        calc
          (2 : ZMod 59567237) ^ 1267388 = (2 : ZMod 59567237) ^ (633694 + 633694) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 633694 * (2 : ZMod 59567237) ^ 633694 := by rw [pow_add]
          _ = 27610212 := by rw [factor_1_19]; decide
      change (2 : ZMod 59567237) ^ 1267388 ≠ 1
      rw [factor_1_20]
      decide
    ·
      have factor_2_0 : (2 : ZMod 59567237) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 59567237) ^ 2 = 4 := by
        calc
          (2 : ZMod 59567237) ^ 2 = (2 : ZMod 59567237) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 1 * (2 : ZMod 59567237) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 59567237) ^ 5 = 32 := by
        calc
          (2 : ZMod 59567237) ^ 5 = (2 : ZMod 59567237) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 2 * (2 : ZMod 59567237) ^ 2) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 59567237) ^ 11 = 2048 := by
        calc
          (2 : ZMod 59567237) ^ 11 = (2 : ZMod 59567237) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 5 * (2 : ZMod 59567237) ^ 5) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 59567237) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 59567237) ^ 23 = (2 : ZMod 59567237) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 11 * (2 : ZMod 59567237) ^ 11) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 59567237) ^ 47 = 2781486 := by
        calc
          (2 : ZMod 59567237) ^ 47 = (2 : ZMod 59567237) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = ((2 : ZMod 59567237) ^ 23 * (2 : ZMod 59567237) ^ 23) * (2 : ZMod 59567237) := by rw [pow_succ, pow_add]
          _ = 2781486 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 59567237) ^ 94 = 12059399 := by
        calc
          (2 : ZMod 59567237) ^ 94 = (2 : ZMod 59567237) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 47 * (2 : ZMod 59567237) ^ 47 := by rw [pow_add]
          _ = 12059399 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 59567237) ^ 188 = 43514002 := by
        calc
          (2 : ZMod 59567237) ^ 188 = (2 : ZMod 59567237) ^ (94 + 94) :=
            congrArg (fun n : ℕ => (2 : ZMod 59567237) ^ n) (by norm_num)
          _ = (2 : ZMod 59567237) ^ 94 * (2 : ZMod 59567237) ^ 94 := by rw [pow_add]
          _ = 43514002 := by rw [factor_2_6]; decide
      change (2 : ZMod 59567237) ^ 188 ≠ 1
      rw [factor_2_7]
      decide

#print axioms prime_lucas_59567237

end TotientTailPeriodKiller
end Erdos249257
