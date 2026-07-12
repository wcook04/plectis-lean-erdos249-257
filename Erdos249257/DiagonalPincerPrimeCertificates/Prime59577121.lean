import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_59577121 : Nat.Prime 59577121 := by
  apply lucas_primality 59577121 (11 : ZMod 59577121)
  ·
      have fermat_0 : (11 : ZMod 59577121) ^ 1 = 11 := by norm_num
      have fermat_1 : (11 : ZMod 59577121) ^ 3 = 1331 := by
        calc
          (11 : ZMod 59577121) ^ 3 = (11 : ZMod 59577121) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 1 * (11 : ZMod 59577121) ^ 1) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 1331 := by rw [fermat_0]; decide
      have fermat_2 : (11 : ZMod 59577121) ^ 7 = 19487171 := by
        calc
          (11 : ZMod 59577121) ^ 7 = (11 : ZMod 59577121) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 3 * (11 : ZMod 59577121) ^ 3) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 19487171 := by rw [fermat_1]; decide
      have fermat_3 : (11 : ZMod 59577121) ^ 14 = 21542593 := by
        calc
          (11 : ZMod 59577121) ^ 14 = (11 : ZMod 59577121) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 7 * (11 : ZMod 59577121) ^ 7 := by rw [pow_add]
          _ = 21542593 := by rw [fermat_2]; decide
      have fermat_4 : (11 : ZMod 59577121) ^ 28 = 1148266 := by
        calc
          (11 : ZMod 59577121) ^ 28 = (11 : ZMod 59577121) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 14 * (11 : ZMod 59577121) ^ 14 := by rw [pow_add]
          _ = 1148266 := by rw [fermat_3]; decide
      have fermat_5 : (11 : ZMod 59577121) ^ 56 = 13541905 := by
        calc
          (11 : ZMod 59577121) ^ 56 = (11 : ZMod 59577121) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 28 * (11 : ZMod 59577121) ^ 28 := by rw [pow_add]
          _ = 13541905 := by rw [fermat_4]; decide
      have fermat_6 : (11 : ZMod 59577121) ^ 113 = 34017827 := by
        calc
          (11 : ZMod 59577121) ^ 113 = (11 : ZMod 59577121) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 56 * (11 : ZMod 59577121) ^ 56) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 34017827 := by rw [fermat_5]; decide
      have fermat_7 : (11 : ZMod 59577121) ^ 227 = 40468662 := by
        calc
          (11 : ZMod 59577121) ^ 227 = (11 : ZMod 59577121) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 113 * (11 : ZMod 59577121) ^ 113) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 40468662 := by rw [fermat_6]; decide
      have fermat_8 : (11 : ZMod 59577121) ^ 454 = 44180173 := by
        calc
          (11 : ZMod 59577121) ^ 454 = (11 : ZMod 59577121) ^ (227 + 227) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 227 * (11 : ZMod 59577121) ^ 227 := by rw [pow_add]
          _ = 44180173 := by rw [fermat_7]; decide
      have fermat_9 : (11 : ZMod 59577121) ^ 909 = 50304749 := by
        calc
          (11 : ZMod 59577121) ^ 909 = (11 : ZMod 59577121) ^ (454 + 454 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 454 * (11 : ZMod 59577121) ^ 454) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 50304749 := by rw [fermat_8]; decide
      have fermat_10 : (11 : ZMod 59577121) ^ 1818 = 7225985 := by
        calc
          (11 : ZMod 59577121) ^ 1818 = (11 : ZMod 59577121) ^ (909 + 909) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 909 * (11 : ZMod 59577121) ^ 909 := by rw [pow_add]
          _ = 7225985 := by rw [fermat_9]; decide
      have fermat_11 : (11 : ZMod 59577121) ^ 3636 = 40524921 := by
        calc
          (11 : ZMod 59577121) ^ 3636 = (11 : ZMod 59577121) ^ (1818 + 1818) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 1818 * (11 : ZMod 59577121) ^ 1818 := by rw [pow_add]
          _ = 40524921 := by rw [fermat_10]; decide
      have fermat_12 : (11 : ZMod 59577121) ^ 7272 = 25220727 := by
        calc
          (11 : ZMod 59577121) ^ 7272 = (11 : ZMod 59577121) ^ (3636 + 3636) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 3636 * (11 : ZMod 59577121) ^ 3636 := by rw [pow_add]
          _ = 25220727 := by rw [fermat_11]; decide
      have fermat_13 : (11 : ZMod 59577121) ^ 14545 = 54132405 := by
        calc
          (11 : ZMod 59577121) ^ 14545 = (11 : ZMod 59577121) ^ (7272 + 7272 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 7272 * (11 : ZMod 59577121) ^ 7272) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 54132405 := by rw [fermat_12]; decide
      have fermat_14 : (11 : ZMod 59577121) ^ 29090 = 12259387 := by
        calc
          (11 : ZMod 59577121) ^ 29090 = (11 : ZMod 59577121) ^ (14545 + 14545) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 14545 * (11 : ZMod 59577121) ^ 14545 := by rw [pow_add]
          _ = 12259387 := by rw [fermat_13]; decide
      have fermat_15 : (11 : ZMod 59577121) ^ 58180 = 47439514 := by
        calc
          (11 : ZMod 59577121) ^ 58180 = (11 : ZMod 59577121) ^ (29090 + 29090) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 29090 * (11 : ZMod 59577121) ^ 29090 := by rw [pow_add]
          _ = 47439514 := by rw [fermat_14]; decide
      have fermat_16 : (11 : ZMod 59577121) ^ 116361 = 5068047 := by
        calc
          (11 : ZMod 59577121) ^ 116361 = (11 : ZMod 59577121) ^ (58180 + 58180 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 58180 * (11 : ZMod 59577121) ^ 58180) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 5068047 := by rw [fermat_15]; decide
      have fermat_17 : (11 : ZMod 59577121) ^ 232723 = 8367860 := by
        calc
          (11 : ZMod 59577121) ^ 232723 = (11 : ZMod 59577121) ^ (116361 + 116361 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 116361 * (11 : ZMod 59577121) ^ 116361) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 8367860 := by rw [fermat_16]; decide
      have fermat_18 : (11 : ZMod 59577121) ^ 465446 = 31091179 := by
        calc
          (11 : ZMod 59577121) ^ 465446 = (11 : ZMod 59577121) ^ (232723 + 232723) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 232723 * (11 : ZMod 59577121) ^ 232723 := by rw [pow_add]
          _ = 31091179 := by rw [fermat_17]; decide
      have fermat_19 : (11 : ZMod 59577121) ^ 930892 = 43656182 := by
        calc
          (11 : ZMod 59577121) ^ 930892 = (11 : ZMod 59577121) ^ (465446 + 465446) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 465446 * (11 : ZMod 59577121) ^ 465446 := by rw [pow_add]
          _ = 43656182 := by rw [fermat_18]; decide
      have fermat_20 : (11 : ZMod 59577121) ^ 1861785 = 54967068 := by
        calc
          (11 : ZMod 59577121) ^ 1861785 = (11 : ZMod 59577121) ^ (930892 + 930892 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 930892 * (11 : ZMod 59577121) ^ 930892) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 54967068 := by rw [fermat_19]; decide
      have fermat_21 : (11 : ZMod 59577121) ^ 3723570 = 59328326 := by
        calc
          (11 : ZMod 59577121) ^ 3723570 = (11 : ZMod 59577121) ^ (1861785 + 1861785) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 1861785 * (11 : ZMod 59577121) ^ 1861785 := by rw [pow_add]
          _ = 59328326 := by rw [fermat_20]; decide
      have fermat_22 : (11 : ZMod 59577121) ^ 7447140 = 57900427 := by
        calc
          (11 : ZMod 59577121) ^ 7447140 = (11 : ZMod 59577121) ^ (3723570 + 3723570) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 3723570 * (11 : ZMod 59577121) ^ 3723570 := by rw [pow_add]
          _ = 57900427 := by rw [fermat_21]; decide
      have fermat_23 : (11 : ZMod 59577121) ^ 14894280 = 37161009 := by
        calc
          (11 : ZMod 59577121) ^ 14894280 = (11 : ZMod 59577121) ^ (7447140 + 7447140) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 7447140 * (11 : ZMod 59577121) ^ 7447140 := by rw [pow_add]
          _ = 37161009 := by rw [fermat_22]; decide
      have fermat_24 : (11 : ZMod 59577121) ^ 29788560 = 59577120 := by
        calc
          (11 : ZMod 59577121) ^ 29788560 = (11 : ZMod 59577121) ^ (14894280 + 14894280) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 14894280 * (11 : ZMod 59577121) ^ 14894280 := by rw [pow_add]
          _ = 59577120 := by rw [fermat_23]; decide
      have fermat_25 : (11 : ZMod 59577121) ^ 59577120 = 1 := by
        calc
          (11 : ZMod 59577121) ^ 59577120 = (11 : ZMod 59577121) ^ (29788560 + 29788560) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 29788560 * (11 : ZMod 59577121) ^ 29788560 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 4), (5, 1), (4597, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 4), (5, 1), (4597, 1)] : List FactorBlock).map factorBlockValue).prod = 59577121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (11 : ZMod 59577121) ^ 1 = 11 := by norm_num
      have factor_0_1 : (11 : ZMod 59577121) ^ 3 = 1331 := by
        calc
          (11 : ZMod 59577121) ^ 3 = (11 : ZMod 59577121) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 1 * (11 : ZMod 59577121) ^ 1) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 1331 := by rw [factor_0_0]; decide
      have factor_0_2 : (11 : ZMod 59577121) ^ 7 = 19487171 := by
        calc
          (11 : ZMod 59577121) ^ 7 = (11 : ZMod 59577121) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 3 * (11 : ZMod 59577121) ^ 3) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 19487171 := by rw [factor_0_1]; decide
      have factor_0_3 : (11 : ZMod 59577121) ^ 14 = 21542593 := by
        calc
          (11 : ZMod 59577121) ^ 14 = (11 : ZMod 59577121) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 7 * (11 : ZMod 59577121) ^ 7 := by rw [pow_add]
          _ = 21542593 := by rw [factor_0_2]; decide
      have factor_0_4 : (11 : ZMod 59577121) ^ 28 = 1148266 := by
        calc
          (11 : ZMod 59577121) ^ 28 = (11 : ZMod 59577121) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 14 * (11 : ZMod 59577121) ^ 14 := by rw [pow_add]
          _ = 1148266 := by rw [factor_0_3]; decide
      have factor_0_5 : (11 : ZMod 59577121) ^ 56 = 13541905 := by
        calc
          (11 : ZMod 59577121) ^ 56 = (11 : ZMod 59577121) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 28 * (11 : ZMod 59577121) ^ 28 := by rw [pow_add]
          _ = 13541905 := by rw [factor_0_4]; decide
      have factor_0_6 : (11 : ZMod 59577121) ^ 113 = 34017827 := by
        calc
          (11 : ZMod 59577121) ^ 113 = (11 : ZMod 59577121) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 56 * (11 : ZMod 59577121) ^ 56) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 34017827 := by rw [factor_0_5]; decide
      have factor_0_7 : (11 : ZMod 59577121) ^ 227 = 40468662 := by
        calc
          (11 : ZMod 59577121) ^ 227 = (11 : ZMod 59577121) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 113 * (11 : ZMod 59577121) ^ 113) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 40468662 := by rw [factor_0_6]; decide
      have factor_0_8 : (11 : ZMod 59577121) ^ 454 = 44180173 := by
        calc
          (11 : ZMod 59577121) ^ 454 = (11 : ZMod 59577121) ^ (227 + 227) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 227 * (11 : ZMod 59577121) ^ 227 := by rw [pow_add]
          _ = 44180173 := by rw [factor_0_7]; decide
      have factor_0_9 : (11 : ZMod 59577121) ^ 909 = 50304749 := by
        calc
          (11 : ZMod 59577121) ^ 909 = (11 : ZMod 59577121) ^ (454 + 454 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 454 * (11 : ZMod 59577121) ^ 454) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 50304749 := by rw [factor_0_8]; decide
      have factor_0_10 : (11 : ZMod 59577121) ^ 1818 = 7225985 := by
        calc
          (11 : ZMod 59577121) ^ 1818 = (11 : ZMod 59577121) ^ (909 + 909) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 909 * (11 : ZMod 59577121) ^ 909 := by rw [pow_add]
          _ = 7225985 := by rw [factor_0_9]; decide
      have factor_0_11 : (11 : ZMod 59577121) ^ 3636 = 40524921 := by
        calc
          (11 : ZMod 59577121) ^ 3636 = (11 : ZMod 59577121) ^ (1818 + 1818) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 1818 * (11 : ZMod 59577121) ^ 1818 := by rw [pow_add]
          _ = 40524921 := by rw [factor_0_10]; decide
      have factor_0_12 : (11 : ZMod 59577121) ^ 7272 = 25220727 := by
        calc
          (11 : ZMod 59577121) ^ 7272 = (11 : ZMod 59577121) ^ (3636 + 3636) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 3636 * (11 : ZMod 59577121) ^ 3636 := by rw [pow_add]
          _ = 25220727 := by rw [factor_0_11]; decide
      have factor_0_13 : (11 : ZMod 59577121) ^ 14545 = 54132405 := by
        calc
          (11 : ZMod 59577121) ^ 14545 = (11 : ZMod 59577121) ^ (7272 + 7272 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 7272 * (11 : ZMod 59577121) ^ 7272) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 54132405 := by rw [factor_0_12]; decide
      have factor_0_14 : (11 : ZMod 59577121) ^ 29090 = 12259387 := by
        calc
          (11 : ZMod 59577121) ^ 29090 = (11 : ZMod 59577121) ^ (14545 + 14545) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 14545 * (11 : ZMod 59577121) ^ 14545 := by rw [pow_add]
          _ = 12259387 := by rw [factor_0_13]; decide
      have factor_0_15 : (11 : ZMod 59577121) ^ 58180 = 47439514 := by
        calc
          (11 : ZMod 59577121) ^ 58180 = (11 : ZMod 59577121) ^ (29090 + 29090) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 29090 * (11 : ZMod 59577121) ^ 29090 := by rw [pow_add]
          _ = 47439514 := by rw [factor_0_14]; decide
      have factor_0_16 : (11 : ZMod 59577121) ^ 116361 = 5068047 := by
        calc
          (11 : ZMod 59577121) ^ 116361 = (11 : ZMod 59577121) ^ (58180 + 58180 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 58180 * (11 : ZMod 59577121) ^ 58180) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 5068047 := by rw [factor_0_15]; decide
      have factor_0_17 : (11 : ZMod 59577121) ^ 232723 = 8367860 := by
        calc
          (11 : ZMod 59577121) ^ 232723 = (11 : ZMod 59577121) ^ (116361 + 116361 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 116361 * (11 : ZMod 59577121) ^ 116361) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 8367860 := by rw [factor_0_16]; decide
      have factor_0_18 : (11 : ZMod 59577121) ^ 465446 = 31091179 := by
        calc
          (11 : ZMod 59577121) ^ 465446 = (11 : ZMod 59577121) ^ (232723 + 232723) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 232723 * (11 : ZMod 59577121) ^ 232723 := by rw [pow_add]
          _ = 31091179 := by rw [factor_0_17]; decide
      have factor_0_19 : (11 : ZMod 59577121) ^ 930892 = 43656182 := by
        calc
          (11 : ZMod 59577121) ^ 930892 = (11 : ZMod 59577121) ^ (465446 + 465446) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 465446 * (11 : ZMod 59577121) ^ 465446 := by rw [pow_add]
          _ = 43656182 := by rw [factor_0_18]; decide
      have factor_0_20 : (11 : ZMod 59577121) ^ 1861785 = 54967068 := by
        calc
          (11 : ZMod 59577121) ^ 1861785 = (11 : ZMod 59577121) ^ (930892 + 930892 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 930892 * (11 : ZMod 59577121) ^ 930892) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 54967068 := by rw [factor_0_19]; decide
      have factor_0_21 : (11 : ZMod 59577121) ^ 3723570 = 59328326 := by
        calc
          (11 : ZMod 59577121) ^ 3723570 = (11 : ZMod 59577121) ^ (1861785 + 1861785) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 1861785 * (11 : ZMod 59577121) ^ 1861785 := by rw [pow_add]
          _ = 59328326 := by rw [factor_0_20]; decide
      have factor_0_22 : (11 : ZMod 59577121) ^ 7447140 = 57900427 := by
        calc
          (11 : ZMod 59577121) ^ 7447140 = (11 : ZMod 59577121) ^ (3723570 + 3723570) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 3723570 * (11 : ZMod 59577121) ^ 3723570 := by rw [pow_add]
          _ = 57900427 := by rw [factor_0_21]; decide
      have factor_0_23 : (11 : ZMod 59577121) ^ 14894280 = 37161009 := by
        calc
          (11 : ZMod 59577121) ^ 14894280 = (11 : ZMod 59577121) ^ (7447140 + 7447140) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 7447140 * (11 : ZMod 59577121) ^ 7447140 := by rw [pow_add]
          _ = 37161009 := by rw [factor_0_22]; decide
      have factor_0_24 : (11 : ZMod 59577121) ^ 29788560 = 59577120 := by
        calc
          (11 : ZMod 59577121) ^ 29788560 = (11 : ZMod 59577121) ^ (14894280 + 14894280) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 14894280 * (11 : ZMod 59577121) ^ 14894280 := by rw [pow_add]
          _ = 59577120 := by rw [factor_0_23]; decide
      change (11 : ZMod 59577121) ^ 29788560 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (11 : ZMod 59577121) ^ 1 = 11 := by norm_num
      have factor_1_1 : (11 : ZMod 59577121) ^ 2 = 121 := by
        calc
          (11 : ZMod 59577121) ^ 2 = (11 : ZMod 59577121) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 1 * (11 : ZMod 59577121) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_1_0]; decide
      have factor_1_2 : (11 : ZMod 59577121) ^ 4 = 14641 := by
        calc
          (11 : ZMod 59577121) ^ 4 = (11 : ZMod 59577121) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 2 * (11 : ZMod 59577121) ^ 2 := by rw [pow_add]
          _ = 14641 := by rw [factor_1_1]; decide
      have factor_1_3 : (11 : ZMod 59577121) ^ 9 = 34439972 := by
        calc
          (11 : ZMod 59577121) ^ 9 = (11 : ZMod 59577121) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 4 * (11 : ZMod 59577121) ^ 4) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 34439972 := by rw [factor_1_2]; decide
      have factor_1_4 : (11 : ZMod 59577121) ^ 18 = 3825539 := by
        calc
          (11 : ZMod 59577121) ^ 18 = (11 : ZMod 59577121) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 9 * (11 : ZMod 59577121) ^ 9 := by rw [pow_add]
          _ = 3825539 := by rw [factor_1_3]; decide
      have factor_1_5 : (11 : ZMod 59577121) ^ 37 = 28356930 := by
        calc
          (11 : ZMod 59577121) ^ 37 = (11 : ZMod 59577121) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 18 * (11 : ZMod 59577121) ^ 18) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 28356930 := by rw [factor_1_4]; decide
      have factor_1_6 : (11 : ZMod 59577121) ^ 75 = 5962172 := by
        calc
          (11 : ZMod 59577121) ^ 75 = (11 : ZMod 59577121) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 37 * (11 : ZMod 59577121) ^ 37) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 5962172 := by rw [factor_1_5]; decide
      have factor_1_7 : (11 : ZMod 59577121) ^ 151 = 45428366 := by
        calc
          (11 : ZMod 59577121) ^ 151 = (11 : ZMod 59577121) ^ (75 + 75 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 75 * (11 : ZMod 59577121) ^ 75) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 45428366 := by rw [factor_1_6]; decide
      have factor_1_8 : (11 : ZMod 59577121) ^ 303 = 11977412 := by
        calc
          (11 : ZMod 59577121) ^ 303 = (11 : ZMod 59577121) ^ (151 + 151 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 151 * (11 : ZMod 59577121) ^ 151) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 11977412 := by rw [factor_1_7]; decide
      have factor_1_9 : (11 : ZMod 59577121) ^ 606 = 27168520 := by
        calc
          (11 : ZMod 59577121) ^ 606 = (11 : ZMod 59577121) ^ (303 + 303) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 303 * (11 : ZMod 59577121) ^ 303 := by rw [pow_add]
          _ = 27168520 := by rw [factor_1_8]; decide
      have factor_1_10 : (11 : ZMod 59577121) ^ 1212 = 2291498 := by
        calc
          (11 : ZMod 59577121) ^ 1212 = (11 : ZMod 59577121) ^ (606 + 606) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 606 * (11 : ZMod 59577121) ^ 606 := by rw [pow_add]
          _ = 2291498 := by rw [factor_1_9]; decide
      have factor_1_11 : (11 : ZMod 59577121) ^ 2424 = 14370427 := by
        calc
          (11 : ZMod 59577121) ^ 2424 = (11 : ZMod 59577121) ^ (1212 + 1212) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 1212 * (11 : ZMod 59577121) ^ 1212 := by rw [pow_add]
          _ = 14370427 := by rw [factor_1_10]; decide
      have factor_1_12 : (11 : ZMod 59577121) ^ 4848 = 36073200 := by
        calc
          (11 : ZMod 59577121) ^ 4848 = (11 : ZMod 59577121) ^ (2424 + 2424) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 2424 * (11 : ZMod 59577121) ^ 2424 := by rw [pow_add]
          _ = 36073200 := by rw [factor_1_11]; decide
      have factor_1_13 : (11 : ZMod 59577121) ^ 9696 = 26383730 := by
        calc
          (11 : ZMod 59577121) ^ 9696 = (11 : ZMod 59577121) ^ (4848 + 4848) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 4848 * (11 : ZMod 59577121) ^ 4848 := by rw [pow_add]
          _ = 26383730 := by rw [factor_1_12]; decide
      have factor_1_14 : (11 : ZMod 59577121) ^ 19393 = 42206468 := by
        calc
          (11 : ZMod 59577121) ^ 19393 = (11 : ZMod 59577121) ^ (9696 + 9696 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 9696 * (11 : ZMod 59577121) ^ 9696) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 42206468 := by rw [factor_1_13]; decide
      have factor_1_15 : (11 : ZMod 59577121) ^ 38787 = 18503561 := by
        calc
          (11 : ZMod 59577121) ^ 38787 = (11 : ZMod 59577121) ^ (19393 + 19393 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 19393 * (11 : ZMod 59577121) ^ 19393) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 18503561 := by rw [factor_1_14]; decide
      have factor_1_16 : (11 : ZMod 59577121) ^ 77574 = 38627935 := by
        calc
          (11 : ZMod 59577121) ^ 77574 = (11 : ZMod 59577121) ^ (38787 + 38787) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 38787 * (11 : ZMod 59577121) ^ 38787 := by rw [pow_add]
          _ = 38627935 := by rw [factor_1_15]; decide
      have factor_1_17 : (11 : ZMod 59577121) ^ 155148 = 26122285 := by
        calc
          (11 : ZMod 59577121) ^ 155148 = (11 : ZMod 59577121) ^ (77574 + 77574) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 77574 * (11 : ZMod 59577121) ^ 77574 := by rw [pow_add]
          _ = 26122285 := by rw [factor_1_16]; decide
      have factor_1_18 : (11 : ZMod 59577121) ^ 310297 = 43999803 := by
        calc
          (11 : ZMod 59577121) ^ 310297 = (11 : ZMod 59577121) ^ (155148 + 155148 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 155148 * (11 : ZMod 59577121) ^ 155148) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 43999803 := by rw [factor_1_17]; decide
      have factor_1_19 : (11 : ZMod 59577121) ^ 620595 = 51239207 := by
        calc
          (11 : ZMod 59577121) ^ 620595 = (11 : ZMod 59577121) ^ (310297 + 310297 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 310297 * (11 : ZMod 59577121) ^ 310297) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 51239207 := by rw [factor_1_18]; decide
      have factor_1_20 : (11 : ZMod 59577121) ^ 1241190 = 29068012 := by
        calc
          (11 : ZMod 59577121) ^ 1241190 = (11 : ZMod 59577121) ^ (620595 + 620595) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 620595 * (11 : ZMod 59577121) ^ 620595 := by rw [pow_add]
          _ = 29068012 := by rw [factor_1_19]; decide
      have factor_1_21 : (11 : ZMod 59577121) ^ 2482380 = 20214178 := by
        calc
          (11 : ZMod 59577121) ^ 2482380 = (11 : ZMod 59577121) ^ (1241190 + 1241190) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 1241190 * (11 : ZMod 59577121) ^ 1241190 := by rw [pow_add]
          _ = 20214178 := by rw [factor_1_20]; decide
      have factor_1_22 : (11 : ZMod 59577121) ^ 4964760 = 31095529 := by
        calc
          (11 : ZMod 59577121) ^ 4964760 = (11 : ZMod 59577121) ^ (2482380 + 2482380) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 2482380 * (11 : ZMod 59577121) ^ 2482380 := by rw [pow_add]
          _ = 31095529 := by rw [factor_1_21]; decide
      have factor_1_23 : (11 : ZMod 59577121) ^ 9929520 = 16129521 := by
        calc
          (11 : ZMod 59577121) ^ 9929520 = (11 : ZMod 59577121) ^ (4964760 + 4964760) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 4964760 * (11 : ZMod 59577121) ^ 4964760 := by rw [pow_add]
          _ = 16129521 := by rw [factor_1_22]; decide
      have factor_1_24 : (11 : ZMod 59577121) ^ 19859040 = 16129520 := by
        calc
          (11 : ZMod 59577121) ^ 19859040 = (11 : ZMod 59577121) ^ (9929520 + 9929520) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 9929520 * (11 : ZMod 59577121) ^ 9929520 := by rw [pow_add]
          _ = 16129520 := by rw [factor_1_23]; decide
      change (11 : ZMod 59577121) ^ 19859040 ≠ 1
      rw [factor_1_24]
      decide
    ·
      have factor_2_0 : (11 : ZMod 59577121) ^ 1 = 11 := by norm_num
      have factor_2_1 : (11 : ZMod 59577121) ^ 2 = 121 := by
        calc
          (11 : ZMod 59577121) ^ 2 = (11 : ZMod 59577121) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 1 * (11 : ZMod 59577121) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_2_0]; decide
      have factor_2_2 : (11 : ZMod 59577121) ^ 5 = 161051 := by
        calc
          (11 : ZMod 59577121) ^ 5 = (11 : ZMod 59577121) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 2 * (11 : ZMod 59577121) ^ 2) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 161051 := by rw [factor_2_1]; decide
      have factor_2_3 : (11 : ZMod 59577121) ^ 11 = 56415263 := by
        calc
          (11 : ZMod 59577121) ^ 11 = (11 : ZMod 59577121) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 5 * (11 : ZMod 59577121) ^ 5) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 56415263 := by rw [factor_2_2]; decide
      have factor_2_4 : (11 : ZMod 59577121) ^ 22 = 7222759 := by
        calc
          (11 : ZMod 59577121) ^ 22 = (11 : ZMod 59577121) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 11 * (11 : ZMod 59577121) ^ 11 := by rw [pow_add]
          _ = 7222759 := by rw [factor_2_3]; decide
      have factor_2_5 : (11 : ZMod 59577121) ^ 45 = 21308026 := by
        calc
          (11 : ZMod 59577121) ^ 45 = (11 : ZMod 59577121) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 22 * (11 : ZMod 59577121) ^ 22) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 21308026 := by rw [factor_2_4]; decide
      have factor_2_6 : (11 : ZMod 59577121) ^ 90 = 35239445 := by
        calc
          (11 : ZMod 59577121) ^ 90 = (11 : ZMod 59577121) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 45 * (11 : ZMod 59577121) ^ 45 := by rw [pow_add]
          _ = 35239445 := by rw [factor_2_5]; decide
      have factor_2_7 : (11 : ZMod 59577121) ^ 181 = 42727333 := by
        calc
          (11 : ZMod 59577121) ^ 181 = (11 : ZMod 59577121) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 90 * (11 : ZMod 59577121) ^ 90) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 42727333 := by rw [factor_2_6]; decide
      have factor_2_8 : (11 : ZMod 59577121) ^ 363 = 6384816 := by
        calc
          (11 : ZMod 59577121) ^ 363 = (11 : ZMod 59577121) ^ (181 + 181 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 181 * (11 : ZMod 59577121) ^ 181) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 6384816 := by rw [factor_2_7]; decide
      have factor_2_9 : (11 : ZMod 59577121) ^ 727 = 31166584 := by
        calc
          (11 : ZMod 59577121) ^ 727 = (11 : ZMod 59577121) ^ (363 + 363 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 363 * (11 : ZMod 59577121) ^ 363) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 31166584 := by rw [factor_2_8]; decide
      have factor_2_10 : (11 : ZMod 59577121) ^ 1454 = 32294639 := by
        calc
          (11 : ZMod 59577121) ^ 1454 = (11 : ZMod 59577121) ^ (727 + 727) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 727 * (11 : ZMod 59577121) ^ 727 := by rw [pow_add]
          _ = 32294639 := by rw [factor_2_9]; decide
      have factor_2_11 : (11 : ZMod 59577121) ^ 2909 = 2969280 := by
        calc
          (11 : ZMod 59577121) ^ 2909 = (11 : ZMod 59577121) ^ (1454 + 1454 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 1454 * (11 : ZMod 59577121) ^ 1454) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 2969280 := by rw [factor_2_10]; decide
      have factor_2_12 : (11 : ZMod 59577121) ^ 5818 = 43890094 := by
        calc
          (11 : ZMod 59577121) ^ 5818 = (11 : ZMod 59577121) ^ (2909 + 2909) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 2909 * (11 : ZMod 59577121) ^ 2909 := by rw [pow_add]
          _ = 43890094 := by rw [factor_2_11]; decide
      have factor_2_13 : (11 : ZMod 59577121) ^ 11636 = 54002318 := by
        calc
          (11 : ZMod 59577121) ^ 11636 = (11 : ZMod 59577121) ^ (5818 + 5818) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 5818 * (11 : ZMod 59577121) ^ 5818 := by rw [pow_add]
          _ = 54002318 := by rw [factor_2_12]; decide
      have factor_2_14 : (11 : ZMod 59577121) ^ 23272 = 23319159 := by
        calc
          (11 : ZMod 59577121) ^ 23272 = (11 : ZMod 59577121) ^ (11636 + 11636) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 11636 * (11 : ZMod 59577121) ^ 11636 := by rw [pow_add]
          _ = 23319159 := by rw [factor_2_13]; decide
      have factor_2_15 : (11 : ZMod 59577121) ^ 46544 = 34640059 := by
        calc
          (11 : ZMod 59577121) ^ 46544 = (11 : ZMod 59577121) ^ (23272 + 23272) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 23272 * (11 : ZMod 59577121) ^ 23272 := by rw [pow_add]
          _ = 34640059 := by rw [factor_2_14]; decide
      have factor_2_16 : (11 : ZMod 59577121) ^ 93089 = 36804813 := by
        calc
          (11 : ZMod 59577121) ^ 93089 = (11 : ZMod 59577121) ^ (46544 + 46544 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 46544 * (11 : ZMod 59577121) ^ 46544) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 36804813 := by rw [factor_2_15]; decide
      have factor_2_17 : (11 : ZMod 59577121) ^ 186178 = 43246870 := by
        calc
          (11 : ZMod 59577121) ^ 186178 = (11 : ZMod 59577121) ^ (93089 + 93089) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 93089 * (11 : ZMod 59577121) ^ 93089 := by rw [pow_add]
          _ = 43246870 := by rw [factor_2_16]; decide
      have factor_2_18 : (11 : ZMod 59577121) ^ 372357 = 38419823 := by
        calc
          (11 : ZMod 59577121) ^ 372357 = (11 : ZMod 59577121) ^ (186178 + 186178 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 186178 * (11 : ZMod 59577121) ^ 186178) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 38419823 := by rw [factor_2_17]; decide
      have factor_2_19 : (11 : ZMod 59577121) ^ 744714 = 49455329 := by
        calc
          (11 : ZMod 59577121) ^ 744714 = (11 : ZMod 59577121) ^ (372357 + 372357) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 372357 * (11 : ZMod 59577121) ^ 372357 := by rw [pow_add]
          _ = 49455329 := by rw [factor_2_18]; decide
      have factor_2_20 : (11 : ZMod 59577121) ^ 1489428 = 9128913 := by
        calc
          (11 : ZMod 59577121) ^ 1489428 = (11 : ZMod 59577121) ^ (744714 + 744714) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 744714 * (11 : ZMod 59577121) ^ 744714 := by rw [pow_add]
          _ = 9128913 := by rw [factor_2_19]; decide
      have factor_2_21 : (11 : ZMod 59577121) ^ 2978856 = 39512680 := by
        calc
          (11 : ZMod 59577121) ^ 2978856 = (11 : ZMod 59577121) ^ (1489428 + 1489428) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 1489428 * (11 : ZMod 59577121) ^ 1489428 := by rw [pow_add]
          _ = 39512680 := by rw [factor_2_20]; decide
      have factor_2_22 : (11 : ZMod 59577121) ^ 5957712 = 2212519 := by
        calc
          (11 : ZMod 59577121) ^ 5957712 = (11 : ZMod 59577121) ^ (2978856 + 2978856) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 2978856 * (11 : ZMod 59577121) ^ 2978856 := by rw [pow_add]
          _ = 2212519 := by rw [factor_2_21]; decide
      have factor_2_23 : (11 : ZMod 59577121) ^ 11915424 = 26601275 := by
        calc
          (11 : ZMod 59577121) ^ 11915424 = (11 : ZMod 59577121) ^ (5957712 + 5957712) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 5957712 * (11 : ZMod 59577121) ^ 5957712 := by rw [pow_add]
          _ = 26601275 := by rw [factor_2_22]; decide
      change (11 : ZMod 59577121) ^ 11915424 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (11 : ZMod 59577121) ^ 1 = 11 := by norm_num
      have factor_3_1 : (11 : ZMod 59577121) ^ 3 = 1331 := by
        calc
          (11 : ZMod 59577121) ^ 3 = (11 : ZMod 59577121) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 1 * (11 : ZMod 59577121) ^ 1) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 1331 := by rw [factor_3_0]; decide
      have factor_3_2 : (11 : ZMod 59577121) ^ 6 = 1771561 := by
        calc
          (11 : ZMod 59577121) ^ 6 = (11 : ZMod 59577121) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 3 * (11 : ZMod 59577121) ^ 3 := by rw [pow_add]
          _ = 1771561 := by rw [factor_3_1]; decide
      have factor_3_3 : (11 : ZMod 59577121) ^ 12 = 24796683 := by
        calc
          (11 : ZMod 59577121) ^ 12 = (11 : ZMod 59577121) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 6 * (11 : ZMod 59577121) ^ 6 := by rw [pow_add]
          _ = 24796683 := by rw [factor_3_2]; decide
      have factor_3_4 : (11 : ZMod 59577121) ^ 25 = 21575748 := by
        calc
          (11 : ZMod 59577121) ^ 25 = (11 : ZMod 59577121) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 12 * (11 : ZMod 59577121) ^ 12) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 21575748 := by rw [factor_3_3]; decide
      have factor_3_5 : (11 : ZMod 59577121) ^ 50 = 36725726 := by
        calc
          (11 : ZMod 59577121) ^ 50 = (11 : ZMod 59577121) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 25 * (11 : ZMod 59577121) ^ 25 := by rw [pow_add]
          _ = 36725726 := by rw [factor_3_4]; decide
      have factor_3_6 : (11 : ZMod 59577121) ^ 101 = 23416447 := by
        calc
          (11 : ZMod 59577121) ^ 101 = (11 : ZMod 59577121) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 50 * (11 : ZMod 59577121) ^ 50) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 23416447 := by rw [factor_3_5]; decide
      have factor_3_7 : (11 : ZMod 59577121) ^ 202 = 41556109 := by
        calc
          (11 : ZMod 59577121) ^ 202 = (11 : ZMod 59577121) ^ (101 + 101) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 101 * (11 : ZMod 59577121) ^ 101 := by rw [pow_add]
          _ = 41556109 := by rw [factor_3_6]; decide
      have factor_3_8 : (11 : ZMod 59577121) ^ 405 = 51038298 := by
        calc
          (11 : ZMod 59577121) ^ 405 = (11 : ZMod 59577121) ^ (202 + 202 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = ((11 : ZMod 59577121) ^ 202 * (11 : ZMod 59577121) ^ 202) * (11 : ZMod 59577121) := by rw [pow_succ, pow_add]
          _ = 51038298 := by rw [factor_3_7]; decide
      have factor_3_9 : (11 : ZMod 59577121) ^ 810 = 4734472 := by
        calc
          (11 : ZMod 59577121) ^ 810 = (11 : ZMod 59577121) ^ (405 + 405) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 405 * (11 : ZMod 59577121) ^ 405 := by rw [pow_add]
          _ = 4734472 := by rw [factor_3_8]; decide
      have factor_3_10 : (11 : ZMod 59577121) ^ 1620 = 48267986 := by
        calc
          (11 : ZMod 59577121) ^ 1620 = (11 : ZMod 59577121) ^ (810 + 810) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 810 * (11 : ZMod 59577121) ^ 810 := by rw [pow_add]
          _ = 48267986 := by rw [factor_3_9]; decide
      have factor_3_11 : (11 : ZMod 59577121) ^ 3240 = 5289806 := by
        calc
          (11 : ZMod 59577121) ^ 3240 = (11 : ZMod 59577121) ^ (1620 + 1620) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 1620 * (11 : ZMod 59577121) ^ 1620 := by rw [pow_add]
          _ = 5289806 := by rw [factor_3_10]; decide
      have factor_3_12 : (11 : ZMod 59577121) ^ 6480 = 44057719 := by
        calc
          (11 : ZMod 59577121) ^ 6480 = (11 : ZMod 59577121) ^ (3240 + 3240) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 3240 * (11 : ZMod 59577121) ^ 3240 := by rw [pow_add]
          _ = 44057719 := by rw [factor_3_11]; decide
      have factor_3_13 : (11 : ZMod 59577121) ^ 12960 = 7142114 := by
        calc
          (11 : ZMod 59577121) ^ 12960 = (11 : ZMod 59577121) ^ (6480 + 6480) :=
            congrArg (fun n : ℕ => (11 : ZMod 59577121) ^ n) (by norm_num)
          _ = (11 : ZMod 59577121) ^ 6480 * (11 : ZMod 59577121) ^ 6480 := by rw [pow_add]
          _ = 7142114 := by rw [factor_3_12]; decide
      change (11 : ZMod 59577121) ^ 12960 ≠ 1
      rw [factor_3_13]
      decide

#print axioms prime_lucas_59577121

end TotientTailPeriodKiller
end Erdos249257
