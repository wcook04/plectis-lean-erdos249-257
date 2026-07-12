import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_44709187 : Nat.Prime 44709187 := by
  apply lucas_primality 44709187 (2 : ZMod 44709187)
  ·
      have fermat_0 : (2 : ZMod 44709187) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 44709187) ^ 2 = 4 := by
        calc
          (2 : ZMod 44709187) ^ 2 = (2 : ZMod 44709187) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 1 * (2 : ZMod 44709187) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 44709187) ^ 5 = 32 := by
        calc
          (2 : ZMod 44709187) ^ 5 = (2 : ZMod 44709187) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 2 * (2 : ZMod 44709187) ^ 2) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 44709187) ^ 10 = 1024 := by
        calc
          (2 : ZMod 44709187) ^ 10 = (2 : ZMod 44709187) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 5 * (2 : ZMod 44709187) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 44709187) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 44709187) ^ 21 = (2 : ZMod 44709187) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 10 * (2 : ZMod 44709187) ^ 10) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 44709187) ^ 42 = 3785914 := by
        calc
          (2 : ZMod 44709187) ^ 42 = (2 : ZMod 44709187) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 21 * (2 : ZMod 44709187) ^ 21 := by rw [pow_add]
          _ = 3785914 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 44709187) ^ 85 = 10783628 := by
        calc
          (2 : ZMod 44709187) ^ 85 = (2 : ZMod 44709187) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 42 * (2 : ZMod 44709187) ^ 42) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 10783628 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 44709187) ^ 170 = 4659612 := by
        calc
          (2 : ZMod 44709187) ^ 170 = (2 : ZMod 44709187) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 85 * (2 : ZMod 44709187) ^ 85 := by rw [pow_add]
          _ = 4659612 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 44709187) ^ 341 = 35979777 := by
        calc
          (2 : ZMod 44709187) ^ 341 = (2 : ZMod 44709187) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 170 * (2 : ZMod 44709187) ^ 170) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 35979777 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 44709187) ^ 682 = 37079365 := by
        calc
          (2 : ZMod 44709187) ^ 682 = (2 : ZMod 44709187) ^ (341 + 341) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 341 * (2 : ZMod 44709187) ^ 341 := by rw [pow_add]
          _ = 37079365 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 44709187) ^ 1364 = 5598903 := by
        calc
          (2 : ZMod 44709187) ^ 1364 = (2 : ZMod 44709187) ^ (682 + 682) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 682 * (2 : ZMod 44709187) ^ 682 := by rw [pow_add]
          _ = 5598903 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 44709187) ^ 2728 = 2465920 := by
        calc
          (2 : ZMod 44709187) ^ 2728 = (2 : ZMod 44709187) ^ (1364 + 1364) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 1364 * (2 : ZMod 44709187) ^ 1364 := by rw [pow_add]
          _ = 2465920 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 44709187) ^ 5457 = 42809369 := by
        calc
          (2 : ZMod 44709187) ^ 5457 = (2 : ZMod 44709187) ^ (2728 + 2728 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 2728 * (2 : ZMod 44709187) ^ 2728) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 42809369 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 44709187) ^ 10915 = 5660789 := by
        calc
          (2 : ZMod 44709187) ^ 10915 = (2 : ZMod 44709187) ^ (5457 + 5457 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 5457 * (2 : ZMod 44709187) ^ 5457) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 5660789 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 44709187) ^ 21830 = 27085637 := by
        calc
          (2 : ZMod 44709187) ^ 21830 = (2 : ZMod 44709187) ^ (10915 + 10915) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 10915 * (2 : ZMod 44709187) ^ 10915 := by rw [pow_add]
          _ = 27085637 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 44709187) ^ 43661 = 2267571 := by
        calc
          (2 : ZMod 44709187) ^ 43661 = (2 : ZMod 44709187) ^ (21830 + 21830 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 21830 * (2 : ZMod 44709187) ^ 21830) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 2267571 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 44709187) ^ 87322 = 8770732 := by
        calc
          (2 : ZMod 44709187) ^ 87322 = (2 : ZMod 44709187) ^ (43661 + 43661) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 43661 * (2 : ZMod 44709187) ^ 43661 := by rw [pow_add]
          _ = 8770732 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 44709187) ^ 174645 = 13694728 := by
        calc
          (2 : ZMod 44709187) ^ 174645 = (2 : ZMod 44709187) ^ (87322 + 87322 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 87322 * (2 : ZMod 44709187) ^ 87322) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 13694728 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 44709187) ^ 349290 = 13876628 := by
        calc
          (2 : ZMod 44709187) ^ 349290 = (2 : ZMod 44709187) ^ (174645 + 174645) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 174645 * (2 : ZMod 44709187) ^ 174645 := by rw [pow_add]
          _ = 13876628 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 44709187) ^ 698581 = 25671793 := by
        calc
          (2 : ZMod 44709187) ^ 698581 = (2 : ZMod 44709187) ^ (349290 + 349290 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 349290 * (2 : ZMod 44709187) ^ 349290) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 25671793 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 44709187) ^ 1397162 = 43304844 := by
        calc
          (2 : ZMod 44709187) ^ 1397162 = (2 : ZMod 44709187) ^ (698581 + 698581) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 698581 * (2 : ZMod 44709187) ^ 698581 := by rw [pow_add]
          _ = 43304844 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 44709187) ^ 2794324 = 12313892 := by
        calc
          (2 : ZMod 44709187) ^ 2794324 = (2 : ZMod 44709187) ^ (1397162 + 1397162) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 1397162 * (2 : ZMod 44709187) ^ 1397162 := by rw [pow_add]
          _ = 12313892 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 44709187) ^ 5588648 = 13130172 := by
        calc
          (2 : ZMod 44709187) ^ 5588648 = (2 : ZMod 44709187) ^ (2794324 + 2794324) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 2794324 * (2 : ZMod 44709187) ^ 2794324 := by rw [pow_add]
          _ = 13130172 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 44709187) ^ 11177296 = 19707990 := by
        calc
          (2 : ZMod 44709187) ^ 11177296 = (2 : ZMod 44709187) ^ (5588648 + 5588648) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 5588648 * (2 : ZMod 44709187) ^ 5588648 := by rw [pow_add]
          _ = 19707990 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 44709187) ^ 22354593 = 44709186 := by
        calc
          (2 : ZMod 44709187) ^ 22354593 = (2 : ZMod 44709187) ^ (11177296 + 11177296 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 11177296 * (2 : ZMod 44709187) ^ 11177296) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 44709186 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 44709187) ^ 44709186 = 1 := by
        calc
          (2 : ZMod 44709187) ^ 44709186 = (2 : ZMod 44709187) ^ (22354593 + 22354593) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 22354593 * (2 : ZMod 44709187) ^ 22354593 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (2693, 1), (2767, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (2693, 1), (2767, 1)] : List FactorBlock).map factorBlockValue).prod = 44709187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 44709187) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 44709187) ^ 2 = 4 := by
        calc
          (2 : ZMod 44709187) ^ 2 = (2 : ZMod 44709187) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 1 * (2 : ZMod 44709187) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 44709187) ^ 5 = 32 := by
        calc
          (2 : ZMod 44709187) ^ 5 = (2 : ZMod 44709187) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 2 * (2 : ZMod 44709187) ^ 2) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 44709187) ^ 10 = 1024 := by
        calc
          (2 : ZMod 44709187) ^ 10 = (2 : ZMod 44709187) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 5 * (2 : ZMod 44709187) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 44709187) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 44709187) ^ 21 = (2 : ZMod 44709187) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 10 * (2 : ZMod 44709187) ^ 10) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 44709187) ^ 42 = 3785914 := by
        calc
          (2 : ZMod 44709187) ^ 42 = (2 : ZMod 44709187) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 21 * (2 : ZMod 44709187) ^ 21 := by rw [pow_add]
          _ = 3785914 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 44709187) ^ 85 = 10783628 := by
        calc
          (2 : ZMod 44709187) ^ 85 = (2 : ZMod 44709187) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 42 * (2 : ZMod 44709187) ^ 42) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 10783628 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 44709187) ^ 170 = 4659612 := by
        calc
          (2 : ZMod 44709187) ^ 170 = (2 : ZMod 44709187) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 85 * (2 : ZMod 44709187) ^ 85 := by rw [pow_add]
          _ = 4659612 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 44709187) ^ 341 = 35979777 := by
        calc
          (2 : ZMod 44709187) ^ 341 = (2 : ZMod 44709187) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 170 * (2 : ZMod 44709187) ^ 170) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 35979777 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 44709187) ^ 682 = 37079365 := by
        calc
          (2 : ZMod 44709187) ^ 682 = (2 : ZMod 44709187) ^ (341 + 341) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 341 * (2 : ZMod 44709187) ^ 341 := by rw [pow_add]
          _ = 37079365 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 44709187) ^ 1364 = 5598903 := by
        calc
          (2 : ZMod 44709187) ^ 1364 = (2 : ZMod 44709187) ^ (682 + 682) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 682 * (2 : ZMod 44709187) ^ 682 := by rw [pow_add]
          _ = 5598903 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 44709187) ^ 2728 = 2465920 := by
        calc
          (2 : ZMod 44709187) ^ 2728 = (2 : ZMod 44709187) ^ (1364 + 1364) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 1364 * (2 : ZMod 44709187) ^ 1364 := by rw [pow_add]
          _ = 2465920 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 44709187) ^ 5457 = 42809369 := by
        calc
          (2 : ZMod 44709187) ^ 5457 = (2 : ZMod 44709187) ^ (2728 + 2728 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 2728 * (2 : ZMod 44709187) ^ 2728) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 42809369 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 44709187) ^ 10915 = 5660789 := by
        calc
          (2 : ZMod 44709187) ^ 10915 = (2 : ZMod 44709187) ^ (5457 + 5457 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 5457 * (2 : ZMod 44709187) ^ 5457) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 5660789 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 44709187) ^ 21830 = 27085637 := by
        calc
          (2 : ZMod 44709187) ^ 21830 = (2 : ZMod 44709187) ^ (10915 + 10915) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 10915 * (2 : ZMod 44709187) ^ 10915 := by rw [pow_add]
          _ = 27085637 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 44709187) ^ 43661 = 2267571 := by
        calc
          (2 : ZMod 44709187) ^ 43661 = (2 : ZMod 44709187) ^ (21830 + 21830 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 21830 * (2 : ZMod 44709187) ^ 21830) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 2267571 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 44709187) ^ 87322 = 8770732 := by
        calc
          (2 : ZMod 44709187) ^ 87322 = (2 : ZMod 44709187) ^ (43661 + 43661) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 43661 * (2 : ZMod 44709187) ^ 43661 := by rw [pow_add]
          _ = 8770732 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 44709187) ^ 174645 = 13694728 := by
        calc
          (2 : ZMod 44709187) ^ 174645 = (2 : ZMod 44709187) ^ (87322 + 87322 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 87322 * (2 : ZMod 44709187) ^ 87322) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 13694728 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 44709187) ^ 349290 = 13876628 := by
        calc
          (2 : ZMod 44709187) ^ 349290 = (2 : ZMod 44709187) ^ (174645 + 174645) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 174645 * (2 : ZMod 44709187) ^ 174645 := by rw [pow_add]
          _ = 13876628 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 44709187) ^ 698581 = 25671793 := by
        calc
          (2 : ZMod 44709187) ^ 698581 = (2 : ZMod 44709187) ^ (349290 + 349290 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 349290 * (2 : ZMod 44709187) ^ 349290) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 25671793 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 44709187) ^ 1397162 = 43304844 := by
        calc
          (2 : ZMod 44709187) ^ 1397162 = (2 : ZMod 44709187) ^ (698581 + 698581) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 698581 * (2 : ZMod 44709187) ^ 698581 := by rw [pow_add]
          _ = 43304844 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 44709187) ^ 2794324 = 12313892 := by
        calc
          (2 : ZMod 44709187) ^ 2794324 = (2 : ZMod 44709187) ^ (1397162 + 1397162) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 1397162 * (2 : ZMod 44709187) ^ 1397162 := by rw [pow_add]
          _ = 12313892 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 44709187) ^ 5588648 = 13130172 := by
        calc
          (2 : ZMod 44709187) ^ 5588648 = (2 : ZMod 44709187) ^ (2794324 + 2794324) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 2794324 * (2 : ZMod 44709187) ^ 2794324 := by rw [pow_add]
          _ = 13130172 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 44709187) ^ 11177296 = 19707990 := by
        calc
          (2 : ZMod 44709187) ^ 11177296 = (2 : ZMod 44709187) ^ (5588648 + 5588648) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 5588648 * (2 : ZMod 44709187) ^ 5588648 := by rw [pow_add]
          _ = 19707990 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 44709187) ^ 22354593 = 44709186 := by
        calc
          (2 : ZMod 44709187) ^ 22354593 = (2 : ZMod 44709187) ^ (11177296 + 11177296 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 11177296 * (2 : ZMod 44709187) ^ 11177296) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 44709186 := by rw [factor_0_23]; decide
      change (2 : ZMod 44709187) ^ 22354593 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (2 : ZMod 44709187) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 44709187) ^ 3 = 8 := by
        calc
          (2 : ZMod 44709187) ^ 3 = (2 : ZMod 44709187) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 1 * (2 : ZMod 44709187) ^ 1) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 44709187) ^ 7 = 128 := by
        calc
          (2 : ZMod 44709187) ^ 7 = (2 : ZMod 44709187) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 3 * (2 : ZMod 44709187) ^ 3) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 44709187) ^ 14 = 16384 := by
        calc
          (2 : ZMod 44709187) ^ 14 = (2 : ZMod 44709187) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 7 * (2 : ZMod 44709187) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 44709187) ^ 28 = 180334 := by
        calc
          (2 : ZMod 44709187) ^ 28 = (2 : ZMod 44709187) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 14 * (2 : ZMod 44709187) ^ 14 := by rw [pow_add]
          _ = 180334 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 44709187) ^ 56 = 16772607 := by
        calc
          (2 : ZMod 44709187) ^ 56 = (2 : ZMod 44709187) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 28 * (2 : ZMod 44709187) ^ 28 := by rw [pow_add]
          _ = 16772607 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 44709187) ^ 113 = 28683187 := by
        calc
          (2 : ZMod 44709187) ^ 113 = (2 : ZMod 44709187) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 56 * (2 : ZMod 44709187) ^ 56) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 28683187 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 44709187) ^ 227 = 27153829 := by
        calc
          (2 : ZMod 44709187) ^ 227 = (2 : ZMod 44709187) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 113 * (2 : ZMod 44709187) ^ 113) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 27153829 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 44709187) ^ 454 = 19531715 := by
        calc
          (2 : ZMod 44709187) ^ 454 = (2 : ZMod 44709187) ^ (227 + 227) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 227 * (2 : ZMod 44709187) ^ 227 := by rw [pow_add]
          _ = 19531715 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 44709187) ^ 909 = 3352976 := by
        calc
          (2 : ZMod 44709187) ^ 909 = (2 : ZMod 44709187) ^ (454 + 454 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 454 * (2 : ZMod 44709187) ^ 454) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 3352976 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 44709187) ^ 1819 = 20042234 := by
        calc
          (2 : ZMod 44709187) ^ 1819 = (2 : ZMod 44709187) ^ (909 + 909 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 909 * (2 : ZMod 44709187) ^ 909) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 20042234 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 44709187) ^ 3638 = 22415272 := by
        calc
          (2 : ZMod 44709187) ^ 3638 = (2 : ZMod 44709187) ^ (1819 + 1819) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 1819 * (2 : ZMod 44709187) ^ 1819 := by rw [pow_add]
          _ = 22415272 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 44709187) ^ 7276 = 26904325 := by
        calc
          (2 : ZMod 44709187) ^ 7276 = (2 : ZMod 44709187) ^ (3638 + 3638) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 3638 * (2 : ZMod 44709187) ^ 3638 := by rw [pow_add]
          _ = 26904325 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 44709187) ^ 14553 = 9856209 := by
        calc
          (2 : ZMod 44709187) ^ 14553 = (2 : ZMod 44709187) ^ (7276 + 7276 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 7276 * (2 : ZMod 44709187) ^ 7276) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 9856209 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 44709187) ^ 29107 = 37982178 := by
        calc
          (2 : ZMod 44709187) ^ 29107 = (2 : ZMod 44709187) ^ (14553 + 14553 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 14553 * (2 : ZMod 44709187) ^ 14553) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 37982178 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 44709187) ^ 58215 = 1127005 := by
        calc
          (2 : ZMod 44709187) ^ 58215 = (2 : ZMod 44709187) ^ (29107 + 29107 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 29107 * (2 : ZMod 44709187) ^ 29107) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 1127005 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 44709187) ^ 116430 = 41685729 := by
        calc
          (2 : ZMod 44709187) ^ 116430 = (2 : ZMod 44709187) ^ (58215 + 58215) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 58215 * (2 : ZMod 44709187) ^ 58215 := by rw [pow_add]
          _ = 41685729 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 44709187) ^ 232860 = 13194557 := by
        calc
          (2 : ZMod 44709187) ^ 232860 = (2 : ZMod 44709187) ^ (116430 + 116430) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 116430 * (2 : ZMod 44709187) ^ 116430 := by rw [pow_add]
          _ = 13194557 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 44709187) ^ 465720 = 12105485 := by
        calc
          (2 : ZMod 44709187) ^ 465720 = (2 : ZMod 44709187) ^ (232860 + 232860) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 232860 * (2 : ZMod 44709187) ^ 232860 := by rw [pow_add]
          _ = 12105485 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 44709187) ^ 931441 = 2731138 := by
        calc
          (2 : ZMod 44709187) ^ 931441 = (2 : ZMod 44709187) ^ (465720 + 465720 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 465720 * (2 : ZMod 44709187) ^ 465720) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 2731138 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 44709187) ^ 1862882 = 12852712 := by
        calc
          (2 : ZMod 44709187) ^ 1862882 = (2 : ZMod 44709187) ^ (931441 + 931441) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 931441 * (2 : ZMod 44709187) ^ 931441 := by rw [pow_add]
          _ = 12852712 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 44709187) ^ 3725765 = 17269891 := by
        calc
          (2 : ZMod 44709187) ^ 3725765 = (2 : ZMod 44709187) ^ (1862882 + 1862882 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 1862882 * (2 : ZMod 44709187) ^ 1862882) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 17269891 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 44709187) ^ 7451531 = 11156756 := by
        calc
          (2 : ZMod 44709187) ^ 7451531 = (2 : ZMod 44709187) ^ (3725765 + 3725765 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 3725765 * (2 : ZMod 44709187) ^ 3725765) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 11156756 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 44709187) ^ 14903062 = 11156755 := by
        calc
          (2 : ZMod 44709187) ^ 14903062 = (2 : ZMod 44709187) ^ (7451531 + 7451531) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 7451531 * (2 : ZMod 44709187) ^ 7451531 := by rw [pow_add]
          _ = 11156755 := by rw [factor_1_22]; decide
      change (2 : ZMod 44709187) ^ 14903062 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (2 : ZMod 44709187) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 44709187) ^ 2 = 4 := by
        calc
          (2 : ZMod 44709187) ^ 2 = (2 : ZMod 44709187) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 1 * (2 : ZMod 44709187) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 44709187) ^ 4 = 16 := by
        calc
          (2 : ZMod 44709187) ^ 4 = (2 : ZMod 44709187) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 2 * (2 : ZMod 44709187) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 44709187) ^ 8 = 256 := by
        calc
          (2 : ZMod 44709187) ^ 8 = (2 : ZMod 44709187) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 4 * (2 : ZMod 44709187) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 44709187) ^ 16 = 65536 := by
        calc
          (2 : ZMod 44709187) ^ 16 = (2 : ZMod 44709187) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 8 * (2 : ZMod 44709187) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 44709187) ^ 32 = 2885344 := by
        calc
          (2 : ZMod 44709187) ^ 32 = (2 : ZMod 44709187) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 16 * (2 : ZMod 44709187) ^ 16 := by rw [pow_add]
          _ = 2885344 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 44709187) ^ 64 = 1705440 := by
        calc
          (2 : ZMod 44709187) ^ 64 = (2 : ZMod 44709187) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 32 * (2 : ZMod 44709187) ^ 32 := by rw [pow_add]
          _ = 1705440 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 44709187) ^ 129 = 28285004 := by
        calc
          (2 : ZMod 44709187) ^ 129 = (2 : ZMod 44709187) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 64 * (2 : ZMod 44709187) ^ 64) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 28285004 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 44709187) ^ 259 = 26538498 := by
        calc
          (2 : ZMod 44709187) ^ 259 = (2 : ZMod 44709187) ^ (129 + 129 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 129 * (2 : ZMod 44709187) ^ 129) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 26538498 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 44709187) ^ 518 = 35347120 := by
        calc
          (2 : ZMod 44709187) ^ 518 = (2 : ZMod 44709187) ^ (259 + 259) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 259 * (2 : ZMod 44709187) ^ 259 := by rw [pow_add]
          _ = 35347120 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 44709187) ^ 1037 = 11870012 := by
        calc
          (2 : ZMod 44709187) ^ 1037 = (2 : ZMod 44709187) ^ (518 + 518 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 518 * (2 : ZMod 44709187) ^ 518) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 11870012 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 44709187) ^ 2075 = 9370265 := by
        calc
          (2 : ZMod 44709187) ^ 2075 = (2 : ZMod 44709187) ^ (1037 + 1037 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 1037 * (2 : ZMod 44709187) ^ 1037) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 9370265 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 44709187) ^ 4150 = 42244584 := by
        calc
          (2 : ZMod 44709187) ^ 4150 = (2 : ZMod 44709187) ^ (2075 + 2075) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 2075 * (2 : ZMod 44709187) ^ 2075 := by rw [pow_add]
          _ = 42244584 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 44709187) ^ 8301 = 21476017 := by
        calc
          (2 : ZMod 44709187) ^ 8301 = (2 : ZMod 44709187) ^ (4150 + 4150 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 4150 * (2 : ZMod 44709187) ^ 4150) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 21476017 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 44709187) ^ 16602 = 3730094 := by
        calc
          (2 : ZMod 44709187) ^ 16602 = (2 : ZMod 44709187) ^ (8301 + 8301) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 8301 * (2 : ZMod 44709187) ^ 8301 := by rw [pow_add]
          _ = 3730094 := by rw [factor_2_13]; decide
      change (2 : ZMod 44709187) ^ 16602 ≠ 1
      rw [factor_2_14]
      decide
    ·
      have factor_3_0 : (2 : ZMod 44709187) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 44709187) ^ 3 = 8 := by
        calc
          (2 : ZMod 44709187) ^ 3 = (2 : ZMod 44709187) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 1 * (2 : ZMod 44709187) ^ 1) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 44709187) ^ 7 = 128 := by
        calc
          (2 : ZMod 44709187) ^ 7 = (2 : ZMod 44709187) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 3 * (2 : ZMod 44709187) ^ 3) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 44709187) ^ 15 = 32768 := by
        calc
          (2 : ZMod 44709187) ^ 15 = (2 : ZMod 44709187) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 7 * (2 : ZMod 44709187) ^ 7) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 44709187) ^ 31 = 1442672 := by
        calc
          (2 : ZMod 44709187) ^ 31 = (2 : ZMod 44709187) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 15 * (2 : ZMod 44709187) ^ 15) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 1442672 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 44709187) ^ 63 = 852720 := by
        calc
          (2 : ZMod 44709187) ^ 63 = (2 : ZMod 44709187) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 31 * (2 : ZMod 44709187) ^ 31) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 852720 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 44709187) ^ 126 = 25890219 := by
        calc
          (2 : ZMod 44709187) ^ 126 = (2 : ZMod 44709187) ^ (63 + 63) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 63 * (2 : ZMod 44709187) ^ 63 := by rw [pow_add]
          _ = 25890219 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 44709187) ^ 252 = 14877534 := by
        calc
          (2 : ZMod 44709187) ^ 252 = (2 : ZMod 44709187) ^ (126 + 126) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 126 * (2 : ZMod 44709187) ^ 126 := by rw [pow_add]
          _ = 14877534 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 44709187) ^ 504 = 5896435 := by
        calc
          (2 : ZMod 44709187) ^ 504 = (2 : ZMod 44709187) ^ (252 + 252) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 252 * (2 : ZMod 44709187) ^ 252 := by rw [pow_add]
          _ = 5896435 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 44709187) ^ 1009 = 5841659 := by
        calc
          (2 : ZMod 44709187) ^ 1009 = (2 : ZMod 44709187) ^ (504 + 504 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 504 * (2 : ZMod 44709187) ^ 504) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 5841659 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 44709187) ^ 2019 = 44513452 := by
        calc
          (2 : ZMod 44709187) ^ 2019 = (2 : ZMod 44709187) ^ (1009 + 1009 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 1009 * (2 : ZMod 44709187) ^ 1009) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 44513452 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 44709187) ^ 4039 = 37543119 := by
        calc
          (2 : ZMod 44709187) ^ 4039 = (2 : ZMod 44709187) ^ (2019 + 2019 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 2019 * (2 : ZMod 44709187) ^ 2019) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 37543119 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 44709187) ^ 8079 = 10968588 := by
        calc
          (2 : ZMod 44709187) ^ 8079 = (2 : ZMod 44709187) ^ (4039 + 4039 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = ((2 : ZMod 44709187) ^ 4039 * (2 : ZMod 44709187) ^ 4039) * (2 : ZMod 44709187) := by rw [pow_succ, pow_add]
          _ = 10968588 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 44709187) ^ 16158 = 4211216 := by
        calc
          (2 : ZMod 44709187) ^ 16158 = (2 : ZMod 44709187) ^ (8079 + 8079) :=
            congrArg (fun n : ℕ => (2 : ZMod 44709187) ^ n) (by norm_num)
          _ = (2 : ZMod 44709187) ^ 8079 * (2 : ZMod 44709187) ^ 8079 := by rw [pow_add]
          _ = 4211216 := by rw [factor_3_12]; decide
      change (2 : ZMod 44709187) ^ 16158 ≠ 1
      rw [factor_3_13]
      decide

#print axioms prime_lucas_44709187

end TotientTailPeriodKiller
end Erdos249257
