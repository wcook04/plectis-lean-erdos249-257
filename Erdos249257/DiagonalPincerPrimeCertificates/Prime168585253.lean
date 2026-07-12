import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_168585253 : Nat.Prime 168585253 := by
  apply lucas_primality 168585253 (5 : ZMod 168585253)
  ·
      have fermat_0 : (5 : ZMod 168585253) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 168585253) ^ 2 = 25 := by
        calc
          (5 : ZMod 168585253) ^ 2 = (5 : ZMod 168585253) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 1 * (5 : ZMod 168585253) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 168585253) ^ 5 = 3125 := by
        calc
          (5 : ZMod 168585253) ^ 5 = (5 : ZMod 168585253) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 2 * (5 : ZMod 168585253) ^ 2) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 168585253) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 168585253) ^ 10 = (5 : ZMod 168585253) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 5 * (5 : ZMod 168585253) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 168585253) ^ 20 = 102700549 := by
        calc
          (5 : ZMod 168585253) ^ 20 = (5 : ZMod 168585253) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 10 * (5 : ZMod 168585253) ^ 10 := by rw [pow_add]
          _ = 102700549 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 168585253) ^ 40 = 99062030 := by
        calc
          (5 : ZMod 168585253) ^ 40 = (5 : ZMod 168585253) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 20 * (5 : ZMod 168585253) ^ 20 := by rw [pow_add]
          _ = 99062030 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 168585253) ^ 80 = 81378751 := by
        calc
          (5 : ZMod 168585253) ^ 80 = (5 : ZMod 168585253) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 40 * (5 : ZMod 168585253) ^ 40 := by rw [pow_add]
          _ = 81378751 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 168585253) ^ 160 = 601095 := by
        calc
          (5 : ZMod 168585253) ^ 160 = (5 : ZMod 168585253) ^ (80 + 80) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 80 * (5 : ZMod 168585253) ^ 80 := by rw [pow_add]
          _ = 601095 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 168585253) ^ 321 = 16423977 := by
        calc
          (5 : ZMod 168585253) ^ 321 = (5 : ZMod 168585253) ^ (160 + 160 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 160 * (5 : ZMod 168585253) ^ 160) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 16423977 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 168585253) ^ 643 = 142713203 := by
        calc
          (5 : ZMod 168585253) ^ 643 = (5 : ZMod 168585253) ^ (321 + 321 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 321 * (5 : ZMod 168585253) ^ 321) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 142713203 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 168585253) ^ 1286 = 113138337 := by
        calc
          (5 : ZMod 168585253) ^ 1286 = (5 : ZMod 168585253) ^ (643 + 643) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 643 * (5 : ZMod 168585253) ^ 643 := by rw [pow_add]
          _ = 113138337 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 168585253) ^ 2572 = 34083348 := by
        calc
          (5 : ZMod 168585253) ^ 2572 = (5 : ZMod 168585253) ^ (1286 + 1286) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 1286 * (5 : ZMod 168585253) ^ 1286 := by rw [pow_add]
          _ = 34083348 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 168585253) ^ 5144 = 161995932 := by
        calc
          (5 : ZMod 168585253) ^ 5144 = (5 : ZMod 168585253) ^ (2572 + 2572) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 2572 * (5 : ZMod 168585253) ^ 2572 := by rw [pow_add]
          _ = 161995932 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 168585253) ^ 10289 = 96654455 := by
        calc
          (5 : ZMod 168585253) ^ 10289 = (5 : ZMod 168585253) ^ (5144 + 5144 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 5144 * (5 : ZMod 168585253) ^ 5144) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 96654455 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 168585253) ^ 20579 = 92556438 := by
        calc
          (5 : ZMod 168585253) ^ 20579 = (5 : ZMod 168585253) ^ (10289 + 10289 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 10289 * (5 : ZMod 168585253) ^ 10289) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 92556438 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 168585253) ^ 41158 = 24075979 := by
        calc
          (5 : ZMod 168585253) ^ 41158 = (5 : ZMod 168585253) ^ (20579 + 20579) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 20579 * (5 : ZMod 168585253) ^ 20579 := by rw [pow_add]
          _ = 24075979 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 168585253) ^ 82317 = 101747165 := by
        calc
          (5 : ZMod 168585253) ^ 82317 = (5 : ZMod 168585253) ^ (41158 + 41158 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 41158 * (5 : ZMod 168585253) ^ 41158) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 101747165 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 168585253) ^ 164634 = 9119683 := by
        calc
          (5 : ZMod 168585253) ^ 164634 = (5 : ZMod 168585253) ^ (82317 + 82317) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 82317 * (5 : ZMod 168585253) ^ 82317 := by rw [pow_add]
          _ = 9119683 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 168585253) ^ 329268 = 117987493 := by
        calc
          (5 : ZMod 168585253) ^ 329268 = (5 : ZMod 168585253) ^ (164634 + 164634) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 164634 * (5 : ZMod 168585253) ^ 164634 := by rw [pow_add]
          _ = 117987493 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 168585253) ^ 658536 = 25153142 := by
        calc
          (5 : ZMod 168585253) ^ 658536 = (5 : ZMod 168585253) ^ (329268 + 329268) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 329268 * (5 : ZMod 168585253) ^ 329268 := by rw [pow_add]
          _ = 25153142 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 168585253) ^ 1317072 = 159608271 := by
        calc
          (5 : ZMod 168585253) ^ 1317072 = (5 : ZMod 168585253) ^ (658536 + 658536) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 658536 * (5 : ZMod 168585253) ^ 658536 := by rw [pow_add]
          _ = 159608271 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 168585253) ^ 2634144 = 94700782 := by
        calc
          (5 : ZMod 168585253) ^ 2634144 = (5 : ZMod 168585253) ^ (1317072 + 1317072) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 1317072 * (5 : ZMod 168585253) ^ 1317072 := by rw [pow_add]
          _ = 94700782 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 168585253) ^ 5268289 = 60124623 := by
        calc
          (5 : ZMod 168585253) ^ 5268289 = (5 : ZMod 168585253) ^ (2634144 + 2634144 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 2634144 * (5 : ZMod 168585253) ^ 2634144) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 60124623 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 168585253) ^ 10536578 = 82518189 := by
        calc
          (5 : ZMod 168585253) ^ 10536578 = (5 : ZMod 168585253) ^ (5268289 + 5268289) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 5268289 * (5 : ZMod 168585253) ^ 5268289 := by rw [pow_add]
          _ = 82518189 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 168585253) ^ 21073156 = 88110065 := by
        calc
          (5 : ZMod 168585253) ^ 21073156 = (5 : ZMod 168585253) ^ (10536578 + 10536578) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 10536578 * (5 : ZMod 168585253) ^ 10536578 := by rw [pow_add]
          _ = 88110065 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 168585253) ^ 42146313 = 77746221 := by
        calc
          (5 : ZMod 168585253) ^ 42146313 = (5 : ZMod 168585253) ^ (21073156 + 21073156 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 21073156 * (5 : ZMod 168585253) ^ 21073156) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 77746221 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 168585253) ^ 84292626 = 168585252 := by
        calc
          (5 : ZMod 168585253) ^ 84292626 = (5 : ZMod 168585253) ^ (42146313 + 42146313) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 42146313 * (5 : ZMod 168585253) ^ 42146313 := by rw [pow_add]
          _ = 168585252 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 168585253) ^ 168585252 = 1 := by
        calc
          (5 : ZMod 168585253) ^ 168585252 = (5 : ZMod 168585253) ^ (84292626 + 84292626) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 84292626 * (5 : ZMod 168585253) ^ 84292626 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (19, 1), (67219, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (19, 1), (67219, 1)] : List FactorBlock).map factorBlockValue).prod = 168585253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 168585253) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 168585253) ^ 2 = 25 := by
        calc
          (5 : ZMod 168585253) ^ 2 = (5 : ZMod 168585253) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 1 * (5 : ZMod 168585253) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 168585253) ^ 5 = 3125 := by
        calc
          (5 : ZMod 168585253) ^ 5 = (5 : ZMod 168585253) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 2 * (5 : ZMod 168585253) ^ 2) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 168585253) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 168585253) ^ 10 = (5 : ZMod 168585253) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 5 * (5 : ZMod 168585253) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 168585253) ^ 20 = 102700549 := by
        calc
          (5 : ZMod 168585253) ^ 20 = (5 : ZMod 168585253) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 10 * (5 : ZMod 168585253) ^ 10 := by rw [pow_add]
          _ = 102700549 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 168585253) ^ 40 = 99062030 := by
        calc
          (5 : ZMod 168585253) ^ 40 = (5 : ZMod 168585253) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 20 * (5 : ZMod 168585253) ^ 20 := by rw [pow_add]
          _ = 99062030 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 168585253) ^ 80 = 81378751 := by
        calc
          (5 : ZMod 168585253) ^ 80 = (5 : ZMod 168585253) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 40 * (5 : ZMod 168585253) ^ 40 := by rw [pow_add]
          _ = 81378751 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 168585253) ^ 160 = 601095 := by
        calc
          (5 : ZMod 168585253) ^ 160 = (5 : ZMod 168585253) ^ (80 + 80) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 80 * (5 : ZMod 168585253) ^ 80 := by rw [pow_add]
          _ = 601095 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 168585253) ^ 321 = 16423977 := by
        calc
          (5 : ZMod 168585253) ^ 321 = (5 : ZMod 168585253) ^ (160 + 160 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 160 * (5 : ZMod 168585253) ^ 160) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 16423977 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 168585253) ^ 643 = 142713203 := by
        calc
          (5 : ZMod 168585253) ^ 643 = (5 : ZMod 168585253) ^ (321 + 321 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 321 * (5 : ZMod 168585253) ^ 321) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 142713203 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 168585253) ^ 1286 = 113138337 := by
        calc
          (5 : ZMod 168585253) ^ 1286 = (5 : ZMod 168585253) ^ (643 + 643) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 643 * (5 : ZMod 168585253) ^ 643 := by rw [pow_add]
          _ = 113138337 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 168585253) ^ 2572 = 34083348 := by
        calc
          (5 : ZMod 168585253) ^ 2572 = (5 : ZMod 168585253) ^ (1286 + 1286) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 1286 * (5 : ZMod 168585253) ^ 1286 := by rw [pow_add]
          _ = 34083348 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 168585253) ^ 5144 = 161995932 := by
        calc
          (5 : ZMod 168585253) ^ 5144 = (5 : ZMod 168585253) ^ (2572 + 2572) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 2572 * (5 : ZMod 168585253) ^ 2572 := by rw [pow_add]
          _ = 161995932 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 168585253) ^ 10289 = 96654455 := by
        calc
          (5 : ZMod 168585253) ^ 10289 = (5 : ZMod 168585253) ^ (5144 + 5144 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 5144 * (5 : ZMod 168585253) ^ 5144) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 96654455 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 168585253) ^ 20579 = 92556438 := by
        calc
          (5 : ZMod 168585253) ^ 20579 = (5 : ZMod 168585253) ^ (10289 + 10289 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 10289 * (5 : ZMod 168585253) ^ 10289) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 92556438 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 168585253) ^ 41158 = 24075979 := by
        calc
          (5 : ZMod 168585253) ^ 41158 = (5 : ZMod 168585253) ^ (20579 + 20579) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 20579 * (5 : ZMod 168585253) ^ 20579 := by rw [pow_add]
          _ = 24075979 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 168585253) ^ 82317 = 101747165 := by
        calc
          (5 : ZMod 168585253) ^ 82317 = (5 : ZMod 168585253) ^ (41158 + 41158 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 41158 * (5 : ZMod 168585253) ^ 41158) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 101747165 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 168585253) ^ 164634 = 9119683 := by
        calc
          (5 : ZMod 168585253) ^ 164634 = (5 : ZMod 168585253) ^ (82317 + 82317) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 82317 * (5 : ZMod 168585253) ^ 82317 := by rw [pow_add]
          _ = 9119683 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 168585253) ^ 329268 = 117987493 := by
        calc
          (5 : ZMod 168585253) ^ 329268 = (5 : ZMod 168585253) ^ (164634 + 164634) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 164634 * (5 : ZMod 168585253) ^ 164634 := by rw [pow_add]
          _ = 117987493 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 168585253) ^ 658536 = 25153142 := by
        calc
          (5 : ZMod 168585253) ^ 658536 = (5 : ZMod 168585253) ^ (329268 + 329268) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 329268 * (5 : ZMod 168585253) ^ 329268 := by rw [pow_add]
          _ = 25153142 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 168585253) ^ 1317072 = 159608271 := by
        calc
          (5 : ZMod 168585253) ^ 1317072 = (5 : ZMod 168585253) ^ (658536 + 658536) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 658536 * (5 : ZMod 168585253) ^ 658536 := by rw [pow_add]
          _ = 159608271 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 168585253) ^ 2634144 = 94700782 := by
        calc
          (5 : ZMod 168585253) ^ 2634144 = (5 : ZMod 168585253) ^ (1317072 + 1317072) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 1317072 * (5 : ZMod 168585253) ^ 1317072 := by rw [pow_add]
          _ = 94700782 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 168585253) ^ 5268289 = 60124623 := by
        calc
          (5 : ZMod 168585253) ^ 5268289 = (5 : ZMod 168585253) ^ (2634144 + 2634144 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 2634144 * (5 : ZMod 168585253) ^ 2634144) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 60124623 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 168585253) ^ 10536578 = 82518189 := by
        calc
          (5 : ZMod 168585253) ^ 10536578 = (5 : ZMod 168585253) ^ (5268289 + 5268289) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 5268289 * (5 : ZMod 168585253) ^ 5268289 := by rw [pow_add]
          _ = 82518189 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 168585253) ^ 21073156 = 88110065 := by
        calc
          (5 : ZMod 168585253) ^ 21073156 = (5 : ZMod 168585253) ^ (10536578 + 10536578) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 10536578 * (5 : ZMod 168585253) ^ 10536578 := by rw [pow_add]
          _ = 88110065 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 168585253) ^ 42146313 = 77746221 := by
        calc
          (5 : ZMod 168585253) ^ 42146313 = (5 : ZMod 168585253) ^ (21073156 + 21073156 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 21073156 * (5 : ZMod 168585253) ^ 21073156) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 77746221 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 168585253) ^ 84292626 = 168585252 := by
        calc
          (5 : ZMod 168585253) ^ 84292626 = (5 : ZMod 168585253) ^ (42146313 + 42146313) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 42146313 * (5 : ZMod 168585253) ^ 42146313 := by rw [pow_add]
          _ = 168585252 := by rw [factor_0_25]; decide
      change (5 : ZMod 168585253) ^ 84292626 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (5 : ZMod 168585253) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 168585253) ^ 3 = 125 := by
        calc
          (5 : ZMod 168585253) ^ 3 = (5 : ZMod 168585253) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 1 * (5 : ZMod 168585253) ^ 1) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 168585253) ^ 6 = 15625 := by
        calc
          (5 : ZMod 168585253) ^ 6 = (5 : ZMod 168585253) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 3 * (5 : ZMod 168585253) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 168585253) ^ 13 = 40606354 := by
        calc
          (5 : ZMod 168585253) ^ 13 = (5 : ZMod 168585253) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 6 * (5 : ZMod 168585253) ^ 6) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 40606354 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 168585253) ^ 26 = 101640071 := by
        calc
          (5 : ZMod 168585253) ^ 26 = (5 : ZMod 168585253) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 13 * (5 : ZMod 168585253) ^ 13 := by rw [pow_add]
          _ = 101640071 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 168585253) ^ 53 = 41628025 := by
        calc
          (5 : ZMod 168585253) ^ 53 = (5 : ZMod 168585253) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 26 * (5 : ZMod 168585253) ^ 26) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 41628025 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 168585253) ^ 107 = 152888464 := by
        calc
          (5 : ZMod 168585253) ^ 107 = (5 : ZMod 168585253) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 53 * (5 : ZMod 168585253) ^ 53) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 152888464 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 168585253) ^ 214 = 151798491 := by
        calc
          (5 : ZMod 168585253) ^ 214 = (5 : ZMod 168585253) ^ (107 + 107) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 107 * (5 : ZMod 168585253) ^ 107 := by rw [pow_add]
          _ = 151798491 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 168585253) ^ 428 = 70497554 := by
        calc
          (5 : ZMod 168585253) ^ 428 = (5 : ZMod 168585253) ^ (214 + 214) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 214 * (5 : ZMod 168585253) ^ 214 := by rw [pow_add]
          _ = 70497554 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 168585253) ^ 857 = 134290777 := by
        calc
          (5 : ZMod 168585253) ^ 857 = (5 : ZMod 168585253) ^ (428 + 428 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 428 * (5 : ZMod 168585253) ^ 428) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 134290777 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 168585253) ^ 1714 = 5666002 := by
        calc
          (5 : ZMod 168585253) ^ 1714 = (5 : ZMod 168585253) ^ (857 + 857) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 857 * (5 : ZMod 168585253) ^ 857 := by rw [pow_add]
          _ = 5666002 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 168585253) ^ 3429 = 119017082 := by
        calc
          (5 : ZMod 168585253) ^ 3429 = (5 : ZMod 168585253) ^ (1714 + 1714 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 1714 * (5 : ZMod 168585253) ^ 1714) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 119017082 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 168585253) ^ 6859 = 100920461 := by
        calc
          (5 : ZMod 168585253) ^ 6859 = (5 : ZMod 168585253) ^ (3429 + 3429 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 3429 * (5 : ZMod 168585253) ^ 3429) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 100920461 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 168585253) ^ 13719 = 164847941 := by
        calc
          (5 : ZMod 168585253) ^ 13719 = (5 : ZMod 168585253) ^ (6859 + 6859 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 6859 * (5 : ZMod 168585253) ^ 6859) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 164847941 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 168585253) ^ 27439 = 52359952 := by
        calc
          (5 : ZMod 168585253) ^ 27439 = (5 : ZMod 168585253) ^ (13719 + 13719 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 13719 * (5 : ZMod 168585253) ^ 13719) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 52359952 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 168585253) ^ 54878 = 884499 := by
        calc
          (5 : ZMod 168585253) ^ 54878 = (5 : ZMod 168585253) ^ (27439 + 27439) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 27439 * (5 : ZMod 168585253) ^ 27439 := by rw [pow_add]
          _ = 884499 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 168585253) ^ 109756 = 102907081 := by
        calc
          (5 : ZMod 168585253) ^ 109756 = (5 : ZMod 168585253) ^ (54878 + 54878) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 54878 * (5 : ZMod 168585253) ^ 54878 := by rw [pow_add]
          _ = 102907081 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 168585253) ^ 219512 = 51893526 := by
        calc
          (5 : ZMod 168585253) ^ 219512 = (5 : ZMod 168585253) ^ (109756 + 109756) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 109756 * (5 : ZMod 168585253) ^ 109756 := by rw [pow_add]
          _ = 51893526 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 168585253) ^ 439024 = 29944938 := by
        calc
          (5 : ZMod 168585253) ^ 439024 = (5 : ZMod 168585253) ^ (219512 + 219512) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 219512 * (5 : ZMod 168585253) ^ 219512 := by rw [pow_add]
          _ = 29944938 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 168585253) ^ 878048 = 83015446 := by
        calc
          (5 : ZMod 168585253) ^ 878048 = (5 : ZMod 168585253) ^ (439024 + 439024) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 439024 * (5 : ZMod 168585253) ^ 439024 := by rw [pow_add]
          _ = 83015446 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 168585253) ^ 1756096 = 85560492 := by
        calc
          (5 : ZMod 168585253) ^ 1756096 = (5 : ZMod 168585253) ^ (878048 + 878048) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 878048 * (5 : ZMod 168585253) ^ 878048 := by rw [pow_add]
          _ = 85560492 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 168585253) ^ 3512192 = 148977675 := by
        calc
          (5 : ZMod 168585253) ^ 3512192 = (5 : ZMod 168585253) ^ (1756096 + 1756096) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 1756096 * (5 : ZMod 168585253) ^ 1756096 := by rw [pow_add]
          _ = 148977675 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 168585253) ^ 7024385 = 151304811 := by
        calc
          (5 : ZMod 168585253) ^ 7024385 = (5 : ZMod 168585253) ^ (3512192 + 3512192 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 3512192 * (5 : ZMod 168585253) ^ 3512192) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 151304811 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 168585253) ^ 14048771 = 165962946 := by
        calc
          (5 : ZMod 168585253) ^ 14048771 = (5 : ZMod 168585253) ^ (7024385 + 7024385 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 7024385 * (5 : ZMod 168585253) ^ 7024385) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 165962946 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 168585253) ^ 28097542 = 70117632 := by
        calc
          (5 : ZMod 168585253) ^ 28097542 = (5 : ZMod 168585253) ^ (14048771 + 14048771) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 14048771 * (5 : ZMod 168585253) ^ 14048771 := by rw [pow_add]
          _ = 70117632 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 168585253) ^ 56195084 = 70117631 := by
        calc
          (5 : ZMod 168585253) ^ 56195084 = (5 : ZMod 168585253) ^ (28097542 + 28097542) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 28097542 * (5 : ZMod 168585253) ^ 28097542 := by rw [pow_add]
          _ = 70117631 := by rw [factor_1_24]; decide
      change (5 : ZMod 168585253) ^ 56195084 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (5 : ZMod 168585253) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 168585253) ^ 3 = 125 := by
        calc
          (5 : ZMod 168585253) ^ 3 = (5 : ZMod 168585253) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 1 * (5 : ZMod 168585253) ^ 1) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 168585253) ^ 7 = 78125 := by
        calc
          (5 : ZMod 168585253) ^ 7 = (5 : ZMod 168585253) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 3 * (5 : ZMod 168585253) ^ 3) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 168585253) ^ 14 = 34446517 := by
        calc
          (5 : ZMod 168585253) ^ 14 = (5 : ZMod 168585253) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 7 * (5 : ZMod 168585253) ^ 7 := by rw [pow_add]
          _ = 34446517 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 168585253) ^ 29 = 61114900 := by
        calc
          (5 : ZMod 168585253) ^ 29 = (5 : ZMod 168585253) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 14 * (5 : ZMod 168585253) ^ 14) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 61114900 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 168585253) ^ 58 = 108348062 := by
        calc
          (5 : ZMod 168585253) ^ 58 = (5 : ZMod 168585253) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 29 * (5 : ZMod 168585253) ^ 29 := by rw [pow_add]
          _ = 108348062 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 168585253) ^ 116 = 111583437 := by
        calc
          (5 : ZMod 168585253) ^ 116 = (5 : ZMod 168585253) ^ (58 + 58) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 58 * (5 : ZMod 168585253) ^ 58 := by rw [pow_add]
          _ = 111583437 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 168585253) ^ 233 = 122283387 := by
        calc
          (5 : ZMod 168585253) ^ 233 = (5 : ZMod 168585253) ^ (116 + 116 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 116 * (5 : ZMod 168585253) ^ 116) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 122283387 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 168585253) ^ 467 = 38113972 := by
        calc
          (5 : ZMod 168585253) ^ 467 = (5 : ZMod 168585253) ^ (233 + 233 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 233 * (5 : ZMod 168585253) ^ 233) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 38113972 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 168585253) ^ 935 = 63961080 := by
        calc
          (5 : ZMod 168585253) ^ 935 = (5 : ZMod 168585253) ^ (467 + 467 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 467 * (5 : ZMod 168585253) ^ 467) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 63961080 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 168585253) ^ 1870 = 26238337 := by
        calc
          (5 : ZMod 168585253) ^ 1870 = (5 : ZMod 168585253) ^ (935 + 935) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 935 * (5 : ZMod 168585253) ^ 935 := by rw [pow_add]
          _ = 26238337 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 168585253) ^ 3741 = 60486959 := by
        calc
          (5 : ZMod 168585253) ^ 3741 = (5 : ZMod 168585253) ^ (1870 + 1870 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 1870 * (5 : ZMod 168585253) ^ 1870) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 60486959 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 168585253) ^ 7483 = 82230538 := by
        calc
          (5 : ZMod 168585253) ^ 7483 = (5 : ZMod 168585253) ^ (3741 + 3741 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 3741 * (5 : ZMod 168585253) ^ 3741) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 82230538 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 168585253) ^ 14966 = 109584353 := by
        calc
          (5 : ZMod 168585253) ^ 14966 = (5 : ZMod 168585253) ^ (7483 + 7483) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 7483 * (5 : ZMod 168585253) ^ 7483 := by rw [pow_add]
          _ = 109584353 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 168585253) ^ 29933 = 168175454 := by
        calc
          (5 : ZMod 168585253) ^ 29933 = (5 : ZMod 168585253) ^ (14966 + 14966 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 14966 * (5 : ZMod 168585253) ^ 14966) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 168175454 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 168585253) ^ 59866 = 24308413 := by
        calc
          (5 : ZMod 168585253) ^ 59866 = (5 : ZMod 168585253) ^ (29933 + 29933) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 29933 * (5 : ZMod 168585253) ^ 29933 := by rw [pow_add]
          _ = 24308413 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 168585253) ^ 119733 = 53800667 := by
        calc
          (5 : ZMod 168585253) ^ 119733 = (5 : ZMod 168585253) ^ (59866 + 59866 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 59866 * (5 : ZMod 168585253) ^ 59866) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 53800667 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 168585253) ^ 239467 = 66532579 := by
        calc
          (5 : ZMod 168585253) ^ 239467 = (5 : ZMod 168585253) ^ (119733 + 119733 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 119733 * (5 : ZMod 168585253) ^ 119733) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 66532579 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 168585253) ^ 478935 = 65013051 := by
        calc
          (5 : ZMod 168585253) ^ 478935 = (5 : ZMod 168585253) ^ (239467 + 239467 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 239467 * (5 : ZMod 168585253) ^ 239467) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 65013051 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 168585253) ^ 957870 = 165941897 := by
        calc
          (5 : ZMod 168585253) ^ 957870 = (5 : ZMod 168585253) ^ (478935 + 478935) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 478935 * (5 : ZMod 168585253) ^ 478935 := by rw [pow_add]
          _ = 165941897 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 168585253) ^ 1915741 = 58393478 := by
        calc
          (5 : ZMod 168585253) ^ 1915741 = (5 : ZMod 168585253) ^ (957870 + 957870 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 957870 * (5 : ZMod 168585253) ^ 957870) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 58393478 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 168585253) ^ 3831483 = 131695550 := by
        calc
          (5 : ZMod 168585253) ^ 3831483 = (5 : ZMod 168585253) ^ (1915741 + 1915741 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 1915741 * (5 : ZMod 168585253) ^ 1915741) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 131695550 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 168585253) ^ 7662966 = 17037175 := by
        calc
          (5 : ZMod 168585253) ^ 7662966 = (5 : ZMod 168585253) ^ (3831483 + 3831483) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 3831483 * (5 : ZMod 168585253) ^ 3831483 := by rw [pow_add]
          _ = 17037175 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 168585253) ^ 15325932 = 132337562 := by
        calc
          (5 : ZMod 168585253) ^ 15325932 = (5 : ZMod 168585253) ^ (7662966 + 7662966) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 7662966 * (5 : ZMod 168585253) ^ 7662966 := by rw [pow_add]
          _ = 132337562 := by rw [factor_2_22]; decide
      change (5 : ZMod 168585253) ^ 15325932 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (5 : ZMod 168585253) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 168585253) ^ 2 = 25 := by
        calc
          (5 : ZMod 168585253) ^ 2 = (5 : ZMod 168585253) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 1 * (5 : ZMod 168585253) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 168585253) ^ 4 = 625 := by
        calc
          (5 : ZMod 168585253) ^ 4 = (5 : ZMod 168585253) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 2 * (5 : ZMod 168585253) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 168585253) ^ 8 = 390625 := by
        calc
          (5 : ZMod 168585253) ^ 8 = (5 : ZMod 168585253) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 4 * (5 : ZMod 168585253) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 168585253) ^ 16 = 18236660 := by
        calc
          (5 : ZMod 168585253) ^ 16 = (5 : ZMod 168585253) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 8 * (5 : ZMod 168585253) ^ 8 := by rw [pow_add]
          _ = 18236660 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 168585253) ^ 33 = 96545322 := by
        calc
          (5 : ZMod 168585253) ^ 33 = (5 : ZMod 168585253) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 16 * (5 : ZMod 168585253) ^ 16) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 96545322 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 168585253) ^ 67 = 164009741 := by
        calc
          (5 : ZMod 168585253) ^ 67 = (5 : ZMod 168585253) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 33 * (5 : ZMod 168585253) ^ 33) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 164009741 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 168585253) ^ 135 = 112285237 := by
        calc
          (5 : ZMod 168585253) ^ 135 = (5 : ZMod 168585253) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 67 * (5 : ZMod 168585253) ^ 67) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 112285237 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 168585253) ^ 270 = 90076614 := by
        calc
          (5 : ZMod 168585253) ^ 270 = (5 : ZMod 168585253) ^ (135 + 135) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 135 * (5 : ZMod 168585253) ^ 135 := by rw [pow_add]
          _ = 90076614 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 168585253) ^ 541 = 35219579 := by
        calc
          (5 : ZMod 168585253) ^ 541 = (5 : ZMod 168585253) ^ (270 + 270 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 270 * (5 : ZMod 168585253) ^ 270) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 35219579 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 168585253) ^ 1083 = 62613013 := by
        calc
          (5 : ZMod 168585253) ^ 1083 = (5 : ZMod 168585253) ^ (541 + 541 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 541 * (5 : ZMod 168585253) ^ 541) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 62613013 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 168585253) ^ 2166 = 29114249 := by
        calc
          (5 : ZMod 168585253) ^ 2166 = (5 : ZMod 168585253) ^ (1083 + 1083) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 1083 * (5 : ZMod 168585253) ^ 1083 := by rw [pow_add]
          _ = 29114249 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 168585253) ^ 4332 = 91915880 := by
        calc
          (5 : ZMod 168585253) ^ 4332 = (5 : ZMod 168585253) ^ (2166 + 2166) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 2166 * (5 : ZMod 168585253) ^ 2166 := by rw [pow_add]
          _ = 91915880 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 168585253) ^ 8664 = 86291054 := by
        calc
          (5 : ZMod 168585253) ^ 8664 = (5 : ZMod 168585253) ^ (4332 + 4332) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 4332 * (5 : ZMod 168585253) ^ 4332 := by rw [pow_add]
          _ = 86291054 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 168585253) ^ 17329 = 102755377 := by
        calc
          (5 : ZMod 168585253) ^ 17329 = (5 : ZMod 168585253) ^ (8664 + 8664 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 8664 * (5 : ZMod 168585253) ^ 8664) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 102755377 := by rw [factor_3_13]; decide
      have factor_3_15 : (5 : ZMod 168585253) ^ 34659 = 18421743 := by
        calc
          (5 : ZMod 168585253) ^ 34659 = (5 : ZMod 168585253) ^ (17329 + 17329 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 17329 * (5 : ZMod 168585253) ^ 17329) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 18421743 := by rw [factor_3_14]; decide
      have factor_3_16 : (5 : ZMod 168585253) ^ 69319 = 90681630 := by
        calc
          (5 : ZMod 168585253) ^ 69319 = (5 : ZMod 168585253) ^ (34659 + 34659 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 34659 * (5 : ZMod 168585253) ^ 34659) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 90681630 := by rw [factor_3_15]; decide
      have factor_3_17 : (5 : ZMod 168585253) ^ 138639 = 61435816 := by
        calc
          (5 : ZMod 168585253) ^ 138639 = (5 : ZMod 168585253) ^ (69319 + 69319 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 69319 * (5 : ZMod 168585253) ^ 69319) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 61435816 := by rw [factor_3_16]; decide
      have factor_3_18 : (5 : ZMod 168585253) ^ 277278 = 14592560 := by
        calc
          (5 : ZMod 168585253) ^ 277278 = (5 : ZMod 168585253) ^ (138639 + 138639) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 138639 * (5 : ZMod 168585253) ^ 138639 := by rw [pow_add]
          _ = 14592560 := by rw [factor_3_17]; decide
      have factor_3_19 : (5 : ZMod 168585253) ^ 554556 = 76925252 := by
        calc
          (5 : ZMod 168585253) ^ 554556 = (5 : ZMod 168585253) ^ (277278 + 277278) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 277278 * (5 : ZMod 168585253) ^ 277278 := by rw [pow_add]
          _ = 76925252 := by rw [factor_3_18]; decide
      have factor_3_20 : (5 : ZMod 168585253) ^ 1109113 = 92496996 := by
        calc
          (5 : ZMod 168585253) ^ 1109113 = (5 : ZMod 168585253) ^ (554556 + 554556 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 554556 * (5 : ZMod 168585253) ^ 554556) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 92496996 := by rw [factor_3_19]; decide
      have factor_3_21 : (5 : ZMod 168585253) ^ 2218227 = 147955234 := by
        calc
          (5 : ZMod 168585253) ^ 2218227 = (5 : ZMod 168585253) ^ (1109113 + 1109113 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 1109113 * (5 : ZMod 168585253) ^ 1109113) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 147955234 := by rw [factor_3_20]; decide
      have factor_3_22 : (5 : ZMod 168585253) ^ 4436454 = 166695789 := by
        calc
          (5 : ZMod 168585253) ^ 4436454 = (5 : ZMod 168585253) ^ (2218227 + 2218227) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 2218227 * (5 : ZMod 168585253) ^ 2218227 := by rw [pow_add]
          _ = 166695789 := by rw [factor_3_21]; decide
      have factor_3_23 : (5 : ZMod 168585253) ^ 8872908 = 112889768 := by
        calc
          (5 : ZMod 168585253) ^ 8872908 = (5 : ZMod 168585253) ^ (4436454 + 4436454) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 4436454 * (5 : ZMod 168585253) ^ 4436454 := by rw [pow_add]
          _ = 112889768 := by rw [factor_3_22]; decide
      change (5 : ZMod 168585253) ^ 8872908 ≠ 1
      rw [factor_3_23]
      decide
    ·
      have factor_4_0 : (5 : ZMod 168585253) ^ 1 = 5 := by norm_num
      have factor_4_1 : (5 : ZMod 168585253) ^ 2 = 25 := by
        calc
          (5 : ZMod 168585253) ^ 2 = (5 : ZMod 168585253) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 1 * (5 : ZMod 168585253) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_4_0]; decide
      have factor_4_2 : (5 : ZMod 168585253) ^ 4 = 625 := by
        calc
          (5 : ZMod 168585253) ^ 4 = (5 : ZMod 168585253) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 2 * (5 : ZMod 168585253) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_4_1]; decide
      have factor_4_3 : (5 : ZMod 168585253) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 168585253) ^ 9 = (5 : ZMod 168585253) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 4 * (5 : ZMod 168585253) ^ 4) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [factor_4_2]; decide
      have factor_4_4 : (5 : ZMod 168585253) ^ 19 = 87974211 := by
        calc
          (5 : ZMod 168585253) ^ 19 = (5 : ZMod 168585253) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 9 * (5 : ZMod 168585253) ^ 9) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 87974211 := by rw [factor_4_3]; decide
      have factor_4_5 : (5 : ZMod 168585253) ^ 39 = 19812406 := by
        calc
          (5 : ZMod 168585253) ^ 39 = (5 : ZMod 168585253) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 19 * (5 : ZMod 168585253) ^ 19) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 19812406 := by rw [factor_4_4]; decide
      have factor_4_6 : (5 : ZMod 168585253) ^ 78 = 57202431 := by
        calc
          (5 : ZMod 168585253) ^ 78 = (5 : ZMod 168585253) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 39 * (5 : ZMod 168585253) ^ 39 := by rw [pow_add]
          _ = 57202431 := by rw [factor_4_5]; decide
      have factor_4_7 : (5 : ZMod 168585253) ^ 156 = 70132427 := by
        calc
          (5 : ZMod 168585253) ^ 156 = (5 : ZMod 168585253) ^ (78 + 78) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 78 * (5 : ZMod 168585253) ^ 78 := by rw [pow_add]
          _ = 70132427 := by rw [factor_4_6]; decide
      have factor_4_8 : (5 : ZMod 168585253) ^ 313 = 106477301 := by
        calc
          (5 : ZMod 168585253) ^ 313 = (5 : ZMod 168585253) ^ (156 + 156 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 156 * (5 : ZMod 168585253) ^ 156) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 106477301 := by rw [factor_4_7]; decide
      have factor_4_9 : (5 : ZMod 168585253) ^ 627 = 56457652 := by
        calc
          (5 : ZMod 168585253) ^ 627 = (5 : ZMod 168585253) ^ (313 + 313 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = ((5 : ZMod 168585253) ^ 313 * (5 : ZMod 168585253) ^ 313) * (5 : ZMod 168585253) := by rw [pow_succ, pow_add]
          _ = 56457652 := by rw [factor_4_8]; decide
      have factor_4_10 : (5 : ZMod 168585253) ^ 1254 = 140264660 := by
        calc
          (5 : ZMod 168585253) ^ 1254 = (5 : ZMod 168585253) ^ (627 + 627) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 627 * (5 : ZMod 168585253) ^ 627 := by rw [pow_add]
          _ = 140264660 := by rw [factor_4_9]; decide
      have factor_4_11 : (5 : ZMod 168585253) ^ 2508 = 14341692 := by
        calc
          (5 : ZMod 168585253) ^ 2508 = (5 : ZMod 168585253) ^ (1254 + 1254) :=
            congrArg (fun n : ℕ => (5 : ZMod 168585253) ^ n) (by norm_num)
          _ = (5 : ZMod 168585253) ^ 1254 * (5 : ZMod 168585253) ^ 1254 := by rw [pow_add]
          _ = 14341692 := by rw [factor_4_10]; decide
      change (5 : ZMod 168585253) ^ 2508 ≠ 1
      rw [factor_4_11]
      decide

#print axioms prime_lucas_168585253

end TotientTailPeriodKiller
end Erdos249257
