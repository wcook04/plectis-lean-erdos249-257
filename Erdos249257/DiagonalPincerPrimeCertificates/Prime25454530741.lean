import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_25454530741 : Nat.Prime 25454530741 := by
  apply lucas_primality 25454530741 (10 : ZMod 25454530741)
  ·
      have fermat_0 : (10 : ZMod 25454530741) ^ 1 = 10 := by norm_num
      have fermat_1 : (10 : ZMod 25454530741) ^ 2 = 100 := by
        calc
          (10 : ZMod 25454530741) ^ 2 = (10 : ZMod 25454530741) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 1 * (10 : ZMod 25454530741) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [fermat_0]; decide
      have fermat_2 : (10 : ZMod 25454530741) ^ 5 = 100000 := by
        calc
          (10 : ZMod 25454530741) ^ 5 = (10 : ZMod 25454530741) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 2 * (10 : ZMod 25454530741) ^ 2) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 100000 := by rw [fermat_1]; decide
      have fermat_3 : (10 : ZMod 25454530741) ^ 11 = 23636407777 := by
        calc
          (10 : ZMod 25454530741) ^ 11 = (10 : ZMod 25454530741) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 5 * (10 : ZMod 25454530741) ^ 5) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 23636407777 := by rw [fermat_2]; decide
      have fermat_4 : (10 : ZMod 25454530741) ^ 23 = 7697844967 := by
        calc
          (10 : ZMod 25454530741) ^ 23 = (10 : ZMod 25454530741) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 11 * (10 : ZMod 25454530741) ^ 11) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 7697844967 := by rw [fermat_3]; decide
      have fermat_5 : (10 : ZMod 25454530741) ^ 47 = 3320178619 := by
        calc
          (10 : ZMod 25454530741) ^ 47 = (10 : ZMod 25454530741) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 23 * (10 : ZMod 25454530741) ^ 23) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 3320178619 := by rw [fermat_4]; decide
      have fermat_6 : (10 : ZMod 25454530741) ^ 94 = 19510037979 := by
        calc
          (10 : ZMod 25454530741) ^ 94 = (10 : ZMod 25454530741) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 47 * (10 : ZMod 25454530741) ^ 47 := by rw [pow_add]
          _ = 19510037979 := by rw [fermat_5]; decide
      have fermat_7 : (10 : ZMod 25454530741) ^ 189 = 1279462358 := by
        calc
          (10 : ZMod 25454530741) ^ 189 = (10 : ZMod 25454530741) ^ (94 + 94 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 94 * (10 : ZMod 25454530741) ^ 94) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 1279462358 := by rw [fermat_6]; decide
      have fermat_8 : (10 : ZMod 25454530741) ^ 379 = 23373679107 := by
        calc
          (10 : ZMod 25454530741) ^ 379 = (10 : ZMod 25454530741) ^ (189 + 189 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 189 * (10 : ZMod 25454530741) ^ 189) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 23373679107 := by rw [fermat_7]; decide
      have fermat_9 : (10 : ZMod 25454530741) ^ 758 = 11022988654 := by
        calc
          (10 : ZMod 25454530741) ^ 758 = (10 : ZMod 25454530741) ^ (379 + 379) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 379 * (10 : ZMod 25454530741) ^ 379 := by rw [pow_add]
          _ = 11022988654 := by rw [fermat_8]; decide
      have fermat_10 : (10 : ZMod 25454530741) ^ 1517 = 18789811974 := by
        calc
          (10 : ZMod 25454530741) ^ 1517 = (10 : ZMod 25454530741) ^ (758 + 758 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 758 * (10 : ZMod 25454530741) ^ 758) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 18789811974 := by rw [fermat_9]; decide
      have fermat_11 : (10 : ZMod 25454530741) ^ 3034 = 9432932214 := by
        calc
          (10 : ZMod 25454530741) ^ 3034 = (10 : ZMod 25454530741) ^ (1517 + 1517) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 1517 * (10 : ZMod 25454530741) ^ 1517 := by rw [pow_add]
          _ = 9432932214 := by rw [fermat_10]; decide
      have fermat_12 : (10 : ZMod 25454530741) ^ 6068 = 20097480243 := by
        calc
          (10 : ZMod 25454530741) ^ 6068 = (10 : ZMod 25454530741) ^ (3034 + 3034) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 3034 * (10 : ZMod 25454530741) ^ 3034 := by rw [pow_add]
          _ = 20097480243 := by rw [fermat_11]; decide
      have fermat_13 : (10 : ZMod 25454530741) ^ 12137 = 24923126032 := by
        calc
          (10 : ZMod 25454530741) ^ 12137 = (10 : ZMod 25454530741) ^ (6068 + 6068 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 6068 * (10 : ZMod 25454530741) ^ 6068) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 24923126032 := by rw [fermat_12]; decide
      have fermat_14 : (10 : ZMod 25454530741) ^ 24275 = 17967042899 := by
        calc
          (10 : ZMod 25454530741) ^ 24275 = (10 : ZMod 25454530741) ^ (12137 + 12137 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 12137 * (10 : ZMod 25454530741) ^ 12137) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 17967042899 := by rw [fermat_13]; decide
      have fermat_15 : (10 : ZMod 25454530741) ^ 48550 = 937725508 := by
        calc
          (10 : ZMod 25454530741) ^ 48550 = (10 : ZMod 25454530741) ^ (24275 + 24275) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 24275 * (10 : ZMod 25454530741) ^ 24275 := by rw [pow_add]
          _ = 937725508 := by rw [fermat_14]; decide
      have fermat_16 : (10 : ZMod 25454530741) ^ 97101 = 17255602992 := by
        calc
          (10 : ZMod 25454530741) ^ 97101 = (10 : ZMod 25454530741) ^ (48550 + 48550 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 48550 * (10 : ZMod 25454530741) ^ 48550) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 17255602992 := by rw [fermat_15]; decide
      have fermat_17 : (10 : ZMod 25454530741) ^ 194202 = 6425603477 := by
        calc
          (10 : ZMod 25454530741) ^ 194202 = (10 : ZMod 25454530741) ^ (97101 + 97101) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 97101 * (10 : ZMod 25454530741) ^ 97101 := by rw [pow_add]
          _ = 6425603477 := by rw [fermat_16]; decide
      have fermat_18 : (10 : ZMod 25454530741) ^ 388405 = 2045310077 := by
        calc
          (10 : ZMod 25454530741) ^ 388405 = (10 : ZMod 25454530741) ^ (194202 + 194202 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 194202 * (10 : ZMod 25454530741) ^ 194202) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 2045310077 := by rw [fermat_17]; decide
      have fermat_19 : (10 : ZMod 25454530741) ^ 776810 = 20066219769 := by
        calc
          (10 : ZMod 25454530741) ^ 776810 = (10 : ZMod 25454530741) ^ (388405 + 388405) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 388405 * (10 : ZMod 25454530741) ^ 388405 := by rw [pow_add]
          _ = 20066219769 := by rw [fermat_18]; decide
      have fermat_20 : (10 : ZMod 25454530741) ^ 1553621 = 7826304960 := by
        calc
          (10 : ZMod 25454530741) ^ 1553621 = (10 : ZMod 25454530741) ^ (776810 + 776810 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 776810 * (10 : ZMod 25454530741) ^ 776810) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 7826304960 := by rw [fermat_19]; decide
      have fermat_21 : (10 : ZMod 25454530741) ^ 3107242 = 12016354626 := by
        calc
          (10 : ZMod 25454530741) ^ 3107242 = (10 : ZMod 25454530741) ^ (1553621 + 1553621) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 1553621 * (10 : ZMod 25454530741) ^ 1553621 := by rw [pow_add]
          _ = 12016354626 := by rw [fermat_20]; decide
      have fermat_22 : (10 : ZMod 25454530741) ^ 6214485 = 4161034301 := by
        calc
          (10 : ZMod 25454530741) ^ 6214485 = (10 : ZMod 25454530741) ^ (3107242 + 3107242 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 3107242 * (10 : ZMod 25454530741) ^ 3107242) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 4161034301 := by rw [fermat_21]; decide
      have fermat_23 : (10 : ZMod 25454530741) ^ 12428970 = 454020100 := by
        calc
          (10 : ZMod 25454530741) ^ 12428970 = (10 : ZMod 25454530741) ^ (6214485 + 6214485) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 6214485 * (10 : ZMod 25454530741) ^ 6214485 := by rw [pow_add]
          _ = 454020100 := by rw [fermat_22]; decide
      have fermat_24 : (10 : ZMod 25454530741) ^ 24857940 = 24901741965 := by
        calc
          (10 : ZMod 25454530741) ^ 24857940 = (10 : ZMod 25454530741) ^ (12428970 + 12428970) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 12428970 * (10 : ZMod 25454530741) ^ 12428970 := by rw [pow_add]
          _ = 24901741965 := by rw [fermat_23]; decide
      have fermat_25 : (10 : ZMod 25454530741) ^ 49715880 = 231373980 := by
        calc
          (10 : ZMod 25454530741) ^ 49715880 = (10 : ZMod 25454530741) ^ (24857940 + 24857940) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 24857940 * (10 : ZMod 25454530741) ^ 24857940 := by rw [pow_add]
          _ = 231373980 := by rw [fermat_24]; decide
      have fermat_26 : (10 : ZMod 25454530741) ^ 99431760 = 11383559221 := by
        calc
          (10 : ZMod 25454530741) ^ 99431760 = (10 : ZMod 25454530741) ^ (49715880 + 49715880) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 49715880 * (10 : ZMod 25454530741) ^ 49715880 := by rw [pow_add]
          _ = 11383559221 := by rw [fermat_25]; decide
      have fermat_27 : (10 : ZMod 25454530741) ^ 198863521 = 7775584615 := by
        calc
          (10 : ZMod 25454530741) ^ 198863521 = (10 : ZMod 25454530741) ^ (99431760 + 99431760 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 99431760 * (10 : ZMod 25454530741) ^ 99431760) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 7775584615 := by rw [fermat_26]; decide
      have fermat_28 : (10 : ZMod 25454530741) ^ 397727042 = 16340510020 := by
        calc
          (10 : ZMod 25454530741) ^ 397727042 = (10 : ZMod 25454530741) ^ (198863521 + 198863521) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 198863521 * (10 : ZMod 25454530741) ^ 198863521 := by rw [pow_add]
          _ = 16340510020 := by rw [fermat_27]; decide
      have fermat_29 : (10 : ZMod 25454530741) ^ 795454085 = 2101632124 := by
        calc
          (10 : ZMod 25454530741) ^ 795454085 = (10 : ZMod 25454530741) ^ (397727042 + 397727042 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 397727042 * (10 : ZMod 25454530741) ^ 397727042) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 2101632124 := by rw [fermat_28]; decide
      have fermat_30 : (10 : ZMod 25454530741) ^ 1590908171 = 2613358746 := by
        calc
          (10 : ZMod 25454530741) ^ 1590908171 = (10 : ZMod 25454530741) ^ (795454085 + 795454085 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 795454085 * (10 : ZMod 25454530741) ^ 795454085) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 2613358746 := by rw [fermat_29]; decide
      have fermat_31 : (10 : ZMod 25454530741) ^ 3181816342 = 10323414621 := by
        calc
          (10 : ZMod 25454530741) ^ 3181816342 = (10 : ZMod 25454530741) ^ (1590908171 + 1590908171) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 1590908171 * (10 : ZMod 25454530741) ^ 1590908171 := by rw [pow_add]
          _ = 10323414621 := by rw [fermat_30]; decide
      have fermat_32 : (10 : ZMod 25454530741) ^ 6363632685 = 7587423619 := by
        calc
          (10 : ZMod 25454530741) ^ 6363632685 = (10 : ZMod 25454530741) ^ (3181816342 + 3181816342 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 3181816342 * (10 : ZMod 25454530741) ^ 3181816342) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 7587423619 := by rw [fermat_31]; decide
      have fermat_33 : (10 : ZMod 25454530741) ^ 12727265370 = 25454530740 := by
        calc
          (10 : ZMod 25454530741) ^ 12727265370 = (10 : ZMod 25454530741) ^ (6363632685 + 6363632685) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 6363632685 * (10 : ZMod 25454530741) ^ 6363632685 := by rw [pow_add]
          _ = 25454530740 := by rw [fermat_32]; decide
      have fermat_34 : (10 : ZMod 25454530741) ^ 25454530740 = 1 := by
        calc
          (10 : ZMod 25454530741) ^ 25454530740 = (10 : ZMod 25454530741) ^ (12727265370 + 12727265370) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 12727265370 * (10 : ZMod 25454530741) ^ 12727265370 := by rw [pow_add]
          _ = 1 := by rw [fermat_33]; decide
      simpa using fermat_34
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (8291, 1), (51169, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (8291, 1), (51169, 1)] : List FactorBlock).map factorBlockValue).prod = 25454530741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (10 : ZMod 25454530741) ^ 1 = 10 := by norm_num
      have factor_0_1 : (10 : ZMod 25454530741) ^ 2 = 100 := by
        calc
          (10 : ZMod 25454530741) ^ 2 = (10 : ZMod 25454530741) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 1 * (10 : ZMod 25454530741) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_0_0]; decide
      have factor_0_2 : (10 : ZMod 25454530741) ^ 5 = 100000 := by
        calc
          (10 : ZMod 25454530741) ^ 5 = (10 : ZMod 25454530741) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 2 * (10 : ZMod 25454530741) ^ 2) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 100000 := by rw [factor_0_1]; decide
      have factor_0_3 : (10 : ZMod 25454530741) ^ 11 = 23636407777 := by
        calc
          (10 : ZMod 25454530741) ^ 11 = (10 : ZMod 25454530741) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 5 * (10 : ZMod 25454530741) ^ 5) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 23636407777 := by rw [factor_0_2]; decide
      have factor_0_4 : (10 : ZMod 25454530741) ^ 23 = 7697844967 := by
        calc
          (10 : ZMod 25454530741) ^ 23 = (10 : ZMod 25454530741) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 11 * (10 : ZMod 25454530741) ^ 11) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 7697844967 := by rw [factor_0_3]; decide
      have factor_0_5 : (10 : ZMod 25454530741) ^ 47 = 3320178619 := by
        calc
          (10 : ZMod 25454530741) ^ 47 = (10 : ZMod 25454530741) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 23 * (10 : ZMod 25454530741) ^ 23) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 3320178619 := by rw [factor_0_4]; decide
      have factor_0_6 : (10 : ZMod 25454530741) ^ 94 = 19510037979 := by
        calc
          (10 : ZMod 25454530741) ^ 94 = (10 : ZMod 25454530741) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 47 * (10 : ZMod 25454530741) ^ 47 := by rw [pow_add]
          _ = 19510037979 := by rw [factor_0_5]; decide
      have factor_0_7 : (10 : ZMod 25454530741) ^ 189 = 1279462358 := by
        calc
          (10 : ZMod 25454530741) ^ 189 = (10 : ZMod 25454530741) ^ (94 + 94 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 94 * (10 : ZMod 25454530741) ^ 94) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 1279462358 := by rw [factor_0_6]; decide
      have factor_0_8 : (10 : ZMod 25454530741) ^ 379 = 23373679107 := by
        calc
          (10 : ZMod 25454530741) ^ 379 = (10 : ZMod 25454530741) ^ (189 + 189 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 189 * (10 : ZMod 25454530741) ^ 189) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 23373679107 := by rw [factor_0_7]; decide
      have factor_0_9 : (10 : ZMod 25454530741) ^ 758 = 11022988654 := by
        calc
          (10 : ZMod 25454530741) ^ 758 = (10 : ZMod 25454530741) ^ (379 + 379) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 379 * (10 : ZMod 25454530741) ^ 379 := by rw [pow_add]
          _ = 11022988654 := by rw [factor_0_8]; decide
      have factor_0_10 : (10 : ZMod 25454530741) ^ 1517 = 18789811974 := by
        calc
          (10 : ZMod 25454530741) ^ 1517 = (10 : ZMod 25454530741) ^ (758 + 758 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 758 * (10 : ZMod 25454530741) ^ 758) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 18789811974 := by rw [factor_0_9]; decide
      have factor_0_11 : (10 : ZMod 25454530741) ^ 3034 = 9432932214 := by
        calc
          (10 : ZMod 25454530741) ^ 3034 = (10 : ZMod 25454530741) ^ (1517 + 1517) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 1517 * (10 : ZMod 25454530741) ^ 1517 := by rw [pow_add]
          _ = 9432932214 := by rw [factor_0_10]; decide
      have factor_0_12 : (10 : ZMod 25454530741) ^ 6068 = 20097480243 := by
        calc
          (10 : ZMod 25454530741) ^ 6068 = (10 : ZMod 25454530741) ^ (3034 + 3034) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 3034 * (10 : ZMod 25454530741) ^ 3034 := by rw [pow_add]
          _ = 20097480243 := by rw [factor_0_11]; decide
      have factor_0_13 : (10 : ZMod 25454530741) ^ 12137 = 24923126032 := by
        calc
          (10 : ZMod 25454530741) ^ 12137 = (10 : ZMod 25454530741) ^ (6068 + 6068 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 6068 * (10 : ZMod 25454530741) ^ 6068) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 24923126032 := by rw [factor_0_12]; decide
      have factor_0_14 : (10 : ZMod 25454530741) ^ 24275 = 17967042899 := by
        calc
          (10 : ZMod 25454530741) ^ 24275 = (10 : ZMod 25454530741) ^ (12137 + 12137 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 12137 * (10 : ZMod 25454530741) ^ 12137) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 17967042899 := by rw [factor_0_13]; decide
      have factor_0_15 : (10 : ZMod 25454530741) ^ 48550 = 937725508 := by
        calc
          (10 : ZMod 25454530741) ^ 48550 = (10 : ZMod 25454530741) ^ (24275 + 24275) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 24275 * (10 : ZMod 25454530741) ^ 24275 := by rw [pow_add]
          _ = 937725508 := by rw [factor_0_14]; decide
      have factor_0_16 : (10 : ZMod 25454530741) ^ 97101 = 17255602992 := by
        calc
          (10 : ZMod 25454530741) ^ 97101 = (10 : ZMod 25454530741) ^ (48550 + 48550 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 48550 * (10 : ZMod 25454530741) ^ 48550) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 17255602992 := by rw [factor_0_15]; decide
      have factor_0_17 : (10 : ZMod 25454530741) ^ 194202 = 6425603477 := by
        calc
          (10 : ZMod 25454530741) ^ 194202 = (10 : ZMod 25454530741) ^ (97101 + 97101) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 97101 * (10 : ZMod 25454530741) ^ 97101 := by rw [pow_add]
          _ = 6425603477 := by rw [factor_0_16]; decide
      have factor_0_18 : (10 : ZMod 25454530741) ^ 388405 = 2045310077 := by
        calc
          (10 : ZMod 25454530741) ^ 388405 = (10 : ZMod 25454530741) ^ (194202 + 194202 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 194202 * (10 : ZMod 25454530741) ^ 194202) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 2045310077 := by rw [factor_0_17]; decide
      have factor_0_19 : (10 : ZMod 25454530741) ^ 776810 = 20066219769 := by
        calc
          (10 : ZMod 25454530741) ^ 776810 = (10 : ZMod 25454530741) ^ (388405 + 388405) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 388405 * (10 : ZMod 25454530741) ^ 388405 := by rw [pow_add]
          _ = 20066219769 := by rw [factor_0_18]; decide
      have factor_0_20 : (10 : ZMod 25454530741) ^ 1553621 = 7826304960 := by
        calc
          (10 : ZMod 25454530741) ^ 1553621 = (10 : ZMod 25454530741) ^ (776810 + 776810 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 776810 * (10 : ZMod 25454530741) ^ 776810) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 7826304960 := by rw [factor_0_19]; decide
      have factor_0_21 : (10 : ZMod 25454530741) ^ 3107242 = 12016354626 := by
        calc
          (10 : ZMod 25454530741) ^ 3107242 = (10 : ZMod 25454530741) ^ (1553621 + 1553621) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 1553621 * (10 : ZMod 25454530741) ^ 1553621 := by rw [pow_add]
          _ = 12016354626 := by rw [factor_0_20]; decide
      have factor_0_22 : (10 : ZMod 25454530741) ^ 6214485 = 4161034301 := by
        calc
          (10 : ZMod 25454530741) ^ 6214485 = (10 : ZMod 25454530741) ^ (3107242 + 3107242 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 3107242 * (10 : ZMod 25454530741) ^ 3107242) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 4161034301 := by rw [factor_0_21]; decide
      have factor_0_23 : (10 : ZMod 25454530741) ^ 12428970 = 454020100 := by
        calc
          (10 : ZMod 25454530741) ^ 12428970 = (10 : ZMod 25454530741) ^ (6214485 + 6214485) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 6214485 * (10 : ZMod 25454530741) ^ 6214485 := by rw [pow_add]
          _ = 454020100 := by rw [factor_0_22]; decide
      have factor_0_24 : (10 : ZMod 25454530741) ^ 24857940 = 24901741965 := by
        calc
          (10 : ZMod 25454530741) ^ 24857940 = (10 : ZMod 25454530741) ^ (12428970 + 12428970) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 12428970 * (10 : ZMod 25454530741) ^ 12428970 := by rw [pow_add]
          _ = 24901741965 := by rw [factor_0_23]; decide
      have factor_0_25 : (10 : ZMod 25454530741) ^ 49715880 = 231373980 := by
        calc
          (10 : ZMod 25454530741) ^ 49715880 = (10 : ZMod 25454530741) ^ (24857940 + 24857940) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 24857940 * (10 : ZMod 25454530741) ^ 24857940 := by rw [pow_add]
          _ = 231373980 := by rw [factor_0_24]; decide
      have factor_0_26 : (10 : ZMod 25454530741) ^ 99431760 = 11383559221 := by
        calc
          (10 : ZMod 25454530741) ^ 99431760 = (10 : ZMod 25454530741) ^ (49715880 + 49715880) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 49715880 * (10 : ZMod 25454530741) ^ 49715880 := by rw [pow_add]
          _ = 11383559221 := by rw [factor_0_25]; decide
      have factor_0_27 : (10 : ZMod 25454530741) ^ 198863521 = 7775584615 := by
        calc
          (10 : ZMod 25454530741) ^ 198863521 = (10 : ZMod 25454530741) ^ (99431760 + 99431760 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 99431760 * (10 : ZMod 25454530741) ^ 99431760) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 7775584615 := by rw [factor_0_26]; decide
      have factor_0_28 : (10 : ZMod 25454530741) ^ 397727042 = 16340510020 := by
        calc
          (10 : ZMod 25454530741) ^ 397727042 = (10 : ZMod 25454530741) ^ (198863521 + 198863521) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 198863521 * (10 : ZMod 25454530741) ^ 198863521 := by rw [pow_add]
          _ = 16340510020 := by rw [factor_0_27]; decide
      have factor_0_29 : (10 : ZMod 25454530741) ^ 795454085 = 2101632124 := by
        calc
          (10 : ZMod 25454530741) ^ 795454085 = (10 : ZMod 25454530741) ^ (397727042 + 397727042 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 397727042 * (10 : ZMod 25454530741) ^ 397727042) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 2101632124 := by rw [factor_0_28]; decide
      have factor_0_30 : (10 : ZMod 25454530741) ^ 1590908171 = 2613358746 := by
        calc
          (10 : ZMod 25454530741) ^ 1590908171 = (10 : ZMod 25454530741) ^ (795454085 + 795454085 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 795454085 * (10 : ZMod 25454530741) ^ 795454085) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 2613358746 := by rw [factor_0_29]; decide
      have factor_0_31 : (10 : ZMod 25454530741) ^ 3181816342 = 10323414621 := by
        calc
          (10 : ZMod 25454530741) ^ 3181816342 = (10 : ZMod 25454530741) ^ (1590908171 + 1590908171) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 1590908171 * (10 : ZMod 25454530741) ^ 1590908171 := by rw [pow_add]
          _ = 10323414621 := by rw [factor_0_30]; decide
      have factor_0_32 : (10 : ZMod 25454530741) ^ 6363632685 = 7587423619 := by
        calc
          (10 : ZMod 25454530741) ^ 6363632685 = (10 : ZMod 25454530741) ^ (3181816342 + 3181816342 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 3181816342 * (10 : ZMod 25454530741) ^ 3181816342) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 7587423619 := by rw [factor_0_31]; decide
      have factor_0_33 : (10 : ZMod 25454530741) ^ 12727265370 = 25454530740 := by
        calc
          (10 : ZMod 25454530741) ^ 12727265370 = (10 : ZMod 25454530741) ^ (6363632685 + 6363632685) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 6363632685 * (10 : ZMod 25454530741) ^ 6363632685 := by rw [pow_add]
          _ = 25454530740 := by rw [factor_0_32]; decide
      change (10 : ZMod 25454530741) ^ 12727265370 ≠ 1
      rw [factor_0_33]
      decide
    ·
      have factor_1_0 : (10 : ZMod 25454530741) ^ 1 = 10 := by norm_num
      have factor_1_1 : (10 : ZMod 25454530741) ^ 3 = 1000 := by
        calc
          (10 : ZMod 25454530741) ^ 3 = (10 : ZMod 25454530741) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 1 * (10 : ZMod 25454530741) ^ 1) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_1_0]; decide
      have factor_1_2 : (10 : ZMod 25454530741) ^ 7 = 10000000 := by
        calc
          (10 : ZMod 25454530741) ^ 7 = (10 : ZMod 25454530741) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 3 * (10 : ZMod 25454530741) ^ 3) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 10000000 := by rw [factor_1_1]; decide
      have factor_1_3 : (10 : ZMod 25454530741) ^ 15 = 18759839815 := by
        calc
          (10 : ZMod 25454530741) ^ 15 = (10 : ZMod 25454530741) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 7 * (10 : ZMod 25454530741) ^ 7) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 18759839815 := by rw [factor_1_2]; decide
      have factor_1_4 : (10 : ZMod 25454530741) ^ 31 = 7114980709 := by
        calc
          (10 : ZMod 25454530741) ^ 31 = (10 : ZMod 25454530741) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 15 * (10 : ZMod 25454530741) ^ 15) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 7114980709 := by rw [factor_1_3]; decide
      have factor_1_5 : (10 : ZMod 25454530741) ^ 63 = 24243319243 := by
        calc
          (10 : ZMod 25454530741) ^ 63 = (10 : ZMod 25454530741) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 31 * (10 : ZMod 25454530741) ^ 31) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 24243319243 := by rw [factor_1_4]; decide
      have factor_1_6 : (10 : ZMod 25454530741) ^ 126 = 2698472360 := by
        calc
          (10 : ZMod 25454530741) ^ 126 = (10 : ZMod 25454530741) ^ (63 + 63) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 63 * (10 : ZMod 25454530741) ^ 63 := by rw [pow_add]
          _ = 2698472360 := by rw [factor_1_5]; decide
      have factor_1_7 : (10 : ZMod 25454530741) ^ 252 = 6773733924 := by
        calc
          (10 : ZMod 25454530741) ^ 252 = (10 : ZMod 25454530741) ^ (126 + 126) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 126 * (10 : ZMod 25454530741) ^ 126 := by rw [pow_add]
          _ = 6773733924 := by rw [factor_1_6]; decide
      have factor_1_8 : (10 : ZMod 25454530741) ^ 505 = 3758990392 := by
        calc
          (10 : ZMod 25454530741) ^ 505 = (10 : ZMod 25454530741) ^ (252 + 252 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 252 * (10 : ZMod 25454530741) ^ 252) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 3758990392 := by rw [factor_1_7]; decide
      have factor_1_9 : (10 : ZMod 25454530741) ^ 1011 = 12977348619 := by
        calc
          (10 : ZMod 25454530741) ^ 1011 = (10 : ZMod 25454530741) ^ (505 + 505 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 505 * (10 : ZMod 25454530741) ^ 505) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 12977348619 := by rw [factor_1_8]; decide
      have factor_1_10 : (10 : ZMod 25454530741) ^ 2022 = 20967758254 := by
        calc
          (10 : ZMod 25454530741) ^ 2022 = (10 : ZMod 25454530741) ^ (1011 + 1011) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 1011 * (10 : ZMod 25454530741) ^ 1011 := by rw [pow_add]
          _ = 20967758254 := by rw [factor_1_9]; decide
      have factor_1_11 : (10 : ZMod 25454530741) ^ 4045 = 18182979386 := by
        calc
          (10 : ZMod 25454530741) ^ 4045 = (10 : ZMod 25454530741) ^ (2022 + 2022 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 2022 * (10 : ZMod 25454530741) ^ 2022) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 18182979386 := by rw [factor_1_10]; decide
      have factor_1_12 : (10 : ZMod 25454530741) ^ 8091 = 19531165191 := by
        calc
          (10 : ZMod 25454530741) ^ 8091 = (10 : ZMod 25454530741) ^ (4045 + 4045 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 4045 * (10 : ZMod 25454530741) ^ 4045) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 19531165191 := by rw [factor_1_11]; decide
      have factor_1_13 : (10 : ZMod 25454530741) ^ 16183 = 6515262436 := by
        calc
          (10 : ZMod 25454530741) ^ 16183 = (10 : ZMod 25454530741) ^ (8091 + 8091 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 8091 * (10 : ZMod 25454530741) ^ 8091) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 6515262436 := by rw [factor_1_12]; decide
      have factor_1_14 : (10 : ZMod 25454530741) ^ 32367 = 1023877621 := by
        calc
          (10 : ZMod 25454530741) ^ 32367 = (10 : ZMod 25454530741) ^ (16183 + 16183 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 16183 * (10 : ZMod 25454530741) ^ 16183) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 1023877621 := by rw [factor_1_13]; decide
      have factor_1_15 : (10 : ZMod 25454530741) ^ 64734 = 6932551506 := by
        calc
          (10 : ZMod 25454530741) ^ 64734 = (10 : ZMod 25454530741) ^ (32367 + 32367) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 32367 * (10 : ZMod 25454530741) ^ 32367 := by rw [pow_add]
          _ = 6932551506 := by rw [factor_1_14]; decide
      have factor_1_16 : (10 : ZMod 25454530741) ^ 129468 = 3739999814 := by
        calc
          (10 : ZMod 25454530741) ^ 129468 = (10 : ZMod 25454530741) ^ (64734 + 64734) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 64734 * (10 : ZMod 25454530741) ^ 64734 := by rw [pow_add]
          _ = 3739999814 := by rw [factor_1_15]; decide
      have factor_1_17 : (10 : ZMod 25454530741) ^ 258936 = 3097212676 := by
        calc
          (10 : ZMod 25454530741) ^ 258936 = (10 : ZMod 25454530741) ^ (129468 + 129468) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 129468 * (10 : ZMod 25454530741) ^ 129468 := by rw [pow_add]
          _ = 3097212676 := by rw [factor_1_16]; decide
      have factor_1_18 : (10 : ZMod 25454530741) ^ 517873 = 12824592992 := by
        calc
          (10 : ZMod 25454530741) ^ 517873 = (10 : ZMod 25454530741) ^ (258936 + 258936 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 258936 * (10 : ZMod 25454530741) ^ 258936) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 12824592992 := by rw [factor_1_17]; decide
      have factor_1_19 : (10 : ZMod 25454530741) ^ 1035747 = 2914465406 := by
        calc
          (10 : ZMod 25454530741) ^ 1035747 = (10 : ZMod 25454530741) ^ (517873 + 517873 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 517873 * (10 : ZMod 25454530741) ^ 517873) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 2914465406 := by rw [factor_1_18]; decide
      have factor_1_20 : (10 : ZMod 25454530741) ^ 2071495 = 17322883095 := by
        calc
          (10 : ZMod 25454530741) ^ 2071495 = (10 : ZMod 25454530741) ^ (1035747 + 1035747 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 1035747 * (10 : ZMod 25454530741) ^ 1035747) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 17322883095 := by rw [factor_1_19]; decide
      have factor_1_21 : (10 : ZMod 25454530741) ^ 4142990 = 13066911827 := by
        calc
          (10 : ZMod 25454530741) ^ 4142990 = (10 : ZMod 25454530741) ^ (2071495 + 2071495) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 2071495 * (10 : ZMod 25454530741) ^ 2071495 := by rw [pow_add]
          _ = 13066911827 := by rw [factor_1_20]; decide
      have factor_1_22 : (10 : ZMod 25454530741) ^ 8285980 = 4821938376 := by
        calc
          (10 : ZMod 25454530741) ^ 8285980 = (10 : ZMod 25454530741) ^ (4142990 + 4142990) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 4142990 * (10 : ZMod 25454530741) ^ 4142990 := by rw [pow_add]
          _ = 4821938376 := by rw [factor_1_21]; decide
      have factor_1_23 : (10 : ZMod 25454530741) ^ 16571960 = 21826477622 := by
        calc
          (10 : ZMod 25454530741) ^ 16571960 = (10 : ZMod 25454530741) ^ (8285980 + 8285980) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 8285980 * (10 : ZMod 25454530741) ^ 8285980 := by rw [pow_add]
          _ = 21826477622 := by rw [factor_1_22]; decide
      have factor_1_24 : (10 : ZMod 25454530741) ^ 33143920 = 2793846543 := by
        calc
          (10 : ZMod 25454530741) ^ 33143920 = (10 : ZMod 25454530741) ^ (16571960 + 16571960) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 16571960 * (10 : ZMod 25454530741) ^ 16571960 := by rw [pow_add]
          _ = 2793846543 := by rw [factor_1_23]; decide
      have factor_1_25 : (10 : ZMod 25454530741) ^ 66287840 = 6801833985 := by
        calc
          (10 : ZMod 25454530741) ^ 66287840 = (10 : ZMod 25454530741) ^ (33143920 + 33143920) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 33143920 * (10 : ZMod 25454530741) ^ 33143920 := by rw [pow_add]
          _ = 6801833985 := by rw [factor_1_24]; decide
      have factor_1_26 : (10 : ZMod 25454530741) ^ 132575680 = 7596600322 := by
        calc
          (10 : ZMod 25454530741) ^ 132575680 = (10 : ZMod 25454530741) ^ (66287840 + 66287840) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 66287840 * (10 : ZMod 25454530741) ^ 66287840 := by rw [pow_add]
          _ = 7596600322 := by rw [factor_1_25]; decide
      have factor_1_27 : (10 : ZMod 25454530741) ^ 265151361 = 7758922878 := by
        calc
          (10 : ZMod 25454530741) ^ 265151361 = (10 : ZMod 25454530741) ^ (132575680 + 132575680 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 132575680 * (10 : ZMod 25454530741) ^ 132575680) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 7758922878 := by rw [factor_1_26]; decide
      have factor_1_28 : (10 : ZMod 25454530741) ^ 530302723 = 11816644495 := by
        calc
          (10 : ZMod 25454530741) ^ 530302723 = (10 : ZMod 25454530741) ^ (265151361 + 265151361 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 265151361 * (10 : ZMod 25454530741) ^ 265151361) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 11816644495 := by rw [factor_1_27]; decide
      have factor_1_29 : (10 : ZMod 25454530741) ^ 1060605447 = 5821124267 := by
        calc
          (10 : ZMod 25454530741) ^ 1060605447 = (10 : ZMod 25454530741) ^ (530302723 + 530302723 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 530302723 * (10 : ZMod 25454530741) ^ 530302723) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 5821124267 := by rw [factor_1_28]; decide
      have factor_1_30 : (10 : ZMod 25454530741) ^ 2121210895 = 13141483441 := by
        calc
          (10 : ZMod 25454530741) ^ 2121210895 = (10 : ZMod 25454530741) ^ (1060605447 + 1060605447 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 1060605447 * (10 : ZMod 25454530741) ^ 1060605447) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 13141483441 := by rw [factor_1_29]; decide
      have factor_1_31 : (10 : ZMod 25454530741) ^ 4242421790 = 8196500152 := by
        calc
          (10 : ZMod 25454530741) ^ 4242421790 = (10 : ZMod 25454530741) ^ (2121210895 + 2121210895) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 2121210895 * (10 : ZMod 25454530741) ^ 2121210895 := by rw [pow_add]
          _ = 8196500152 := by rw [factor_1_30]; decide
      have factor_1_32 : (10 : ZMod 25454530741) ^ 8484843580 = 8196500151 := by
        calc
          (10 : ZMod 25454530741) ^ 8484843580 = (10 : ZMod 25454530741) ^ (4242421790 + 4242421790) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 4242421790 * (10 : ZMod 25454530741) ^ 4242421790 := by rw [pow_add]
          _ = 8196500151 := by rw [factor_1_31]; decide
      change (10 : ZMod 25454530741) ^ 8484843580 ≠ 1
      rw [factor_1_32]
      decide
    ·
      have factor_2_0 : (10 : ZMod 25454530741) ^ 1 = 10 := by norm_num
      have factor_2_1 : (10 : ZMod 25454530741) ^ 2 = 100 := by
        calc
          (10 : ZMod 25454530741) ^ 2 = (10 : ZMod 25454530741) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 1 * (10 : ZMod 25454530741) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_2_0]; decide
      have factor_2_2 : (10 : ZMod 25454530741) ^ 4 = 10000 := by
        calc
          (10 : ZMod 25454530741) ^ 4 = (10 : ZMod 25454530741) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 2 * (10 : ZMod 25454530741) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [factor_2_1]; decide
      have factor_2_3 : (10 : ZMod 25454530741) ^ 9 = 1000000000 := by
        calc
          (10 : ZMod 25454530741) ^ 9 = (10 : ZMod 25454530741) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 4 * (10 : ZMod 25454530741) ^ 4) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 1000000000 := by rw [factor_2_2]; decide
      have factor_2_4 : (10 : ZMod 25454530741) ^ 18 = 25305189624 := by
        calc
          (10 : ZMod 25454530741) ^ 18 = (10 : ZMod 25454530741) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 9 * (10 : ZMod 25454530741) ^ 9 := by rw [pow_add]
          _ = 25305189624 := by rw [factor_2_3]; decide
      have factor_2_5 : (10 : ZMod 25454530741) ^ 37 = 6639867903 := by
        calc
          (10 : ZMod 25454530741) ^ 37 = (10 : ZMod 25454530741) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 18 * (10 : ZMod 25454530741) ^ 18) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 6639867903 := by rw [factor_2_4]; decide
      have factor_2_6 : (10 : ZMod 25454530741) ^ 75 = 7690389055 := by
        calc
          (10 : ZMod 25454530741) ^ 75 = (10 : ZMod 25454530741) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 37 * (10 : ZMod 25454530741) ^ 37) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 7690389055 := by rw [factor_2_5]; decide
      have factor_2_7 : (10 : ZMod 25454530741) ^ 151 = 7635406009 := by
        calc
          (10 : ZMod 25454530741) ^ 151 = (10 : ZMod 25454530741) ^ (75 + 75 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 75 * (10 : ZMod 25454530741) ^ 75) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 7635406009 := by rw [factor_2_6]; decide
      have factor_2_8 : (10 : ZMod 25454530741) ^ 303 = 1433931506 := by
        calc
          (10 : ZMod 25454530741) ^ 303 = (10 : ZMod 25454530741) ^ (151 + 151 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 151 * (10 : ZMod 25454530741) ^ 151) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 1433931506 := by rw [factor_2_7]; decide
      have factor_2_9 : (10 : ZMod 25454530741) ^ 606 = 21517330473 := by
        calc
          (10 : ZMod 25454530741) ^ 606 = (10 : ZMod 25454530741) ^ (303 + 303) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 303 * (10 : ZMod 25454530741) ^ 303 := by rw [pow_add]
          _ = 21517330473 := by rw [factor_2_8]; decide
      have factor_2_10 : (10 : ZMod 25454530741) ^ 1213 = 1908198388 := by
        calc
          (10 : ZMod 25454530741) ^ 1213 = (10 : ZMod 25454530741) ^ (606 + 606 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 606 * (10 : ZMod 25454530741) ^ 606) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 1908198388 := by rw [factor_2_9]; decide
      have factor_2_11 : (10 : ZMod 25454530741) ^ 2427 = 25280236041 := by
        calc
          (10 : ZMod 25454530741) ^ 2427 = (10 : ZMod 25454530741) ^ (1213 + 1213 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 1213 * (10 : ZMod 25454530741) ^ 1213) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 25280236041 := by rw [factor_2_10]; decide
      have factor_2_12 : (10 : ZMod 25454530741) ^ 4855 = 14624765507 := by
        calc
          (10 : ZMod 25454530741) ^ 4855 = (10 : ZMod 25454530741) ^ (2427 + 2427 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 2427 * (10 : ZMod 25454530741) ^ 2427) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 14624765507 := by rw [factor_2_11]; decide
      have factor_2_13 : (10 : ZMod 25454530741) ^ 9710 = 17409172246 := by
        calc
          (10 : ZMod 25454530741) ^ 9710 = (10 : ZMod 25454530741) ^ (4855 + 4855) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 4855 * (10 : ZMod 25454530741) ^ 4855 := by rw [pow_add]
          _ = 17409172246 := by rw [factor_2_12]; decide
      have factor_2_14 : (10 : ZMod 25454530741) ^ 19420 = 7835358601 := by
        calc
          (10 : ZMod 25454530741) ^ 19420 = (10 : ZMod 25454530741) ^ (9710 + 9710) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 9710 * (10 : ZMod 25454530741) ^ 9710 := by rw [pow_add]
          _ = 7835358601 := by rw [factor_2_13]; decide
      have factor_2_15 : (10 : ZMod 25454530741) ^ 38840 = 16958951943 := by
        calc
          (10 : ZMod 25454530741) ^ 38840 = (10 : ZMod 25454530741) ^ (19420 + 19420) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 19420 * (10 : ZMod 25454530741) ^ 19420 := by rw [pow_add]
          _ = 16958951943 := by rw [factor_2_14]; decide
      have factor_2_16 : (10 : ZMod 25454530741) ^ 77681 = 760770733 := by
        calc
          (10 : ZMod 25454530741) ^ 77681 = (10 : ZMod 25454530741) ^ (38840 + 38840 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 38840 * (10 : ZMod 25454530741) ^ 38840) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 760770733 := by rw [factor_2_15]; decide
      have factor_2_17 : (10 : ZMod 25454530741) ^ 155362 = 20920238681 := by
        calc
          (10 : ZMod 25454530741) ^ 155362 = (10 : ZMod 25454530741) ^ (77681 + 77681) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 77681 * (10 : ZMod 25454530741) ^ 77681 := by rw [pow_add]
          _ = 20920238681 := by rw [factor_2_16]; decide
      have factor_2_18 : (10 : ZMod 25454530741) ^ 310724 = 16886473989 := by
        calc
          (10 : ZMod 25454530741) ^ 310724 = (10 : ZMod 25454530741) ^ (155362 + 155362) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 155362 * (10 : ZMod 25454530741) ^ 155362 := by rw [pow_add]
          _ = 16886473989 := by rw [factor_2_17]; decide
      have factor_2_19 : (10 : ZMod 25454530741) ^ 621448 = 16143383552 := by
        calc
          (10 : ZMod 25454530741) ^ 621448 = (10 : ZMod 25454530741) ^ (310724 + 310724) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 310724 * (10 : ZMod 25454530741) ^ 310724 := by rw [pow_add]
          _ = 16143383552 := by rw [factor_2_18]; decide
      have factor_2_20 : (10 : ZMod 25454530741) ^ 1242897 = 4440220238 := by
        calc
          (10 : ZMod 25454530741) ^ 1242897 = (10 : ZMod 25454530741) ^ (621448 + 621448 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 621448 * (10 : ZMod 25454530741) ^ 621448) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 4440220238 := by rw [factor_2_19]; decide
      have factor_2_21 : (10 : ZMod 25454530741) ^ 2485794 = 9085394386 := by
        calc
          (10 : ZMod 25454530741) ^ 2485794 = (10 : ZMod 25454530741) ^ (1242897 + 1242897) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 1242897 * (10 : ZMod 25454530741) ^ 1242897 := by rw [pow_add]
          _ = 9085394386 := by rw [factor_2_20]; decide
      have factor_2_22 : (10 : ZMod 25454530741) ^ 4971588 = 681011415 := by
        calc
          (10 : ZMod 25454530741) ^ 4971588 = (10 : ZMod 25454530741) ^ (2485794 + 2485794) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 2485794 * (10 : ZMod 25454530741) ^ 2485794 := by rw [pow_add]
          _ = 681011415 := by rw [factor_2_21]; decide
      have factor_2_23 : (10 : ZMod 25454530741) ^ 9943176 = 11801838202 := by
        calc
          (10 : ZMod 25454530741) ^ 9943176 = (10 : ZMod 25454530741) ^ (4971588 + 4971588) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 4971588 * (10 : ZMod 25454530741) ^ 4971588 := by rw [pow_add]
          _ = 11801838202 := by rw [factor_2_22]; decide
      have factor_2_24 : (10 : ZMod 25454530741) ^ 19886352 = 16506585656 := by
        calc
          (10 : ZMod 25454530741) ^ 19886352 = (10 : ZMod 25454530741) ^ (9943176 + 9943176) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 9943176 * (10 : ZMod 25454530741) ^ 9943176 := by rw [pow_add]
          _ = 16506585656 := by rw [factor_2_23]; decide
      have factor_2_25 : (10 : ZMod 25454530741) ^ 39772704 = 1126464778 := by
        calc
          (10 : ZMod 25454530741) ^ 39772704 = (10 : ZMod 25454530741) ^ (19886352 + 19886352) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 19886352 * (10 : ZMod 25454530741) ^ 19886352 := by rw [pow_add]
          _ = 1126464778 := by rw [factor_2_24]; decide
      have factor_2_26 : (10 : ZMod 25454530741) ^ 79545408 = 4098686173 := by
        calc
          (10 : ZMod 25454530741) ^ 79545408 = (10 : ZMod 25454530741) ^ (39772704 + 39772704) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 39772704 * (10 : ZMod 25454530741) ^ 39772704 := by rw [pow_add]
          _ = 4098686173 := by rw [factor_2_25]; decide
      have factor_2_27 : (10 : ZMod 25454530741) ^ 159090817 = 14227747266 := by
        calc
          (10 : ZMod 25454530741) ^ 159090817 = (10 : ZMod 25454530741) ^ (79545408 + 79545408 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 79545408 * (10 : ZMod 25454530741) ^ 79545408) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 14227747266 := by rw [factor_2_26]; decide
      have factor_2_28 : (10 : ZMod 25454530741) ^ 318181634 = 24677574384 := by
        calc
          (10 : ZMod 25454530741) ^ 318181634 = (10 : ZMod 25454530741) ^ (159090817 + 159090817) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 159090817 * (10 : ZMod 25454530741) ^ 159090817 := by rw [pow_add]
          _ = 24677574384 := by rw [factor_2_27]; decide
      have factor_2_29 : (10 : ZMod 25454530741) ^ 636363268 = 9618473415 := by
        calc
          (10 : ZMod 25454530741) ^ 636363268 = (10 : ZMod 25454530741) ^ (318181634 + 318181634) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 318181634 * (10 : ZMod 25454530741) ^ 318181634 := by rw [pow_add]
          _ = 9618473415 := by rw [factor_2_28]; decide
      have factor_2_30 : (10 : ZMod 25454530741) ^ 1272726537 = 22996467737 := by
        calc
          (10 : ZMod 25454530741) ^ 1272726537 = (10 : ZMod 25454530741) ^ (636363268 + 636363268 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 636363268 * (10 : ZMod 25454530741) ^ 636363268) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 22996467737 := by rw [factor_2_29]; decide
      have factor_2_31 : (10 : ZMod 25454530741) ^ 2545453074 = 13239250637 := by
        calc
          (10 : ZMod 25454530741) ^ 2545453074 = (10 : ZMod 25454530741) ^ (1272726537 + 1272726537) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 1272726537 * (10 : ZMod 25454530741) ^ 1272726537 := by rw [pow_add]
          _ = 13239250637 := by rw [factor_2_30]; decide
      have factor_2_32 : (10 : ZMod 25454530741) ^ 5090906148 = 7359369430 := by
        calc
          (10 : ZMod 25454530741) ^ 5090906148 = (10 : ZMod 25454530741) ^ (2545453074 + 2545453074) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 2545453074 * (10 : ZMod 25454530741) ^ 2545453074 := by rw [pow_add]
          _ = 7359369430 := by rw [factor_2_31]; decide
      change (10 : ZMod 25454530741) ^ 5090906148 ≠ 1
      rw [factor_2_32]
      decide
    ·
      have factor_3_0 : (10 : ZMod 25454530741) ^ 1 = 10 := by norm_num
      have factor_3_1 : (10 : ZMod 25454530741) ^ 2 = 100 := by
        calc
          (10 : ZMod 25454530741) ^ 2 = (10 : ZMod 25454530741) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 1 * (10 : ZMod 25454530741) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_3_0]; decide
      have factor_3_2 : (10 : ZMod 25454530741) ^ 5 = 100000 := by
        calc
          (10 : ZMod 25454530741) ^ 5 = (10 : ZMod 25454530741) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 2 * (10 : ZMod 25454530741) ^ 2) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 100000 := by rw [factor_3_1]; decide
      have factor_3_3 : (10 : ZMod 25454530741) ^ 11 = 23636407777 := by
        calc
          (10 : ZMod 25454530741) ^ 11 = (10 : ZMod 25454530741) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 5 * (10 : ZMod 25454530741) ^ 5) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 23636407777 := by rw [factor_3_2]; decide
      have factor_3_4 : (10 : ZMod 25454530741) ^ 23 = 7697844967 := by
        calc
          (10 : ZMod 25454530741) ^ 23 = (10 : ZMod 25454530741) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 11 * (10 : ZMod 25454530741) ^ 11) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 7697844967 := by rw [factor_3_3]; decide
      have factor_3_5 : (10 : ZMod 25454530741) ^ 46 = 2877470936 := by
        calc
          (10 : ZMod 25454530741) ^ 46 = (10 : ZMod 25454530741) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 23 * (10 : ZMod 25454530741) ^ 23 := by rw [pow_add]
          _ = 2877470936 := by rw [factor_3_4]; decide
      have factor_3_6 : (10 : ZMod 25454530741) ^ 93 = 4496456872 := by
        calc
          (10 : ZMod 25454530741) ^ 93 = (10 : ZMod 25454530741) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 46 * (10 : ZMod 25454530741) ^ 46) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 4496456872 := by rw [factor_3_5]; decide
      have factor_3_7 : (10 : ZMod 25454530741) ^ 187 = 15794603683 := by
        calc
          (10 : ZMod 25454530741) ^ 187 = (10 : ZMod 25454530741) ^ (93 + 93 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 93 * (10 : ZMod 25454530741) ^ 93) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 15794603683 := by rw [factor_3_6]; decide
      have factor_3_8 : (10 : ZMod 25454530741) ^ 374 = 6331539168 := by
        calc
          (10 : ZMod 25454530741) ^ 374 = (10 : ZMod 25454530741) ^ (187 + 187) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 187 * (10 : ZMod 25454530741) ^ 187 := by rw [pow_add]
          _ = 6331539168 := by rw [factor_3_7]; decide
      have factor_3_9 : (10 : ZMod 25454530741) ^ 749 = 13993905893 := by
        calc
          (10 : ZMod 25454530741) ^ 749 = (10 : ZMod 25454530741) ^ (374 + 374 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 374 * (10 : ZMod 25454530741) ^ 374) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 13993905893 := by rw [factor_3_8]; decide
      have factor_3_10 : (10 : ZMod 25454530741) ^ 1499 = 18945117928 := by
        calc
          (10 : ZMod 25454530741) ^ 1499 = (10 : ZMod 25454530741) ^ (749 + 749 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 749 * (10 : ZMod 25454530741) ^ 749) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 18945117928 := by rw [factor_3_9]; decide
      have factor_3_11 : (10 : ZMod 25454530741) ^ 2998 = 15431054380 := by
        calc
          (10 : ZMod 25454530741) ^ 2998 = (10 : ZMod 25454530741) ^ (1499 + 1499) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 1499 * (10 : ZMod 25454530741) ^ 1499 := by rw [pow_add]
          _ = 15431054380 := by rw [factor_3_10]; decide
      have factor_3_12 : (10 : ZMod 25454530741) ^ 5996 = 5403146487 := by
        calc
          (10 : ZMod 25454530741) ^ 5996 = (10 : ZMod 25454530741) ^ (2998 + 2998) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 2998 * (10 : ZMod 25454530741) ^ 2998 := by rw [pow_add]
          _ = 5403146487 := by rw [factor_3_11]; decide
      have factor_3_13 : (10 : ZMod 25454530741) ^ 11992 = 24146821820 := by
        calc
          (10 : ZMod 25454530741) ^ 11992 = (10 : ZMod 25454530741) ^ (5996 + 5996) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 5996 * (10 : ZMod 25454530741) ^ 5996 := by rw [pow_add]
          _ = 24146821820 := by rw [factor_3_12]; decide
      have factor_3_14 : (10 : ZMod 25454530741) ^ 23985 = 11032926672 := by
        calc
          (10 : ZMod 25454530741) ^ 23985 = (10 : ZMod 25454530741) ^ (11992 + 11992 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 11992 * (10 : ZMod 25454530741) ^ 11992) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 11032926672 := by rw [factor_3_13]; decide
      have factor_3_15 : (10 : ZMod 25454530741) ^ 47970 = 5549931367 := by
        calc
          (10 : ZMod 25454530741) ^ 47970 = (10 : ZMod 25454530741) ^ (23985 + 23985) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 23985 * (10 : ZMod 25454530741) ^ 23985 := by rw [pow_add]
          _ = 5549931367 := by rw [factor_3_14]; decide
      have factor_3_16 : (10 : ZMod 25454530741) ^ 95941 = 9973208040 := by
        calc
          (10 : ZMod 25454530741) ^ 95941 = (10 : ZMod 25454530741) ^ (47970 + 47970 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 47970 * (10 : ZMod 25454530741) ^ 47970) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 9973208040 := by rw [factor_3_15]; decide
      have factor_3_17 : (10 : ZMod 25454530741) ^ 191883 = 23235223249 := by
        calc
          (10 : ZMod 25454530741) ^ 191883 = (10 : ZMod 25454530741) ^ (95941 + 95941 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 95941 * (10 : ZMod 25454530741) ^ 95941) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 23235223249 := by rw [factor_3_16]; decide
      have factor_3_18 : (10 : ZMod 25454530741) ^ 383767 = 23182957543 := by
        calc
          (10 : ZMod 25454530741) ^ 383767 = (10 : ZMod 25454530741) ^ (191883 + 191883 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 191883 * (10 : ZMod 25454530741) ^ 191883) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 23182957543 := by rw [factor_3_17]; decide
      have factor_3_19 : (10 : ZMod 25454530741) ^ 767535 = 12726927174 := by
        calc
          (10 : ZMod 25454530741) ^ 767535 = (10 : ZMod 25454530741) ^ (383767 + 383767 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 383767 * (10 : ZMod 25454530741) ^ 383767) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 12726927174 := by rw [factor_3_18]; decide
      have factor_3_20 : (10 : ZMod 25454530741) ^ 1535070 = 6195116963 := by
        calc
          (10 : ZMod 25454530741) ^ 1535070 = (10 : ZMod 25454530741) ^ (767535 + 767535) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 767535 * (10 : ZMod 25454530741) ^ 767535 := by rw [pow_add]
          _ = 6195116963 := by rw [factor_3_19]; decide
      have factor_3_21 : (10 : ZMod 25454530741) ^ 3070140 = 20741950721 := by
        calc
          (10 : ZMod 25454530741) ^ 3070140 = (10 : ZMod 25454530741) ^ (1535070 + 1535070) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 1535070 * (10 : ZMod 25454530741) ^ 1535070 := by rw [pow_add]
          _ = 20741950721 := by rw [factor_3_20]; decide
      change (10 : ZMod 25454530741) ^ 3070140 ≠ 1
      rw [factor_3_21]
      decide
    ·
      have factor_4_0 : (10 : ZMod 25454530741) ^ 1 = 10 := by norm_num
      have factor_4_1 : (10 : ZMod 25454530741) ^ 3 = 1000 := by
        calc
          (10 : ZMod 25454530741) ^ 3 = (10 : ZMod 25454530741) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 1 * (10 : ZMod 25454530741) ^ 1) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_4_0]; decide
      have factor_4_2 : (10 : ZMod 25454530741) ^ 7 = 10000000 := by
        calc
          (10 : ZMod 25454530741) ^ 7 = (10 : ZMod 25454530741) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 3 * (10 : ZMod 25454530741) ^ 3) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 10000000 := by rw [factor_4_1]; decide
      have factor_4_3 : (10 : ZMod 25454530741) ^ 15 = 18759839815 := by
        calc
          (10 : ZMod 25454530741) ^ 15 = (10 : ZMod 25454530741) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 7 * (10 : ZMod 25454530741) ^ 7) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 18759839815 := by rw [factor_4_2]; decide
      have factor_4_4 : (10 : ZMod 25454530741) ^ 30 = 3256951145 := by
        calc
          (10 : ZMod 25454530741) ^ 30 = (10 : ZMod 25454530741) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 15 * (10 : ZMod 25454530741) ^ 15 := by rw [pow_add]
          _ = 3256951145 := by rw [factor_4_3]; decide
      have factor_4_5 : (10 : ZMod 25454530741) ^ 60 = 19802413705 := by
        calc
          (10 : ZMod 25454530741) ^ 60 = (10 : ZMod 25454530741) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 30 * (10 : ZMod 25454530741) ^ 30 := by rw [pow_add]
          _ = 19802413705 := by rw [factor_4_4]; decide
      have factor_4_6 : (10 : ZMod 25454530741) ^ 121 = 19864742775 := by
        calc
          (10 : ZMod 25454530741) ^ 121 = (10 : ZMod 25454530741) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 60 * (10 : ZMod 25454530741) ^ 60) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 19864742775 := by rw [factor_4_5]; decide
      have factor_4_7 : (10 : ZMod 25454530741) ^ 242 = 13157557505 := by
        calc
          (10 : ZMod 25454530741) ^ 242 = (10 : ZMod 25454530741) ^ (121 + 121) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 121 * (10 : ZMod 25454530741) ^ 121 := by rw [pow_add]
          _ = 13157557505 := by rw [factor_4_6]; decide
      have factor_4_8 : (10 : ZMod 25454530741) ^ 485 = 13087693072 := by
        calc
          (10 : ZMod 25454530741) ^ 485 = (10 : ZMod 25454530741) ^ (242 + 242 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 242 * (10 : ZMod 25454530741) ^ 242) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 13087693072 := by rw [factor_4_7]; decide
      have factor_4_9 : (10 : ZMod 25454530741) ^ 971 = 87810187 := by
        calc
          (10 : ZMod 25454530741) ^ 971 = (10 : ZMod 25454530741) ^ (485 + 485 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 485 * (10 : ZMod 25454530741) ^ 485) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 87810187 := by rw [factor_4_8]; decide
      have factor_4_10 : (10 : ZMod 25454530741) ^ 1943 = 10343319533 := by
        calc
          (10 : ZMod 25454530741) ^ 1943 = (10 : ZMod 25454530741) ^ (971 + 971 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 971 * (10 : ZMod 25454530741) ^ 971) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 10343319533 := by rw [factor_4_9]; decide
      have factor_4_11 : (10 : ZMod 25454530741) ^ 3886 = 2115542229 := by
        calc
          (10 : ZMod 25454530741) ^ 3886 = (10 : ZMod 25454530741) ^ (1943 + 1943) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 1943 * (10 : ZMod 25454530741) ^ 1943 := by rw [pow_add]
          _ = 2115542229 := by rw [factor_4_10]; decide
      have factor_4_12 : (10 : ZMod 25454530741) ^ 7772 = 7859390722 := by
        calc
          (10 : ZMod 25454530741) ^ 7772 = (10 : ZMod 25454530741) ^ (3886 + 3886) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 3886 * (10 : ZMod 25454530741) ^ 3886 := by rw [pow_add]
          _ = 7859390722 := by rw [factor_4_11]; decide
      have factor_4_13 : (10 : ZMod 25454530741) ^ 15545 = 21388009132 := by
        calc
          (10 : ZMod 25454530741) ^ 15545 = (10 : ZMod 25454530741) ^ (7772 + 7772 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 7772 * (10 : ZMod 25454530741) ^ 7772) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 21388009132 := by rw [factor_4_12]; decide
      have factor_4_14 : (10 : ZMod 25454530741) ^ 31091 = 17001031374 := by
        calc
          (10 : ZMod 25454530741) ^ 31091 = (10 : ZMod 25454530741) ^ (15545 + 15545 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 15545 * (10 : ZMod 25454530741) ^ 15545) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 17001031374 := by rw [factor_4_13]; decide
      have factor_4_15 : (10 : ZMod 25454530741) ^ 62182 = 22297568262 := by
        calc
          (10 : ZMod 25454530741) ^ 62182 = (10 : ZMod 25454530741) ^ (31091 + 31091) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 31091 * (10 : ZMod 25454530741) ^ 31091 := by rw [pow_add]
          _ = 22297568262 := by rw [factor_4_14]; decide
      have factor_4_16 : (10 : ZMod 25454530741) ^ 124365 = 23600568888 := by
        calc
          (10 : ZMod 25454530741) ^ 124365 = (10 : ZMod 25454530741) ^ (62182 + 62182 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = ((10 : ZMod 25454530741) ^ 62182 * (10 : ZMod 25454530741) ^ 62182) * (10 : ZMod 25454530741) := by rw [pow_succ, pow_add]
          _ = 23600568888 := by rw [factor_4_15]; decide
      have factor_4_17 : (10 : ZMod 25454530741) ^ 248730 = 11904979774 := by
        calc
          (10 : ZMod 25454530741) ^ 248730 = (10 : ZMod 25454530741) ^ (124365 + 124365) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 124365 * (10 : ZMod 25454530741) ^ 124365 := by rw [pow_add]
          _ = 11904979774 := by rw [factor_4_16]; decide
      have factor_4_18 : (10 : ZMod 25454530741) ^ 497460 = 8504642855 := by
        calc
          (10 : ZMod 25454530741) ^ 497460 = (10 : ZMod 25454530741) ^ (248730 + 248730) :=
            congrArg (fun n : ℕ => (10 : ZMod 25454530741) ^ n) (by norm_num)
          _ = (10 : ZMod 25454530741) ^ 248730 * (10 : ZMod 25454530741) ^ 248730 := by rw [pow_add]
          _ = 8504642855 := by rw [factor_4_17]; decide
      change (10 : ZMod 25454530741) ^ 497460 ≠ 1
      rw [factor_4_18]
      decide

#print axioms prime_lucas_25454530741

end TotientTailPeriodKiller
end Erdos249257
