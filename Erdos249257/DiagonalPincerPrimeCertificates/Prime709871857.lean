import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_709871857 : Nat.Prime 709871857 := by
  apply lucas_primality 709871857 (10 : ZMod 709871857)
  ·
      have fermat_0 : (10 : ZMod 709871857) ^ 1 = 10 := by norm_num
      have fermat_1 : (10 : ZMod 709871857) ^ 2 = 100 := by
        calc
          (10 : ZMod 709871857) ^ 2 = (10 : ZMod 709871857) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 1 * (10 : ZMod 709871857) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [fermat_0]; decide
      have fermat_2 : (10 : ZMod 709871857) ^ 5 = 100000 := by
        calc
          (10 : ZMod 709871857) ^ 5 = (10 : ZMod 709871857) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 2 * (10 : ZMod 709871857) ^ 2) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 100000 := by rw [fermat_1]; decide
      have fermat_3 : (10 : ZMod 709871857) ^ 10 = 61794002 := by
        calc
          (10 : ZMod 709871857) ^ 10 = (10 : ZMod 709871857) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 5 * (10 : ZMod 709871857) ^ 5 := by rw [pow_add]
          _ = 61794002 := by rw [fermat_2]; decide
      have fermat_4 : (10 : ZMod 709871857) ^ 21 = 20567380 := by
        calc
          (10 : ZMod 709871857) ^ 21 = (10 : ZMod 709871857) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 10 * (10 : ZMod 709871857) ^ 10) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 20567380 := by rw [fermat_3]; decide
      have fermat_5 : (10 : ZMod 709871857) ^ 42 = 221246958 := by
        calc
          (10 : ZMod 709871857) ^ 42 = (10 : ZMod 709871857) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 21 * (10 : ZMod 709871857) ^ 21 := by rw [pow_add]
          _ = 221246958 := by rw [fermat_4]; decide
      have fermat_6 : (10 : ZMod 709871857) ^ 84 = 185756680 := by
        calc
          (10 : ZMod 709871857) ^ 84 = (10 : ZMod 709871857) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 42 * (10 : ZMod 709871857) ^ 42 := by rw [pow_add]
          _ = 185756680 := by rw [fermat_5]; decide
      have fermat_7 : (10 : ZMod 709871857) ^ 169 = 173403187 := by
        calc
          (10 : ZMod 709871857) ^ 169 = (10 : ZMod 709871857) ^ (84 + 84 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 84 * (10 : ZMod 709871857) ^ 84) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 173403187 := by rw [fermat_6]; decide
      have fermat_8 : (10 : ZMod 709871857) ^ 338 = 457189380 := by
        calc
          (10 : ZMod 709871857) ^ 338 = (10 : ZMod 709871857) ^ (169 + 169) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 169 * (10 : ZMod 709871857) ^ 169 := by rw [pow_add]
          _ = 457189380 := by rw [fermat_7]; decide
      have fermat_9 : (10 : ZMod 709871857) ^ 676 = 276231044 := by
        calc
          (10 : ZMod 709871857) ^ 676 = (10 : ZMod 709871857) ^ (338 + 338) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 338 * (10 : ZMod 709871857) ^ 338 := by rw [pow_add]
          _ = 276231044 := by rw [fermat_8]; decide
      have fermat_10 : (10 : ZMod 709871857) ^ 1353 = 685878995 := by
        calc
          (10 : ZMod 709871857) ^ 1353 = (10 : ZMod 709871857) ^ (676 + 676 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 676 * (10 : ZMod 709871857) ^ 676) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 685878995 := by rw [fermat_9]; decide
      have fermat_11 : (10 : ZMod 709871857) ^ 2707 = 481334342 := by
        calc
          (10 : ZMod 709871857) ^ 2707 = (10 : ZMod 709871857) ^ (1353 + 1353 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 1353 * (10 : ZMod 709871857) ^ 1353) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 481334342 := by rw [fermat_10]; decide
      have fermat_12 : (10 : ZMod 709871857) ^ 5415 = 231910262 := by
        calc
          (10 : ZMod 709871857) ^ 5415 = (10 : ZMod 709871857) ^ (2707 + 2707 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 2707 * (10 : ZMod 709871857) ^ 2707) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 231910262 := by rw [fermat_11]; decide
      have fermat_13 : (10 : ZMod 709871857) ^ 10831 = 688461569 := by
        calc
          (10 : ZMod 709871857) ^ 10831 = (10 : ZMod 709871857) ^ (5415 + 5415 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 5415 * (10 : ZMod 709871857) ^ 5415) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 688461569 := by rw [fermat_12]; decide
      have fermat_14 : (10 : ZMod 709871857) ^ 21663 = 417005227 := by
        calc
          (10 : ZMod 709871857) ^ 21663 = (10 : ZMod 709871857) ^ (10831 + 10831 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 10831 * (10 : ZMod 709871857) ^ 10831) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 417005227 := by rw [fermat_13]; decide
      have fermat_15 : (10 : ZMod 709871857) ^ 43327 = 500823199 := by
        calc
          (10 : ZMod 709871857) ^ 43327 = (10 : ZMod 709871857) ^ (21663 + 21663 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 21663 * (10 : ZMod 709871857) ^ 21663) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 500823199 := by rw [fermat_14]; decide
      have fermat_16 : (10 : ZMod 709871857) ^ 86654 = 28897292 := by
        calc
          (10 : ZMod 709871857) ^ 86654 = (10 : ZMod 709871857) ^ (43327 + 43327) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 43327 * (10 : ZMod 709871857) ^ 43327 := by rw [pow_add]
          _ = 28897292 := by rw [fermat_15]; decide
      have fermat_17 : (10 : ZMod 709871857) ^ 173308 = 695054313 := by
        calc
          (10 : ZMod 709871857) ^ 173308 = (10 : ZMod 709871857) ^ (86654 + 86654) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 86654 * (10 : ZMod 709871857) ^ 86654 := by rw [pow_add]
          _ = 695054313 := by rw [fermat_16]; decide
      have fermat_18 : (10 : ZMod 709871857) ^ 346617 = 71426781 := by
        calc
          (10 : ZMod 709871857) ^ 346617 = (10 : ZMod 709871857) ^ (173308 + 173308 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 173308 * (10 : ZMod 709871857) ^ 173308) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 71426781 := by rw [fermat_17]; decide
      have fermat_19 : (10 : ZMod 709871857) ^ 693234 = 606101948 := by
        calc
          (10 : ZMod 709871857) ^ 693234 = (10 : ZMod 709871857) ^ (346617 + 346617) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 346617 * (10 : ZMod 709871857) ^ 346617 := by rw [pow_add]
          _ = 606101948 := by rw [fermat_18]; decide
      have fermat_20 : (10 : ZMod 709871857) ^ 1386468 = 161689025 := by
        calc
          (10 : ZMod 709871857) ^ 1386468 = (10 : ZMod 709871857) ^ (693234 + 693234) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 693234 * (10 : ZMod 709871857) ^ 693234 := by rw [pow_add]
          _ = 161689025 := by rw [fermat_19]; decide
      have fermat_21 : (10 : ZMod 709871857) ^ 2772936 = 458274804 := by
        calc
          (10 : ZMod 709871857) ^ 2772936 = (10 : ZMod 709871857) ^ (1386468 + 1386468) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 1386468 * (10 : ZMod 709871857) ^ 1386468 := by rw [pow_add]
          _ = 458274804 := by rw [fermat_20]; decide
      have fermat_22 : (10 : ZMod 709871857) ^ 5545873 = 181677291 := by
        calc
          (10 : ZMod 709871857) ^ 5545873 = (10 : ZMod 709871857) ^ (2772936 + 2772936 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 2772936 * (10 : ZMod 709871857) ^ 2772936) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 181677291 := by rw [fermat_21]; decide
      have fermat_23 : (10 : ZMod 709871857) ^ 11091747 = 567577402 := by
        calc
          (10 : ZMod 709871857) ^ 11091747 = (10 : ZMod 709871857) ^ (5545873 + 5545873 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 5545873 * (10 : ZMod 709871857) ^ 5545873) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 567577402 := by rw [fermat_22]; decide
      have fermat_24 : (10 : ZMod 709871857) ^ 22183495 = 331994610 := by
        calc
          (10 : ZMod 709871857) ^ 22183495 = (10 : ZMod 709871857) ^ (11091747 + 11091747 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 11091747 * (10 : ZMod 709871857) ^ 11091747) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 331994610 := by rw [fermat_23]; decide
      have fermat_25 : (10 : ZMod 709871857) ^ 44366991 = 241548647 := by
        calc
          (10 : ZMod 709871857) ^ 44366991 = (10 : ZMod 709871857) ^ (22183495 + 22183495 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 22183495 * (10 : ZMod 709871857) ^ 22183495) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 241548647 := by rw [fermat_24]; decide
      have fermat_26 : (10 : ZMod 709871857) ^ 88733982 = 239938744 := by
        calc
          (10 : ZMod 709871857) ^ 88733982 = (10 : ZMod 709871857) ^ (44366991 + 44366991) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 44366991 * (10 : ZMod 709871857) ^ 44366991 := by rw [pow_add]
          _ = 239938744 := by rw [fermat_25]; decide
      have fermat_27 : (10 : ZMod 709871857) ^ 177467964 = 368316106 := by
        calc
          (10 : ZMod 709871857) ^ 177467964 = (10 : ZMod 709871857) ^ (88733982 + 88733982) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 88733982 * (10 : ZMod 709871857) ^ 88733982 := by rw [pow_add]
          _ = 368316106 := by rw [fermat_26]; decide
      have fermat_28 : (10 : ZMod 709871857) ^ 354935928 = 709871856 := by
        calc
          (10 : ZMod 709871857) ^ 354935928 = (10 : ZMod 709871857) ^ (177467964 + 177467964) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 177467964 * (10 : ZMod 709871857) ^ 177467964 := by rw [pow_add]
          _ = 709871856 := by rw [fermat_27]; decide
      have fermat_29 : (10 : ZMod 709871857) ^ 709871856 = 1 := by
        calc
          (10 : ZMod 709871857) ^ 709871856 = (10 : ZMod 709871857) ^ (354935928 + 354935928) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 354935928 * (10 : ZMod 709871857) ^ 354935928 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (17, 2), (73, 1), (701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (17, 2), (73, 1), (701, 1)] : List FactorBlock).map factorBlockValue).prod = 709871857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (10 : ZMod 709871857) ^ 1 = 10 := by norm_num
      have factor_0_1 : (10 : ZMod 709871857) ^ 2 = 100 := by
        calc
          (10 : ZMod 709871857) ^ 2 = (10 : ZMod 709871857) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 1 * (10 : ZMod 709871857) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_0_0]; decide
      have factor_0_2 : (10 : ZMod 709871857) ^ 5 = 100000 := by
        calc
          (10 : ZMod 709871857) ^ 5 = (10 : ZMod 709871857) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 2 * (10 : ZMod 709871857) ^ 2) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 100000 := by rw [factor_0_1]; decide
      have factor_0_3 : (10 : ZMod 709871857) ^ 10 = 61794002 := by
        calc
          (10 : ZMod 709871857) ^ 10 = (10 : ZMod 709871857) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 5 * (10 : ZMod 709871857) ^ 5 := by rw [pow_add]
          _ = 61794002 := by rw [factor_0_2]; decide
      have factor_0_4 : (10 : ZMod 709871857) ^ 21 = 20567380 := by
        calc
          (10 : ZMod 709871857) ^ 21 = (10 : ZMod 709871857) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 10 * (10 : ZMod 709871857) ^ 10) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 20567380 := by rw [factor_0_3]; decide
      have factor_0_5 : (10 : ZMod 709871857) ^ 42 = 221246958 := by
        calc
          (10 : ZMod 709871857) ^ 42 = (10 : ZMod 709871857) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 21 * (10 : ZMod 709871857) ^ 21 := by rw [pow_add]
          _ = 221246958 := by rw [factor_0_4]; decide
      have factor_0_6 : (10 : ZMod 709871857) ^ 84 = 185756680 := by
        calc
          (10 : ZMod 709871857) ^ 84 = (10 : ZMod 709871857) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 42 * (10 : ZMod 709871857) ^ 42 := by rw [pow_add]
          _ = 185756680 := by rw [factor_0_5]; decide
      have factor_0_7 : (10 : ZMod 709871857) ^ 169 = 173403187 := by
        calc
          (10 : ZMod 709871857) ^ 169 = (10 : ZMod 709871857) ^ (84 + 84 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 84 * (10 : ZMod 709871857) ^ 84) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 173403187 := by rw [factor_0_6]; decide
      have factor_0_8 : (10 : ZMod 709871857) ^ 338 = 457189380 := by
        calc
          (10 : ZMod 709871857) ^ 338 = (10 : ZMod 709871857) ^ (169 + 169) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 169 * (10 : ZMod 709871857) ^ 169 := by rw [pow_add]
          _ = 457189380 := by rw [factor_0_7]; decide
      have factor_0_9 : (10 : ZMod 709871857) ^ 676 = 276231044 := by
        calc
          (10 : ZMod 709871857) ^ 676 = (10 : ZMod 709871857) ^ (338 + 338) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 338 * (10 : ZMod 709871857) ^ 338 := by rw [pow_add]
          _ = 276231044 := by rw [factor_0_8]; decide
      have factor_0_10 : (10 : ZMod 709871857) ^ 1353 = 685878995 := by
        calc
          (10 : ZMod 709871857) ^ 1353 = (10 : ZMod 709871857) ^ (676 + 676 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 676 * (10 : ZMod 709871857) ^ 676) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 685878995 := by rw [factor_0_9]; decide
      have factor_0_11 : (10 : ZMod 709871857) ^ 2707 = 481334342 := by
        calc
          (10 : ZMod 709871857) ^ 2707 = (10 : ZMod 709871857) ^ (1353 + 1353 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 1353 * (10 : ZMod 709871857) ^ 1353) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 481334342 := by rw [factor_0_10]; decide
      have factor_0_12 : (10 : ZMod 709871857) ^ 5415 = 231910262 := by
        calc
          (10 : ZMod 709871857) ^ 5415 = (10 : ZMod 709871857) ^ (2707 + 2707 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 2707 * (10 : ZMod 709871857) ^ 2707) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 231910262 := by rw [factor_0_11]; decide
      have factor_0_13 : (10 : ZMod 709871857) ^ 10831 = 688461569 := by
        calc
          (10 : ZMod 709871857) ^ 10831 = (10 : ZMod 709871857) ^ (5415 + 5415 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 5415 * (10 : ZMod 709871857) ^ 5415) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 688461569 := by rw [factor_0_12]; decide
      have factor_0_14 : (10 : ZMod 709871857) ^ 21663 = 417005227 := by
        calc
          (10 : ZMod 709871857) ^ 21663 = (10 : ZMod 709871857) ^ (10831 + 10831 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 10831 * (10 : ZMod 709871857) ^ 10831) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 417005227 := by rw [factor_0_13]; decide
      have factor_0_15 : (10 : ZMod 709871857) ^ 43327 = 500823199 := by
        calc
          (10 : ZMod 709871857) ^ 43327 = (10 : ZMod 709871857) ^ (21663 + 21663 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 21663 * (10 : ZMod 709871857) ^ 21663) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 500823199 := by rw [factor_0_14]; decide
      have factor_0_16 : (10 : ZMod 709871857) ^ 86654 = 28897292 := by
        calc
          (10 : ZMod 709871857) ^ 86654 = (10 : ZMod 709871857) ^ (43327 + 43327) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 43327 * (10 : ZMod 709871857) ^ 43327 := by rw [pow_add]
          _ = 28897292 := by rw [factor_0_15]; decide
      have factor_0_17 : (10 : ZMod 709871857) ^ 173308 = 695054313 := by
        calc
          (10 : ZMod 709871857) ^ 173308 = (10 : ZMod 709871857) ^ (86654 + 86654) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 86654 * (10 : ZMod 709871857) ^ 86654 := by rw [pow_add]
          _ = 695054313 := by rw [factor_0_16]; decide
      have factor_0_18 : (10 : ZMod 709871857) ^ 346617 = 71426781 := by
        calc
          (10 : ZMod 709871857) ^ 346617 = (10 : ZMod 709871857) ^ (173308 + 173308 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 173308 * (10 : ZMod 709871857) ^ 173308) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 71426781 := by rw [factor_0_17]; decide
      have factor_0_19 : (10 : ZMod 709871857) ^ 693234 = 606101948 := by
        calc
          (10 : ZMod 709871857) ^ 693234 = (10 : ZMod 709871857) ^ (346617 + 346617) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 346617 * (10 : ZMod 709871857) ^ 346617 := by rw [pow_add]
          _ = 606101948 := by rw [factor_0_18]; decide
      have factor_0_20 : (10 : ZMod 709871857) ^ 1386468 = 161689025 := by
        calc
          (10 : ZMod 709871857) ^ 1386468 = (10 : ZMod 709871857) ^ (693234 + 693234) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 693234 * (10 : ZMod 709871857) ^ 693234 := by rw [pow_add]
          _ = 161689025 := by rw [factor_0_19]; decide
      have factor_0_21 : (10 : ZMod 709871857) ^ 2772936 = 458274804 := by
        calc
          (10 : ZMod 709871857) ^ 2772936 = (10 : ZMod 709871857) ^ (1386468 + 1386468) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 1386468 * (10 : ZMod 709871857) ^ 1386468 := by rw [pow_add]
          _ = 458274804 := by rw [factor_0_20]; decide
      have factor_0_22 : (10 : ZMod 709871857) ^ 5545873 = 181677291 := by
        calc
          (10 : ZMod 709871857) ^ 5545873 = (10 : ZMod 709871857) ^ (2772936 + 2772936 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 2772936 * (10 : ZMod 709871857) ^ 2772936) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 181677291 := by rw [factor_0_21]; decide
      have factor_0_23 : (10 : ZMod 709871857) ^ 11091747 = 567577402 := by
        calc
          (10 : ZMod 709871857) ^ 11091747 = (10 : ZMod 709871857) ^ (5545873 + 5545873 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 5545873 * (10 : ZMod 709871857) ^ 5545873) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 567577402 := by rw [factor_0_22]; decide
      have factor_0_24 : (10 : ZMod 709871857) ^ 22183495 = 331994610 := by
        calc
          (10 : ZMod 709871857) ^ 22183495 = (10 : ZMod 709871857) ^ (11091747 + 11091747 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 11091747 * (10 : ZMod 709871857) ^ 11091747) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 331994610 := by rw [factor_0_23]; decide
      have factor_0_25 : (10 : ZMod 709871857) ^ 44366991 = 241548647 := by
        calc
          (10 : ZMod 709871857) ^ 44366991 = (10 : ZMod 709871857) ^ (22183495 + 22183495 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 22183495 * (10 : ZMod 709871857) ^ 22183495) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 241548647 := by rw [factor_0_24]; decide
      have factor_0_26 : (10 : ZMod 709871857) ^ 88733982 = 239938744 := by
        calc
          (10 : ZMod 709871857) ^ 88733982 = (10 : ZMod 709871857) ^ (44366991 + 44366991) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 44366991 * (10 : ZMod 709871857) ^ 44366991 := by rw [pow_add]
          _ = 239938744 := by rw [factor_0_25]; decide
      have factor_0_27 : (10 : ZMod 709871857) ^ 177467964 = 368316106 := by
        calc
          (10 : ZMod 709871857) ^ 177467964 = (10 : ZMod 709871857) ^ (88733982 + 88733982) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 88733982 * (10 : ZMod 709871857) ^ 88733982 := by rw [pow_add]
          _ = 368316106 := by rw [factor_0_26]; decide
      have factor_0_28 : (10 : ZMod 709871857) ^ 354935928 = 709871856 := by
        calc
          (10 : ZMod 709871857) ^ 354935928 = (10 : ZMod 709871857) ^ (177467964 + 177467964) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 177467964 * (10 : ZMod 709871857) ^ 177467964 := by rw [pow_add]
          _ = 709871856 := by rw [factor_0_27]; decide
      change (10 : ZMod 709871857) ^ 354935928 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (10 : ZMod 709871857) ^ 1 = 10 := by norm_num
      have factor_1_1 : (10 : ZMod 709871857) ^ 3 = 1000 := by
        calc
          (10 : ZMod 709871857) ^ 3 = (10 : ZMod 709871857) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 1 * (10 : ZMod 709871857) ^ 1) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_1_0]; decide
      have factor_1_2 : (10 : ZMod 709871857) ^ 7 = 10000000 := by
        calc
          (10 : ZMod 709871857) ^ 7 = (10 : ZMod 709871857) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 3 * (10 : ZMod 709871857) ^ 3) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 10000000 := by rw [factor_1_1]; decide
      have factor_1_3 : (10 : ZMod 709871857) ^ 14 = 351504410 := by
        calc
          (10 : ZMod 709871857) ^ 14 = (10 : ZMod 709871857) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 7 * (10 : ZMod 709871857) ^ 7 := by rw [pow_add]
          _ = 351504410 := by rw [factor_1_2]; decide
      have factor_1_4 : (10 : ZMod 709871857) ^ 28 = 497255819 := by
        calc
          (10 : ZMod 709871857) ^ 28 = (10 : ZMod 709871857) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 14 * (10 : ZMod 709871857) ^ 14 := by rw [pow_add]
          _ = 497255819 := by rw [factor_1_3]; decide
      have factor_1_5 : (10 : ZMod 709871857) ^ 56 = 600590633 := by
        calc
          (10 : ZMod 709871857) ^ 56 = (10 : ZMod 709871857) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 28 * (10 : ZMod 709871857) ^ 28 := by rw [pow_add]
          _ = 600590633 := by rw [factor_1_4]; decide
      have factor_1_6 : (10 : ZMod 709871857) ^ 112 = 126813790 := by
        calc
          (10 : ZMod 709871857) ^ 112 = (10 : ZMod 709871857) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 56 * (10 : ZMod 709871857) ^ 56 := by rw [pow_add]
          _ = 126813790 := by rw [factor_1_5]; decide
      have factor_1_7 : (10 : ZMod 709871857) ^ 225 = 98905890 := by
        calc
          (10 : ZMod 709871857) ^ 225 = (10 : ZMod 709871857) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 112 * (10 : ZMod 709871857) ^ 112) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 98905890 := by rw [factor_1_6]; decide
      have factor_1_8 : (10 : ZMod 709871857) ^ 451 = 67663686 := by
        calc
          (10 : ZMod 709871857) ^ 451 = (10 : ZMod 709871857) ^ (225 + 225 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 225 * (10 : ZMod 709871857) ^ 225) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 67663686 := by rw [factor_1_7]; decide
      have factor_1_9 : (10 : ZMod 709871857) ^ 902 = 491380250 := by
        calc
          (10 : ZMod 709871857) ^ 902 = (10 : ZMod 709871857) ^ (451 + 451) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 451 * (10 : ZMod 709871857) ^ 451 := by rw [pow_add]
          _ = 491380250 := by rw [factor_1_8]; decide
      have factor_1_10 : (10 : ZMod 709871857) ^ 1805 = 90264029 := by
        calc
          (10 : ZMod 709871857) ^ 1805 = (10 : ZMod 709871857) ^ (902 + 902 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 902 * (10 : ZMod 709871857) ^ 902) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 90264029 := by rw [factor_1_9]; decide
      have factor_1_11 : (10 : ZMod 709871857) ^ 3610 = 229899492 := by
        calc
          (10 : ZMod 709871857) ^ 3610 = (10 : ZMod 709871857) ^ (1805 + 1805) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 1805 * (10 : ZMod 709871857) ^ 1805 := by rw [pow_add]
          _ = 229899492 := by rw [factor_1_10]; decide
      have factor_1_12 : (10 : ZMod 709871857) ^ 7221 = 421689035 := by
        calc
          (10 : ZMod 709871857) ^ 7221 = (10 : ZMod 709871857) ^ (3610 + 3610 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 3610 * (10 : ZMod 709871857) ^ 3610) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 421689035 := by rw [factor_1_11]; decide
      have factor_1_13 : (10 : ZMod 709871857) ^ 14442 = 663533686 := by
        calc
          (10 : ZMod 709871857) ^ 14442 = (10 : ZMod 709871857) ^ (7221 + 7221) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 7221 * (10 : ZMod 709871857) ^ 7221 := by rw [pow_add]
          _ = 663533686 := by rw [factor_1_12]; decide
      have factor_1_14 : (10 : ZMod 709871857) ^ 28884 = 19596785 := by
        calc
          (10 : ZMod 709871857) ^ 28884 = (10 : ZMod 709871857) ^ (14442 + 14442) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 14442 * (10 : ZMod 709871857) ^ 14442 := by rw [pow_add]
          _ = 19596785 := by rw [factor_1_13]; decide
      have factor_1_15 : (10 : ZMod 709871857) ^ 57769 = 514818665 := by
        calc
          (10 : ZMod 709871857) ^ 57769 = (10 : ZMod 709871857) ^ (28884 + 28884 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 28884 * (10 : ZMod 709871857) ^ 28884) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 514818665 := by rw [factor_1_14]; decide
      have factor_1_16 : (10 : ZMod 709871857) ^ 115539 = 623439973 := by
        calc
          (10 : ZMod 709871857) ^ 115539 = (10 : ZMod 709871857) ^ (57769 + 57769 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 57769 * (10 : ZMod 709871857) ^ 57769) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 623439973 := by rw [factor_1_15]; decide
      have factor_1_17 : (10 : ZMod 709871857) ^ 231078 = 628740840 := by
        calc
          (10 : ZMod 709871857) ^ 231078 = (10 : ZMod 709871857) ^ (115539 + 115539) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 115539 * (10 : ZMod 709871857) ^ 115539 := by rw [pow_add]
          _ = 628740840 := by rw [factor_1_16]; decide
      have factor_1_18 : (10 : ZMod 709871857) ^ 462156 = 557220637 := by
        calc
          (10 : ZMod 709871857) ^ 462156 = (10 : ZMod 709871857) ^ (231078 + 231078) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 231078 * (10 : ZMod 709871857) ^ 231078 := by rw [pow_add]
          _ = 557220637 := by rw [factor_1_17]; decide
      have factor_1_19 : (10 : ZMod 709871857) ^ 924312 = 125106857 := by
        calc
          (10 : ZMod 709871857) ^ 924312 = (10 : ZMod 709871857) ^ (462156 + 462156) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 462156 * (10 : ZMod 709871857) ^ 462156 := by rw [pow_add]
          _ = 125106857 := by rw [factor_1_18]; decide
      have factor_1_20 : (10 : ZMod 709871857) ^ 1848624 = 320241258 := by
        calc
          (10 : ZMod 709871857) ^ 1848624 = (10 : ZMod 709871857) ^ (924312 + 924312) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 924312 * (10 : ZMod 709871857) ^ 924312 := by rw [pow_add]
          _ = 320241258 := by rw [factor_1_19]; decide
      have factor_1_21 : (10 : ZMod 709871857) ^ 3697249 = 9651469 := by
        calc
          (10 : ZMod 709871857) ^ 3697249 = (10 : ZMod 709871857) ^ (1848624 + 1848624 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 1848624 * (10 : ZMod 709871857) ^ 1848624) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 9651469 := by rw [factor_1_20]; decide
      have factor_1_22 : (10 : ZMod 709871857) ^ 7394498 = 49038707 := by
        calc
          (10 : ZMod 709871857) ^ 7394498 = (10 : ZMod 709871857) ^ (3697249 + 3697249) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 3697249 * (10 : ZMod 709871857) ^ 3697249 := by rw [pow_add]
          _ = 49038707 := by rw [factor_1_21]; decide
      have factor_1_23 : (10 : ZMod 709871857) ^ 14788997 = 143916699 := by
        calc
          (10 : ZMod 709871857) ^ 14788997 = (10 : ZMod 709871857) ^ (7394498 + 7394498 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 7394498 * (10 : ZMod 709871857) ^ 7394498) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 143916699 := by rw [factor_1_22]; decide
      have factor_1_24 : (10 : ZMod 709871857) ^ 29577994 = 604616618 := by
        calc
          (10 : ZMod 709871857) ^ 29577994 = (10 : ZMod 709871857) ^ (14788997 + 14788997) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 14788997 * (10 : ZMod 709871857) ^ 14788997 := by rw [pow_add]
          _ = 604616618 := by rw [factor_1_23]; decide
      have factor_1_25 : (10 : ZMod 709871857) ^ 59155988 = 509646631 := by
        calc
          (10 : ZMod 709871857) ^ 59155988 = (10 : ZMod 709871857) ^ (29577994 + 29577994) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 29577994 * (10 : ZMod 709871857) ^ 29577994 := by rw [pow_add]
          _ = 509646631 := by rw [factor_1_24]; decide
      have factor_1_26 : (10 : ZMod 709871857) ^ 118311976 = 225741816 := by
        calc
          (10 : ZMod 709871857) ^ 118311976 = (10 : ZMod 709871857) ^ (59155988 + 59155988) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 59155988 * (10 : ZMod 709871857) ^ 59155988 := by rw [pow_add]
          _ = 225741816 := by rw [factor_1_25]; decide
      have factor_1_27 : (10 : ZMod 709871857) ^ 236623952 = 225741815 := by
        calc
          (10 : ZMod 709871857) ^ 236623952 = (10 : ZMod 709871857) ^ (118311976 + 118311976) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 118311976 * (10 : ZMod 709871857) ^ 118311976 := by rw [pow_add]
          _ = 225741815 := by rw [factor_1_26]; decide
      change (10 : ZMod 709871857) ^ 236623952 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (10 : ZMod 709871857) ^ 1 = 10 := by norm_num
      have factor_2_1 : (10 : ZMod 709871857) ^ 2 = 100 := by
        calc
          (10 : ZMod 709871857) ^ 2 = (10 : ZMod 709871857) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 1 * (10 : ZMod 709871857) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_2_0]; decide
      have factor_2_2 : (10 : ZMod 709871857) ^ 4 = 10000 := by
        calc
          (10 : ZMod 709871857) ^ 4 = (10 : ZMod 709871857) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 2 * (10 : ZMod 709871857) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [factor_2_1]; decide
      have factor_2_3 : (10 : ZMod 709871857) ^ 9 = 290128143 := by
        calc
          (10 : ZMod 709871857) ^ 9 = (10 : ZMod 709871857) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 4 * (10 : ZMod 709871857) ^ 4) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 290128143 := by rw [factor_2_2]; decide
      have factor_2_4 : (10 : ZMod 709871857) ^ 19 = 426128788 := by
        calc
          (10 : ZMod 709871857) ^ 19 = (10 : ZMod 709871857) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 9 * (10 : ZMod 709871857) ^ 9) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 426128788 := by rw [factor_2_3]; decide
      have factor_2_5 : (10 : ZMod 709871857) ^ 39 = 501390778 := by
        calc
          (10 : ZMod 709871857) ^ 39 = (10 : ZMod 709871857) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 19 * (10 : ZMod 709871857) ^ 19) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 501390778 := by rw [factor_2_4]; decide
      have factor_2_6 : (10 : ZMod 709871857) ^ 79 = 544899495 := by
        calc
          (10 : ZMod 709871857) ^ 79 = (10 : ZMod 709871857) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 39 * (10 : ZMod 709871857) ^ 39) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 544899495 := by rw [factor_2_5]; decide
      have factor_2_7 : (10 : ZMod 709871857) ^ 159 = 249424076 := by
        calc
          (10 : ZMod 709871857) ^ 159 = (10 : ZMod 709871857) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 79 * (10 : ZMod 709871857) ^ 79) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 249424076 := by rw [factor_2_6]; decide
      have factor_2_8 : (10 : ZMod 709871857) ^ 318 = 166556615 := by
        calc
          (10 : ZMod 709871857) ^ 318 = (10 : ZMod 709871857) ^ (159 + 159) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 159 * (10 : ZMod 709871857) ^ 159 := by rw [pow_add]
          _ = 166556615 := by rw [factor_2_7]; decide
      have factor_2_9 : (10 : ZMod 709871857) ^ 637 = 618223869 := by
        calc
          (10 : ZMod 709871857) ^ 637 = (10 : ZMod 709871857) ^ (318 + 318 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 318 * (10 : ZMod 709871857) ^ 318) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 618223869 := by rw [factor_2_8]; decide
      have factor_2_10 : (10 : ZMod 709871857) ^ 1274 = 109462317 := by
        calc
          (10 : ZMod 709871857) ^ 1274 = (10 : ZMod 709871857) ^ (637 + 637) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 637 * (10 : ZMod 709871857) ^ 637 := by rw [pow_add]
          _ = 109462317 := by rw [factor_2_9]; decide
      have factor_2_11 : (10 : ZMod 709871857) ^ 2548 = 71647932 := by
        calc
          (10 : ZMod 709871857) ^ 2548 = (10 : ZMod 709871857) ^ (1274 + 1274) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 1274 * (10 : ZMod 709871857) ^ 1274 := by rw [pow_add]
          _ = 71647932 := by rw [factor_2_10]; decide
      have factor_2_12 : (10 : ZMod 709871857) ^ 5097 = 357770644 := by
        calc
          (10 : ZMod 709871857) ^ 5097 = (10 : ZMod 709871857) ^ (2548 + 2548 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 2548 * (10 : ZMod 709871857) ^ 2548) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 357770644 := by rw [factor_2_11]; decide
      have factor_2_13 : (10 : ZMod 709871857) ^ 10194 = 394948593 := by
        calc
          (10 : ZMod 709871857) ^ 10194 = (10 : ZMod 709871857) ^ (5097 + 5097) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 5097 * (10 : ZMod 709871857) ^ 5097 := by rw [pow_add]
          _ = 394948593 := by rw [factor_2_12]; decide
      have factor_2_14 : (10 : ZMod 709871857) ^ 20389 = 298901753 := by
        calc
          (10 : ZMod 709871857) ^ 20389 = (10 : ZMod 709871857) ^ (10194 + 10194 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 10194 * (10 : ZMod 709871857) ^ 10194) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 298901753 := by rw [factor_2_13]; decide
      have factor_2_15 : (10 : ZMod 709871857) ^ 40778 = 114774992 := by
        calc
          (10 : ZMod 709871857) ^ 40778 = (10 : ZMod 709871857) ^ (20389 + 20389) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 20389 * (10 : ZMod 709871857) ^ 20389 := by rw [pow_add]
          _ = 114774992 := by rw [factor_2_14]; decide
      have factor_2_16 : (10 : ZMod 709871857) ^ 81556 = 165540677 := by
        calc
          (10 : ZMod 709871857) ^ 81556 = (10 : ZMod 709871857) ^ (40778 + 40778) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 40778 * (10 : ZMod 709871857) ^ 40778 := by rw [pow_add]
          _ = 165540677 := by rw [factor_2_15]; decide
      have factor_2_17 : (10 : ZMod 709871857) ^ 163113 = 419545790 := by
        calc
          (10 : ZMod 709871857) ^ 163113 = (10 : ZMod 709871857) ^ (81556 + 81556 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 81556 * (10 : ZMod 709871857) ^ 81556) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 419545790 := by rw [factor_2_16]; decide
      have factor_2_18 : (10 : ZMod 709871857) ^ 326227 = 583616674 := by
        calc
          (10 : ZMod 709871857) ^ 326227 = (10 : ZMod 709871857) ^ (163113 + 163113 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 163113 * (10 : ZMod 709871857) ^ 163113) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 583616674 := by rw [factor_2_17]; decide
      have factor_2_19 : (10 : ZMod 709871857) ^ 652455 = 632829004 := by
        calc
          (10 : ZMod 709871857) ^ 652455 = (10 : ZMod 709871857) ^ (326227 + 326227 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 326227 * (10 : ZMod 709871857) ^ 326227) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 632829004 := by rw [factor_2_18]; decide
      have factor_2_20 : (10 : ZMod 709871857) ^ 1304911 = 704452391 := by
        calc
          (10 : ZMod 709871857) ^ 1304911 = (10 : ZMod 709871857) ^ (652455 + 652455 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 652455 * (10 : ZMod 709871857) ^ 652455) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 704452391 := by rw [factor_2_19]; decide
      have factor_2_21 : (10 : ZMod 709871857) ^ 2609823 = 185777095 := by
        calc
          (10 : ZMod 709871857) ^ 2609823 = (10 : ZMod 709871857) ^ (1304911 + 1304911 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 1304911 * (10 : ZMod 709871857) ^ 1304911) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 185777095 := by rw [factor_2_20]; decide
      have factor_2_22 : (10 : ZMod 709871857) ^ 5219646 = 537449570 := by
        calc
          (10 : ZMod 709871857) ^ 5219646 = (10 : ZMod 709871857) ^ (2609823 + 2609823) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 2609823 * (10 : ZMod 709871857) ^ 2609823 := by rw [pow_add]
          _ = 537449570 := by rw [factor_2_21]; decide
      have factor_2_23 : (10 : ZMod 709871857) ^ 10439292 = 325200657 := by
        calc
          (10 : ZMod 709871857) ^ 10439292 = (10 : ZMod 709871857) ^ (5219646 + 5219646) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 5219646 * (10 : ZMod 709871857) ^ 5219646 := by rw [pow_add]
          _ = 325200657 := by rw [factor_2_22]; decide
      have factor_2_24 : (10 : ZMod 709871857) ^ 20878584 = 333121399 := by
        calc
          (10 : ZMod 709871857) ^ 20878584 = (10 : ZMod 709871857) ^ (10439292 + 10439292) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 10439292 * (10 : ZMod 709871857) ^ 10439292 := by rw [pow_add]
          _ = 333121399 := by rw [factor_2_23]; decide
      have factor_2_25 : (10 : ZMod 709871857) ^ 41757168 = 272420601 := by
        calc
          (10 : ZMod 709871857) ^ 41757168 = (10 : ZMod 709871857) ^ (20878584 + 20878584) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 20878584 * (10 : ZMod 709871857) ^ 20878584 := by rw [pow_add]
          _ = 272420601 := by rw [factor_2_24]; decide
      change (10 : ZMod 709871857) ^ 41757168 ≠ 1
      rw [factor_2_25]
      decide
    ·
      have factor_3_0 : (10 : ZMod 709871857) ^ 1 = 10 := by norm_num
      have factor_3_1 : (10 : ZMod 709871857) ^ 2 = 100 := by
        calc
          (10 : ZMod 709871857) ^ 2 = (10 : ZMod 709871857) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 1 * (10 : ZMod 709871857) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_3_0]; decide
      have factor_3_2 : (10 : ZMod 709871857) ^ 4 = 10000 := by
        calc
          (10 : ZMod 709871857) ^ 4 = (10 : ZMod 709871857) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 2 * (10 : ZMod 709871857) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [factor_3_1]; decide
      have factor_3_3 : (10 : ZMod 709871857) ^ 9 = 290128143 := by
        calc
          (10 : ZMod 709871857) ^ 9 = (10 : ZMod 709871857) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 4 * (10 : ZMod 709871857) ^ 4) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 290128143 := by rw [factor_3_2]; decide
      have factor_3_4 : (10 : ZMod 709871857) ^ 18 = 468535993 := by
        calc
          (10 : ZMod 709871857) ^ 18 = (10 : ZMod 709871857) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 9 * (10 : ZMod 709871857) ^ 9 := by rw [pow_add]
          _ = 468535993 := by rw [factor_3_3]; decide
      have factor_3_5 : (10 : ZMod 709871857) ^ 37 = 331554962 := by
        calc
          (10 : ZMod 709871857) ^ 37 = (10 : ZMod 709871857) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 18 * (10 : ZMod 709871857) ^ 18) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 331554962 := by rw [factor_3_4]; decide
      have factor_3_6 : (10 : ZMod 709871857) ^ 74 = 649289743 := by
        calc
          (10 : ZMod 709871857) ^ 74 = (10 : ZMod 709871857) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 37 * (10 : ZMod 709871857) ^ 37 := by rw [pow_add]
          _ = 649289743 := by rw [factor_3_5]; decide
      have factor_3_7 : (10 : ZMod 709871857) ^ 148 = 283954170 := by
        calc
          (10 : ZMod 709871857) ^ 148 = (10 : ZMod 709871857) ^ (74 + 74) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 74 * (10 : ZMod 709871857) ^ 74 := by rw [pow_add]
          _ = 283954170 := by rw [factor_3_6]; decide
      have factor_3_8 : (10 : ZMod 709871857) ^ 296 = 654141734 := by
        calc
          (10 : ZMod 709871857) ^ 296 = (10 : ZMod 709871857) ^ (148 + 148) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 148 * (10 : ZMod 709871857) ^ 148 := by rw [pow_add]
          _ = 654141734 := by rw [factor_3_7]; decide
      have factor_3_9 : (10 : ZMod 709871857) ^ 593 = 695909892 := by
        calc
          (10 : ZMod 709871857) ^ 593 = (10 : ZMod 709871857) ^ (296 + 296 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 296 * (10 : ZMod 709871857) ^ 296) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 695909892 := by rw [factor_3_8]; decide
      have factor_3_10 : (10 : ZMod 709871857) ^ 1187 = 467413547 := by
        calc
          (10 : ZMod 709871857) ^ 1187 = (10 : ZMod 709871857) ^ (593 + 593 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 593 * (10 : ZMod 709871857) ^ 593) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 467413547 := by rw [factor_3_9]; decide
      have factor_3_11 : (10 : ZMod 709871857) ^ 2374 = 348468982 := by
        calc
          (10 : ZMod 709871857) ^ 2374 = (10 : ZMod 709871857) ^ (1187 + 1187) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 1187 * (10 : ZMod 709871857) ^ 1187 := by rw [pow_add]
          _ = 348468982 := by rw [factor_3_10]; decide
      have factor_3_12 : (10 : ZMod 709871857) ^ 4748 = 538854457 := by
        calc
          (10 : ZMod 709871857) ^ 4748 = (10 : ZMod 709871857) ^ (2374 + 2374) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 2374 * (10 : ZMod 709871857) ^ 2374 := by rw [pow_add]
          _ = 538854457 := by rw [factor_3_11]; decide
      have factor_3_13 : (10 : ZMod 709871857) ^ 9496 = 595878332 := by
        calc
          (10 : ZMod 709871857) ^ 9496 = (10 : ZMod 709871857) ^ (4748 + 4748) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 4748 * (10 : ZMod 709871857) ^ 4748 := by rw [pow_add]
          _ = 595878332 := by rw [factor_3_12]; decide
      have factor_3_14 : (10 : ZMod 709871857) ^ 18992 = 667076832 := by
        calc
          (10 : ZMod 709871857) ^ 18992 = (10 : ZMod 709871857) ^ (9496 + 9496) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 9496 * (10 : ZMod 709871857) ^ 9496 := by rw [pow_add]
          _ = 667076832 := by rw [factor_3_13]; decide
      have factor_3_15 : (10 : ZMod 709871857) ^ 37985 = 17210996 := by
        calc
          (10 : ZMod 709871857) ^ 37985 = (10 : ZMod 709871857) ^ (18992 + 18992 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 18992 * (10 : ZMod 709871857) ^ 18992) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 17210996 := by rw [factor_3_14]; decide
      have factor_3_16 : (10 : ZMod 709871857) ^ 75970 = 215335628 := by
        calc
          (10 : ZMod 709871857) ^ 75970 = (10 : ZMod 709871857) ^ (37985 + 37985) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 37985 * (10 : ZMod 709871857) ^ 37985 := by rw [pow_add]
          _ = 215335628 := by rw [factor_3_15]; decide
      have factor_3_17 : (10 : ZMod 709871857) ^ 151941 = 217590482 := by
        calc
          (10 : ZMod 709871857) ^ 151941 = (10 : ZMod 709871857) ^ (75970 + 75970 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 75970 * (10 : ZMod 709871857) ^ 75970) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 217590482 := by rw [factor_3_16]; decide
      have factor_3_18 : (10 : ZMod 709871857) ^ 303883 = 103276249 := by
        calc
          (10 : ZMod 709871857) ^ 303883 = (10 : ZMod 709871857) ^ (151941 + 151941 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 151941 * (10 : ZMod 709871857) ^ 151941) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 103276249 := by rw [factor_3_17]; decide
      have factor_3_19 : (10 : ZMod 709871857) ^ 607767 = 157762187 := by
        calc
          (10 : ZMod 709871857) ^ 607767 = (10 : ZMod 709871857) ^ (303883 + 303883 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 303883 * (10 : ZMod 709871857) ^ 303883) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 157762187 := by rw [factor_3_18]; decide
      have factor_3_20 : (10 : ZMod 709871857) ^ 1215534 = 315020130 := by
        calc
          (10 : ZMod 709871857) ^ 1215534 = (10 : ZMod 709871857) ^ (607767 + 607767) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 607767 * (10 : ZMod 709871857) ^ 607767 := by rw [pow_add]
          _ = 315020130 := by rw [factor_3_19]; decide
      have factor_3_21 : (10 : ZMod 709871857) ^ 2431068 = 322724702 := by
        calc
          (10 : ZMod 709871857) ^ 2431068 = (10 : ZMod 709871857) ^ (1215534 + 1215534) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 1215534 * (10 : ZMod 709871857) ^ 1215534 := by rw [pow_add]
          _ = 322724702 := by rw [factor_3_20]; decide
      have factor_3_22 : (10 : ZMod 709871857) ^ 4862136 = 31537998 := by
        calc
          (10 : ZMod 709871857) ^ 4862136 = (10 : ZMod 709871857) ^ (2431068 + 2431068) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 2431068 * (10 : ZMod 709871857) ^ 2431068 := by rw [pow_add]
          _ = 31537998 := by rw [factor_3_21]; decide
      have factor_3_23 : (10 : ZMod 709871857) ^ 9724272 = 556822027 := by
        calc
          (10 : ZMod 709871857) ^ 9724272 = (10 : ZMod 709871857) ^ (4862136 + 4862136) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 4862136 * (10 : ZMod 709871857) ^ 4862136 := by rw [pow_add]
          _ = 556822027 := by rw [factor_3_22]; decide
      change (10 : ZMod 709871857) ^ 9724272 ≠ 1
      rw [factor_3_23]
      decide
    ·
      have factor_4_0 : (10 : ZMod 709871857) ^ 1 = 10 := by norm_num
      have factor_4_1 : (10 : ZMod 709871857) ^ 3 = 1000 := by
        calc
          (10 : ZMod 709871857) ^ 3 = (10 : ZMod 709871857) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 1 * (10 : ZMod 709871857) ^ 1) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_4_0]; decide
      have factor_4_2 : (10 : ZMod 709871857) ^ 7 = 10000000 := by
        calc
          (10 : ZMod 709871857) ^ 7 = (10 : ZMod 709871857) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 3 * (10 : ZMod 709871857) ^ 3) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 10000000 := by rw [factor_4_1]; decide
      have factor_4_3 : (10 : ZMod 709871857) ^ 15 = 675556672 := by
        calc
          (10 : ZMod 709871857) ^ 15 = (10 : ZMod 709871857) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 7 * (10 : ZMod 709871857) ^ 7) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 675556672 := by rw [factor_4_2]; decide
      have factor_4_4 : (10 : ZMod 709871857) ^ 30 = 34551910 := by
        calc
          (10 : ZMod 709871857) ^ 30 = (10 : ZMod 709871857) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 15 * (10 : ZMod 709871857) ^ 15 := by rw [pow_add]
          _ = 34551910 := by rw [factor_4_3]; decide
      have factor_4_5 : (10 : ZMod 709871857) ^ 61 = 354838515 := by
        calc
          (10 : ZMod 709871857) ^ 61 = (10 : ZMod 709871857) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 30 * (10 : ZMod 709871857) ^ 30) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 354838515 := by rw [factor_4_4]; decide
      have factor_4_6 : (10 : ZMod 709871857) ^ 123 = 126006913 := by
        calc
          (10 : ZMod 709871857) ^ 123 = (10 : ZMod 709871857) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 61 * (10 : ZMod 709871857) ^ 61) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 126006913 := by rw [factor_4_5]; decide
      have factor_4_7 : (10 : ZMod 709871857) ^ 247 = 361774767 := by
        calc
          (10 : ZMod 709871857) ^ 247 = (10 : ZMod 709871857) ^ (123 + 123 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 123 * (10 : ZMod 709871857) ^ 123) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 361774767 := by rw [factor_4_6]; decide
      have factor_4_8 : (10 : ZMod 709871857) ^ 494 = 337134530 := by
        calc
          (10 : ZMod 709871857) ^ 494 = (10 : ZMod 709871857) ^ (247 + 247) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 247 * (10 : ZMod 709871857) ^ 247 := by rw [pow_add]
          _ = 337134530 := by rw [factor_4_7]; decide
      have factor_4_9 : (10 : ZMod 709871857) ^ 988 = 684507467 := by
        calc
          (10 : ZMod 709871857) ^ 988 = (10 : ZMod 709871857) ^ (494 + 494) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 494 * (10 : ZMod 709871857) ^ 494 := by rw [pow_add]
          _ = 684507467 := by rw [factor_4_8]; decide
      have factor_4_10 : (10 : ZMod 709871857) ^ 1977 = 302400705 := by
        calc
          (10 : ZMod 709871857) ^ 1977 = (10 : ZMod 709871857) ^ (988 + 988 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 988 * (10 : ZMod 709871857) ^ 988) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 302400705 := by rw [factor_4_9]; decide
      have factor_4_11 : (10 : ZMod 709871857) ^ 3955 = 498804815 := by
        calc
          (10 : ZMod 709871857) ^ 3955 = (10 : ZMod 709871857) ^ (1977 + 1977 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 1977 * (10 : ZMod 709871857) ^ 1977) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 498804815 := by rw [factor_4_10]; decide
      have factor_4_12 : (10 : ZMod 709871857) ^ 7911 = 540589803 := by
        calc
          (10 : ZMod 709871857) ^ 7911 = (10 : ZMod 709871857) ^ (3955 + 3955 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 3955 * (10 : ZMod 709871857) ^ 3955) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 540589803 := by rw [factor_4_11]; decide
      have factor_4_13 : (10 : ZMod 709871857) ^ 15822 = 18440692 := by
        calc
          (10 : ZMod 709871857) ^ 15822 = (10 : ZMod 709871857) ^ (7911 + 7911) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 7911 * (10 : ZMod 709871857) ^ 7911 := by rw [pow_add]
          _ = 18440692 := by rw [factor_4_12]; decide
      have factor_4_14 : (10 : ZMod 709871857) ^ 31645 = 484331987 := by
        calc
          (10 : ZMod 709871857) ^ 31645 = (10 : ZMod 709871857) ^ (15822 + 15822 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 15822 * (10 : ZMod 709871857) ^ 15822) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 484331987 := by rw [factor_4_13]; decide
      have factor_4_15 : (10 : ZMod 709871857) ^ 63291 = 372031188 := by
        calc
          (10 : ZMod 709871857) ^ 63291 = (10 : ZMod 709871857) ^ (31645 + 31645 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = ((10 : ZMod 709871857) ^ 31645 * (10 : ZMod 709871857) ^ 31645) * (10 : ZMod 709871857) := by rw [pow_succ, pow_add]
          _ = 372031188 := by rw [factor_4_14]; decide
      have factor_4_16 : (10 : ZMod 709871857) ^ 126582 = 575096046 := by
        calc
          (10 : ZMod 709871857) ^ 126582 = (10 : ZMod 709871857) ^ (63291 + 63291) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 63291 * (10 : ZMod 709871857) ^ 63291 := by rw [pow_add]
          _ = 575096046 := by rw [factor_4_15]; decide
      have factor_4_17 : (10 : ZMod 709871857) ^ 253164 = 131199785 := by
        calc
          (10 : ZMod 709871857) ^ 253164 = (10 : ZMod 709871857) ^ (126582 + 126582) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 126582 * (10 : ZMod 709871857) ^ 126582 := by rw [pow_add]
          _ = 131199785 := by rw [factor_4_16]; decide
      have factor_4_18 : (10 : ZMod 709871857) ^ 506328 = 489576879 := by
        calc
          (10 : ZMod 709871857) ^ 506328 = (10 : ZMod 709871857) ^ (253164 + 253164) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 253164 * (10 : ZMod 709871857) ^ 253164 := by rw [pow_add]
          _ = 489576879 := by rw [factor_4_17]; decide
      have factor_4_19 : (10 : ZMod 709871857) ^ 1012656 = 355696238 := by
        calc
          (10 : ZMod 709871857) ^ 1012656 = (10 : ZMod 709871857) ^ (506328 + 506328) :=
            congrArg (fun n : ℕ => (10 : ZMod 709871857) ^ n) (by norm_num)
          _ = (10 : ZMod 709871857) ^ 506328 * (10 : ZMod 709871857) ^ 506328 := by rw [pow_add]
          _ = 355696238 := by rw [factor_4_18]; decide
      change (10 : ZMod 709871857) ^ 1012656 ≠ 1
      rw [factor_4_19]
      decide

#print axioms prime_lucas_709871857

end TotientTailPeriodKiller
end Erdos249257
