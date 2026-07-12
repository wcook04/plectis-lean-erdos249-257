import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=23 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_43707991 : Nat.Prime 43707991 := by
  apply lucas_primality 43707991 (3 : ZMod 43707991)
  ·
      have fermat_0 : (3 : ZMod 43707991) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 43707991) ^ 2 = 9 := by
        calc
          (3 : ZMod 43707991) ^ 2 = (3 : ZMod 43707991) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 1 * (3 : ZMod 43707991) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 43707991) ^ 5 = 243 := by
        calc
          (3 : ZMod 43707991) ^ 5 = (3 : ZMod 43707991) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 2 * (3 : ZMod 43707991) ^ 2) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 43707991) ^ 10 = 59049 := by
        calc
          (3 : ZMod 43707991) ^ 10 = (3 : ZMod 43707991) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 5 * (3 : ZMod 43707991) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 43707991) ^ 20 = 33853112 := by
        calc
          (3 : ZMod 43707991) ^ 20 = (3 : ZMod 43707991) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 10 * (3 : ZMod 43707991) ^ 10 := by rw [pow_add]
          _ = 33853112 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 43707991) ^ 41 = 25795599 := by
        calc
          (3 : ZMod 43707991) ^ 41 = (3 : ZMod 43707991) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 20 * (3 : ZMod 43707991) ^ 20) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 25795599 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 43707991) ^ 83 = 31703924 := by
        calc
          (3 : ZMod 43707991) ^ 83 = (3 : ZMod 43707991) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 41 * (3 : ZMod 43707991) ^ 41) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 31703924 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 43707991) ^ 166 = 27111914 := by
        calc
          (3 : ZMod 43707991) ^ 166 = (3 : ZMod 43707991) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 83 * (3 : ZMod 43707991) ^ 83 := by rw [pow_add]
          _ = 27111914 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 43707991) ^ 333 = 16892672 := by
        calc
          (3 : ZMod 43707991) ^ 333 = (3 : ZMod 43707991) ^ (166 + 166 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 166 * (3 : ZMod 43707991) ^ 166) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 16892672 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 43707991) ^ 666 = 18463117 := by
        calc
          (3 : ZMod 43707991) ^ 666 = (3 : ZMod 43707991) ^ (333 + 333) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 333 * (3 : ZMod 43707991) ^ 333 := by rw [pow_add]
          _ = 18463117 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 43707991) ^ 1333 = 32121044 := by
        calc
          (3 : ZMod 43707991) ^ 1333 = (3 : ZMod 43707991) ^ (666 + 666 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 666 * (3 : ZMod 43707991) ^ 666) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 32121044 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 43707991) ^ 2667 = 550021 := by
        calc
          (3 : ZMod 43707991) ^ 2667 = (3 : ZMod 43707991) ^ (1333 + 1333 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 1333 * (3 : ZMod 43707991) ^ 1333) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 550021 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 43707991) ^ 5335 = 16576199 := by
        calc
          (3 : ZMod 43707991) ^ 5335 = (3 : ZMod 43707991) ^ (2667 + 2667 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 2667 * (3 : ZMod 43707991) ^ 2667) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 16576199 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 43707991) ^ 10670 = 450119 := by
        calc
          (3 : ZMod 43707991) ^ 10670 = (3 : ZMod 43707991) ^ (5335 + 5335) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 5335 * (3 : ZMod 43707991) ^ 5335 := by rw [pow_add]
          _ = 450119 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 43707991) ^ 21341 = 18019637 := by
        calc
          (3 : ZMod 43707991) ^ 21341 = (3 : ZMod 43707991) ^ (10670 + 10670 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 10670 * (3 : ZMod 43707991) ^ 10670) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 18019637 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 43707991) ^ 42683 = 34266703 := by
        calc
          (3 : ZMod 43707991) ^ 42683 = (3 : ZMod 43707991) ^ (21341 + 21341 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 21341 * (3 : ZMod 43707991) ^ 21341) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 34266703 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 43707991) ^ 85367 = 7548533 := by
        calc
          (3 : ZMod 43707991) ^ 85367 = (3 : ZMod 43707991) ^ (42683 + 42683 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 42683 * (3 : ZMod 43707991) ^ 42683) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 7548533 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 43707991) ^ 170734 = 34613020 := by
        calc
          (3 : ZMod 43707991) ^ 170734 = (3 : ZMod 43707991) ^ (85367 + 85367) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 85367 * (3 : ZMod 43707991) ^ 85367 := by rw [pow_add]
          _ = 34613020 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 43707991) ^ 341468 = 31823566 := by
        calc
          (3 : ZMod 43707991) ^ 341468 = (3 : ZMod 43707991) ^ (170734 + 170734) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 170734 * (3 : ZMod 43707991) ^ 170734 := by rw [pow_add]
          _ = 31823566 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 43707991) ^ 682937 = 33342629 := by
        calc
          (3 : ZMod 43707991) ^ 682937 = (3 : ZMod 43707991) ^ (341468 + 341468 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 341468 * (3 : ZMod 43707991) ^ 341468) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 33342629 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 43707991) ^ 1365874 = 18730376 := by
        calc
          (3 : ZMod 43707991) ^ 1365874 = (3 : ZMod 43707991) ^ (682937 + 682937) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 682937 * (3 : ZMod 43707991) ^ 682937 := by rw [pow_add]
          _ = 18730376 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 43707991) ^ 2731749 = 6090589 := by
        calc
          (3 : ZMod 43707991) ^ 2731749 = (3 : ZMod 43707991) ^ (1365874 + 1365874 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 1365874 * (3 : ZMod 43707991) ^ 1365874) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 6090589 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 43707991) ^ 5463498 = 40157275 := by
        calc
          (3 : ZMod 43707991) ^ 5463498 = (3 : ZMod 43707991) ^ (2731749 + 2731749) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 2731749 * (3 : ZMod 43707991) ^ 2731749 := by rw [pow_add]
          _ = 40157275 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 43707991) ^ 10926997 = 42326118 := by
        calc
          (3 : ZMod 43707991) ^ 10926997 = (3 : ZMod 43707991) ^ (5463498 + 5463498 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 5463498 * (3 : ZMod 43707991) ^ 5463498) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 42326118 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 43707991) ^ 21853995 = 43707990 := by
        calc
          (3 : ZMod 43707991) ^ 21853995 = (3 : ZMod 43707991) ^ (10926997 + 10926997 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 10926997 * (3 : ZMod 43707991) ^ 10926997) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 43707990 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 43707991) ^ 43707990 = 1 := by
        calc
          (3 : ZMod 43707991) ^ 43707990 = (3 : ZMod 43707991) ^ (21853995 + 21853995) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 21853995 * (3 : ZMod 43707991) ^ 21853995 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (257, 1), (5669, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (257, 1), (5669, 1)] : List FactorBlock).map factorBlockValue).prod = 43707991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 43707991) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 43707991) ^ 2 = 9 := by
        calc
          (3 : ZMod 43707991) ^ 2 = (3 : ZMod 43707991) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 1 * (3 : ZMod 43707991) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 43707991) ^ 5 = 243 := by
        calc
          (3 : ZMod 43707991) ^ 5 = (3 : ZMod 43707991) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 2 * (3 : ZMod 43707991) ^ 2) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 43707991) ^ 10 = 59049 := by
        calc
          (3 : ZMod 43707991) ^ 10 = (3 : ZMod 43707991) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 5 * (3 : ZMod 43707991) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 43707991) ^ 20 = 33853112 := by
        calc
          (3 : ZMod 43707991) ^ 20 = (3 : ZMod 43707991) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 10 * (3 : ZMod 43707991) ^ 10 := by rw [pow_add]
          _ = 33853112 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 43707991) ^ 41 = 25795599 := by
        calc
          (3 : ZMod 43707991) ^ 41 = (3 : ZMod 43707991) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 20 * (3 : ZMod 43707991) ^ 20) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 25795599 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 43707991) ^ 83 = 31703924 := by
        calc
          (3 : ZMod 43707991) ^ 83 = (3 : ZMod 43707991) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 41 * (3 : ZMod 43707991) ^ 41) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 31703924 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 43707991) ^ 166 = 27111914 := by
        calc
          (3 : ZMod 43707991) ^ 166 = (3 : ZMod 43707991) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 83 * (3 : ZMod 43707991) ^ 83 := by rw [pow_add]
          _ = 27111914 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 43707991) ^ 333 = 16892672 := by
        calc
          (3 : ZMod 43707991) ^ 333 = (3 : ZMod 43707991) ^ (166 + 166 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 166 * (3 : ZMod 43707991) ^ 166) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 16892672 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 43707991) ^ 666 = 18463117 := by
        calc
          (3 : ZMod 43707991) ^ 666 = (3 : ZMod 43707991) ^ (333 + 333) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 333 * (3 : ZMod 43707991) ^ 333 := by rw [pow_add]
          _ = 18463117 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 43707991) ^ 1333 = 32121044 := by
        calc
          (3 : ZMod 43707991) ^ 1333 = (3 : ZMod 43707991) ^ (666 + 666 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 666 * (3 : ZMod 43707991) ^ 666) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 32121044 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 43707991) ^ 2667 = 550021 := by
        calc
          (3 : ZMod 43707991) ^ 2667 = (3 : ZMod 43707991) ^ (1333 + 1333 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 1333 * (3 : ZMod 43707991) ^ 1333) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 550021 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 43707991) ^ 5335 = 16576199 := by
        calc
          (3 : ZMod 43707991) ^ 5335 = (3 : ZMod 43707991) ^ (2667 + 2667 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 2667 * (3 : ZMod 43707991) ^ 2667) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 16576199 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 43707991) ^ 10670 = 450119 := by
        calc
          (3 : ZMod 43707991) ^ 10670 = (3 : ZMod 43707991) ^ (5335 + 5335) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 5335 * (3 : ZMod 43707991) ^ 5335 := by rw [pow_add]
          _ = 450119 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 43707991) ^ 21341 = 18019637 := by
        calc
          (3 : ZMod 43707991) ^ 21341 = (3 : ZMod 43707991) ^ (10670 + 10670 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 10670 * (3 : ZMod 43707991) ^ 10670) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 18019637 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 43707991) ^ 42683 = 34266703 := by
        calc
          (3 : ZMod 43707991) ^ 42683 = (3 : ZMod 43707991) ^ (21341 + 21341 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 21341 * (3 : ZMod 43707991) ^ 21341) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 34266703 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 43707991) ^ 85367 = 7548533 := by
        calc
          (3 : ZMod 43707991) ^ 85367 = (3 : ZMod 43707991) ^ (42683 + 42683 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 42683 * (3 : ZMod 43707991) ^ 42683) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 7548533 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 43707991) ^ 170734 = 34613020 := by
        calc
          (3 : ZMod 43707991) ^ 170734 = (3 : ZMod 43707991) ^ (85367 + 85367) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 85367 * (3 : ZMod 43707991) ^ 85367 := by rw [pow_add]
          _ = 34613020 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 43707991) ^ 341468 = 31823566 := by
        calc
          (3 : ZMod 43707991) ^ 341468 = (3 : ZMod 43707991) ^ (170734 + 170734) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 170734 * (3 : ZMod 43707991) ^ 170734 := by rw [pow_add]
          _ = 31823566 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 43707991) ^ 682937 = 33342629 := by
        calc
          (3 : ZMod 43707991) ^ 682937 = (3 : ZMod 43707991) ^ (341468 + 341468 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 341468 * (3 : ZMod 43707991) ^ 341468) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 33342629 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 43707991) ^ 1365874 = 18730376 := by
        calc
          (3 : ZMod 43707991) ^ 1365874 = (3 : ZMod 43707991) ^ (682937 + 682937) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 682937 * (3 : ZMod 43707991) ^ 682937 := by rw [pow_add]
          _ = 18730376 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 43707991) ^ 2731749 = 6090589 := by
        calc
          (3 : ZMod 43707991) ^ 2731749 = (3 : ZMod 43707991) ^ (1365874 + 1365874 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 1365874 * (3 : ZMod 43707991) ^ 1365874) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 6090589 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 43707991) ^ 5463498 = 40157275 := by
        calc
          (3 : ZMod 43707991) ^ 5463498 = (3 : ZMod 43707991) ^ (2731749 + 2731749) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 2731749 * (3 : ZMod 43707991) ^ 2731749 := by rw [pow_add]
          _ = 40157275 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 43707991) ^ 10926997 = 42326118 := by
        calc
          (3 : ZMod 43707991) ^ 10926997 = (3 : ZMod 43707991) ^ (5463498 + 5463498 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 5463498 * (3 : ZMod 43707991) ^ 5463498) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 42326118 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 43707991) ^ 21853995 = 43707990 := by
        calc
          (3 : ZMod 43707991) ^ 21853995 = (3 : ZMod 43707991) ^ (10926997 + 10926997 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 10926997 * (3 : ZMod 43707991) ^ 10926997) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 43707990 := by rw [factor_0_23]; decide
      change (3 : ZMod 43707991) ^ 21853995 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (3 : ZMod 43707991) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 43707991) ^ 3 = 27 := by
        calc
          (3 : ZMod 43707991) ^ 3 = (3 : ZMod 43707991) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 1 * (3 : ZMod 43707991) ^ 1) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 43707991) ^ 6 = 729 := by
        calc
          (3 : ZMod 43707991) ^ 6 = (3 : ZMod 43707991) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 3 * (3 : ZMod 43707991) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 43707991) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 43707991) ^ 13 = (3 : ZMod 43707991) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 6 * (3 : ZMod 43707991) ^ 6) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 43707991) ^ 27 = 39127181 := by
        calc
          (3 : ZMod 43707991) ^ 27 = (3 : ZMod 43707991) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 13 * (3 : ZMod 43707991) ^ 13) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 39127181 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 43707991) ^ 55 = 21446757 := by
        calc
          (3 : ZMod 43707991) ^ 55 = (3 : ZMod 43707991) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 27 * (3 : ZMod 43707991) ^ 27) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 21446757 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 43707991) ^ 111 = 34307087 := by
        calc
          (3 : ZMod 43707991) ^ 111 = (3 : ZMod 43707991) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 55 * (3 : ZMod 43707991) ^ 55) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 34307087 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 43707991) ^ 222 = 6419099 := by
        calc
          (3 : ZMod 43707991) ^ 222 = (3 : ZMod 43707991) ^ (111 + 111) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 111 * (3 : ZMod 43707991) ^ 111 := by rw [pow_add]
          _ = 6419099 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 43707991) ^ 444 = 41324362 := by
        calc
          (3 : ZMod 43707991) ^ 444 = (3 : ZMod 43707991) ^ (222 + 222) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 222 * (3 : ZMod 43707991) ^ 222 := by rw [pow_add]
          _ = 41324362 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 43707991) ^ 889 = 37838698 := by
        calc
          (3 : ZMod 43707991) ^ 889 = (3 : ZMod 43707991) ^ (444 + 444 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 444 * (3 : ZMod 43707991) ^ 444) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 37838698 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 43707991) ^ 1778 = 16089226 := by
        calc
          (3 : ZMod 43707991) ^ 1778 = (3 : ZMod 43707991) ^ (889 + 889) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 889 * (3 : ZMod 43707991) ^ 889 := by rw [pow_add]
          _ = 16089226 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 43707991) ^ 3556 = 37810107 := by
        calc
          (3 : ZMod 43707991) ^ 3556 = (3 : ZMod 43707991) ^ (1778 + 1778) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 1778 * (3 : ZMod 43707991) ^ 1778 := by rw [pow_add]
          _ = 37810107 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 43707991) ^ 7113 = 5704336 := by
        calc
          (3 : ZMod 43707991) ^ 7113 = (3 : ZMod 43707991) ^ (3556 + 3556 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 3556 * (3 : ZMod 43707991) ^ 3556) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 5704336 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 43707991) ^ 14227 = 2635477 := by
        calc
          (3 : ZMod 43707991) ^ 14227 = (3 : ZMod 43707991) ^ (7113 + 7113 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 7113 * (3 : ZMod 43707991) ^ 7113) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 2635477 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 43707991) ^ 28455 = 547220 := by
        calc
          (3 : ZMod 43707991) ^ 28455 = (3 : ZMod 43707991) ^ (14227 + 14227 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 14227 * (3 : ZMod 43707991) ^ 14227) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 547220 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 43707991) ^ 56911 = 18846177 := by
        calc
          (3 : ZMod 43707991) ^ 56911 = (3 : ZMod 43707991) ^ (28455 + 28455 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 28455 * (3 : ZMod 43707991) ^ 28455) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 18846177 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 43707991) ^ 113822 = 40830814 := by
        calc
          (3 : ZMod 43707991) ^ 113822 = (3 : ZMod 43707991) ^ (56911 + 56911) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 56911 * (3 : ZMod 43707991) ^ 56911 := by rw [pow_add]
          _ = 40830814 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 43707991) ^ 227645 = 42769688 := by
        calc
          (3 : ZMod 43707991) ^ 227645 = (3 : ZMod 43707991) ^ (113822 + 113822 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 113822 * (3 : ZMod 43707991) ^ 113822) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 42769688 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 43707991) ^ 455291 = 7371288 := by
        calc
          (3 : ZMod 43707991) ^ 455291 = (3 : ZMod 43707991) ^ (227645 + 227645 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 227645 * (3 : ZMod 43707991) ^ 227645) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 7371288 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 43707991) ^ 910583 = 19142062 := by
        calc
          (3 : ZMod 43707991) ^ 910583 = (3 : ZMod 43707991) ^ (455291 + 455291 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 455291 * (3 : ZMod 43707991) ^ 455291) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 19142062 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 43707991) ^ 1821166 = 25421814 := by
        calc
          (3 : ZMod 43707991) ^ 1821166 = (3 : ZMod 43707991) ^ (910583 + 910583) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 910583 * (3 : ZMod 43707991) ^ 910583 := by rw [pow_add]
          _ = 25421814 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 43707991) ^ 3642332 = 43017055 := by
        calc
          (3 : ZMod 43707991) ^ 3642332 = (3 : ZMod 43707991) ^ (1821166 + 1821166) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 1821166 * (3 : ZMod 43707991) ^ 1821166 := by rw [pow_add]
          _ = 43017055 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 43707991) ^ 7284665 = 41635182 := by
        calc
          (3 : ZMod 43707991) ^ 7284665 = (3 : ZMod 43707991) ^ (3642332 + 3642332 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 3642332 * (3 : ZMod 43707991) ^ 3642332) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 41635182 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 43707991) ^ 14569330 = 41635181 := by
        calc
          (3 : ZMod 43707991) ^ 14569330 = (3 : ZMod 43707991) ^ (7284665 + 7284665) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 7284665 * (3 : ZMod 43707991) ^ 7284665 := by rw [pow_add]
          _ = 41635181 := by rw [factor_1_22]; decide
      change (3 : ZMod 43707991) ^ 14569330 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (3 : ZMod 43707991) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 43707991) ^ 2 = 9 := by
        calc
          (3 : ZMod 43707991) ^ 2 = (3 : ZMod 43707991) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 1 * (3 : ZMod 43707991) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 43707991) ^ 4 = 81 := by
        calc
          (3 : ZMod 43707991) ^ 4 = (3 : ZMod 43707991) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 2 * (3 : ZMod 43707991) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 43707991) ^ 8 = 6561 := by
        calc
          (3 : ZMod 43707991) ^ 8 = (3 : ZMod 43707991) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 4 * (3 : ZMod 43707991) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 43707991) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 43707991) ^ 16 = (3 : ZMod 43707991) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 8 * (3 : ZMod 43707991) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 43707991) ^ 33 = 26104817 := by
        calc
          (3 : ZMod 43707991) ^ 33 = (3 : ZMod 43707991) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 16 * (3 : ZMod 43707991) ^ 16) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 26104817 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 43707991) ^ 66 = 42668577 := by
        calc
          (3 : ZMod 43707991) ^ 66 = (3 : ZMod 43707991) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 33 * (3 : ZMod 43707991) ^ 33 := by rw [pow_add]
          _ = 42668577 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 43707991) ^ 133 = 22025574 := by
        calc
          (3 : ZMod 43707991) ^ 133 = (3 : ZMod 43707991) ^ (66 + 66 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 66 * (3 : ZMod 43707991) ^ 66) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 22025574 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 43707991) ^ 266 = 34630717 := by
        calc
          (3 : ZMod 43707991) ^ 266 = (3 : ZMod 43707991) ^ (133 + 133) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 133 * (3 : ZMod 43707991) ^ 133 := by rw [pow_add]
          _ = 34630717 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 43707991) ^ 533 = 35588755 := by
        calc
          (3 : ZMod 43707991) ^ 533 = (3 : ZMod 43707991) ^ (266 + 266 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 266 * (3 : ZMod 43707991) ^ 266) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 35588755 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 43707991) ^ 1067 = 39421469 := by
        calc
          (3 : ZMod 43707991) ^ 1067 = (3 : ZMod 43707991) ^ (533 + 533 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 533 * (3 : ZMod 43707991) ^ 533) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 39421469 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 43707991) ^ 2134 = 43351958 := by
        calc
          (3 : ZMod 43707991) ^ 2134 = (3 : ZMod 43707991) ^ (1067 + 1067) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 1067 * (3 : ZMod 43707991) ^ 1067 := by rw [pow_add]
          _ = 43351958 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 43707991) ^ 4268 = 6323189 := by
        calc
          (3 : ZMod 43707991) ^ 4268 = (3 : ZMod 43707991) ^ (2134 + 2134) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 2134 * (3 : ZMod 43707991) ^ 2134 := by rw [pow_add]
          _ = 6323189 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 43707991) ^ 8536 = 3910642 := by
        calc
          (3 : ZMod 43707991) ^ 8536 = (3 : ZMod 43707991) ^ (4268 + 4268) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 4268 * (3 : ZMod 43707991) ^ 4268 := by rw [pow_add]
          _ = 3910642 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 43707991) ^ 17073 = 2271603 := by
        calc
          (3 : ZMod 43707991) ^ 17073 = (3 : ZMod 43707991) ^ (8536 + 8536 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 8536 * (3 : ZMod 43707991) ^ 8536) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 2271603 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 43707991) ^ 34146 = 14772149 := by
        calc
          (3 : ZMod 43707991) ^ 34146 = (3 : ZMod 43707991) ^ (17073 + 17073) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 17073 * (3 : ZMod 43707991) ^ 17073 := by rw [pow_add]
          _ = 14772149 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 43707991) ^ 68293 = 4006722 := by
        calc
          (3 : ZMod 43707991) ^ 68293 = (3 : ZMod 43707991) ^ (34146 + 34146 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 34146 * (3 : ZMod 43707991) ^ 34146) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 4006722 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 43707991) ^ 136587 = 21644871 := by
        calc
          (3 : ZMod 43707991) ^ 136587 = (3 : ZMod 43707991) ^ (68293 + 68293 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 68293 * (3 : ZMod 43707991) ^ 68293) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 21644871 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 43707991) ^ 273174 = 35992498 := by
        calc
          (3 : ZMod 43707991) ^ 273174 = (3 : ZMod 43707991) ^ (136587 + 136587) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 136587 * (3 : ZMod 43707991) ^ 136587 := by rw [pow_add]
          _ = 35992498 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 43707991) ^ 546349 = 16272247 := by
        calc
          (3 : ZMod 43707991) ^ 546349 = (3 : ZMod 43707991) ^ (273174 + 273174 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 273174 * (3 : ZMod 43707991) ^ 273174) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 16272247 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 43707991) ^ 1092699 = 35006881 := by
        calc
          (3 : ZMod 43707991) ^ 1092699 = (3 : ZMod 43707991) ^ (546349 + 546349 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 546349 * (3 : ZMod 43707991) ^ 546349) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 35006881 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 43707991) ^ 2185399 = 26084665 := by
        calc
          (3 : ZMod 43707991) ^ 2185399 = (3 : ZMod 43707991) ^ (1092699 + 1092699 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 1092699 * (3 : ZMod 43707991) ^ 1092699) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 26084665 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 43707991) ^ 4370799 = 22012274 := by
        calc
          (3 : ZMod 43707991) ^ 4370799 = (3 : ZMod 43707991) ^ (2185399 + 2185399 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 2185399 * (3 : ZMod 43707991) ^ 2185399) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 22012274 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 43707991) ^ 8741598 = 18331717 := by
        calc
          (3 : ZMod 43707991) ^ 8741598 = (3 : ZMod 43707991) ^ (4370799 + 4370799) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 4370799 * (3 : ZMod 43707991) ^ 4370799 := by rw [pow_add]
          _ = 18331717 := by rw [factor_2_22]; decide
      change (3 : ZMod 43707991) ^ 8741598 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (3 : ZMod 43707991) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 43707991) ^ 2 = 9 := by
        calc
          (3 : ZMod 43707991) ^ 2 = (3 : ZMod 43707991) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 1 * (3 : ZMod 43707991) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 43707991) ^ 5 = 243 := by
        calc
          (3 : ZMod 43707991) ^ 5 = (3 : ZMod 43707991) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 2 * (3 : ZMod 43707991) ^ 2) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 43707991) ^ 10 = 59049 := by
        calc
          (3 : ZMod 43707991) ^ 10 = (3 : ZMod 43707991) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 5 * (3 : ZMod 43707991) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 43707991) ^ 20 = 33853112 := by
        calc
          (3 : ZMod 43707991) ^ 20 = (3 : ZMod 43707991) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 10 * (3 : ZMod 43707991) ^ 10 := by rw [pow_add]
          _ = 33853112 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 43707991) ^ 41 = 25795599 := by
        calc
          (3 : ZMod 43707991) ^ 41 = (3 : ZMod 43707991) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 20 * (3 : ZMod 43707991) ^ 20) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 25795599 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 43707991) ^ 83 = 31703924 := by
        calc
          (3 : ZMod 43707991) ^ 83 = (3 : ZMod 43707991) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 41 * (3 : ZMod 43707991) ^ 41) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 31703924 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 43707991) ^ 166 = 27111914 := by
        calc
          (3 : ZMod 43707991) ^ 166 = (3 : ZMod 43707991) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 83 * (3 : ZMod 43707991) ^ 83 := by rw [pow_add]
          _ = 27111914 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 43707991) ^ 332 = 20200221 := by
        calc
          (3 : ZMod 43707991) ^ 332 = (3 : ZMod 43707991) ^ (166 + 166) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 166 * (3 : ZMod 43707991) ^ 166 := by rw [pow_add]
          _ = 20200221 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 43707991) ^ 664 = 40903005 := by
        calc
          (3 : ZMod 43707991) ^ 664 = (3 : ZMod 43707991) ^ (332 + 332) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 332 * (3 : ZMod 43707991) ^ 332 := by rw [pow_add]
          _ = 40903005 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 43707991) ^ 1328 = 27292295 := by
        calc
          (3 : ZMod 43707991) ^ 1328 = (3 : ZMod 43707991) ^ (664 + 664) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 664 * (3 : ZMod 43707991) ^ 664 := by rw [pow_add]
          _ = 27292295 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 43707991) ^ 2657 = 38557698 := by
        calc
          (3 : ZMod 43707991) ^ 2657 = (3 : ZMod 43707991) ^ (1328 + 1328 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 1328 * (3 : ZMod 43707991) ^ 1328) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 38557698 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 43707991) ^ 5314 = 12407769 := by
        calc
          (3 : ZMod 43707991) ^ 5314 = (3 : ZMod 43707991) ^ (2657 + 2657) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 2657 * (3 : ZMod 43707991) ^ 2657 := by rw [pow_add]
          _ = 12407769 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 43707991) ^ 10629 = 6034228 := by
        calc
          (3 : ZMod 43707991) ^ 10629 = (3 : ZMod 43707991) ^ (5314 + 5314 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 5314 * (3 : ZMod 43707991) ^ 5314) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 6034228 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 43707991) ^ 21258 = 4077632 := by
        calc
          (3 : ZMod 43707991) ^ 21258 = (3 : ZMod 43707991) ^ (10629 + 10629) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 10629 * (3 : ZMod 43707991) ^ 10629 := by rw [pow_add]
          _ = 4077632 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 43707991) ^ 42517 = 27949414 := by
        calc
          (3 : ZMod 43707991) ^ 42517 = (3 : ZMod 43707991) ^ (21258 + 21258 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 21258 * (3 : ZMod 43707991) ^ 21258) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 27949414 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 43707991) ^ 85035 = 42522860 := by
        calc
          (3 : ZMod 43707991) ^ 85035 = (3 : ZMod 43707991) ^ (42517 + 42517 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 42517 * (3 : ZMod 43707991) ^ 42517) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 42522860 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 43707991) ^ 170070 = 22904367 := by
        calc
          (3 : ZMod 43707991) ^ 170070 = (3 : ZMod 43707991) ^ (85035 + 85035) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 85035 * (3 : ZMod 43707991) ^ 85035 := by rw [pow_add]
          _ = 22904367 := by rw [factor_3_16]; decide
      change (3 : ZMod 43707991) ^ 170070 ≠ 1
      rw [factor_3_17]
      decide
    ·
      have factor_4_0 : (3 : ZMod 43707991) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 43707991) ^ 3 = 27 := by
        calc
          (3 : ZMod 43707991) ^ 3 = (3 : ZMod 43707991) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 1 * (3 : ZMod 43707991) ^ 1) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 43707991) ^ 7 = 2187 := by
        calc
          (3 : ZMod 43707991) ^ 7 = (3 : ZMod 43707991) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 3 * (3 : ZMod 43707991) ^ 3) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 43707991) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 43707991) ^ 15 = (3 : ZMod 43707991) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 7 * (3 : ZMod 43707991) ^ 7) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 43707991) ^ 30 = 7442103 := by
        calc
          (3 : ZMod 43707991) ^ 30 = (3 : ZMod 43707991) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 15 * (3 : ZMod 43707991) ^ 15 := by rw [pow_add]
          _ = 7442103 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 43707991) ^ 60 = 10311022 := by
        calc
          (3 : ZMod 43707991) ^ 60 = (3 : ZMod 43707991) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 30 * (3 : ZMod 43707991) ^ 30 := by rw [pow_add]
          _ = 10311022 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 43707991) ^ 120 = 21640462 := by
        calc
          (3 : ZMod 43707991) ^ 120 = (3 : ZMod 43707991) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 60 * (3 : ZMod 43707991) ^ 60 := by rw [pow_add]
          _ = 21640462 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 43707991) ^ 240 = 20048007 := by
        calc
          (3 : ZMod 43707991) ^ 240 = (3 : ZMod 43707991) ^ (120 + 120) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 120 * (3 : ZMod 43707991) ^ 120 := by rw [pow_add]
          _ = 20048007 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 43707991) ^ 481 = 39346193 := by
        calc
          (3 : ZMod 43707991) ^ 481 = (3 : ZMod 43707991) ^ (240 + 240 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 240 * (3 : ZMod 43707991) ^ 240) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 39346193 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 43707991) ^ 963 = 27579008 := by
        calc
          (3 : ZMod 43707991) ^ 963 = (3 : ZMod 43707991) ^ (481 + 481 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 481 * (3 : ZMod 43707991) ^ 481) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 27579008 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 43707991) ^ 1927 = 4867240 := by
        calc
          (3 : ZMod 43707991) ^ 1927 = (3 : ZMod 43707991) ^ (963 + 963 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 963 * (3 : ZMod 43707991) ^ 963) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 4867240 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 43707991) ^ 3855 = 8126980 := by
        calc
          (3 : ZMod 43707991) ^ 3855 = (3 : ZMod 43707991) ^ (1927 + 1927 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = ((3 : ZMod 43707991) ^ 1927 * (3 : ZMod 43707991) ^ 1927) * (3 : ZMod 43707991) := by rw [pow_succ, pow_add]
          _ = 8126980 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 43707991) ^ 7710 = 3100435 := by
        calc
          (3 : ZMod 43707991) ^ 7710 = (3 : ZMod 43707991) ^ (3855 + 3855) :=
            congrArg (fun n : ℕ => (3 : ZMod 43707991) ^ n) (by norm_num)
          _ = (3 : ZMod 43707991) ^ 3855 * (3 : ZMod 43707991) ^ 3855 := by rw [pow_add]
          _ = 3100435 := by rw [factor_4_11]; decide
      change (3 : ZMod 43707991) ^ 7710 ≠ 1
      rw [factor_4_12]
      decide

#print axioms prime_lucas_43707991

end TotientTailPeriodKiller
end Erdos249257
