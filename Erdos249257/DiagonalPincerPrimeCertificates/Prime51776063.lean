import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_51776063 : Nat.Prime 51776063 := by
  apply lucas_primality 51776063 (5 : ZMod 51776063)
  ·
      have fermat_0 : (5 : ZMod 51776063) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 51776063) ^ 3 = 125 := by
        calc
          (5 : ZMod 51776063) ^ 3 = (5 : ZMod 51776063) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 1 * (5 : ZMod 51776063) ^ 1) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 51776063) ^ 6 = 15625 := by
        calc
          (5 : ZMod 51776063) ^ 6 = (5 : ZMod 51776063) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 3 * (5 : ZMod 51776063) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 51776063) ^ 12 = 37036373 := by
        calc
          (5 : ZMod 51776063) ^ 12 = (5 : ZMod 51776063) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 6 * (5 : ZMod 51776063) ^ 6 := by rw [pow_add]
          _ = 37036373 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 51776063) ^ 24 = 43148729 := by
        calc
          (5 : ZMod 51776063) ^ 24 = (5 : ZMod 51776063) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 12 * (5 : ZMod 51776063) ^ 12 := by rw [pow_add]
          _ = 43148729 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 51776063) ^ 49 = 27388270 := by
        calc
          (5 : ZMod 51776063) ^ 49 = (5 : ZMod 51776063) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 24 * (5 : ZMod 51776063) ^ 24) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 27388270 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 51776063) ^ 98 = 23042288 := by
        calc
          (5 : ZMod 51776063) ^ 98 = (5 : ZMod 51776063) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 49 * (5 : ZMod 51776063) ^ 49 := by rw [pow_add]
          _ = 23042288 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 51776063) ^ 197 = 30318079 := by
        calc
          (5 : ZMod 51776063) ^ 197 = (5 : ZMod 51776063) ^ (98 + 98 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 98 * (5 : ZMod 51776063) ^ 98) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 30318079 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 51776063) ^ 395 = 1294941 := by
        calc
          (5 : ZMod 51776063) ^ 395 = (5 : ZMod 51776063) ^ (197 + 197 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 197 * (5 : ZMod 51776063) ^ 197) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 1294941 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 51776063) ^ 790 = 841100 := by
        calc
          (5 : ZMod 51776063) ^ 790 = (5 : ZMod 51776063) ^ (395 + 395) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 395 * (5 : ZMod 51776063) ^ 395 := by rw [pow_add]
          _ = 841100 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 51776063) ^ 1580 = 32861231 := by
        calc
          (5 : ZMod 51776063) ^ 1580 = (5 : ZMod 51776063) ^ (790 + 790) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 790 * (5 : ZMod 51776063) ^ 790 := by rw [pow_add]
          _ = 32861231 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 51776063) ^ 3160 = 34644366 := by
        calc
          (5 : ZMod 51776063) ^ 3160 = (5 : ZMod 51776063) ^ (1580 + 1580) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 1580 * (5 : ZMod 51776063) ^ 1580 := by rw [pow_add]
          _ = 34644366 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 51776063) ^ 6320 = 47285411 := by
        calc
          (5 : ZMod 51776063) ^ 6320 = (5 : ZMod 51776063) ^ (3160 + 3160) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 3160 * (5 : ZMod 51776063) ^ 3160 := by rw [pow_add]
          _ = 47285411 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 51776063) ^ 12640 = 7263612 := by
        calc
          (5 : ZMod 51776063) ^ 12640 = (5 : ZMod 51776063) ^ (6320 + 6320) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 6320 * (5 : ZMod 51776063) ^ 6320 := by rw [pow_add]
          _ = 7263612 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 51776063) ^ 25281 = 12822208 := by
        calc
          (5 : ZMod 51776063) ^ 25281 = (5 : ZMod 51776063) ^ (12640 + 12640 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 12640 * (5 : ZMod 51776063) ^ 12640) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 12822208 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 51776063) ^ 50562 = 32409946 := by
        calc
          (5 : ZMod 51776063) ^ 50562 = (5 : ZMod 51776063) ^ (25281 + 25281) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 25281 * (5 : ZMod 51776063) ^ 25281 := by rw [pow_add]
          _ = 32409946 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 51776063) ^ 101125 = 50562003 := by
        calc
          (5 : ZMod 51776063) ^ 101125 = (5 : ZMod 51776063) ^ (50562 + 50562 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 50562 * (5 : ZMod 51776063) ^ 50562) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 50562003 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 51776063) ^ 202250 = 32498179 := by
        calc
          (5 : ZMod 51776063) ^ 202250 = (5 : ZMod 51776063) ^ (101125 + 101125) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 101125 * (5 : ZMod 51776063) ^ 101125 := by rw [pow_add]
          _ = 32498179 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 51776063) ^ 404500 = 36245820 := by
        calc
          (5 : ZMod 51776063) ^ 404500 = (5 : ZMod 51776063) ^ (202250 + 202250) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 202250 * (5 : ZMod 51776063) ^ 202250 := by rw [pow_add]
          _ = 36245820 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 51776063) ^ 809000 = 13366149 := by
        calc
          (5 : ZMod 51776063) ^ 809000 = (5 : ZMod 51776063) ^ (404500 + 404500) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 404500 * (5 : ZMod 51776063) ^ 404500 := by rw [pow_add]
          _ = 13366149 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 51776063) ^ 1618001 = 10203662 := by
        calc
          (5 : ZMod 51776063) ^ 1618001 = (5 : ZMod 51776063) ^ (809000 + 809000 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 809000 * (5 : ZMod 51776063) ^ 809000) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 10203662 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 51776063) ^ 3236003 = 19324493 := by
        calc
          (5 : ZMod 51776063) ^ 3236003 = (5 : ZMod 51776063) ^ (1618001 + 1618001 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 1618001 * (5 : ZMod 51776063) ^ 1618001) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 19324493 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 51776063) ^ 6472007 = 25902626 := by
        calc
          (5 : ZMod 51776063) ^ 6472007 = (5 : ZMod 51776063) ^ (3236003 + 3236003 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 3236003 * (5 : ZMod 51776063) ^ 3236003) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 25902626 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 51776063) ^ 12944015 = 42419907 := by
        calc
          (5 : ZMod 51776063) ^ 12944015 = (5 : ZMod 51776063) ^ (6472007 + 6472007 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 6472007 * (5 : ZMod 51776063) ^ 6472007) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 42419907 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 51776063) ^ 25888031 = 51776062 := by
        calc
          (5 : ZMod 51776063) ^ 25888031 = (5 : ZMod 51776063) ^ (12944015 + 12944015 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 12944015 * (5 : ZMod 51776063) ^ 12944015) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 51776062 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 51776063) ^ 51776062 = 1 := by
        calc
          (5 : ZMod 51776063) ^ 51776062 = (5 : ZMod 51776063) ^ (25888031 + 25888031) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 25888031 * (5 : ZMod 51776063) ^ 25888031 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (1991387, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (1991387, 1)] : List FactorBlock).map factorBlockValue).prod = 51776063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 51776063) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 51776063) ^ 3 = 125 := by
        calc
          (5 : ZMod 51776063) ^ 3 = (5 : ZMod 51776063) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 1 * (5 : ZMod 51776063) ^ 1) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 51776063) ^ 6 = 15625 := by
        calc
          (5 : ZMod 51776063) ^ 6 = (5 : ZMod 51776063) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 3 * (5 : ZMod 51776063) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 51776063) ^ 12 = 37036373 := by
        calc
          (5 : ZMod 51776063) ^ 12 = (5 : ZMod 51776063) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 6 * (5 : ZMod 51776063) ^ 6 := by rw [pow_add]
          _ = 37036373 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 51776063) ^ 24 = 43148729 := by
        calc
          (5 : ZMod 51776063) ^ 24 = (5 : ZMod 51776063) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 12 * (5 : ZMod 51776063) ^ 12 := by rw [pow_add]
          _ = 43148729 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 51776063) ^ 49 = 27388270 := by
        calc
          (5 : ZMod 51776063) ^ 49 = (5 : ZMod 51776063) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 24 * (5 : ZMod 51776063) ^ 24) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 27388270 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 51776063) ^ 98 = 23042288 := by
        calc
          (5 : ZMod 51776063) ^ 98 = (5 : ZMod 51776063) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 49 * (5 : ZMod 51776063) ^ 49 := by rw [pow_add]
          _ = 23042288 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 51776063) ^ 197 = 30318079 := by
        calc
          (5 : ZMod 51776063) ^ 197 = (5 : ZMod 51776063) ^ (98 + 98 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 98 * (5 : ZMod 51776063) ^ 98) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 30318079 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 51776063) ^ 395 = 1294941 := by
        calc
          (5 : ZMod 51776063) ^ 395 = (5 : ZMod 51776063) ^ (197 + 197 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 197 * (5 : ZMod 51776063) ^ 197) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 1294941 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 51776063) ^ 790 = 841100 := by
        calc
          (5 : ZMod 51776063) ^ 790 = (5 : ZMod 51776063) ^ (395 + 395) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 395 * (5 : ZMod 51776063) ^ 395 := by rw [pow_add]
          _ = 841100 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 51776063) ^ 1580 = 32861231 := by
        calc
          (5 : ZMod 51776063) ^ 1580 = (5 : ZMod 51776063) ^ (790 + 790) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 790 * (5 : ZMod 51776063) ^ 790 := by rw [pow_add]
          _ = 32861231 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 51776063) ^ 3160 = 34644366 := by
        calc
          (5 : ZMod 51776063) ^ 3160 = (5 : ZMod 51776063) ^ (1580 + 1580) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 1580 * (5 : ZMod 51776063) ^ 1580 := by rw [pow_add]
          _ = 34644366 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 51776063) ^ 6320 = 47285411 := by
        calc
          (5 : ZMod 51776063) ^ 6320 = (5 : ZMod 51776063) ^ (3160 + 3160) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 3160 * (5 : ZMod 51776063) ^ 3160 := by rw [pow_add]
          _ = 47285411 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 51776063) ^ 12640 = 7263612 := by
        calc
          (5 : ZMod 51776063) ^ 12640 = (5 : ZMod 51776063) ^ (6320 + 6320) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 6320 * (5 : ZMod 51776063) ^ 6320 := by rw [pow_add]
          _ = 7263612 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 51776063) ^ 25281 = 12822208 := by
        calc
          (5 : ZMod 51776063) ^ 25281 = (5 : ZMod 51776063) ^ (12640 + 12640 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 12640 * (5 : ZMod 51776063) ^ 12640) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 12822208 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 51776063) ^ 50562 = 32409946 := by
        calc
          (5 : ZMod 51776063) ^ 50562 = (5 : ZMod 51776063) ^ (25281 + 25281) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 25281 * (5 : ZMod 51776063) ^ 25281 := by rw [pow_add]
          _ = 32409946 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 51776063) ^ 101125 = 50562003 := by
        calc
          (5 : ZMod 51776063) ^ 101125 = (5 : ZMod 51776063) ^ (50562 + 50562 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 50562 * (5 : ZMod 51776063) ^ 50562) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 50562003 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 51776063) ^ 202250 = 32498179 := by
        calc
          (5 : ZMod 51776063) ^ 202250 = (5 : ZMod 51776063) ^ (101125 + 101125) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 101125 * (5 : ZMod 51776063) ^ 101125 := by rw [pow_add]
          _ = 32498179 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 51776063) ^ 404500 = 36245820 := by
        calc
          (5 : ZMod 51776063) ^ 404500 = (5 : ZMod 51776063) ^ (202250 + 202250) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 202250 * (5 : ZMod 51776063) ^ 202250 := by rw [pow_add]
          _ = 36245820 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 51776063) ^ 809000 = 13366149 := by
        calc
          (5 : ZMod 51776063) ^ 809000 = (5 : ZMod 51776063) ^ (404500 + 404500) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 404500 * (5 : ZMod 51776063) ^ 404500 := by rw [pow_add]
          _ = 13366149 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 51776063) ^ 1618001 = 10203662 := by
        calc
          (5 : ZMod 51776063) ^ 1618001 = (5 : ZMod 51776063) ^ (809000 + 809000 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 809000 * (5 : ZMod 51776063) ^ 809000) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 10203662 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 51776063) ^ 3236003 = 19324493 := by
        calc
          (5 : ZMod 51776063) ^ 3236003 = (5 : ZMod 51776063) ^ (1618001 + 1618001 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 1618001 * (5 : ZMod 51776063) ^ 1618001) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 19324493 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 51776063) ^ 6472007 = 25902626 := by
        calc
          (5 : ZMod 51776063) ^ 6472007 = (5 : ZMod 51776063) ^ (3236003 + 3236003 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 3236003 * (5 : ZMod 51776063) ^ 3236003) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 25902626 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 51776063) ^ 12944015 = 42419907 := by
        calc
          (5 : ZMod 51776063) ^ 12944015 = (5 : ZMod 51776063) ^ (6472007 + 6472007 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 6472007 * (5 : ZMod 51776063) ^ 6472007) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 42419907 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 51776063) ^ 25888031 = 51776062 := by
        calc
          (5 : ZMod 51776063) ^ 25888031 = (5 : ZMod 51776063) ^ (12944015 + 12944015 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 12944015 * (5 : ZMod 51776063) ^ 12944015) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 51776062 := by rw [factor_0_23]; decide
      change (5 : ZMod 51776063) ^ 25888031 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (5 : ZMod 51776063) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 51776063) ^ 3 = 125 := by
        calc
          (5 : ZMod 51776063) ^ 3 = (5 : ZMod 51776063) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 1 * (5 : ZMod 51776063) ^ 1) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 51776063) ^ 7 = 78125 := by
        calc
          (5 : ZMod 51776063) ^ 7 = (5 : ZMod 51776063) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 3 * (5 : ZMod 51776063) ^ 3) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 51776063) ^ 15 = 21477018 := by
        calc
          (5 : ZMod 51776063) ^ 15 = (5 : ZMod 51776063) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 7 * (5 : ZMod 51776063) ^ 7) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 21477018 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 51776063) ^ 30 = 22774302 := by
        calc
          (5 : ZMod 51776063) ^ 30 = (5 : ZMod 51776063) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 15 * (5 : ZMod 51776063) ^ 15 := by rw [pow_add]
          _ = 22774302 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 51776063) ^ 60 = 49442184 := by
        calc
          (5 : ZMod 51776063) ^ 60 = (5 : ZMod 51776063) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 30 * (5 : ZMod 51776063) ^ 30 := by rw [pow_add]
          _ = 49442184 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 51776063) ^ 121 = 21930323 := by
        calc
          (5 : ZMod 51776063) ^ 121 = (5 : ZMod 51776063) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 60 * (5 : ZMod 51776063) ^ 60) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 21930323 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 51776063) ^ 243 = 46264132 := by
        calc
          (5 : ZMod 51776063) ^ 243 = (5 : ZMod 51776063) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 121 * (5 : ZMod 51776063) ^ 121) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 46264132 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 51776063) ^ 486 = 17997369 := by
        calc
          (5 : ZMod 51776063) ^ 486 = (5 : ZMod 51776063) ^ (243 + 243) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 243 * (5 : ZMod 51776063) ^ 243 := by rw [pow_add]
          _ = 17997369 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 51776063) ^ 972 = 39713217 := by
        calc
          (5 : ZMod 51776063) ^ 972 = (5 : ZMod 51776063) ^ (486 + 486) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 486 * (5 : ZMod 51776063) ^ 486 := by rw [pow_add]
          _ = 39713217 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 51776063) ^ 1944 = 29523571 := by
        calc
          (5 : ZMod 51776063) ^ 1944 = (5 : ZMod 51776063) ^ (972 + 972) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 972 * (5 : ZMod 51776063) ^ 972 := by rw [pow_add]
          _ = 29523571 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 51776063) ^ 3889 = 26036629 := by
        calc
          (5 : ZMod 51776063) ^ 3889 = (5 : ZMod 51776063) ^ (1944 + 1944 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 1944 * (5 : ZMod 51776063) ^ 1944) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 26036629 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 51776063) ^ 7778 = 37558184 := by
        calc
          (5 : ZMod 51776063) ^ 7778 = (5 : ZMod 51776063) ^ (3889 + 3889) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 3889 * (5 : ZMod 51776063) ^ 3889 := by rw [pow_add]
          _ = 37558184 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 51776063) ^ 15557 = 8462013 := by
        calc
          (5 : ZMod 51776063) ^ 15557 = (5 : ZMod 51776063) ^ (7778 + 7778 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 7778 * (5 : ZMod 51776063) ^ 7778) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 8462013 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 51776063) ^ 31115 = 2755688 := by
        calc
          (5 : ZMod 51776063) ^ 31115 = (5 : ZMod 51776063) ^ (15557 + 15557 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 15557 * (5 : ZMod 51776063) ^ 15557) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 2755688 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 51776063) ^ 62230 = 28297386 := by
        calc
          (5 : ZMod 51776063) ^ 62230 = (5 : ZMod 51776063) ^ (31115 + 31115) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 31115 * (5 : ZMod 51776063) ^ 31115 := by rw [pow_add]
          _ = 28297386 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 51776063) ^ 124461 = 22424449 := by
        calc
          (5 : ZMod 51776063) ^ 124461 = (5 : ZMod 51776063) ^ (62230 + 62230 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 62230 * (5 : ZMod 51776063) ^ 62230) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 22424449 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 51776063) ^ 248923 = 32166740 := by
        calc
          (5 : ZMod 51776063) ^ 248923 = (5 : ZMod 51776063) ^ (124461 + 124461 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 124461 * (5 : ZMod 51776063) ^ 124461) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 32166740 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 51776063) ^ 497846 = 2555914 := by
        calc
          (5 : ZMod 51776063) ^ 497846 = (5 : ZMod 51776063) ^ (248923 + 248923) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 248923 * (5 : ZMod 51776063) ^ 248923 := by rw [pow_add]
          _ = 2555914 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 51776063) ^ 995693 = 34772800 := by
        calc
          (5 : ZMod 51776063) ^ 995693 = (5 : ZMod 51776063) ^ (497846 + 497846 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 497846 * (5 : ZMod 51776063) ^ 497846) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 34772800 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 51776063) ^ 1991387 = 13851913 := by
        calc
          (5 : ZMod 51776063) ^ 1991387 = (5 : ZMod 51776063) ^ (995693 + 995693 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 995693 * (5 : ZMod 51776063) ^ 995693) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 13851913 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 51776063) ^ 3982774 = 31617633 := by
        calc
          (5 : ZMod 51776063) ^ 3982774 = (5 : ZMod 51776063) ^ (1991387 + 1991387) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 1991387 * (5 : ZMod 51776063) ^ 1991387 := by rw [pow_add]
          _ = 31617633 := by rw [factor_1_20]; decide
      change (5 : ZMod 51776063) ^ 3982774 ≠ 1
      rw [factor_1_21]
      decide
    ·
      have factor_2_0 : (5 : ZMod 51776063) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 51776063) ^ 3 = 125 := by
        calc
          (5 : ZMod 51776063) ^ 3 = (5 : ZMod 51776063) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 1 * (5 : ZMod 51776063) ^ 1) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 51776063) ^ 6 = 15625 := by
        calc
          (5 : ZMod 51776063) ^ 6 = (5 : ZMod 51776063) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 3 * (5 : ZMod 51776063) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 51776063) ^ 13 = 29853676 := by
        calc
          (5 : ZMod 51776063) ^ 13 = (5 : ZMod 51776063) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = ((5 : ZMod 51776063) ^ 6 * (5 : ZMod 51776063) ^ 6) * (5 : ZMod 51776063) := by rw [pow_succ, pow_add]
          _ = 29853676 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 51776063) ^ 26 = 43196965 := by
        calc
          (5 : ZMod 51776063) ^ 26 = (5 : ZMod 51776063) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (5 : ZMod 51776063) ^ n) (by norm_num)
          _ = (5 : ZMod 51776063) ^ 13 * (5 : ZMod 51776063) ^ 13 := by rw [pow_add]
          _ = 43196965 := by rw [factor_2_3]; decide
      change (5 : ZMod 51776063) ^ 26 ≠ 1
      rw [factor_2_4]
      decide

#print axioms prime_lucas_51776063

end TotientTailPeriodKiller
end Erdos249257
