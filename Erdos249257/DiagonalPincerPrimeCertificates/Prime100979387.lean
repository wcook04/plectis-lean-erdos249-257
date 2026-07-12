import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_100979387 : Nat.Prime 100979387 := by
  apply lucas_primality 100979387 (2 : ZMod 100979387)
  ·
      have fermat_0 : (2 : ZMod 100979387) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 100979387) ^ 3 = 8 := by
        calc
          (2 : ZMod 100979387) ^ 3 = (2 : ZMod 100979387) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 1 * (2 : ZMod 100979387) ^ 1) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 100979387) ^ 6 = 64 := by
        calc
          (2 : ZMod 100979387) ^ 6 = (2 : ZMod 100979387) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 3 * (2 : ZMod 100979387) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 100979387) ^ 12 = 4096 := by
        calc
          (2 : ZMod 100979387) ^ 12 = (2 : ZMod 100979387) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 6 * (2 : ZMod 100979387) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 100979387) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 100979387) ^ 24 = (2 : ZMod 100979387) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 12 * (2 : ZMod 100979387) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 100979387) ^ 48 = 85396893 := by
        calc
          (2 : ZMod 100979387) ^ 48 = (2 : ZMod 100979387) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 24 * (2 : ZMod 100979387) ^ 24 := by rw [pow_add]
          _ = 85396893 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 100979387) ^ 96 = 95073706 := by
        calc
          (2 : ZMod 100979387) ^ 96 = (2 : ZMod 100979387) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 48 * (2 : ZMod 100979387) ^ 48 := by rw [pow_add]
          _ = 95073706 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 100979387) ^ 192 = 100535992 := by
        calc
          (2 : ZMod 100979387) ^ 192 = (2 : ZMod 100979387) ^ (96 + 96) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 96 * (2 : ZMod 100979387) ^ 96 := by rw [pow_add]
          _ = 100535992 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 100979387) ^ 385 = 85498459 := by
        calc
          (2 : ZMod 100979387) ^ 385 = (2 : ZMod 100979387) ^ (192 + 192 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 192 * (2 : ZMod 100979387) ^ 192) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 85498459 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 100979387) ^ 770 = 6542895 := by
        calc
          (2 : ZMod 100979387) ^ 770 = (2 : ZMod 100979387) ^ (385 + 385) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 385 * (2 : ZMod 100979387) ^ 385 := by rw [pow_add]
          _ = 6542895 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 100979387) ^ 1540 = 71697471 := by
        calc
          (2 : ZMod 100979387) ^ 1540 = (2 : ZMod 100979387) ^ (770 + 770) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 770 * (2 : ZMod 100979387) ^ 770 := by rw [pow_add]
          _ = 71697471 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 100979387) ^ 3081 = 76185269 := by
        calc
          (2 : ZMod 100979387) ^ 3081 = (2 : ZMod 100979387) ^ (1540 + 1540 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 1540 * (2 : ZMod 100979387) ^ 1540) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 76185269 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 100979387) ^ 6163 = 34870982 := by
        calc
          (2 : ZMod 100979387) ^ 6163 = (2 : ZMod 100979387) ^ (3081 + 3081 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 3081 * (2 : ZMod 100979387) ^ 3081) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 34870982 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 100979387) ^ 12326 = 89658832 := by
        calc
          (2 : ZMod 100979387) ^ 12326 = (2 : ZMod 100979387) ^ (6163 + 6163) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 6163 * (2 : ZMod 100979387) ^ 6163 := by rw [pow_add]
          _ = 89658832 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 100979387) ^ 24653 = 11757170 := by
        calc
          (2 : ZMod 100979387) ^ 24653 = (2 : ZMod 100979387) ^ (12326 + 12326 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 12326 * (2 : ZMod 100979387) ^ 12326) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 11757170 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 100979387) ^ 49306 = 60606439 := by
        calc
          (2 : ZMod 100979387) ^ 49306 = (2 : ZMod 100979387) ^ (24653 + 24653) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 24653 * (2 : ZMod 100979387) ^ 24653 := by rw [pow_add]
          _ = 60606439 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 100979387) ^ 98612 = 99227671 := by
        calc
          (2 : ZMod 100979387) ^ 98612 = (2 : ZMod 100979387) ^ (49306 + 49306) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 49306 * (2 : ZMod 100979387) ^ 49306 := by rw [pow_add]
          _ = 99227671 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 100979387) ^ 197225 = 96623774 := by
        calc
          (2 : ZMod 100979387) ^ 197225 = (2 : ZMod 100979387) ^ (98612 + 98612 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 98612 * (2 : ZMod 100979387) ^ 98612) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 96623774 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 100979387) ^ 394450 = 64231918 := by
        calc
          (2 : ZMod 100979387) ^ 394450 = (2 : ZMod 100979387) ^ (197225 + 197225) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 197225 * (2 : ZMod 100979387) ^ 197225 := by rw [pow_add]
          _ = 64231918 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 100979387) ^ 788901 = 76576140 := by
        calc
          (2 : ZMod 100979387) ^ 788901 = (2 : ZMod 100979387) ^ (394450 + 394450 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 394450 * (2 : ZMod 100979387) ^ 394450) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 76576140 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 100979387) ^ 1577802 = 1785147 := by
        calc
          (2 : ZMod 100979387) ^ 1577802 = (2 : ZMod 100979387) ^ (788901 + 788901) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 788901 * (2 : ZMod 100979387) ^ 788901 := by rw [pow_add]
          _ = 1785147 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 100979387) ^ 3155605 = 84633326 := by
        calc
          (2 : ZMod 100979387) ^ 3155605 = (2 : ZMod 100979387) ^ (1577802 + 1577802 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 1577802 * (2 : ZMod 100979387) ^ 1577802) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 84633326 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 100979387) ^ 6311211 = 61334414 := by
        calc
          (2 : ZMod 100979387) ^ 6311211 = (2 : ZMod 100979387) ^ (3155605 + 3155605 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 3155605 * (2 : ZMod 100979387) ^ 3155605) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 61334414 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 100979387) ^ 12622423 = 44745032 := by
        calc
          (2 : ZMod 100979387) ^ 12622423 = (2 : ZMod 100979387) ^ (6311211 + 6311211 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 6311211 * (2 : ZMod 100979387) ^ 6311211) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 44745032 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 100979387) ^ 25244846 = 87528959 := by
        calc
          (2 : ZMod 100979387) ^ 25244846 = (2 : ZMod 100979387) ^ (12622423 + 12622423) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 12622423 * (2 : ZMod 100979387) ^ 12622423 := by rw [pow_add]
          _ = 87528959 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 100979387) ^ 50489693 = 100979386 := by
        calc
          (2 : ZMod 100979387) ^ 50489693 = (2 : ZMod 100979387) ^ (25244846 + 25244846 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 25244846 * (2 : ZMod 100979387) ^ 25244846) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 100979386 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 100979387) ^ 100979386 = 1 := by
        calc
          (2 : ZMod 100979387) ^ 100979386 = (2 : ZMod 100979387) ^ (50489693 + 50489693) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 50489693 * (2 : ZMod 100979387) ^ 50489693 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (149, 1), (338857, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (149, 1), (338857, 1)] : List FactorBlock).map factorBlockValue).prod = 100979387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 100979387) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 100979387) ^ 3 = 8 := by
        calc
          (2 : ZMod 100979387) ^ 3 = (2 : ZMod 100979387) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 1 * (2 : ZMod 100979387) ^ 1) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 100979387) ^ 6 = 64 := by
        calc
          (2 : ZMod 100979387) ^ 6 = (2 : ZMod 100979387) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 3 * (2 : ZMod 100979387) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 100979387) ^ 12 = 4096 := by
        calc
          (2 : ZMod 100979387) ^ 12 = (2 : ZMod 100979387) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 6 * (2 : ZMod 100979387) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 100979387) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 100979387) ^ 24 = (2 : ZMod 100979387) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 12 * (2 : ZMod 100979387) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 100979387) ^ 48 = 85396893 := by
        calc
          (2 : ZMod 100979387) ^ 48 = (2 : ZMod 100979387) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 24 * (2 : ZMod 100979387) ^ 24 := by rw [pow_add]
          _ = 85396893 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 100979387) ^ 96 = 95073706 := by
        calc
          (2 : ZMod 100979387) ^ 96 = (2 : ZMod 100979387) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 48 * (2 : ZMod 100979387) ^ 48 := by rw [pow_add]
          _ = 95073706 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 100979387) ^ 192 = 100535992 := by
        calc
          (2 : ZMod 100979387) ^ 192 = (2 : ZMod 100979387) ^ (96 + 96) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 96 * (2 : ZMod 100979387) ^ 96 := by rw [pow_add]
          _ = 100535992 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 100979387) ^ 385 = 85498459 := by
        calc
          (2 : ZMod 100979387) ^ 385 = (2 : ZMod 100979387) ^ (192 + 192 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 192 * (2 : ZMod 100979387) ^ 192) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 85498459 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 100979387) ^ 770 = 6542895 := by
        calc
          (2 : ZMod 100979387) ^ 770 = (2 : ZMod 100979387) ^ (385 + 385) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 385 * (2 : ZMod 100979387) ^ 385 := by rw [pow_add]
          _ = 6542895 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 100979387) ^ 1540 = 71697471 := by
        calc
          (2 : ZMod 100979387) ^ 1540 = (2 : ZMod 100979387) ^ (770 + 770) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 770 * (2 : ZMod 100979387) ^ 770 := by rw [pow_add]
          _ = 71697471 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 100979387) ^ 3081 = 76185269 := by
        calc
          (2 : ZMod 100979387) ^ 3081 = (2 : ZMod 100979387) ^ (1540 + 1540 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 1540 * (2 : ZMod 100979387) ^ 1540) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 76185269 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 100979387) ^ 6163 = 34870982 := by
        calc
          (2 : ZMod 100979387) ^ 6163 = (2 : ZMod 100979387) ^ (3081 + 3081 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 3081 * (2 : ZMod 100979387) ^ 3081) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 34870982 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 100979387) ^ 12326 = 89658832 := by
        calc
          (2 : ZMod 100979387) ^ 12326 = (2 : ZMod 100979387) ^ (6163 + 6163) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 6163 * (2 : ZMod 100979387) ^ 6163 := by rw [pow_add]
          _ = 89658832 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 100979387) ^ 24653 = 11757170 := by
        calc
          (2 : ZMod 100979387) ^ 24653 = (2 : ZMod 100979387) ^ (12326 + 12326 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 12326 * (2 : ZMod 100979387) ^ 12326) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 11757170 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 100979387) ^ 49306 = 60606439 := by
        calc
          (2 : ZMod 100979387) ^ 49306 = (2 : ZMod 100979387) ^ (24653 + 24653) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 24653 * (2 : ZMod 100979387) ^ 24653 := by rw [pow_add]
          _ = 60606439 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 100979387) ^ 98612 = 99227671 := by
        calc
          (2 : ZMod 100979387) ^ 98612 = (2 : ZMod 100979387) ^ (49306 + 49306) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 49306 * (2 : ZMod 100979387) ^ 49306 := by rw [pow_add]
          _ = 99227671 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 100979387) ^ 197225 = 96623774 := by
        calc
          (2 : ZMod 100979387) ^ 197225 = (2 : ZMod 100979387) ^ (98612 + 98612 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 98612 * (2 : ZMod 100979387) ^ 98612) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 96623774 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 100979387) ^ 394450 = 64231918 := by
        calc
          (2 : ZMod 100979387) ^ 394450 = (2 : ZMod 100979387) ^ (197225 + 197225) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 197225 * (2 : ZMod 100979387) ^ 197225 := by rw [pow_add]
          _ = 64231918 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 100979387) ^ 788901 = 76576140 := by
        calc
          (2 : ZMod 100979387) ^ 788901 = (2 : ZMod 100979387) ^ (394450 + 394450 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 394450 * (2 : ZMod 100979387) ^ 394450) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 76576140 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 100979387) ^ 1577802 = 1785147 := by
        calc
          (2 : ZMod 100979387) ^ 1577802 = (2 : ZMod 100979387) ^ (788901 + 788901) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 788901 * (2 : ZMod 100979387) ^ 788901 := by rw [pow_add]
          _ = 1785147 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 100979387) ^ 3155605 = 84633326 := by
        calc
          (2 : ZMod 100979387) ^ 3155605 = (2 : ZMod 100979387) ^ (1577802 + 1577802 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 1577802 * (2 : ZMod 100979387) ^ 1577802) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 84633326 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 100979387) ^ 6311211 = 61334414 := by
        calc
          (2 : ZMod 100979387) ^ 6311211 = (2 : ZMod 100979387) ^ (3155605 + 3155605 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 3155605 * (2 : ZMod 100979387) ^ 3155605) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 61334414 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 100979387) ^ 12622423 = 44745032 := by
        calc
          (2 : ZMod 100979387) ^ 12622423 = (2 : ZMod 100979387) ^ (6311211 + 6311211 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 6311211 * (2 : ZMod 100979387) ^ 6311211) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 44745032 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 100979387) ^ 25244846 = 87528959 := by
        calc
          (2 : ZMod 100979387) ^ 25244846 = (2 : ZMod 100979387) ^ (12622423 + 12622423) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 12622423 * (2 : ZMod 100979387) ^ 12622423 := by rw [pow_add]
          _ = 87528959 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 100979387) ^ 50489693 = 100979386 := by
        calc
          (2 : ZMod 100979387) ^ 50489693 = (2 : ZMod 100979387) ^ (25244846 + 25244846 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 25244846 * (2 : ZMod 100979387) ^ 25244846) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 100979386 := by rw [factor_0_24]; decide
      change (2 : ZMod 100979387) ^ 50489693 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (2 : ZMod 100979387) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 100979387) ^ 2 = 4 := by
        calc
          (2 : ZMod 100979387) ^ 2 = (2 : ZMod 100979387) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 1 * (2 : ZMod 100979387) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 100979387) ^ 5 = 32 := by
        calc
          (2 : ZMod 100979387) ^ 5 = (2 : ZMod 100979387) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 2 * (2 : ZMod 100979387) ^ 2) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 100979387) ^ 10 = 1024 := by
        calc
          (2 : ZMod 100979387) ^ 10 = (2 : ZMod 100979387) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 5 * (2 : ZMod 100979387) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 100979387) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 100979387) ^ 20 = (2 : ZMod 100979387) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 10 * (2 : ZMod 100979387) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 100979387) ^ 41 = 96124240 := by
        calc
          (2 : ZMod 100979387) ^ 41 = (2 : ZMod 100979387) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 20 * (2 : ZMod 100979387) ^ 20) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 96124240 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 100979387) ^ 82 = 26249103 := by
        calc
          (2 : ZMod 100979387) ^ 82 = (2 : ZMod 100979387) ^ (41 + 41) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 41 * (2 : ZMod 100979387) ^ 41 := by rw [pow_add]
          _ = 26249103 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 100979387) ^ 165 = 61088120 := by
        calc
          (2 : ZMod 100979387) ^ 165 = (2 : ZMod 100979387) ^ (82 + 82 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 82 * (2 : ZMod 100979387) ^ 82) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 61088120 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 100979387) ^ 330 = 26844785 := by
        calc
          (2 : ZMod 100979387) ^ 330 = (2 : ZMod 100979387) ^ (165 + 165) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 165 * (2 : ZMod 100979387) ^ 165 := by rw [pow_add]
          _ = 26844785 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 100979387) ^ 661 = 12998843 := by
        calc
          (2 : ZMod 100979387) ^ 661 = (2 : ZMod 100979387) ^ (330 + 330 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 330 * (2 : ZMod 100979387) ^ 330) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 12998843 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 100979387) ^ 1323 = 596584 := by
        calc
          (2 : ZMod 100979387) ^ 1323 = (2 : ZMod 100979387) ^ (661 + 661 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 661 * (2 : ZMod 100979387) ^ 661) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 596584 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 100979387) ^ 2647 = 21239149 := by
        calc
          (2 : ZMod 100979387) ^ 2647 = (2 : ZMod 100979387) ^ (1323 + 1323 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 1323 * (2 : ZMod 100979387) ^ 1323) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 21239149 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 100979387) ^ 5294 = 71915807 := by
        calc
          (2 : ZMod 100979387) ^ 5294 = (2 : ZMod 100979387) ^ (2647 + 2647) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 2647 * (2 : ZMod 100979387) ^ 2647 := by rw [pow_add]
          _ = 71915807 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 100979387) ^ 10589 = 37951766 := by
        calc
          (2 : ZMod 100979387) ^ 10589 = (2 : ZMod 100979387) ^ (5294 + 5294 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 5294 * (2 : ZMod 100979387) ^ 5294) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 37951766 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 100979387) ^ 21178 = 91507240 := by
        calc
          (2 : ZMod 100979387) ^ 21178 = (2 : ZMod 100979387) ^ (10589 + 10589) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 10589 * (2 : ZMod 100979387) ^ 10589 := by rw [pow_add]
          _ = 91507240 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 100979387) ^ 42357 = 40436769 := by
        calc
          (2 : ZMod 100979387) ^ 42357 = (2 : ZMod 100979387) ^ (21178 + 21178 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 21178 * (2 : ZMod 100979387) ^ 21178) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 40436769 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 100979387) ^ 84714 = 34964690 := by
        calc
          (2 : ZMod 100979387) ^ 84714 = (2 : ZMod 100979387) ^ (42357 + 42357) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 42357 * (2 : ZMod 100979387) ^ 42357 := by rw [pow_add]
          _ = 34964690 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 100979387) ^ 169428 = 79677299 := by
        calc
          (2 : ZMod 100979387) ^ 169428 = (2 : ZMod 100979387) ^ (84714 + 84714) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 84714 * (2 : ZMod 100979387) ^ 84714 := by rw [pow_add]
          _ = 79677299 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 100979387) ^ 338857 = 10811316 := by
        calc
          (2 : ZMod 100979387) ^ 338857 = (2 : ZMod 100979387) ^ (169428 + 169428 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 169428 * (2 : ZMod 100979387) ^ 169428) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 10811316 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 100979387) ^ 677714 = 4384873 := by
        calc
          (2 : ZMod 100979387) ^ 677714 = (2 : ZMod 100979387) ^ (338857 + 338857) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 338857 * (2 : ZMod 100979387) ^ 338857 := by rw [pow_add]
          _ = 4384873 := by rw [factor_1_18]; decide
      change (2 : ZMod 100979387) ^ 677714 ≠ 1
      rw [factor_1_19]
      decide
    ·
      have factor_2_0 : (2 : ZMod 100979387) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 100979387) ^ 2 = 4 := by
        calc
          (2 : ZMod 100979387) ^ 2 = (2 : ZMod 100979387) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 1 * (2 : ZMod 100979387) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 100979387) ^ 4 = 16 := by
        calc
          (2 : ZMod 100979387) ^ 4 = (2 : ZMod 100979387) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 2 * (2 : ZMod 100979387) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 100979387) ^ 9 = 512 := by
        calc
          (2 : ZMod 100979387) ^ 9 = (2 : ZMod 100979387) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 4 * (2 : ZMod 100979387) ^ 4) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 100979387) ^ 18 = 262144 := by
        calc
          (2 : ZMod 100979387) ^ 18 = (2 : ZMod 100979387) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 9 * (2 : ZMod 100979387) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 100979387) ^ 37 = 6007765 := by
        calc
          (2 : ZMod 100979387) ^ 37 = (2 : ZMod 100979387) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 18 * (2 : ZMod 100979387) ^ 18) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 6007765 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 100979387) ^ 74 = 77020428 := by
        calc
          (2 : ZMod 100979387) ^ 74 = (2 : ZMod 100979387) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 37 * (2 : ZMod 100979387) ^ 37 := by rw [pow_add]
          _ = 77020428 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 100979387) ^ 149 = 2799067 := by
        calc
          (2 : ZMod 100979387) ^ 149 = (2 : ZMod 100979387) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = ((2 : ZMod 100979387) ^ 74 * (2 : ZMod 100979387) ^ 74) * (2 : ZMod 100979387) := by rw [pow_succ, pow_add]
          _ = 2799067 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 100979387) ^ 298 = 88371320 := by
        calc
          (2 : ZMod 100979387) ^ 298 = (2 : ZMod 100979387) ^ (149 + 149) :=
            congrArg (fun n : ℕ => (2 : ZMod 100979387) ^ n) (by norm_num)
          _ = (2 : ZMod 100979387) ^ 149 * (2 : ZMod 100979387) ^ 149 := by rw [pow_add]
          _ = 88371320 := by rw [factor_2_7]; decide
      change (2 : ZMod 100979387) ^ 298 ≠ 1
      rw [factor_2_8]
      decide

#print axioms prime_lucas_100979387

end TotientTailPeriodKiller
end Erdos249257
