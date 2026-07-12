import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=27 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_101086763 : Nat.Prime 101086763 := by
  apply lucas_primality 101086763 (2 : ZMod 101086763)
  ·
      have fermat_0 : (2 : ZMod 101086763) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 101086763) ^ 3 = 8 := by
        calc
          (2 : ZMod 101086763) ^ 3 = (2 : ZMod 101086763) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 1 * (2 : ZMod 101086763) ^ 1) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 101086763) ^ 6 = 64 := by
        calc
          (2 : ZMod 101086763) ^ 6 = (2 : ZMod 101086763) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 3 * (2 : ZMod 101086763) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 101086763) ^ 12 = 4096 := by
        calc
          (2 : ZMod 101086763) ^ 12 = (2 : ZMod 101086763) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 6 * (2 : ZMod 101086763) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 101086763) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 101086763) ^ 24 = (2 : ZMod 101086763) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 12 * (2 : ZMod 101086763) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 101086763) ^ 48 = 98178312 := by
        calc
          (2 : ZMod 101086763) ^ 48 = (2 : ZMod 101086763) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 24 * (2 : ZMod 101086763) ^ 24 := by rw [pow_add]
          _ = 98178312 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 101086763) ^ 96 = 45804798 := by
        calc
          (2 : ZMod 101086763) ^ 96 = (2 : ZMod 101086763) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 48 * (2 : ZMod 101086763) ^ 48 := by rw [pow_add]
          _ = 45804798 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 101086763) ^ 192 = 99453262 := by
        calc
          (2 : ZMod 101086763) ^ 192 = (2 : ZMod 101086763) ^ (96 + 96) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 96 * (2 : ZMod 101086763) ^ 96 := by rw [pow_add]
          _ = 99453262 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 101086763) ^ 385 = 78641706 := by
        calc
          (2 : ZMod 101086763) ^ 385 = (2 : ZMod 101086763) ^ (192 + 192 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 192 * (2 : ZMod 101086763) ^ 192) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 78641706 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 101086763) ^ 771 = 85484228 := by
        calc
          (2 : ZMod 101086763) ^ 771 = (2 : ZMod 101086763) ^ (385 + 385 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 385 * (2 : ZMod 101086763) ^ 385) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 85484228 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 101086763) ^ 1542 = 35121128 := by
        calc
          (2 : ZMod 101086763) ^ 1542 = (2 : ZMod 101086763) ^ (771 + 771) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 771 * (2 : ZMod 101086763) ^ 771 := by rw [pow_add]
          _ = 35121128 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 101086763) ^ 3084 = 96668409 := by
        calc
          (2 : ZMod 101086763) ^ 3084 = (2 : ZMod 101086763) ^ (1542 + 1542) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 1542 * (2 : ZMod 101086763) ^ 1542 := by rw [pow_add]
          _ = 96668409 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 101086763) ^ 6169 = 53884275 := by
        calc
          (2 : ZMod 101086763) ^ 6169 = (2 : ZMod 101086763) ^ (3084 + 3084 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 3084 * (2 : ZMod 101086763) ^ 3084) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 53884275 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 101086763) ^ 12339 = 98340013 := by
        calc
          (2 : ZMod 101086763) ^ 12339 = (2 : ZMod 101086763) ^ (6169 + 6169 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 6169 * (2 : ZMod 101086763) ^ 6169) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 98340013 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 101086763) ^ 24679 = 50011990 := by
        calc
          (2 : ZMod 101086763) ^ 24679 = (2 : ZMod 101086763) ^ (12339 + 12339 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 12339 * (2 : ZMod 101086763) ^ 12339) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 50011990 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 101086763) ^ 49358 = 66868904 := by
        calc
          (2 : ZMod 101086763) ^ 49358 = (2 : ZMod 101086763) ^ (24679 + 24679) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 24679 * (2 : ZMod 101086763) ^ 24679 := by rw [pow_add]
          _ = 66868904 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 101086763) ^ 98717 = 59286233 := by
        calc
          (2 : ZMod 101086763) ^ 98717 = (2 : ZMod 101086763) ^ (49358 + 49358 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 49358 * (2 : ZMod 101086763) ^ 49358) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 59286233 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 101086763) ^ 197435 = 28345904 := by
        calc
          (2 : ZMod 101086763) ^ 197435 = (2 : ZMod 101086763) ^ (98717 + 98717 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 98717 * (2 : ZMod 101086763) ^ 98717) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 28345904 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 101086763) ^ 394870 = 15049693 := by
        calc
          (2 : ZMod 101086763) ^ 394870 = (2 : ZMod 101086763) ^ (197435 + 197435) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 197435 * (2 : ZMod 101086763) ^ 197435 := by rw [pow_add]
          _ = 15049693 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 101086763) ^ 789740 = 77778183 := by
        calc
          (2 : ZMod 101086763) ^ 789740 = (2 : ZMod 101086763) ^ (394870 + 394870) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 394870 * (2 : ZMod 101086763) ^ 394870 := by rw [pow_add]
          _ = 77778183 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 101086763) ^ 1579480 = 3653767 := by
        calc
          (2 : ZMod 101086763) ^ 1579480 = (2 : ZMod 101086763) ^ (789740 + 789740) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 789740 * (2 : ZMod 101086763) ^ 789740 := by rw [pow_add]
          _ = 3653767 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 101086763) ^ 3158961 = 80956151 := by
        calc
          (2 : ZMod 101086763) ^ 3158961 = (2 : ZMod 101086763) ^ (1579480 + 1579480 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 1579480 * (2 : ZMod 101086763) ^ 1579480) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 80956151 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 101086763) ^ 6317922 = 71815520 := by
        calc
          (2 : ZMod 101086763) ^ 6317922 = (2 : ZMod 101086763) ^ (3158961 + 3158961) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 3158961 * (2 : ZMod 101086763) ^ 3158961 := by rw [pow_add]
          _ = 71815520 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 101086763) ^ 12635845 = 51045080 := by
        calc
          (2 : ZMod 101086763) ^ 12635845 = (2 : ZMod 101086763) ^ (6317922 + 6317922 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 6317922 * (2 : ZMod 101086763) ^ 6317922) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 51045080 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 101086763) ^ 25271690 = 20616723 := by
        calc
          (2 : ZMod 101086763) ^ 25271690 = (2 : ZMod 101086763) ^ (12635845 + 12635845) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 12635845 * (2 : ZMod 101086763) ^ 12635845 := by rw [pow_add]
          _ = 20616723 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 101086763) ^ 50543381 = 101086762 := by
        calc
          (2 : ZMod 101086763) ^ 50543381 = (2 : ZMod 101086763) ^ (25271690 + 25271690 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 25271690 * (2 : ZMod 101086763) ^ 25271690) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 101086762 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 101086763) ^ 101086762 = 1 := by
        calc
          (2 : ZMod 101086763) ^ 101086762 = (2 : ZMod 101086763) ^ (50543381 + 50543381) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 50543381 * (2 : ZMod 101086763) ^ 50543381 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (7220483, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (7220483, 1)] : List FactorBlock).map factorBlockValue).prod = 101086763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 101086763) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 101086763) ^ 3 = 8 := by
        calc
          (2 : ZMod 101086763) ^ 3 = (2 : ZMod 101086763) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 1 * (2 : ZMod 101086763) ^ 1) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 101086763) ^ 6 = 64 := by
        calc
          (2 : ZMod 101086763) ^ 6 = (2 : ZMod 101086763) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 3 * (2 : ZMod 101086763) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 101086763) ^ 12 = 4096 := by
        calc
          (2 : ZMod 101086763) ^ 12 = (2 : ZMod 101086763) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 6 * (2 : ZMod 101086763) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 101086763) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 101086763) ^ 24 = (2 : ZMod 101086763) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 12 * (2 : ZMod 101086763) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 101086763) ^ 48 = 98178312 := by
        calc
          (2 : ZMod 101086763) ^ 48 = (2 : ZMod 101086763) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 24 * (2 : ZMod 101086763) ^ 24 := by rw [pow_add]
          _ = 98178312 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 101086763) ^ 96 = 45804798 := by
        calc
          (2 : ZMod 101086763) ^ 96 = (2 : ZMod 101086763) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 48 * (2 : ZMod 101086763) ^ 48 := by rw [pow_add]
          _ = 45804798 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 101086763) ^ 192 = 99453262 := by
        calc
          (2 : ZMod 101086763) ^ 192 = (2 : ZMod 101086763) ^ (96 + 96) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 96 * (2 : ZMod 101086763) ^ 96 := by rw [pow_add]
          _ = 99453262 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 101086763) ^ 385 = 78641706 := by
        calc
          (2 : ZMod 101086763) ^ 385 = (2 : ZMod 101086763) ^ (192 + 192 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 192 * (2 : ZMod 101086763) ^ 192) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 78641706 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 101086763) ^ 771 = 85484228 := by
        calc
          (2 : ZMod 101086763) ^ 771 = (2 : ZMod 101086763) ^ (385 + 385 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 385 * (2 : ZMod 101086763) ^ 385) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 85484228 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 101086763) ^ 1542 = 35121128 := by
        calc
          (2 : ZMod 101086763) ^ 1542 = (2 : ZMod 101086763) ^ (771 + 771) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 771 * (2 : ZMod 101086763) ^ 771 := by rw [pow_add]
          _ = 35121128 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 101086763) ^ 3084 = 96668409 := by
        calc
          (2 : ZMod 101086763) ^ 3084 = (2 : ZMod 101086763) ^ (1542 + 1542) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 1542 * (2 : ZMod 101086763) ^ 1542 := by rw [pow_add]
          _ = 96668409 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 101086763) ^ 6169 = 53884275 := by
        calc
          (2 : ZMod 101086763) ^ 6169 = (2 : ZMod 101086763) ^ (3084 + 3084 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 3084 * (2 : ZMod 101086763) ^ 3084) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 53884275 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 101086763) ^ 12339 = 98340013 := by
        calc
          (2 : ZMod 101086763) ^ 12339 = (2 : ZMod 101086763) ^ (6169 + 6169 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 6169 * (2 : ZMod 101086763) ^ 6169) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 98340013 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 101086763) ^ 24679 = 50011990 := by
        calc
          (2 : ZMod 101086763) ^ 24679 = (2 : ZMod 101086763) ^ (12339 + 12339 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 12339 * (2 : ZMod 101086763) ^ 12339) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 50011990 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 101086763) ^ 49358 = 66868904 := by
        calc
          (2 : ZMod 101086763) ^ 49358 = (2 : ZMod 101086763) ^ (24679 + 24679) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 24679 * (2 : ZMod 101086763) ^ 24679 := by rw [pow_add]
          _ = 66868904 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 101086763) ^ 98717 = 59286233 := by
        calc
          (2 : ZMod 101086763) ^ 98717 = (2 : ZMod 101086763) ^ (49358 + 49358 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 49358 * (2 : ZMod 101086763) ^ 49358) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 59286233 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 101086763) ^ 197435 = 28345904 := by
        calc
          (2 : ZMod 101086763) ^ 197435 = (2 : ZMod 101086763) ^ (98717 + 98717 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 98717 * (2 : ZMod 101086763) ^ 98717) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 28345904 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 101086763) ^ 394870 = 15049693 := by
        calc
          (2 : ZMod 101086763) ^ 394870 = (2 : ZMod 101086763) ^ (197435 + 197435) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 197435 * (2 : ZMod 101086763) ^ 197435 := by rw [pow_add]
          _ = 15049693 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 101086763) ^ 789740 = 77778183 := by
        calc
          (2 : ZMod 101086763) ^ 789740 = (2 : ZMod 101086763) ^ (394870 + 394870) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 394870 * (2 : ZMod 101086763) ^ 394870 := by rw [pow_add]
          _ = 77778183 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 101086763) ^ 1579480 = 3653767 := by
        calc
          (2 : ZMod 101086763) ^ 1579480 = (2 : ZMod 101086763) ^ (789740 + 789740) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 789740 * (2 : ZMod 101086763) ^ 789740 := by rw [pow_add]
          _ = 3653767 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 101086763) ^ 3158961 = 80956151 := by
        calc
          (2 : ZMod 101086763) ^ 3158961 = (2 : ZMod 101086763) ^ (1579480 + 1579480 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 1579480 * (2 : ZMod 101086763) ^ 1579480) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 80956151 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 101086763) ^ 6317922 = 71815520 := by
        calc
          (2 : ZMod 101086763) ^ 6317922 = (2 : ZMod 101086763) ^ (3158961 + 3158961) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 3158961 * (2 : ZMod 101086763) ^ 3158961 := by rw [pow_add]
          _ = 71815520 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 101086763) ^ 12635845 = 51045080 := by
        calc
          (2 : ZMod 101086763) ^ 12635845 = (2 : ZMod 101086763) ^ (6317922 + 6317922 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 6317922 * (2 : ZMod 101086763) ^ 6317922) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 51045080 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 101086763) ^ 25271690 = 20616723 := by
        calc
          (2 : ZMod 101086763) ^ 25271690 = (2 : ZMod 101086763) ^ (12635845 + 12635845) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 12635845 * (2 : ZMod 101086763) ^ 12635845 := by rw [pow_add]
          _ = 20616723 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 101086763) ^ 50543381 = 101086762 := by
        calc
          (2 : ZMod 101086763) ^ 50543381 = (2 : ZMod 101086763) ^ (25271690 + 25271690 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 25271690 * (2 : ZMod 101086763) ^ 25271690) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 101086762 := by rw [factor_0_24]; decide
      change (2 : ZMod 101086763) ^ 50543381 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (2 : ZMod 101086763) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 101086763) ^ 3 = 8 := by
        calc
          (2 : ZMod 101086763) ^ 3 = (2 : ZMod 101086763) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 1 * (2 : ZMod 101086763) ^ 1) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 101086763) ^ 6 = 64 := by
        calc
          (2 : ZMod 101086763) ^ 6 = (2 : ZMod 101086763) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 3 * (2 : ZMod 101086763) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 101086763) ^ 13 = 8192 := by
        calc
          (2 : ZMod 101086763) ^ 13 = (2 : ZMod 101086763) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 6 * (2 : ZMod 101086763) ^ 6) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 101086763) ^ 27 = 33130965 := by
        calc
          (2 : ZMod 101086763) ^ 27 = (2 : ZMod 101086763) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 13 * (2 : ZMod 101086763) ^ 13) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 33130965 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 101086763) ^ 55 = 32065324 := by
        calc
          (2 : ZMod 101086763) ^ 55 = (2 : ZMod 101086763) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 27 * (2 : ZMod 101086763) ^ 27) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 32065324 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 101086763) ^ 110 = 98768683 := by
        calc
          (2 : ZMod 101086763) ^ 110 = (2 : ZMod 101086763) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 55 * (2 : ZMod 101086763) ^ 55 := by rw [pow_add]
          _ = 98768683 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 101086763) ^ 220 = 25825609 := by
        calc
          (2 : ZMod 101086763) ^ 220 = (2 : ZMod 101086763) ^ (110 + 110) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 110 * (2 : ZMod 101086763) ^ 110 := by rw [pow_add]
          _ = 25825609 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 101086763) ^ 440 = 8148210 := by
        calc
          (2 : ZMod 101086763) ^ 440 = (2 : ZMod 101086763) ^ (220 + 220) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 220 * (2 : ZMod 101086763) ^ 220 := by rw [pow_add]
          _ = 8148210 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 101086763) ^ 881 = 91399030 := by
        calc
          (2 : ZMod 101086763) ^ 881 = (2 : ZMod 101086763) ^ (440 + 440 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 440 * (2 : ZMod 101086763) ^ 440) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 91399030 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 101086763) ^ 1762 = 86220436 := by
        calc
          (2 : ZMod 101086763) ^ 1762 = (2 : ZMod 101086763) ^ (881 + 881) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 881 * (2 : ZMod 101086763) ^ 881 := by rw [pow_add]
          _ = 86220436 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 101086763) ^ 3525 = 41184879 := by
        calc
          (2 : ZMod 101086763) ^ 3525 = (2 : ZMod 101086763) ^ (1762 + 1762 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 1762 * (2 : ZMod 101086763) ^ 1762) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 41184879 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 101086763) ^ 7051 = 45701994 := by
        calc
          (2 : ZMod 101086763) ^ 7051 = (2 : ZMod 101086763) ^ (3525 + 3525 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 3525 * (2 : ZMod 101086763) ^ 3525) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 45701994 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 101086763) ^ 14102 = 70460037 := by
        calc
          (2 : ZMod 101086763) ^ 14102 = (2 : ZMod 101086763) ^ (7051 + 7051) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 7051 * (2 : ZMod 101086763) ^ 7051 := by rw [pow_add]
          _ = 70460037 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 101086763) ^ 28205 = 80207506 := by
        calc
          (2 : ZMod 101086763) ^ 28205 = (2 : ZMod 101086763) ^ (14102 + 14102 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 14102 * (2 : ZMod 101086763) ^ 14102) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 80207506 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 101086763) ^ 56410 = 35708191 := by
        calc
          (2 : ZMod 101086763) ^ 56410 = (2 : ZMod 101086763) ^ (28205 + 28205) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 28205 * (2 : ZMod 101086763) ^ 28205 := by rw [pow_add]
          _ = 35708191 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 101086763) ^ 112820 = 36815797 := by
        calc
          (2 : ZMod 101086763) ^ 112820 = (2 : ZMod 101086763) ^ (56410 + 56410) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 56410 * (2 : ZMod 101086763) ^ 56410 := by rw [pow_add]
          _ = 36815797 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 101086763) ^ 225640 = 51371153 := by
        calc
          (2 : ZMod 101086763) ^ 225640 = (2 : ZMod 101086763) ^ (112820 + 112820) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 112820 * (2 : ZMod 101086763) ^ 112820 := by rw [pow_add]
          _ = 51371153 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 101086763) ^ 451280 = 64848289 := by
        calc
          (2 : ZMod 101086763) ^ 451280 = (2 : ZMod 101086763) ^ (225640 + 225640) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 225640 * (2 : ZMod 101086763) ^ 225640 := by rw [pow_add]
          _ = 64848289 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 101086763) ^ 902560 = 65167295 := by
        calc
          (2 : ZMod 101086763) ^ 902560 = (2 : ZMod 101086763) ^ (451280 + 451280) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 451280 * (2 : ZMod 101086763) ^ 451280 := by rw [pow_add]
          _ = 65167295 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 101086763) ^ 1805120 = 18784662 := by
        calc
          (2 : ZMod 101086763) ^ 1805120 = (2 : ZMod 101086763) ^ (902560 + 902560) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 902560 * (2 : ZMod 101086763) ^ 902560 := by rw [pow_add]
          _ = 18784662 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 101086763) ^ 3610241 = 26787051 := by
        calc
          (2 : ZMod 101086763) ^ 3610241 = (2 : ZMod 101086763) ^ (1805120 + 1805120 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 1805120 * (2 : ZMod 101086763) ^ 1805120) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 26787051 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 101086763) ^ 7220483 = 21650408 := by
        calc
          (2 : ZMod 101086763) ^ 7220483 = (2 : ZMod 101086763) ^ (3610241 + 3610241 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 3610241 * (2 : ZMod 101086763) ^ 3610241) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 21650408 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 101086763) ^ 14440966 = 37841360 := by
        calc
          (2 : ZMod 101086763) ^ 14440966 = (2 : ZMod 101086763) ^ (7220483 + 7220483) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 7220483 * (2 : ZMod 101086763) ^ 7220483 := by rw [pow_add]
          _ = 37841360 := by rw [factor_1_22]; decide
      change (2 : ZMod 101086763) ^ 14440966 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (2 : ZMod 101086763) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 101086763) ^ 3 = 8 := by
        calc
          (2 : ZMod 101086763) ^ 3 = (2 : ZMod 101086763) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 1 * (2 : ZMod 101086763) ^ 1) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 101086763) ^ 7 = 128 := by
        calc
          (2 : ZMod 101086763) ^ 7 = (2 : ZMod 101086763) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = ((2 : ZMod 101086763) ^ 3 * (2 : ZMod 101086763) ^ 3) * (2 : ZMod 101086763) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 101086763) ^ 14 = 16384 := by
        calc
          (2 : ZMod 101086763) ^ 14 = (2 : ZMod 101086763) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 101086763) ^ n) (by norm_num)
          _ = (2 : ZMod 101086763) ^ 7 * (2 : ZMod 101086763) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_2_2]; decide
      change (2 : ZMod 101086763) ^ 14 ≠ 1
      rw [factor_2_3]
      decide

#print axioms prime_lucas_101086763

end TotientTailPeriodKiller
end Erdos249257
