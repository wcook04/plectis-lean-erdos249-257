import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_43693841 : Nat.Prime 43693841 := by
  apply lucas_primality 43693841 (3 : ZMod 43693841)
  ·
      have fermat_0 : (3 : ZMod 43693841) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 43693841) ^ 2 = 9 := by
        calc
          (3 : ZMod 43693841) ^ 2 = (3 : ZMod 43693841) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 1 * (3 : ZMod 43693841) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 43693841) ^ 5 = 243 := by
        calc
          (3 : ZMod 43693841) ^ 5 = (3 : ZMod 43693841) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 2 * (3 : ZMod 43693841) ^ 2) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 43693841) ^ 10 = 59049 := by
        calc
          (3 : ZMod 43693841) ^ 10 = (3 : ZMod 43693841) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 5 * (3 : ZMod 43693841) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 43693841) ^ 20 = 34970962 := by
        calc
          (3 : ZMod 43693841) ^ 20 = (3 : ZMod 43693841) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 10 * (3 : ZMod 43693841) ^ 10 := by rw [pow_add]
          _ = 34970962 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 43693841) ^ 41 = 9361472 := by
        calc
          (3 : ZMod 43693841) ^ 41 = (3 : ZMod 43693841) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 20 * (3 : ZMod 43693841) ^ 20) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 9361472 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 43693841) ^ 83 = 39911704 := by
        calc
          (3 : ZMod 43693841) ^ 83 = (3 : ZMod 43693841) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 41 * (3 : ZMod 43693841) ^ 41) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 39911704 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 43693841) ^ 166 = 26926348 := by
        calc
          (3 : ZMod 43693841) ^ 166 = (3 : ZMod 43693841) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 83 * (3 : ZMod 43693841) ^ 83 := by rw [pow_add]
          _ = 26926348 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 43693841) ^ 333 = 1610392 := by
        calc
          (3 : ZMod 43693841) ^ 333 = (3 : ZMod 43693841) ^ (166 + 166 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 166 * (3 : ZMod 43693841) ^ 166) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 1610392 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 43693841) ^ 666 = 1848791 := by
        calc
          (3 : ZMod 43693841) ^ 666 = (3 : ZMod 43693841) ^ (333 + 333) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 333 * (3 : ZMod 43693841) ^ 333 := by rw [pow_add]
          _ = 1848791 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 43693841) ^ 1333 = 13879163 := by
        calc
          (3 : ZMod 43693841) ^ 1333 = (3 : ZMod 43693841) ^ (666 + 666 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 666 * (3 : ZMod 43693841) ^ 666) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 13879163 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 43693841) ^ 2666 = 7599032 := by
        calc
          (3 : ZMod 43693841) ^ 2666 = (3 : ZMod 43693841) ^ (1333 + 1333) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 1333 * (3 : ZMod 43693841) ^ 1333 := by rw [pow_add]
          _ = 7599032 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 43693841) ^ 5333 = 6804866 := by
        calc
          (3 : ZMod 43693841) ^ 5333 = (3 : ZMod 43693841) ^ (2666 + 2666 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 2666 * (3 : ZMod 43693841) ^ 2666) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 6804866 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 43693841) ^ 10667 = 22430585 := by
        calc
          (3 : ZMod 43693841) ^ 10667 = (3 : ZMod 43693841) ^ (5333 + 5333 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 5333 * (3 : ZMod 43693841) ^ 5333) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 22430585 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 43693841) ^ 21334 = 16140664 := by
        calc
          (3 : ZMod 43693841) ^ 21334 = (3 : ZMod 43693841) ^ (10667 + 10667) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 10667 * (3 : ZMod 43693841) ^ 10667 := by rw [pow_add]
          _ = 16140664 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 43693841) ^ 42669 = 8717028 := by
        calc
          (3 : ZMod 43693841) ^ 42669 = (3 : ZMod 43693841) ^ (21334 + 21334 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 21334 * (3 : ZMod 43693841) ^ 21334) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 8717028 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 43693841) ^ 85339 = 5723947 := by
        calc
          (3 : ZMod 43693841) ^ 85339 = (3 : ZMod 43693841) ^ (42669 + 42669 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 42669 * (3 : ZMod 43693841) ^ 42669) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 5723947 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 43693841) ^ 170679 = 14244015 := by
        calc
          (3 : ZMod 43693841) ^ 170679 = (3 : ZMod 43693841) ^ (85339 + 85339 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 85339 * (3 : ZMod 43693841) ^ 85339) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 14244015 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 43693841) ^ 341358 = 5881294 := by
        calc
          (3 : ZMod 43693841) ^ 341358 = (3 : ZMod 43693841) ^ (170679 + 170679) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 170679 * (3 : ZMod 43693841) ^ 170679 := by rw [pow_add]
          _ = 5881294 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 43693841) ^ 682716 = 1600560 := by
        calc
          (3 : ZMod 43693841) ^ 682716 = (3 : ZMod 43693841) ^ (341358 + 341358) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 341358 * (3 : ZMod 43693841) ^ 341358 := by rw [pow_add]
          _ = 1600560 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 43693841) ^ 1365432 = 22415770 := by
        calc
          (3 : ZMod 43693841) ^ 1365432 = (3 : ZMod 43693841) ^ (682716 + 682716) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 682716 * (3 : ZMod 43693841) ^ 682716 := by rw [pow_add]
          _ = 22415770 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 43693841) ^ 2730865 = 34118914 := by
        calc
          (3 : ZMod 43693841) ^ 2730865 = (3 : ZMod 43693841) ^ (1365432 + 1365432 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 1365432 * (3 : ZMod 43693841) ^ 1365432) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 34118914 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 43693841) ^ 5461730 = 23379991 := by
        calc
          (3 : ZMod 43693841) ^ 5461730 = (3 : ZMod 43693841) ^ (2730865 + 2730865) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 2730865 * (3 : ZMod 43693841) ^ 2730865 := by rw [pow_add]
          _ = 23379991 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 43693841) ^ 10923460 = 2527120 := by
        calc
          (3 : ZMod 43693841) ^ 10923460 = (3 : ZMod 43693841) ^ (5461730 + 5461730) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 5461730 * (3 : ZMod 43693841) ^ 5461730 := by rw [pow_add]
          _ = 2527120 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 43693841) ^ 21846920 = 43693840 := by
        calc
          (3 : ZMod 43693841) ^ 21846920 = (3 : ZMod 43693841) ^ (10923460 + 10923460) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 10923460 * (3 : ZMod 43693841) ^ 10923460 := by rw [pow_add]
          _ = 43693840 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 43693841) ^ 43693840 = 1 := by
        calc
          (3 : ZMod 43693841) ^ 43693840 = (3 : ZMod 43693841) ^ (21846920 + 21846920) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 21846920 * (3 : ZMod 43693841) ^ 21846920 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (546173, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (546173, 1)] : List FactorBlock).map factorBlockValue).prod = 43693841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 43693841) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 43693841) ^ 2 = 9 := by
        calc
          (3 : ZMod 43693841) ^ 2 = (3 : ZMod 43693841) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 1 * (3 : ZMod 43693841) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 43693841) ^ 5 = 243 := by
        calc
          (3 : ZMod 43693841) ^ 5 = (3 : ZMod 43693841) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 2 * (3 : ZMod 43693841) ^ 2) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 43693841) ^ 10 = 59049 := by
        calc
          (3 : ZMod 43693841) ^ 10 = (3 : ZMod 43693841) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 5 * (3 : ZMod 43693841) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 43693841) ^ 20 = 34970962 := by
        calc
          (3 : ZMod 43693841) ^ 20 = (3 : ZMod 43693841) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 10 * (3 : ZMod 43693841) ^ 10 := by rw [pow_add]
          _ = 34970962 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 43693841) ^ 41 = 9361472 := by
        calc
          (3 : ZMod 43693841) ^ 41 = (3 : ZMod 43693841) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 20 * (3 : ZMod 43693841) ^ 20) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 9361472 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 43693841) ^ 83 = 39911704 := by
        calc
          (3 : ZMod 43693841) ^ 83 = (3 : ZMod 43693841) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 41 * (3 : ZMod 43693841) ^ 41) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 39911704 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 43693841) ^ 166 = 26926348 := by
        calc
          (3 : ZMod 43693841) ^ 166 = (3 : ZMod 43693841) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 83 * (3 : ZMod 43693841) ^ 83 := by rw [pow_add]
          _ = 26926348 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 43693841) ^ 333 = 1610392 := by
        calc
          (3 : ZMod 43693841) ^ 333 = (3 : ZMod 43693841) ^ (166 + 166 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 166 * (3 : ZMod 43693841) ^ 166) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 1610392 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 43693841) ^ 666 = 1848791 := by
        calc
          (3 : ZMod 43693841) ^ 666 = (3 : ZMod 43693841) ^ (333 + 333) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 333 * (3 : ZMod 43693841) ^ 333 := by rw [pow_add]
          _ = 1848791 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 43693841) ^ 1333 = 13879163 := by
        calc
          (3 : ZMod 43693841) ^ 1333 = (3 : ZMod 43693841) ^ (666 + 666 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 666 * (3 : ZMod 43693841) ^ 666) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 13879163 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 43693841) ^ 2666 = 7599032 := by
        calc
          (3 : ZMod 43693841) ^ 2666 = (3 : ZMod 43693841) ^ (1333 + 1333) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 1333 * (3 : ZMod 43693841) ^ 1333 := by rw [pow_add]
          _ = 7599032 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 43693841) ^ 5333 = 6804866 := by
        calc
          (3 : ZMod 43693841) ^ 5333 = (3 : ZMod 43693841) ^ (2666 + 2666 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 2666 * (3 : ZMod 43693841) ^ 2666) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 6804866 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 43693841) ^ 10667 = 22430585 := by
        calc
          (3 : ZMod 43693841) ^ 10667 = (3 : ZMod 43693841) ^ (5333 + 5333 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 5333 * (3 : ZMod 43693841) ^ 5333) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 22430585 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 43693841) ^ 21334 = 16140664 := by
        calc
          (3 : ZMod 43693841) ^ 21334 = (3 : ZMod 43693841) ^ (10667 + 10667) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 10667 * (3 : ZMod 43693841) ^ 10667 := by rw [pow_add]
          _ = 16140664 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 43693841) ^ 42669 = 8717028 := by
        calc
          (3 : ZMod 43693841) ^ 42669 = (3 : ZMod 43693841) ^ (21334 + 21334 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 21334 * (3 : ZMod 43693841) ^ 21334) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 8717028 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 43693841) ^ 85339 = 5723947 := by
        calc
          (3 : ZMod 43693841) ^ 85339 = (3 : ZMod 43693841) ^ (42669 + 42669 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 42669 * (3 : ZMod 43693841) ^ 42669) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 5723947 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 43693841) ^ 170679 = 14244015 := by
        calc
          (3 : ZMod 43693841) ^ 170679 = (3 : ZMod 43693841) ^ (85339 + 85339 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 85339 * (3 : ZMod 43693841) ^ 85339) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 14244015 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 43693841) ^ 341358 = 5881294 := by
        calc
          (3 : ZMod 43693841) ^ 341358 = (3 : ZMod 43693841) ^ (170679 + 170679) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 170679 * (3 : ZMod 43693841) ^ 170679 := by rw [pow_add]
          _ = 5881294 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 43693841) ^ 682716 = 1600560 := by
        calc
          (3 : ZMod 43693841) ^ 682716 = (3 : ZMod 43693841) ^ (341358 + 341358) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 341358 * (3 : ZMod 43693841) ^ 341358 := by rw [pow_add]
          _ = 1600560 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 43693841) ^ 1365432 = 22415770 := by
        calc
          (3 : ZMod 43693841) ^ 1365432 = (3 : ZMod 43693841) ^ (682716 + 682716) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 682716 * (3 : ZMod 43693841) ^ 682716 := by rw [pow_add]
          _ = 22415770 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 43693841) ^ 2730865 = 34118914 := by
        calc
          (3 : ZMod 43693841) ^ 2730865 = (3 : ZMod 43693841) ^ (1365432 + 1365432 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 1365432 * (3 : ZMod 43693841) ^ 1365432) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 34118914 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 43693841) ^ 5461730 = 23379991 := by
        calc
          (3 : ZMod 43693841) ^ 5461730 = (3 : ZMod 43693841) ^ (2730865 + 2730865) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 2730865 * (3 : ZMod 43693841) ^ 2730865 := by rw [pow_add]
          _ = 23379991 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 43693841) ^ 10923460 = 2527120 := by
        calc
          (3 : ZMod 43693841) ^ 10923460 = (3 : ZMod 43693841) ^ (5461730 + 5461730) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 5461730 * (3 : ZMod 43693841) ^ 5461730 := by rw [pow_add]
          _ = 2527120 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 43693841) ^ 21846920 = 43693840 := by
        calc
          (3 : ZMod 43693841) ^ 21846920 = (3 : ZMod 43693841) ^ (10923460 + 10923460) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 10923460 * (3 : ZMod 43693841) ^ 10923460 := by rw [pow_add]
          _ = 43693840 := by rw [factor_0_23]; decide
      change (3 : ZMod 43693841) ^ 21846920 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (3 : ZMod 43693841) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 43693841) ^ 2 = 9 := by
        calc
          (3 : ZMod 43693841) ^ 2 = (3 : ZMod 43693841) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 1 * (3 : ZMod 43693841) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 43693841) ^ 4 = 81 := by
        calc
          (3 : ZMod 43693841) ^ 4 = (3 : ZMod 43693841) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 2 * (3 : ZMod 43693841) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 43693841) ^ 8 = 6561 := by
        calc
          (3 : ZMod 43693841) ^ 8 = (3 : ZMod 43693841) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 4 * (3 : ZMod 43693841) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 43693841) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 43693841) ^ 16 = (3 : ZMod 43693841) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 8 * (3 : ZMod 43693841) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 43693841) ^ 33 = 7566768 := by
        calc
          (3 : ZMod 43693841) ^ 33 = (3 : ZMod 43693841) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 16 * (3 : ZMod 43693841) ^ 16) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 7566768 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 43693841) ^ 66 = 5657834 := by
        calc
          (3 : ZMod 43693841) ^ 66 = (3 : ZMod 43693841) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 33 * (3 : ZMod 43693841) ^ 33 := by rw [pow_add]
          _ = 5657834 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 43693841) ^ 133 = 5477521 := by
        calc
          (3 : ZMod 43693841) ^ 133 = (3 : ZMod 43693841) ^ (66 + 66 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 66 * (3 : ZMod 43693841) ^ 66) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 5477521 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 43693841) ^ 266 = 30199812 := by
        calc
          (3 : ZMod 43693841) ^ 266 = (3 : ZMod 43693841) ^ (133 + 133) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 133 * (3 : ZMod 43693841) ^ 133 := by rw [pow_add]
          _ = 30199812 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 43693841) ^ 533 = 26026465 := by
        calc
          (3 : ZMod 43693841) ^ 533 = (3 : ZMod 43693841) ^ (266 + 266 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 266 * (3 : ZMod 43693841) ^ 266) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 26026465 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 43693841) ^ 1066 = 2141425 := by
        calc
          (3 : ZMod 43693841) ^ 1066 = (3 : ZMod 43693841) ^ (533 + 533) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 533 * (3 : ZMod 43693841) ^ 533 := by rw [pow_add]
          _ = 2141425 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 43693841) ^ 2133 = 9865343 := by
        calc
          (3 : ZMod 43693841) ^ 2133 = (3 : ZMod 43693841) ^ (1066 + 1066 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 1066 * (3 : ZMod 43693841) ^ 1066) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 9865343 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 43693841) ^ 4266 = 20249019 := by
        calc
          (3 : ZMod 43693841) ^ 4266 = (3 : ZMod 43693841) ^ (2133 + 2133) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 2133 * (3 : ZMod 43693841) ^ 2133 := by rw [pow_add]
          _ = 20249019 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 43693841) ^ 8533 = 42350380 := by
        calc
          (3 : ZMod 43693841) ^ 8533 = (3 : ZMod 43693841) ^ (4266 + 4266 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 4266 * (3 : ZMod 43693841) ^ 4266) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 42350380 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 43693841) ^ 17067 = 34211161 := by
        calc
          (3 : ZMod 43693841) ^ 17067 = (3 : ZMod 43693841) ^ (8533 + 8533 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 8533 * (3 : ZMod 43693841) ^ 8533) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 34211161 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 43693841) ^ 34135 = 26611409 := by
        calc
          (3 : ZMod 43693841) ^ 34135 = (3 : ZMod 43693841) ^ (17067 + 17067 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 17067 * (3 : ZMod 43693841) ^ 17067) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 26611409 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 43693841) ^ 68271 = 17116121 := by
        calc
          (3 : ZMod 43693841) ^ 68271 = (3 : ZMod 43693841) ^ (34135 + 34135 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 34135 * (3 : ZMod 43693841) ^ 34135) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 17116121 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 43693841) ^ 136543 = 4673708 := by
        calc
          (3 : ZMod 43693841) ^ 136543 = (3 : ZMod 43693841) ^ (68271 + 68271 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 68271 * (3 : ZMod 43693841) ^ 68271) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 4673708 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 43693841) ^ 273086 = 34088862 := by
        calc
          (3 : ZMod 43693841) ^ 273086 = (3 : ZMod 43693841) ^ (136543 + 136543) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 136543 * (3 : ZMod 43693841) ^ 136543 := by rw [pow_add]
          _ = 34088862 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 43693841) ^ 546173 = 26293893 := by
        calc
          (3 : ZMod 43693841) ^ 546173 = (3 : ZMod 43693841) ^ (273086 + 273086 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 273086 * (3 : ZMod 43693841) ^ 273086) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 26293893 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 43693841) ^ 1092346 = 26912583 := by
        calc
          (3 : ZMod 43693841) ^ 1092346 = (3 : ZMod 43693841) ^ (546173 + 546173) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 546173 * (3 : ZMod 43693841) ^ 546173 := by rw [pow_add]
          _ = 26912583 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 43693841) ^ 2184692 = 13453397 := by
        calc
          (3 : ZMod 43693841) ^ 2184692 = (3 : ZMod 43693841) ^ (1092346 + 1092346) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 1092346 * (3 : ZMod 43693841) ^ 1092346 := by rw [pow_add]
          _ = 13453397 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 43693841) ^ 4369384 = 19388489 := by
        calc
          (3 : ZMod 43693841) ^ 4369384 = (3 : ZMod 43693841) ^ (2184692 + 2184692) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 2184692 * (3 : ZMod 43693841) ^ 2184692 := by rw [pow_add]
          _ = 19388489 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 43693841) ^ 8738768 = 11348089 := by
        calc
          (3 : ZMod 43693841) ^ 8738768 = (3 : ZMod 43693841) ^ (4369384 + 4369384) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 4369384 * (3 : ZMod 43693841) ^ 4369384 := by rw [pow_add]
          _ = 11348089 := by rw [factor_1_22]; decide
      change (3 : ZMod 43693841) ^ 8738768 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (3 : ZMod 43693841) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 43693841) ^ 2 = 9 := by
        calc
          (3 : ZMod 43693841) ^ 2 = (3 : ZMod 43693841) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 1 * (3 : ZMod 43693841) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 43693841) ^ 5 = 243 := by
        calc
          (3 : ZMod 43693841) ^ 5 = (3 : ZMod 43693841) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = ((3 : ZMod 43693841) ^ 2 * (3 : ZMod 43693841) ^ 2) * (3 : ZMod 43693841) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 43693841) ^ 10 = 59049 := by
        calc
          (3 : ZMod 43693841) ^ 10 = (3 : ZMod 43693841) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 5 * (3 : ZMod 43693841) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 43693841) ^ 20 = 34970962 := by
        calc
          (3 : ZMod 43693841) ^ 20 = (3 : ZMod 43693841) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 10 * (3 : ZMod 43693841) ^ 10 := by rw [pow_add]
          _ = 34970962 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 43693841) ^ 40 = 32249718 := by
        calc
          (3 : ZMod 43693841) ^ 40 = (3 : ZMod 43693841) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 20 * (3 : ZMod 43693841) ^ 20 := by rw [pow_add]
          _ = 32249718 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 43693841) ^ 80 = 32225729 := by
        calc
          (3 : ZMod 43693841) ^ 80 = (3 : ZMod 43693841) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (3 : ZMod 43693841) ^ n) (by norm_num)
          _ = (3 : ZMod 43693841) ^ 40 * (3 : ZMod 43693841) ^ 40 := by rw [pow_add]
          _ = 32225729 := by rw [factor_2_5]; decide
      change (3 : ZMod 43693841) ^ 80 ≠ 1
      rw [factor_2_6]
      decide

#print axioms prime_lucas_43693841

end TotientTailPeriodKiller
end Erdos249257
