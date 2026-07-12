import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_40430111 : Nat.Prime 40430111 := by
  apply lucas_primality 40430111 (7 : ZMod 40430111)
  ·
      have fermat_0 : (7 : ZMod 40430111) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 40430111) ^ 2 = 49 := by
        calc
          (7 : ZMod 40430111) ^ 2 = (7 : ZMod 40430111) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 1 * (7 : ZMod 40430111) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 40430111) ^ 4 = 2401 := by
        calc
          (7 : ZMod 40430111) ^ 4 = (7 : ZMod 40430111) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 2 * (7 : ZMod 40430111) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 40430111) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 40430111) ^ 9 = (7 : ZMod 40430111) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 4 * (7 : ZMod 40430111) ^ 4) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 40430111) ^ 19 = 14331669 := by
        calc
          (7 : ZMod 40430111) ^ 19 = (7 : ZMod 40430111) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 9 * (7 : ZMod 40430111) ^ 9) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 14331669 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 40430111) ^ 38 = 7283260 := by
        calc
          (7 : ZMod 40430111) ^ 38 = (7 : ZMod 40430111) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 19 * (7 : ZMod 40430111) ^ 19 := by rw [pow_add]
          _ = 7283260 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 40430111) ^ 77 = 37609119 := by
        calc
          (7 : ZMod 40430111) ^ 77 = (7 : ZMod 40430111) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 38 * (7 : ZMod 40430111) ^ 38) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 37609119 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 40430111) ^ 154 = 15825601 := by
        calc
          (7 : ZMod 40430111) ^ 154 = (7 : ZMod 40430111) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 77 * (7 : ZMod 40430111) ^ 77 := by rw [pow_add]
          _ = 15825601 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 40430111) ^ 308 = 28077160 := by
        calc
          (7 : ZMod 40430111) ^ 308 = (7 : ZMod 40430111) ^ (154 + 154) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 154 * (7 : ZMod 40430111) ^ 154 := by rw [pow_add]
          _ = 28077160 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 40430111) ^ 616 = 30461101 := by
        calc
          (7 : ZMod 40430111) ^ 616 = (7 : ZMod 40430111) ^ (308 + 308) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 308 * (7 : ZMod 40430111) ^ 308 := by rw [pow_add]
          _ = 30461101 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 40430111) ^ 1233 = 19028887 := by
        calc
          (7 : ZMod 40430111) ^ 1233 = (7 : ZMod 40430111) ^ (616 + 616 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 616 * (7 : ZMod 40430111) ^ 616) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 19028887 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 40430111) ^ 2467 = 23105174 := by
        calc
          (7 : ZMod 40430111) ^ 2467 = (7 : ZMod 40430111) ^ (1233 + 1233 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 1233 * (7 : ZMod 40430111) ^ 1233) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 23105174 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 40430111) ^ 4935 = 23994122 := by
        calc
          (7 : ZMod 40430111) ^ 4935 = (7 : ZMod 40430111) ^ (2467 + 2467 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 2467 * (7 : ZMod 40430111) ^ 2467) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 23994122 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 40430111) ^ 9870 = 23459865 := by
        calc
          (7 : ZMod 40430111) ^ 9870 = (7 : ZMod 40430111) ^ (4935 + 4935) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 4935 * (7 : ZMod 40430111) ^ 4935 := by rw [pow_add]
          _ = 23459865 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 40430111) ^ 19741 = 5905608 := by
        calc
          (7 : ZMod 40430111) ^ 19741 = (7 : ZMod 40430111) ^ (9870 + 9870 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 9870 * (7 : ZMod 40430111) ^ 9870) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 5905608 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 40430111) ^ 39482 = 19627845 := by
        calc
          (7 : ZMod 40430111) ^ 39482 = (7 : ZMod 40430111) ^ (19741 + 19741) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 19741 * (7 : ZMod 40430111) ^ 19741 := by rw [pow_add]
          _ = 19627845 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 40430111) ^ 78965 = 25464944 := by
        calc
          (7 : ZMod 40430111) ^ 78965 = (7 : ZMod 40430111) ^ (39482 + 39482 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 39482 * (7 : ZMod 40430111) ^ 39482) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 25464944 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 40430111) ^ 157930 = 11410927 := by
        calc
          (7 : ZMod 40430111) ^ 157930 = (7 : ZMod 40430111) ^ (78965 + 78965) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 78965 * (7 : ZMod 40430111) ^ 78965 := by rw [pow_add]
          _ = 11410927 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 40430111) ^ 315860 = 39512729 := by
        calc
          (7 : ZMod 40430111) ^ 315860 = (7 : ZMod 40430111) ^ (157930 + 157930) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 157930 * (7 : ZMod 40430111) ^ 157930 := by rw [pow_add]
          _ = 39512729 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 40430111) ^ 631720 = 36973459 := by
        calc
          (7 : ZMod 40430111) ^ 631720 = (7 : ZMod 40430111) ^ (315860 + 315860) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 315860 * (7 : ZMod 40430111) ^ 315860 := by rw [pow_add]
          _ = 36973459 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 40430111) ^ 1263440 = 11054941 := by
        calc
          (7 : ZMod 40430111) ^ 1263440 = (7 : ZMod 40430111) ^ (631720 + 631720) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 631720 * (7 : ZMod 40430111) ^ 631720 := by rw [pow_add]
          _ = 11054941 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 40430111) ^ 2526881 = 18276870 := by
        calc
          (7 : ZMod 40430111) ^ 2526881 = (7 : ZMod 40430111) ^ (1263440 + 1263440 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 1263440 * (7 : ZMod 40430111) ^ 1263440) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 18276870 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 40430111) ^ 5053763 = 25204500 := by
        calc
          (7 : ZMod 40430111) ^ 5053763 = (7 : ZMod 40430111) ^ (2526881 + 2526881 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 2526881 * (7 : ZMod 40430111) ^ 2526881) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 25204500 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 40430111) ^ 10107527 = 20390334 := by
        calc
          (7 : ZMod 40430111) ^ 10107527 = (7 : ZMod 40430111) ^ (5053763 + 5053763 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 5053763 * (7 : ZMod 40430111) ^ 5053763) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 20390334 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 40430111) ^ 20215055 = 40430110 := by
        calc
          (7 : ZMod 40430111) ^ 20215055 = (7 : ZMod 40430111) ^ (10107527 + 10107527 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 10107527 * (7 : ZMod 40430111) ^ 10107527) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 40430110 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 40430111) ^ 40430110 = 1 := by
        calc
          (7 : ZMod 40430111) ^ 40430110 = (7 : ZMod 40430111) ^ (20215055 + 20215055) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 20215055 * (7 : ZMod 40430111) ^ 20215055 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (577573, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (577573, 1)] : List FactorBlock).map factorBlockValue).prod = 40430111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 40430111) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 40430111) ^ 2 = 49 := by
        calc
          (7 : ZMod 40430111) ^ 2 = (7 : ZMod 40430111) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 1 * (7 : ZMod 40430111) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 40430111) ^ 4 = 2401 := by
        calc
          (7 : ZMod 40430111) ^ 4 = (7 : ZMod 40430111) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 2 * (7 : ZMod 40430111) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 40430111) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 40430111) ^ 9 = (7 : ZMod 40430111) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 4 * (7 : ZMod 40430111) ^ 4) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 40430111) ^ 19 = 14331669 := by
        calc
          (7 : ZMod 40430111) ^ 19 = (7 : ZMod 40430111) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 9 * (7 : ZMod 40430111) ^ 9) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 14331669 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 40430111) ^ 38 = 7283260 := by
        calc
          (7 : ZMod 40430111) ^ 38 = (7 : ZMod 40430111) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 19 * (7 : ZMod 40430111) ^ 19 := by rw [pow_add]
          _ = 7283260 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 40430111) ^ 77 = 37609119 := by
        calc
          (7 : ZMod 40430111) ^ 77 = (7 : ZMod 40430111) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 38 * (7 : ZMod 40430111) ^ 38) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 37609119 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 40430111) ^ 154 = 15825601 := by
        calc
          (7 : ZMod 40430111) ^ 154 = (7 : ZMod 40430111) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 77 * (7 : ZMod 40430111) ^ 77 := by rw [pow_add]
          _ = 15825601 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 40430111) ^ 308 = 28077160 := by
        calc
          (7 : ZMod 40430111) ^ 308 = (7 : ZMod 40430111) ^ (154 + 154) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 154 * (7 : ZMod 40430111) ^ 154 := by rw [pow_add]
          _ = 28077160 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 40430111) ^ 616 = 30461101 := by
        calc
          (7 : ZMod 40430111) ^ 616 = (7 : ZMod 40430111) ^ (308 + 308) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 308 * (7 : ZMod 40430111) ^ 308 := by rw [pow_add]
          _ = 30461101 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 40430111) ^ 1233 = 19028887 := by
        calc
          (7 : ZMod 40430111) ^ 1233 = (7 : ZMod 40430111) ^ (616 + 616 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 616 * (7 : ZMod 40430111) ^ 616) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 19028887 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 40430111) ^ 2467 = 23105174 := by
        calc
          (7 : ZMod 40430111) ^ 2467 = (7 : ZMod 40430111) ^ (1233 + 1233 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 1233 * (7 : ZMod 40430111) ^ 1233) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 23105174 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 40430111) ^ 4935 = 23994122 := by
        calc
          (7 : ZMod 40430111) ^ 4935 = (7 : ZMod 40430111) ^ (2467 + 2467 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 2467 * (7 : ZMod 40430111) ^ 2467) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 23994122 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 40430111) ^ 9870 = 23459865 := by
        calc
          (7 : ZMod 40430111) ^ 9870 = (7 : ZMod 40430111) ^ (4935 + 4935) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 4935 * (7 : ZMod 40430111) ^ 4935 := by rw [pow_add]
          _ = 23459865 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 40430111) ^ 19741 = 5905608 := by
        calc
          (7 : ZMod 40430111) ^ 19741 = (7 : ZMod 40430111) ^ (9870 + 9870 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 9870 * (7 : ZMod 40430111) ^ 9870) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 5905608 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 40430111) ^ 39482 = 19627845 := by
        calc
          (7 : ZMod 40430111) ^ 39482 = (7 : ZMod 40430111) ^ (19741 + 19741) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 19741 * (7 : ZMod 40430111) ^ 19741 := by rw [pow_add]
          _ = 19627845 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 40430111) ^ 78965 = 25464944 := by
        calc
          (7 : ZMod 40430111) ^ 78965 = (7 : ZMod 40430111) ^ (39482 + 39482 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 39482 * (7 : ZMod 40430111) ^ 39482) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 25464944 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 40430111) ^ 157930 = 11410927 := by
        calc
          (7 : ZMod 40430111) ^ 157930 = (7 : ZMod 40430111) ^ (78965 + 78965) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 78965 * (7 : ZMod 40430111) ^ 78965 := by rw [pow_add]
          _ = 11410927 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 40430111) ^ 315860 = 39512729 := by
        calc
          (7 : ZMod 40430111) ^ 315860 = (7 : ZMod 40430111) ^ (157930 + 157930) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 157930 * (7 : ZMod 40430111) ^ 157930 := by rw [pow_add]
          _ = 39512729 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 40430111) ^ 631720 = 36973459 := by
        calc
          (7 : ZMod 40430111) ^ 631720 = (7 : ZMod 40430111) ^ (315860 + 315860) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 315860 * (7 : ZMod 40430111) ^ 315860 := by rw [pow_add]
          _ = 36973459 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 40430111) ^ 1263440 = 11054941 := by
        calc
          (7 : ZMod 40430111) ^ 1263440 = (7 : ZMod 40430111) ^ (631720 + 631720) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 631720 * (7 : ZMod 40430111) ^ 631720 := by rw [pow_add]
          _ = 11054941 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 40430111) ^ 2526881 = 18276870 := by
        calc
          (7 : ZMod 40430111) ^ 2526881 = (7 : ZMod 40430111) ^ (1263440 + 1263440 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 1263440 * (7 : ZMod 40430111) ^ 1263440) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 18276870 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 40430111) ^ 5053763 = 25204500 := by
        calc
          (7 : ZMod 40430111) ^ 5053763 = (7 : ZMod 40430111) ^ (2526881 + 2526881 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 2526881 * (7 : ZMod 40430111) ^ 2526881) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 25204500 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 40430111) ^ 10107527 = 20390334 := by
        calc
          (7 : ZMod 40430111) ^ 10107527 = (7 : ZMod 40430111) ^ (5053763 + 5053763 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 5053763 * (7 : ZMod 40430111) ^ 5053763) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 20390334 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 40430111) ^ 20215055 = 40430110 := by
        calc
          (7 : ZMod 40430111) ^ 20215055 = (7 : ZMod 40430111) ^ (10107527 + 10107527 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 10107527 * (7 : ZMod 40430111) ^ 10107527) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 40430110 := by rw [factor_0_23]; decide
      change (7 : ZMod 40430111) ^ 20215055 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (7 : ZMod 40430111) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 40430111) ^ 3 = 343 := by
        calc
          (7 : ZMod 40430111) ^ 3 = (7 : ZMod 40430111) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 1 * (7 : ZMod 40430111) ^ 1) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 40430111) ^ 7 = 823543 := by
        calc
          (7 : ZMod 40430111) ^ 7 = (7 : ZMod 40430111) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 3 * (7 : ZMod 40430111) ^ 3) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 40430111) ^ 15 = 15295657 := by
        calc
          (7 : ZMod 40430111) ^ 15 = (7 : ZMod 40430111) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 7 * (7 : ZMod 40430111) ^ 7) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 15295657 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 40430111) ^ 30 = 38017505 := by
        calc
          (7 : ZMod 40430111) ^ 30 = (7 : ZMod 40430111) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 15 * (7 : ZMod 40430111) ^ 15 := by rw [pow_add]
          _ = 38017505 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 40430111) ^ 61 = 16715072 := by
        calc
          (7 : ZMod 40430111) ^ 61 = (7 : ZMod 40430111) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 30 * (7 : ZMod 40430111) ^ 30) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 16715072 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 40430111) ^ 123 = 29081925 := by
        calc
          (7 : ZMod 40430111) ^ 123 = (7 : ZMod 40430111) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 61 * (7 : ZMod 40430111) ^ 61) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 29081925 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 40430111) ^ 246 = 20664294 := by
        calc
          (7 : ZMod 40430111) ^ 246 = (7 : ZMod 40430111) ^ (123 + 123) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 123 * (7 : ZMod 40430111) ^ 123 := by rw [pow_add]
          _ = 20664294 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 40430111) ^ 493 = 27993197 := by
        calc
          (7 : ZMod 40430111) ^ 493 = (7 : ZMod 40430111) ^ (246 + 246 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 246 * (7 : ZMod 40430111) ^ 246) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 27993197 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 40430111) ^ 987 = 29870492 := by
        calc
          (7 : ZMod 40430111) ^ 987 = (7 : ZMod 40430111) ^ (493 + 493 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 493 * (7 : ZMod 40430111) ^ 493) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 29870492 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 40430111) ^ 1974 = 35029159 := by
        calc
          (7 : ZMod 40430111) ^ 1974 = (7 : ZMod 40430111) ^ (987 + 987) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 987 * (7 : ZMod 40430111) ^ 987 := by rw [pow_add]
          _ = 35029159 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 40430111) ^ 3948 = 38280026 := by
        calc
          (7 : ZMod 40430111) ^ 3948 = (7 : ZMod 40430111) ^ (1974 + 1974) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 1974 * (7 : ZMod 40430111) ^ 1974 := by rw [pow_add]
          _ = 38280026 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 40430111) ^ 7896 = 5755263 := by
        calc
          (7 : ZMod 40430111) ^ 7896 = (7 : ZMod 40430111) ^ (3948 + 3948) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 3948 * (7 : ZMod 40430111) ^ 3948 := by rw [pow_add]
          _ = 5755263 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 40430111) ^ 15793 = 15583835 := by
        calc
          (7 : ZMod 40430111) ^ 15793 = (7 : ZMod 40430111) ^ (7896 + 7896 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 7896 * (7 : ZMod 40430111) ^ 7896) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 15583835 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 40430111) ^ 31586 = 39541648 := by
        calc
          (7 : ZMod 40430111) ^ 31586 = (7 : ZMod 40430111) ^ (15793 + 15793) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 15793 * (7 : ZMod 40430111) ^ 15793 := by rw [pow_add]
          _ = 39541648 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 40430111) ^ 63172 = 9015205 := by
        calc
          (7 : ZMod 40430111) ^ 63172 = (7 : ZMod 40430111) ^ (31586 + 31586) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 31586 * (7 : ZMod 40430111) ^ 31586 := by rw [pow_add]
          _ = 9015205 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 40430111) ^ 126344 = 18296273 := by
        calc
          (7 : ZMod 40430111) ^ 126344 = (7 : ZMod 40430111) ^ (63172 + 63172) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 63172 * (7 : ZMod 40430111) ^ 63172 := by rw [pow_add]
          _ = 18296273 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 40430111) ^ 252688 = 8761730 := by
        calc
          (7 : ZMod 40430111) ^ 252688 = (7 : ZMod 40430111) ^ (126344 + 126344) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 126344 * (7 : ZMod 40430111) ^ 126344 := by rw [pow_add]
          _ = 8761730 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 40430111) ^ 505376 = 26428320 := by
        calc
          (7 : ZMod 40430111) ^ 505376 = (7 : ZMod 40430111) ^ (252688 + 252688) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 252688 * (7 : ZMod 40430111) ^ 252688 := by rw [pow_add]
          _ = 26428320 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 40430111) ^ 1010752 = 14796249 := by
        calc
          (7 : ZMod 40430111) ^ 1010752 = (7 : ZMod 40430111) ^ (505376 + 505376) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 505376 * (7 : ZMod 40430111) ^ 505376 := by rw [pow_add]
          _ = 14796249 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 40430111) ^ 2021505 = 18996339 := by
        calc
          (7 : ZMod 40430111) ^ 2021505 = (7 : ZMod 40430111) ^ (1010752 + 1010752 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 1010752 * (7 : ZMod 40430111) ^ 1010752) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 18996339 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 40430111) ^ 4043011 = 33619762 := by
        calc
          (7 : ZMod 40430111) ^ 4043011 = (7 : ZMod 40430111) ^ (2021505 + 2021505 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 2021505 * (7 : ZMod 40430111) ^ 2021505) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 33619762 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 40430111) ^ 8086022 = 36614266 := by
        calc
          (7 : ZMod 40430111) ^ 8086022 = (7 : ZMod 40430111) ^ (4043011 + 4043011) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 4043011 * (7 : ZMod 40430111) ^ 4043011 := by rw [pow_add]
          _ = 36614266 := by rw [factor_1_21]; decide
      change (7 : ZMod 40430111) ^ 8086022 ≠ 1
      rw [factor_1_22]
      decide
    ·
      have factor_2_0 : (7 : ZMod 40430111) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 40430111) ^ 2 = 49 := by
        calc
          (7 : ZMod 40430111) ^ 2 = (7 : ZMod 40430111) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 1 * (7 : ZMod 40430111) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 40430111) ^ 5 = 16807 := by
        calc
          (7 : ZMod 40430111) ^ 5 = (7 : ZMod 40430111) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 2 * (7 : ZMod 40430111) ^ 2) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 40430111) ^ 11 = 36681415 := by
        calc
          (7 : ZMod 40430111) ^ 11 = (7 : ZMod 40430111) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 5 * (7 : ZMod 40430111) ^ 5) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 36681415 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 40430111) ^ 22 = 23719036 := by
        calc
          (7 : ZMod 40430111) ^ 22 = (7 : ZMod 40430111) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 11 * (7 : ZMod 40430111) ^ 11 := by rw [pow_add]
          _ = 23719036 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 40430111) ^ 44 = 32913317 := by
        calc
          (7 : ZMod 40430111) ^ 44 = (7 : ZMod 40430111) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 22 * (7 : ZMod 40430111) ^ 22 := by rw [pow_add]
          _ = 32913317 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 40430111) ^ 88 = 20302939 := by
        calc
          (7 : ZMod 40430111) ^ 88 = (7 : ZMod 40430111) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 44 * (7 : ZMod 40430111) ^ 44 := by rw [pow_add]
          _ = 20302939 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 40430111) ^ 176 = 11465899 := by
        calc
          (7 : ZMod 40430111) ^ 176 = (7 : ZMod 40430111) ^ (88 + 88) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 88 * (7 : ZMod 40430111) ^ 88 := by rw [pow_add]
          _ = 11465899 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 40430111) ^ 352 = 5358835 := by
        calc
          (7 : ZMod 40430111) ^ 352 = (7 : ZMod 40430111) ^ (176 + 176) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 176 * (7 : ZMod 40430111) ^ 176 := by rw [pow_add]
          _ = 5358835 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 40430111) ^ 705 = 22675134 := by
        calc
          (7 : ZMod 40430111) ^ 705 = (7 : ZMod 40430111) ^ (352 + 352 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 352 * (7 : ZMod 40430111) ^ 352) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 22675134 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 40430111) ^ 1410 = 13018100 := by
        calc
          (7 : ZMod 40430111) ^ 1410 = (7 : ZMod 40430111) ^ (705 + 705) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 705 * (7 : ZMod 40430111) ^ 705 := by rw [pow_add]
          _ = 13018100 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 40430111) ^ 2820 = 31331300 := by
        calc
          (7 : ZMod 40430111) ^ 2820 = (7 : ZMod 40430111) ^ (1410 + 1410) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 1410 * (7 : ZMod 40430111) ^ 1410 := by rw [pow_add]
          _ = 31331300 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 40430111) ^ 5640 = 27620131 := by
        calc
          (7 : ZMod 40430111) ^ 5640 = (7 : ZMod 40430111) ^ (2820 + 2820) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 2820 * (7 : ZMod 40430111) ^ 2820 := by rw [pow_add]
          _ = 27620131 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 40430111) ^ 11280 = 36299594 := by
        calc
          (7 : ZMod 40430111) ^ 11280 = (7 : ZMod 40430111) ^ (5640 + 5640) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 5640 * (7 : ZMod 40430111) ^ 5640 := by rw [pow_add]
          _ = 36299594 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 40430111) ^ 22561 = 32293572 := by
        calc
          (7 : ZMod 40430111) ^ 22561 = (7 : ZMod 40430111) ^ (11280 + 11280 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 11280 * (7 : ZMod 40430111) ^ 11280) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 32293572 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 40430111) ^ 45122 = 11318907 := by
        calc
          (7 : ZMod 40430111) ^ 45122 = (7 : ZMod 40430111) ^ (22561 + 22561) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 22561 * (7 : ZMod 40430111) ^ 22561 := by rw [pow_add]
          _ = 11318907 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 40430111) ^ 90245 = 37412773 := by
        calc
          (7 : ZMod 40430111) ^ 90245 = (7 : ZMod 40430111) ^ (45122 + 45122 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 45122 * (7 : ZMod 40430111) ^ 45122) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 37412773 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 40430111) ^ 180491 = 33263631 := by
        calc
          (7 : ZMod 40430111) ^ 180491 = (7 : ZMod 40430111) ^ (90245 + 90245 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 90245 * (7 : ZMod 40430111) ^ 90245) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 33263631 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 40430111) ^ 360983 = 14378479 := by
        calc
          (7 : ZMod 40430111) ^ 360983 = (7 : ZMod 40430111) ^ (180491 + 180491 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 180491 * (7 : ZMod 40430111) ^ 180491) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 14378479 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 40430111) ^ 721966 = 32421500 := by
        calc
          (7 : ZMod 40430111) ^ 721966 = (7 : ZMod 40430111) ^ (360983 + 360983) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 360983 * (7 : ZMod 40430111) ^ 360983 := by rw [pow_add]
          _ = 32421500 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 40430111) ^ 1443932 = 7220253 := by
        calc
          (7 : ZMod 40430111) ^ 1443932 = (7 : ZMod 40430111) ^ (721966 + 721966) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 721966 * (7 : ZMod 40430111) ^ 721966 := by rw [pow_add]
          _ = 7220253 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 40430111) ^ 2887865 = 8576069 := by
        calc
          (7 : ZMod 40430111) ^ 2887865 = (7 : ZMod 40430111) ^ (1443932 + 1443932 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 1443932 * (7 : ZMod 40430111) ^ 1443932) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 8576069 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 40430111) ^ 5775730 = 37905779 := by
        calc
          (7 : ZMod 40430111) ^ 5775730 = (7 : ZMod 40430111) ^ (2887865 + 2887865) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 2887865 * (7 : ZMod 40430111) ^ 2887865 := by rw [pow_add]
          _ = 37905779 := by rw [factor_2_21]; decide
      change (7 : ZMod 40430111) ^ 5775730 ≠ 1
      rw [factor_2_22]
      decide
    ·
      have factor_3_0 : (7 : ZMod 40430111) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 40430111) ^ 2 = 49 := by
        calc
          (7 : ZMod 40430111) ^ 2 = (7 : ZMod 40430111) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 1 * (7 : ZMod 40430111) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 40430111) ^ 4 = 2401 := by
        calc
          (7 : ZMod 40430111) ^ 4 = (7 : ZMod 40430111) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 2 * (7 : ZMod 40430111) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 40430111) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 40430111) ^ 8 = (7 : ZMod 40430111) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 4 * (7 : ZMod 40430111) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 40430111) ^ 17 = 21745195 := by
        calc
          (7 : ZMod 40430111) ^ 17 = (7 : ZMod 40430111) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 8 * (7 : ZMod 40430111) ^ 8) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 21745195 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 40430111) ^ 35 = 2732291 := by
        calc
          (7 : ZMod 40430111) ^ 35 = (7 : ZMod 40430111) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = ((7 : ZMod 40430111) ^ 17 * (7 : ZMod 40430111) ^ 17) * (7 : ZMod 40430111) := by rw [pow_succ, pow_add]
          _ = 2732291 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 40430111) ^ 70 = 34542642 := by
        calc
          (7 : ZMod 40430111) ^ 70 = (7 : ZMod 40430111) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (7 : ZMod 40430111) ^ n) (by norm_num)
          _ = (7 : ZMod 40430111) ^ 35 * (7 : ZMod 40430111) ^ 35 := by rw [pow_add]
          _ = 34542642 := by rw [factor_3_5]; decide
      change (7 : ZMod 40430111) ^ 70 ≠ 1
      rw [factor_3_6]
      decide

#print axioms prime_lucas_40430111

end TotientTailPeriodKiller
end Erdos249257
