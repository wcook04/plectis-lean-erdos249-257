import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=23 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_334639307 : Nat.Prime 334639307 := by
  apply lucas_primality 334639307 (2 : ZMod 334639307)
  ·
      have fermat_0 : (2 : ZMod 334639307) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 334639307) ^ 2 = 4 := by
        calc
          (2 : ZMod 334639307) ^ 2 = (2 : ZMod 334639307) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 1 * (2 : ZMod 334639307) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 334639307) ^ 4 = 16 := by
        calc
          (2 : ZMod 334639307) ^ 4 = (2 : ZMod 334639307) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 2 * (2 : ZMod 334639307) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 334639307) ^ 9 = 512 := by
        calc
          (2 : ZMod 334639307) ^ 9 = (2 : ZMod 334639307) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 4 * (2 : ZMod 334639307) ^ 4) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 334639307) ^ 19 = 524288 := by
        calc
          (2 : ZMod 334639307) ^ 19 = (2 : ZMod 334639307) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 9 * (2 : ZMod 334639307) ^ 9) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 334639307) ^ 39 = 278071794 := by
        calc
          (2 : ZMod 334639307) ^ 39 = (2 : ZMod 334639307) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 19 * (2 : ZMod 334639307) ^ 19) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 278071794 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 334639307) ^ 79 = 126480827 := by
        calc
          (2 : ZMod 334639307) ^ 79 = (2 : ZMod 334639307) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 39 * (2 : ZMod 334639307) ^ 39) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 126480827 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 334639307) ^ 159 = 309602723 := by
        calc
          (2 : ZMod 334639307) ^ 159 = (2 : ZMod 334639307) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 79 * (2 : ZMod 334639307) ^ 79) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 309602723 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 334639307) ^ 319 = 167767477 := by
        calc
          (2 : ZMod 334639307) ^ 319 = (2 : ZMod 334639307) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 159 * (2 : ZMod 334639307) ^ 159) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 167767477 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 334639307) ^ 638 = 180602086 := by
        calc
          (2 : ZMod 334639307) ^ 638 = (2 : ZMod 334639307) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 319 * (2 : ZMod 334639307) ^ 319 := by rw [pow_add]
          _ = 180602086 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 334639307) ^ 1276 = 250208562 := by
        calc
          (2 : ZMod 334639307) ^ 1276 = (2 : ZMod 334639307) ^ (638 + 638) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 638 * (2 : ZMod 334639307) ^ 638 := by rw [pow_add]
          _ = 250208562 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 334639307) ^ 2553 = 200227469 := by
        calc
          (2 : ZMod 334639307) ^ 2553 = (2 : ZMod 334639307) ^ (1276 + 1276 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 1276 * (2 : ZMod 334639307) ^ 1276) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 200227469 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 334639307) ^ 5106 = 151095009 := by
        calc
          (2 : ZMod 334639307) ^ 5106 = (2 : ZMod 334639307) ^ (2553 + 2553) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 2553 * (2 : ZMod 334639307) ^ 2553 := by rw [pow_add]
          _ = 151095009 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 334639307) ^ 10212 = 181549262 := by
        calc
          (2 : ZMod 334639307) ^ 10212 = (2 : ZMod 334639307) ^ (5106 + 5106) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 5106 * (2 : ZMod 334639307) ^ 5106 := by rw [pow_add]
          _ = 181549262 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 334639307) ^ 20424 = 297679381 := by
        calc
          (2 : ZMod 334639307) ^ 20424 = (2 : ZMod 334639307) ^ (10212 + 10212) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 10212 * (2 : ZMod 334639307) ^ 10212 := by rw [pow_add]
          _ = 297679381 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 334639307) ^ 40849 = 325101649 := by
        calc
          (2 : ZMod 334639307) ^ 40849 = (2 : ZMod 334639307) ^ (20424 + 20424 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 20424 * (2 : ZMod 334639307) ^ 20424) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 325101649 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 334639307) ^ 81699 = 153573931 := by
        calc
          (2 : ZMod 334639307) ^ 81699 = (2 : ZMod 334639307) ^ (40849 + 40849 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 40849 * (2 : ZMod 334639307) ^ 40849) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 153573931 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 334639307) ^ 163398 = 255909879 := by
        calc
          (2 : ZMod 334639307) ^ 163398 = (2 : ZMod 334639307) ^ (81699 + 81699) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 81699 * (2 : ZMod 334639307) ^ 81699 := by rw [pow_add]
          _ = 255909879 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 334639307) ^ 326796 = 67869691 := by
        calc
          (2 : ZMod 334639307) ^ 326796 = (2 : ZMod 334639307) ^ (163398 + 163398) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 163398 * (2 : ZMod 334639307) ^ 163398 := by rw [pow_add]
          _ = 67869691 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 334639307) ^ 653592 = 288988603 := by
        calc
          (2 : ZMod 334639307) ^ 653592 = (2 : ZMod 334639307) ^ (326796 + 326796) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 326796 * (2 : ZMod 334639307) ^ 326796 := by rw [pow_add]
          _ = 288988603 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 334639307) ^ 1307184 = 78355389 := by
        calc
          (2 : ZMod 334639307) ^ 1307184 = (2 : ZMod 334639307) ^ (653592 + 653592) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 653592 * (2 : ZMod 334639307) ^ 653592 := by rw [pow_add]
          _ = 78355389 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 334639307) ^ 2614369 = 44414469 := by
        calc
          (2 : ZMod 334639307) ^ 2614369 = (2 : ZMod 334639307) ^ (1307184 + 1307184 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 1307184 * (2 : ZMod 334639307) ^ 1307184) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 44414469 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 334639307) ^ 5228739 = 102791469 := by
        calc
          (2 : ZMod 334639307) ^ 5228739 = (2 : ZMod 334639307) ^ (2614369 + 2614369 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 2614369 * (2 : ZMod 334639307) ^ 2614369) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 102791469 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 334639307) ^ 10457478 = 233701804 := by
        calc
          (2 : ZMod 334639307) ^ 10457478 = (2 : ZMod 334639307) ^ (5228739 + 5228739) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 5228739 * (2 : ZMod 334639307) ^ 5228739 := by rw [pow_add]
          _ = 233701804 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 334639307) ^ 20914956 = 28291831 := by
        calc
          (2 : ZMod 334639307) ^ 20914956 = (2 : ZMod 334639307) ^ (10457478 + 10457478) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 10457478 * (2 : ZMod 334639307) ^ 10457478 := by rw [pow_add]
          _ = 28291831 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 334639307) ^ 41829913 = 189134461 := by
        calc
          (2 : ZMod 334639307) ^ 41829913 = (2 : ZMod 334639307) ^ (20914956 + 20914956 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 20914956 * (2 : ZMod 334639307) ^ 20914956) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 189134461 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 334639307) ^ 83659826 = 36387481 := by
        calc
          (2 : ZMod 334639307) ^ 83659826 = (2 : ZMod 334639307) ^ (41829913 + 41829913) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 41829913 * (2 : ZMod 334639307) ^ 41829913 := by rw [pow_add]
          _ = 36387481 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 334639307) ^ 167319653 = 334639306 := by
        calc
          (2 : ZMod 334639307) ^ 167319653 = (2 : ZMod 334639307) ^ (83659826 + 83659826 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 83659826 * (2 : ZMod 334639307) ^ 83659826) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 334639306 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 334639307) ^ 334639306 = 1 := by
        calc
          (2 : ZMod 334639307) ^ 334639306 = (2 : ZMod 334639307) ^ (167319653 + 167319653) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 167319653 * (2 : ZMod 334639307) ^ 167319653 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5659, 1), (29567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5659, 1), (29567, 1)] : List FactorBlock).map factorBlockValue).prod = 334639307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 334639307) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 334639307) ^ 2 = 4 := by
        calc
          (2 : ZMod 334639307) ^ 2 = (2 : ZMod 334639307) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 1 * (2 : ZMod 334639307) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 334639307) ^ 4 = 16 := by
        calc
          (2 : ZMod 334639307) ^ 4 = (2 : ZMod 334639307) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 2 * (2 : ZMod 334639307) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 334639307) ^ 9 = 512 := by
        calc
          (2 : ZMod 334639307) ^ 9 = (2 : ZMod 334639307) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 4 * (2 : ZMod 334639307) ^ 4) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 334639307) ^ 19 = 524288 := by
        calc
          (2 : ZMod 334639307) ^ 19 = (2 : ZMod 334639307) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 9 * (2 : ZMod 334639307) ^ 9) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 334639307) ^ 39 = 278071794 := by
        calc
          (2 : ZMod 334639307) ^ 39 = (2 : ZMod 334639307) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 19 * (2 : ZMod 334639307) ^ 19) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 278071794 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 334639307) ^ 79 = 126480827 := by
        calc
          (2 : ZMod 334639307) ^ 79 = (2 : ZMod 334639307) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 39 * (2 : ZMod 334639307) ^ 39) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 126480827 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 334639307) ^ 159 = 309602723 := by
        calc
          (2 : ZMod 334639307) ^ 159 = (2 : ZMod 334639307) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 79 * (2 : ZMod 334639307) ^ 79) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 309602723 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 334639307) ^ 319 = 167767477 := by
        calc
          (2 : ZMod 334639307) ^ 319 = (2 : ZMod 334639307) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 159 * (2 : ZMod 334639307) ^ 159) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 167767477 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 334639307) ^ 638 = 180602086 := by
        calc
          (2 : ZMod 334639307) ^ 638 = (2 : ZMod 334639307) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 319 * (2 : ZMod 334639307) ^ 319 := by rw [pow_add]
          _ = 180602086 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 334639307) ^ 1276 = 250208562 := by
        calc
          (2 : ZMod 334639307) ^ 1276 = (2 : ZMod 334639307) ^ (638 + 638) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 638 * (2 : ZMod 334639307) ^ 638 := by rw [pow_add]
          _ = 250208562 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 334639307) ^ 2553 = 200227469 := by
        calc
          (2 : ZMod 334639307) ^ 2553 = (2 : ZMod 334639307) ^ (1276 + 1276 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 1276 * (2 : ZMod 334639307) ^ 1276) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 200227469 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 334639307) ^ 5106 = 151095009 := by
        calc
          (2 : ZMod 334639307) ^ 5106 = (2 : ZMod 334639307) ^ (2553 + 2553) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 2553 * (2 : ZMod 334639307) ^ 2553 := by rw [pow_add]
          _ = 151095009 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 334639307) ^ 10212 = 181549262 := by
        calc
          (2 : ZMod 334639307) ^ 10212 = (2 : ZMod 334639307) ^ (5106 + 5106) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 5106 * (2 : ZMod 334639307) ^ 5106 := by rw [pow_add]
          _ = 181549262 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 334639307) ^ 20424 = 297679381 := by
        calc
          (2 : ZMod 334639307) ^ 20424 = (2 : ZMod 334639307) ^ (10212 + 10212) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 10212 * (2 : ZMod 334639307) ^ 10212 := by rw [pow_add]
          _ = 297679381 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 334639307) ^ 40849 = 325101649 := by
        calc
          (2 : ZMod 334639307) ^ 40849 = (2 : ZMod 334639307) ^ (20424 + 20424 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 20424 * (2 : ZMod 334639307) ^ 20424) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 325101649 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 334639307) ^ 81699 = 153573931 := by
        calc
          (2 : ZMod 334639307) ^ 81699 = (2 : ZMod 334639307) ^ (40849 + 40849 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 40849 * (2 : ZMod 334639307) ^ 40849) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 153573931 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 334639307) ^ 163398 = 255909879 := by
        calc
          (2 : ZMod 334639307) ^ 163398 = (2 : ZMod 334639307) ^ (81699 + 81699) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 81699 * (2 : ZMod 334639307) ^ 81699 := by rw [pow_add]
          _ = 255909879 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 334639307) ^ 326796 = 67869691 := by
        calc
          (2 : ZMod 334639307) ^ 326796 = (2 : ZMod 334639307) ^ (163398 + 163398) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 163398 * (2 : ZMod 334639307) ^ 163398 := by rw [pow_add]
          _ = 67869691 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 334639307) ^ 653592 = 288988603 := by
        calc
          (2 : ZMod 334639307) ^ 653592 = (2 : ZMod 334639307) ^ (326796 + 326796) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 326796 * (2 : ZMod 334639307) ^ 326796 := by rw [pow_add]
          _ = 288988603 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 334639307) ^ 1307184 = 78355389 := by
        calc
          (2 : ZMod 334639307) ^ 1307184 = (2 : ZMod 334639307) ^ (653592 + 653592) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 653592 * (2 : ZMod 334639307) ^ 653592 := by rw [pow_add]
          _ = 78355389 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 334639307) ^ 2614369 = 44414469 := by
        calc
          (2 : ZMod 334639307) ^ 2614369 = (2 : ZMod 334639307) ^ (1307184 + 1307184 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 1307184 * (2 : ZMod 334639307) ^ 1307184) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 44414469 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 334639307) ^ 5228739 = 102791469 := by
        calc
          (2 : ZMod 334639307) ^ 5228739 = (2 : ZMod 334639307) ^ (2614369 + 2614369 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 2614369 * (2 : ZMod 334639307) ^ 2614369) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 102791469 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 334639307) ^ 10457478 = 233701804 := by
        calc
          (2 : ZMod 334639307) ^ 10457478 = (2 : ZMod 334639307) ^ (5228739 + 5228739) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 5228739 * (2 : ZMod 334639307) ^ 5228739 := by rw [pow_add]
          _ = 233701804 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 334639307) ^ 20914956 = 28291831 := by
        calc
          (2 : ZMod 334639307) ^ 20914956 = (2 : ZMod 334639307) ^ (10457478 + 10457478) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 10457478 * (2 : ZMod 334639307) ^ 10457478 := by rw [pow_add]
          _ = 28291831 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 334639307) ^ 41829913 = 189134461 := by
        calc
          (2 : ZMod 334639307) ^ 41829913 = (2 : ZMod 334639307) ^ (20914956 + 20914956 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 20914956 * (2 : ZMod 334639307) ^ 20914956) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 189134461 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 334639307) ^ 83659826 = 36387481 := by
        calc
          (2 : ZMod 334639307) ^ 83659826 = (2 : ZMod 334639307) ^ (41829913 + 41829913) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 41829913 * (2 : ZMod 334639307) ^ 41829913 := by rw [pow_add]
          _ = 36387481 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 334639307) ^ 167319653 = 334639306 := by
        calc
          (2 : ZMod 334639307) ^ 167319653 = (2 : ZMod 334639307) ^ (83659826 + 83659826 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 83659826 * (2 : ZMod 334639307) ^ 83659826) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 334639306 := by rw [factor_0_26]; decide
      change (2 : ZMod 334639307) ^ 167319653 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (2 : ZMod 334639307) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 334639307) ^ 3 = 8 := by
        calc
          (2 : ZMod 334639307) ^ 3 = (2 : ZMod 334639307) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 1 * (2 : ZMod 334639307) ^ 1) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 334639307) ^ 7 = 128 := by
        calc
          (2 : ZMod 334639307) ^ 7 = (2 : ZMod 334639307) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 3 * (2 : ZMod 334639307) ^ 3) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 334639307) ^ 14 = 16384 := by
        calc
          (2 : ZMod 334639307) ^ 14 = (2 : ZMod 334639307) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 7 * (2 : ZMod 334639307) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 334639307) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 334639307) ^ 28 = (2 : ZMod 334639307) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 14 * (2 : ZMod 334639307) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 334639307) ^ 57 = 37483219 := by
        calc
          (2 : ZMod 334639307) ^ 57 = (2 : ZMod 334639307) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 28 * (2 : ZMod 334639307) ^ 28) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 37483219 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 334639307) ^ 115 = 85720265 := by
        calc
          (2 : ZMod 334639307) ^ 115 = (2 : ZMod 334639307) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 57 * (2 : ZMod 334639307) ^ 57) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 85720265 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 334639307) ^ 230 = 108788591 := by
        calc
          (2 : ZMod 334639307) ^ 230 = (2 : ZMod 334639307) ^ (115 + 115) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 115 * (2 : ZMod 334639307) ^ 115 := by rw [pow_add]
          _ = 108788591 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 334639307) ^ 461 = 124436222 := by
        calc
          (2 : ZMod 334639307) ^ 461 = (2 : ZMod 334639307) ^ (230 + 230 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 230 * (2 : ZMod 334639307) ^ 230) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 124436222 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 334639307) ^ 923 = 106983641 := by
        calc
          (2 : ZMod 334639307) ^ 923 = (2 : ZMod 334639307) ^ (461 + 461 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 461 * (2 : ZMod 334639307) ^ 461) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 106983641 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 334639307) ^ 1847 = 99652525 := by
        calc
          (2 : ZMod 334639307) ^ 1847 = (2 : ZMod 334639307) ^ (923 + 923 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 923 * (2 : ZMod 334639307) ^ 923) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 99652525 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 334639307) ^ 3695 = 12707403 := by
        calc
          (2 : ZMod 334639307) ^ 3695 = (2 : ZMod 334639307) ^ (1847 + 1847 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 1847 * (2 : ZMod 334639307) ^ 1847) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 12707403 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 334639307) ^ 7391 = 137134109 := by
        calc
          (2 : ZMod 334639307) ^ 7391 = (2 : ZMod 334639307) ^ (3695 + 3695 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 3695 * (2 : ZMod 334639307) ^ 3695) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 137134109 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 334639307) ^ 14783 = 129809845 := by
        calc
          (2 : ZMod 334639307) ^ 14783 = (2 : ZMod 334639307) ^ (7391 + 7391 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 7391 * (2 : ZMod 334639307) ^ 7391) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 129809845 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 334639307) ^ 29567 = 75988515 := by
        calc
          (2 : ZMod 334639307) ^ 29567 = (2 : ZMod 334639307) ^ (14783 + 14783 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 14783 * (2 : ZMod 334639307) ^ 14783) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 75988515 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 334639307) ^ 59134 = 296609719 := by
        calc
          (2 : ZMod 334639307) ^ 59134 = (2 : ZMod 334639307) ^ (29567 + 29567) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 29567 * (2 : ZMod 334639307) ^ 29567 := by rw [pow_add]
          _ = 296609719 := by rw [factor_1_14]; decide
      change (2 : ZMod 334639307) ^ 59134 ≠ 1
      rw [factor_1_15]
      decide
    ·
      have factor_2_0 : (2 : ZMod 334639307) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 334639307) ^ 2 = 4 := by
        calc
          (2 : ZMod 334639307) ^ 2 = (2 : ZMod 334639307) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 1 * (2 : ZMod 334639307) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 334639307) ^ 5 = 32 := by
        calc
          (2 : ZMod 334639307) ^ 5 = (2 : ZMod 334639307) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 2 * (2 : ZMod 334639307) ^ 2) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 334639307) ^ 11 = 2048 := by
        calc
          (2 : ZMod 334639307) ^ 11 = (2 : ZMod 334639307) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 5 * (2 : ZMod 334639307) ^ 5) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 334639307) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 334639307) ^ 22 = (2 : ZMod 334639307) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 11 * (2 : ZMod 334639307) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 334639307) ^ 44 = 197675426 := by
        calc
          (2 : ZMod 334639307) ^ 44 = (2 : ZMod 334639307) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 22 * (2 : ZMod 334639307) ^ 22 := by rw [pow_add]
          _ = 197675426 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 334639307) ^ 88 = 172797173 := by
        calc
          (2 : ZMod 334639307) ^ 88 = (2 : ZMod 334639307) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 44 * (2 : ZMod 334639307) ^ 44 := by rw [pow_add]
          _ = 172797173 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 334639307) ^ 176 = 212545701 := by
        calc
          (2 : ZMod 334639307) ^ 176 = (2 : ZMod 334639307) ^ (88 + 88) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 88 * (2 : ZMod 334639307) ^ 88 := by rw [pow_add]
          _ = 212545701 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 334639307) ^ 353 = 65907420 := by
        calc
          (2 : ZMod 334639307) ^ 353 = (2 : ZMod 334639307) ^ (176 + 176 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 176 * (2 : ZMod 334639307) ^ 176) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 65907420 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 334639307) ^ 707 = 288135502 := by
        calc
          (2 : ZMod 334639307) ^ 707 = (2 : ZMod 334639307) ^ (353 + 353 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 353 * (2 : ZMod 334639307) ^ 353) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 288135502 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 334639307) ^ 1414 = 35104981 := by
        calc
          (2 : ZMod 334639307) ^ 1414 = (2 : ZMod 334639307) ^ (707 + 707) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 707 * (2 : ZMod 334639307) ^ 707 := by rw [pow_add]
          _ = 35104981 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 334639307) ^ 2829 = 159534315 := by
        calc
          (2 : ZMod 334639307) ^ 2829 = (2 : ZMod 334639307) ^ (1414 + 1414 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 1414 * (2 : ZMod 334639307) ^ 1414) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 159534315 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 334639307) ^ 5659 = 69478068 := by
        calc
          (2 : ZMod 334639307) ^ 5659 = (2 : ZMod 334639307) ^ (2829 + 2829 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = ((2 : ZMod 334639307) ^ 2829 * (2 : ZMod 334639307) ^ 2829) * (2 : ZMod 334639307) := by rw [pow_succ, pow_add]
          _ = 69478068 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 334639307) ^ 11318 = 146639301 := by
        calc
          (2 : ZMod 334639307) ^ 11318 = (2 : ZMod 334639307) ^ (5659 + 5659) :=
            congrArg (fun n : ℕ => (2 : ZMod 334639307) ^ n) (by norm_num)
          _ = (2 : ZMod 334639307) ^ 5659 * (2 : ZMod 334639307) ^ 5659 := by rw [pow_add]
          _ = 146639301 := by rw [factor_2_12]; decide
      change (2 : ZMod 334639307) ^ 11318 ≠ 1
      rw [factor_2_13]
      decide

#print axioms prime_lucas_334639307

end TotientTailPeriodKiller
end Erdos249257
