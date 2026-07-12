import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=23 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_10708457761 : Nat.Prime 10708457761 := by
  apply lucas_primality 10708457761 (47 : ZMod 10708457761)
  ·
      have fermat_0 : (47 : ZMod 10708457761) ^ 1 = 47 := by norm_num
      have fermat_1 : (47 : ZMod 10708457761) ^ 2 = 2209 := by
        calc
          (47 : ZMod 10708457761) ^ 2 = (47 : ZMod 10708457761) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 1 * (47 : ZMod 10708457761) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [fermat_0]; decide
      have fermat_2 : (47 : ZMod 10708457761) ^ 4 = 4879681 := by
        calc
          (47 : ZMod 10708457761) ^ 4 = (47 : ZMod 10708457761) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 2 * (47 : ZMod 10708457761) ^ 2 := by rw [pow_add]
          _ = 4879681 := by rw [fermat_1]; decide
      have fermat_3 : (47 : ZMod 10708457761) ^ 9 = 260958418 := by
        calc
          (47 : ZMod 10708457761) ^ 9 = (47 : ZMod 10708457761) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 4 * (47 : ZMod 10708457761) ^ 4) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 260958418 := by rw [fermat_2]; decide
      have fermat_4 : (47 : ZMod 10708457761) ^ 19 = 1982136377 := by
        calc
          (47 : ZMod 10708457761) ^ 19 = (47 : ZMod 10708457761) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 9 * (47 : ZMod 10708457761) ^ 9) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 1982136377 := by rw [fermat_3]; decide
      have fermat_5 : (47 : ZMod 10708457761) ^ 39 = 587203429 := by
        calc
          (47 : ZMod 10708457761) ^ 39 = (47 : ZMod 10708457761) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 19 * (47 : ZMod 10708457761) ^ 19) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 587203429 := by rw [fermat_4]; decide
      have fermat_6 : (47 : ZMod 10708457761) ^ 79 = 3325191879 := by
        calc
          (47 : ZMod 10708457761) ^ 79 = (47 : ZMod 10708457761) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 39 * (47 : ZMod 10708457761) ^ 39) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 3325191879 := by rw [fermat_5]; decide
      have fermat_7 : (47 : ZMod 10708457761) ^ 159 = 6412594494 := by
        calc
          (47 : ZMod 10708457761) ^ 159 = (47 : ZMod 10708457761) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 79 * (47 : ZMod 10708457761) ^ 79) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 6412594494 := by rw [fermat_6]; decide
      have fermat_8 : (47 : ZMod 10708457761) ^ 319 = 2338328332 := by
        calc
          (47 : ZMod 10708457761) ^ 319 = (47 : ZMod 10708457761) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 159 * (47 : ZMod 10708457761) ^ 159) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 2338328332 := by rw [fermat_7]; decide
      have fermat_9 : (47 : ZMod 10708457761) ^ 638 = 2700944009 := by
        calc
          (47 : ZMod 10708457761) ^ 638 = (47 : ZMod 10708457761) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 319 * (47 : ZMod 10708457761) ^ 319 := by rw [pow_add]
          _ = 2700944009 := by rw [fermat_8]; decide
      have fermat_10 : (47 : ZMod 10708457761) ^ 1276 = 4933610939 := by
        calc
          (47 : ZMod 10708457761) ^ 1276 = (47 : ZMod 10708457761) ^ (638 + 638) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 638 * (47 : ZMod 10708457761) ^ 638 := by rw [pow_add]
          _ = 4933610939 := by rw [fermat_9]; decide
      have fermat_11 : (47 : ZMod 10708457761) ^ 2553 = 2835318324 := by
        calc
          (47 : ZMod 10708457761) ^ 2553 = (47 : ZMod 10708457761) ^ (1276 + 1276 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 1276 * (47 : ZMod 10708457761) ^ 1276) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 2835318324 := by rw [fermat_10]; decide
      have fermat_12 : (47 : ZMod 10708457761) ^ 5106 = 7469372283 := by
        calc
          (47 : ZMod 10708457761) ^ 5106 = (47 : ZMod 10708457761) ^ (2553 + 2553) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 2553 * (47 : ZMod 10708457761) ^ 2553 := by rw [pow_add]
          _ = 7469372283 := by rw [fermat_11]; decide
      have fermat_13 : (47 : ZMod 10708457761) ^ 10212 = 9007659779 := by
        calc
          (47 : ZMod 10708457761) ^ 10212 = (47 : ZMod 10708457761) ^ (5106 + 5106) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 5106 * (47 : ZMod 10708457761) ^ 5106 := by rw [pow_add]
          _ = 9007659779 := by rw [fermat_12]; decide
      have fermat_14 : (47 : ZMod 10708457761) ^ 20424 = 1320544208 := by
        calc
          (47 : ZMod 10708457761) ^ 20424 = (47 : ZMod 10708457761) ^ (10212 + 10212) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 10212 * (47 : ZMod 10708457761) ^ 10212 := by rw [pow_add]
          _ = 1320544208 := by rw [fermat_13]; decide
      have fermat_15 : (47 : ZMod 10708457761) ^ 40849 = 181511162 := by
        calc
          (47 : ZMod 10708457761) ^ 40849 = (47 : ZMod 10708457761) ^ (20424 + 20424 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 20424 * (47 : ZMod 10708457761) ^ 20424) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 181511162 := by rw [fermat_14]; decide
      have fermat_16 : (47 : ZMod 10708457761) ^ 81699 = 2278082368 := by
        calc
          (47 : ZMod 10708457761) ^ 81699 = (47 : ZMod 10708457761) ^ (40849 + 40849 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 40849 * (47 : ZMod 10708457761) ^ 40849) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 2278082368 := by rw [fermat_15]; decide
      have fermat_17 : (47 : ZMod 10708457761) ^ 163398 = 8370510014 := by
        calc
          (47 : ZMod 10708457761) ^ 163398 = (47 : ZMod 10708457761) ^ (81699 + 81699) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 81699 * (47 : ZMod 10708457761) ^ 81699 := by rw [pow_add]
          _ = 8370510014 := by rw [fermat_16]; decide
      have fermat_18 : (47 : ZMod 10708457761) ^ 326796 = 6432380472 := by
        calc
          (47 : ZMod 10708457761) ^ 326796 = (47 : ZMod 10708457761) ^ (163398 + 163398) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 163398 * (47 : ZMod 10708457761) ^ 163398 := by rw [pow_add]
          _ = 6432380472 := by rw [fermat_17]; decide
      have fermat_19 : (47 : ZMod 10708457761) ^ 653592 = 8696899468 := by
        calc
          (47 : ZMod 10708457761) ^ 653592 = (47 : ZMod 10708457761) ^ (326796 + 326796) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 326796 * (47 : ZMod 10708457761) ^ 326796 := by rw [pow_add]
          _ = 8696899468 := by rw [fermat_18]; decide
      have fermat_20 : (47 : ZMod 10708457761) ^ 1307184 = 7639921814 := by
        calc
          (47 : ZMod 10708457761) ^ 1307184 = (47 : ZMod 10708457761) ^ (653592 + 653592) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 653592 * (47 : ZMod 10708457761) ^ 653592 := by rw [pow_add]
          _ = 7639921814 := by rw [fermat_19]; decide
      have fermat_21 : (47 : ZMod 10708457761) ^ 2614369 = 3980434756 := by
        calc
          (47 : ZMod 10708457761) ^ 2614369 = (47 : ZMod 10708457761) ^ (1307184 + 1307184 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 1307184 * (47 : ZMod 10708457761) ^ 1307184) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 3980434756 := by rw [fermat_20]; decide
      have fermat_22 : (47 : ZMod 10708457761) ^ 5228739 = 5035192115 := by
        calc
          (47 : ZMod 10708457761) ^ 5228739 = (47 : ZMod 10708457761) ^ (2614369 + 2614369 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 2614369 * (47 : ZMod 10708457761) ^ 2614369) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 5035192115 := by rw [fermat_21]; decide
      have fermat_23 : (47 : ZMod 10708457761) ^ 10457478 = 7205478978 := by
        calc
          (47 : ZMod 10708457761) ^ 10457478 = (47 : ZMod 10708457761) ^ (5228739 + 5228739) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 5228739 * (47 : ZMod 10708457761) ^ 5228739 := by rw [pow_add]
          _ = 7205478978 := by rw [fermat_22]; decide
      have fermat_24 : (47 : ZMod 10708457761) ^ 20914956 = 1828032684 := by
        calc
          (47 : ZMod 10708457761) ^ 20914956 = (47 : ZMod 10708457761) ^ (10457478 + 10457478) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 10457478 * (47 : ZMod 10708457761) ^ 10457478 := by rw [pow_add]
          _ = 1828032684 := by rw [fermat_23]; decide
      have fermat_25 : (47 : ZMod 10708457761) ^ 41829913 = 8917535630 := by
        calc
          (47 : ZMod 10708457761) ^ 41829913 = (47 : ZMod 10708457761) ^ (20914956 + 20914956 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 20914956 * (47 : ZMod 10708457761) ^ 20914956) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 8917535630 := by rw [fermat_24]; decide
      have fermat_26 : (47 : ZMod 10708457761) ^ 83659826 = 2633326472 := by
        calc
          (47 : ZMod 10708457761) ^ 83659826 = (47 : ZMod 10708457761) ^ (41829913 + 41829913) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 41829913 * (47 : ZMod 10708457761) ^ 41829913 := by rw [pow_add]
          _ = 2633326472 := by rw [fermat_25]; decide
      have fermat_27 : (47 : ZMod 10708457761) ^ 167319652 = 4006704065 := by
        calc
          (47 : ZMod 10708457761) ^ 167319652 = (47 : ZMod 10708457761) ^ (83659826 + 83659826) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 83659826 * (47 : ZMod 10708457761) ^ 83659826 := by rw [pow_add]
          _ = 4006704065 := by rw [fermat_26]; decide
      have fermat_28 : (47 : ZMod 10708457761) ^ 334639305 = 711526740 := by
        calc
          (47 : ZMod 10708457761) ^ 334639305 = (47 : ZMod 10708457761) ^ (167319652 + 167319652 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 167319652 * (47 : ZMod 10708457761) ^ 167319652) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 711526740 := by rw [fermat_27]; decide
      have fermat_29 : (47 : ZMod 10708457761) ^ 669278610 = 1300538629 := by
        calc
          (47 : ZMod 10708457761) ^ 669278610 = (47 : ZMod 10708457761) ^ (334639305 + 334639305) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 334639305 * (47 : ZMod 10708457761) ^ 334639305 := by rw [pow_add]
          _ = 1300538629 := by rw [fermat_28]; decide
      have fermat_30 : (47 : ZMod 10708457761) ^ 1338557220 = 4215031578 := by
        calc
          (47 : ZMod 10708457761) ^ 1338557220 = (47 : ZMod 10708457761) ^ (669278610 + 669278610) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 669278610 * (47 : ZMod 10708457761) ^ 669278610 := by rw [pow_add]
          _ = 4215031578 := by rw [fermat_29]; decide
      have fermat_31 : (47 : ZMod 10708457761) ^ 2677114440 = 9228822740 := by
        calc
          (47 : ZMod 10708457761) ^ 2677114440 = (47 : ZMod 10708457761) ^ (1338557220 + 1338557220) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 1338557220 * (47 : ZMod 10708457761) ^ 1338557220 := by rw [pow_add]
          _ = 9228822740 := by rw [fermat_30]; decide
      have fermat_32 : (47 : ZMod 10708457761) ^ 5354228880 = 10708457760 := by
        calc
          (47 : ZMod 10708457761) ^ 5354228880 = (47 : ZMod 10708457761) ^ (2677114440 + 2677114440) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 2677114440 * (47 : ZMod 10708457761) ^ 2677114440 := by rw [pow_add]
          _ = 10708457760 := by rw [fermat_31]; decide
      have fermat_33 : (47 : ZMod 10708457761) ^ 10708457760 = 1 := by
        calc
          (47 : ZMod 10708457761) ^ 10708457760 = (47 : ZMod 10708457761) ^ (5354228880 + 5354228880) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 5354228880 * (47 : ZMod 10708457761) ^ 5354228880 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 10708457761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (47 : ZMod 10708457761) ^ 1 = 47 := by norm_num
      have factor_0_1 : (47 : ZMod 10708457761) ^ 2 = 2209 := by
        calc
          (47 : ZMod 10708457761) ^ 2 = (47 : ZMod 10708457761) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 1 * (47 : ZMod 10708457761) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_0_0]; decide
      have factor_0_2 : (47 : ZMod 10708457761) ^ 4 = 4879681 := by
        calc
          (47 : ZMod 10708457761) ^ 4 = (47 : ZMod 10708457761) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 2 * (47 : ZMod 10708457761) ^ 2 := by rw [pow_add]
          _ = 4879681 := by rw [factor_0_1]; decide
      have factor_0_3 : (47 : ZMod 10708457761) ^ 9 = 260958418 := by
        calc
          (47 : ZMod 10708457761) ^ 9 = (47 : ZMod 10708457761) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 4 * (47 : ZMod 10708457761) ^ 4) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 260958418 := by rw [factor_0_2]; decide
      have factor_0_4 : (47 : ZMod 10708457761) ^ 19 = 1982136377 := by
        calc
          (47 : ZMod 10708457761) ^ 19 = (47 : ZMod 10708457761) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 9 * (47 : ZMod 10708457761) ^ 9) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 1982136377 := by rw [factor_0_3]; decide
      have factor_0_5 : (47 : ZMod 10708457761) ^ 39 = 587203429 := by
        calc
          (47 : ZMod 10708457761) ^ 39 = (47 : ZMod 10708457761) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 19 * (47 : ZMod 10708457761) ^ 19) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 587203429 := by rw [factor_0_4]; decide
      have factor_0_6 : (47 : ZMod 10708457761) ^ 79 = 3325191879 := by
        calc
          (47 : ZMod 10708457761) ^ 79 = (47 : ZMod 10708457761) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 39 * (47 : ZMod 10708457761) ^ 39) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 3325191879 := by rw [factor_0_5]; decide
      have factor_0_7 : (47 : ZMod 10708457761) ^ 159 = 6412594494 := by
        calc
          (47 : ZMod 10708457761) ^ 159 = (47 : ZMod 10708457761) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 79 * (47 : ZMod 10708457761) ^ 79) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 6412594494 := by rw [factor_0_6]; decide
      have factor_0_8 : (47 : ZMod 10708457761) ^ 319 = 2338328332 := by
        calc
          (47 : ZMod 10708457761) ^ 319 = (47 : ZMod 10708457761) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 159 * (47 : ZMod 10708457761) ^ 159) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 2338328332 := by rw [factor_0_7]; decide
      have factor_0_9 : (47 : ZMod 10708457761) ^ 638 = 2700944009 := by
        calc
          (47 : ZMod 10708457761) ^ 638 = (47 : ZMod 10708457761) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 319 * (47 : ZMod 10708457761) ^ 319 := by rw [pow_add]
          _ = 2700944009 := by rw [factor_0_8]; decide
      have factor_0_10 : (47 : ZMod 10708457761) ^ 1276 = 4933610939 := by
        calc
          (47 : ZMod 10708457761) ^ 1276 = (47 : ZMod 10708457761) ^ (638 + 638) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 638 * (47 : ZMod 10708457761) ^ 638 := by rw [pow_add]
          _ = 4933610939 := by rw [factor_0_9]; decide
      have factor_0_11 : (47 : ZMod 10708457761) ^ 2553 = 2835318324 := by
        calc
          (47 : ZMod 10708457761) ^ 2553 = (47 : ZMod 10708457761) ^ (1276 + 1276 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 1276 * (47 : ZMod 10708457761) ^ 1276) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 2835318324 := by rw [factor_0_10]; decide
      have factor_0_12 : (47 : ZMod 10708457761) ^ 5106 = 7469372283 := by
        calc
          (47 : ZMod 10708457761) ^ 5106 = (47 : ZMod 10708457761) ^ (2553 + 2553) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 2553 * (47 : ZMod 10708457761) ^ 2553 := by rw [pow_add]
          _ = 7469372283 := by rw [factor_0_11]; decide
      have factor_0_13 : (47 : ZMod 10708457761) ^ 10212 = 9007659779 := by
        calc
          (47 : ZMod 10708457761) ^ 10212 = (47 : ZMod 10708457761) ^ (5106 + 5106) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 5106 * (47 : ZMod 10708457761) ^ 5106 := by rw [pow_add]
          _ = 9007659779 := by rw [factor_0_12]; decide
      have factor_0_14 : (47 : ZMod 10708457761) ^ 20424 = 1320544208 := by
        calc
          (47 : ZMod 10708457761) ^ 20424 = (47 : ZMod 10708457761) ^ (10212 + 10212) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 10212 * (47 : ZMod 10708457761) ^ 10212 := by rw [pow_add]
          _ = 1320544208 := by rw [factor_0_13]; decide
      have factor_0_15 : (47 : ZMod 10708457761) ^ 40849 = 181511162 := by
        calc
          (47 : ZMod 10708457761) ^ 40849 = (47 : ZMod 10708457761) ^ (20424 + 20424 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 20424 * (47 : ZMod 10708457761) ^ 20424) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 181511162 := by rw [factor_0_14]; decide
      have factor_0_16 : (47 : ZMod 10708457761) ^ 81699 = 2278082368 := by
        calc
          (47 : ZMod 10708457761) ^ 81699 = (47 : ZMod 10708457761) ^ (40849 + 40849 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 40849 * (47 : ZMod 10708457761) ^ 40849) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 2278082368 := by rw [factor_0_15]; decide
      have factor_0_17 : (47 : ZMod 10708457761) ^ 163398 = 8370510014 := by
        calc
          (47 : ZMod 10708457761) ^ 163398 = (47 : ZMod 10708457761) ^ (81699 + 81699) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 81699 * (47 : ZMod 10708457761) ^ 81699 := by rw [pow_add]
          _ = 8370510014 := by rw [factor_0_16]; decide
      have factor_0_18 : (47 : ZMod 10708457761) ^ 326796 = 6432380472 := by
        calc
          (47 : ZMod 10708457761) ^ 326796 = (47 : ZMod 10708457761) ^ (163398 + 163398) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 163398 * (47 : ZMod 10708457761) ^ 163398 := by rw [pow_add]
          _ = 6432380472 := by rw [factor_0_17]; decide
      have factor_0_19 : (47 : ZMod 10708457761) ^ 653592 = 8696899468 := by
        calc
          (47 : ZMod 10708457761) ^ 653592 = (47 : ZMod 10708457761) ^ (326796 + 326796) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 326796 * (47 : ZMod 10708457761) ^ 326796 := by rw [pow_add]
          _ = 8696899468 := by rw [factor_0_18]; decide
      have factor_0_20 : (47 : ZMod 10708457761) ^ 1307184 = 7639921814 := by
        calc
          (47 : ZMod 10708457761) ^ 1307184 = (47 : ZMod 10708457761) ^ (653592 + 653592) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 653592 * (47 : ZMod 10708457761) ^ 653592 := by rw [pow_add]
          _ = 7639921814 := by rw [factor_0_19]; decide
      have factor_0_21 : (47 : ZMod 10708457761) ^ 2614369 = 3980434756 := by
        calc
          (47 : ZMod 10708457761) ^ 2614369 = (47 : ZMod 10708457761) ^ (1307184 + 1307184 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 1307184 * (47 : ZMod 10708457761) ^ 1307184) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 3980434756 := by rw [factor_0_20]; decide
      have factor_0_22 : (47 : ZMod 10708457761) ^ 5228739 = 5035192115 := by
        calc
          (47 : ZMod 10708457761) ^ 5228739 = (47 : ZMod 10708457761) ^ (2614369 + 2614369 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 2614369 * (47 : ZMod 10708457761) ^ 2614369) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 5035192115 := by rw [factor_0_21]; decide
      have factor_0_23 : (47 : ZMod 10708457761) ^ 10457478 = 7205478978 := by
        calc
          (47 : ZMod 10708457761) ^ 10457478 = (47 : ZMod 10708457761) ^ (5228739 + 5228739) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 5228739 * (47 : ZMod 10708457761) ^ 5228739 := by rw [pow_add]
          _ = 7205478978 := by rw [factor_0_22]; decide
      have factor_0_24 : (47 : ZMod 10708457761) ^ 20914956 = 1828032684 := by
        calc
          (47 : ZMod 10708457761) ^ 20914956 = (47 : ZMod 10708457761) ^ (10457478 + 10457478) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 10457478 * (47 : ZMod 10708457761) ^ 10457478 := by rw [pow_add]
          _ = 1828032684 := by rw [factor_0_23]; decide
      have factor_0_25 : (47 : ZMod 10708457761) ^ 41829913 = 8917535630 := by
        calc
          (47 : ZMod 10708457761) ^ 41829913 = (47 : ZMod 10708457761) ^ (20914956 + 20914956 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 20914956 * (47 : ZMod 10708457761) ^ 20914956) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 8917535630 := by rw [factor_0_24]; decide
      have factor_0_26 : (47 : ZMod 10708457761) ^ 83659826 = 2633326472 := by
        calc
          (47 : ZMod 10708457761) ^ 83659826 = (47 : ZMod 10708457761) ^ (41829913 + 41829913) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 41829913 * (47 : ZMod 10708457761) ^ 41829913 := by rw [pow_add]
          _ = 2633326472 := by rw [factor_0_25]; decide
      have factor_0_27 : (47 : ZMod 10708457761) ^ 167319652 = 4006704065 := by
        calc
          (47 : ZMod 10708457761) ^ 167319652 = (47 : ZMod 10708457761) ^ (83659826 + 83659826) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 83659826 * (47 : ZMod 10708457761) ^ 83659826 := by rw [pow_add]
          _ = 4006704065 := by rw [factor_0_26]; decide
      have factor_0_28 : (47 : ZMod 10708457761) ^ 334639305 = 711526740 := by
        calc
          (47 : ZMod 10708457761) ^ 334639305 = (47 : ZMod 10708457761) ^ (167319652 + 167319652 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 167319652 * (47 : ZMod 10708457761) ^ 167319652) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 711526740 := by rw [factor_0_27]; decide
      have factor_0_29 : (47 : ZMod 10708457761) ^ 669278610 = 1300538629 := by
        calc
          (47 : ZMod 10708457761) ^ 669278610 = (47 : ZMod 10708457761) ^ (334639305 + 334639305) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 334639305 * (47 : ZMod 10708457761) ^ 334639305 := by rw [pow_add]
          _ = 1300538629 := by rw [factor_0_28]; decide
      have factor_0_30 : (47 : ZMod 10708457761) ^ 1338557220 = 4215031578 := by
        calc
          (47 : ZMod 10708457761) ^ 1338557220 = (47 : ZMod 10708457761) ^ (669278610 + 669278610) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 669278610 * (47 : ZMod 10708457761) ^ 669278610 := by rw [pow_add]
          _ = 4215031578 := by rw [factor_0_29]; decide
      have factor_0_31 : (47 : ZMod 10708457761) ^ 2677114440 = 9228822740 := by
        calc
          (47 : ZMod 10708457761) ^ 2677114440 = (47 : ZMod 10708457761) ^ (1338557220 + 1338557220) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 1338557220 * (47 : ZMod 10708457761) ^ 1338557220 := by rw [pow_add]
          _ = 9228822740 := by rw [factor_0_30]; decide
      have factor_0_32 : (47 : ZMod 10708457761) ^ 5354228880 = 10708457760 := by
        calc
          (47 : ZMod 10708457761) ^ 5354228880 = (47 : ZMod 10708457761) ^ (2677114440 + 2677114440) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 2677114440 * (47 : ZMod 10708457761) ^ 2677114440 := by rw [pow_add]
          _ = 10708457760 := by rw [factor_0_31]; decide
      change (47 : ZMod 10708457761) ^ 5354228880 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (47 : ZMod 10708457761) ^ 1 = 47 := by norm_num
      have factor_1_1 : (47 : ZMod 10708457761) ^ 3 = 103823 := by
        calc
          (47 : ZMod 10708457761) ^ 3 = (47 : ZMod 10708457761) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 1 * (47 : ZMod 10708457761) ^ 1) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_1_0]; decide
      have factor_1_2 : (47 : ZMod 10708457761) ^ 6 = 70757568 := by
        calc
          (47 : ZMod 10708457761) ^ 6 = (47 : ZMod 10708457761) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 3 * (47 : ZMod 10708457761) ^ 3 := by rw [pow_add]
          _ = 70757568 := by rw [factor_1_1]; decide
      have factor_1_3 : (47 : ZMod 10708457761) ^ 13 = 8287913104 := by
        calc
          (47 : ZMod 10708457761) ^ 13 = (47 : ZMod 10708457761) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 6 * (47 : ZMod 10708457761) ^ 6) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 8287913104 := by rw [factor_1_2]; decide
      have factor_1_4 : (47 : ZMod 10708457761) ^ 26 = 9509995756 := by
        calc
          (47 : ZMod 10708457761) ^ 26 = (47 : ZMod 10708457761) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 13 * (47 : ZMod 10708457761) ^ 13 := by rw [pow_add]
          _ = 9509995756 := by rw [factor_1_3]; decide
      have factor_1_5 : (47 : ZMod 10708457761) ^ 53 = 777896492 := by
        calc
          (47 : ZMod 10708457761) ^ 53 = (47 : ZMod 10708457761) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 26 * (47 : ZMod 10708457761) ^ 26) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 777896492 := by rw [factor_1_4]; decide
      have factor_1_6 : (47 : ZMod 10708457761) ^ 106 = 8372946145 := by
        calc
          (47 : ZMod 10708457761) ^ 106 = (47 : ZMod 10708457761) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 53 * (47 : ZMod 10708457761) ^ 53 := by rw [pow_add]
          _ = 8372946145 := by rw [factor_1_5]; decide
      have factor_1_7 : (47 : ZMod 10708457761) ^ 212 = 4533226792 := by
        calc
          (47 : ZMod 10708457761) ^ 212 = (47 : ZMod 10708457761) ^ (106 + 106) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 106 * (47 : ZMod 10708457761) ^ 106 := by rw [pow_add]
          _ = 4533226792 := by rw [factor_1_6]; decide
      have factor_1_8 : (47 : ZMod 10708457761) ^ 425 = 6552284238 := by
        calc
          (47 : ZMod 10708457761) ^ 425 = (47 : ZMod 10708457761) ^ (212 + 212 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 212 * (47 : ZMod 10708457761) ^ 212) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 6552284238 := by rw [factor_1_7]; decide
      have factor_1_9 : (47 : ZMod 10708457761) ^ 851 = 2801819190 := by
        calc
          (47 : ZMod 10708457761) ^ 851 = (47 : ZMod 10708457761) ^ (425 + 425 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 425 * (47 : ZMod 10708457761) ^ 425) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 2801819190 := by rw [factor_1_8]; decide
      have factor_1_10 : (47 : ZMod 10708457761) ^ 1702 = 1825181353 := by
        calc
          (47 : ZMod 10708457761) ^ 1702 = (47 : ZMod 10708457761) ^ (851 + 851) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 851 * (47 : ZMod 10708457761) ^ 851 := by rw [pow_add]
          _ = 1825181353 := by rw [factor_1_9]; decide
      have factor_1_11 : (47 : ZMod 10708457761) ^ 3404 = 10427662718 := by
        calc
          (47 : ZMod 10708457761) ^ 3404 = (47 : ZMod 10708457761) ^ (1702 + 1702) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 1702 * (47 : ZMod 10708457761) ^ 1702 := by rw [pow_add]
          _ = 10427662718 := by rw [factor_1_10]; decide
      have factor_1_12 : (47 : ZMod 10708457761) ^ 6808 = 6393559138 := by
        calc
          (47 : ZMod 10708457761) ^ 6808 = (47 : ZMod 10708457761) ^ (3404 + 3404) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 3404 * (47 : ZMod 10708457761) ^ 3404 := by rw [pow_add]
          _ = 6393559138 := by rw [factor_1_11]; decide
      have factor_1_13 : (47 : ZMod 10708457761) ^ 13616 = 3891791641 := by
        calc
          (47 : ZMod 10708457761) ^ 13616 = (47 : ZMod 10708457761) ^ (6808 + 6808) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 6808 * (47 : ZMod 10708457761) ^ 6808 := by rw [pow_add]
          _ = 3891791641 := by rw [factor_1_12]; decide
      have factor_1_14 : (47 : ZMod 10708457761) ^ 27233 = 3985385595 := by
        calc
          (47 : ZMod 10708457761) ^ 27233 = (47 : ZMod 10708457761) ^ (13616 + 13616 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 13616 * (47 : ZMod 10708457761) ^ 13616) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 3985385595 := by rw [factor_1_13]; decide
      have factor_1_15 : (47 : ZMod 10708457761) ^ 54466 = 8623389006 := by
        calc
          (47 : ZMod 10708457761) ^ 54466 = (47 : ZMod 10708457761) ^ (27233 + 27233) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 27233 * (47 : ZMod 10708457761) ^ 27233 := by rw [pow_add]
          _ = 8623389006 := by rw [factor_1_14]; decide
      have factor_1_16 : (47 : ZMod 10708457761) ^ 108932 = 2780471991 := by
        calc
          (47 : ZMod 10708457761) ^ 108932 = (47 : ZMod 10708457761) ^ (54466 + 54466) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 54466 * (47 : ZMod 10708457761) ^ 54466 := by rw [pow_add]
          _ = 2780471991 := by rw [factor_1_15]; decide
      have factor_1_17 : (47 : ZMod 10708457761) ^ 217864 = 9102699974 := by
        calc
          (47 : ZMod 10708457761) ^ 217864 = (47 : ZMod 10708457761) ^ (108932 + 108932) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 108932 * (47 : ZMod 10708457761) ^ 108932 := by rw [pow_add]
          _ = 9102699974 := by rw [factor_1_16]; decide
      have factor_1_18 : (47 : ZMod 10708457761) ^ 435728 = 9105764709 := by
        calc
          (47 : ZMod 10708457761) ^ 435728 = (47 : ZMod 10708457761) ^ (217864 + 217864) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 217864 * (47 : ZMod 10708457761) ^ 217864 := by rw [pow_add]
          _ = 9105764709 := by rw [factor_1_17]; decide
      have factor_1_19 : (47 : ZMod 10708457761) ^ 871456 = 9571198055 := by
        calc
          (47 : ZMod 10708457761) ^ 871456 = (47 : ZMod 10708457761) ^ (435728 + 435728) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 435728 * (47 : ZMod 10708457761) ^ 435728 := by rw [pow_add]
          _ = 9571198055 := by rw [factor_1_18]; decide
      have factor_1_20 : (47 : ZMod 10708457761) ^ 1742913 = 6803790400 := by
        calc
          (47 : ZMod 10708457761) ^ 1742913 = (47 : ZMod 10708457761) ^ (871456 + 871456 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 871456 * (47 : ZMod 10708457761) ^ 871456) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 6803790400 := by rw [factor_1_19]; decide
      have factor_1_21 : (47 : ZMod 10708457761) ^ 3485826 = 1016833518 := by
        calc
          (47 : ZMod 10708457761) ^ 3485826 = (47 : ZMod 10708457761) ^ (1742913 + 1742913) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 1742913 * (47 : ZMod 10708457761) ^ 1742913 := by rw [pow_add]
          _ = 1016833518 := by rw [factor_1_20]; decide
      have factor_1_22 : (47 : ZMod 10708457761) ^ 6971652 = 8061689447 := by
        calc
          (47 : ZMod 10708457761) ^ 6971652 = (47 : ZMod 10708457761) ^ (3485826 + 3485826) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 3485826 * (47 : ZMod 10708457761) ^ 3485826 := by rw [pow_add]
          _ = 8061689447 := by rw [factor_1_21]; decide
      have factor_1_23 : (47 : ZMod 10708457761) ^ 13943304 = 2175487373 := by
        calc
          (47 : ZMod 10708457761) ^ 13943304 = (47 : ZMod 10708457761) ^ (6971652 + 6971652) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 6971652 * (47 : ZMod 10708457761) ^ 6971652 := by rw [pow_add]
          _ = 2175487373 := by rw [factor_1_22]; decide
      have factor_1_24 : (47 : ZMod 10708457761) ^ 27886608 = 1537185351 := by
        calc
          (47 : ZMod 10708457761) ^ 27886608 = (47 : ZMod 10708457761) ^ (13943304 + 13943304) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 13943304 * (47 : ZMod 10708457761) ^ 13943304 := by rw [pow_add]
          _ = 1537185351 := by rw [factor_1_23]; decide
      have factor_1_25 : (47 : ZMod 10708457761) ^ 55773217 = 6193079102 := by
        calc
          (47 : ZMod 10708457761) ^ 55773217 = (47 : ZMod 10708457761) ^ (27886608 + 27886608 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 27886608 * (47 : ZMod 10708457761) ^ 27886608) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 6193079102 := by rw [factor_1_24]; decide
      have factor_1_26 : (47 : ZMod 10708457761) ^ 111546435 = 2995698519 := by
        calc
          (47 : ZMod 10708457761) ^ 111546435 = (47 : ZMod 10708457761) ^ (55773217 + 55773217 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 55773217 * (47 : ZMod 10708457761) ^ 55773217) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 2995698519 := by rw [factor_1_25]; decide
      have factor_1_27 : (47 : ZMod 10708457761) ^ 223092870 = 7830317894 := by
        calc
          (47 : ZMod 10708457761) ^ 223092870 = (47 : ZMod 10708457761) ^ (111546435 + 111546435) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 111546435 * (47 : ZMod 10708457761) ^ 111546435 := by rw [pow_add]
          _ = 7830317894 := by rw [factor_1_26]; decide
      have factor_1_28 : (47 : ZMod 10708457761) ^ 446185740 = 2365614199 := by
        calc
          (47 : ZMod 10708457761) ^ 446185740 = (47 : ZMod 10708457761) ^ (223092870 + 223092870) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 223092870 * (47 : ZMod 10708457761) ^ 223092870 := by rw [pow_add]
          _ = 2365614199 := by rw [factor_1_27]; decide
      have factor_1_29 : (47 : ZMod 10708457761) ^ 892371480 = 6592417826 := by
        calc
          (47 : ZMod 10708457761) ^ 892371480 = (47 : ZMod 10708457761) ^ (446185740 + 446185740) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 446185740 * (47 : ZMod 10708457761) ^ 446185740 := by rw [pow_add]
          _ = 6592417826 := by rw [factor_1_28]; decide
      have factor_1_30 : (47 : ZMod 10708457761) ^ 1784742960 = 8190244815 := by
        calc
          (47 : ZMod 10708457761) ^ 1784742960 = (47 : ZMod 10708457761) ^ (892371480 + 892371480) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 892371480 * (47 : ZMod 10708457761) ^ 892371480 := by rw [pow_add]
          _ = 8190244815 := by rw [factor_1_29]; decide
      have factor_1_31 : (47 : ZMod 10708457761) ^ 3569485920 = 8190244814 := by
        calc
          (47 : ZMod 10708457761) ^ 3569485920 = (47 : ZMod 10708457761) ^ (1784742960 + 1784742960) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 1784742960 * (47 : ZMod 10708457761) ^ 1784742960 := by rw [pow_add]
          _ = 8190244814 := by rw [factor_1_30]; decide
      change (47 : ZMod 10708457761) ^ 3569485920 ≠ 1
      rw [factor_1_31]
      decide
    ·
      have factor_2_0 : (47 : ZMod 10708457761) ^ 1 = 47 := by norm_num
      have factor_2_1 : (47 : ZMod 10708457761) ^ 3 = 103823 := by
        calc
          (47 : ZMod 10708457761) ^ 3 = (47 : ZMod 10708457761) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 1 * (47 : ZMod 10708457761) ^ 1) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_2_0]; decide
      have factor_2_2 : (47 : ZMod 10708457761) ^ 7 = 3325605696 := by
        calc
          (47 : ZMod 10708457761) ^ 7 = (47 : ZMod 10708457761) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 3 * (47 : ZMod 10708457761) ^ 3) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 3325605696 := by rw [factor_2_1]; decide
      have factor_2_3 : (47 : ZMod 10708457761) ^ 15 = 7245733187 := by
        calc
          (47 : ZMod 10708457761) ^ 15 = (47 : ZMod 10708457761) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 7 * (47 : ZMod 10708457761) ^ 7) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 7245733187 := by rw [factor_2_2]; decide
      have factor_2_4 : (47 : ZMod 10708457761) ^ 31 = 885363206 := by
        calc
          (47 : ZMod 10708457761) ^ 31 = (47 : ZMod 10708457761) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 15 * (47 : ZMod 10708457761) ^ 15) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 885363206 := by rw [factor_2_3]; decide
      have factor_2_5 : (47 : ZMod 10708457761) ^ 63 = 7551870637 := by
        calc
          (47 : ZMod 10708457761) ^ 63 = (47 : ZMod 10708457761) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 31 * (47 : ZMod 10708457761) ^ 31) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 7551870637 := by rw [factor_2_4]; decide
      have factor_2_6 : (47 : ZMod 10708457761) ^ 127 = 9718682019 := by
        calc
          (47 : ZMod 10708457761) ^ 127 = (47 : ZMod 10708457761) ^ (63 + 63 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 63 * (47 : ZMod 10708457761) ^ 63) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 9718682019 := by rw [factor_2_5]; decide
      have factor_2_7 : (47 : ZMod 10708457761) ^ 255 = 4888564000 := by
        calc
          (47 : ZMod 10708457761) ^ 255 = (47 : ZMod 10708457761) ^ (127 + 127 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 127 * (47 : ZMod 10708457761) ^ 127) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 4888564000 := by rw [factor_2_6]; decide
      have factor_2_8 : (47 : ZMod 10708457761) ^ 510 = 3664373153 := by
        calc
          (47 : ZMod 10708457761) ^ 510 = (47 : ZMod 10708457761) ^ (255 + 255) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 255 * (47 : ZMod 10708457761) ^ 255 := by rw [pow_add]
          _ = 3664373153 := by rw [factor_2_7]; decide
      have factor_2_9 : (47 : ZMod 10708457761) ^ 1021 = 1860084818 := by
        calc
          (47 : ZMod 10708457761) ^ 1021 = (47 : ZMod 10708457761) ^ (510 + 510 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 510 * (47 : ZMod 10708457761) ^ 510) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 1860084818 := by rw [factor_2_8]; decide
      have factor_2_10 : (47 : ZMod 10708457761) ^ 2042 = 9551053207 := by
        calc
          (47 : ZMod 10708457761) ^ 2042 = (47 : ZMod 10708457761) ^ (1021 + 1021) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 1021 * (47 : ZMod 10708457761) ^ 1021 := by rw [pow_add]
          _ = 9551053207 := by rw [factor_2_9]; decide
      have factor_2_11 : (47 : ZMod 10708457761) ^ 4084 = 5299136350 := by
        calc
          (47 : ZMod 10708457761) ^ 4084 = (47 : ZMod 10708457761) ^ (2042 + 2042) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 2042 * (47 : ZMod 10708457761) ^ 2042 := by rw [pow_add]
          _ = 5299136350 := by rw [factor_2_10]; decide
      have factor_2_12 : (47 : ZMod 10708457761) ^ 8169 = 7570625823 := by
        calc
          (47 : ZMod 10708457761) ^ 8169 = (47 : ZMod 10708457761) ^ (4084 + 4084 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 4084 * (47 : ZMod 10708457761) ^ 4084) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 7570625823 := by rw [factor_2_11]; decide
      have factor_2_13 : (47 : ZMod 10708457761) ^ 16339 = 9782473015 := by
        calc
          (47 : ZMod 10708457761) ^ 16339 = (47 : ZMod 10708457761) ^ (8169 + 8169 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 8169 * (47 : ZMod 10708457761) ^ 8169) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 9782473015 := by rw [factor_2_12]; decide
      have factor_2_14 : (47 : ZMod 10708457761) ^ 32679 = 6688165966 := by
        calc
          (47 : ZMod 10708457761) ^ 32679 = (47 : ZMod 10708457761) ^ (16339 + 16339 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 16339 * (47 : ZMod 10708457761) ^ 16339) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 6688165966 := by rw [factor_2_13]; decide
      have factor_2_15 : (47 : ZMod 10708457761) ^ 65359 = 8843647769 := by
        calc
          (47 : ZMod 10708457761) ^ 65359 = (47 : ZMod 10708457761) ^ (32679 + 32679 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 32679 * (47 : ZMod 10708457761) ^ 32679) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 8843647769 := by rw [factor_2_14]; decide
      have factor_2_16 : (47 : ZMod 10708457761) ^ 130718 = 396456673 := by
        calc
          (47 : ZMod 10708457761) ^ 130718 = (47 : ZMod 10708457761) ^ (65359 + 65359) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 65359 * (47 : ZMod 10708457761) ^ 65359 := by rw [pow_add]
          _ = 396456673 := by rw [factor_2_15]; decide
      have factor_2_17 : (47 : ZMod 10708457761) ^ 261436 = 7226891809 := by
        calc
          (47 : ZMod 10708457761) ^ 261436 = (47 : ZMod 10708457761) ^ (130718 + 130718) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 130718 * (47 : ZMod 10708457761) ^ 130718 := by rw [pow_add]
          _ = 7226891809 := by rw [factor_2_16]; decide
      have factor_2_18 : (47 : ZMod 10708457761) ^ 522873 = 1916099077 := by
        calc
          (47 : ZMod 10708457761) ^ 522873 = (47 : ZMod 10708457761) ^ (261436 + 261436 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 261436 * (47 : ZMod 10708457761) ^ 261436) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 1916099077 := by rw [factor_2_17]; decide
      have factor_2_19 : (47 : ZMod 10708457761) ^ 1045747 = 9445246862 := by
        calc
          (47 : ZMod 10708457761) ^ 1045747 = (47 : ZMod 10708457761) ^ (522873 + 522873 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 522873 * (47 : ZMod 10708457761) ^ 522873) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 9445246862 := by rw [factor_2_18]; decide
      have factor_2_20 : (47 : ZMod 10708457761) ^ 2091495 = 8924074814 := by
        calc
          (47 : ZMod 10708457761) ^ 2091495 = (47 : ZMod 10708457761) ^ (1045747 + 1045747 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 1045747 * (47 : ZMod 10708457761) ^ 1045747) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 8924074814 := by rw [factor_2_19]; decide
      have factor_2_21 : (47 : ZMod 10708457761) ^ 4182991 = 9539017060 := by
        calc
          (47 : ZMod 10708457761) ^ 4182991 = (47 : ZMod 10708457761) ^ (2091495 + 2091495 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 2091495 * (47 : ZMod 10708457761) ^ 2091495) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 9539017060 := by rw [factor_2_20]; decide
      have factor_2_22 : (47 : ZMod 10708457761) ^ 8365982 = 9622372856 := by
        calc
          (47 : ZMod 10708457761) ^ 8365982 = (47 : ZMod 10708457761) ^ (4182991 + 4182991) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 4182991 * (47 : ZMod 10708457761) ^ 4182991 := by rw [pow_add]
          _ = 9622372856 := by rw [factor_2_21]; decide
      have factor_2_23 : (47 : ZMod 10708457761) ^ 16731965 = 10290553862 := by
        calc
          (47 : ZMod 10708457761) ^ 16731965 = (47 : ZMod 10708457761) ^ (8365982 + 8365982 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 8365982 * (47 : ZMod 10708457761) ^ 8365982) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 10290553862 := by rw [factor_2_22]; decide
      have factor_2_24 : (47 : ZMod 10708457761) ^ 33463930 = 9431972295 := by
        calc
          (47 : ZMod 10708457761) ^ 33463930 = (47 : ZMod 10708457761) ^ (16731965 + 16731965) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 16731965 * (47 : ZMod 10708457761) ^ 16731965 := by rw [pow_add]
          _ = 9431972295 := by rw [factor_2_23]; decide
      have factor_2_25 : (47 : ZMod 10708457761) ^ 66927861 = 3475442377 := by
        calc
          (47 : ZMod 10708457761) ^ 66927861 = (47 : ZMod 10708457761) ^ (33463930 + 33463930 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 33463930 * (47 : ZMod 10708457761) ^ 33463930) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 3475442377 := by rw [factor_2_24]; decide
      have factor_2_26 : (47 : ZMod 10708457761) ^ 133855722 = 3767817518 := by
        calc
          (47 : ZMod 10708457761) ^ 133855722 = (47 : ZMod 10708457761) ^ (66927861 + 66927861) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 66927861 * (47 : ZMod 10708457761) ^ 66927861 := by rw [pow_add]
          _ = 3767817518 := by rw [factor_2_25]; decide
      have factor_2_27 : (47 : ZMod 10708457761) ^ 267711444 = 4285357475 := by
        calc
          (47 : ZMod 10708457761) ^ 267711444 = (47 : ZMod 10708457761) ^ (133855722 + 133855722) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 133855722 * (47 : ZMod 10708457761) ^ 133855722 := by rw [pow_add]
          _ = 4285357475 := by rw [factor_2_26]; decide
      have factor_2_28 : (47 : ZMod 10708457761) ^ 535422888 = 2830671003 := by
        calc
          (47 : ZMod 10708457761) ^ 535422888 = (47 : ZMod 10708457761) ^ (267711444 + 267711444) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 267711444 * (47 : ZMod 10708457761) ^ 267711444 := by rw [pow_add]
          _ = 2830671003 := by rw [factor_2_27]; decide
      have factor_2_29 : (47 : ZMod 10708457761) ^ 1070845776 = 5580217876 := by
        calc
          (47 : ZMod 10708457761) ^ 1070845776 = (47 : ZMod 10708457761) ^ (535422888 + 535422888) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 535422888 * (47 : ZMod 10708457761) ^ 535422888 := by rw [pow_add]
          _ = 5580217876 := by rw [factor_2_28]; decide
      have factor_2_30 : (47 : ZMod 10708457761) ^ 2141691552 = 361694877 := by
        calc
          (47 : ZMod 10708457761) ^ 2141691552 = (47 : ZMod 10708457761) ^ (1070845776 + 1070845776) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 1070845776 * (47 : ZMod 10708457761) ^ 1070845776 := by rw [pow_add]
          _ = 361694877 := by rw [factor_2_29]; decide
      change (47 : ZMod 10708457761) ^ 2141691552 ≠ 1
      rw [factor_2_30]
      decide
    ·
      have factor_3_0 : (47 : ZMod 10708457761) ^ 1 = 47 := by norm_num
      have factor_3_1 : (47 : ZMod 10708457761) ^ 2 = 2209 := by
        calc
          (47 : ZMod 10708457761) ^ 2 = (47 : ZMod 10708457761) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 1 * (47 : ZMod 10708457761) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_3_0]; decide
      have factor_3_2 : (47 : ZMod 10708457761) ^ 5 = 229345007 := by
        calc
          (47 : ZMod 10708457761) ^ 5 = (47 : ZMod 10708457761) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 2 * (47 : ZMod 10708457761) ^ 2) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 229345007 := by rw [factor_3_1]; decide
      have factor_3_3 : (47 : ZMod 10708457761) ^ 11 = 8908884029 := by
        calc
          (47 : ZMod 10708457761) ^ 11 = (47 : ZMod 10708457761) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 5 * (47 : ZMod 10708457761) ^ 5) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 8908884029 := by rw [factor_3_2]; decide
      have factor_3_4 : (47 : ZMod 10708457761) ^ 22 = 6912276134 := by
        calc
          (47 : ZMod 10708457761) ^ 22 = (47 : ZMod 10708457761) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 11 * (47 : ZMod 10708457761) ^ 11 := by rw [pow_add]
          _ = 6912276134 := by rw [factor_3_3]; decide
      have factor_3_5 : (47 : ZMod 10708457761) ^ 45 = 2733176647 := by
        calc
          (47 : ZMod 10708457761) ^ 45 = (47 : ZMod 10708457761) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 22 * (47 : ZMod 10708457761) ^ 22) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 2733176647 := by rw [factor_3_4]; decide
      have factor_3_6 : (47 : ZMod 10708457761) ^ 91 = 3208521662 := by
        calc
          (47 : ZMod 10708457761) ^ 91 = (47 : ZMod 10708457761) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 45 * (47 : ZMod 10708457761) ^ 45) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 3208521662 := by rw [factor_3_5]; decide
      have factor_3_7 : (47 : ZMod 10708457761) ^ 182 = 6241449900 := by
        calc
          (47 : ZMod 10708457761) ^ 182 = (47 : ZMod 10708457761) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 91 * (47 : ZMod 10708457761) ^ 91 := by rw [pow_add]
          _ = 6241449900 := by rw [factor_3_6]; decide
      have factor_3_8 : (47 : ZMod 10708457761) ^ 364 = 9458954024 := by
        calc
          (47 : ZMod 10708457761) ^ 364 = (47 : ZMod 10708457761) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 182 * (47 : ZMod 10708457761) ^ 182 := by rw [pow_add]
          _ = 9458954024 := by rw [factor_3_7]; decide
      have factor_3_9 : (47 : ZMod 10708457761) ^ 729 = 520936608 := by
        calc
          (47 : ZMod 10708457761) ^ 729 = (47 : ZMod 10708457761) ^ (364 + 364 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 364 * (47 : ZMod 10708457761) ^ 364) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 520936608 := by rw [factor_3_8]; decide
      have factor_3_10 : (47 : ZMod 10708457761) ^ 1458 = 2919556671 := by
        calc
          (47 : ZMod 10708457761) ^ 1458 = (47 : ZMod 10708457761) ^ (729 + 729) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 729 * (47 : ZMod 10708457761) ^ 729 := by rw [pow_add]
          _ = 2919556671 := by rw [factor_3_9]; decide
      have factor_3_11 : (47 : ZMod 10708457761) ^ 2917 = 6033418660 := by
        calc
          (47 : ZMod 10708457761) ^ 2917 = (47 : ZMod 10708457761) ^ (1458 + 1458 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 1458 * (47 : ZMod 10708457761) ^ 1458) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 6033418660 := by rw [factor_3_10]; decide
      have factor_3_12 : (47 : ZMod 10708457761) ^ 5835 = 1610807612 := by
        calc
          (47 : ZMod 10708457761) ^ 5835 = (47 : ZMod 10708457761) ^ (2917 + 2917 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 2917 * (47 : ZMod 10708457761) ^ 2917) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 1610807612 := by rw [factor_3_11]; decide
      have factor_3_13 : (47 : ZMod 10708457761) ^ 11671 = 4744636698 := by
        calc
          (47 : ZMod 10708457761) ^ 11671 = (47 : ZMod 10708457761) ^ (5835 + 5835 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 5835 * (47 : ZMod 10708457761) ^ 5835) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 4744636698 := by rw [factor_3_12]; decide
      have factor_3_14 : (47 : ZMod 10708457761) ^ 23342 = 5967279959 := by
        calc
          (47 : ZMod 10708457761) ^ 23342 = (47 : ZMod 10708457761) ^ (11671 + 11671) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 11671 * (47 : ZMod 10708457761) ^ 11671 := by rw [pow_add]
          _ = 5967279959 := by rw [factor_3_13]; decide
      have factor_3_15 : (47 : ZMod 10708457761) ^ 46685 = 7969420068 := by
        calc
          (47 : ZMod 10708457761) ^ 46685 = (47 : ZMod 10708457761) ^ (23342 + 23342 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 23342 * (47 : ZMod 10708457761) ^ 23342) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 7969420068 := by rw [factor_3_14]; decide
      have factor_3_16 : (47 : ZMod 10708457761) ^ 93370 = 9361031773 := by
        calc
          (47 : ZMod 10708457761) ^ 93370 = (47 : ZMod 10708457761) ^ (46685 + 46685) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 46685 * (47 : ZMod 10708457761) ^ 46685 := by rw [pow_add]
          _ = 9361031773 := by rw [factor_3_15]; decide
      have factor_3_17 : (47 : ZMod 10708457761) ^ 186740 = 6608275315 := by
        calc
          (47 : ZMod 10708457761) ^ 186740 = (47 : ZMod 10708457761) ^ (93370 + 93370) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 93370 * (47 : ZMod 10708457761) ^ 93370 := by rw [pow_add]
          _ = 6608275315 := by rw [factor_3_16]; decide
      have factor_3_18 : (47 : ZMod 10708457761) ^ 373481 = 4109430141 := by
        calc
          (47 : ZMod 10708457761) ^ 373481 = (47 : ZMod 10708457761) ^ (186740 + 186740 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 186740 * (47 : ZMod 10708457761) ^ 186740) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 4109430141 := by rw [factor_3_17]; decide
      have factor_3_19 : (47 : ZMod 10708457761) ^ 746962 = 5925136841 := by
        calc
          (47 : ZMod 10708457761) ^ 746962 = (47 : ZMod 10708457761) ^ (373481 + 373481) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 373481 * (47 : ZMod 10708457761) ^ 373481 := by rw [pow_add]
          _ = 5925136841 := by rw [factor_3_18]; decide
      have factor_3_20 : (47 : ZMod 10708457761) ^ 1493925 = 2920145170 := by
        calc
          (47 : ZMod 10708457761) ^ 1493925 = (47 : ZMod 10708457761) ^ (746962 + 746962 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 746962 * (47 : ZMod 10708457761) ^ 746962) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 2920145170 := by rw [factor_3_19]; decide
      have factor_3_21 : (47 : ZMod 10708457761) ^ 2987850 = 1219403451 := by
        calc
          (47 : ZMod 10708457761) ^ 2987850 = (47 : ZMod 10708457761) ^ (1493925 + 1493925) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 1493925 * (47 : ZMod 10708457761) ^ 1493925 := by rw [pow_add]
          _ = 1219403451 := by rw [factor_3_20]; decide
      have factor_3_22 : (47 : ZMod 10708457761) ^ 5975701 = 8144212042 := by
        calc
          (47 : ZMod 10708457761) ^ 5975701 = (47 : ZMod 10708457761) ^ (2987850 + 2987850 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 2987850 * (47 : ZMod 10708457761) ^ 2987850) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 8144212042 := by rw [factor_3_21]; decide
      have factor_3_23 : (47 : ZMod 10708457761) ^ 11951403 = 6934454396 := by
        calc
          (47 : ZMod 10708457761) ^ 11951403 = (47 : ZMod 10708457761) ^ (5975701 + 5975701 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 5975701 * (47 : ZMod 10708457761) ^ 5975701) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 6934454396 := by rw [factor_3_22]; decide
      have factor_3_24 : (47 : ZMod 10708457761) ^ 23902807 = 1169783009 := by
        calc
          (47 : ZMod 10708457761) ^ 23902807 = (47 : ZMod 10708457761) ^ (11951403 + 11951403 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 11951403 * (47 : ZMod 10708457761) ^ 11951403) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 1169783009 := by rw [factor_3_23]; decide
      have factor_3_25 : (47 : ZMod 10708457761) ^ 47805615 = 4174420321 := by
        calc
          (47 : ZMod 10708457761) ^ 47805615 = (47 : ZMod 10708457761) ^ (23902807 + 23902807 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 23902807 * (47 : ZMod 10708457761) ^ 23902807) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 4174420321 := by rw [factor_3_24]; decide
      have factor_3_26 : (47 : ZMod 10708457761) ^ 95611230 = 3845140247 := by
        calc
          (47 : ZMod 10708457761) ^ 95611230 = (47 : ZMod 10708457761) ^ (47805615 + 47805615) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 47805615 * (47 : ZMod 10708457761) ^ 47805615 := by rw [pow_add]
          _ = 3845140247 := by rw [factor_3_25]; decide
      have factor_3_27 : (47 : ZMod 10708457761) ^ 191222460 = 23136116 := by
        calc
          (47 : ZMod 10708457761) ^ 191222460 = (47 : ZMod 10708457761) ^ (95611230 + 95611230) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 95611230 * (47 : ZMod 10708457761) ^ 95611230 := by rw [pow_add]
          _ = 23136116 := by rw [factor_3_26]; decide
      have factor_3_28 : (47 : ZMod 10708457761) ^ 382444920 = 6893924110 := by
        calc
          (47 : ZMod 10708457761) ^ 382444920 = (47 : ZMod 10708457761) ^ (191222460 + 191222460) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 191222460 * (47 : ZMod 10708457761) ^ 191222460 := by rw [pow_add]
          _ = 6893924110 := by rw [factor_3_27]; decide
      have factor_3_29 : (47 : ZMod 10708457761) ^ 764889840 = 5462034841 := by
        calc
          (47 : ZMod 10708457761) ^ 764889840 = (47 : ZMod 10708457761) ^ (382444920 + 382444920) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 382444920 * (47 : ZMod 10708457761) ^ 382444920 := by rw [pow_add]
          _ = 5462034841 := by rw [factor_3_28]; decide
      have factor_3_30 : (47 : ZMod 10708457761) ^ 1529779680 = 8356586839 := by
        calc
          (47 : ZMod 10708457761) ^ 1529779680 = (47 : ZMod 10708457761) ^ (764889840 + 764889840) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 764889840 * (47 : ZMod 10708457761) ^ 764889840 := by rw [pow_add]
          _ = 8356586839 := by rw [factor_3_29]; decide
      change (47 : ZMod 10708457761) ^ 1529779680 ≠ 1
      rw [factor_3_30]
      decide
    ·
      have factor_4_0 : (47 : ZMod 10708457761) ^ 1 = 47 := by norm_num
      have factor_4_1 : (47 : ZMod 10708457761) ^ 3 = 103823 := by
        calc
          (47 : ZMod 10708457761) ^ 3 = (47 : ZMod 10708457761) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 1 * (47 : ZMod 10708457761) ^ 1) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_4_0]; decide
      have factor_4_2 : (47 : ZMod 10708457761) ^ 7 = 3325605696 := by
        calc
          (47 : ZMod 10708457761) ^ 7 = (47 : ZMod 10708457761) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 3 * (47 : ZMod 10708457761) ^ 3) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 3325605696 := by rw [factor_4_1]; decide
      have factor_4_3 : (47 : ZMod 10708457761) ^ 14 = 4027436492 := by
        calc
          (47 : ZMod 10708457761) ^ 14 = (47 : ZMod 10708457761) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 7 * (47 : ZMod 10708457761) ^ 7 := by rw [pow_add]
          _ = 4027436492 := by rw [factor_4_2]; decide
      have factor_4_4 : (47 : ZMod 10708457761) ^ 29 = 4358437705 := by
        calc
          (47 : ZMod 10708457761) ^ 29 = (47 : ZMod 10708457761) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 14 * (47 : ZMod 10708457761) ^ 14) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 4358437705 := by rw [factor_4_3]; decide
      have factor_4_5 : (47 : ZMod 10708457761) ^ 58 = 727623572 := by
        calc
          (47 : ZMod 10708457761) ^ 58 = (47 : ZMod 10708457761) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 29 * (47 : ZMod 10708457761) ^ 29 := by rw [pow_add]
          _ = 727623572 := by rw [factor_4_4]; decide
      have factor_4_6 : (47 : ZMod 10708457761) ^ 116 = 5502770259 := by
        calc
          (47 : ZMod 10708457761) ^ 116 = (47 : ZMod 10708457761) ^ (58 + 58) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 58 * (47 : ZMod 10708457761) ^ 58 := by rw [pow_add]
          _ = 5502770259 := by rw [factor_4_5]; decide
      have factor_4_7 : (47 : ZMod 10708457761) ^ 232 = 7527553825 := by
        calc
          (47 : ZMod 10708457761) ^ 232 = (47 : ZMod 10708457761) ^ (116 + 116) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 116 * (47 : ZMod 10708457761) ^ 116 := by rw [pow_add]
          _ = 7527553825 := by rw [factor_4_6]; decide
      have factor_4_8 : (47 : ZMod 10708457761) ^ 464 = 10142401647 := by
        calc
          (47 : ZMod 10708457761) ^ 464 = (47 : ZMod 10708457761) ^ (232 + 232) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 232 * (47 : ZMod 10708457761) ^ 232 := by rw [pow_add]
          _ = 10142401647 := by rw [factor_4_7]; decide
      have factor_4_9 : (47 : ZMod 10708457761) ^ 928 = 1643278418 := by
        calc
          (47 : ZMod 10708457761) ^ 928 = (47 : ZMod 10708457761) ^ (464 + 464) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 464 * (47 : ZMod 10708457761) ^ 464 := by rw [pow_add]
          _ = 1643278418 := by rw [factor_4_8]; decide
      have factor_4_10 : (47 : ZMod 10708457761) ^ 1856 = 665196228 := by
        calc
          (47 : ZMod 10708457761) ^ 1856 = (47 : ZMod 10708457761) ^ (928 + 928) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 928 * (47 : ZMod 10708457761) ^ 928 := by rw [pow_add]
          _ = 665196228 := by rw [factor_4_9]; decide
      have factor_4_11 : (47 : ZMod 10708457761) ^ 3713 = 7802234739 := by
        calc
          (47 : ZMod 10708457761) ^ 3713 = (47 : ZMod 10708457761) ^ (1856 + 1856 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 1856 * (47 : ZMod 10708457761) ^ 1856) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 7802234739 := by rw [factor_4_10]; decide
      have factor_4_12 : (47 : ZMod 10708457761) ^ 7427 = 3276665459 := by
        calc
          (47 : ZMod 10708457761) ^ 7427 = (47 : ZMod 10708457761) ^ (3713 + 3713 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 3713 * (47 : ZMod 10708457761) ^ 3713) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 3276665459 := by rw [factor_4_11]; decide
      have factor_4_13 : (47 : ZMod 10708457761) ^ 14854 = 4315527210 := by
        calc
          (47 : ZMod 10708457761) ^ 14854 = (47 : ZMod 10708457761) ^ (7427 + 7427) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 7427 * (47 : ZMod 10708457761) ^ 7427 := by rw [pow_add]
          _ = 4315527210 := by rw [factor_4_12]; decide
      have factor_4_14 : (47 : ZMod 10708457761) ^ 29708 = 8422410446 := by
        calc
          (47 : ZMod 10708457761) ^ 29708 = (47 : ZMod 10708457761) ^ (14854 + 14854) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 14854 * (47 : ZMod 10708457761) ^ 14854 := by rw [pow_add]
          _ = 8422410446 := by rw [factor_4_13]; decide
      have factor_4_15 : (47 : ZMod 10708457761) ^ 59417 = 9605933843 := by
        calc
          (47 : ZMod 10708457761) ^ 59417 = (47 : ZMod 10708457761) ^ (29708 + 29708 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 29708 * (47 : ZMod 10708457761) ^ 29708) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 9605933843 := by rw [factor_4_14]; decide
      have factor_4_16 : (47 : ZMod 10708457761) ^ 118834 = 4281910887 := by
        calc
          (47 : ZMod 10708457761) ^ 118834 = (47 : ZMod 10708457761) ^ (59417 + 59417) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 59417 * (47 : ZMod 10708457761) ^ 59417 := by rw [pow_add]
          _ = 4281910887 := by rw [factor_4_15]; decide
      have factor_4_17 : (47 : ZMod 10708457761) ^ 237669 = 4512803882 := by
        calc
          (47 : ZMod 10708457761) ^ 237669 = (47 : ZMod 10708457761) ^ (118834 + 118834 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 118834 * (47 : ZMod 10708457761) ^ 118834) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 4512803882 := by rw [factor_4_16]; decide
      have factor_4_18 : (47 : ZMod 10708457761) ^ 475339 = 418460545 := by
        calc
          (47 : ZMod 10708457761) ^ 475339 = (47 : ZMod 10708457761) ^ (237669 + 237669 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 237669 * (47 : ZMod 10708457761) ^ 237669) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 418460545 := by rw [factor_4_17]; decide
      have factor_4_19 : (47 : ZMod 10708457761) ^ 950679 = 7227896149 := by
        calc
          (47 : ZMod 10708457761) ^ 950679 = (47 : ZMod 10708457761) ^ (475339 + 475339 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 475339 * (47 : ZMod 10708457761) ^ 475339) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 7227896149 := by rw [factor_4_18]; decide
      have factor_4_20 : (47 : ZMod 10708457761) ^ 1901359 = 9492772610 := by
        calc
          (47 : ZMod 10708457761) ^ 1901359 = (47 : ZMod 10708457761) ^ (950679 + 950679 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 950679 * (47 : ZMod 10708457761) ^ 950679) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 9492772610 := by rw [factor_4_19]; decide
      have factor_4_21 : (47 : ZMod 10708457761) ^ 3802719 = 8622728369 := by
        calc
          (47 : ZMod 10708457761) ^ 3802719 = (47 : ZMod 10708457761) ^ (1901359 + 1901359 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 1901359 * (47 : ZMod 10708457761) ^ 1901359) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 8622728369 := by rw [factor_4_20]; decide
      have factor_4_22 : (47 : ZMod 10708457761) ^ 7605438 = 3797886481 := by
        calc
          (47 : ZMod 10708457761) ^ 7605438 = (47 : ZMod 10708457761) ^ (3802719 + 3802719) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 3802719 * (47 : ZMod 10708457761) ^ 3802719 := by rw [pow_add]
          _ = 3797886481 := by rw [factor_4_21]; decide
      have factor_4_23 : (47 : ZMod 10708457761) ^ 15210877 = 1164812885 := by
        calc
          (47 : ZMod 10708457761) ^ 15210877 = (47 : ZMod 10708457761) ^ (7605438 + 7605438 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 7605438 * (47 : ZMod 10708457761) ^ 7605438) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 1164812885 := by rw [factor_4_22]; decide
      have factor_4_24 : (47 : ZMod 10708457761) ^ 30421755 = 9732209138 := by
        calc
          (47 : ZMod 10708457761) ^ 30421755 = (47 : ZMod 10708457761) ^ (15210877 + 15210877 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 15210877 * (47 : ZMod 10708457761) ^ 15210877) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 9732209138 := by rw [factor_4_23]; decide
      have factor_4_25 : (47 : ZMod 10708457761) ^ 60843510 = 2163440763 := by
        calc
          (47 : ZMod 10708457761) ^ 60843510 = (47 : ZMod 10708457761) ^ (30421755 + 30421755) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 30421755 * (47 : ZMod 10708457761) ^ 30421755 := by rw [pow_add]
          _ = 2163440763 := by rw [factor_4_24]; decide
      have factor_4_26 : (47 : ZMod 10708457761) ^ 121687020 = 895716321 := by
        calc
          (47 : ZMod 10708457761) ^ 121687020 = (47 : ZMod 10708457761) ^ (60843510 + 60843510) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 60843510 * (47 : ZMod 10708457761) ^ 60843510 := by rw [pow_add]
          _ = 895716321 := by rw [factor_4_25]; decide
      have factor_4_27 : (47 : ZMod 10708457761) ^ 243374040 = 2902262153 := by
        calc
          (47 : ZMod 10708457761) ^ 243374040 = (47 : ZMod 10708457761) ^ (121687020 + 121687020) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 121687020 * (47 : ZMod 10708457761) ^ 121687020 := by rw [pow_add]
          _ = 2902262153 := by rw [factor_4_26]; decide
      have factor_4_28 : (47 : ZMod 10708457761) ^ 486748080 = 3353182442 := by
        calc
          (47 : ZMod 10708457761) ^ 486748080 = (47 : ZMod 10708457761) ^ (243374040 + 243374040) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 243374040 * (47 : ZMod 10708457761) ^ 243374040 := by rw [pow_add]
          _ = 3353182442 := by rw [factor_4_27]; decide
      have factor_4_29 : (47 : ZMod 10708457761) ^ 973496160 = 6930092342 := by
        calc
          (47 : ZMod 10708457761) ^ 973496160 = (47 : ZMod 10708457761) ^ (486748080 + 486748080) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 486748080 * (47 : ZMod 10708457761) ^ 486748080 := by rw [pow_add]
          _ = 6930092342 := by rw [factor_4_28]; decide
      change (47 : ZMod 10708457761) ^ 973496160 ≠ 1
      rw [factor_4_29]
      decide
    ·
      have factor_5_0 : (47 : ZMod 10708457761) ^ 1 = 47 := by norm_num
      have factor_5_1 : (47 : ZMod 10708457761) ^ 3 = 103823 := by
        calc
          (47 : ZMod 10708457761) ^ 3 = (47 : ZMod 10708457761) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 1 * (47 : ZMod 10708457761) ^ 1) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_5_0]; decide
      have factor_5_2 : (47 : ZMod 10708457761) ^ 6 = 70757568 := by
        calc
          (47 : ZMod 10708457761) ^ 6 = (47 : ZMod 10708457761) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 3 * (47 : ZMod 10708457761) ^ 3 := by rw [pow_add]
          _ = 70757568 := by rw [factor_5_1]; decide
      have factor_5_3 : (47 : ZMod 10708457761) ^ 12 = 1087696684 := by
        calc
          (47 : ZMod 10708457761) ^ 12 = (47 : ZMod 10708457761) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 6 * (47 : ZMod 10708457761) ^ 6 := by rw [pow_add]
          _ = 1087696684 := by rw [factor_5_2]; decide
      have factor_5_4 : (47 : ZMod 10708457761) ^ 24 = 9665670581 := by
        calc
          (47 : ZMod 10708457761) ^ 24 = (47 : ZMod 10708457761) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 12 * (47 : ZMod 10708457761) ^ 12 := by rw [pow_add]
          _ = 9665670581 := by rw [factor_5_3]; decide
      have factor_5_5 : (47 : ZMod 10708457761) ^ 49 = 10100247981 := by
        calc
          (47 : ZMod 10708457761) ^ 49 = (47 : ZMod 10708457761) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 24 * (47 : ZMod 10708457761) ^ 24) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 10100247981 := by rw [factor_5_4]; decide
      have factor_5_6 : (47 : ZMod 10708457761) ^ 98 = 3519994064 := by
        calc
          (47 : ZMod 10708457761) ^ 98 = (47 : ZMod 10708457761) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 49 * (47 : ZMod 10708457761) ^ 49 := by rw [pow_add]
          _ = 3519994064 := by rw [factor_5_5]; decide
      have factor_5_7 : (47 : ZMod 10708457761) ^ 196 = 4303183208 := by
        calc
          (47 : ZMod 10708457761) ^ 196 = (47 : ZMod 10708457761) ^ (98 + 98) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 98 * (47 : ZMod 10708457761) ^ 98 := by rw [pow_add]
          _ = 4303183208 := by rw [factor_5_6]; decide
      have factor_5_8 : (47 : ZMod 10708457761) ^ 392 = 3608895729 := by
        calc
          (47 : ZMod 10708457761) ^ 392 = (47 : ZMod 10708457761) ^ (196 + 196) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 196 * (47 : ZMod 10708457761) ^ 196 := by rw [pow_add]
          _ = 3608895729 := by rw [factor_5_7]; decide
      have factor_5_9 : (47 : ZMod 10708457761) ^ 785 = 5990216026 := by
        calc
          (47 : ZMod 10708457761) ^ 785 = (47 : ZMod 10708457761) ^ (392 + 392 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 392 * (47 : ZMod 10708457761) ^ 392) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 5990216026 := by rw [factor_5_8]; decide
      have factor_5_10 : (47 : ZMod 10708457761) ^ 1571 = 5104888436 := by
        calc
          (47 : ZMod 10708457761) ^ 1571 = (47 : ZMod 10708457761) ^ (785 + 785 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 785 * (47 : ZMod 10708457761) ^ 785) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 5104888436 := by rw [factor_5_9]; decide
      have factor_5_11 : (47 : ZMod 10708457761) ^ 3142 = 4523501868 := by
        calc
          (47 : ZMod 10708457761) ^ 3142 = (47 : ZMod 10708457761) ^ (1571 + 1571) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 1571 * (47 : ZMod 10708457761) ^ 1571 := by rw [pow_add]
          _ = 4523501868 := by rw [factor_5_10]; decide
      have factor_5_12 : (47 : ZMod 10708457761) ^ 6284 = 3078083641 := by
        calc
          (47 : ZMod 10708457761) ^ 6284 = (47 : ZMod 10708457761) ^ (3142 + 3142) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 3142 * (47 : ZMod 10708457761) ^ 3142 := by rw [pow_add]
          _ = 3078083641 := by rw [factor_5_11]; decide
      have factor_5_13 : (47 : ZMod 10708457761) ^ 12569 = 4564293525 := by
        calc
          (47 : ZMod 10708457761) ^ 12569 = (47 : ZMod 10708457761) ^ (6284 + 6284 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 6284 * (47 : ZMod 10708457761) ^ 6284) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 4564293525 := by rw [factor_5_12]; decide
      have factor_5_14 : (47 : ZMod 10708457761) ^ 25138 = 9605516484 := by
        calc
          (47 : ZMod 10708457761) ^ 25138 = (47 : ZMod 10708457761) ^ (12569 + 12569) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 12569 * (47 : ZMod 10708457761) ^ 12569 := by rw [pow_add]
          _ = 9605516484 := by rw [factor_5_13]; decide
      have factor_5_15 : (47 : ZMod 10708457761) ^ 50276 = 8126468615 := by
        calc
          (47 : ZMod 10708457761) ^ 50276 = (47 : ZMod 10708457761) ^ (25138 + 25138) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 25138 * (47 : ZMod 10708457761) ^ 25138 := by rw [pow_add]
          _ = 8126468615 := by rw [factor_5_14]; decide
      have factor_5_16 : (47 : ZMod 10708457761) ^ 100552 = 2793501297 := by
        calc
          (47 : ZMod 10708457761) ^ 100552 = (47 : ZMod 10708457761) ^ (50276 + 50276) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 50276 * (47 : ZMod 10708457761) ^ 50276 := by rw [pow_add]
          _ = 2793501297 := by rw [factor_5_15]; decide
      have factor_5_17 : (47 : ZMod 10708457761) ^ 201105 = 8566193128 := by
        calc
          (47 : ZMod 10708457761) ^ 201105 = (47 : ZMod 10708457761) ^ (100552 + 100552 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 100552 * (47 : ZMod 10708457761) ^ 100552) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 8566193128 := by rw [factor_5_16]; decide
      have factor_5_18 : (47 : ZMod 10708457761) ^ 402210 = 4597840636 := by
        calc
          (47 : ZMod 10708457761) ^ 402210 = (47 : ZMod 10708457761) ^ (201105 + 201105) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 201105 * (47 : ZMod 10708457761) ^ 201105 := by rw [pow_add]
          _ = 4597840636 := by rw [factor_5_17]; decide
      have factor_5_19 : (47 : ZMod 10708457761) ^ 804421 = 9335898323 := by
        calc
          (47 : ZMod 10708457761) ^ 804421 = (47 : ZMod 10708457761) ^ (402210 + 402210 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 402210 * (47 : ZMod 10708457761) ^ 402210) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 9335898323 := by rw [factor_5_18]; decide
      have factor_5_20 : (47 : ZMod 10708457761) ^ 1608842 = 1302475191 := by
        calc
          (47 : ZMod 10708457761) ^ 1608842 = (47 : ZMod 10708457761) ^ (804421 + 804421) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 804421 * (47 : ZMod 10708457761) ^ 804421 := by rw [pow_add]
          _ = 1302475191 := by rw [factor_5_19]; decide
      have factor_5_21 : (47 : ZMod 10708457761) ^ 3217685 = 8436970456 := by
        calc
          (47 : ZMod 10708457761) ^ 3217685 = (47 : ZMod 10708457761) ^ (1608842 + 1608842 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 1608842 * (47 : ZMod 10708457761) ^ 1608842) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 8436970456 := by rw [factor_5_20]; decide
      have factor_5_22 : (47 : ZMod 10708457761) ^ 6435371 = 5267550193 := by
        calc
          (47 : ZMod 10708457761) ^ 6435371 = (47 : ZMod 10708457761) ^ (3217685 + 3217685 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 3217685 * (47 : ZMod 10708457761) ^ 3217685) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 5267550193 := by rw [factor_5_21]; decide
      have factor_5_23 : (47 : ZMod 10708457761) ^ 12870742 = 9722997484 := by
        calc
          (47 : ZMod 10708457761) ^ 12870742 = (47 : ZMod 10708457761) ^ (6435371 + 6435371) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 6435371 * (47 : ZMod 10708457761) ^ 6435371 := by rw [pow_add]
          _ = 9722997484 := by rw [factor_5_22]; decide
      have factor_5_24 : (47 : ZMod 10708457761) ^ 25741485 = 10139071764 := by
        calc
          (47 : ZMod 10708457761) ^ 25741485 = (47 : ZMod 10708457761) ^ (12870742 + 12870742 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 12870742 * (47 : ZMod 10708457761) ^ 12870742) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 10139071764 := by rw [factor_5_23]; decide
      have factor_5_25 : (47 : ZMod 10708457761) ^ 51482970 = 2302216356 := by
        calc
          (47 : ZMod 10708457761) ^ 51482970 = (47 : ZMod 10708457761) ^ (25741485 + 25741485) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 25741485 * (47 : ZMod 10708457761) ^ 25741485 := by rw [pow_add]
          _ = 2302216356 := by rw [factor_5_24]; decide
      have factor_5_26 : (47 : ZMod 10708457761) ^ 102965940 = 541169922 := by
        calc
          (47 : ZMod 10708457761) ^ 102965940 = (47 : ZMod 10708457761) ^ (51482970 + 51482970) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 51482970 * (47 : ZMod 10708457761) ^ 51482970 := by rw [pow_add]
          _ = 541169922 := by rw [factor_5_25]; decide
      have factor_5_27 : (47 : ZMod 10708457761) ^ 205931880 = 1347024832 := by
        calc
          (47 : ZMod 10708457761) ^ 205931880 = (47 : ZMod 10708457761) ^ (102965940 + 102965940) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 102965940 * (47 : ZMod 10708457761) ^ 102965940 := by rw [pow_add]
          _ = 1347024832 := by rw [factor_5_26]; decide
      have factor_5_28 : (47 : ZMod 10708457761) ^ 411863760 = 1804607213 := by
        calc
          (47 : ZMod 10708457761) ^ 411863760 = (47 : ZMod 10708457761) ^ (205931880 + 205931880) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 205931880 * (47 : ZMod 10708457761) ^ 205931880 := by rw [pow_add]
          _ = 1804607213 := by rw [factor_5_27]; decide
      have factor_5_29 : (47 : ZMod 10708457761) ^ 823727520 = 10130563944 := by
        calc
          (47 : ZMod 10708457761) ^ 823727520 = (47 : ZMod 10708457761) ^ (411863760 + 411863760) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 411863760 * (47 : ZMod 10708457761) ^ 411863760 := by rw [pow_add]
          _ = 10130563944 := by rw [factor_5_28]; decide
      change (47 : ZMod 10708457761) ^ 823727520 ≠ 1
      rw [factor_5_29]
      decide
    ·
      have factor_6_0 : (47 : ZMod 10708457761) ^ 1 = 47 := by norm_num
      have factor_6_1 : (47 : ZMod 10708457761) ^ 2 = 2209 := by
        calc
          (47 : ZMod 10708457761) ^ 2 = (47 : ZMod 10708457761) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 1 * (47 : ZMod 10708457761) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_6_0]; decide
      have factor_6_2 : (47 : ZMod 10708457761) ^ 4 = 4879681 := by
        calc
          (47 : ZMod 10708457761) ^ 4 = (47 : ZMod 10708457761) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 2 * (47 : ZMod 10708457761) ^ 2 := by rw [pow_add]
          _ = 4879681 := by rw [factor_6_1]; decide
      have factor_6_3 : (47 : ZMod 10708457761) ^ 9 = 260958418 := by
        calc
          (47 : ZMod 10708457761) ^ 9 = (47 : ZMod 10708457761) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 4 * (47 : ZMod 10708457761) ^ 4) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 260958418 := by rw [factor_6_2]; decide
      have factor_6_4 : (47 : ZMod 10708457761) ^ 18 = 4598963651 := by
        calc
          (47 : ZMod 10708457761) ^ 18 = (47 : ZMod 10708457761) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 9 * (47 : ZMod 10708457761) ^ 9 := by rw [pow_add]
          _ = 4598963651 := by rw [factor_6_3]; decide
      have factor_6_5 : (47 : ZMod 10708457761) ^ 37 = 9540440053 := by
        calc
          (47 : ZMod 10708457761) ^ 37 = (47 : ZMod 10708457761) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 18 * (47 : ZMod 10708457761) ^ 18) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 9540440053 := by rw [factor_6_4]; decide
      have factor_6_6 : (47 : ZMod 10708457761) ^ 75 = 9455939046 := by
        calc
          (47 : ZMod 10708457761) ^ 75 = (47 : ZMod 10708457761) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 37 * (47 : ZMod 10708457761) ^ 37) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 9455939046 := by rw [factor_6_5]; decide
      have factor_6_7 : (47 : ZMod 10708457761) ^ 150 = 9233711032 := by
        calc
          (47 : ZMod 10708457761) ^ 150 = (47 : ZMod 10708457761) ^ (75 + 75) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 75 * (47 : ZMod 10708457761) ^ 75 := by rw [pow_add]
          _ = 9233711032 := by rw [factor_6_6]; decide
      have factor_6_8 : (47 : ZMod 10708457761) ^ 300 = 5926697322 := by
        calc
          (47 : ZMod 10708457761) ^ 300 = (47 : ZMod 10708457761) ^ (150 + 150) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 150 * (47 : ZMod 10708457761) ^ 150 := by rw [pow_add]
          _ = 5926697322 := by rw [factor_6_7]; decide
      have factor_6_9 : (47 : ZMod 10708457761) ^ 600 = 3828140305 := by
        calc
          (47 : ZMod 10708457761) ^ 600 = (47 : ZMod 10708457761) ^ (300 + 300) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 300 * (47 : ZMod 10708457761) ^ 300 := by rw [pow_add]
          _ = 3828140305 := by rw [factor_6_8]; decide
      have factor_6_10 : (47 : ZMod 10708457761) ^ 1201 = 9379232345 := by
        calc
          (47 : ZMod 10708457761) ^ 1201 = (47 : ZMod 10708457761) ^ (600 + 600 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 600 * (47 : ZMod 10708457761) ^ 600) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 9379232345 := by rw [factor_6_9]; decide
      have factor_6_11 : (47 : ZMod 10708457761) ^ 2402 = 6576624143 := by
        calc
          (47 : ZMod 10708457761) ^ 2402 = (47 : ZMod 10708457761) ^ (1201 + 1201) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 1201 * (47 : ZMod 10708457761) ^ 1201 := by rw [pow_add]
          _ = 6576624143 := by rw [factor_6_10]; decide
      have factor_6_12 : (47 : ZMod 10708457761) ^ 4805 = 10618780907 := by
        calc
          (47 : ZMod 10708457761) ^ 4805 = (47 : ZMod 10708457761) ^ (2402 + 2402 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 2402 * (47 : ZMod 10708457761) ^ 2402) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 10618780907 := by rw [factor_6_11]; decide
      have factor_6_13 : (47 : ZMod 10708457761) ^ 9611 = 2667259591 := by
        calc
          (47 : ZMod 10708457761) ^ 9611 = (47 : ZMod 10708457761) ^ (4805 + 4805 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 4805 * (47 : ZMod 10708457761) ^ 4805) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 2667259591 := by rw [factor_6_12]; decide
      have factor_6_14 : (47 : ZMod 10708457761) ^ 19223 = 10177925276 := by
        calc
          (47 : ZMod 10708457761) ^ 19223 = (47 : ZMod 10708457761) ^ (9611 + 9611 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 9611 * (47 : ZMod 10708457761) ^ 9611) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 10177925276 := by rw [factor_6_13]; decide
      have factor_6_15 : (47 : ZMod 10708457761) ^ 38446 = 5099885768 := by
        calc
          (47 : ZMod 10708457761) ^ 38446 = (47 : ZMod 10708457761) ^ (19223 + 19223) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 19223 * (47 : ZMod 10708457761) ^ 19223 := by rw [pow_add]
          _ = 5099885768 := by rw [factor_6_14]; decide
      have factor_6_16 : (47 : ZMod 10708457761) ^ 76893 = 8433933339 := by
        calc
          (47 : ZMod 10708457761) ^ 76893 = (47 : ZMod 10708457761) ^ (38446 + 38446 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 38446 * (47 : ZMod 10708457761) ^ 38446) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 8433933339 := by rw [factor_6_15]; decide
      have factor_6_17 : (47 : ZMod 10708457761) ^ 153786 = 3007020343 := by
        calc
          (47 : ZMod 10708457761) ^ 153786 = (47 : ZMod 10708457761) ^ (76893 + 76893) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 76893 * (47 : ZMod 10708457761) ^ 76893 := by rw [pow_add]
          _ = 3007020343 := by rw [factor_6_16]; decide
      have factor_6_18 : (47 : ZMod 10708457761) ^ 307572 = 3829660915 := by
        calc
          (47 : ZMod 10708457761) ^ 307572 = (47 : ZMod 10708457761) ^ (153786 + 153786) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 153786 * (47 : ZMod 10708457761) ^ 153786 := by rw [pow_add]
          _ = 3829660915 := by rw [factor_6_17]; decide
      have factor_6_19 : (47 : ZMod 10708457761) ^ 615145 = 6889589597 := by
        calc
          (47 : ZMod 10708457761) ^ 615145 = (47 : ZMod 10708457761) ^ (307572 + 307572 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 307572 * (47 : ZMod 10708457761) ^ 307572) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 6889589597 := by rw [factor_6_18]; decide
      have factor_6_20 : (47 : ZMod 10708457761) ^ 1230291 = 1234656948 := by
        calc
          (47 : ZMod 10708457761) ^ 1230291 = (47 : ZMod 10708457761) ^ (615145 + 615145 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 615145 * (47 : ZMod 10708457761) ^ 615145) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 1234656948 := by rw [factor_6_19]; decide
      have factor_6_21 : (47 : ZMod 10708457761) ^ 2460583 = 2388107569 := by
        calc
          (47 : ZMod 10708457761) ^ 2460583 = (47 : ZMod 10708457761) ^ (1230291 + 1230291 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 1230291 * (47 : ZMod 10708457761) ^ 1230291) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 2388107569 := by rw [factor_6_20]; decide
      have factor_6_22 : (47 : ZMod 10708457761) ^ 4921166 = 1665436120 := by
        calc
          (47 : ZMod 10708457761) ^ 4921166 = (47 : ZMod 10708457761) ^ (2460583 + 2460583) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 2460583 * (47 : ZMod 10708457761) ^ 2460583 := by rw [pow_add]
          _ = 1665436120 := by rw [factor_6_21]; decide
      have factor_6_23 : (47 : ZMod 10708457761) ^ 9842332 = 4279893906 := by
        calc
          (47 : ZMod 10708457761) ^ 9842332 = (47 : ZMod 10708457761) ^ (4921166 + 4921166) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 4921166 * (47 : ZMod 10708457761) ^ 4921166 := by rw [pow_add]
          _ = 4279893906 := by rw [factor_6_22]; decide
      have factor_6_24 : (47 : ZMod 10708457761) ^ 19684665 = 4740288235 := by
        calc
          (47 : ZMod 10708457761) ^ 19684665 = (47 : ZMod 10708457761) ^ (9842332 + 9842332 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 9842332 * (47 : ZMod 10708457761) ^ 9842332) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 4740288235 := by rw [factor_6_23]; decide
      have factor_6_25 : (47 : ZMod 10708457761) ^ 39369330 = 6669028234 := by
        calc
          (47 : ZMod 10708457761) ^ 39369330 = (47 : ZMod 10708457761) ^ (19684665 + 19684665) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 19684665 * (47 : ZMod 10708457761) ^ 19684665 := by rw [pow_add]
          _ = 6669028234 := by rw [factor_6_24]; decide
      have factor_6_26 : (47 : ZMod 10708457761) ^ 78738660 = 10651913188 := by
        calc
          (47 : ZMod 10708457761) ^ 78738660 = (47 : ZMod 10708457761) ^ (39369330 + 39369330) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 39369330 * (47 : ZMod 10708457761) ^ 39369330 := by rw [pow_add]
          _ = 10651913188 := by rw [factor_6_25]; decide
      have factor_6_27 : (47 : ZMod 10708457761) ^ 157477320 = 251303993 := by
        calc
          (47 : ZMod 10708457761) ^ 157477320 = (47 : ZMod 10708457761) ^ (78738660 + 78738660) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 78738660 * (47 : ZMod 10708457761) ^ 78738660 := by rw [pow_add]
          _ = 251303993 := by rw [factor_6_26]; decide
      have factor_6_28 : (47 : ZMod 10708457761) ^ 314954640 = 10412442977 := by
        calc
          (47 : ZMod 10708457761) ^ 314954640 = (47 : ZMod 10708457761) ^ (157477320 + 157477320) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 157477320 * (47 : ZMod 10708457761) ^ 157477320 := by rw [pow_add]
          _ = 10412442977 := by rw [factor_6_27]; decide
      have factor_6_29 : (47 : ZMod 10708457761) ^ 629909280 = 1809708535 := by
        calc
          (47 : ZMod 10708457761) ^ 629909280 = (47 : ZMod 10708457761) ^ (314954640 + 314954640) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 314954640 * (47 : ZMod 10708457761) ^ 314954640 := by rw [pow_add]
          _ = 1809708535 := by rw [factor_6_28]; decide
      change (47 : ZMod 10708457761) ^ 629909280 ≠ 1
      rw [factor_6_29]
      decide
    ·
      have factor_7_0 : (47 : ZMod 10708457761) ^ 1 = 47 := by norm_num
      have factor_7_1 : (47 : ZMod 10708457761) ^ 2 = 2209 := by
        calc
          (47 : ZMod 10708457761) ^ 2 = (47 : ZMod 10708457761) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 1 * (47 : ZMod 10708457761) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_7_0]; decide
      have factor_7_2 : (47 : ZMod 10708457761) ^ 4 = 4879681 := by
        calc
          (47 : ZMod 10708457761) ^ 4 = (47 : ZMod 10708457761) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 2 * (47 : ZMod 10708457761) ^ 2 := by rw [pow_add]
          _ = 4879681 := by rw [factor_7_1]; decide
      have factor_7_3 : (47 : ZMod 10708457761) ^ 8 = 6385059058 := by
        calc
          (47 : ZMod 10708457761) ^ 8 = (47 : ZMod 10708457761) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 4 * (47 : ZMod 10708457761) ^ 4 := by rw [pow_add]
          _ = 6385059058 := by rw [factor_7_2]; decide
      have factor_7_4 : (47 : ZMod 10708457761) ^ 16 = 8587269198 := by
        calc
          (47 : ZMod 10708457761) ^ 16 = (47 : ZMod 10708457761) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 8 * (47 : ZMod 10708457761) ^ 8 := by rw [pow_add]
          _ = 8587269198 := by rw [factor_7_3]; decide
      have factor_7_5 : (47 : ZMod 10708457761) ^ 33 = 6828009552 := by
        calc
          (47 : ZMod 10708457761) ^ 33 = (47 : ZMod 10708457761) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 16 * (47 : ZMod 10708457761) ^ 16) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 6828009552 := by rw [factor_7_4]; decide
      have factor_7_6 : (47 : ZMod 10708457761) ^ 67 = 3805714805 := by
        calc
          (47 : ZMod 10708457761) ^ 67 = (47 : ZMod 10708457761) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 33 * (47 : ZMod 10708457761) ^ 33) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 3805714805 := by rw [factor_7_5]; decide
      have factor_7_7 : (47 : ZMod 10708457761) ^ 134 = 1911067206 := by
        calc
          (47 : ZMod 10708457761) ^ 134 = (47 : ZMod 10708457761) ^ (67 + 67) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 67 * (47 : ZMod 10708457761) ^ 67 := by rw [pow_add]
          _ = 1911067206 := by rw [factor_7_6]; decide
      have factor_7_8 : (47 : ZMod 10708457761) ^ 268 = 6781714508 := by
        calc
          (47 : ZMod 10708457761) ^ 268 = (47 : ZMod 10708457761) ^ (134 + 134) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 134 * (47 : ZMod 10708457761) ^ 134 := by rw [pow_add]
          _ = 6781714508 := by rw [factor_7_7]; decide
      have factor_7_9 : (47 : ZMod 10708457761) ^ 537 = 10521005822 := by
        calc
          (47 : ZMod 10708457761) ^ 537 = (47 : ZMod 10708457761) ^ (268 + 268 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 268 * (47 : ZMod 10708457761) ^ 268) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 10521005822 := by rw [factor_7_8]; decide
      have factor_7_10 : (47 : ZMod 10708457761) ^ 1074 = 10143886849 := by
        calc
          (47 : ZMod 10708457761) ^ 1074 = (47 : ZMod 10708457761) ^ (537 + 537) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 537 * (47 : ZMod 10708457761) ^ 537 := by rw [pow_add]
          _ = 10143886849 := by rw [factor_7_9]; decide
      have factor_7_11 : (47 : ZMod 10708457761) ^ 2149 = 9121798537 := by
        calc
          (47 : ZMod 10708457761) ^ 2149 = (47 : ZMod 10708457761) ^ (1074 + 1074 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 1074 * (47 : ZMod 10708457761) ^ 1074) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 9121798537 := by rw [factor_7_10]; decide
      have factor_7_12 : (47 : ZMod 10708457761) ^ 4299 = 7789019333 := by
        calc
          (47 : ZMod 10708457761) ^ 4299 = (47 : ZMod 10708457761) ^ (2149 + 2149 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 2149 * (47 : ZMod 10708457761) ^ 2149) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 7789019333 := by rw [factor_7_11]; decide
      have factor_7_13 : (47 : ZMod 10708457761) ^ 8599 = 5936835193 := by
        calc
          (47 : ZMod 10708457761) ^ 8599 = (47 : ZMod 10708457761) ^ (4299 + 4299 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 4299 * (47 : ZMod 10708457761) ^ 4299) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 5936835193 := by rw [factor_7_12]; decide
      have factor_7_14 : (47 : ZMod 10708457761) ^ 17199 = 8458437159 := by
        calc
          (47 : ZMod 10708457761) ^ 17199 = (47 : ZMod 10708457761) ^ (8599 + 8599 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 8599 * (47 : ZMod 10708457761) ^ 8599) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 8458437159 := by rw [factor_7_13]; decide
      have factor_7_15 : (47 : ZMod 10708457761) ^ 34399 = 6764956869 := by
        calc
          (47 : ZMod 10708457761) ^ 34399 = (47 : ZMod 10708457761) ^ (17199 + 17199 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 17199 * (47 : ZMod 10708457761) ^ 17199) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 6764956869 := by rw [factor_7_14]; decide
      have factor_7_16 : (47 : ZMod 10708457761) ^ 68799 = 8558747946 := by
        calc
          (47 : ZMod 10708457761) ^ 68799 = (47 : ZMod 10708457761) ^ (34399 + 34399 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 34399 * (47 : ZMod 10708457761) ^ 34399) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 8558747946 := by rw [factor_7_15]; decide
      have factor_7_17 : (47 : ZMod 10708457761) ^ 137598 = 4954669166 := by
        calc
          (47 : ZMod 10708457761) ^ 137598 = (47 : ZMod 10708457761) ^ (68799 + 68799) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 68799 * (47 : ZMod 10708457761) ^ 68799 := by rw [pow_add]
          _ = 4954669166 := by rw [factor_7_16]; decide
      have factor_7_18 : (47 : ZMod 10708457761) ^ 275196 = 10025428885 := by
        calc
          (47 : ZMod 10708457761) ^ 275196 = (47 : ZMod 10708457761) ^ (137598 + 137598) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 137598 * (47 : ZMod 10708457761) ^ 137598 := by rw [pow_add]
          _ = 10025428885 := by rw [factor_7_17]; decide
      have factor_7_19 : (47 : ZMod 10708457761) ^ 550393 = 782850185 := by
        calc
          (47 : ZMod 10708457761) ^ 550393 = (47 : ZMod 10708457761) ^ (275196 + 275196 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 275196 * (47 : ZMod 10708457761) ^ 275196) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 782850185 := by rw [factor_7_18]; decide
      have factor_7_20 : (47 : ZMod 10708457761) ^ 1100787 = 1653122230 := by
        calc
          (47 : ZMod 10708457761) ^ 1100787 = (47 : ZMod 10708457761) ^ (550393 + 550393 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 550393 * (47 : ZMod 10708457761) ^ 550393) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 1653122230 := by rw [factor_7_19]; decide
      have factor_7_21 : (47 : ZMod 10708457761) ^ 2201574 = 5417382569 := by
        calc
          (47 : ZMod 10708457761) ^ 2201574 = (47 : ZMod 10708457761) ^ (1100787 + 1100787) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 1100787 * (47 : ZMod 10708457761) ^ 1100787 := by rw [pow_add]
          _ = 5417382569 := by rw [factor_7_20]; decide
      have factor_7_22 : (47 : ZMod 10708457761) ^ 4403148 = 9892498381 := by
        calc
          (47 : ZMod 10708457761) ^ 4403148 = (47 : ZMod 10708457761) ^ (2201574 + 2201574) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 2201574 * (47 : ZMod 10708457761) ^ 2201574 := by rw [pow_add]
          _ = 9892498381 := by rw [factor_7_21]; decide
      have factor_7_23 : (47 : ZMod 10708457761) ^ 8806297 = 1989142492 := by
        calc
          (47 : ZMod 10708457761) ^ 8806297 = (47 : ZMod 10708457761) ^ (4403148 + 4403148 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 4403148 * (47 : ZMod 10708457761) ^ 4403148) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 1989142492 := by rw [factor_7_22]; decide
      have factor_7_24 : (47 : ZMod 10708457761) ^ 17612595 = 10072571806 := by
        calc
          (47 : ZMod 10708457761) ^ 17612595 = (47 : ZMod 10708457761) ^ (8806297 + 8806297 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 8806297 * (47 : ZMod 10708457761) ^ 8806297) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 10072571806 := by rw [factor_7_23]; decide
      have factor_7_25 : (47 : ZMod 10708457761) ^ 35225190 = 340754704 := by
        calc
          (47 : ZMod 10708457761) ^ 35225190 = (47 : ZMod 10708457761) ^ (17612595 + 17612595) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 17612595 * (47 : ZMod 10708457761) ^ 17612595 := by rw [pow_add]
          _ = 340754704 := by rw [factor_7_24]; decide
      have factor_7_26 : (47 : ZMod 10708457761) ^ 70450380 = 1147834353 := by
        calc
          (47 : ZMod 10708457761) ^ 70450380 = (47 : ZMod 10708457761) ^ (35225190 + 35225190) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 35225190 * (47 : ZMod 10708457761) ^ 35225190 := by rw [pow_add]
          _ = 1147834353 := by rw [factor_7_25]; decide
      have factor_7_27 : (47 : ZMod 10708457761) ^ 140900760 = 2410711526 := by
        calc
          (47 : ZMod 10708457761) ^ 140900760 = (47 : ZMod 10708457761) ^ (70450380 + 70450380) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 70450380 * (47 : ZMod 10708457761) ^ 70450380 := by rw [pow_add]
          _ = 2410711526 := by rw [factor_7_26]; decide
      have factor_7_28 : (47 : ZMod 10708457761) ^ 281801520 = 4779889284 := by
        calc
          (47 : ZMod 10708457761) ^ 281801520 = (47 : ZMod 10708457761) ^ (140900760 + 140900760) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 140900760 * (47 : ZMod 10708457761) ^ 140900760 := by rw [pow_add]
          _ = 4779889284 := by rw [factor_7_27]; decide
      have factor_7_29 : (47 : ZMod 10708457761) ^ 563603040 = 2280215166 := by
        calc
          (47 : ZMod 10708457761) ^ 563603040 = (47 : ZMod 10708457761) ^ (281801520 + 281801520) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 281801520 * (47 : ZMod 10708457761) ^ 281801520 := by rw [pow_add]
          _ = 2280215166 := by rw [factor_7_28]; decide
      change (47 : ZMod 10708457761) ^ 563603040 ≠ 1
      rw [factor_7_29]
      decide
    ·
      have factor_8_0 : (47 : ZMod 10708457761) ^ 1 = 47 := by norm_num
      have factor_8_1 : (47 : ZMod 10708457761) ^ 3 = 103823 := by
        calc
          (47 : ZMod 10708457761) ^ 3 = (47 : ZMod 10708457761) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 1 * (47 : ZMod 10708457761) ^ 1) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_8_0]; decide
      have factor_8_2 : (47 : ZMod 10708457761) ^ 6 = 70757568 := by
        calc
          (47 : ZMod 10708457761) ^ 6 = (47 : ZMod 10708457761) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 3 * (47 : ZMod 10708457761) ^ 3 := by rw [pow_add]
          _ = 70757568 := by rw [factor_8_1]; decide
      have factor_8_3 : (47 : ZMod 10708457761) ^ 13 = 8287913104 := by
        calc
          (47 : ZMod 10708457761) ^ 13 = (47 : ZMod 10708457761) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 6 * (47 : ZMod 10708457761) ^ 6) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 8287913104 := by rw [factor_8_2]; decide
      have factor_8_4 : (47 : ZMod 10708457761) ^ 27 = 7923032331 := by
        calc
          (47 : ZMod 10708457761) ^ 27 = (47 : ZMod 10708457761) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 13 * (47 : ZMod 10708457761) ^ 13) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 7923032331 := by rw [factor_8_3]; decide
      have factor_8_5 : (47 : ZMod 10708457761) ^ 55 = 5020109068 := by
        calc
          (47 : ZMod 10708457761) ^ 55 = (47 : ZMod 10708457761) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 27 * (47 : ZMod 10708457761) ^ 27) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 5020109068 := by rw [factor_8_4]; decide
      have factor_8_6 : (47 : ZMod 10708457761) ^ 111 = 7378655090 := by
        calc
          (47 : ZMod 10708457761) ^ 111 = (47 : ZMod 10708457761) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 55 * (47 : ZMod 10708457761) ^ 55) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 7378655090 := by rw [factor_8_5]; decide
      have factor_8_7 : (47 : ZMod 10708457761) ^ 222 = 2827268257 := by
        calc
          (47 : ZMod 10708457761) ^ 222 = (47 : ZMod 10708457761) ^ (111 + 111) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 111 * (47 : ZMod 10708457761) ^ 111 := by rw [pow_add]
          _ = 2827268257 := by rw [factor_8_6]; decide
      have factor_8_8 : (47 : ZMod 10708457761) ^ 444 = 8142814357 := by
        calc
          (47 : ZMod 10708457761) ^ 444 = (47 : ZMod 10708457761) ^ (222 + 222) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 222 * (47 : ZMod 10708457761) ^ 222 := by rw [pow_add]
          _ = 8142814357 := by rw [factor_8_7]; decide
      have factor_8_9 : (47 : ZMod 10708457761) ^ 888 = 7412780873 := by
        calc
          (47 : ZMod 10708457761) ^ 888 = (47 : ZMod 10708457761) ^ (444 + 444) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 444 * (47 : ZMod 10708457761) ^ 444 := by rw [pow_add]
          _ = 7412780873 := by rw [factor_8_8]; decide
      have factor_8_10 : (47 : ZMod 10708457761) ^ 1776 = 8723499402 := by
        calc
          (47 : ZMod 10708457761) ^ 1776 = (47 : ZMod 10708457761) ^ (888 + 888) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 888 * (47 : ZMod 10708457761) ^ 888 := by rw [pow_add]
          _ = 8723499402 := by rw [factor_8_9]; decide
      have factor_8_11 : (47 : ZMod 10708457761) ^ 3552 = 7792625680 := by
        calc
          (47 : ZMod 10708457761) ^ 3552 = (47 : ZMod 10708457761) ^ (1776 + 1776) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 1776 * (47 : ZMod 10708457761) ^ 1776 := by rw [pow_add]
          _ = 7792625680 := by rw [factor_8_10]; decide
      have factor_8_12 : (47 : ZMod 10708457761) ^ 7104 = 9286174253 := by
        calc
          (47 : ZMod 10708457761) ^ 7104 = (47 : ZMod 10708457761) ^ (3552 + 3552) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 3552 * (47 : ZMod 10708457761) ^ 3552 := by rw [pow_add]
          _ = 9286174253 := by rw [factor_8_11]; decide
      have factor_8_13 : (47 : ZMod 10708457761) ^ 14208 = 8055695409 := by
        calc
          (47 : ZMod 10708457761) ^ 14208 = (47 : ZMod 10708457761) ^ (7104 + 7104) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 7104 * (47 : ZMod 10708457761) ^ 7104 := by rw [pow_add]
          _ = 8055695409 := by rw [factor_8_12]; decide
      have factor_8_14 : (47 : ZMod 10708457761) ^ 28417 = 3682463434 := by
        calc
          (47 : ZMod 10708457761) ^ 28417 = (47 : ZMod 10708457761) ^ (14208 + 14208 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 14208 * (47 : ZMod 10708457761) ^ 14208) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 3682463434 := by rw [factor_8_13]; decide
      have factor_8_15 : (47 : ZMod 10708457761) ^ 56834 = 10440594387 := by
        calc
          (47 : ZMod 10708457761) ^ 56834 = (47 : ZMod 10708457761) ^ (28417 + 28417) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 28417 * (47 : ZMod 10708457761) ^ 28417 := by rw [pow_add]
          _ = 10440594387 := by rw [factor_8_14]; decide
      have factor_8_16 : (47 : ZMod 10708457761) ^ 113668 = 8084183652 := by
        calc
          (47 : ZMod 10708457761) ^ 113668 = (47 : ZMod 10708457761) ^ (56834 + 56834) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 56834 * (47 : ZMod 10708457761) ^ 56834 := by rw [pow_add]
          _ = 8084183652 := by rw [factor_8_15]; decide
      have factor_8_17 : (47 : ZMod 10708457761) ^ 227336 = 3431872379 := by
        calc
          (47 : ZMod 10708457761) ^ 227336 = (47 : ZMod 10708457761) ^ (113668 + 113668) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 113668 * (47 : ZMod 10708457761) ^ 113668 := by rw [pow_add]
          _ = 3431872379 := by rw [factor_8_16]; decide
      have factor_8_18 : (47 : ZMod 10708457761) ^ 454672 = 9925940262 := by
        calc
          (47 : ZMod 10708457761) ^ 454672 = (47 : ZMod 10708457761) ^ (227336 + 227336) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 227336 * (47 : ZMod 10708457761) ^ 227336 := by rw [pow_add]
          _ = 9925940262 := by rw [factor_8_17]; decide
      have factor_8_19 : (47 : ZMod 10708457761) ^ 909345 = 5549845056 := by
        calc
          (47 : ZMod 10708457761) ^ 909345 = (47 : ZMod 10708457761) ^ (454672 + 454672 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 454672 * (47 : ZMod 10708457761) ^ 454672) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 5549845056 := by rw [factor_8_18]; decide
      have factor_8_20 : (47 : ZMod 10708457761) ^ 1818691 = 10664571399 := by
        calc
          (47 : ZMod 10708457761) ^ 1818691 = (47 : ZMod 10708457761) ^ (909345 + 909345 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 909345 * (47 : ZMod 10708457761) ^ 909345) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 10664571399 := by rw [factor_8_19]; decide
      have factor_8_21 : (47 : ZMod 10708457761) ^ 3637383 = 1754031454 := by
        calc
          (47 : ZMod 10708457761) ^ 3637383 = (47 : ZMod 10708457761) ^ (1818691 + 1818691 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 1818691 * (47 : ZMod 10708457761) ^ 1818691) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 1754031454 := by rw [factor_8_20]; decide
      have factor_8_22 : (47 : ZMod 10708457761) ^ 7274767 = 2945147800 := by
        calc
          (47 : ZMod 10708457761) ^ 7274767 = (47 : ZMod 10708457761) ^ (3637383 + 3637383 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 3637383 * (47 : ZMod 10708457761) ^ 3637383) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 2945147800 := by rw [factor_8_21]; decide
      have factor_8_23 : (47 : ZMod 10708457761) ^ 14549535 = 6233710670 := by
        calc
          (47 : ZMod 10708457761) ^ 14549535 = (47 : ZMod 10708457761) ^ (7274767 + 7274767 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = ((47 : ZMod 10708457761) ^ 7274767 * (47 : ZMod 10708457761) ^ 7274767) * (47 : ZMod 10708457761) := by rw [pow_succ, pow_add]
          _ = 6233710670 := by rw [factor_8_22]; decide
      have factor_8_24 : (47 : ZMod 10708457761) ^ 29099070 = 2326807867 := by
        calc
          (47 : ZMod 10708457761) ^ 29099070 = (47 : ZMod 10708457761) ^ (14549535 + 14549535) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 14549535 * (47 : ZMod 10708457761) ^ 14549535 := by rw [pow_add]
          _ = 2326807867 := by rw [factor_8_23]; decide
      have factor_8_25 : (47 : ZMod 10708457761) ^ 58198140 = 3846863481 := by
        calc
          (47 : ZMod 10708457761) ^ 58198140 = (47 : ZMod 10708457761) ^ (29099070 + 29099070) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 29099070 * (47 : ZMod 10708457761) ^ 29099070 := by rw [pow_add]
          _ = 3846863481 := by rw [factor_8_24]; decide
      have factor_8_26 : (47 : ZMod 10708457761) ^ 116396280 = 606546970 := by
        calc
          (47 : ZMod 10708457761) ^ 116396280 = (47 : ZMod 10708457761) ^ (58198140 + 58198140) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 58198140 * (47 : ZMod 10708457761) ^ 58198140 := by rw [pow_add]
          _ = 606546970 := by rw [factor_8_25]; decide
      have factor_8_27 : (47 : ZMod 10708457761) ^ 232792560 = 8819068472 := by
        calc
          (47 : ZMod 10708457761) ^ 232792560 = (47 : ZMod 10708457761) ^ (116396280 + 116396280) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 116396280 * (47 : ZMod 10708457761) ^ 116396280 := by rw [pow_add]
          _ = 8819068472 := by rw [factor_8_26]; decide
      have factor_8_28 : (47 : ZMod 10708457761) ^ 465585120 = 6568930816 := by
        calc
          (47 : ZMod 10708457761) ^ 465585120 = (47 : ZMod 10708457761) ^ (232792560 + 232792560) :=
            congrArg (fun n : ℕ => (47 : ZMod 10708457761) ^ n) (by norm_num)
          _ = (47 : ZMod 10708457761) ^ 232792560 * (47 : ZMod 10708457761) ^ 232792560 := by rw [pow_add]
          _ = 6568930816 := by rw [factor_8_27]; decide
      change (47 : ZMod 10708457761) ^ 465585120 ≠ 1
      rw [factor_8_28]
      decide

#print axioms prime_lucas_10708457761

end TotientTailPeriodKiller
end Erdos249257
