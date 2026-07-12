import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=23 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_10708457791 : Nat.Prime 10708457791 := by
  apply lucas_primality 10708457791 (11 : ZMod 10708457791)
  ·
      have fermat_0 : (11 : ZMod 10708457791) ^ 1 = 11 := by norm_num
      have fermat_1 : (11 : ZMod 10708457791) ^ 2 = 121 := by
        calc
          (11 : ZMod 10708457791) ^ 2 = (11 : ZMod 10708457791) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 1 * (11 : ZMod 10708457791) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [fermat_0]; decide
      have fermat_2 : (11 : ZMod 10708457791) ^ 4 = 14641 := by
        calc
          (11 : ZMod 10708457791) ^ 4 = (11 : ZMod 10708457791) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 2 * (11 : ZMod 10708457791) ^ 2 := by rw [pow_add]
          _ = 14641 := by rw [fermat_1]; decide
      have fermat_3 : (11 : ZMod 10708457791) ^ 9 = 2357947691 := by
        calc
          (11 : ZMod 10708457791) ^ 9 = (11 : ZMod 10708457791) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 4 * (11 : ZMod 10708457791) ^ 4) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 2357947691 := by rw [fermat_2]; decide
      have fermat_4 : (11 : ZMod 10708457791) ^ 19 = 6040355621 := by
        calc
          (11 : ZMod 10708457791) ^ 19 = (11 : ZMod 10708457791) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 9 * (11 : ZMod 10708457791) ^ 9) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 6040355621 := by rw [fermat_3]; decide
      have fermat_5 : (11 : ZMod 10708457791) ^ 39 = 7638496097 := by
        calc
          (11 : ZMod 10708457791) ^ 39 = (11 : ZMod 10708457791) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 19 * (11 : ZMod 10708457791) ^ 19) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 7638496097 := by rw [fermat_4]; decide
      have fermat_6 : (11 : ZMod 10708457791) ^ 79 = 5883173722 := by
        calc
          (11 : ZMod 10708457791) ^ 79 = (11 : ZMod 10708457791) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 39 * (11 : ZMod 10708457791) ^ 39) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 5883173722 := by rw [fermat_5]; decide
      have fermat_7 : (11 : ZMod 10708457791) ^ 159 = 5044949520 := by
        calc
          (11 : ZMod 10708457791) ^ 159 = (11 : ZMod 10708457791) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 79 * (11 : ZMod 10708457791) ^ 79) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 5044949520 := by rw [fermat_6]; decide
      have fermat_8 : (11 : ZMod 10708457791) ^ 319 = 4574813851 := by
        calc
          (11 : ZMod 10708457791) ^ 319 = (11 : ZMod 10708457791) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 159 * (11 : ZMod 10708457791) ^ 159) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 4574813851 := by rw [fermat_7]; decide
      have fermat_9 : (11 : ZMod 10708457791) ^ 638 = 2154802908 := by
        calc
          (11 : ZMod 10708457791) ^ 638 = (11 : ZMod 10708457791) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 319 * (11 : ZMod 10708457791) ^ 319 := by rw [pow_add]
          _ = 2154802908 := by rw [fermat_8]; decide
      have fermat_10 : (11 : ZMod 10708457791) ^ 1276 = 10617395400 := by
        calc
          (11 : ZMod 10708457791) ^ 1276 = (11 : ZMod 10708457791) ^ (638 + 638) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 638 * (11 : ZMod 10708457791) ^ 638 := by rw [pow_add]
          _ = 10617395400 := by rw [fermat_9]; decide
      have fermat_11 : (11 : ZMod 10708457791) ^ 2553 = 10413874980 := by
        calc
          (11 : ZMod 10708457791) ^ 2553 = (11 : ZMod 10708457791) ^ (1276 + 1276 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 1276 * (11 : ZMod 10708457791) ^ 1276) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 10413874980 := by rw [fermat_10]; decide
      have fermat_12 : (11 : ZMod 10708457791) ^ 5106 = 3625280577 := by
        calc
          (11 : ZMod 10708457791) ^ 5106 = (11 : ZMod 10708457791) ^ (2553 + 2553) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 2553 * (11 : ZMod 10708457791) ^ 2553 := by rw [pow_add]
          _ = 3625280577 := by rw [fermat_11]; decide
      have fermat_13 : (11 : ZMod 10708457791) ^ 10212 = 3489837576 := by
        calc
          (11 : ZMod 10708457791) ^ 10212 = (11 : ZMod 10708457791) ^ (5106 + 5106) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 5106 * (11 : ZMod 10708457791) ^ 5106 := by rw [pow_add]
          _ = 3489837576 := by rw [fermat_12]; decide
      have fermat_14 : (11 : ZMod 10708457791) ^ 20424 = 4566438380 := by
        calc
          (11 : ZMod 10708457791) ^ 20424 = (11 : ZMod 10708457791) ^ (10212 + 10212) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 10212 * (11 : ZMod 10708457791) ^ 10212 := by rw [pow_add]
          _ = 4566438380 := by rw [fermat_13]; decide
      have fermat_15 : (11 : ZMod 10708457791) ^ 40849 = 407779398 := by
        calc
          (11 : ZMod 10708457791) ^ 40849 = (11 : ZMod 10708457791) ^ (20424 + 20424 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 20424 * (11 : ZMod 10708457791) ^ 20424) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 407779398 := by rw [fermat_14]; decide
      have fermat_16 : (11 : ZMod 10708457791) ^ 81699 = 4128642945 := by
        calc
          (11 : ZMod 10708457791) ^ 81699 = (11 : ZMod 10708457791) ^ (40849 + 40849 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 40849 * (11 : ZMod 10708457791) ^ 40849) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 4128642945 := by rw [fermat_15]; decide
      have fermat_17 : (11 : ZMod 10708457791) ^ 163398 = 6814550748 := by
        calc
          (11 : ZMod 10708457791) ^ 163398 = (11 : ZMod 10708457791) ^ (81699 + 81699) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 81699 * (11 : ZMod 10708457791) ^ 81699 := by rw [pow_add]
          _ = 6814550748 := by rw [fermat_16]; decide
      have fermat_18 : (11 : ZMod 10708457791) ^ 326796 = 8855032833 := by
        calc
          (11 : ZMod 10708457791) ^ 326796 = (11 : ZMod 10708457791) ^ (163398 + 163398) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 163398 * (11 : ZMod 10708457791) ^ 163398 := by rw [pow_add]
          _ = 8855032833 := by rw [fermat_17]; decide
      have fermat_19 : (11 : ZMod 10708457791) ^ 653592 = 6329443003 := by
        calc
          (11 : ZMod 10708457791) ^ 653592 = (11 : ZMod 10708457791) ^ (326796 + 326796) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 326796 * (11 : ZMod 10708457791) ^ 326796 := by rw [pow_add]
          _ = 6329443003 := by rw [fermat_18]; decide
      have fermat_20 : (11 : ZMod 10708457791) ^ 1307184 = 6441662524 := by
        calc
          (11 : ZMod 10708457791) ^ 1307184 = (11 : ZMod 10708457791) ^ (653592 + 653592) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 653592 * (11 : ZMod 10708457791) ^ 653592 := by rw [pow_add]
          _ = 6441662524 := by rw [fermat_19]; decide
      have fermat_21 : (11 : ZMod 10708457791) ^ 2614369 = 4758898744 := by
        calc
          (11 : ZMod 10708457791) ^ 2614369 = (11 : ZMod 10708457791) ^ (1307184 + 1307184 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 1307184 * (11 : ZMod 10708457791) ^ 1307184) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 4758898744 := by rw [fermat_20]; decide
      have fermat_22 : (11 : ZMod 10708457791) ^ 5228739 = 9966495512 := by
        calc
          (11 : ZMod 10708457791) ^ 5228739 = (11 : ZMod 10708457791) ^ (2614369 + 2614369 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 2614369 * (11 : ZMod 10708457791) ^ 2614369) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 9966495512 := by rw [fermat_21]; decide
      have fermat_23 : (11 : ZMod 10708457791) ^ 10457478 = 917198649 := by
        calc
          (11 : ZMod 10708457791) ^ 10457478 = (11 : ZMod 10708457791) ^ (5228739 + 5228739) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 5228739 * (11 : ZMod 10708457791) ^ 5228739 := by rw [pow_add]
          _ = 917198649 := by rw [fermat_22]; decide
      have fermat_24 : (11 : ZMod 10708457791) ^ 20914956 = 1702309009 := by
        calc
          (11 : ZMod 10708457791) ^ 20914956 = (11 : ZMod 10708457791) ^ (10457478 + 10457478) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 10457478 * (11 : ZMod 10708457791) ^ 10457478 := by rw [pow_add]
          _ = 1702309009 := by rw [fermat_23]; decide
      have fermat_25 : (11 : ZMod 10708457791) ^ 41829913 = 7953009128 := by
        calc
          (11 : ZMod 10708457791) ^ 41829913 = (11 : ZMod 10708457791) ^ (20914956 + 20914956 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 20914956 * (11 : ZMod 10708457791) ^ 20914956) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 7953009128 := by rw [fermat_24]; decide
      have fermat_26 : (11 : ZMod 10708457791) ^ 83659826 = 9151279692 := by
        calc
          (11 : ZMod 10708457791) ^ 83659826 = (11 : ZMod 10708457791) ^ (41829913 + 41829913) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 41829913 * (11 : ZMod 10708457791) ^ 41829913 := by rw [pow_add]
          _ = 9151279692 := by rw [fermat_25]; decide
      have fermat_27 : (11 : ZMod 10708457791) ^ 167319652 = 3455140167 := by
        calc
          (11 : ZMod 10708457791) ^ 167319652 = (11 : ZMod 10708457791) ^ (83659826 + 83659826) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 83659826 * (11 : ZMod 10708457791) ^ 83659826 := by rw [pow_add]
          _ = 3455140167 := by rw [fermat_26]; decide
      have fermat_28 : (11 : ZMod 10708457791) ^ 334639305 = 7956809215 := by
        calc
          (11 : ZMod 10708457791) ^ 334639305 = (11 : ZMod 10708457791) ^ (167319652 + 167319652 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 167319652 * (11 : ZMod 10708457791) ^ 167319652) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 7956809215 := by rw [fermat_27]; decide
      have fermat_29 : (11 : ZMod 10708457791) ^ 669278611 = 3189588507 := by
        calc
          (11 : ZMod 10708457791) ^ 669278611 = (11 : ZMod 10708457791) ^ (334639305 + 334639305 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 334639305 * (11 : ZMod 10708457791) ^ 334639305) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 3189588507 := by rw [fermat_28]; decide
      have fermat_30 : (11 : ZMod 10708457791) ^ 1338557223 = 1656470819 := by
        calc
          (11 : ZMod 10708457791) ^ 1338557223 = (11 : ZMod 10708457791) ^ (669278611 + 669278611 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 669278611 * (11 : ZMod 10708457791) ^ 669278611) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 1656470819 := by rw [fermat_29]; decide
      have fermat_31 : (11 : ZMod 10708457791) ^ 2677114447 = 3645425801 := by
        calc
          (11 : ZMod 10708457791) ^ 2677114447 = (11 : ZMod 10708457791) ^ (1338557223 + 1338557223 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 1338557223 * (11 : ZMod 10708457791) ^ 1338557223) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 3645425801 := by rw [fermat_30]; decide
      have fermat_32 : (11 : ZMod 10708457791) ^ 5354228895 = 10708457790 := by
        calc
          (11 : ZMod 10708457791) ^ 5354228895 = (11 : ZMod 10708457791) ^ (2677114447 + 2677114447 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 2677114447 * (11 : ZMod 10708457791) ^ 2677114447) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 10708457790 := by rw [fermat_31]; decide
      have fermat_33 : (11 : ZMod 10708457791) ^ 10708457790 = 1 := by
        calc
          (11 : ZMod 10708457791) ^ 10708457790 = (11 : ZMod 10708457791) ^ (5354228895 + 5354228895) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 5354228895 * (11 : ZMod 10708457791) ^ 5354228895 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (307, 1), (661, 1), (1759, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (307, 1), (661, 1), (1759, 1)] : List FactorBlock).map factorBlockValue).prod = 10708457791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (11 : ZMod 10708457791) ^ 1 = 11 := by norm_num
      have factor_0_1 : (11 : ZMod 10708457791) ^ 2 = 121 := by
        calc
          (11 : ZMod 10708457791) ^ 2 = (11 : ZMod 10708457791) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 1 * (11 : ZMod 10708457791) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_0_0]; decide
      have factor_0_2 : (11 : ZMod 10708457791) ^ 4 = 14641 := by
        calc
          (11 : ZMod 10708457791) ^ 4 = (11 : ZMod 10708457791) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 2 * (11 : ZMod 10708457791) ^ 2 := by rw [pow_add]
          _ = 14641 := by rw [factor_0_1]; decide
      have factor_0_3 : (11 : ZMod 10708457791) ^ 9 = 2357947691 := by
        calc
          (11 : ZMod 10708457791) ^ 9 = (11 : ZMod 10708457791) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 4 * (11 : ZMod 10708457791) ^ 4) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 2357947691 := by rw [factor_0_2]; decide
      have factor_0_4 : (11 : ZMod 10708457791) ^ 19 = 6040355621 := by
        calc
          (11 : ZMod 10708457791) ^ 19 = (11 : ZMod 10708457791) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 9 * (11 : ZMod 10708457791) ^ 9) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 6040355621 := by rw [factor_0_3]; decide
      have factor_0_5 : (11 : ZMod 10708457791) ^ 39 = 7638496097 := by
        calc
          (11 : ZMod 10708457791) ^ 39 = (11 : ZMod 10708457791) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 19 * (11 : ZMod 10708457791) ^ 19) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 7638496097 := by rw [factor_0_4]; decide
      have factor_0_6 : (11 : ZMod 10708457791) ^ 79 = 5883173722 := by
        calc
          (11 : ZMod 10708457791) ^ 79 = (11 : ZMod 10708457791) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 39 * (11 : ZMod 10708457791) ^ 39) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 5883173722 := by rw [factor_0_5]; decide
      have factor_0_7 : (11 : ZMod 10708457791) ^ 159 = 5044949520 := by
        calc
          (11 : ZMod 10708457791) ^ 159 = (11 : ZMod 10708457791) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 79 * (11 : ZMod 10708457791) ^ 79) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 5044949520 := by rw [factor_0_6]; decide
      have factor_0_8 : (11 : ZMod 10708457791) ^ 319 = 4574813851 := by
        calc
          (11 : ZMod 10708457791) ^ 319 = (11 : ZMod 10708457791) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 159 * (11 : ZMod 10708457791) ^ 159) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 4574813851 := by rw [factor_0_7]; decide
      have factor_0_9 : (11 : ZMod 10708457791) ^ 638 = 2154802908 := by
        calc
          (11 : ZMod 10708457791) ^ 638 = (11 : ZMod 10708457791) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 319 * (11 : ZMod 10708457791) ^ 319 := by rw [pow_add]
          _ = 2154802908 := by rw [factor_0_8]; decide
      have factor_0_10 : (11 : ZMod 10708457791) ^ 1276 = 10617395400 := by
        calc
          (11 : ZMod 10708457791) ^ 1276 = (11 : ZMod 10708457791) ^ (638 + 638) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 638 * (11 : ZMod 10708457791) ^ 638 := by rw [pow_add]
          _ = 10617395400 := by rw [factor_0_9]; decide
      have factor_0_11 : (11 : ZMod 10708457791) ^ 2553 = 10413874980 := by
        calc
          (11 : ZMod 10708457791) ^ 2553 = (11 : ZMod 10708457791) ^ (1276 + 1276 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 1276 * (11 : ZMod 10708457791) ^ 1276) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 10413874980 := by rw [factor_0_10]; decide
      have factor_0_12 : (11 : ZMod 10708457791) ^ 5106 = 3625280577 := by
        calc
          (11 : ZMod 10708457791) ^ 5106 = (11 : ZMod 10708457791) ^ (2553 + 2553) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 2553 * (11 : ZMod 10708457791) ^ 2553 := by rw [pow_add]
          _ = 3625280577 := by rw [factor_0_11]; decide
      have factor_0_13 : (11 : ZMod 10708457791) ^ 10212 = 3489837576 := by
        calc
          (11 : ZMod 10708457791) ^ 10212 = (11 : ZMod 10708457791) ^ (5106 + 5106) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 5106 * (11 : ZMod 10708457791) ^ 5106 := by rw [pow_add]
          _ = 3489837576 := by rw [factor_0_12]; decide
      have factor_0_14 : (11 : ZMod 10708457791) ^ 20424 = 4566438380 := by
        calc
          (11 : ZMod 10708457791) ^ 20424 = (11 : ZMod 10708457791) ^ (10212 + 10212) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 10212 * (11 : ZMod 10708457791) ^ 10212 := by rw [pow_add]
          _ = 4566438380 := by rw [factor_0_13]; decide
      have factor_0_15 : (11 : ZMod 10708457791) ^ 40849 = 407779398 := by
        calc
          (11 : ZMod 10708457791) ^ 40849 = (11 : ZMod 10708457791) ^ (20424 + 20424 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 20424 * (11 : ZMod 10708457791) ^ 20424) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 407779398 := by rw [factor_0_14]; decide
      have factor_0_16 : (11 : ZMod 10708457791) ^ 81699 = 4128642945 := by
        calc
          (11 : ZMod 10708457791) ^ 81699 = (11 : ZMod 10708457791) ^ (40849 + 40849 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 40849 * (11 : ZMod 10708457791) ^ 40849) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 4128642945 := by rw [factor_0_15]; decide
      have factor_0_17 : (11 : ZMod 10708457791) ^ 163398 = 6814550748 := by
        calc
          (11 : ZMod 10708457791) ^ 163398 = (11 : ZMod 10708457791) ^ (81699 + 81699) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 81699 * (11 : ZMod 10708457791) ^ 81699 := by rw [pow_add]
          _ = 6814550748 := by rw [factor_0_16]; decide
      have factor_0_18 : (11 : ZMod 10708457791) ^ 326796 = 8855032833 := by
        calc
          (11 : ZMod 10708457791) ^ 326796 = (11 : ZMod 10708457791) ^ (163398 + 163398) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 163398 * (11 : ZMod 10708457791) ^ 163398 := by rw [pow_add]
          _ = 8855032833 := by rw [factor_0_17]; decide
      have factor_0_19 : (11 : ZMod 10708457791) ^ 653592 = 6329443003 := by
        calc
          (11 : ZMod 10708457791) ^ 653592 = (11 : ZMod 10708457791) ^ (326796 + 326796) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 326796 * (11 : ZMod 10708457791) ^ 326796 := by rw [pow_add]
          _ = 6329443003 := by rw [factor_0_18]; decide
      have factor_0_20 : (11 : ZMod 10708457791) ^ 1307184 = 6441662524 := by
        calc
          (11 : ZMod 10708457791) ^ 1307184 = (11 : ZMod 10708457791) ^ (653592 + 653592) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 653592 * (11 : ZMod 10708457791) ^ 653592 := by rw [pow_add]
          _ = 6441662524 := by rw [factor_0_19]; decide
      have factor_0_21 : (11 : ZMod 10708457791) ^ 2614369 = 4758898744 := by
        calc
          (11 : ZMod 10708457791) ^ 2614369 = (11 : ZMod 10708457791) ^ (1307184 + 1307184 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 1307184 * (11 : ZMod 10708457791) ^ 1307184) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 4758898744 := by rw [factor_0_20]; decide
      have factor_0_22 : (11 : ZMod 10708457791) ^ 5228739 = 9966495512 := by
        calc
          (11 : ZMod 10708457791) ^ 5228739 = (11 : ZMod 10708457791) ^ (2614369 + 2614369 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 2614369 * (11 : ZMod 10708457791) ^ 2614369) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 9966495512 := by rw [factor_0_21]; decide
      have factor_0_23 : (11 : ZMod 10708457791) ^ 10457478 = 917198649 := by
        calc
          (11 : ZMod 10708457791) ^ 10457478 = (11 : ZMod 10708457791) ^ (5228739 + 5228739) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 5228739 * (11 : ZMod 10708457791) ^ 5228739 := by rw [pow_add]
          _ = 917198649 := by rw [factor_0_22]; decide
      have factor_0_24 : (11 : ZMod 10708457791) ^ 20914956 = 1702309009 := by
        calc
          (11 : ZMod 10708457791) ^ 20914956 = (11 : ZMod 10708457791) ^ (10457478 + 10457478) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 10457478 * (11 : ZMod 10708457791) ^ 10457478 := by rw [pow_add]
          _ = 1702309009 := by rw [factor_0_23]; decide
      have factor_0_25 : (11 : ZMod 10708457791) ^ 41829913 = 7953009128 := by
        calc
          (11 : ZMod 10708457791) ^ 41829913 = (11 : ZMod 10708457791) ^ (20914956 + 20914956 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 20914956 * (11 : ZMod 10708457791) ^ 20914956) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 7953009128 := by rw [factor_0_24]; decide
      have factor_0_26 : (11 : ZMod 10708457791) ^ 83659826 = 9151279692 := by
        calc
          (11 : ZMod 10708457791) ^ 83659826 = (11 : ZMod 10708457791) ^ (41829913 + 41829913) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 41829913 * (11 : ZMod 10708457791) ^ 41829913 := by rw [pow_add]
          _ = 9151279692 := by rw [factor_0_25]; decide
      have factor_0_27 : (11 : ZMod 10708457791) ^ 167319652 = 3455140167 := by
        calc
          (11 : ZMod 10708457791) ^ 167319652 = (11 : ZMod 10708457791) ^ (83659826 + 83659826) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 83659826 * (11 : ZMod 10708457791) ^ 83659826 := by rw [pow_add]
          _ = 3455140167 := by rw [factor_0_26]; decide
      have factor_0_28 : (11 : ZMod 10708457791) ^ 334639305 = 7956809215 := by
        calc
          (11 : ZMod 10708457791) ^ 334639305 = (11 : ZMod 10708457791) ^ (167319652 + 167319652 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 167319652 * (11 : ZMod 10708457791) ^ 167319652) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 7956809215 := by rw [factor_0_27]; decide
      have factor_0_29 : (11 : ZMod 10708457791) ^ 669278611 = 3189588507 := by
        calc
          (11 : ZMod 10708457791) ^ 669278611 = (11 : ZMod 10708457791) ^ (334639305 + 334639305 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 334639305 * (11 : ZMod 10708457791) ^ 334639305) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 3189588507 := by rw [factor_0_28]; decide
      have factor_0_30 : (11 : ZMod 10708457791) ^ 1338557223 = 1656470819 := by
        calc
          (11 : ZMod 10708457791) ^ 1338557223 = (11 : ZMod 10708457791) ^ (669278611 + 669278611 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 669278611 * (11 : ZMod 10708457791) ^ 669278611) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 1656470819 := by rw [factor_0_29]; decide
      have factor_0_31 : (11 : ZMod 10708457791) ^ 2677114447 = 3645425801 := by
        calc
          (11 : ZMod 10708457791) ^ 2677114447 = (11 : ZMod 10708457791) ^ (1338557223 + 1338557223 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 1338557223 * (11 : ZMod 10708457791) ^ 1338557223) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 3645425801 := by rw [factor_0_30]; decide
      have factor_0_32 : (11 : ZMod 10708457791) ^ 5354228895 = 10708457790 := by
        calc
          (11 : ZMod 10708457791) ^ 5354228895 = (11 : ZMod 10708457791) ^ (2677114447 + 2677114447 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 2677114447 * (11 : ZMod 10708457791) ^ 2677114447) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 10708457790 := by rw [factor_0_31]; decide
      change (11 : ZMod 10708457791) ^ 5354228895 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (11 : ZMod 10708457791) ^ 1 = 11 := by norm_num
      have factor_1_1 : (11 : ZMod 10708457791) ^ 3 = 1331 := by
        calc
          (11 : ZMod 10708457791) ^ 3 = (11 : ZMod 10708457791) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 1 * (11 : ZMod 10708457791) ^ 1) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 1331 := by rw [factor_1_0]; decide
      have factor_1_2 : (11 : ZMod 10708457791) ^ 6 = 1771561 := by
        calc
          (11 : ZMod 10708457791) ^ 6 = (11 : ZMod 10708457791) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 3 * (11 : ZMod 10708457791) ^ 3 := by rw [pow_add]
          _ = 1771561 := by rw [factor_1_1]; decide
      have factor_1_3 : (11 : ZMod 10708457791) ^ 13 = 9352683538 := by
        calc
          (11 : ZMod 10708457791) ^ 13 = (11 : ZMod 10708457791) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 6 * (11 : ZMod 10708457791) ^ 6) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 9352683538 := by rw [factor_1_2]; decide
      have factor_1_4 : (11 : ZMod 10708457791) ^ 26 = 8116212528 := by
        calc
          (11 : ZMod 10708457791) ^ 26 = (11 : ZMod 10708457791) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 13 * (11 : ZMod 10708457791) ^ 13 := by rw [pow_add]
          _ = 8116212528 := by rw [factor_1_3]; decide
      have factor_1_5 : (11 : ZMod 10708457791) ^ 53 = 3673961087 := by
        calc
          (11 : ZMod 10708457791) ^ 53 = (11 : ZMod 10708457791) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 26 * (11 : ZMod 10708457791) ^ 26) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 3673961087 := by rw [factor_1_4]; decide
      have factor_1_6 : (11 : ZMod 10708457791) ^ 106 = 1103534138 := by
        calc
          (11 : ZMod 10708457791) ^ 106 = (11 : ZMod 10708457791) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 53 * (11 : ZMod 10708457791) ^ 53 := by rw [pow_add]
          _ = 1103534138 := by rw [factor_1_5]; decide
      have factor_1_7 : (11 : ZMod 10708457791) ^ 212 = 3444193941 := by
        calc
          (11 : ZMod 10708457791) ^ 212 = (11 : ZMod 10708457791) ^ (106 + 106) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 106 * (11 : ZMod 10708457791) ^ 106 := by rw [pow_add]
          _ = 3444193941 := by rw [factor_1_6]; decide
      have factor_1_8 : (11 : ZMod 10708457791) ^ 425 = 5545394916 := by
        calc
          (11 : ZMod 10708457791) ^ 425 = (11 : ZMod 10708457791) ^ (212 + 212 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 212 * (11 : ZMod 10708457791) ^ 212) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 5545394916 := by rw [factor_1_7]; decide
      have factor_1_9 : (11 : ZMod 10708457791) ^ 851 = 9590615431 := by
        calc
          (11 : ZMod 10708457791) ^ 851 = (11 : ZMod 10708457791) ^ (425 + 425 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 425 * (11 : ZMod 10708457791) ^ 425) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 9590615431 := by rw [factor_1_8]; decide
      have factor_1_10 : (11 : ZMod 10708457791) ^ 1702 = 6618368741 := by
        calc
          (11 : ZMod 10708457791) ^ 1702 = (11 : ZMod 10708457791) ^ (851 + 851) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 851 * (11 : ZMod 10708457791) ^ 851 := by rw [pow_add]
          _ = 6618368741 := by rw [factor_1_9]; decide
      have factor_1_11 : (11 : ZMod 10708457791) ^ 3404 = 9866951294 := by
        calc
          (11 : ZMod 10708457791) ^ 3404 = (11 : ZMod 10708457791) ^ (1702 + 1702) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 1702 * (11 : ZMod 10708457791) ^ 1702 := by rw [pow_add]
          _ = 9866951294 := by rw [factor_1_10]; decide
      have factor_1_12 : (11 : ZMod 10708457791) ^ 6808 = 4306846609 := by
        calc
          (11 : ZMod 10708457791) ^ 6808 = (11 : ZMod 10708457791) ^ (3404 + 3404) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 3404 * (11 : ZMod 10708457791) ^ 3404 := by rw [pow_add]
          _ = 4306846609 := by rw [factor_1_11]; decide
      have factor_1_13 : (11 : ZMod 10708457791) ^ 13616 = 9814910140 := by
        calc
          (11 : ZMod 10708457791) ^ 13616 = (11 : ZMod 10708457791) ^ (6808 + 6808) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 6808 * (11 : ZMod 10708457791) ^ 6808 := by rw [pow_add]
          _ = 9814910140 := by rw [factor_1_12]; decide
      have factor_1_14 : (11 : ZMod 10708457791) ^ 27233 = 1787988509 := by
        calc
          (11 : ZMod 10708457791) ^ 27233 = (11 : ZMod 10708457791) ^ (13616 + 13616 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 13616 * (11 : ZMod 10708457791) ^ 13616) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 1787988509 := by rw [factor_1_13]; decide
      have factor_1_15 : (11 : ZMod 10708457791) ^ 54466 = 5058565409 := by
        calc
          (11 : ZMod 10708457791) ^ 54466 = (11 : ZMod 10708457791) ^ (27233 + 27233) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 27233 * (11 : ZMod 10708457791) ^ 27233 := by rw [pow_add]
          _ = 5058565409 := by rw [factor_1_14]; decide
      have factor_1_16 : (11 : ZMod 10708457791) ^ 108932 = 309832489 := by
        calc
          (11 : ZMod 10708457791) ^ 108932 = (11 : ZMod 10708457791) ^ (54466 + 54466) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 54466 * (11 : ZMod 10708457791) ^ 54466 := by rw [pow_add]
          _ = 309832489 := by rw [factor_1_15]; decide
      have factor_1_17 : (11 : ZMod 10708457791) ^ 217864 = 8620275383 := by
        calc
          (11 : ZMod 10708457791) ^ 217864 = (11 : ZMod 10708457791) ^ (108932 + 108932) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 108932 * (11 : ZMod 10708457791) ^ 108932 := by rw [pow_add]
          _ = 8620275383 := by rw [factor_1_16]; decide
      have factor_1_18 : (11 : ZMod 10708457791) ^ 435728 = 7707704943 := by
        calc
          (11 : ZMod 10708457791) ^ 435728 = (11 : ZMod 10708457791) ^ (217864 + 217864) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 217864 * (11 : ZMod 10708457791) ^ 217864 := by rw [pow_add]
          _ = 7707704943 := by rw [factor_1_17]; decide
      have factor_1_19 : (11 : ZMod 10708457791) ^ 871456 = 1145799419 := by
        calc
          (11 : ZMod 10708457791) ^ 871456 = (11 : ZMod 10708457791) ^ (435728 + 435728) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 435728 * (11 : ZMod 10708457791) ^ 435728 := by rw [pow_add]
          _ = 1145799419 := by rw [factor_1_18]; decide
      have factor_1_20 : (11 : ZMod 10708457791) ^ 1742913 = 6607752665 := by
        calc
          (11 : ZMod 10708457791) ^ 1742913 = (11 : ZMod 10708457791) ^ (871456 + 871456 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 871456 * (11 : ZMod 10708457791) ^ 871456) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 6607752665 := by rw [factor_1_19]; decide
      have factor_1_21 : (11 : ZMod 10708457791) ^ 3485826 = 1851918467 := by
        calc
          (11 : ZMod 10708457791) ^ 3485826 = (11 : ZMod 10708457791) ^ (1742913 + 1742913) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 1742913 * (11 : ZMod 10708457791) ^ 1742913 := by rw [pow_add]
          _ = 1851918467 := by rw [factor_1_20]; decide
      have factor_1_22 : (11 : ZMod 10708457791) ^ 6971652 = 1851232644 := by
        calc
          (11 : ZMod 10708457791) ^ 6971652 = (11 : ZMod 10708457791) ^ (3485826 + 3485826) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 3485826 * (11 : ZMod 10708457791) ^ 3485826 := by rw [pow_add]
          _ = 1851232644 := by rw [factor_1_21]; decide
      have factor_1_23 : (11 : ZMod 10708457791) ^ 13943304 = 9872666970 := by
        calc
          (11 : ZMod 10708457791) ^ 13943304 = (11 : ZMod 10708457791) ^ (6971652 + 6971652) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 6971652 * (11 : ZMod 10708457791) ^ 6971652 := by rw [pow_add]
          _ = 9872666970 := by rw [factor_1_22]; decide
      have factor_1_24 : (11 : ZMod 10708457791) ^ 27886608 = 2328833674 := by
        calc
          (11 : ZMod 10708457791) ^ 27886608 = (11 : ZMod 10708457791) ^ (13943304 + 13943304) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 13943304 * (11 : ZMod 10708457791) ^ 13943304 := by rw [pow_add]
          _ = 2328833674 := by rw [factor_1_23]; decide
      have factor_1_25 : (11 : ZMod 10708457791) ^ 55773217 = 2408187054 := by
        calc
          (11 : ZMod 10708457791) ^ 55773217 = (11 : ZMod 10708457791) ^ (27886608 + 27886608 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 27886608 * (11 : ZMod 10708457791) ^ 27886608) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 2408187054 := by rw [factor_1_24]; decide
      have factor_1_26 : (11 : ZMod 10708457791) ^ 111546435 = 7736109703 := by
        calc
          (11 : ZMod 10708457791) ^ 111546435 = (11 : ZMod 10708457791) ^ (55773217 + 55773217 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 55773217 * (11 : ZMod 10708457791) ^ 55773217) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 7736109703 := by rw [factor_1_25]; decide
      have factor_1_27 : (11 : ZMod 10708457791) ^ 223092870 = 8006729911 := by
        calc
          (11 : ZMod 10708457791) ^ 223092870 = (11 : ZMod 10708457791) ^ (111546435 + 111546435) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 111546435 * (11 : ZMod 10708457791) ^ 111546435 := by rw [pow_add]
          _ = 8006729911 := by rw [factor_1_26]; decide
      have factor_1_28 : (11 : ZMod 10708457791) ^ 446185741 = 4970237307 := by
        calc
          (11 : ZMod 10708457791) ^ 446185741 = (11 : ZMod 10708457791) ^ (223092870 + 223092870 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 223092870 * (11 : ZMod 10708457791) ^ 223092870) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 4970237307 := by rw [factor_1_27]; decide
      have factor_1_29 : (11 : ZMod 10708457791) ^ 892371482 = 710956203 := by
        calc
          (11 : ZMod 10708457791) ^ 892371482 = (11 : ZMod 10708457791) ^ (446185741 + 446185741) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 446185741 * (11 : ZMod 10708457791) ^ 446185741 := by rw [pow_add]
          _ = 710956203 := by rw [factor_1_28]; decide
      have factor_1_30 : (11 : ZMod 10708457791) ^ 1784742965 = 1593870913 := by
        calc
          (11 : ZMod 10708457791) ^ 1784742965 = (11 : ZMod 10708457791) ^ (892371482 + 892371482 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 892371482 * (11 : ZMod 10708457791) ^ 892371482) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 1593870913 := by rw [factor_1_29]; decide
      have factor_1_31 : (11 : ZMod 10708457791) ^ 3569485930 = 1593870912 := by
        calc
          (11 : ZMod 10708457791) ^ 3569485930 = (11 : ZMod 10708457791) ^ (1784742965 + 1784742965) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 1784742965 * (11 : ZMod 10708457791) ^ 1784742965 := by rw [pow_add]
          _ = 1593870912 := by rw [factor_1_30]; decide
      change (11 : ZMod 10708457791) ^ 3569485930 ≠ 1
      rw [factor_1_31]
      decide
    ·
      have factor_2_0 : (11 : ZMod 10708457791) ^ 1 = 11 := by norm_num
      have factor_2_1 : (11 : ZMod 10708457791) ^ 3 = 1331 := by
        calc
          (11 : ZMod 10708457791) ^ 3 = (11 : ZMod 10708457791) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 1 * (11 : ZMod 10708457791) ^ 1) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 1331 := by rw [factor_2_0]; decide
      have factor_2_2 : (11 : ZMod 10708457791) ^ 7 = 19487171 := by
        calc
          (11 : ZMod 10708457791) ^ 7 = (11 : ZMod 10708457791) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 3 * (11 : ZMod 10708457791) ^ 3) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 19487171 := by rw [factor_2_1]; decide
      have factor_2_3 : (11 : ZMod 10708457791) ^ 15 = 7286640043 := by
        calc
          (11 : ZMod 10708457791) ^ 15 = (11 : ZMod 10708457791) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 7 * (11 : ZMod 10708457791) ^ 7) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 7286640043 := by rw [factor_2_2]; decide
      have factor_2_4 : (11 : ZMod 10708457791) ^ 31 = 6952046304 := by
        calc
          (11 : ZMod 10708457791) ^ 31 = (11 : ZMod 10708457791) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 15 * (11 : ZMod 10708457791) ^ 15) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 6952046304 := by rw [factor_2_3]; decide
      have factor_2_5 : (11 : ZMod 10708457791) ^ 63 = 9296854155 := by
        calc
          (11 : ZMod 10708457791) ^ 63 = (11 : ZMod 10708457791) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 31 * (11 : ZMod 10708457791) ^ 31) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 9296854155 := by rw [factor_2_4]; decide
      have factor_2_6 : (11 : ZMod 10708457791) ^ 127 = 2958217823 := by
        calc
          (11 : ZMod 10708457791) ^ 127 = (11 : ZMod 10708457791) ^ (63 + 63 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 63 * (11 : ZMod 10708457791) ^ 63) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 2958217823 := by rw [factor_2_5]; decide
      have factor_2_7 : (11 : ZMod 10708457791) ^ 255 = 8279592189 := by
        calc
          (11 : ZMod 10708457791) ^ 255 = (11 : ZMod 10708457791) ^ (127 + 127 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 127 * (11 : ZMod 10708457791) ^ 127) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 8279592189 := by rw [factor_2_6]; decide
      have factor_2_8 : (11 : ZMod 10708457791) ^ 510 = 4953004966 := by
        calc
          (11 : ZMod 10708457791) ^ 510 = (11 : ZMod 10708457791) ^ (255 + 255) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 255 * (11 : ZMod 10708457791) ^ 255 := by rw [pow_add]
          _ = 4953004966 := by rw [factor_2_7]; decide
      have factor_2_9 : (11 : ZMod 10708457791) ^ 1021 = 1633520079 := by
        calc
          (11 : ZMod 10708457791) ^ 1021 = (11 : ZMod 10708457791) ^ (510 + 510 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 510 * (11 : ZMod 10708457791) ^ 510) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 1633520079 := by rw [factor_2_8]; decide
      have factor_2_10 : (11 : ZMod 10708457791) ^ 2042 = 1419954707 := by
        calc
          (11 : ZMod 10708457791) ^ 2042 = (11 : ZMod 10708457791) ^ (1021 + 1021) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 1021 * (11 : ZMod 10708457791) ^ 1021 := by rw [pow_add]
          _ = 1419954707 := by rw [factor_2_9]; decide
      have factor_2_11 : (11 : ZMod 10708457791) ^ 4084 = 36384554 := by
        calc
          (11 : ZMod 10708457791) ^ 4084 = (11 : ZMod 10708457791) ^ (2042 + 2042) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 2042 * (11 : ZMod 10708457791) ^ 2042 := by rw [pow_add]
          _ = 36384554 := by rw [factor_2_10]; decide
      have factor_2_12 : (11 : ZMod 10708457791) ^ 8169 = 8012116369 := by
        calc
          (11 : ZMod 10708457791) ^ 8169 = (11 : ZMod 10708457791) ^ (4084 + 4084 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 4084 * (11 : ZMod 10708457791) ^ 4084) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 8012116369 := by rw [factor_2_11]; decide
      have factor_2_13 : (11 : ZMod 10708457791) ^ 16339 = 8818964394 := by
        calc
          (11 : ZMod 10708457791) ^ 16339 = (11 : ZMod 10708457791) ^ (8169 + 8169 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 8169 * (11 : ZMod 10708457791) ^ 8169) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 8818964394 := by rw [factor_2_12]; decide
      have factor_2_14 : (11 : ZMod 10708457791) ^ 32679 = 2100184165 := by
        calc
          (11 : ZMod 10708457791) ^ 32679 = (11 : ZMod 10708457791) ^ (16339 + 16339 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 16339 * (11 : ZMod 10708457791) ^ 16339) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 2100184165 := by rw [factor_2_13]; decide
      have factor_2_15 : (11 : ZMod 10708457791) ^ 65359 = 3528194878 := by
        calc
          (11 : ZMod 10708457791) ^ 65359 = (11 : ZMod 10708457791) ^ (32679 + 32679 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 32679 * (11 : ZMod 10708457791) ^ 32679) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 3528194878 := by rw [factor_2_14]; decide
      have factor_2_16 : (11 : ZMod 10708457791) ^ 130718 = 6275257294 := by
        calc
          (11 : ZMod 10708457791) ^ 130718 = (11 : ZMod 10708457791) ^ (65359 + 65359) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 65359 * (11 : ZMod 10708457791) ^ 65359 := by rw [pow_add]
          _ = 6275257294 := by rw [factor_2_15]; decide
      have factor_2_17 : (11 : ZMod 10708457791) ^ 261436 = 9882971629 := by
        calc
          (11 : ZMod 10708457791) ^ 261436 = (11 : ZMod 10708457791) ^ (130718 + 130718) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 130718 * (11 : ZMod 10708457791) ^ 130718 := by rw [pow_add]
          _ = 9882971629 := by rw [factor_2_16]; decide
      have factor_2_18 : (11 : ZMod 10708457791) ^ 522873 = 6575592007 := by
        calc
          (11 : ZMod 10708457791) ^ 522873 = (11 : ZMod 10708457791) ^ (261436 + 261436 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 261436 * (11 : ZMod 10708457791) ^ 261436) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 6575592007 := by rw [factor_2_17]; decide
      have factor_2_19 : (11 : ZMod 10708457791) ^ 1045747 = 9605057938 := by
        calc
          (11 : ZMod 10708457791) ^ 1045747 = (11 : ZMod 10708457791) ^ (522873 + 522873 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 522873 * (11 : ZMod 10708457791) ^ 522873) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 9605057938 := by rw [factor_2_18]; decide
      have factor_2_20 : (11 : ZMod 10708457791) ^ 2091495 = 9999904950 := by
        calc
          (11 : ZMod 10708457791) ^ 2091495 = (11 : ZMod 10708457791) ^ (1045747 + 1045747 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 1045747 * (11 : ZMod 10708457791) ^ 1045747) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 9999904950 := by rw [factor_2_19]; decide
      have factor_2_21 : (11 : ZMod 10708457791) ^ 4182991 = 10582836012 := by
        calc
          (11 : ZMod 10708457791) ^ 4182991 = (11 : ZMod 10708457791) ^ (2091495 + 2091495 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 2091495 * (11 : ZMod 10708457791) ^ 2091495) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 10582836012 := by rw [factor_2_20]; decide
      have factor_2_22 : (11 : ZMod 10708457791) ^ 8365982 = 1990141752 := by
        calc
          (11 : ZMod 10708457791) ^ 8365982 = (11 : ZMod 10708457791) ^ (4182991 + 4182991) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 4182991 * (11 : ZMod 10708457791) ^ 4182991 := by rw [pow_add]
          _ = 1990141752 := by rw [factor_2_21]; decide
      have factor_2_23 : (11 : ZMod 10708457791) ^ 16731965 = 10580460615 := by
        calc
          (11 : ZMod 10708457791) ^ 16731965 = (11 : ZMod 10708457791) ^ (8365982 + 8365982 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 8365982 * (11 : ZMod 10708457791) ^ 8365982) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 10580460615 := by rw [factor_2_22]; decide
      have factor_2_24 : (11 : ZMod 10708457791) ^ 33463930 = 568128018 := by
        calc
          (11 : ZMod 10708457791) ^ 33463930 = (11 : ZMod 10708457791) ^ (16731965 + 16731965) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 16731965 * (11 : ZMod 10708457791) ^ 16731965 := by rw [pow_add]
          _ = 568128018 := by rw [factor_2_23]; decide
      have factor_2_25 : (11 : ZMod 10708457791) ^ 66927861 = 10395091548 := by
        calc
          (11 : ZMod 10708457791) ^ 66927861 = (11 : ZMod 10708457791) ^ (33463930 + 33463930 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 33463930 * (11 : ZMod 10708457791) ^ 33463930) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 10395091548 := by rw [factor_2_24]; decide
      have factor_2_26 : (11 : ZMod 10708457791) ^ 133855722 = 2453724997 := by
        calc
          (11 : ZMod 10708457791) ^ 133855722 = (11 : ZMod 10708457791) ^ (66927861 + 66927861) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 66927861 * (11 : ZMod 10708457791) ^ 66927861 := by rw [pow_add]
          _ = 2453724997 := by rw [factor_2_25]; decide
      have factor_2_27 : (11 : ZMod 10708457791) ^ 267711444 = 4490490189 := by
        calc
          (11 : ZMod 10708457791) ^ 267711444 = (11 : ZMod 10708457791) ^ (133855722 + 133855722) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 133855722 * (11 : ZMod 10708457791) ^ 133855722 := by rw [pow_add]
          _ = 4490490189 := by rw [factor_2_26]; decide
      have factor_2_28 : (11 : ZMod 10708457791) ^ 535422889 = 5746848442 := by
        calc
          (11 : ZMod 10708457791) ^ 535422889 = (11 : ZMod 10708457791) ^ (267711444 + 267711444 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 267711444 * (11 : ZMod 10708457791) ^ 267711444) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 5746848442 := by rw [factor_2_27]; decide
      have factor_2_29 : (11 : ZMod 10708457791) ^ 1070845779 = 7902047609 := by
        calc
          (11 : ZMod 10708457791) ^ 1070845779 = (11 : ZMod 10708457791) ^ (535422889 + 535422889 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 535422889 * (11 : ZMod 10708457791) ^ 535422889) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 7902047609 := by rw [factor_2_28]; decide
      have factor_2_30 : (11 : ZMod 10708457791) ^ 2141691558 = 7185599077 := by
        calc
          (11 : ZMod 10708457791) ^ 2141691558 = (11 : ZMod 10708457791) ^ (1070845779 + 1070845779) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 1070845779 * (11 : ZMod 10708457791) ^ 1070845779 := by rw [pow_add]
          _ = 7185599077 := by rw [factor_2_29]; decide
      change (11 : ZMod 10708457791) ^ 2141691558 ≠ 1
      rw [factor_2_30]
      decide
    ·
      have factor_3_0 : (11 : ZMod 10708457791) ^ 1 = 11 := by norm_num
      have factor_3_1 : (11 : ZMod 10708457791) ^ 2 = 121 := by
        calc
          (11 : ZMod 10708457791) ^ 2 = (11 : ZMod 10708457791) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 1 * (11 : ZMod 10708457791) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_3_0]; decide
      have factor_3_2 : (11 : ZMod 10708457791) ^ 4 = 14641 := by
        calc
          (11 : ZMod 10708457791) ^ 4 = (11 : ZMod 10708457791) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 2 * (11 : ZMod 10708457791) ^ 2 := by rw [pow_add]
          _ = 14641 := by rw [factor_3_1]; decide
      have factor_3_3 : (11 : ZMod 10708457791) ^ 8 = 214358881 := by
        calc
          (11 : ZMod 10708457791) ^ 8 = (11 : ZMod 10708457791) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 4 * (11 : ZMod 10708457791) ^ 4 := by rw [pow_add]
          _ = 214358881 := by rw [factor_3_2]; decide
      have factor_3_4 : (11 : ZMod 10708457791) ^ 16 = 5193835936 := by
        calc
          (11 : ZMod 10708457791) ^ 16 = (11 : ZMod 10708457791) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 8 * (11 : ZMod 10708457791) ^ 8 := by rw [pow_add]
          _ = 5193835936 := by rw [factor_3_3]; decide
      have factor_3_5 : (11 : ZMod 10708457791) ^ 33 = 5937895086 := by
        calc
          (11 : ZMod 10708457791) ^ 33 = (11 : ZMod 10708457791) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 16 * (11 : ZMod 10708457791) ^ 16) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 5937895086 := by rw [factor_3_4]; decide
      have factor_3_6 : (11 : ZMod 10708457791) ^ 66 = 5844131700 := by
        calc
          (11 : ZMod 10708457791) ^ 66 = (11 : ZMod 10708457791) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 33 * (11 : ZMod 10708457791) ^ 33 := by rw [pow_add]
          _ = 5844131700 := by rw [factor_3_5]; decide
      have factor_3_7 : (11 : ZMod 10708457791) ^ 133 = 8332563049 := by
        calc
          (11 : ZMod 10708457791) ^ 133 = (11 : ZMod 10708457791) ^ (66 + 66 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 66 * (11 : ZMod 10708457791) ^ 66) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 8332563049 := by rw [factor_3_6]; decide
      have factor_3_8 : (11 : ZMod 10708457791) ^ 266 = 2806904854 := by
        calc
          (11 : ZMod 10708457791) ^ 266 = (11 : ZMod 10708457791) ^ (133 + 133) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 133 * (11 : ZMod 10708457791) ^ 133 := by rw [pow_add]
          _ = 2806904854 := by rw [factor_3_7]; decide
      have factor_3_9 : (11 : ZMod 10708457791) ^ 532 = 313592014 := by
        calc
          (11 : ZMod 10708457791) ^ 532 = (11 : ZMod 10708457791) ^ (266 + 266) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 266 * (11 : ZMod 10708457791) ^ 266 := by rw [pow_add]
          _ = 313592014 := by rw [factor_3_8]; decide
      have factor_3_10 : (11 : ZMod 10708457791) ^ 1064 = 7051284706 := by
        calc
          (11 : ZMod 10708457791) ^ 1064 = (11 : ZMod 10708457791) ^ (532 + 532) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 532 * (11 : ZMod 10708457791) ^ 532 := by rw [pow_add]
          _ = 7051284706 := by rw [factor_3_9]; decide
      have factor_3_11 : (11 : ZMod 10708457791) ^ 2128 = 6261176245 := by
        calc
          (11 : ZMod 10708457791) ^ 2128 = (11 : ZMod 10708457791) ^ (1064 + 1064) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 1064 * (11 : ZMod 10708457791) ^ 1064 := by rw [pow_add]
          _ = 6261176245 := by rw [factor_3_10]; decide
      have factor_3_12 : (11 : ZMod 10708457791) ^ 4257 = 9583681691 := by
        calc
          (11 : ZMod 10708457791) ^ 4257 = (11 : ZMod 10708457791) ^ (2128 + 2128 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 2128 * (11 : ZMod 10708457791) ^ 2128) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 9583681691 := by rw [factor_3_11]; decide
      have factor_3_13 : (11 : ZMod 10708457791) ^ 8515 = 691371943 := by
        calc
          (11 : ZMod 10708457791) ^ 8515 = (11 : ZMod 10708457791) ^ (4257 + 4257 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 4257 * (11 : ZMod 10708457791) ^ 4257) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 691371943 := by rw [factor_3_12]; decide
      have factor_3_14 : (11 : ZMod 10708457791) ^ 17031 = 3603142759 := by
        calc
          (11 : ZMod 10708457791) ^ 17031 = (11 : ZMod 10708457791) ^ (8515 + 8515 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 8515 * (11 : ZMod 10708457791) ^ 8515) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 3603142759 := by rw [factor_3_13]; decide
      have factor_3_15 : (11 : ZMod 10708457791) ^ 34063 = 254048687 := by
        calc
          (11 : ZMod 10708457791) ^ 34063 = (11 : ZMod 10708457791) ^ (17031 + 17031 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 17031 * (11 : ZMod 10708457791) ^ 17031) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 254048687 := by rw [factor_3_14]; decide
      have factor_3_16 : (11 : ZMod 10708457791) ^ 68126 = 3583443689 := by
        calc
          (11 : ZMod 10708457791) ^ 68126 = (11 : ZMod 10708457791) ^ (34063 + 34063) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 34063 * (11 : ZMod 10708457791) ^ 34063 := by rw [pow_add]
          _ = 3583443689 := by rw [factor_3_15]; decide
      have factor_3_17 : (11 : ZMod 10708457791) ^ 136253 = 8927258204 := by
        calc
          (11 : ZMod 10708457791) ^ 136253 = (11 : ZMod 10708457791) ^ (68126 + 68126 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 68126 * (11 : ZMod 10708457791) ^ 68126) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 8927258204 := by rw [factor_3_16]; decide
      have factor_3_18 : (11 : ZMod 10708457791) ^ 272507 = 2349735779 := by
        calc
          (11 : ZMod 10708457791) ^ 272507 = (11 : ZMod 10708457791) ^ (136253 + 136253 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 136253 * (11 : ZMod 10708457791) ^ 136253) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 2349735779 := by rw [factor_3_17]; decide
      have factor_3_19 : (11 : ZMod 10708457791) ^ 545015 = 6611327853 := by
        calc
          (11 : ZMod 10708457791) ^ 545015 = (11 : ZMod 10708457791) ^ (272507 + 272507 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 272507 * (11 : ZMod 10708457791) ^ 272507) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 6611327853 := by rw [factor_3_18]; decide
      have factor_3_20 : (11 : ZMod 10708457791) ^ 1090030 = 2984564242 := by
        calc
          (11 : ZMod 10708457791) ^ 1090030 = (11 : ZMod 10708457791) ^ (545015 + 545015) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 545015 * (11 : ZMod 10708457791) ^ 545015 := by rw [pow_add]
          _ = 2984564242 := by rw [factor_3_19]; decide
      have factor_3_21 : (11 : ZMod 10708457791) ^ 2180060 = 10003122266 := by
        calc
          (11 : ZMod 10708457791) ^ 2180060 = (11 : ZMod 10708457791) ^ (1090030 + 1090030) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 1090030 * (11 : ZMod 10708457791) ^ 1090030 := by rw [pow_add]
          _ = 10003122266 := by rw [factor_3_20]; decide
      have factor_3_22 : (11 : ZMod 10708457791) ^ 4360121 = 10028200448 := by
        calc
          (11 : ZMod 10708457791) ^ 4360121 = (11 : ZMod 10708457791) ^ (2180060 + 2180060 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 2180060 * (11 : ZMod 10708457791) ^ 2180060) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 10028200448 := by rw [factor_3_21]; decide
      have factor_3_23 : (11 : ZMod 10708457791) ^ 8720242 = 4869463239 := by
        calc
          (11 : ZMod 10708457791) ^ 8720242 = (11 : ZMod 10708457791) ^ (4360121 + 4360121) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 4360121 * (11 : ZMod 10708457791) ^ 4360121 := by rw [pow_add]
          _ = 4869463239 := by rw [factor_3_22]; decide
      have factor_3_24 : (11 : ZMod 10708457791) ^ 17440485 = 5890596735 := by
        calc
          (11 : ZMod 10708457791) ^ 17440485 = (11 : ZMod 10708457791) ^ (8720242 + 8720242 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 8720242 * (11 : ZMod 10708457791) ^ 8720242) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 5890596735 := by rw [factor_3_23]; decide
      have factor_3_25 : (11 : ZMod 10708457791) ^ 34880970 = 1156814315 := by
        calc
          (11 : ZMod 10708457791) ^ 34880970 = (11 : ZMod 10708457791) ^ (17440485 + 17440485) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 17440485 * (11 : ZMod 10708457791) ^ 17440485 := by rw [pow_add]
          _ = 1156814315 := by rw [factor_3_24]; decide
      change (11 : ZMod 10708457791) ^ 34880970 ≠ 1
      rw [factor_3_25]
      decide
    ·
      have factor_4_0 : (11 : ZMod 10708457791) ^ 1 = 11 := by norm_num
      have factor_4_1 : (11 : ZMod 10708457791) ^ 3 = 1331 := by
        calc
          (11 : ZMod 10708457791) ^ 3 = (11 : ZMod 10708457791) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 1 * (11 : ZMod 10708457791) ^ 1) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 1331 := by rw [factor_4_0]; decide
      have factor_4_2 : (11 : ZMod 10708457791) ^ 7 = 19487171 := by
        calc
          (11 : ZMod 10708457791) ^ 7 = (11 : ZMod 10708457791) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 3 * (11 : ZMod 10708457791) ^ 3) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 19487171 := by rw [factor_4_1]; decide
      have factor_4_3 : (11 : ZMod 10708457791) ^ 15 = 7286640043 := by
        calc
          (11 : ZMod 10708457791) ^ 15 = (11 : ZMod 10708457791) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 7 * (11 : ZMod 10708457791) ^ 7) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 7286640043 := by rw [factor_4_2]; decide
      have factor_4_4 : (11 : ZMod 10708457791) ^ 30 = 8419973512 := by
        calc
          (11 : ZMod 10708457791) ^ 30 = (11 : ZMod 10708457791) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 15 * (11 : ZMod 10708457791) ^ 15 := by rw [pow_add]
          _ = 8419973512 := by rw [factor_4_3]; decide
      have factor_4_5 : (11 : ZMod 10708457791) ^ 61 = 5209813273 := by
        calc
          (11 : ZMod 10708457791) ^ 61 = (11 : ZMod 10708457791) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 30 * (11 : ZMod 10708457791) ^ 30) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 5209813273 := by rw [factor_4_4]; decide
      have factor_4_6 : (11 : ZMod 10708457791) ^ 123 = 5849224450 := by
        calc
          (11 : ZMod 10708457791) ^ 123 = (11 : ZMod 10708457791) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 61 * (11 : ZMod 10708457791) ^ 61) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 5849224450 := by rw [factor_4_5]; decide
      have factor_4_7 : (11 : ZMod 10708457791) ^ 247 = 2705984399 := by
        calc
          (11 : ZMod 10708457791) ^ 247 = (11 : ZMod 10708457791) ^ (123 + 123 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 123 * (11 : ZMod 10708457791) ^ 123) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 2705984399 := by rw [factor_4_6]; decide
      have factor_4_8 : (11 : ZMod 10708457791) ^ 494 = 8713437981 := by
        calc
          (11 : ZMod 10708457791) ^ 494 = (11 : ZMod 10708457791) ^ (247 + 247) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 247 * (11 : ZMod 10708457791) ^ 247 := by rw [pow_add]
          _ = 8713437981 := by rw [factor_4_7]; decide
      have factor_4_9 : (11 : ZMod 10708457791) ^ 988 = 9922726423 := by
        calc
          (11 : ZMod 10708457791) ^ 988 = (11 : ZMod 10708457791) ^ (494 + 494) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 494 * (11 : ZMod 10708457791) ^ 494 := by rw [pow_add]
          _ = 9922726423 := by rw [factor_4_8]; decide
      have factor_4_10 : (11 : ZMod 10708457791) ^ 1977 = 2100392024 := by
        calc
          (11 : ZMod 10708457791) ^ 1977 = (11 : ZMod 10708457791) ^ (988 + 988 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 988 * (11 : ZMod 10708457791) ^ 988) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 2100392024 := by rw [factor_4_9]; decide
      have factor_4_11 : (11 : ZMod 10708457791) ^ 3955 = 1670667630 := by
        calc
          (11 : ZMod 10708457791) ^ 3955 = (11 : ZMod 10708457791) ^ (1977 + 1977 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 1977 * (11 : ZMod 10708457791) ^ 1977) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 1670667630 := by rw [factor_4_10]; decide
      have factor_4_12 : (11 : ZMod 10708457791) ^ 7910 = 8670062957 := by
        calc
          (11 : ZMod 10708457791) ^ 7910 = (11 : ZMod 10708457791) ^ (3955 + 3955) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 3955 * (11 : ZMod 10708457791) ^ 3955 := by rw [pow_add]
          _ = 8670062957 := by rw [factor_4_11]; decide
      have factor_4_13 : (11 : ZMod 10708457791) ^ 15820 = 5622342006 := by
        calc
          (11 : ZMod 10708457791) ^ 15820 = (11 : ZMod 10708457791) ^ (7910 + 7910) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 7910 * (11 : ZMod 10708457791) ^ 7910 := by rw [pow_add]
          _ = 5622342006 := by rw [factor_4_12]; decide
      have factor_4_14 : (11 : ZMod 10708457791) ^ 31641 = 10062220017 := by
        calc
          (11 : ZMod 10708457791) ^ 31641 = (11 : ZMod 10708457791) ^ (15820 + 15820 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 15820 * (11 : ZMod 10708457791) ^ 15820) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 10062220017 := by rw [factor_4_13]; decide
      have factor_4_15 : (11 : ZMod 10708457791) ^ 63282 = 3105474332 := by
        calc
          (11 : ZMod 10708457791) ^ 63282 = (11 : ZMod 10708457791) ^ (31641 + 31641) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 31641 * (11 : ZMod 10708457791) ^ 31641 := by rw [pow_add]
          _ = 3105474332 := by rw [factor_4_14]; decide
      have factor_4_16 : (11 : ZMod 10708457791) ^ 126565 = 1969795088 := by
        calc
          (11 : ZMod 10708457791) ^ 126565 = (11 : ZMod 10708457791) ^ (63282 + 63282 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 63282 * (11 : ZMod 10708457791) ^ 63282) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 1969795088 := by rw [factor_4_15]; decide
      have factor_4_17 : (11 : ZMod 10708457791) ^ 253131 = 10581261982 := by
        calc
          (11 : ZMod 10708457791) ^ 253131 = (11 : ZMod 10708457791) ^ (126565 + 126565 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 126565 * (11 : ZMod 10708457791) ^ 126565) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 10581261982 := by rw [factor_4_16]; decide
      have factor_4_18 : (11 : ZMod 10708457791) ^ 506262 = 7458210041 := by
        calc
          (11 : ZMod 10708457791) ^ 506262 = (11 : ZMod 10708457791) ^ (253131 + 253131) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 253131 * (11 : ZMod 10708457791) ^ 253131 := by rw [pow_add]
          _ = 7458210041 := by rw [factor_4_17]; decide
      have factor_4_19 : (11 : ZMod 10708457791) ^ 1012524 = 705210332 := by
        calc
          (11 : ZMod 10708457791) ^ 1012524 = (11 : ZMod 10708457791) ^ (506262 + 506262) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 506262 * (11 : ZMod 10708457791) ^ 506262 := by rw [pow_add]
          _ = 705210332 := by rw [factor_4_18]; decide
      have factor_4_20 : (11 : ZMod 10708457791) ^ 2025048 = 4595106729 := by
        calc
          (11 : ZMod 10708457791) ^ 2025048 = (11 : ZMod 10708457791) ^ (1012524 + 1012524) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 1012524 * (11 : ZMod 10708457791) ^ 1012524 := by rw [pow_add]
          _ = 4595106729 := by rw [factor_4_19]; decide
      have factor_4_21 : (11 : ZMod 10708457791) ^ 4050097 = 1428681910 := by
        calc
          (11 : ZMod 10708457791) ^ 4050097 = (11 : ZMod 10708457791) ^ (2025048 + 2025048 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 2025048 * (11 : ZMod 10708457791) ^ 2025048) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 1428681910 := by rw [factor_4_20]; decide
      have factor_4_22 : (11 : ZMod 10708457791) ^ 8100195 = 435558294 := by
        calc
          (11 : ZMod 10708457791) ^ 8100195 = (11 : ZMod 10708457791) ^ (4050097 + 4050097 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 4050097 * (11 : ZMod 10708457791) ^ 4050097) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 435558294 := by rw [factor_4_21]; decide
      have factor_4_23 : (11 : ZMod 10708457791) ^ 16200390 = 10663750018 := by
        calc
          (11 : ZMod 10708457791) ^ 16200390 = (11 : ZMod 10708457791) ^ (8100195 + 8100195) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 8100195 * (11 : ZMod 10708457791) ^ 8100195 := by rw [pow_add]
          _ = 10663750018 := by rw [factor_4_22]; decide
      change (11 : ZMod 10708457791) ^ 16200390 ≠ 1
      rw [factor_4_23]
      decide
    ·
      have factor_5_0 : (11 : ZMod 10708457791) ^ 1 = 11 := by norm_num
      have factor_5_1 : (11 : ZMod 10708457791) ^ 2 = 121 := by
        calc
          (11 : ZMod 10708457791) ^ 2 = (11 : ZMod 10708457791) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 1 * (11 : ZMod 10708457791) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_5_0]; decide
      have factor_5_2 : (11 : ZMod 10708457791) ^ 5 = 161051 := by
        calc
          (11 : ZMod 10708457791) ^ 5 = (11 : ZMod 10708457791) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 2 * (11 : ZMod 10708457791) ^ 2) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 161051 := by rw [factor_5_1]; decide
      have factor_5_3 : (11 : ZMod 10708457791) ^ 11 = 6891768045 := by
        calc
          (11 : ZMod 10708457791) ^ 11 = (11 : ZMod 10708457791) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 5 * (11 : ZMod 10708457791) ^ 5) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 6891768045 := by rw [factor_5_2]; decide
      have factor_5_4 : (11 : ZMod 10708457791) ^ 23 = 6402208983 := by
        calc
          (11 : ZMod 10708457791) ^ 23 = (11 : ZMod 10708457791) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 11 * (11 : ZMod 10708457791) ^ 11) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 6402208983 := by rw [factor_5_3]; decide
      have factor_5_5 : (11 : ZMod 10708457791) ^ 46 = 8395805280 := by
        calc
          (11 : ZMod 10708457791) ^ 46 = (11 : ZMod 10708457791) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 23 * (11 : ZMod 10708457791) ^ 23 := by rw [pow_add]
          _ = 8395805280 := by rw [factor_5_4]; decide
      have factor_5_6 : (11 : ZMod 10708457791) ^ 92 = 1534414140 := by
        calc
          (11 : ZMod 10708457791) ^ 92 = (11 : ZMod 10708457791) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 46 * (11 : ZMod 10708457791) ^ 46 := by rw [pow_add]
          _ = 1534414140 := by rw [factor_5_5]; decide
      have factor_5_7 : (11 : ZMod 10708457791) ^ 185 = 8874394182 := by
        calc
          (11 : ZMod 10708457791) ^ 185 = (11 : ZMod 10708457791) ^ (92 + 92 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 92 * (11 : ZMod 10708457791) ^ 92) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 8874394182 := by rw [factor_5_6]; decide
      have factor_5_8 : (11 : ZMod 10708457791) ^ 371 = 6749503029 := by
        calc
          (11 : ZMod 10708457791) ^ 371 = (11 : ZMod 10708457791) ^ (185 + 185 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 185 * (11 : ZMod 10708457791) ^ 185) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 6749503029 := by rw [factor_5_7]; decide
      have factor_5_9 : (11 : ZMod 10708457791) ^ 743 = 8707302227 := by
        calc
          (11 : ZMod 10708457791) ^ 743 = (11 : ZMod 10708457791) ^ (371 + 371 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 371 * (11 : ZMod 10708457791) ^ 371) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 8707302227 := by rw [factor_5_8]; decide
      have factor_5_10 : (11 : ZMod 10708457791) ^ 1486 = 6941457452 := by
        calc
          (11 : ZMod 10708457791) ^ 1486 = (11 : ZMod 10708457791) ^ (743 + 743) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 743 * (11 : ZMod 10708457791) ^ 743 := by rw [pow_add]
          _ = 6941457452 := by rw [factor_5_9]; decide
      have factor_5_11 : (11 : ZMod 10708457791) ^ 2972 = 696553429 := by
        calc
          (11 : ZMod 10708457791) ^ 2972 = (11 : ZMod 10708457791) ^ (1486 + 1486) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 1486 * (11 : ZMod 10708457791) ^ 1486 := by rw [pow_add]
          _ = 696553429 := by rw [factor_5_10]; decide
      have factor_5_12 : (11 : ZMod 10708457791) ^ 5945 = 2420716843 := by
        calc
          (11 : ZMod 10708457791) ^ 5945 = (11 : ZMod 10708457791) ^ (2972 + 2972 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 2972 * (11 : ZMod 10708457791) ^ 2972) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 2420716843 := by rw [factor_5_11]; decide
      have factor_5_13 : (11 : ZMod 10708457791) ^ 11890 = 1360121762 := by
        calc
          (11 : ZMod 10708457791) ^ 11890 = (11 : ZMod 10708457791) ^ (5945 + 5945) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 5945 * (11 : ZMod 10708457791) ^ 5945 := by rw [pow_add]
          _ = 1360121762 := by rw [factor_5_12]; decide
      have factor_5_14 : (11 : ZMod 10708457791) ^ 23780 = 9338061161 := by
        calc
          (11 : ZMod 10708457791) ^ 23780 = (11 : ZMod 10708457791) ^ (11890 + 11890) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 11890 * (11 : ZMod 10708457791) ^ 11890 := by rw [pow_add]
          _ = 9338061161 := by rw [factor_5_13]; decide
      have factor_5_15 : (11 : ZMod 10708457791) ^ 47561 = 1697322373 := by
        calc
          (11 : ZMod 10708457791) ^ 47561 = (11 : ZMod 10708457791) ^ (23780 + 23780 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 23780 * (11 : ZMod 10708457791) ^ 23780) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 1697322373 := by rw [factor_5_14]; decide
      have factor_5_16 : (11 : ZMod 10708457791) ^ 95122 = 6377550471 := by
        calc
          (11 : ZMod 10708457791) ^ 95122 = (11 : ZMod 10708457791) ^ (47561 + 47561) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 47561 * (11 : ZMod 10708457791) ^ 47561 := by rw [pow_add]
          _ = 6377550471 := by rw [factor_5_15]; decide
      have factor_5_17 : (11 : ZMod 10708457791) ^ 190244 = 1681462498 := by
        calc
          (11 : ZMod 10708457791) ^ 190244 = (11 : ZMod 10708457791) ^ (95122 + 95122) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 95122 * (11 : ZMod 10708457791) ^ 95122 := by rw [pow_add]
          _ = 1681462498 := by rw [factor_5_16]; decide
      have factor_5_18 : (11 : ZMod 10708457791) ^ 380488 = 4522454681 := by
        calc
          (11 : ZMod 10708457791) ^ 380488 = (11 : ZMod 10708457791) ^ (190244 + 190244) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 190244 * (11 : ZMod 10708457791) ^ 190244 := by rw [pow_add]
          _ = 4522454681 := by rw [factor_5_17]; decide
      have factor_5_19 : (11 : ZMod 10708457791) ^ 760976 = 41216353 := by
        calc
          (11 : ZMod 10708457791) ^ 760976 = (11 : ZMod 10708457791) ^ (380488 + 380488) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 380488 * (11 : ZMod 10708457791) ^ 380488 := by rw [pow_add]
          _ = 41216353 := by rw [factor_5_18]; decide
      have factor_5_20 : (11 : ZMod 10708457791) ^ 1521952 = 8719114160 := by
        calc
          (11 : ZMod 10708457791) ^ 1521952 = (11 : ZMod 10708457791) ^ (760976 + 760976) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 760976 * (11 : ZMod 10708457791) ^ 760976 := by rw [pow_add]
          _ = 8719114160 := by rw [factor_5_19]; decide
      have factor_5_21 : (11 : ZMod 10708457791) ^ 3043905 = 2121660413 := by
        calc
          (11 : ZMod 10708457791) ^ 3043905 = (11 : ZMod 10708457791) ^ (1521952 + 1521952 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = ((11 : ZMod 10708457791) ^ 1521952 * (11 : ZMod 10708457791) ^ 1521952) * (11 : ZMod 10708457791) := by rw [pow_succ, pow_add]
          _ = 2121660413 := by rw [factor_5_20]; decide
      have factor_5_22 : (11 : ZMod 10708457791) ^ 6087810 = 6861331076 := by
        calc
          (11 : ZMod 10708457791) ^ 6087810 = (11 : ZMod 10708457791) ^ (3043905 + 3043905) :=
            congrArg (fun n : ℕ => (11 : ZMod 10708457791) ^ n) (by norm_num)
          _ = (11 : ZMod 10708457791) ^ 3043905 * (11 : ZMod 10708457791) ^ 3043905 := by rw [pow_add]
          _ = 6861331076 := by rw [factor_5_21]; decide
      change (11 : ZMod 10708457791) ^ 6087810 ≠ 1
      rw [factor_5_22]
      decide

#print axioms prime_lucas_10708457791

end TotientTailPeriodKiller
end Erdos249257
