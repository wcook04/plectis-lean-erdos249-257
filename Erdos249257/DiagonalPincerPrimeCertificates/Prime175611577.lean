import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_175611577 : Nat.Prime 175611577 := by
  apply lucas_primality 175611577 (5 : ZMod 175611577)
  ·
      have fermat_0 : (5 : ZMod 175611577) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 175611577) ^ 2 = 25 := by
        calc
          (5 : ZMod 175611577) ^ 2 = (5 : ZMod 175611577) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 1 * (5 : ZMod 175611577) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 175611577) ^ 5 = 3125 := by
        calc
          (5 : ZMod 175611577) ^ 5 = (5 : ZMod 175611577) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 2 * (5 : ZMod 175611577) ^ 2) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 175611577) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 175611577) ^ 10 = (5 : ZMod 175611577) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 5 * (5 : ZMod 175611577) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 175611577) ^ 20 = 159858159 := by
        calc
          (5 : ZMod 175611577) ^ 20 = (5 : ZMod 175611577) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 10 * (5 : ZMod 175611577) ^ 10 := by rw [pow_add]
          _ = 159858159 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 175611577) ^ 41 = 36886129 := by
        calc
          (5 : ZMod 175611577) ^ 41 = (5 : ZMod 175611577) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 20 * (5 : ZMod 175611577) ^ 20) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 36886129 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 175611577) ^ 83 = 150788742 := by
        calc
          (5 : ZMod 175611577) ^ 83 = (5 : ZMod 175611577) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 41 * (5 : ZMod 175611577) ^ 41) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 150788742 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 175611577) ^ 167 = 102912153 := by
        calc
          (5 : ZMod 175611577) ^ 167 = (5 : ZMod 175611577) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 83 * (5 : ZMod 175611577) ^ 83) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 102912153 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 175611577) ^ 334 = 52928199 := by
        calc
          (5 : ZMod 175611577) ^ 334 = (5 : ZMod 175611577) ^ (167 + 167) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 167 * (5 : ZMod 175611577) ^ 167 := by rw [pow_add]
          _ = 52928199 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 175611577) ^ 669 = 97555921 := by
        calc
          (5 : ZMod 175611577) ^ 669 = (5 : ZMod 175611577) ^ (334 + 334 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 334 * (5 : ZMod 175611577) ^ 334) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 97555921 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 175611577) ^ 1339 = 153642642 := by
        calc
          (5 : ZMod 175611577) ^ 1339 = (5 : ZMod 175611577) ^ (669 + 669 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 669 * (5 : ZMod 175611577) ^ 669) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 153642642 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 175611577) ^ 2679 = 759354 := by
        calc
          (5 : ZMod 175611577) ^ 2679 = (5 : ZMod 175611577) ^ (1339 + 1339 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 1339 * (5 : ZMod 175611577) ^ 1339) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 759354 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 175611577) ^ 5359 = 77226971 := by
        calc
          (5 : ZMod 175611577) ^ 5359 = (5 : ZMod 175611577) ^ (2679 + 2679 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 2679 * (5 : ZMod 175611577) ^ 2679) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 77226971 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 175611577) ^ 10718 = 48566930 := by
        calc
          (5 : ZMod 175611577) ^ 10718 = (5 : ZMod 175611577) ^ (5359 + 5359) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 5359 * (5 : ZMod 175611577) ^ 5359 := by rw [pow_add]
          _ = 48566930 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 175611577) ^ 21436 = 124652776 := by
        calc
          (5 : ZMod 175611577) ^ 21436 = (5 : ZMod 175611577) ^ (10718 + 10718) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 10718 * (5 : ZMod 175611577) ^ 10718 := by rw [pow_add]
          _ = 124652776 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 175611577) ^ 42873 = 161882091 := by
        calc
          (5 : ZMod 175611577) ^ 42873 = (5 : ZMod 175611577) ^ (21436 + 21436 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 21436 * (5 : ZMod 175611577) ^ 21436) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 161882091 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 175611577) ^ 85747 = 117453409 := by
        calc
          (5 : ZMod 175611577) ^ 85747 = (5 : ZMod 175611577) ^ (42873 + 42873 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 42873 * (5 : ZMod 175611577) ^ 42873) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 117453409 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 175611577) ^ 171495 = 6851569 := by
        calc
          (5 : ZMod 175611577) ^ 171495 = (5 : ZMod 175611577) ^ (85747 + 85747 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 85747 * (5 : ZMod 175611577) ^ 85747) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 6851569 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 175611577) ^ 342991 = 13552683 := by
        calc
          (5 : ZMod 175611577) ^ 342991 = (5 : ZMod 175611577) ^ (171495 + 171495 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 171495 * (5 : ZMod 175611577) ^ 171495) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 13552683 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 175611577) ^ 685982 = 82717380 := by
        calc
          (5 : ZMod 175611577) ^ 685982 = (5 : ZMod 175611577) ^ (342991 + 342991) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 342991 * (5 : ZMod 175611577) ^ 342991 := by rw [pow_add]
          _ = 82717380 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 175611577) ^ 1371965 = 11739683 := by
        calc
          (5 : ZMod 175611577) ^ 1371965 = (5 : ZMod 175611577) ^ (685982 + 685982 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 685982 * (5 : ZMod 175611577) ^ 685982) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 11739683 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 175611577) ^ 2743930 = 15699312 := by
        calc
          (5 : ZMod 175611577) ^ 2743930 = (5 : ZMod 175611577) ^ (1371965 + 1371965) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 1371965 * (5 : ZMod 175611577) ^ 1371965 := by rw [pow_add]
          _ = 15699312 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 175611577) ^ 5487861 = 37579610 := by
        calc
          (5 : ZMod 175611577) ^ 5487861 = (5 : ZMod 175611577) ^ (2743930 + 2743930 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 2743930 * (5 : ZMod 175611577) ^ 2743930) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 37579610 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 175611577) ^ 10975723 = 95581898 := by
        calc
          (5 : ZMod 175611577) ^ 10975723 = (5 : ZMod 175611577) ^ (5487861 + 5487861 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 5487861 * (5 : ZMod 175611577) ^ 5487861) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 95581898 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 175611577) ^ 21951447 = 137897085 := by
        calc
          (5 : ZMod 175611577) ^ 21951447 = (5 : ZMod 175611577) ^ (10975723 + 10975723 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 10975723 * (5 : ZMod 175611577) ^ 10975723) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 137897085 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 175611577) ^ 43902894 = 80195172 := by
        calc
          (5 : ZMod 175611577) ^ 43902894 = (5 : ZMod 175611577) ^ (21951447 + 21951447) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 21951447 * (5 : ZMod 175611577) ^ 21951447 := by rw [pow_add]
          _ = 80195172 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 175611577) ^ 87805788 = 175611576 := by
        calc
          (5 : ZMod 175611577) ^ 87805788 = (5 : ZMod 175611577) ^ (43902894 + 43902894) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 43902894 * (5 : ZMod 175611577) ^ 43902894 := by rw [pow_add]
          _ = 175611576 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 175611577) ^ 175611576 = 1 := by
        calc
          (5 : ZMod 175611577) ^ 175611576 = (5 : ZMod 175611577) ^ (87805788 + 87805788) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 87805788 * (5 : ZMod 175611577) ^ 87805788 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (1045307, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (1045307, 1)] : List FactorBlock).map factorBlockValue).prod = 175611577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 175611577) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 175611577) ^ 2 = 25 := by
        calc
          (5 : ZMod 175611577) ^ 2 = (5 : ZMod 175611577) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 1 * (5 : ZMod 175611577) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 175611577) ^ 5 = 3125 := by
        calc
          (5 : ZMod 175611577) ^ 5 = (5 : ZMod 175611577) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 2 * (5 : ZMod 175611577) ^ 2) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 175611577) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 175611577) ^ 10 = (5 : ZMod 175611577) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 5 * (5 : ZMod 175611577) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 175611577) ^ 20 = 159858159 := by
        calc
          (5 : ZMod 175611577) ^ 20 = (5 : ZMod 175611577) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 10 * (5 : ZMod 175611577) ^ 10 := by rw [pow_add]
          _ = 159858159 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 175611577) ^ 41 = 36886129 := by
        calc
          (5 : ZMod 175611577) ^ 41 = (5 : ZMod 175611577) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 20 * (5 : ZMod 175611577) ^ 20) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 36886129 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 175611577) ^ 83 = 150788742 := by
        calc
          (5 : ZMod 175611577) ^ 83 = (5 : ZMod 175611577) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 41 * (5 : ZMod 175611577) ^ 41) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 150788742 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 175611577) ^ 167 = 102912153 := by
        calc
          (5 : ZMod 175611577) ^ 167 = (5 : ZMod 175611577) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 83 * (5 : ZMod 175611577) ^ 83) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 102912153 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 175611577) ^ 334 = 52928199 := by
        calc
          (5 : ZMod 175611577) ^ 334 = (5 : ZMod 175611577) ^ (167 + 167) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 167 * (5 : ZMod 175611577) ^ 167 := by rw [pow_add]
          _ = 52928199 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 175611577) ^ 669 = 97555921 := by
        calc
          (5 : ZMod 175611577) ^ 669 = (5 : ZMod 175611577) ^ (334 + 334 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 334 * (5 : ZMod 175611577) ^ 334) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 97555921 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 175611577) ^ 1339 = 153642642 := by
        calc
          (5 : ZMod 175611577) ^ 1339 = (5 : ZMod 175611577) ^ (669 + 669 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 669 * (5 : ZMod 175611577) ^ 669) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 153642642 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 175611577) ^ 2679 = 759354 := by
        calc
          (5 : ZMod 175611577) ^ 2679 = (5 : ZMod 175611577) ^ (1339 + 1339 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 1339 * (5 : ZMod 175611577) ^ 1339) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 759354 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 175611577) ^ 5359 = 77226971 := by
        calc
          (5 : ZMod 175611577) ^ 5359 = (5 : ZMod 175611577) ^ (2679 + 2679 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 2679 * (5 : ZMod 175611577) ^ 2679) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 77226971 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 175611577) ^ 10718 = 48566930 := by
        calc
          (5 : ZMod 175611577) ^ 10718 = (5 : ZMod 175611577) ^ (5359 + 5359) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 5359 * (5 : ZMod 175611577) ^ 5359 := by rw [pow_add]
          _ = 48566930 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 175611577) ^ 21436 = 124652776 := by
        calc
          (5 : ZMod 175611577) ^ 21436 = (5 : ZMod 175611577) ^ (10718 + 10718) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 10718 * (5 : ZMod 175611577) ^ 10718 := by rw [pow_add]
          _ = 124652776 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 175611577) ^ 42873 = 161882091 := by
        calc
          (5 : ZMod 175611577) ^ 42873 = (5 : ZMod 175611577) ^ (21436 + 21436 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 21436 * (5 : ZMod 175611577) ^ 21436) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 161882091 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 175611577) ^ 85747 = 117453409 := by
        calc
          (5 : ZMod 175611577) ^ 85747 = (5 : ZMod 175611577) ^ (42873 + 42873 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 42873 * (5 : ZMod 175611577) ^ 42873) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 117453409 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 175611577) ^ 171495 = 6851569 := by
        calc
          (5 : ZMod 175611577) ^ 171495 = (5 : ZMod 175611577) ^ (85747 + 85747 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 85747 * (5 : ZMod 175611577) ^ 85747) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 6851569 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 175611577) ^ 342991 = 13552683 := by
        calc
          (5 : ZMod 175611577) ^ 342991 = (5 : ZMod 175611577) ^ (171495 + 171495 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 171495 * (5 : ZMod 175611577) ^ 171495) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 13552683 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 175611577) ^ 685982 = 82717380 := by
        calc
          (5 : ZMod 175611577) ^ 685982 = (5 : ZMod 175611577) ^ (342991 + 342991) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 342991 * (5 : ZMod 175611577) ^ 342991 := by rw [pow_add]
          _ = 82717380 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 175611577) ^ 1371965 = 11739683 := by
        calc
          (5 : ZMod 175611577) ^ 1371965 = (5 : ZMod 175611577) ^ (685982 + 685982 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 685982 * (5 : ZMod 175611577) ^ 685982) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 11739683 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 175611577) ^ 2743930 = 15699312 := by
        calc
          (5 : ZMod 175611577) ^ 2743930 = (5 : ZMod 175611577) ^ (1371965 + 1371965) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 1371965 * (5 : ZMod 175611577) ^ 1371965 := by rw [pow_add]
          _ = 15699312 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 175611577) ^ 5487861 = 37579610 := by
        calc
          (5 : ZMod 175611577) ^ 5487861 = (5 : ZMod 175611577) ^ (2743930 + 2743930 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 2743930 * (5 : ZMod 175611577) ^ 2743930) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 37579610 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 175611577) ^ 10975723 = 95581898 := by
        calc
          (5 : ZMod 175611577) ^ 10975723 = (5 : ZMod 175611577) ^ (5487861 + 5487861 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 5487861 * (5 : ZMod 175611577) ^ 5487861) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 95581898 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 175611577) ^ 21951447 = 137897085 := by
        calc
          (5 : ZMod 175611577) ^ 21951447 = (5 : ZMod 175611577) ^ (10975723 + 10975723 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 10975723 * (5 : ZMod 175611577) ^ 10975723) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 137897085 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 175611577) ^ 43902894 = 80195172 := by
        calc
          (5 : ZMod 175611577) ^ 43902894 = (5 : ZMod 175611577) ^ (21951447 + 21951447) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 21951447 * (5 : ZMod 175611577) ^ 21951447 := by rw [pow_add]
          _ = 80195172 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 175611577) ^ 87805788 = 175611576 := by
        calc
          (5 : ZMod 175611577) ^ 87805788 = (5 : ZMod 175611577) ^ (43902894 + 43902894) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 43902894 * (5 : ZMod 175611577) ^ 43902894 := by rw [pow_add]
          _ = 175611576 := by rw [factor_0_25]; decide
      change (5 : ZMod 175611577) ^ 87805788 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (5 : ZMod 175611577) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 175611577) ^ 3 = 125 := by
        calc
          (5 : ZMod 175611577) ^ 3 = (5 : ZMod 175611577) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 1 * (5 : ZMod 175611577) ^ 1) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 175611577) ^ 6 = 15625 := by
        calc
          (5 : ZMod 175611577) ^ 6 = (5 : ZMod 175611577) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 3 * (5 : ZMod 175611577) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 175611577) ^ 13 = 167033663 := by
        calc
          (5 : ZMod 175611577) ^ 13 = (5 : ZMod 175611577) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 6 * (5 : ZMod 175611577) ^ 6) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 167033663 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 175611577) ^ 27 = 125761943 := by
        calc
          (5 : ZMod 175611577) ^ 27 = (5 : ZMod 175611577) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 13 * (5 : ZMod 175611577) ^ 13) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 125761943 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 175611577) ^ 55 = 45829600 := by
        calc
          (5 : ZMod 175611577) ^ 55 = (5 : ZMod 175611577) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 27 * (5 : ZMod 175611577) ^ 27) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 45829600 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 175611577) ^ 111 = 93754725 := by
        calc
          (5 : ZMod 175611577) ^ 111 = (5 : ZMod 175611577) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 55 * (5 : ZMod 175611577) ^ 55) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 93754725 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 175611577) ^ 223 = 148731835 := by
        calc
          (5 : ZMod 175611577) ^ 223 = (5 : ZMod 175611577) ^ (111 + 111 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 111 * (5 : ZMod 175611577) ^ 111) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 148731835 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 175611577) ^ 446 = 62619694 := by
        calc
          (5 : ZMod 175611577) ^ 446 = (5 : ZMod 175611577) ^ (223 + 223) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 223 * (5 : ZMod 175611577) ^ 223 := by rw [pow_add]
          _ = 62619694 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 175611577) ^ 893 = 103500806 := by
        calc
          (5 : ZMod 175611577) ^ 893 = (5 : ZMod 175611577) ^ (446 + 446 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 446 * (5 : ZMod 175611577) ^ 446) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 103500806 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 175611577) ^ 1786 = 10356126 := by
        calc
          (5 : ZMod 175611577) ^ 1786 = (5 : ZMod 175611577) ^ (893 + 893) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 893 * (5 : ZMod 175611577) ^ 893 := by rw [pow_add]
          _ = 10356126 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 175611577) ^ 3572 = 19034013 := by
        calc
          (5 : ZMod 175611577) ^ 3572 = (5 : ZMod 175611577) ^ (1786 + 1786) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 1786 * (5 : ZMod 175611577) ^ 1786 := by rw [pow_add]
          _ = 19034013 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 175611577) ^ 7145 = 66573599 := by
        calc
          (5 : ZMod 175611577) ^ 7145 = (5 : ZMod 175611577) ^ (3572 + 3572 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 3572 * (5 : ZMod 175611577) ^ 3572) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 66573599 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 175611577) ^ 14291 = 104921210 := by
        calc
          (5 : ZMod 175611577) ^ 14291 = (5 : ZMod 175611577) ^ (7145 + 7145 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 7145 * (5 : ZMod 175611577) ^ 7145) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 104921210 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 175611577) ^ 28582 = 113237645 := by
        calc
          (5 : ZMod 175611577) ^ 28582 = (5 : ZMod 175611577) ^ (14291 + 14291) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 14291 * (5 : ZMod 175611577) ^ 14291 := by rw [pow_add]
          _ = 113237645 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 175611577) ^ 57165 = 83411486 := by
        calc
          (5 : ZMod 175611577) ^ 57165 = (5 : ZMod 175611577) ^ (28582 + 28582 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 28582 * (5 : ZMod 175611577) ^ 28582) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 83411486 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 175611577) ^ 114330 = 128386423 := by
        calc
          (5 : ZMod 175611577) ^ 114330 = (5 : ZMod 175611577) ^ (57165 + 57165) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 57165 * (5 : ZMod 175611577) ^ 57165 := by rw [pow_add]
          _ = 128386423 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 175611577) ^ 228660 = 123450508 := by
        calc
          (5 : ZMod 175611577) ^ 228660 = (5 : ZMod 175611577) ^ (114330 + 114330) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 114330 * (5 : ZMod 175611577) ^ 114330 := by rw [pow_add]
          _ = 123450508 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 175611577) ^ 457321 = 89729246 := by
        calc
          (5 : ZMod 175611577) ^ 457321 = (5 : ZMod 175611577) ^ (228660 + 228660 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 228660 * (5 : ZMod 175611577) ^ 228660) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 89729246 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 175611577) ^ 914643 = 3182188 := by
        calc
          (5 : ZMod 175611577) ^ 914643 = (5 : ZMod 175611577) ^ (457321 + 457321 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 457321 * (5 : ZMod 175611577) ^ 457321) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 3182188 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 175611577) ^ 1829287 = 150513965 := by
        calc
          (5 : ZMod 175611577) ^ 1829287 = (5 : ZMod 175611577) ^ (914643 + 914643 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 914643 * (5 : ZMod 175611577) ^ 914643) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 150513965 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 175611577) ^ 3658574 = 26090595 := by
        calc
          (5 : ZMod 175611577) ^ 3658574 = (5 : ZMod 175611577) ^ (1829287 + 1829287) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 1829287 * (5 : ZMod 175611577) ^ 1829287 := by rw [pow_add]
          _ = 26090595 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 175611577) ^ 7317149 = 152975980 := by
        calc
          (5 : ZMod 175611577) ^ 7317149 = (5 : ZMod 175611577) ^ (3658574 + 3658574 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 3658574 * (5 : ZMod 175611577) ^ 3658574) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 152975980 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 175611577) ^ 14634298 = 119309168 := by
        calc
          (5 : ZMod 175611577) ^ 14634298 = (5 : ZMod 175611577) ^ (7317149 + 7317149) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 7317149 * (5 : ZMod 175611577) ^ 7317149 := by rw [pow_add]
          _ = 119309168 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 175611577) ^ 29268596 = 19396244 := by
        calc
          (5 : ZMod 175611577) ^ 29268596 = (5 : ZMod 175611577) ^ (14634298 + 14634298) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 14634298 * (5 : ZMod 175611577) ^ 14634298 := by rw [pow_add]
          _ = 19396244 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 175611577) ^ 58537192 = 19396243 := by
        calc
          (5 : ZMod 175611577) ^ 58537192 = (5 : ZMod 175611577) ^ (29268596 + 29268596) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 29268596 * (5 : ZMod 175611577) ^ 29268596 := by rw [pow_add]
          _ = 19396243 := by rw [factor_1_24]; decide
      change (5 : ZMod 175611577) ^ 58537192 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (5 : ZMod 175611577) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 175611577) ^ 2 = 25 := by
        calc
          (5 : ZMod 175611577) ^ 2 = (5 : ZMod 175611577) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 1 * (5 : ZMod 175611577) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 175611577) ^ 5 = 3125 := by
        calc
          (5 : ZMod 175611577) ^ 5 = (5 : ZMod 175611577) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 2 * (5 : ZMod 175611577) ^ 2) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 175611577) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 175611577) ^ 11 = (5 : ZMod 175611577) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 5 * (5 : ZMod 175611577) ^ 5) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 175611577) ^ 23 = 138161674 := by
        calc
          (5 : ZMod 175611577) ^ 23 = (5 : ZMod 175611577) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 11 * (5 : ZMod 175611577) ^ 11) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 138161674 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 175611577) ^ 47 = 164181488 := by
        calc
          (5 : ZMod 175611577) ^ 47 = (5 : ZMod 175611577) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 23 * (5 : ZMod 175611577) ^ 23) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 164181488 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 175611577) ^ 95 = 172573892 := by
        calc
          (5 : ZMod 175611577) ^ 95 = (5 : ZMod 175611577) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 47 * (5 : ZMod 175611577) ^ 47) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 172573892 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 175611577) ^ 191 = 99228800 := by
        calc
          (5 : ZMod 175611577) ^ 191 = (5 : ZMod 175611577) ^ (95 + 95 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 95 * (5 : ZMod 175611577) ^ 95) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 99228800 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 175611577) ^ 382 = 126544774 := by
        calc
          (5 : ZMod 175611577) ^ 382 = (5 : ZMod 175611577) ^ (191 + 191) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 191 * (5 : ZMod 175611577) ^ 191 := by rw [pow_add]
          _ = 126544774 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 175611577) ^ 765 = 135407305 := by
        calc
          (5 : ZMod 175611577) ^ 765 = (5 : ZMod 175611577) ^ (382 + 382 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 382 * (5 : ZMod 175611577) ^ 382) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 135407305 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 175611577) ^ 1531 = 112542416 := by
        calc
          (5 : ZMod 175611577) ^ 1531 = (5 : ZMod 175611577) ^ (765 + 765 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 765 * (5 : ZMod 175611577) ^ 765) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 112542416 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 175611577) ^ 3062 = 68495216 := by
        calc
          (5 : ZMod 175611577) ^ 3062 = (5 : ZMod 175611577) ^ (1531 + 1531) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 1531 * (5 : ZMod 175611577) ^ 1531 := by rw [pow_add]
          _ = 68495216 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 175611577) ^ 6124 = 153483637 := by
        calc
          (5 : ZMod 175611577) ^ 6124 = (5 : ZMod 175611577) ^ (3062 + 3062) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 3062 * (5 : ZMod 175611577) ^ 3062 := by rw [pow_add]
          _ = 153483637 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 175611577) ^ 12249 = 77243411 := by
        calc
          (5 : ZMod 175611577) ^ 12249 = (5 : ZMod 175611577) ^ (6124 + 6124 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 6124 * (5 : ZMod 175611577) ^ 6124) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 77243411 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 175611577) ^ 24499 = 113160065 := by
        calc
          (5 : ZMod 175611577) ^ 24499 = (5 : ZMod 175611577) ^ (12249 + 12249 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 12249 * (5 : ZMod 175611577) ^ 12249) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 113160065 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 175611577) ^ 48998 = 120070360 := by
        calc
          (5 : ZMod 175611577) ^ 48998 = (5 : ZMod 175611577) ^ (24499 + 24499) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 24499 * (5 : ZMod 175611577) ^ 24499 := by rw [pow_add]
          _ = 120070360 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 175611577) ^ 97997 = 7346794 := by
        calc
          (5 : ZMod 175611577) ^ 97997 = (5 : ZMod 175611577) ^ (48998 + 48998 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 48998 * (5 : ZMod 175611577) ^ 48998) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 7346794 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 175611577) ^ 195995 = 24255389 := by
        calc
          (5 : ZMod 175611577) ^ 195995 = (5 : ZMod 175611577) ^ (97997 + 97997 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 97997 * (5 : ZMod 175611577) ^ 97997) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 24255389 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 175611577) ^ 391990 = 135810 := by
        calc
          (5 : ZMod 175611577) ^ 391990 = (5 : ZMod 175611577) ^ (195995 + 195995) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 195995 * (5 : ZMod 175611577) ^ 195995 := by rw [pow_add]
          _ = 135810 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 175611577) ^ 783980 = 5140515 := by
        calc
          (5 : ZMod 175611577) ^ 783980 = (5 : ZMod 175611577) ^ (391990 + 391990) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 391990 * (5 : ZMod 175611577) ^ 391990 := by rw [pow_add]
          _ = 5140515 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 175611577) ^ 1567960 = 93639304 := by
        calc
          (5 : ZMod 175611577) ^ 1567960 = (5 : ZMod 175611577) ^ (783980 + 783980) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 783980 * (5 : ZMod 175611577) ^ 783980 := by rw [pow_add]
          _ = 93639304 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 175611577) ^ 3135921 = 117031815 := by
        calc
          (5 : ZMod 175611577) ^ 3135921 = (5 : ZMod 175611577) ^ (1567960 + 1567960 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 1567960 * (5 : ZMod 175611577) ^ 1567960) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 117031815 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 175611577) ^ 6271842 = 95085545 := by
        calc
          (5 : ZMod 175611577) ^ 6271842 = (5 : ZMod 175611577) ^ (3135921 + 3135921) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 3135921 * (5 : ZMod 175611577) ^ 3135921 := by rw [pow_add]
          _ = 95085545 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 175611577) ^ 12543684 = 153981954 := by
        calc
          (5 : ZMod 175611577) ^ 12543684 = (5 : ZMod 175611577) ^ (6271842 + 6271842) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 6271842 * (5 : ZMod 175611577) ^ 6271842 := by rw [pow_add]
          _ = 153981954 := by rw [factor_2_22]; decide
      have factor_2_24 : (5 : ZMod 175611577) ^ 25087368 = 110853201 := by
        calc
          (5 : ZMod 175611577) ^ 25087368 = (5 : ZMod 175611577) ^ (12543684 + 12543684) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 12543684 * (5 : ZMod 175611577) ^ 12543684 := by rw [pow_add]
          _ = 110853201 := by rw [factor_2_23]; decide
      change (5 : ZMod 175611577) ^ 25087368 ≠ 1
      rw [factor_2_24]
      decide
    ·
      have factor_3_0 : (5 : ZMod 175611577) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 175611577) ^ 2 = 25 := by
        calc
          (5 : ZMod 175611577) ^ 2 = (5 : ZMod 175611577) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 1 * (5 : ZMod 175611577) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 175611577) ^ 5 = 3125 := by
        calc
          (5 : ZMod 175611577) ^ 5 = (5 : ZMod 175611577) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 2 * (5 : ZMod 175611577) ^ 2) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 175611577) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 175611577) ^ 10 = (5 : ZMod 175611577) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 5 * (5 : ZMod 175611577) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 175611577) ^ 21 = 96844487 := by
        calc
          (5 : ZMod 175611577) ^ 21 = (5 : ZMod 175611577) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = ((5 : ZMod 175611577) ^ 10 * (5 : ZMod 175611577) ^ 10) * (5 : ZMod 175611577) := by rw [pow_succ, pow_add]
          _ = 96844487 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 175611577) ^ 42 = 8819068 := by
        calc
          (5 : ZMod 175611577) ^ 42 = (5 : ZMod 175611577) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 21 * (5 : ZMod 175611577) ^ 21 := by rw [pow_add]
          _ = 8819068 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 175611577) ^ 84 = 51497402 := by
        calc
          (5 : ZMod 175611577) ^ 84 = (5 : ZMod 175611577) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 42 * (5 : ZMod 175611577) ^ 42 := by rw [pow_add]
          _ = 51497402 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 175611577) ^ 168 = 163337611 := by
        calc
          (5 : ZMod 175611577) ^ 168 = (5 : ZMod 175611577) ^ (84 + 84) :=
            congrArg (fun n : ℕ => (5 : ZMod 175611577) ^ n) (by norm_num)
          _ = (5 : ZMod 175611577) ^ 84 * (5 : ZMod 175611577) ^ 84 := by rw [pow_add]
          _ = 163337611 := by rw [factor_3_6]; decide
      change (5 : ZMod 175611577) ^ 168 ≠ 1
      rw [factor_3_7]
      decide

#print axioms prime_lucas_175611577

end TotientTailPeriodKiller
end Erdos249257
