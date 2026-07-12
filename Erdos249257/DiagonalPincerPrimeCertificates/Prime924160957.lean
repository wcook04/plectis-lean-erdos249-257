import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime77013413

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_924160957 : Nat.Prime 924160957 := by
  apply lucas_primality 924160957 (5 : ZMod 924160957)
  ·
      have fermat_0 : (5 : ZMod 924160957) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 924160957) ^ 3 = 125 := by
        calc
          (5 : ZMod 924160957) ^ 3 = (5 : ZMod 924160957) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 1 * (5 : ZMod 924160957) ^ 1) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 924160957) ^ 6 = 15625 := by
        calc
          (5 : ZMod 924160957) ^ 6 = (5 : ZMod 924160957) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 3 * (5 : ZMod 924160957) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 924160957) ^ 13 = 296542168 := by
        calc
          (5 : ZMod 924160957) ^ 13 = (5 : ZMod 924160957) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 6 * (5 : ZMod 924160957) ^ 6) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 296542168 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 924160957) ^ 27 = 115365689 := by
        calc
          (5 : ZMod 924160957) ^ 27 = (5 : ZMod 924160957) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 13 * (5 : ZMod 924160957) ^ 13) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 115365689 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 924160957) ^ 55 = 474966700 := by
        calc
          (5 : ZMod 924160957) ^ 55 = (5 : ZMod 924160957) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 27 * (5 : ZMod 924160957) ^ 27) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 474966700 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 924160957) ^ 110 = 308592106 := by
        calc
          (5 : ZMod 924160957) ^ 110 = (5 : ZMod 924160957) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 55 * (5 : ZMod 924160957) ^ 55 := by rw [pow_add]
          _ = 308592106 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 924160957) ^ 220 = 567287055 := by
        calc
          (5 : ZMod 924160957) ^ 220 = (5 : ZMod 924160957) ^ (110 + 110) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 110 * (5 : ZMod 924160957) ^ 110 := by rw [pow_add]
          _ = 567287055 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 924160957) ^ 440 = 21762374 := by
        calc
          (5 : ZMod 924160957) ^ 440 = (5 : ZMod 924160957) ^ (220 + 220) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 220 * (5 : ZMod 924160957) ^ 220 := by rw [pow_add]
          _ = 21762374 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 924160957) ^ 881 = 189790527 := by
        calc
          (5 : ZMod 924160957) ^ 881 = (5 : ZMod 924160957) ^ (440 + 440 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 440 * (5 : ZMod 924160957) ^ 440) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 189790527 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 924160957) ^ 1762 = 118546854 := by
        calc
          (5 : ZMod 924160957) ^ 1762 = (5 : ZMod 924160957) ^ (881 + 881) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 881 * (5 : ZMod 924160957) ^ 881 := by rw [pow_add]
          _ = 118546854 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 924160957) ^ 3525 = 245731031 := by
        calc
          (5 : ZMod 924160957) ^ 3525 = (5 : ZMod 924160957) ^ (1762 + 1762 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 1762 * (5 : ZMod 924160957) ^ 1762) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 245731031 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 924160957) ^ 7050 = 689314316 := by
        calc
          (5 : ZMod 924160957) ^ 7050 = (5 : ZMod 924160957) ^ (3525 + 3525) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 3525 * (5 : ZMod 924160957) ^ 3525 := by rw [pow_add]
          _ = 689314316 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 924160957) ^ 14101 = 746635118 := by
        calc
          (5 : ZMod 924160957) ^ 14101 = (5 : ZMod 924160957) ^ (7050 + 7050 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 7050 * (5 : ZMod 924160957) ^ 7050) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 746635118 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 924160957) ^ 28203 = 162182677 := by
        calc
          (5 : ZMod 924160957) ^ 28203 = (5 : ZMod 924160957) ^ (14101 + 14101 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 14101 * (5 : ZMod 924160957) ^ 14101) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 162182677 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 924160957) ^ 56406 = 160049762 := by
        calc
          (5 : ZMod 924160957) ^ 56406 = (5 : ZMod 924160957) ^ (28203 + 28203) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 28203 * (5 : ZMod 924160957) ^ 28203 := by rw [pow_add]
          _ = 160049762 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 924160957) ^ 112812 = 564497149 := by
        calc
          (5 : ZMod 924160957) ^ 112812 = (5 : ZMod 924160957) ^ (56406 + 56406) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 56406 * (5 : ZMod 924160957) ^ 56406 := by rw [pow_add]
          _ = 564497149 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 924160957) ^ 225625 = 826610357 := by
        calc
          (5 : ZMod 924160957) ^ 225625 = (5 : ZMod 924160957) ^ (112812 + 112812 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 112812 * (5 : ZMod 924160957) ^ 112812) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 826610357 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 924160957) ^ 451250 = 916336548 := by
        calc
          (5 : ZMod 924160957) ^ 451250 = (5 : ZMod 924160957) ^ (225625 + 225625) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 225625 * (5 : ZMod 924160957) ^ 225625 := by rw [pow_add]
          _ = 916336548 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 924160957) ^ 902500 = 333602816 := by
        calc
          (5 : ZMod 924160957) ^ 902500 = (5 : ZMod 924160957) ^ (451250 + 451250) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 451250 * (5 : ZMod 924160957) ^ 451250 := by rw [pow_add]
          _ = 333602816 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 924160957) ^ 1805001 = 357747761 := by
        calc
          (5 : ZMod 924160957) ^ 1805001 = (5 : ZMod 924160957) ^ (902500 + 902500 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 902500 * (5 : ZMod 924160957) ^ 902500) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 357747761 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 924160957) ^ 3610003 = 578666287 := by
        calc
          (5 : ZMod 924160957) ^ 3610003 = (5 : ZMod 924160957) ^ (1805001 + 1805001 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 1805001 * (5 : ZMod 924160957) ^ 1805001) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 578666287 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 924160957) ^ 7220007 = 57971312 := by
        calc
          (5 : ZMod 924160957) ^ 7220007 = (5 : ZMod 924160957) ^ (3610003 + 3610003 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 3610003 * (5 : ZMod 924160957) ^ 3610003) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 57971312 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 924160957) ^ 14440014 = 509631038 := by
        calc
          (5 : ZMod 924160957) ^ 14440014 = (5 : ZMod 924160957) ^ (7220007 + 7220007) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 7220007 * (5 : ZMod 924160957) ^ 7220007 := by rw [pow_add]
          _ = 509631038 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 924160957) ^ 28880029 = 690896736 := by
        calc
          (5 : ZMod 924160957) ^ 28880029 = (5 : ZMod 924160957) ^ (14440014 + 14440014 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 14440014 * (5 : ZMod 924160957) ^ 14440014) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 690896736 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 924160957) ^ 57760059 = 331232764 := by
        calc
          (5 : ZMod 924160957) ^ 57760059 = (5 : ZMod 924160957) ^ (28880029 + 28880029 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 28880029 * (5 : ZMod 924160957) ^ 28880029) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 331232764 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 924160957) ^ 115520119 = 808404832 := by
        calc
          (5 : ZMod 924160957) ^ 115520119 = (5 : ZMod 924160957) ^ (57760059 + 57760059 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 57760059 * (5 : ZMod 924160957) ^ 57760059) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 808404832 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 924160957) ^ 231040239 = 767877551 := by
        calc
          (5 : ZMod 924160957) ^ 231040239 = (5 : ZMod 924160957) ^ (115520119 + 115520119 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 115520119 * (5 : ZMod 924160957) ^ 115520119) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 767877551 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 924160957) ^ 462080478 = 924160956 := by
        calc
          (5 : ZMod 924160957) ^ 462080478 = (5 : ZMod 924160957) ^ (231040239 + 231040239) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 231040239 * (5 : ZMod 924160957) ^ 231040239 := by rw [pow_add]
          _ = 924160956 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 924160957) ^ 924160956 = 1 := by
        calc
          (5 : ZMod 924160957) ^ 924160956 = (5 : ZMod 924160957) ^ (462080478 + 462080478) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 462080478 * (5 : ZMod 924160957) ^ 462080478 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (77013413, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (77013413, 1)] : List FactorBlock).map factorBlockValue).prod = 924160957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_77013413) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 924160957) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 924160957) ^ 3 = 125 := by
        calc
          (5 : ZMod 924160957) ^ 3 = (5 : ZMod 924160957) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 1 * (5 : ZMod 924160957) ^ 1) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 924160957) ^ 6 = 15625 := by
        calc
          (5 : ZMod 924160957) ^ 6 = (5 : ZMod 924160957) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 3 * (5 : ZMod 924160957) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 924160957) ^ 13 = 296542168 := by
        calc
          (5 : ZMod 924160957) ^ 13 = (5 : ZMod 924160957) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 6 * (5 : ZMod 924160957) ^ 6) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 296542168 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 924160957) ^ 27 = 115365689 := by
        calc
          (5 : ZMod 924160957) ^ 27 = (5 : ZMod 924160957) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 13 * (5 : ZMod 924160957) ^ 13) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 115365689 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 924160957) ^ 55 = 474966700 := by
        calc
          (5 : ZMod 924160957) ^ 55 = (5 : ZMod 924160957) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 27 * (5 : ZMod 924160957) ^ 27) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 474966700 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 924160957) ^ 110 = 308592106 := by
        calc
          (5 : ZMod 924160957) ^ 110 = (5 : ZMod 924160957) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 55 * (5 : ZMod 924160957) ^ 55 := by rw [pow_add]
          _ = 308592106 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 924160957) ^ 220 = 567287055 := by
        calc
          (5 : ZMod 924160957) ^ 220 = (5 : ZMod 924160957) ^ (110 + 110) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 110 * (5 : ZMod 924160957) ^ 110 := by rw [pow_add]
          _ = 567287055 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 924160957) ^ 440 = 21762374 := by
        calc
          (5 : ZMod 924160957) ^ 440 = (5 : ZMod 924160957) ^ (220 + 220) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 220 * (5 : ZMod 924160957) ^ 220 := by rw [pow_add]
          _ = 21762374 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 924160957) ^ 881 = 189790527 := by
        calc
          (5 : ZMod 924160957) ^ 881 = (5 : ZMod 924160957) ^ (440 + 440 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 440 * (5 : ZMod 924160957) ^ 440) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 189790527 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 924160957) ^ 1762 = 118546854 := by
        calc
          (5 : ZMod 924160957) ^ 1762 = (5 : ZMod 924160957) ^ (881 + 881) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 881 * (5 : ZMod 924160957) ^ 881 := by rw [pow_add]
          _ = 118546854 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 924160957) ^ 3525 = 245731031 := by
        calc
          (5 : ZMod 924160957) ^ 3525 = (5 : ZMod 924160957) ^ (1762 + 1762 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 1762 * (5 : ZMod 924160957) ^ 1762) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 245731031 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 924160957) ^ 7050 = 689314316 := by
        calc
          (5 : ZMod 924160957) ^ 7050 = (5 : ZMod 924160957) ^ (3525 + 3525) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 3525 * (5 : ZMod 924160957) ^ 3525 := by rw [pow_add]
          _ = 689314316 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 924160957) ^ 14101 = 746635118 := by
        calc
          (5 : ZMod 924160957) ^ 14101 = (5 : ZMod 924160957) ^ (7050 + 7050 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 7050 * (5 : ZMod 924160957) ^ 7050) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 746635118 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 924160957) ^ 28203 = 162182677 := by
        calc
          (5 : ZMod 924160957) ^ 28203 = (5 : ZMod 924160957) ^ (14101 + 14101 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 14101 * (5 : ZMod 924160957) ^ 14101) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 162182677 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 924160957) ^ 56406 = 160049762 := by
        calc
          (5 : ZMod 924160957) ^ 56406 = (5 : ZMod 924160957) ^ (28203 + 28203) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 28203 * (5 : ZMod 924160957) ^ 28203 := by rw [pow_add]
          _ = 160049762 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 924160957) ^ 112812 = 564497149 := by
        calc
          (5 : ZMod 924160957) ^ 112812 = (5 : ZMod 924160957) ^ (56406 + 56406) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 56406 * (5 : ZMod 924160957) ^ 56406 := by rw [pow_add]
          _ = 564497149 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 924160957) ^ 225625 = 826610357 := by
        calc
          (5 : ZMod 924160957) ^ 225625 = (5 : ZMod 924160957) ^ (112812 + 112812 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 112812 * (5 : ZMod 924160957) ^ 112812) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 826610357 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 924160957) ^ 451250 = 916336548 := by
        calc
          (5 : ZMod 924160957) ^ 451250 = (5 : ZMod 924160957) ^ (225625 + 225625) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 225625 * (5 : ZMod 924160957) ^ 225625 := by rw [pow_add]
          _ = 916336548 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 924160957) ^ 902500 = 333602816 := by
        calc
          (5 : ZMod 924160957) ^ 902500 = (5 : ZMod 924160957) ^ (451250 + 451250) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 451250 * (5 : ZMod 924160957) ^ 451250 := by rw [pow_add]
          _ = 333602816 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 924160957) ^ 1805001 = 357747761 := by
        calc
          (5 : ZMod 924160957) ^ 1805001 = (5 : ZMod 924160957) ^ (902500 + 902500 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 902500 * (5 : ZMod 924160957) ^ 902500) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 357747761 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 924160957) ^ 3610003 = 578666287 := by
        calc
          (5 : ZMod 924160957) ^ 3610003 = (5 : ZMod 924160957) ^ (1805001 + 1805001 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 1805001 * (5 : ZMod 924160957) ^ 1805001) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 578666287 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 924160957) ^ 7220007 = 57971312 := by
        calc
          (5 : ZMod 924160957) ^ 7220007 = (5 : ZMod 924160957) ^ (3610003 + 3610003 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 3610003 * (5 : ZMod 924160957) ^ 3610003) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 57971312 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 924160957) ^ 14440014 = 509631038 := by
        calc
          (5 : ZMod 924160957) ^ 14440014 = (5 : ZMod 924160957) ^ (7220007 + 7220007) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 7220007 * (5 : ZMod 924160957) ^ 7220007 := by rw [pow_add]
          _ = 509631038 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 924160957) ^ 28880029 = 690896736 := by
        calc
          (5 : ZMod 924160957) ^ 28880029 = (5 : ZMod 924160957) ^ (14440014 + 14440014 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 14440014 * (5 : ZMod 924160957) ^ 14440014) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 690896736 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 924160957) ^ 57760059 = 331232764 := by
        calc
          (5 : ZMod 924160957) ^ 57760059 = (5 : ZMod 924160957) ^ (28880029 + 28880029 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 28880029 * (5 : ZMod 924160957) ^ 28880029) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 331232764 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 924160957) ^ 115520119 = 808404832 := by
        calc
          (5 : ZMod 924160957) ^ 115520119 = (5 : ZMod 924160957) ^ (57760059 + 57760059 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 57760059 * (5 : ZMod 924160957) ^ 57760059) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 808404832 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 924160957) ^ 231040239 = 767877551 := by
        calc
          (5 : ZMod 924160957) ^ 231040239 = (5 : ZMod 924160957) ^ (115520119 + 115520119 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 115520119 * (5 : ZMod 924160957) ^ 115520119) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 767877551 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 924160957) ^ 462080478 = 924160956 := by
        calc
          (5 : ZMod 924160957) ^ 462080478 = (5 : ZMod 924160957) ^ (231040239 + 231040239) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 231040239 * (5 : ZMod 924160957) ^ 231040239 := by rw [pow_add]
          _ = 924160956 := by rw [factor_0_27]; decide
      change (5 : ZMod 924160957) ^ 462080478 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (5 : ZMod 924160957) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 924160957) ^ 2 = 25 := by
        calc
          (5 : ZMod 924160957) ^ 2 = (5 : ZMod 924160957) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 1 * (5 : ZMod 924160957) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 924160957) ^ 4 = 625 := by
        calc
          (5 : ZMod 924160957) ^ 4 = (5 : ZMod 924160957) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 2 * (5 : ZMod 924160957) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 924160957) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 924160957) ^ 9 = (5 : ZMod 924160957) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 4 * (5 : ZMod 924160957) ^ 4) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 924160957) ^ 18 = 684996086 := by
        calc
          (5 : ZMod 924160957) ^ 18 = (5 : ZMod 924160957) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 9 * (5 : ZMod 924160957) ^ 9 := by rw [pow_add]
          _ = 684996086 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 924160957) ^ 36 = 231758127 := by
        calc
          (5 : ZMod 924160957) ^ 36 = (5 : ZMod 924160957) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 18 * (5 : ZMod 924160957) ^ 18 := by rw [pow_add]
          _ = 231758127 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 924160957) ^ 73 = 657680303 := by
        calc
          (5 : ZMod 924160957) ^ 73 = (5 : ZMod 924160957) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 36 * (5 : ZMod 924160957) ^ 36) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 657680303 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 924160957) ^ 146 = 635078282 := by
        calc
          (5 : ZMod 924160957) ^ 146 = (5 : ZMod 924160957) ^ (73 + 73) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 73 * (5 : ZMod 924160957) ^ 73 := by rw [pow_add]
          _ = 635078282 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 924160957) ^ 293 = 450508014 := by
        calc
          (5 : ZMod 924160957) ^ 293 = (5 : ZMod 924160957) ^ (146 + 146 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 146 * (5 : ZMod 924160957) ^ 146) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 450508014 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 924160957) ^ 587 = 303135599 := by
        calc
          (5 : ZMod 924160957) ^ 587 = (5 : ZMod 924160957) ^ (293 + 293 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 293 * (5 : ZMod 924160957) ^ 293) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 303135599 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 924160957) ^ 1175 = 334745434 := by
        calc
          (5 : ZMod 924160957) ^ 1175 = (5 : ZMod 924160957) ^ (587 + 587 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 587 * (5 : ZMod 924160957) ^ 587) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 334745434 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 924160957) ^ 2350 = 637529840 := by
        calc
          (5 : ZMod 924160957) ^ 2350 = (5 : ZMod 924160957) ^ (1175 + 1175) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 1175 * (5 : ZMod 924160957) ^ 1175 := by rw [pow_add]
          _ = 637529840 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 924160957) ^ 4700 = 140537867 := by
        calc
          (5 : ZMod 924160957) ^ 4700 = (5 : ZMod 924160957) ^ (2350 + 2350) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 2350 * (5 : ZMod 924160957) ^ 2350 := by rw [pow_add]
          _ = 140537867 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 924160957) ^ 9401 = 211837246 := by
        calc
          (5 : ZMod 924160957) ^ 9401 = (5 : ZMod 924160957) ^ (4700 + 4700 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 4700 * (5 : ZMod 924160957) ^ 4700) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 211837246 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 924160957) ^ 18802 = 114621413 := by
        calc
          (5 : ZMod 924160957) ^ 18802 = (5 : ZMod 924160957) ^ (9401 + 9401) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 9401 * (5 : ZMod 924160957) ^ 9401 := by rw [pow_add]
          _ = 114621413 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 924160957) ^ 37604 = 231281685 := by
        calc
          (5 : ZMod 924160957) ^ 37604 = (5 : ZMod 924160957) ^ (18802 + 18802) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 18802 * (5 : ZMod 924160957) ^ 18802 := by rw [pow_add]
          _ = 231281685 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 924160957) ^ 75208 = 709270560 := by
        calc
          (5 : ZMod 924160957) ^ 75208 = (5 : ZMod 924160957) ^ (37604 + 37604) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 37604 * (5 : ZMod 924160957) ^ 37604 := by rw [pow_add]
          _ = 709270560 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 924160957) ^ 150416 = 410615046 := by
        calc
          (5 : ZMod 924160957) ^ 150416 = (5 : ZMod 924160957) ^ (75208 + 75208) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 75208 * (5 : ZMod 924160957) ^ 75208 := by rw [pow_add]
          _ = 410615046 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 924160957) ^ 300833 = 547775577 := by
        calc
          (5 : ZMod 924160957) ^ 300833 = (5 : ZMod 924160957) ^ (150416 + 150416 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 150416 * (5 : ZMod 924160957) ^ 150416) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 547775577 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 924160957) ^ 601667 = 917712321 := by
        calc
          (5 : ZMod 924160957) ^ 601667 = (5 : ZMod 924160957) ^ (300833 + 300833 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 300833 * (5 : ZMod 924160957) ^ 300833) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 917712321 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 924160957) ^ 1203334 = 435678367 := by
        calc
          (5 : ZMod 924160957) ^ 1203334 = (5 : ZMod 924160957) ^ (601667 + 601667) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 601667 * (5 : ZMod 924160957) ^ 601667 := by rw [pow_add]
          _ = 435678367 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 924160957) ^ 2406669 = 622207004 := by
        calc
          (5 : ZMod 924160957) ^ 2406669 = (5 : ZMod 924160957) ^ (1203334 + 1203334 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 1203334 * (5 : ZMod 924160957) ^ 1203334) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 622207004 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 924160957) ^ 4813338 = 125251001 := by
        calc
          (5 : ZMod 924160957) ^ 4813338 = (5 : ZMod 924160957) ^ (2406669 + 2406669) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 2406669 * (5 : ZMod 924160957) ^ 2406669 := by rw [pow_add]
          _ = 125251001 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 924160957) ^ 9626676 = 795040386 := by
        calc
          (5 : ZMod 924160957) ^ 9626676 = (5 : ZMod 924160957) ^ (4813338 + 4813338) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 4813338 * (5 : ZMod 924160957) ^ 4813338 := by rw [pow_add]
          _ = 795040386 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 924160957) ^ 19253353 = 826734233 := by
        calc
          (5 : ZMod 924160957) ^ 19253353 = (5 : ZMod 924160957) ^ (9626676 + 9626676 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 9626676 * (5 : ZMod 924160957) ^ 9626676) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 826734233 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 924160957) ^ 38506706 = 851959919 := by
        calc
          (5 : ZMod 924160957) ^ 38506706 = (5 : ZMod 924160957) ^ (19253353 + 19253353) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 19253353 * (5 : ZMod 924160957) ^ 19253353 := by rw [pow_add]
          _ = 851959919 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 924160957) ^ 77013413 = 681289178 := by
        calc
          (5 : ZMod 924160957) ^ 77013413 = (5 : ZMod 924160957) ^ (38506706 + 38506706 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 38506706 * (5 : ZMod 924160957) ^ 38506706) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 681289178 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 924160957) ^ 154026826 = 535576827 := by
        calc
          (5 : ZMod 924160957) ^ 154026826 = (5 : ZMod 924160957) ^ (77013413 + 77013413) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 77013413 * (5 : ZMod 924160957) ^ 77013413 := by rw [pow_add]
          _ = 535576827 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 924160957) ^ 308053652 = 535576826 := by
        calc
          (5 : ZMod 924160957) ^ 308053652 = (5 : ZMod 924160957) ^ (154026826 + 154026826) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 154026826 * (5 : ZMod 924160957) ^ 154026826 := by rw [pow_add]
          _ = 535576826 := by rw [factor_1_27]; decide
      change (5 : ZMod 924160957) ^ 308053652 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (5 : ZMod 924160957) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 924160957) ^ 3 = 125 := by
        calc
          (5 : ZMod 924160957) ^ 3 = (5 : ZMod 924160957) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = ((5 : ZMod 924160957) ^ 1 * (5 : ZMod 924160957) ^ 1) * (5 : ZMod 924160957) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 924160957) ^ 6 = 15625 := by
        calc
          (5 : ZMod 924160957) ^ 6 = (5 : ZMod 924160957) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 3 * (5 : ZMod 924160957) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 924160957) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 924160957) ^ 12 = (5 : ZMod 924160957) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 924160957) ^ n) (by norm_num)
          _ = (5 : ZMod 924160957) ^ 6 * (5 : ZMod 924160957) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_2_2]; decide
      change (5 : ZMod 924160957) ^ 12 ≠ 1
      rw [factor_2_3]
      decide

#print axioms prime_lucas_924160957

end TotientTailPeriodKiller
end Erdos249257
