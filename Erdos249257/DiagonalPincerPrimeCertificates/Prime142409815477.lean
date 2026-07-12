import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime11867484623

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_142409815477 : Nat.Prime 142409815477 := by
  apply lucas_primality 142409815477 (2 : ZMod 142409815477)
  ·
      have fermat_0 : (2 : ZMod 142409815477) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 142409815477) ^ 2 = 4 := by
        calc
          (2 : ZMod 142409815477) ^ 2 = (2 : ZMod 142409815477) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 1 * (2 : ZMod 142409815477) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 142409815477) ^ 4 = 16 := by
        calc
          (2 : ZMod 142409815477) ^ 4 = (2 : ZMod 142409815477) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 2 * (2 : ZMod 142409815477) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 142409815477) ^ 8 = 256 := by
        calc
          (2 : ZMod 142409815477) ^ 8 = (2 : ZMod 142409815477) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 4 * (2 : ZMod 142409815477) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 142409815477) ^ 16 = 65536 := by
        calc
          (2 : ZMod 142409815477) ^ 16 = (2 : ZMod 142409815477) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 8 * (2 : ZMod 142409815477) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 142409815477) ^ 33 = 8589934592 := by
        calc
          (2 : ZMod 142409815477) ^ 33 = (2 : ZMod 142409815477) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 16 * (2 : ZMod 142409815477) ^ 16) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 8589934592 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 142409815477) ^ 66 = 19831588306 := by
        calc
          (2 : ZMod 142409815477) ^ 66 = (2 : ZMod 142409815477) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 33 * (2 : ZMod 142409815477) ^ 33 := by rw [pow_add]
          _ = 19831588306 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 142409815477) ^ 132 = 132149949842 := by
        calc
          (2 : ZMod 142409815477) ^ 132 = (2 : ZMod 142409815477) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 66 * (2 : ZMod 142409815477) ^ 66 := by rw [pow_add]
          _ = 132149949842 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 142409815477) ^ 265 = 127438258719 := by
        calc
          (2 : ZMod 142409815477) ^ 265 = (2 : ZMod 142409815477) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 132 * (2 : ZMod 142409815477) ^ 132) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 127438258719 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 142409815477) ^ 530 = 87711924663 := by
        calc
          (2 : ZMod 142409815477) ^ 530 = (2 : ZMod 142409815477) ^ (265 + 265) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 265 * (2 : ZMod 142409815477) ^ 265 := by rw [pow_add]
          _ = 87711924663 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 142409815477) ^ 1061 = 48049596962 := by
        calc
          (2 : ZMod 142409815477) ^ 1061 = (2 : ZMod 142409815477) ^ (530 + 530 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 530 * (2 : ZMod 142409815477) ^ 530) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 48049596962 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 142409815477) ^ 2122 = 23379384642 := by
        calc
          (2 : ZMod 142409815477) ^ 2122 = (2 : ZMod 142409815477) ^ (1061 + 1061) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 1061 * (2 : ZMod 142409815477) ^ 1061 := by rw [pow_add]
          _ = 23379384642 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 142409815477) ^ 4244 = 48235619651 := by
        calc
          (2 : ZMod 142409815477) ^ 4244 = (2 : ZMod 142409815477) ^ (2122 + 2122) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 2122 * (2 : ZMod 142409815477) ^ 2122 := by rw [pow_add]
          _ = 48235619651 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 142409815477) ^ 8488 = 114251336901 := by
        calc
          (2 : ZMod 142409815477) ^ 8488 = (2 : ZMod 142409815477) ^ (4244 + 4244) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 4244 * (2 : ZMod 142409815477) ^ 4244 := by rw [pow_add]
          _ = 114251336901 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 142409815477) ^ 16976 = 117089352237 := by
        calc
          (2 : ZMod 142409815477) ^ 16976 = (2 : ZMod 142409815477) ^ (8488 + 8488) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 8488 * (2 : ZMod 142409815477) ^ 8488 := by rw [pow_add]
          _ = 117089352237 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 142409815477) ^ 33953 = 11421856982 := by
        calc
          (2 : ZMod 142409815477) ^ 33953 = (2 : ZMod 142409815477) ^ (16976 + 16976 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 16976 * (2 : ZMod 142409815477) ^ 16976) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 11421856982 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 142409815477) ^ 67906 = 116014797660 := by
        calc
          (2 : ZMod 142409815477) ^ 67906 = (2 : ZMod 142409815477) ^ (33953 + 33953) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 33953 * (2 : ZMod 142409815477) ^ 33953 := by rw [pow_add]
          _ = 116014797660 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 142409815477) ^ 135812 = 91775523577 := by
        calc
          (2 : ZMod 142409815477) ^ 135812 = (2 : ZMod 142409815477) ^ (67906 + 67906) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 67906 * (2 : ZMod 142409815477) ^ 67906 := by rw [pow_add]
          _ = 91775523577 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 142409815477) ^ 271625 = 91013953744 := by
        calc
          (2 : ZMod 142409815477) ^ 271625 = (2 : ZMod 142409815477) ^ (135812 + 135812 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 135812 * (2 : ZMod 142409815477) ^ 135812) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 91013953744 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 142409815477) ^ 543250 = 122304715289 := by
        calc
          (2 : ZMod 142409815477) ^ 543250 = (2 : ZMod 142409815477) ^ (271625 + 271625) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 271625 * (2 : ZMod 142409815477) ^ 271625 := by rw [pow_add]
          _ = 122304715289 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 142409815477) ^ 1086500 = 139838108697 := by
        calc
          (2 : ZMod 142409815477) ^ 1086500 = (2 : ZMod 142409815477) ^ (543250 + 543250) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 543250 * (2 : ZMod 142409815477) ^ 543250 := by rw [pow_add]
          _ = 139838108697 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 142409815477) ^ 2173001 = 35696948746 := by
        calc
          (2 : ZMod 142409815477) ^ 2173001 = (2 : ZMod 142409815477) ^ (1086500 + 1086500 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 1086500 * (2 : ZMod 142409815477) ^ 1086500) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 35696948746 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 142409815477) ^ 4346002 = 141798522454 := by
        calc
          (2 : ZMod 142409815477) ^ 4346002 = (2 : ZMod 142409815477) ^ (2173001 + 2173001) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 2173001 * (2 : ZMod 142409815477) ^ 2173001 := by rw [pow_add]
          _ = 141798522454 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 142409815477) ^ 8692005 = 10492774201 := by
        calc
          (2 : ZMod 142409815477) ^ 8692005 = (2 : ZMod 142409815477) ^ (4346002 + 4346002 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 4346002 * (2 : ZMod 142409815477) ^ 4346002) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 10492774201 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 142409815477) ^ 17384010 = 114743564447 := by
        calc
          (2 : ZMod 142409815477) ^ 17384010 = (2 : ZMod 142409815477) ^ (8692005 + 8692005) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 8692005 * (2 : ZMod 142409815477) ^ 8692005 := by rw [pow_add]
          _ = 114743564447 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 142409815477) ^ 34768021 = 21328686119 := by
        calc
          (2 : ZMod 142409815477) ^ 34768021 = (2 : ZMod 142409815477) ^ (17384010 + 17384010 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 17384010 * (2 : ZMod 142409815477) ^ 17384010) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 21328686119 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 142409815477) ^ 69536042 = 92367017966 := by
        calc
          (2 : ZMod 142409815477) ^ 69536042 = (2 : ZMod 142409815477) ^ (34768021 + 34768021) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 34768021 * (2 : ZMod 142409815477) ^ 34768021 := by rw [pow_add]
          _ = 92367017966 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 142409815477) ^ 139072085 = 112064486034 := by
        calc
          (2 : ZMod 142409815477) ^ 139072085 = (2 : ZMod 142409815477) ^ (69536042 + 69536042 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 69536042 * (2 : ZMod 142409815477) ^ 69536042) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 112064486034 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 142409815477) ^ 278144170 = 6925009415 := by
        calc
          (2 : ZMod 142409815477) ^ 278144170 = (2 : ZMod 142409815477) ^ (139072085 + 139072085) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 139072085 * (2 : ZMod 142409815477) ^ 139072085 := by rw [pow_add]
          _ = 6925009415 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 142409815477) ^ 556288341 = 74504203691 := by
        calc
          (2 : ZMod 142409815477) ^ 556288341 = (2 : ZMod 142409815477) ^ (278144170 + 278144170 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 278144170 * (2 : ZMod 142409815477) ^ 278144170) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 74504203691 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 142409815477) ^ 1112576683 = 59824268586 := by
        calc
          (2 : ZMod 142409815477) ^ 1112576683 = (2 : ZMod 142409815477) ^ (556288341 + 556288341 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 556288341 * (2 : ZMod 142409815477) ^ 556288341) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 59824268586 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 142409815477) ^ 2225153366 = 4670259950 := by
        calc
          (2 : ZMod 142409815477) ^ 2225153366 = (2 : ZMod 142409815477) ^ (1112576683 + 1112576683) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 1112576683 * (2 : ZMod 142409815477) ^ 1112576683 := by rw [pow_add]
          _ = 4670259950 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 142409815477) ^ 4450306733 = 37400402526 := by
        calc
          (2 : ZMod 142409815477) ^ 4450306733 = (2 : ZMod 142409815477) ^ (2225153366 + 2225153366 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 2225153366 * (2 : ZMod 142409815477) ^ 2225153366) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 37400402526 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 142409815477) ^ 8900613467 = 79669878489 := by
        calc
          (2 : ZMod 142409815477) ^ 8900613467 = (2 : ZMod 142409815477) ^ (4450306733 + 4450306733 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 4450306733 * (2 : ZMod 142409815477) ^ 4450306733) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 79669878489 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 142409815477) ^ 17801226934 = 121796266699 := by
        calc
          (2 : ZMod 142409815477) ^ 17801226934 = (2 : ZMod 142409815477) ^ (8900613467 + 8900613467) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 8900613467 * (2 : ZMod 142409815477) ^ 8900613467 := by rw [pow_add]
          _ = 121796266699 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 142409815477) ^ 35602453869 = 101182717920 := by
        calc
          (2 : ZMod 142409815477) ^ 35602453869 = (2 : ZMod 142409815477) ^ (17801226934 + 17801226934 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 17801226934 * (2 : ZMod 142409815477) ^ 17801226934) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 101182717920 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 142409815477) ^ 71204907738 = 142409815476 := by
        calc
          (2 : ZMod 142409815477) ^ 71204907738 = (2 : ZMod 142409815477) ^ (35602453869 + 35602453869) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 35602453869 * (2 : ZMod 142409815477) ^ 35602453869 := by rw [pow_add]
          _ = 142409815476 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 142409815477) ^ 142409815476 = 1 := by
        calc
          (2 : ZMod 142409815477) ^ 142409815476 = (2 : ZMod 142409815477) ^ (71204907738 + 71204907738) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 71204907738 * (2 : ZMod 142409815477) ^ 71204907738 := by rw [pow_add]
          _ = 1 := by rw [fermat_36]; decide
      simpa using fermat_37
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11867484623, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11867484623, 1)] : List FactorBlock).map factorBlockValue).prod = 142409815477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_11867484623) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 142409815477) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 142409815477) ^ 2 = 4 := by
        calc
          (2 : ZMod 142409815477) ^ 2 = (2 : ZMod 142409815477) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 1 * (2 : ZMod 142409815477) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 142409815477) ^ 4 = 16 := by
        calc
          (2 : ZMod 142409815477) ^ 4 = (2 : ZMod 142409815477) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 2 * (2 : ZMod 142409815477) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 142409815477) ^ 8 = 256 := by
        calc
          (2 : ZMod 142409815477) ^ 8 = (2 : ZMod 142409815477) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 4 * (2 : ZMod 142409815477) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 142409815477) ^ 16 = 65536 := by
        calc
          (2 : ZMod 142409815477) ^ 16 = (2 : ZMod 142409815477) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 8 * (2 : ZMod 142409815477) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 142409815477) ^ 33 = 8589934592 := by
        calc
          (2 : ZMod 142409815477) ^ 33 = (2 : ZMod 142409815477) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 16 * (2 : ZMod 142409815477) ^ 16) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 8589934592 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 142409815477) ^ 66 = 19831588306 := by
        calc
          (2 : ZMod 142409815477) ^ 66 = (2 : ZMod 142409815477) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 33 * (2 : ZMod 142409815477) ^ 33 := by rw [pow_add]
          _ = 19831588306 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 142409815477) ^ 132 = 132149949842 := by
        calc
          (2 : ZMod 142409815477) ^ 132 = (2 : ZMod 142409815477) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 66 * (2 : ZMod 142409815477) ^ 66 := by rw [pow_add]
          _ = 132149949842 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 142409815477) ^ 265 = 127438258719 := by
        calc
          (2 : ZMod 142409815477) ^ 265 = (2 : ZMod 142409815477) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 132 * (2 : ZMod 142409815477) ^ 132) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 127438258719 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 142409815477) ^ 530 = 87711924663 := by
        calc
          (2 : ZMod 142409815477) ^ 530 = (2 : ZMod 142409815477) ^ (265 + 265) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 265 * (2 : ZMod 142409815477) ^ 265 := by rw [pow_add]
          _ = 87711924663 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 142409815477) ^ 1061 = 48049596962 := by
        calc
          (2 : ZMod 142409815477) ^ 1061 = (2 : ZMod 142409815477) ^ (530 + 530 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 530 * (2 : ZMod 142409815477) ^ 530) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 48049596962 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 142409815477) ^ 2122 = 23379384642 := by
        calc
          (2 : ZMod 142409815477) ^ 2122 = (2 : ZMod 142409815477) ^ (1061 + 1061) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 1061 * (2 : ZMod 142409815477) ^ 1061 := by rw [pow_add]
          _ = 23379384642 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 142409815477) ^ 4244 = 48235619651 := by
        calc
          (2 : ZMod 142409815477) ^ 4244 = (2 : ZMod 142409815477) ^ (2122 + 2122) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 2122 * (2 : ZMod 142409815477) ^ 2122 := by rw [pow_add]
          _ = 48235619651 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 142409815477) ^ 8488 = 114251336901 := by
        calc
          (2 : ZMod 142409815477) ^ 8488 = (2 : ZMod 142409815477) ^ (4244 + 4244) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 4244 * (2 : ZMod 142409815477) ^ 4244 := by rw [pow_add]
          _ = 114251336901 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 142409815477) ^ 16976 = 117089352237 := by
        calc
          (2 : ZMod 142409815477) ^ 16976 = (2 : ZMod 142409815477) ^ (8488 + 8488) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 8488 * (2 : ZMod 142409815477) ^ 8488 := by rw [pow_add]
          _ = 117089352237 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 142409815477) ^ 33953 = 11421856982 := by
        calc
          (2 : ZMod 142409815477) ^ 33953 = (2 : ZMod 142409815477) ^ (16976 + 16976 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 16976 * (2 : ZMod 142409815477) ^ 16976) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 11421856982 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 142409815477) ^ 67906 = 116014797660 := by
        calc
          (2 : ZMod 142409815477) ^ 67906 = (2 : ZMod 142409815477) ^ (33953 + 33953) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 33953 * (2 : ZMod 142409815477) ^ 33953 := by rw [pow_add]
          _ = 116014797660 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 142409815477) ^ 135812 = 91775523577 := by
        calc
          (2 : ZMod 142409815477) ^ 135812 = (2 : ZMod 142409815477) ^ (67906 + 67906) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 67906 * (2 : ZMod 142409815477) ^ 67906 := by rw [pow_add]
          _ = 91775523577 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 142409815477) ^ 271625 = 91013953744 := by
        calc
          (2 : ZMod 142409815477) ^ 271625 = (2 : ZMod 142409815477) ^ (135812 + 135812 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 135812 * (2 : ZMod 142409815477) ^ 135812) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 91013953744 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 142409815477) ^ 543250 = 122304715289 := by
        calc
          (2 : ZMod 142409815477) ^ 543250 = (2 : ZMod 142409815477) ^ (271625 + 271625) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 271625 * (2 : ZMod 142409815477) ^ 271625 := by rw [pow_add]
          _ = 122304715289 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 142409815477) ^ 1086500 = 139838108697 := by
        calc
          (2 : ZMod 142409815477) ^ 1086500 = (2 : ZMod 142409815477) ^ (543250 + 543250) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 543250 * (2 : ZMod 142409815477) ^ 543250 := by rw [pow_add]
          _ = 139838108697 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 142409815477) ^ 2173001 = 35696948746 := by
        calc
          (2 : ZMod 142409815477) ^ 2173001 = (2 : ZMod 142409815477) ^ (1086500 + 1086500 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 1086500 * (2 : ZMod 142409815477) ^ 1086500) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 35696948746 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 142409815477) ^ 4346002 = 141798522454 := by
        calc
          (2 : ZMod 142409815477) ^ 4346002 = (2 : ZMod 142409815477) ^ (2173001 + 2173001) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 2173001 * (2 : ZMod 142409815477) ^ 2173001 := by rw [pow_add]
          _ = 141798522454 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 142409815477) ^ 8692005 = 10492774201 := by
        calc
          (2 : ZMod 142409815477) ^ 8692005 = (2 : ZMod 142409815477) ^ (4346002 + 4346002 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 4346002 * (2 : ZMod 142409815477) ^ 4346002) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 10492774201 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 142409815477) ^ 17384010 = 114743564447 := by
        calc
          (2 : ZMod 142409815477) ^ 17384010 = (2 : ZMod 142409815477) ^ (8692005 + 8692005) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 8692005 * (2 : ZMod 142409815477) ^ 8692005 := by rw [pow_add]
          _ = 114743564447 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 142409815477) ^ 34768021 = 21328686119 := by
        calc
          (2 : ZMod 142409815477) ^ 34768021 = (2 : ZMod 142409815477) ^ (17384010 + 17384010 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 17384010 * (2 : ZMod 142409815477) ^ 17384010) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 21328686119 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 142409815477) ^ 69536042 = 92367017966 := by
        calc
          (2 : ZMod 142409815477) ^ 69536042 = (2 : ZMod 142409815477) ^ (34768021 + 34768021) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 34768021 * (2 : ZMod 142409815477) ^ 34768021 := by rw [pow_add]
          _ = 92367017966 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 142409815477) ^ 139072085 = 112064486034 := by
        calc
          (2 : ZMod 142409815477) ^ 139072085 = (2 : ZMod 142409815477) ^ (69536042 + 69536042 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 69536042 * (2 : ZMod 142409815477) ^ 69536042) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 112064486034 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 142409815477) ^ 278144170 = 6925009415 := by
        calc
          (2 : ZMod 142409815477) ^ 278144170 = (2 : ZMod 142409815477) ^ (139072085 + 139072085) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 139072085 * (2 : ZMod 142409815477) ^ 139072085 := by rw [pow_add]
          _ = 6925009415 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 142409815477) ^ 556288341 = 74504203691 := by
        calc
          (2 : ZMod 142409815477) ^ 556288341 = (2 : ZMod 142409815477) ^ (278144170 + 278144170 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 278144170 * (2 : ZMod 142409815477) ^ 278144170) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 74504203691 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 142409815477) ^ 1112576683 = 59824268586 := by
        calc
          (2 : ZMod 142409815477) ^ 1112576683 = (2 : ZMod 142409815477) ^ (556288341 + 556288341 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 556288341 * (2 : ZMod 142409815477) ^ 556288341) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 59824268586 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 142409815477) ^ 2225153366 = 4670259950 := by
        calc
          (2 : ZMod 142409815477) ^ 2225153366 = (2 : ZMod 142409815477) ^ (1112576683 + 1112576683) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 1112576683 * (2 : ZMod 142409815477) ^ 1112576683 := by rw [pow_add]
          _ = 4670259950 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 142409815477) ^ 4450306733 = 37400402526 := by
        calc
          (2 : ZMod 142409815477) ^ 4450306733 = (2 : ZMod 142409815477) ^ (2225153366 + 2225153366 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 2225153366 * (2 : ZMod 142409815477) ^ 2225153366) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 37400402526 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 142409815477) ^ 8900613467 = 79669878489 := by
        calc
          (2 : ZMod 142409815477) ^ 8900613467 = (2 : ZMod 142409815477) ^ (4450306733 + 4450306733 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 4450306733 * (2 : ZMod 142409815477) ^ 4450306733) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 79669878489 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 142409815477) ^ 17801226934 = 121796266699 := by
        calc
          (2 : ZMod 142409815477) ^ 17801226934 = (2 : ZMod 142409815477) ^ (8900613467 + 8900613467) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 8900613467 * (2 : ZMod 142409815477) ^ 8900613467 := by rw [pow_add]
          _ = 121796266699 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 142409815477) ^ 35602453869 = 101182717920 := by
        calc
          (2 : ZMod 142409815477) ^ 35602453869 = (2 : ZMod 142409815477) ^ (17801226934 + 17801226934 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 17801226934 * (2 : ZMod 142409815477) ^ 17801226934) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 101182717920 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 142409815477) ^ 71204907738 = 142409815476 := by
        calc
          (2 : ZMod 142409815477) ^ 71204907738 = (2 : ZMod 142409815477) ^ (35602453869 + 35602453869) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 35602453869 * (2 : ZMod 142409815477) ^ 35602453869 := by rw [pow_add]
          _ = 142409815476 := by rw [factor_0_35]; decide
      change (2 : ZMod 142409815477) ^ 71204907738 ≠ 1
      rw [factor_0_36]
      decide
    ·
      have factor_1_0 : (2 : ZMod 142409815477) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 142409815477) ^ 2 = 4 := by
        calc
          (2 : ZMod 142409815477) ^ 2 = (2 : ZMod 142409815477) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 1 * (2 : ZMod 142409815477) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 142409815477) ^ 5 = 32 := by
        calc
          (2 : ZMod 142409815477) ^ 5 = (2 : ZMod 142409815477) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 2 * (2 : ZMod 142409815477) ^ 2) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 142409815477) ^ 11 = 2048 := by
        calc
          (2 : ZMod 142409815477) ^ 11 = (2 : ZMod 142409815477) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 5 * (2 : ZMod 142409815477) ^ 5) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 142409815477) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 142409815477) ^ 22 = (2 : ZMod 142409815477) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 11 * (2 : ZMod 142409815477) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 142409815477) ^ 44 = 75778740745 := by
        calc
          (2 : ZMod 142409815477) ^ 44 = (2 : ZMod 142409815477) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 22 * (2 : ZMod 142409815477) ^ 22 := by rw [pow_add]
          _ = 75778740745 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 142409815477) ^ 88 = 130675510002 := by
        calc
          (2 : ZMod 142409815477) ^ 88 = (2 : ZMod 142409815477) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 44 * (2 : ZMod 142409815477) ^ 44 := by rw [pow_add]
          _ = 130675510002 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 142409815477) ^ 176 = 4809485327 := by
        calc
          (2 : ZMod 142409815477) ^ 176 = (2 : ZMod 142409815477) ^ (88 + 88) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 88 * (2 : ZMod 142409815477) ^ 88 := by rw [pow_add]
          _ = 4809485327 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 142409815477) ^ 353 = 138391516189 := by
        calc
          (2 : ZMod 142409815477) ^ 353 = (2 : ZMod 142409815477) ^ (176 + 176 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 176 * (2 : ZMod 142409815477) ^ 176) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 138391516189 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 142409815477) ^ 707 = 61176560667 := by
        calc
          (2 : ZMod 142409815477) ^ 707 = (2 : ZMod 142409815477) ^ (353 + 353 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 353 * (2 : ZMod 142409815477) ^ 353) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 61176560667 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 142409815477) ^ 1414 = 54654789944 := by
        calc
          (2 : ZMod 142409815477) ^ 1414 = (2 : ZMod 142409815477) ^ (707 + 707) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 707 * (2 : ZMod 142409815477) ^ 707 := by rw [pow_add]
          _ = 54654789944 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 142409815477) ^ 2829 = 53557954904 := by
        calc
          (2 : ZMod 142409815477) ^ 2829 = (2 : ZMod 142409815477) ^ (1414 + 1414 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 1414 * (2 : ZMod 142409815477) ^ 1414) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 53557954904 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 142409815477) ^ 5658 = 50618521785 := by
        calc
          (2 : ZMod 142409815477) ^ 5658 = (2 : ZMod 142409815477) ^ (2829 + 2829) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 2829 * (2 : ZMod 142409815477) ^ 2829 := by rw [pow_add]
          _ = 50618521785 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 142409815477) ^ 11317 = 38297690700 := by
        calc
          (2 : ZMod 142409815477) ^ 11317 = (2 : ZMod 142409815477) ^ (5658 + 5658 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 5658 * (2 : ZMod 142409815477) ^ 5658) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 38297690700 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 142409815477) ^ 22635 = 109292779120 := by
        calc
          (2 : ZMod 142409815477) ^ 22635 = (2 : ZMod 142409815477) ^ (11317 + 11317 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 11317 * (2 : ZMod 142409815477) ^ 11317) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 109292779120 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 142409815477) ^ 45270 = 66871520123 := by
        calc
          (2 : ZMod 142409815477) ^ 45270 = (2 : ZMod 142409815477) ^ (22635 + 22635) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 22635 * (2 : ZMod 142409815477) ^ 22635 := by rw [pow_add]
          _ = 66871520123 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 142409815477) ^ 90541 = 122351071968 := by
        calc
          (2 : ZMod 142409815477) ^ 90541 = (2 : ZMod 142409815477) ^ (45270 + 45270 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 45270 * (2 : ZMod 142409815477) ^ 45270) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 122351071968 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 142409815477) ^ 181083 = 52532219541 := by
        calc
          (2 : ZMod 142409815477) ^ 181083 = (2 : ZMod 142409815477) ^ (90541 + 90541 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 90541 * (2 : ZMod 142409815477) ^ 90541) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 52532219541 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 142409815477) ^ 362166 = 2076072499 := by
        calc
          (2 : ZMod 142409815477) ^ 362166 = (2 : ZMod 142409815477) ^ (181083 + 181083) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 181083 * (2 : ZMod 142409815477) ^ 181083 := by rw [pow_add]
          _ = 2076072499 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 142409815477) ^ 724333 = 44529250693 := by
        calc
          (2 : ZMod 142409815477) ^ 724333 = (2 : ZMod 142409815477) ^ (362166 + 362166 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 362166 * (2 : ZMod 142409815477) ^ 362166) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 44529250693 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 142409815477) ^ 1448667 = 141756905 := by
        calc
          (2 : ZMod 142409815477) ^ 1448667 = (2 : ZMod 142409815477) ^ (724333 + 724333 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 724333 * (2 : ZMod 142409815477) ^ 724333) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 141756905 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 142409815477) ^ 2897335 = 138975147449 := by
        calc
          (2 : ZMod 142409815477) ^ 2897335 = (2 : ZMod 142409815477) ^ (1448667 + 1448667 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 1448667 * (2 : ZMod 142409815477) ^ 1448667) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 138975147449 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 142409815477) ^ 5794670 = 25671867307 := by
        calc
          (2 : ZMod 142409815477) ^ 5794670 = (2 : ZMod 142409815477) ^ (2897335 + 2897335) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 2897335 * (2 : ZMod 142409815477) ^ 2897335 := by rw [pow_add]
          _ = 25671867307 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 142409815477) ^ 11589340 = 75747102495 := by
        calc
          (2 : ZMod 142409815477) ^ 11589340 = (2 : ZMod 142409815477) ^ (5794670 + 5794670) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 5794670 * (2 : ZMod 142409815477) ^ 5794670 := by rw [pow_add]
          _ = 75747102495 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 142409815477) ^ 23178680 = 16868123071 := by
        calc
          (2 : ZMod 142409815477) ^ 23178680 = (2 : ZMod 142409815477) ^ (11589340 + 11589340) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 11589340 * (2 : ZMod 142409815477) ^ 11589340 := by rw [pow_add]
          _ = 16868123071 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 142409815477) ^ 46357361 = 41011468032 := by
        calc
          (2 : ZMod 142409815477) ^ 46357361 = (2 : ZMod 142409815477) ^ (23178680 + 23178680 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 23178680 * (2 : ZMod 142409815477) ^ 23178680) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 41011468032 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 142409815477) ^ 92714723 = 138077930310 := by
        calc
          (2 : ZMod 142409815477) ^ 92714723 = (2 : ZMod 142409815477) ^ (46357361 + 46357361 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 46357361 * (2 : ZMod 142409815477) ^ 46357361) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 138077930310 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 142409815477) ^ 185429447 = 9619663007 := by
        calc
          (2 : ZMod 142409815477) ^ 185429447 = (2 : ZMod 142409815477) ^ (92714723 + 92714723 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 92714723 * (2 : ZMod 142409815477) ^ 92714723) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 9619663007 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 142409815477) ^ 370858894 = 42833300993 := by
        calc
          (2 : ZMod 142409815477) ^ 370858894 = (2 : ZMod 142409815477) ^ (185429447 + 185429447) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 185429447 * (2 : ZMod 142409815477) ^ 185429447 := by rw [pow_add]
          _ = 42833300993 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 142409815477) ^ 741717788 = 45259828609 := by
        calc
          (2 : ZMod 142409815477) ^ 741717788 = (2 : ZMod 142409815477) ^ (370858894 + 370858894) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 370858894 * (2 : ZMod 142409815477) ^ 370858894 := by rw [pow_add]
          _ = 45259828609 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 142409815477) ^ 1483435577 = 2032565463 := by
        calc
          (2 : ZMod 142409815477) ^ 1483435577 = (2 : ZMod 142409815477) ^ (741717788 + 741717788 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 741717788 * (2 : ZMod 142409815477) ^ 741717788) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 2032565463 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 142409815477) ^ 2966871155 = 28510512631 := by
        calc
          (2 : ZMod 142409815477) ^ 2966871155 = (2 : ZMod 142409815477) ^ (1483435577 + 1483435577 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 1483435577 * (2 : ZMod 142409815477) ^ 1483435577) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 28510512631 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 142409815477) ^ 5933742311 = 77950468021 := by
        calc
          (2 : ZMod 142409815477) ^ 5933742311 = (2 : ZMod 142409815477) ^ (2966871155 + 2966871155 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 2966871155 * (2 : ZMod 142409815477) ^ 2966871155) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 77950468021 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 142409815477) ^ 11867484623 = 91735617014 := by
        calc
          (2 : ZMod 142409815477) ^ 11867484623 = (2 : ZMod 142409815477) ^ (5933742311 + 5933742311 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 5933742311 * (2 : ZMod 142409815477) ^ 5933742311) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 91735617014 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 142409815477) ^ 23734969246 = 22938221471 := by
        calc
          (2 : ZMod 142409815477) ^ 23734969246 = (2 : ZMod 142409815477) ^ (11867484623 + 11867484623) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 11867484623 * (2 : ZMod 142409815477) ^ 11867484623 := by rw [pow_add]
          _ = 22938221471 := by rw [factor_1_33]; decide
      have factor_1_35 : (2 : ZMod 142409815477) ^ 47469938492 = 22938221470 := by
        calc
          (2 : ZMod 142409815477) ^ 47469938492 = (2 : ZMod 142409815477) ^ (23734969246 + 23734969246) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 23734969246 * (2 : ZMod 142409815477) ^ 23734969246 := by rw [pow_add]
          _ = 22938221470 := by rw [factor_1_34]; decide
      change (2 : ZMod 142409815477) ^ 47469938492 ≠ 1
      rw [factor_1_35]
      decide
    ·
      have factor_2_0 : (2 : ZMod 142409815477) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 142409815477) ^ 3 = 8 := by
        calc
          (2 : ZMod 142409815477) ^ 3 = (2 : ZMod 142409815477) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = ((2 : ZMod 142409815477) ^ 1 * (2 : ZMod 142409815477) ^ 1) * (2 : ZMod 142409815477) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 142409815477) ^ 6 = 64 := by
        calc
          (2 : ZMod 142409815477) ^ 6 = (2 : ZMod 142409815477) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 3 * (2 : ZMod 142409815477) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 142409815477) ^ 12 = 4096 := by
        calc
          (2 : ZMod 142409815477) ^ 12 = (2 : ZMod 142409815477) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 142409815477) ^ n) (by norm_num)
          _ = (2 : ZMod 142409815477) ^ 6 * (2 : ZMod 142409815477) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_2_2]; decide
      change (2 : ZMod 142409815477) ^ 12 ≠ 1
      rw [factor_2_3]
      decide

#print axioms prime_lucas_142409815477

end TotientTailPeriodKiller
end Erdos249257
