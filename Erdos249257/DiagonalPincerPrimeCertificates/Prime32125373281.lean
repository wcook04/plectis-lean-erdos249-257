import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=27 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_32125373281 : Nat.Prime 32125373281 := by
  apply lucas_primality 32125373281 (106 : ZMod 32125373281)
  ·
      have fermat_0 : (106 : ZMod 32125373281) ^ 1 = 106 := by norm_num
      have fermat_1 : (106 : ZMod 32125373281) ^ 3 = 1191016 := by
        calc
          (106 : ZMod 32125373281) ^ 3 = (106 : ZMod 32125373281) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 1 * (106 : ZMod 32125373281) ^ 1) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 1191016 := by rw [fermat_0]; decide
      have fermat_2 : (106 : ZMod 32125373281) ^ 7 = 16278944056 := by
        calc
          (106 : ZMod 32125373281) ^ 7 = (106 : ZMod 32125373281) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 3 * (106 : ZMod 32125373281) ^ 3) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 16278944056 := by rw [fermat_1]; decide
      have fermat_3 : (106 : ZMod 32125373281) ^ 14 = 10689995107 := by
        calc
          (106 : ZMod 32125373281) ^ 14 = (106 : ZMod 32125373281) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 7 * (106 : ZMod 32125373281) ^ 7 := by rw [pow_add]
          _ = 10689995107 := by rw [fermat_2]; decide
      have fermat_4 : (106 : ZMod 32125373281) ^ 29 = 24437113428 := by
        calc
          (106 : ZMod 32125373281) ^ 29 = (106 : ZMod 32125373281) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 14 * (106 : ZMod 32125373281) ^ 14) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 24437113428 := by rw [fermat_3]; decide
      have fermat_5 : (106 : ZMod 32125373281) ^ 59 = 18691607169 := by
        calc
          (106 : ZMod 32125373281) ^ 59 = (106 : ZMod 32125373281) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 29 * (106 : ZMod 32125373281) ^ 29) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 18691607169 := by rw [fermat_4]; decide
      have fermat_6 : (106 : ZMod 32125373281) ^ 119 = 12834756167 := by
        calc
          (106 : ZMod 32125373281) ^ 119 = (106 : ZMod 32125373281) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 59 * (106 : ZMod 32125373281) ^ 59) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 12834756167 := by rw [fermat_5]; decide
      have fermat_7 : (106 : ZMod 32125373281) ^ 239 = 350043408 := by
        calc
          (106 : ZMod 32125373281) ^ 239 = (106 : ZMod 32125373281) ^ (119 + 119 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 119 * (106 : ZMod 32125373281) ^ 119) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 350043408 := by rw [fermat_6]; decide
      have fermat_8 : (106 : ZMod 32125373281) ^ 478 = 5366620653 := by
        calc
          (106 : ZMod 32125373281) ^ 478 = (106 : ZMod 32125373281) ^ (239 + 239) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 239 * (106 : ZMod 32125373281) ^ 239 := by rw [pow_add]
          _ = 5366620653 := by rw [fermat_7]; decide
      have fermat_9 : (106 : ZMod 32125373281) ^ 957 = 10628843402 := by
        calc
          (106 : ZMod 32125373281) ^ 957 = (106 : ZMod 32125373281) ^ (478 + 478 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 478 * (106 : ZMod 32125373281) ^ 478) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 10628843402 := by rw [fermat_8]; decide
      have fermat_10 : (106 : ZMod 32125373281) ^ 1914 = 20667339100 := by
        calc
          (106 : ZMod 32125373281) ^ 1914 = (106 : ZMod 32125373281) ^ (957 + 957) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 957 * (106 : ZMod 32125373281) ^ 957 := by rw [pow_add]
          _ = 20667339100 := by rw [fermat_9]; decide
      have fermat_11 : (106 : ZMod 32125373281) ^ 3829 = 11338008366 := by
        calc
          (106 : ZMod 32125373281) ^ 3829 = (106 : ZMod 32125373281) ^ (1914 + 1914 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 1914 * (106 : ZMod 32125373281) ^ 1914) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 11338008366 := by rw [fermat_10]; decide
      have fermat_12 : (106 : ZMod 32125373281) ^ 7659 = 3226972650 := by
        calc
          (106 : ZMod 32125373281) ^ 7659 = (106 : ZMod 32125373281) ^ (3829 + 3829 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 3829 * (106 : ZMod 32125373281) ^ 3829) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 3226972650 := by rw [fermat_11]; decide
      have fermat_13 : (106 : ZMod 32125373281) ^ 15318 = 19451076977 := by
        calc
          (106 : ZMod 32125373281) ^ 15318 = (106 : ZMod 32125373281) ^ (7659 + 7659) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 7659 * (106 : ZMod 32125373281) ^ 7659 := by rw [pow_add]
          _ = 19451076977 := by rw [fermat_12]; decide
      have fermat_14 : (106 : ZMod 32125373281) ^ 30637 = 28034512256 := by
        calc
          (106 : ZMod 32125373281) ^ 30637 = (106 : ZMod 32125373281) ^ (15318 + 15318 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 15318 * (106 : ZMod 32125373281) ^ 15318) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 28034512256 := by rw [fermat_13]; decide
      have fermat_15 : (106 : ZMod 32125373281) ^ 61274 = 8867013226 := by
        calc
          (106 : ZMod 32125373281) ^ 61274 = (106 : ZMod 32125373281) ^ (30637 + 30637) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 30637 * (106 : ZMod 32125373281) ^ 30637 := by rw [pow_add]
          _ = 8867013226 := by rw [fermat_14]; decide
      have fermat_16 : (106 : ZMod 32125373281) ^ 122548 = 30078524606 := by
        calc
          (106 : ZMod 32125373281) ^ 122548 = (106 : ZMod 32125373281) ^ (61274 + 61274) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 61274 * (106 : ZMod 32125373281) ^ 61274 := by rw [pow_add]
          _ = 30078524606 := by rw [fermat_15]; decide
      have fermat_17 : (106 : ZMod 32125373281) ^ 245097 = 27155149725 := by
        calc
          (106 : ZMod 32125373281) ^ 245097 = (106 : ZMod 32125373281) ^ (122548 + 122548 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 122548 * (106 : ZMod 32125373281) ^ 122548) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 27155149725 := by rw [fermat_16]; decide
      have fermat_18 : (106 : ZMod 32125373281) ^ 490194 = 9390890567 := by
        calc
          (106 : ZMod 32125373281) ^ 490194 = (106 : ZMod 32125373281) ^ (245097 + 245097) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 245097 * (106 : ZMod 32125373281) ^ 245097 := by rw [pow_add]
          _ = 9390890567 := by rw [fermat_17]; decide
      have fermat_19 : (106 : ZMod 32125373281) ^ 980388 = 8442038815 := by
        calc
          (106 : ZMod 32125373281) ^ 980388 = (106 : ZMod 32125373281) ^ (490194 + 490194) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 490194 * (106 : ZMod 32125373281) ^ 490194 := by rw [pow_add]
          _ = 8442038815 := by rw [fermat_18]; decide
      have fermat_20 : (106 : ZMod 32125373281) ^ 1960777 = 30544151935 := by
        calc
          (106 : ZMod 32125373281) ^ 1960777 = (106 : ZMod 32125373281) ^ (980388 + 980388 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 980388 * (106 : ZMod 32125373281) ^ 980388) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 30544151935 := by rw [fermat_19]; decide
      have fermat_21 : (106 : ZMod 32125373281) ^ 3921554 = 4496529086 := by
        calc
          (106 : ZMod 32125373281) ^ 3921554 = (106 : ZMod 32125373281) ^ (1960777 + 1960777) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1960777 * (106 : ZMod 32125373281) ^ 1960777 := by rw [pow_add]
          _ = 4496529086 := by rw [fermat_20]; decide
      have fermat_22 : (106 : ZMod 32125373281) ^ 7843108 = 11560003736 := by
        calc
          (106 : ZMod 32125373281) ^ 7843108 = (106 : ZMod 32125373281) ^ (3921554 + 3921554) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 3921554 * (106 : ZMod 32125373281) ^ 3921554 := by rw [pow_add]
          _ = 11560003736 := by rw [fermat_21]; decide
      have fermat_23 : (106 : ZMod 32125373281) ^ 15686217 = 26270405214 := by
        calc
          (106 : ZMod 32125373281) ^ 15686217 = (106 : ZMod 32125373281) ^ (7843108 + 7843108 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 7843108 * (106 : ZMod 32125373281) ^ 7843108) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 26270405214 := by rw [fermat_22]; decide
      have fermat_24 : (106 : ZMod 32125373281) ^ 31372434 = 15949577790 := by
        calc
          (106 : ZMod 32125373281) ^ 31372434 = (106 : ZMod 32125373281) ^ (15686217 + 15686217) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 15686217 * (106 : ZMod 32125373281) ^ 15686217 := by rw [pow_add]
          _ = 15949577790 := by rw [fermat_23]; decide
      have fermat_25 : (106 : ZMod 32125373281) ^ 62744869 = 23720207036 := by
        calc
          (106 : ZMod 32125373281) ^ 62744869 = (106 : ZMod 32125373281) ^ (31372434 + 31372434 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 31372434 * (106 : ZMod 32125373281) ^ 31372434) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 23720207036 := by rw [fermat_24]; decide
      have fermat_26 : (106 : ZMod 32125373281) ^ 125489739 = 19914766294 := by
        calc
          (106 : ZMod 32125373281) ^ 125489739 = (106 : ZMod 32125373281) ^ (62744869 + 62744869 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 62744869 * (106 : ZMod 32125373281) ^ 62744869) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 19914766294 := by rw [fermat_25]; decide
      have fermat_27 : (106 : ZMod 32125373281) ^ 250979478 = 742523527 := by
        calc
          (106 : ZMod 32125373281) ^ 250979478 = (106 : ZMod 32125373281) ^ (125489739 + 125489739) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 125489739 * (106 : ZMod 32125373281) ^ 125489739 := by rw [pow_add]
          _ = 742523527 := by rw [fermat_26]; decide
      have fermat_28 : (106 : ZMod 32125373281) ^ 501958957 = 29086634462 := by
        calc
          (106 : ZMod 32125373281) ^ 501958957 = (106 : ZMod 32125373281) ^ (250979478 + 250979478 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 250979478 * (106 : ZMod 32125373281) ^ 250979478) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 29086634462 := by rw [fermat_27]; decide
      have fermat_29 : (106 : ZMod 32125373281) ^ 1003917915 = 12793739551 := by
        calc
          (106 : ZMod 32125373281) ^ 1003917915 = (106 : ZMod 32125373281) ^ (501958957 + 501958957 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 501958957 * (106 : ZMod 32125373281) ^ 501958957) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 12793739551 := by rw [fermat_28]; decide
      have fermat_30 : (106 : ZMod 32125373281) ^ 2007835830 = 5692288874 := by
        calc
          (106 : ZMod 32125373281) ^ 2007835830 = (106 : ZMod 32125373281) ^ (1003917915 + 1003917915) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1003917915 * (106 : ZMod 32125373281) ^ 1003917915 := by rw [pow_add]
          _ = 5692288874 := by rw [fermat_29]; decide
      have fermat_31 : (106 : ZMod 32125373281) ^ 4015671660 = 10149777557 := by
        calc
          (106 : ZMod 32125373281) ^ 4015671660 = (106 : ZMod 32125373281) ^ (2007835830 + 2007835830) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 2007835830 * (106 : ZMod 32125373281) ^ 2007835830 := by rw [pow_add]
          _ = 10149777557 := by rw [fermat_30]; decide
      have fermat_32 : (106 : ZMod 32125373281) ^ 8031343320 = 3513499842 := by
        calc
          (106 : ZMod 32125373281) ^ 8031343320 = (106 : ZMod 32125373281) ^ (4015671660 + 4015671660) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 4015671660 * (106 : ZMod 32125373281) ^ 4015671660 := by rw [pow_add]
          _ = 3513499842 := by rw [fermat_31]; decide
      have fermat_33 : (106 : ZMod 32125373281) ^ 16062686640 = 32125373280 := by
        calc
          (106 : ZMod 32125373281) ^ 16062686640 = (106 : ZMod 32125373281) ^ (8031343320 + 8031343320) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 8031343320 * (106 : ZMod 32125373281) ^ 8031343320 := by rw [pow_add]
          _ = 32125373280 := by rw [fermat_32]; decide
      have fermat_34 : (106 : ZMod 32125373281) ^ 32125373280 = 1 := by
        calc
          (106 : ZMod 32125373281) ^ 32125373280 = (106 : ZMod 32125373281) ^ (16062686640 + 16062686640) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 16062686640 * (106 : ZMod 32125373281) ^ 16062686640 := by rw [pow_add]
          _ = 1 := by rw [fermat_33]; decide
      simpa using fermat_34
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 32125373281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (106 : ZMod 32125373281) ^ 1 = 106 := by norm_num
      have factor_0_1 : (106 : ZMod 32125373281) ^ 3 = 1191016 := by
        calc
          (106 : ZMod 32125373281) ^ 3 = (106 : ZMod 32125373281) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 1 * (106 : ZMod 32125373281) ^ 1) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 1191016 := by rw [factor_0_0]; decide
      have factor_0_2 : (106 : ZMod 32125373281) ^ 7 = 16278944056 := by
        calc
          (106 : ZMod 32125373281) ^ 7 = (106 : ZMod 32125373281) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 3 * (106 : ZMod 32125373281) ^ 3) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 16278944056 := by rw [factor_0_1]; decide
      have factor_0_3 : (106 : ZMod 32125373281) ^ 14 = 10689995107 := by
        calc
          (106 : ZMod 32125373281) ^ 14 = (106 : ZMod 32125373281) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 7 * (106 : ZMod 32125373281) ^ 7 := by rw [pow_add]
          _ = 10689995107 := by rw [factor_0_2]; decide
      have factor_0_4 : (106 : ZMod 32125373281) ^ 29 = 24437113428 := by
        calc
          (106 : ZMod 32125373281) ^ 29 = (106 : ZMod 32125373281) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 14 * (106 : ZMod 32125373281) ^ 14) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 24437113428 := by rw [factor_0_3]; decide
      have factor_0_5 : (106 : ZMod 32125373281) ^ 59 = 18691607169 := by
        calc
          (106 : ZMod 32125373281) ^ 59 = (106 : ZMod 32125373281) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 29 * (106 : ZMod 32125373281) ^ 29) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 18691607169 := by rw [factor_0_4]; decide
      have factor_0_6 : (106 : ZMod 32125373281) ^ 119 = 12834756167 := by
        calc
          (106 : ZMod 32125373281) ^ 119 = (106 : ZMod 32125373281) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 59 * (106 : ZMod 32125373281) ^ 59) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 12834756167 := by rw [factor_0_5]; decide
      have factor_0_7 : (106 : ZMod 32125373281) ^ 239 = 350043408 := by
        calc
          (106 : ZMod 32125373281) ^ 239 = (106 : ZMod 32125373281) ^ (119 + 119 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 119 * (106 : ZMod 32125373281) ^ 119) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 350043408 := by rw [factor_0_6]; decide
      have factor_0_8 : (106 : ZMod 32125373281) ^ 478 = 5366620653 := by
        calc
          (106 : ZMod 32125373281) ^ 478 = (106 : ZMod 32125373281) ^ (239 + 239) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 239 * (106 : ZMod 32125373281) ^ 239 := by rw [pow_add]
          _ = 5366620653 := by rw [factor_0_7]; decide
      have factor_0_9 : (106 : ZMod 32125373281) ^ 957 = 10628843402 := by
        calc
          (106 : ZMod 32125373281) ^ 957 = (106 : ZMod 32125373281) ^ (478 + 478 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 478 * (106 : ZMod 32125373281) ^ 478) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 10628843402 := by rw [factor_0_8]; decide
      have factor_0_10 : (106 : ZMod 32125373281) ^ 1914 = 20667339100 := by
        calc
          (106 : ZMod 32125373281) ^ 1914 = (106 : ZMod 32125373281) ^ (957 + 957) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 957 * (106 : ZMod 32125373281) ^ 957 := by rw [pow_add]
          _ = 20667339100 := by rw [factor_0_9]; decide
      have factor_0_11 : (106 : ZMod 32125373281) ^ 3829 = 11338008366 := by
        calc
          (106 : ZMod 32125373281) ^ 3829 = (106 : ZMod 32125373281) ^ (1914 + 1914 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 1914 * (106 : ZMod 32125373281) ^ 1914) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 11338008366 := by rw [factor_0_10]; decide
      have factor_0_12 : (106 : ZMod 32125373281) ^ 7659 = 3226972650 := by
        calc
          (106 : ZMod 32125373281) ^ 7659 = (106 : ZMod 32125373281) ^ (3829 + 3829 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 3829 * (106 : ZMod 32125373281) ^ 3829) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 3226972650 := by rw [factor_0_11]; decide
      have factor_0_13 : (106 : ZMod 32125373281) ^ 15318 = 19451076977 := by
        calc
          (106 : ZMod 32125373281) ^ 15318 = (106 : ZMod 32125373281) ^ (7659 + 7659) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 7659 * (106 : ZMod 32125373281) ^ 7659 := by rw [pow_add]
          _ = 19451076977 := by rw [factor_0_12]; decide
      have factor_0_14 : (106 : ZMod 32125373281) ^ 30637 = 28034512256 := by
        calc
          (106 : ZMod 32125373281) ^ 30637 = (106 : ZMod 32125373281) ^ (15318 + 15318 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 15318 * (106 : ZMod 32125373281) ^ 15318) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 28034512256 := by rw [factor_0_13]; decide
      have factor_0_15 : (106 : ZMod 32125373281) ^ 61274 = 8867013226 := by
        calc
          (106 : ZMod 32125373281) ^ 61274 = (106 : ZMod 32125373281) ^ (30637 + 30637) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 30637 * (106 : ZMod 32125373281) ^ 30637 := by rw [pow_add]
          _ = 8867013226 := by rw [factor_0_14]; decide
      have factor_0_16 : (106 : ZMod 32125373281) ^ 122548 = 30078524606 := by
        calc
          (106 : ZMod 32125373281) ^ 122548 = (106 : ZMod 32125373281) ^ (61274 + 61274) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 61274 * (106 : ZMod 32125373281) ^ 61274 := by rw [pow_add]
          _ = 30078524606 := by rw [factor_0_15]; decide
      have factor_0_17 : (106 : ZMod 32125373281) ^ 245097 = 27155149725 := by
        calc
          (106 : ZMod 32125373281) ^ 245097 = (106 : ZMod 32125373281) ^ (122548 + 122548 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 122548 * (106 : ZMod 32125373281) ^ 122548) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 27155149725 := by rw [factor_0_16]; decide
      have factor_0_18 : (106 : ZMod 32125373281) ^ 490194 = 9390890567 := by
        calc
          (106 : ZMod 32125373281) ^ 490194 = (106 : ZMod 32125373281) ^ (245097 + 245097) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 245097 * (106 : ZMod 32125373281) ^ 245097 := by rw [pow_add]
          _ = 9390890567 := by rw [factor_0_17]; decide
      have factor_0_19 : (106 : ZMod 32125373281) ^ 980388 = 8442038815 := by
        calc
          (106 : ZMod 32125373281) ^ 980388 = (106 : ZMod 32125373281) ^ (490194 + 490194) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 490194 * (106 : ZMod 32125373281) ^ 490194 := by rw [pow_add]
          _ = 8442038815 := by rw [factor_0_18]; decide
      have factor_0_20 : (106 : ZMod 32125373281) ^ 1960777 = 30544151935 := by
        calc
          (106 : ZMod 32125373281) ^ 1960777 = (106 : ZMod 32125373281) ^ (980388 + 980388 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 980388 * (106 : ZMod 32125373281) ^ 980388) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 30544151935 := by rw [factor_0_19]; decide
      have factor_0_21 : (106 : ZMod 32125373281) ^ 3921554 = 4496529086 := by
        calc
          (106 : ZMod 32125373281) ^ 3921554 = (106 : ZMod 32125373281) ^ (1960777 + 1960777) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1960777 * (106 : ZMod 32125373281) ^ 1960777 := by rw [pow_add]
          _ = 4496529086 := by rw [factor_0_20]; decide
      have factor_0_22 : (106 : ZMod 32125373281) ^ 7843108 = 11560003736 := by
        calc
          (106 : ZMod 32125373281) ^ 7843108 = (106 : ZMod 32125373281) ^ (3921554 + 3921554) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 3921554 * (106 : ZMod 32125373281) ^ 3921554 := by rw [pow_add]
          _ = 11560003736 := by rw [factor_0_21]; decide
      have factor_0_23 : (106 : ZMod 32125373281) ^ 15686217 = 26270405214 := by
        calc
          (106 : ZMod 32125373281) ^ 15686217 = (106 : ZMod 32125373281) ^ (7843108 + 7843108 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 7843108 * (106 : ZMod 32125373281) ^ 7843108) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 26270405214 := by rw [factor_0_22]; decide
      have factor_0_24 : (106 : ZMod 32125373281) ^ 31372434 = 15949577790 := by
        calc
          (106 : ZMod 32125373281) ^ 31372434 = (106 : ZMod 32125373281) ^ (15686217 + 15686217) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 15686217 * (106 : ZMod 32125373281) ^ 15686217 := by rw [pow_add]
          _ = 15949577790 := by rw [factor_0_23]; decide
      have factor_0_25 : (106 : ZMod 32125373281) ^ 62744869 = 23720207036 := by
        calc
          (106 : ZMod 32125373281) ^ 62744869 = (106 : ZMod 32125373281) ^ (31372434 + 31372434 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 31372434 * (106 : ZMod 32125373281) ^ 31372434) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 23720207036 := by rw [factor_0_24]; decide
      have factor_0_26 : (106 : ZMod 32125373281) ^ 125489739 = 19914766294 := by
        calc
          (106 : ZMod 32125373281) ^ 125489739 = (106 : ZMod 32125373281) ^ (62744869 + 62744869 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 62744869 * (106 : ZMod 32125373281) ^ 62744869) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 19914766294 := by rw [factor_0_25]; decide
      have factor_0_27 : (106 : ZMod 32125373281) ^ 250979478 = 742523527 := by
        calc
          (106 : ZMod 32125373281) ^ 250979478 = (106 : ZMod 32125373281) ^ (125489739 + 125489739) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 125489739 * (106 : ZMod 32125373281) ^ 125489739 := by rw [pow_add]
          _ = 742523527 := by rw [factor_0_26]; decide
      have factor_0_28 : (106 : ZMod 32125373281) ^ 501958957 = 29086634462 := by
        calc
          (106 : ZMod 32125373281) ^ 501958957 = (106 : ZMod 32125373281) ^ (250979478 + 250979478 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 250979478 * (106 : ZMod 32125373281) ^ 250979478) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 29086634462 := by rw [factor_0_27]; decide
      have factor_0_29 : (106 : ZMod 32125373281) ^ 1003917915 = 12793739551 := by
        calc
          (106 : ZMod 32125373281) ^ 1003917915 = (106 : ZMod 32125373281) ^ (501958957 + 501958957 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 501958957 * (106 : ZMod 32125373281) ^ 501958957) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 12793739551 := by rw [factor_0_28]; decide
      have factor_0_30 : (106 : ZMod 32125373281) ^ 2007835830 = 5692288874 := by
        calc
          (106 : ZMod 32125373281) ^ 2007835830 = (106 : ZMod 32125373281) ^ (1003917915 + 1003917915) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1003917915 * (106 : ZMod 32125373281) ^ 1003917915 := by rw [pow_add]
          _ = 5692288874 := by rw [factor_0_29]; decide
      have factor_0_31 : (106 : ZMod 32125373281) ^ 4015671660 = 10149777557 := by
        calc
          (106 : ZMod 32125373281) ^ 4015671660 = (106 : ZMod 32125373281) ^ (2007835830 + 2007835830) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 2007835830 * (106 : ZMod 32125373281) ^ 2007835830 := by rw [pow_add]
          _ = 10149777557 := by rw [factor_0_30]; decide
      have factor_0_32 : (106 : ZMod 32125373281) ^ 8031343320 = 3513499842 := by
        calc
          (106 : ZMod 32125373281) ^ 8031343320 = (106 : ZMod 32125373281) ^ (4015671660 + 4015671660) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 4015671660 * (106 : ZMod 32125373281) ^ 4015671660 := by rw [pow_add]
          _ = 3513499842 := by rw [factor_0_31]; decide
      have factor_0_33 : (106 : ZMod 32125373281) ^ 16062686640 = 32125373280 := by
        calc
          (106 : ZMod 32125373281) ^ 16062686640 = (106 : ZMod 32125373281) ^ (8031343320 + 8031343320) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 8031343320 * (106 : ZMod 32125373281) ^ 8031343320 := by rw [pow_add]
          _ = 32125373280 := by rw [factor_0_32]; decide
      change (106 : ZMod 32125373281) ^ 16062686640 ≠ 1
      rw [factor_0_33]
      decide
    ·
      have factor_1_0 : (106 : ZMod 32125373281) ^ 1 = 106 := by norm_num
      have factor_1_1 : (106 : ZMod 32125373281) ^ 2 = 11236 := by
        calc
          (106 : ZMod 32125373281) ^ 2 = (106 : ZMod 32125373281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1 * (106 : ZMod 32125373281) ^ 1 := by rw [pow_add]
          _ = 11236 := by rw [factor_1_0]; decide
      have factor_1_2 : (106 : ZMod 32125373281) ^ 4 = 126247696 := by
        calc
          (106 : ZMod 32125373281) ^ 4 = (106 : ZMod 32125373281) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 2 * (106 : ZMod 32125373281) ^ 2 := by rw [pow_add]
          _ = 126247696 := by rw [factor_1_1]; decide
      have factor_1_3 : (106 : ZMod 32125373281) ^ 9 = 20465324483 := by
        calc
          (106 : ZMod 32125373281) ^ 9 = (106 : ZMod 32125373281) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 4 * (106 : ZMod 32125373281) ^ 4) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 20465324483 := by rw [factor_1_2]; decide
      have factor_1_4 : (106 : ZMod 32125373281) ^ 19 = 2602323453 := by
        calc
          (106 : ZMod 32125373281) ^ 19 = (106 : ZMod 32125373281) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 9 * (106 : ZMod 32125373281) ^ 9) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 2602323453 := by rw [factor_1_3]; decide
      have factor_1_5 : (106 : ZMod 32125373281) ^ 39 = 1291083860 := by
        calc
          (106 : ZMod 32125373281) ^ 39 = (106 : ZMod 32125373281) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 19 * (106 : ZMod 32125373281) ^ 19) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 1291083860 := by rw [factor_1_4]; decide
      have factor_1_6 : (106 : ZMod 32125373281) ^ 79 = 27517420407 := by
        calc
          (106 : ZMod 32125373281) ^ 79 = (106 : ZMod 32125373281) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 39 * (106 : ZMod 32125373281) ^ 39) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 27517420407 := by rw [factor_1_5]; decide
      have factor_1_7 : (106 : ZMod 32125373281) ^ 159 = 24304121559 := by
        calc
          (106 : ZMod 32125373281) ^ 159 = (106 : ZMod 32125373281) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 79 * (106 : ZMod 32125373281) ^ 79) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 24304121559 := by rw [factor_1_6]; decide
      have factor_1_8 : (106 : ZMod 32125373281) ^ 319 = 15060813109 := by
        calc
          (106 : ZMod 32125373281) ^ 319 = (106 : ZMod 32125373281) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 159 * (106 : ZMod 32125373281) ^ 159) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 15060813109 := by rw [factor_1_7]; decide
      have factor_1_9 : (106 : ZMod 32125373281) ^ 638 = 23252482182 := by
        calc
          (106 : ZMod 32125373281) ^ 638 = (106 : ZMod 32125373281) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 319 * (106 : ZMod 32125373281) ^ 319 := by rw [pow_add]
          _ = 23252482182 := by rw [factor_1_8]; decide
      have factor_1_10 : (106 : ZMod 32125373281) ^ 1276 = 12633076159 := by
        calc
          (106 : ZMod 32125373281) ^ 1276 = (106 : ZMod 32125373281) ^ (638 + 638) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 638 * (106 : ZMod 32125373281) ^ 638 := by rw [pow_add]
          _ = 12633076159 := by rw [factor_1_9]; decide
      have factor_1_11 : (106 : ZMod 32125373281) ^ 2553 = 28036803763 := by
        calc
          (106 : ZMod 32125373281) ^ 2553 = (106 : ZMod 32125373281) ^ (1276 + 1276 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 1276 * (106 : ZMod 32125373281) ^ 1276) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 28036803763 := by rw [factor_1_10]; decide
      have factor_1_12 : (106 : ZMod 32125373281) ^ 5106 = 14308781565 := by
        calc
          (106 : ZMod 32125373281) ^ 5106 = (106 : ZMod 32125373281) ^ (2553 + 2553) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 2553 * (106 : ZMod 32125373281) ^ 2553 := by rw [pow_add]
          _ = 14308781565 := by rw [factor_1_11]; decide
      have factor_1_13 : (106 : ZMod 32125373281) ^ 10212 = 25603618144 := by
        calc
          (106 : ZMod 32125373281) ^ 10212 = (106 : ZMod 32125373281) ^ (5106 + 5106) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 5106 * (106 : ZMod 32125373281) ^ 5106 := by rw [pow_add]
          _ = 25603618144 := by rw [factor_1_12]; decide
      have factor_1_14 : (106 : ZMod 32125373281) ^ 20424 = 31124208289 := by
        calc
          (106 : ZMod 32125373281) ^ 20424 = (106 : ZMod 32125373281) ^ (10212 + 10212) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 10212 * (106 : ZMod 32125373281) ^ 10212 := by rw [pow_add]
          _ = 31124208289 := by rw [factor_1_13]; decide
      have factor_1_15 : (106 : ZMod 32125373281) ^ 40849 = 17693674280 := by
        calc
          (106 : ZMod 32125373281) ^ 40849 = (106 : ZMod 32125373281) ^ (20424 + 20424 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 20424 * (106 : ZMod 32125373281) ^ 20424) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 17693674280 := by rw [factor_1_14]; decide
      have factor_1_16 : (106 : ZMod 32125373281) ^ 81699 = 3867310037 := by
        calc
          (106 : ZMod 32125373281) ^ 81699 = (106 : ZMod 32125373281) ^ (40849 + 40849 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 40849 * (106 : ZMod 32125373281) ^ 40849) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 3867310037 := by rw [factor_1_15]; decide
      have factor_1_17 : (106 : ZMod 32125373281) ^ 163398 = 13424279173 := by
        calc
          (106 : ZMod 32125373281) ^ 163398 = (106 : ZMod 32125373281) ^ (81699 + 81699) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 81699 * (106 : ZMod 32125373281) ^ 81699 := by rw [pow_add]
          _ = 13424279173 := by rw [factor_1_16]; decide
      have factor_1_18 : (106 : ZMod 32125373281) ^ 326796 = 19886683572 := by
        calc
          (106 : ZMod 32125373281) ^ 326796 = (106 : ZMod 32125373281) ^ (163398 + 163398) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 163398 * (106 : ZMod 32125373281) ^ 163398 := by rw [pow_add]
          _ = 19886683572 := by rw [factor_1_17]; decide
      have factor_1_19 : (106 : ZMod 32125373281) ^ 653592 = 17840936158 := by
        calc
          (106 : ZMod 32125373281) ^ 653592 = (106 : ZMod 32125373281) ^ (326796 + 326796) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 326796 * (106 : ZMod 32125373281) ^ 326796 := by rw [pow_add]
          _ = 17840936158 := by rw [factor_1_18]; decide
      have factor_1_20 : (106 : ZMod 32125373281) ^ 1307184 = 9960724881 := by
        calc
          (106 : ZMod 32125373281) ^ 1307184 = (106 : ZMod 32125373281) ^ (653592 + 653592) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 653592 * (106 : ZMod 32125373281) ^ 653592 := by rw [pow_add]
          _ = 9960724881 := by rw [factor_1_19]; decide
      have factor_1_21 : (106 : ZMod 32125373281) ^ 2614369 = 840444346 := by
        calc
          (106 : ZMod 32125373281) ^ 2614369 = (106 : ZMod 32125373281) ^ (1307184 + 1307184 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 1307184 * (106 : ZMod 32125373281) ^ 1307184) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 840444346 := by rw [factor_1_20]; decide
      have factor_1_22 : (106 : ZMod 32125373281) ^ 5228739 = 15608012035 := by
        calc
          (106 : ZMod 32125373281) ^ 5228739 = (106 : ZMod 32125373281) ^ (2614369 + 2614369 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 2614369 * (106 : ZMod 32125373281) ^ 2614369) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 15608012035 := by rw [factor_1_21]; decide
      have factor_1_23 : (106 : ZMod 32125373281) ^ 10457478 = 27266619202 := by
        calc
          (106 : ZMod 32125373281) ^ 10457478 = (106 : ZMod 32125373281) ^ (5228739 + 5228739) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 5228739 * (106 : ZMod 32125373281) ^ 5228739 := by rw [pow_add]
          _ = 27266619202 := by rw [factor_1_22]; decide
      have factor_1_24 : (106 : ZMod 32125373281) ^ 20914956 = 17789883241 := by
        calc
          (106 : ZMod 32125373281) ^ 20914956 = (106 : ZMod 32125373281) ^ (10457478 + 10457478) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 10457478 * (106 : ZMod 32125373281) ^ 10457478 := by rw [pow_add]
          _ = 17789883241 := by rw [factor_1_23]; decide
      have factor_1_25 : (106 : ZMod 32125373281) ^ 41829913 = 24177711345 := by
        calc
          (106 : ZMod 32125373281) ^ 41829913 = (106 : ZMod 32125373281) ^ (20914956 + 20914956 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 20914956 * (106 : ZMod 32125373281) ^ 20914956) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 24177711345 := by rw [factor_1_24]; decide
      have factor_1_26 : (106 : ZMod 32125373281) ^ 83659826 = 11695861062 := by
        calc
          (106 : ZMod 32125373281) ^ 83659826 = (106 : ZMod 32125373281) ^ (41829913 + 41829913) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 41829913 * (106 : ZMod 32125373281) ^ 41829913 := by rw [pow_add]
          _ = 11695861062 := by rw [factor_1_25]; decide
      have factor_1_27 : (106 : ZMod 32125373281) ^ 167319652 = 831893575 := by
        calc
          (106 : ZMod 32125373281) ^ 167319652 = (106 : ZMod 32125373281) ^ (83659826 + 83659826) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 83659826 * (106 : ZMod 32125373281) ^ 83659826 := by rw [pow_add]
          _ = 831893575 := by rw [factor_1_26]; decide
      have factor_1_28 : (106 : ZMod 32125373281) ^ 334639305 = 15517808506 := by
        calc
          (106 : ZMod 32125373281) ^ 334639305 = (106 : ZMod 32125373281) ^ (167319652 + 167319652 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 167319652 * (106 : ZMod 32125373281) ^ 167319652) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 15517808506 := by rw [factor_1_27]; decide
      have factor_1_29 : (106 : ZMod 32125373281) ^ 669278610 = 10684290938 := by
        calc
          (106 : ZMod 32125373281) ^ 669278610 = (106 : ZMod 32125373281) ^ (334639305 + 334639305) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 334639305 * (106 : ZMod 32125373281) ^ 334639305 := by rw [pow_add]
          _ = 10684290938 := by rw [factor_1_28]; decide
      have factor_1_30 : (106 : ZMod 32125373281) ^ 1338557220 = 3154414159 := by
        calc
          (106 : ZMod 32125373281) ^ 1338557220 = (106 : ZMod 32125373281) ^ (669278610 + 669278610) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 669278610 * (106 : ZMod 32125373281) ^ 669278610 := by rw [pow_add]
          _ = 3154414159 := by rw [factor_1_29]; decide
      have factor_1_31 : (106 : ZMod 32125373281) ^ 2677114440 = 30336116783 := by
        calc
          (106 : ZMod 32125373281) ^ 2677114440 = (106 : ZMod 32125373281) ^ (1338557220 + 1338557220) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1338557220 * (106 : ZMod 32125373281) ^ 1338557220 := by rw [pow_add]
          _ = 30336116783 := by rw [factor_1_30]; decide
      have factor_1_32 : (106 : ZMod 32125373281) ^ 5354228880 = 869477479 := by
        calc
          (106 : ZMod 32125373281) ^ 5354228880 = (106 : ZMod 32125373281) ^ (2677114440 + 2677114440) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 2677114440 * (106 : ZMod 32125373281) ^ 2677114440 := by rw [pow_add]
          _ = 869477479 := by rw [factor_1_31]; decide
      have factor_1_33 : (106 : ZMod 32125373281) ^ 10708457760 = 869477478 := by
        calc
          (106 : ZMod 32125373281) ^ 10708457760 = (106 : ZMod 32125373281) ^ (5354228880 + 5354228880) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 5354228880 * (106 : ZMod 32125373281) ^ 5354228880 := by rw [pow_add]
          _ = 869477478 := by rw [factor_1_32]; decide
      change (106 : ZMod 32125373281) ^ 10708457760 ≠ 1
      rw [factor_1_33]
      decide
    ·
      have factor_2_0 : (106 : ZMod 32125373281) ^ 1 = 106 := by norm_num
      have factor_2_1 : (106 : ZMod 32125373281) ^ 2 = 11236 := by
        calc
          (106 : ZMod 32125373281) ^ 2 = (106 : ZMod 32125373281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1 * (106 : ZMod 32125373281) ^ 1 := by rw [pow_add]
          _ = 11236 := by rw [factor_2_0]; decide
      have factor_2_2 : (106 : ZMod 32125373281) ^ 5 = 13382255776 := by
        calc
          (106 : ZMod 32125373281) ^ 5 = (106 : ZMod 32125373281) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 2 * (106 : ZMod 32125373281) ^ 2) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 13382255776 := by rw [factor_2_1]; decide
      have factor_2_3 : (106 : ZMod 32125373281) ^ 11 = 27089318871 := by
        calc
          (106 : ZMod 32125373281) ^ 11 = (106 : ZMod 32125373281) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 5 * (106 : ZMod 32125373281) ^ 5) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 27089318871 := by rw [factor_2_2]; decide
      have factor_2_4 : (106 : ZMod 32125373281) ^ 23 = 14246252844 := by
        calc
          (106 : ZMod 32125373281) ^ 23 = (106 : ZMod 32125373281) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 11 * (106 : ZMod 32125373281) ^ 11) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 14246252844 := by rw [factor_2_3]; decide
      have factor_2_5 : (106 : ZMod 32125373281) ^ 47 = 16691888972 := by
        calc
          (106 : ZMod 32125373281) ^ 47 = (106 : ZMod 32125373281) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 23 * (106 : ZMod 32125373281) ^ 23) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 16691888972 := by rw [factor_2_4]; decide
      have factor_2_6 : (106 : ZMod 32125373281) ^ 95 = 1173294168 := by
        calc
          (106 : ZMod 32125373281) ^ 95 = (106 : ZMod 32125373281) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 47 * (106 : ZMod 32125373281) ^ 47) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 1173294168 := by rw [factor_2_5]; decide
      have factor_2_7 : (106 : ZMod 32125373281) ^ 191 = 16539597918 := by
        calc
          (106 : ZMod 32125373281) ^ 191 = (106 : ZMod 32125373281) ^ (95 + 95 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 95 * (106 : ZMod 32125373281) ^ 95) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 16539597918 := by rw [factor_2_6]; decide
      have factor_2_8 : (106 : ZMod 32125373281) ^ 382 = 24659306629 := by
        calc
          (106 : ZMod 32125373281) ^ 382 = (106 : ZMod 32125373281) ^ (191 + 191) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 191 * (106 : ZMod 32125373281) ^ 191 := by rw [pow_add]
          _ = 24659306629 := by rw [factor_2_7]; decide
      have factor_2_9 : (106 : ZMod 32125373281) ^ 765 = 3543782351 := by
        calc
          (106 : ZMod 32125373281) ^ 765 = (106 : ZMod 32125373281) ^ (382 + 382 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 382 * (106 : ZMod 32125373281) ^ 382) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 3543782351 := by rw [factor_2_8]; decide
      have factor_2_10 : (106 : ZMod 32125373281) ^ 1531 = 26844701909 := by
        calc
          (106 : ZMod 32125373281) ^ 1531 = (106 : ZMod 32125373281) ^ (765 + 765 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 765 * (106 : ZMod 32125373281) ^ 765) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 26844701909 := by rw [factor_2_9]; decide
      have factor_2_11 : (106 : ZMod 32125373281) ^ 3063 = 2198185316 := by
        calc
          (106 : ZMod 32125373281) ^ 3063 = (106 : ZMod 32125373281) ^ (1531 + 1531 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 1531 * (106 : ZMod 32125373281) ^ 1531) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 2198185316 := by rw [factor_2_10]; decide
      have factor_2_12 : (106 : ZMod 32125373281) ^ 6127 = 21999654263 := by
        calc
          (106 : ZMod 32125373281) ^ 6127 = (106 : ZMod 32125373281) ^ (3063 + 3063 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 3063 * (106 : ZMod 32125373281) ^ 3063) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 21999654263 := by rw [factor_2_11]; decide
      have factor_2_13 : (106 : ZMod 32125373281) ^ 12254 = 10276441580 := by
        calc
          (106 : ZMod 32125373281) ^ 12254 = (106 : ZMod 32125373281) ^ (6127 + 6127) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 6127 * (106 : ZMod 32125373281) ^ 6127 := by rw [pow_add]
          _ = 10276441580 := by rw [factor_2_12]; decide
      have factor_2_14 : (106 : ZMod 32125373281) ^ 24509 = 10641824882 := by
        calc
          (106 : ZMod 32125373281) ^ 24509 = (106 : ZMod 32125373281) ^ (12254 + 12254 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 12254 * (106 : ZMod 32125373281) ^ 12254) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 10641824882 := by rw [factor_2_13]; decide
      have factor_2_15 : (106 : ZMod 32125373281) ^ 49019 = 9414257109 := by
        calc
          (106 : ZMod 32125373281) ^ 49019 = (106 : ZMod 32125373281) ^ (24509 + 24509 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 24509 * (106 : ZMod 32125373281) ^ 24509) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 9414257109 := by rw [factor_2_14]; decide
      have factor_2_16 : (106 : ZMod 32125373281) ^ 98038 = 8062124554 := by
        calc
          (106 : ZMod 32125373281) ^ 98038 = (106 : ZMod 32125373281) ^ (49019 + 49019) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 49019 * (106 : ZMod 32125373281) ^ 49019 := by rw [pow_add]
          _ = 8062124554 := by rw [factor_2_15]; decide
      have factor_2_17 : (106 : ZMod 32125373281) ^ 196077 = 23660484388 := by
        calc
          (106 : ZMod 32125373281) ^ 196077 = (106 : ZMod 32125373281) ^ (98038 + 98038 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 98038 * (106 : ZMod 32125373281) ^ 98038) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 23660484388 := by rw [factor_2_16]; decide
      have factor_2_18 : (106 : ZMod 32125373281) ^ 392155 = 4000034455 := by
        calc
          (106 : ZMod 32125373281) ^ 392155 = (106 : ZMod 32125373281) ^ (196077 + 196077 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 196077 * (106 : ZMod 32125373281) ^ 196077) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 4000034455 := by rw [factor_2_17]; decide
      have factor_2_19 : (106 : ZMod 32125373281) ^ 784310 = 23497463998 := by
        calc
          (106 : ZMod 32125373281) ^ 784310 = (106 : ZMod 32125373281) ^ (392155 + 392155) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 392155 * (106 : ZMod 32125373281) ^ 392155 := by rw [pow_add]
          _ = 23497463998 := by rw [factor_2_18]; decide
      have factor_2_20 : (106 : ZMod 32125373281) ^ 1568621 = 22801038938 := by
        calc
          (106 : ZMod 32125373281) ^ 1568621 = (106 : ZMod 32125373281) ^ (784310 + 784310 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 784310 * (106 : ZMod 32125373281) ^ 784310) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 22801038938 := by rw [factor_2_19]; decide
      have factor_2_21 : (106 : ZMod 32125373281) ^ 3137243 = 5212497805 := by
        calc
          (106 : ZMod 32125373281) ^ 3137243 = (106 : ZMod 32125373281) ^ (1568621 + 1568621 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 1568621 * (106 : ZMod 32125373281) ^ 1568621) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 5212497805 := by rw [factor_2_20]; decide
      have factor_2_22 : (106 : ZMod 32125373281) ^ 6274486 = 699735826 := by
        calc
          (106 : ZMod 32125373281) ^ 6274486 = (106 : ZMod 32125373281) ^ (3137243 + 3137243) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 3137243 * (106 : ZMod 32125373281) ^ 3137243 := by rw [pow_add]
          _ = 699735826 := by rw [factor_2_21]; decide
      have factor_2_23 : (106 : ZMod 32125373281) ^ 12548973 = 15162255120 := by
        calc
          (106 : ZMod 32125373281) ^ 12548973 = (106 : ZMod 32125373281) ^ (6274486 + 6274486 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 6274486 * (106 : ZMod 32125373281) ^ 6274486) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 15162255120 := by rw [factor_2_22]; decide
      have factor_2_24 : (106 : ZMod 32125373281) ^ 25097947 = 9433541383 := by
        calc
          (106 : ZMod 32125373281) ^ 25097947 = (106 : ZMod 32125373281) ^ (12548973 + 12548973 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 12548973 * (106 : ZMod 32125373281) ^ 12548973) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 9433541383 := by rw [factor_2_23]; decide
      have factor_2_25 : (106 : ZMod 32125373281) ^ 50195895 = 7617080423 := by
        calc
          (106 : ZMod 32125373281) ^ 50195895 = (106 : ZMod 32125373281) ^ (25097947 + 25097947 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 25097947 * (106 : ZMod 32125373281) ^ 25097947) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 7617080423 := by rw [factor_2_24]; decide
      have factor_2_26 : (106 : ZMod 32125373281) ^ 100391791 = 15328540429 := by
        calc
          (106 : ZMod 32125373281) ^ 100391791 = (106 : ZMod 32125373281) ^ (50195895 + 50195895 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 50195895 * (106 : ZMod 32125373281) ^ 50195895) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 15328540429 := by rw [factor_2_25]; decide
      have factor_2_27 : (106 : ZMod 32125373281) ^ 200783583 = 24800739302 := by
        calc
          (106 : ZMod 32125373281) ^ 200783583 = (106 : ZMod 32125373281) ^ (100391791 + 100391791 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 100391791 * (106 : ZMod 32125373281) ^ 100391791) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 24800739302 := by rw [factor_2_26]; decide
      have factor_2_28 : (106 : ZMod 32125373281) ^ 401567166 = 27590594832 := by
        calc
          (106 : ZMod 32125373281) ^ 401567166 = (106 : ZMod 32125373281) ^ (200783583 + 200783583) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 200783583 * (106 : ZMod 32125373281) ^ 200783583 := by rw [pow_add]
          _ = 27590594832 := by rw [factor_2_27]; decide
      have factor_2_29 : (106 : ZMod 32125373281) ^ 803134332 = 10217883735 := by
        calc
          (106 : ZMod 32125373281) ^ 803134332 = (106 : ZMod 32125373281) ^ (401567166 + 401567166) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 401567166 * (106 : ZMod 32125373281) ^ 401567166 := by rw [pow_add]
          _ = 10217883735 := by rw [factor_2_28]; decide
      have factor_2_30 : (106 : ZMod 32125373281) ^ 1606268664 = 5878418771 := by
        calc
          (106 : ZMod 32125373281) ^ 1606268664 = (106 : ZMod 32125373281) ^ (803134332 + 803134332) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 803134332 * (106 : ZMod 32125373281) ^ 803134332 := by rw [pow_add]
          _ = 5878418771 := by rw [factor_2_29]; decide
      have factor_2_31 : (106 : ZMod 32125373281) ^ 3212537328 = 30300997229 := by
        calc
          (106 : ZMod 32125373281) ^ 3212537328 = (106 : ZMod 32125373281) ^ (1606268664 + 1606268664) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1606268664 * (106 : ZMod 32125373281) ^ 1606268664 := by rw [pow_add]
          _ = 30300997229 := by rw [factor_2_30]; decide
      have factor_2_32 : (106 : ZMod 32125373281) ^ 6425074656 = 29598779506 := by
        calc
          (106 : ZMod 32125373281) ^ 6425074656 = (106 : ZMod 32125373281) ^ (3212537328 + 3212537328) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 3212537328 * (106 : ZMod 32125373281) ^ 3212537328 := by rw [pow_add]
          _ = 29598779506 := by rw [factor_2_31]; decide
      change (106 : ZMod 32125373281) ^ 6425074656 ≠ 1
      rw [factor_2_32]
      decide
    ·
      have factor_3_0 : (106 : ZMod 32125373281) ^ 1 = 106 := by norm_num
      have factor_3_1 : (106 : ZMod 32125373281) ^ 2 = 11236 := by
        calc
          (106 : ZMod 32125373281) ^ 2 = (106 : ZMod 32125373281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1 * (106 : ZMod 32125373281) ^ 1 := by rw [pow_add]
          _ = 11236 := by rw [factor_3_0]; decide
      have factor_3_2 : (106 : ZMod 32125373281) ^ 4 = 126247696 := by
        calc
          (106 : ZMod 32125373281) ^ 4 = (106 : ZMod 32125373281) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 2 * (106 : ZMod 32125373281) ^ 2 := by rw [pow_add]
          _ = 126247696 := by rw [factor_3_1]; decide
      have factor_3_3 : (106 : ZMod 32125373281) ^ 8 = 22923286043 := by
        calc
          (106 : ZMod 32125373281) ^ 8 = (106 : ZMod 32125373281) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 4 * (106 : ZMod 32125373281) ^ 4 := by rw [pow_add]
          _ = 22923286043 := by rw [factor_3_2]; decide
      have factor_3_4 : (106 : ZMod 32125373281) ^ 17 = 27273632792 := by
        calc
          (106 : ZMod 32125373281) ^ 17 = (106 : ZMod 32125373281) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 8 * (106 : ZMod 32125373281) ^ 8) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 27273632792 := by rw [factor_3_3]; decide
      have factor_3_5 : (106 : ZMod 32125373281) ^ 34 = 28169318030 := by
        calc
          (106 : ZMod 32125373281) ^ 34 = (106 : ZMod 32125373281) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 17 * (106 : ZMod 32125373281) ^ 17 := by rw [pow_add]
          _ = 28169318030 := by rw [factor_3_4]; decide
      have factor_3_6 : (106 : ZMod 32125373281) ^ 68 = 29469520154 := by
        calc
          (106 : ZMod 32125373281) ^ 68 = (106 : ZMod 32125373281) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 34 * (106 : ZMod 32125373281) ^ 34 := by rw [pow_add]
          _ = 29469520154 := by rw [factor_3_5]; decide
      have factor_3_7 : (106 : ZMod 32125373281) ^ 136 = 1729268820 := by
        calc
          (106 : ZMod 32125373281) ^ 136 = (106 : ZMod 32125373281) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 68 * (106 : ZMod 32125373281) ^ 68 := by rw [pow_add]
          _ = 1729268820 := by rw [factor_3_6]; decide
      have factor_3_8 : (106 : ZMod 32125373281) ^ 273 = 9793232508 := by
        calc
          (106 : ZMod 32125373281) ^ 273 = (106 : ZMod 32125373281) ^ (136 + 136 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 136 * (106 : ZMod 32125373281) ^ 136) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 9793232508 := by rw [factor_3_7]; decide
      have factor_3_9 : (106 : ZMod 32125373281) ^ 547 = 23005692002 := by
        calc
          (106 : ZMod 32125373281) ^ 547 = (106 : ZMod 32125373281) ^ (273 + 273 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 273 * (106 : ZMod 32125373281) ^ 273) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 23005692002 := by rw [factor_3_8]; decide
      have factor_3_10 : (106 : ZMod 32125373281) ^ 1094 = 19318031863 := by
        calc
          (106 : ZMod 32125373281) ^ 1094 = (106 : ZMod 32125373281) ^ (547 + 547) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 547 * (106 : ZMod 32125373281) ^ 547 := by rw [pow_add]
          _ = 19318031863 := by rw [factor_3_9]; decide
      have factor_3_11 : (106 : ZMod 32125373281) ^ 2188 = 2290057712 := by
        calc
          (106 : ZMod 32125373281) ^ 2188 = (106 : ZMod 32125373281) ^ (1094 + 1094) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1094 * (106 : ZMod 32125373281) ^ 1094 := by rw [pow_add]
          _ = 2290057712 := by rw [factor_3_10]; decide
      have factor_3_12 : (106 : ZMod 32125373281) ^ 4376 = 1612670706 := by
        calc
          (106 : ZMod 32125373281) ^ 4376 = (106 : ZMod 32125373281) ^ (2188 + 2188) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 2188 * (106 : ZMod 32125373281) ^ 2188 := by rw [pow_add]
          _ = 1612670706 := by rw [factor_3_11]; decide
      have factor_3_13 : (106 : ZMod 32125373281) ^ 8753 = 28315629416 := by
        calc
          (106 : ZMod 32125373281) ^ 8753 = (106 : ZMod 32125373281) ^ (4376 + 4376 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 4376 * (106 : ZMod 32125373281) ^ 4376) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 28315629416 := by rw [factor_3_12]; decide
      have factor_3_14 : (106 : ZMod 32125373281) ^ 17506 = 16657236233 := by
        calc
          (106 : ZMod 32125373281) ^ 17506 = (106 : ZMod 32125373281) ^ (8753 + 8753) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 8753 * (106 : ZMod 32125373281) ^ 8753 := by rw [pow_add]
          _ = 16657236233 := by rw [factor_3_13]; decide
      have factor_3_15 : (106 : ZMod 32125373281) ^ 35013 = 17388589121 := by
        calc
          (106 : ZMod 32125373281) ^ 35013 = (106 : ZMod 32125373281) ^ (17506 + 17506 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 17506 * (106 : ZMod 32125373281) ^ 17506) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 17388589121 := by rw [factor_3_14]; decide
      have factor_3_16 : (106 : ZMod 32125373281) ^ 70027 = 20636275303 := by
        calc
          (106 : ZMod 32125373281) ^ 70027 = (106 : ZMod 32125373281) ^ (35013 + 35013 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 35013 * (106 : ZMod 32125373281) ^ 35013) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 20636275303 := by rw [factor_3_15]; decide
      have factor_3_17 : (106 : ZMod 32125373281) ^ 140055 = 25862288376 := by
        calc
          (106 : ZMod 32125373281) ^ 140055 = (106 : ZMod 32125373281) ^ (70027 + 70027 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 70027 * (106 : ZMod 32125373281) ^ 70027) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 25862288376 := by rw [factor_3_16]; decide
      have factor_3_18 : (106 : ZMod 32125373281) ^ 280111 = 14288498284 := by
        calc
          (106 : ZMod 32125373281) ^ 280111 = (106 : ZMod 32125373281) ^ (140055 + 140055 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 140055 * (106 : ZMod 32125373281) ^ 140055) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 14288498284 := by rw [factor_3_17]; decide
      have factor_3_19 : (106 : ZMod 32125373281) ^ 560222 = 11071811052 := by
        calc
          (106 : ZMod 32125373281) ^ 560222 = (106 : ZMod 32125373281) ^ (280111 + 280111) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 280111 * (106 : ZMod 32125373281) ^ 280111 := by rw [pow_add]
          _ = 11071811052 := by rw [factor_3_18]; decide
      have factor_3_20 : (106 : ZMod 32125373281) ^ 1120444 = 28673336678 := by
        calc
          (106 : ZMod 32125373281) ^ 1120444 = (106 : ZMod 32125373281) ^ (560222 + 560222) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 560222 * (106 : ZMod 32125373281) ^ 560222 := by rw [pow_add]
          _ = 28673336678 := by rw [factor_3_19]; decide
      have factor_3_21 : (106 : ZMod 32125373281) ^ 2240888 = 9812698600 := by
        calc
          (106 : ZMod 32125373281) ^ 2240888 = (106 : ZMod 32125373281) ^ (1120444 + 1120444) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1120444 * (106 : ZMod 32125373281) ^ 1120444 := by rw [pow_add]
          _ = 9812698600 := by rw [factor_3_20]; decide
      have factor_3_22 : (106 : ZMod 32125373281) ^ 4481776 = 29606633076 := by
        calc
          (106 : ZMod 32125373281) ^ 4481776 = (106 : ZMod 32125373281) ^ (2240888 + 2240888) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 2240888 * (106 : ZMod 32125373281) ^ 2240888 := by rw [pow_add]
          _ = 29606633076 := by rw [factor_3_21]; decide
      have factor_3_23 : (106 : ZMod 32125373281) ^ 8963552 = 4274253695 := by
        calc
          (106 : ZMod 32125373281) ^ 8963552 = (106 : ZMod 32125373281) ^ (4481776 + 4481776) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 4481776 * (106 : ZMod 32125373281) ^ 4481776 := by rw [pow_add]
          _ = 4274253695 := by rw [factor_3_22]; decide
      have factor_3_24 : (106 : ZMod 32125373281) ^ 17927105 = 25370255524 := by
        calc
          (106 : ZMod 32125373281) ^ 17927105 = (106 : ZMod 32125373281) ^ (8963552 + 8963552 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 8963552 * (106 : ZMod 32125373281) ^ 8963552) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 25370255524 := by rw [factor_3_23]; decide
      have factor_3_25 : (106 : ZMod 32125373281) ^ 35854211 = 3915850570 := by
        calc
          (106 : ZMod 32125373281) ^ 35854211 = (106 : ZMod 32125373281) ^ (17927105 + 17927105 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 17927105 * (106 : ZMod 32125373281) ^ 17927105) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 3915850570 := by rw [factor_3_24]; decide
      have factor_3_26 : (106 : ZMod 32125373281) ^ 71708422 = 18877336488 := by
        calc
          (106 : ZMod 32125373281) ^ 71708422 = (106 : ZMod 32125373281) ^ (35854211 + 35854211) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 35854211 * (106 : ZMod 32125373281) ^ 35854211 := by rw [pow_add]
          _ = 18877336488 := by rw [factor_3_25]; decide
      have factor_3_27 : (106 : ZMod 32125373281) ^ 143416845 = 24268232389 := by
        calc
          (106 : ZMod 32125373281) ^ 143416845 = (106 : ZMod 32125373281) ^ (71708422 + 71708422 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 71708422 * (106 : ZMod 32125373281) ^ 71708422) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 24268232389 := by rw [factor_3_26]; decide
      have factor_3_28 : (106 : ZMod 32125373281) ^ 286833690 = 21139422662 := by
        calc
          (106 : ZMod 32125373281) ^ 286833690 = (106 : ZMod 32125373281) ^ (143416845 + 143416845) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 143416845 * (106 : ZMod 32125373281) ^ 143416845 := by rw [pow_add]
          _ = 21139422662 := by rw [factor_3_27]; decide
      have factor_3_29 : (106 : ZMod 32125373281) ^ 573667380 = 22771543152 := by
        calc
          (106 : ZMod 32125373281) ^ 573667380 = (106 : ZMod 32125373281) ^ (286833690 + 286833690) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 286833690 * (106 : ZMod 32125373281) ^ 286833690 := by rw [pow_add]
          _ = 22771543152 := by rw [factor_3_28]; decide
      have factor_3_30 : (106 : ZMod 32125373281) ^ 1147334760 = 2187504151 := by
        calc
          (106 : ZMod 32125373281) ^ 1147334760 = (106 : ZMod 32125373281) ^ (573667380 + 573667380) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 573667380 * (106 : ZMod 32125373281) ^ 573667380 := by rw [pow_add]
          _ = 2187504151 := by rw [factor_3_29]; decide
      have factor_3_31 : (106 : ZMod 32125373281) ^ 2294669520 = 22024883767 := by
        calc
          (106 : ZMod 32125373281) ^ 2294669520 = (106 : ZMod 32125373281) ^ (1147334760 + 1147334760) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1147334760 * (106 : ZMod 32125373281) ^ 1147334760 := by rw [pow_add]
          _ = 22024883767 := by rw [factor_3_30]; decide
      have factor_3_32 : (106 : ZMod 32125373281) ^ 4589339040 = 27865715126 := by
        calc
          (106 : ZMod 32125373281) ^ 4589339040 = (106 : ZMod 32125373281) ^ (2294669520 + 2294669520) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 2294669520 * (106 : ZMod 32125373281) ^ 2294669520 := by rw [pow_add]
          _ = 27865715126 := by rw [factor_3_31]; decide
      change (106 : ZMod 32125373281) ^ 4589339040 ≠ 1
      rw [factor_3_32]
      decide
    ·
      have factor_4_0 : (106 : ZMod 32125373281) ^ 1 = 106 := by norm_num
      have factor_4_1 : (106 : ZMod 32125373281) ^ 2 = 11236 := by
        calc
          (106 : ZMod 32125373281) ^ 2 = (106 : ZMod 32125373281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1 * (106 : ZMod 32125373281) ^ 1 := by rw [pow_add]
          _ = 11236 := by rw [factor_4_0]; decide
      have factor_4_2 : (106 : ZMod 32125373281) ^ 5 = 13382255776 := by
        calc
          (106 : ZMod 32125373281) ^ 5 = (106 : ZMod 32125373281) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 2 * (106 : ZMod 32125373281) ^ 2) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 13382255776 := by rw [factor_4_1]; decide
      have factor_4_3 : (106 : ZMod 32125373281) ^ 10 = 16924385371 := by
        calc
          (106 : ZMod 32125373281) ^ 10 = (106 : ZMod 32125373281) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 5 * (106 : ZMod 32125373281) ^ 5 := by rw [pow_add]
          _ = 16924385371 := by rw [factor_4_2]; decide
      have factor_4_4 : (106 : ZMod 32125373281) ^ 21 = 5616632198 := by
        calc
          (106 : ZMod 32125373281) ^ 21 = (106 : ZMod 32125373281) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 10 * (106 : ZMod 32125373281) ^ 10) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 5616632198 := by rw [factor_4_3]; decide
      have factor_4_5 : (106 : ZMod 32125373281) ^ 43 = 25105699843 := by
        calc
          (106 : ZMod 32125373281) ^ 43 = (106 : ZMod 32125373281) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 21 * (106 : ZMod 32125373281) ^ 21) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 25105699843 := by rw [factor_4_4]; decide
      have factor_4_6 : (106 : ZMod 32125373281) ^ 87 = 30191396560 := by
        calc
          (106 : ZMod 32125373281) ^ 87 = (106 : ZMod 32125373281) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 43 * (106 : ZMod 32125373281) ^ 43) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 30191396560 := by rw [factor_4_5]; decide
      have factor_4_7 : (106 : ZMod 32125373281) ^ 174 = 14448573162 := by
        calc
          (106 : ZMod 32125373281) ^ 174 = (106 : ZMod 32125373281) ^ (87 + 87) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 87 * (106 : ZMod 32125373281) ^ 87 := by rw [pow_add]
          _ = 14448573162 := by rw [factor_4_6]; decide
      have factor_4_8 : (106 : ZMod 32125373281) ^ 348 = 1668384412 := by
        calc
          (106 : ZMod 32125373281) ^ 348 = (106 : ZMod 32125373281) ^ (174 + 174) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 174 * (106 : ZMod 32125373281) ^ 174 := by rw [pow_add]
          _ = 1668384412 := by rw [factor_4_7]; decide
      have factor_4_9 : (106 : ZMod 32125373281) ^ 696 = 12355906553 := by
        calc
          (106 : ZMod 32125373281) ^ 696 = (106 : ZMod 32125373281) ^ (348 + 348) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 348 * (106 : ZMod 32125373281) ^ 348 := by rw [pow_add]
          _ = 12355906553 := by rw [factor_4_8]; decide
      have factor_4_10 : (106 : ZMod 32125373281) ^ 1392 = 10113851021 := by
        calc
          (106 : ZMod 32125373281) ^ 1392 = (106 : ZMod 32125373281) ^ (696 + 696) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 696 * (106 : ZMod 32125373281) ^ 696 := by rw [pow_add]
          _ = 10113851021 := by rw [factor_4_9]; decide
      have factor_4_11 : (106 : ZMod 32125373281) ^ 2785 = 1955751111 := by
        calc
          (106 : ZMod 32125373281) ^ 2785 = (106 : ZMod 32125373281) ^ (1392 + 1392 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 1392 * (106 : ZMod 32125373281) ^ 1392) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 1955751111 := by rw [factor_4_10]; decide
      have factor_4_12 : (106 : ZMod 32125373281) ^ 5570 = 6750302407 := by
        calc
          (106 : ZMod 32125373281) ^ 5570 = (106 : ZMod 32125373281) ^ (2785 + 2785) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 2785 * (106 : ZMod 32125373281) ^ 2785 := by rw [pow_add]
          _ = 6750302407 := by rw [factor_4_11]; decide
      have factor_4_13 : (106 : ZMod 32125373281) ^ 11140 = 27224583909 := by
        calc
          (106 : ZMod 32125373281) ^ 11140 = (106 : ZMod 32125373281) ^ (5570 + 5570) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 5570 * (106 : ZMod 32125373281) ^ 5570 := by rw [pow_add]
          _ = 27224583909 := by rw [factor_4_12]; decide
      have factor_4_14 : (106 : ZMod 32125373281) ^ 22281 = 16922705257 := by
        calc
          (106 : ZMod 32125373281) ^ 22281 = (106 : ZMod 32125373281) ^ (11140 + 11140 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 11140 * (106 : ZMod 32125373281) ^ 11140) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 16922705257 := by rw [factor_4_13]; decide
      have factor_4_15 : (106 : ZMod 32125373281) ^ 44563 = 30678136303 := by
        calc
          (106 : ZMod 32125373281) ^ 44563 = (106 : ZMod 32125373281) ^ (22281 + 22281 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 22281 * (106 : ZMod 32125373281) ^ 22281) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 30678136303 := by rw [factor_4_14]; decide
      have factor_4_16 : (106 : ZMod 32125373281) ^ 89126 = 10742869678 := by
        calc
          (106 : ZMod 32125373281) ^ 89126 = (106 : ZMod 32125373281) ^ (44563 + 44563) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 44563 * (106 : ZMod 32125373281) ^ 44563 := by rw [pow_add]
          _ = 10742869678 := by rw [factor_4_15]; decide
      have factor_4_17 : (106 : ZMod 32125373281) ^ 178252 = 24540416105 := by
        calc
          (106 : ZMod 32125373281) ^ 178252 = (106 : ZMod 32125373281) ^ (89126 + 89126) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 89126 * (106 : ZMod 32125373281) ^ 89126 := by rw [pow_add]
          _ = 24540416105 := by rw [factor_4_16]; decide
      have factor_4_18 : (106 : ZMod 32125373281) ^ 356504 = 4460801626 := by
        calc
          (106 : ZMod 32125373281) ^ 356504 = (106 : ZMod 32125373281) ^ (178252 + 178252) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 178252 * (106 : ZMod 32125373281) ^ 178252 := by rw [pow_add]
          _ = 4460801626 := by rw [factor_4_17]; decide
      have factor_4_19 : (106 : ZMod 32125373281) ^ 713009 = 20283193053 := by
        calc
          (106 : ZMod 32125373281) ^ 713009 = (106 : ZMod 32125373281) ^ (356504 + 356504 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 356504 * (106 : ZMod 32125373281) ^ 356504) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 20283193053 := by rw [factor_4_18]; decide
      have factor_4_20 : (106 : ZMod 32125373281) ^ 1426019 = 23949758893 := by
        calc
          (106 : ZMod 32125373281) ^ 1426019 = (106 : ZMod 32125373281) ^ (713009 + 713009 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 713009 * (106 : ZMod 32125373281) ^ 713009) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 23949758893 := by rw [factor_4_19]; decide
      have factor_4_21 : (106 : ZMod 32125373281) ^ 2852039 = 23851957719 := by
        calc
          (106 : ZMod 32125373281) ^ 2852039 = (106 : ZMod 32125373281) ^ (1426019 + 1426019 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 1426019 * (106 : ZMod 32125373281) ^ 1426019) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 23851957719 := by rw [factor_4_20]; decide
      have factor_4_22 : (106 : ZMod 32125373281) ^ 5704079 = 9277853271 := by
        calc
          (106 : ZMod 32125373281) ^ 5704079 = (106 : ZMod 32125373281) ^ (2852039 + 2852039 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 2852039 * (106 : ZMod 32125373281) ^ 2852039) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 9277853271 := by rw [factor_4_21]; decide
      have factor_4_23 : (106 : ZMod 32125373281) ^ 11408158 = 23384123886 := by
        calc
          (106 : ZMod 32125373281) ^ 11408158 = (106 : ZMod 32125373281) ^ (5704079 + 5704079) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 5704079 * (106 : ZMod 32125373281) ^ 5704079 := by rw [pow_add]
          _ = 23384123886 := by rw [factor_4_22]; decide
      have factor_4_24 : (106 : ZMod 32125373281) ^ 22816316 = 16302982303 := by
        calc
          (106 : ZMod 32125373281) ^ 22816316 = (106 : ZMod 32125373281) ^ (11408158 + 11408158) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 11408158 * (106 : ZMod 32125373281) ^ 11408158 := by rw [pow_add]
          _ = 16302982303 := by rw [factor_4_23]; decide
      have factor_4_25 : (106 : ZMod 32125373281) ^ 45632632 = 12076567591 := by
        calc
          (106 : ZMod 32125373281) ^ 45632632 = (106 : ZMod 32125373281) ^ (22816316 + 22816316) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 22816316 * (106 : ZMod 32125373281) ^ 22816316 := by rw [pow_add]
          _ = 12076567591 := by rw [factor_4_24]; decide
      have factor_4_26 : (106 : ZMod 32125373281) ^ 91265265 = 22632893028 := by
        calc
          (106 : ZMod 32125373281) ^ 91265265 = (106 : ZMod 32125373281) ^ (45632632 + 45632632 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 45632632 * (106 : ZMod 32125373281) ^ 45632632) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 22632893028 := by rw [factor_4_25]; decide
      have factor_4_27 : (106 : ZMod 32125373281) ^ 182530530 = 9944775156 := by
        calc
          (106 : ZMod 32125373281) ^ 182530530 = (106 : ZMod 32125373281) ^ (91265265 + 91265265) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 91265265 * (106 : ZMod 32125373281) ^ 91265265 := by rw [pow_add]
          _ = 9944775156 := by rw [factor_4_26]; decide
      have factor_4_28 : (106 : ZMod 32125373281) ^ 365061060 = 22466460812 := by
        calc
          (106 : ZMod 32125373281) ^ 365061060 = (106 : ZMod 32125373281) ^ (182530530 + 182530530) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 182530530 * (106 : ZMod 32125373281) ^ 182530530 := by rw [pow_add]
          _ = 22466460812 := by rw [factor_4_27]; decide
      have factor_4_29 : (106 : ZMod 32125373281) ^ 730122120 = 7535398432 := by
        calc
          (106 : ZMod 32125373281) ^ 730122120 = (106 : ZMod 32125373281) ^ (365061060 + 365061060) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 365061060 * (106 : ZMod 32125373281) ^ 365061060 := by rw [pow_add]
          _ = 7535398432 := by rw [factor_4_28]; decide
      have factor_4_30 : (106 : ZMod 32125373281) ^ 1460244240 = 27474388544 := by
        calc
          (106 : ZMod 32125373281) ^ 1460244240 = (106 : ZMod 32125373281) ^ (730122120 + 730122120) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 730122120 * (106 : ZMod 32125373281) ^ 730122120 := by rw [pow_add]
          _ = 27474388544 := by rw [factor_4_29]; decide
      have factor_4_31 : (106 : ZMod 32125373281) ^ 2920488480 = 21218565878 := by
        calc
          (106 : ZMod 32125373281) ^ 2920488480 = (106 : ZMod 32125373281) ^ (1460244240 + 1460244240) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1460244240 * (106 : ZMod 32125373281) ^ 1460244240 := by rw [pow_add]
          _ = 21218565878 := by rw [factor_4_30]; decide
      change (106 : ZMod 32125373281) ^ 2920488480 ≠ 1
      rw [factor_4_31]
      decide
    ·
      have factor_5_0 : (106 : ZMod 32125373281) ^ 1 = 106 := by norm_num
      have factor_5_1 : (106 : ZMod 32125373281) ^ 2 = 11236 := by
        calc
          (106 : ZMod 32125373281) ^ 2 = (106 : ZMod 32125373281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1 * (106 : ZMod 32125373281) ^ 1 := by rw [pow_add]
          _ = 11236 := by rw [factor_5_0]; decide
      have factor_5_2 : (106 : ZMod 32125373281) ^ 4 = 126247696 := by
        calc
          (106 : ZMod 32125373281) ^ 4 = (106 : ZMod 32125373281) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 2 * (106 : ZMod 32125373281) ^ 2 := by rw [pow_add]
          _ = 126247696 := by rw [factor_5_1]; decide
      have factor_5_3 : (106 : ZMod 32125373281) ^ 9 = 20465324483 := by
        calc
          (106 : ZMod 32125373281) ^ 9 = (106 : ZMod 32125373281) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 4 * (106 : ZMod 32125373281) ^ 4) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 20465324483 := by rw [factor_5_2]; decide
      have factor_5_4 : (106 : ZMod 32125373281) ^ 18 = 31846853943 := by
        calc
          (106 : ZMod 32125373281) ^ 18 = (106 : ZMod 32125373281) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 9 * (106 : ZMod 32125373281) ^ 9 := by rw [pow_add]
          _ = 31846853943 := by rw [factor_5_3]; decide
      have factor_5_5 : (106 : ZMod 32125373281) ^ 36 = 11279820668 := by
        calc
          (106 : ZMod 32125373281) ^ 36 = (106 : ZMod 32125373281) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 18 * (106 : ZMod 32125373281) ^ 18 := by rw [pow_add]
          _ = 11279820668 := by rw [factor_5_4]; decide
      have factor_5_6 : (106 : ZMod 32125373281) ^ 73 = 7449090624 := by
        calc
          (106 : ZMod 32125373281) ^ 73 = (106 : ZMod 32125373281) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 36 * (106 : ZMod 32125373281) ^ 36) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 7449090624 := by rw [factor_5_5]; decide
      have factor_5_7 : (106 : ZMod 32125373281) ^ 147 = 10544813135 := by
        calc
          (106 : ZMod 32125373281) ^ 147 = (106 : ZMod 32125373281) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 73 * (106 : ZMod 32125373281) ^ 73) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 10544813135 := by rw [factor_5_6]; decide
      have factor_5_8 : (106 : ZMod 32125373281) ^ 294 = 19999283687 := by
        calc
          (106 : ZMod 32125373281) ^ 294 = (106 : ZMod 32125373281) ^ (147 + 147) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 147 * (106 : ZMod 32125373281) ^ 147 := by rw [pow_add]
          _ = 19999283687 := by rw [factor_5_7]; decide
      have factor_5_9 : (106 : ZMod 32125373281) ^ 589 = 9135473254 := by
        calc
          (106 : ZMod 32125373281) ^ 589 = (106 : ZMod 32125373281) ^ (294 + 294 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 294 * (106 : ZMod 32125373281) ^ 294) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 9135473254 := by rw [factor_5_8]; decide
      have factor_5_10 : (106 : ZMod 32125373281) ^ 1178 = 23345423912 := by
        calc
          (106 : ZMod 32125373281) ^ 1178 = (106 : ZMod 32125373281) ^ (589 + 589) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 589 * (106 : ZMod 32125373281) ^ 589 := by rw [pow_add]
          _ = 23345423912 := by rw [factor_5_9]; decide
      have factor_5_11 : (106 : ZMod 32125373281) ^ 2356 = 20330280249 := by
        calc
          (106 : ZMod 32125373281) ^ 2356 = (106 : ZMod 32125373281) ^ (1178 + 1178) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1178 * (106 : ZMod 32125373281) ^ 1178 := by rw [pow_add]
          _ = 20330280249 := by rw [factor_5_10]; decide
      have factor_5_12 : (106 : ZMod 32125373281) ^ 4713 = 2746222413 := by
        calc
          (106 : ZMod 32125373281) ^ 4713 = (106 : ZMod 32125373281) ^ (2356 + 2356 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 2356 * (106 : ZMod 32125373281) ^ 2356) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 2746222413 := by rw [factor_5_11]; decide
      have factor_5_13 : (106 : ZMod 32125373281) ^ 9426 = 9141424639 := by
        calc
          (106 : ZMod 32125373281) ^ 9426 = (106 : ZMod 32125373281) ^ (4713 + 4713) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 4713 * (106 : ZMod 32125373281) ^ 4713 := by rw [pow_add]
          _ = 9141424639 := by rw [factor_5_12]; decide
      have factor_5_14 : (106 : ZMod 32125373281) ^ 18853 = 10188069035 := by
        calc
          (106 : ZMod 32125373281) ^ 18853 = (106 : ZMod 32125373281) ^ (9426 + 9426 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 9426 * (106 : ZMod 32125373281) ^ 9426) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 10188069035 := by rw [factor_5_13]; decide
      have factor_5_15 : (106 : ZMod 32125373281) ^ 37707 = 18651415579 := by
        calc
          (106 : ZMod 32125373281) ^ 37707 = (106 : ZMod 32125373281) ^ (18853 + 18853 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 18853 * (106 : ZMod 32125373281) ^ 18853) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 18651415579 := by rw [factor_5_14]; decide
      have factor_5_16 : (106 : ZMod 32125373281) ^ 75414 = 41328337 := by
        calc
          (106 : ZMod 32125373281) ^ 75414 = (106 : ZMod 32125373281) ^ (37707 + 37707) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 37707 * (106 : ZMod 32125373281) ^ 37707 := by rw [pow_add]
          _ = 41328337 := by rw [factor_5_15]; decide
      have factor_5_17 : (106 : ZMod 32125373281) ^ 150829 = 21201689101 := by
        calc
          (106 : ZMod 32125373281) ^ 150829 = (106 : ZMod 32125373281) ^ (75414 + 75414 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 75414 * (106 : ZMod 32125373281) ^ 75414) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 21201689101 := by rw [factor_5_16]; decide
      have factor_5_18 : (106 : ZMod 32125373281) ^ 301658 = 29284840275 := by
        calc
          (106 : ZMod 32125373281) ^ 301658 = (106 : ZMod 32125373281) ^ (150829 + 150829) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 150829 * (106 : ZMod 32125373281) ^ 150829 := by rw [pow_add]
          _ = 29284840275 := by rw [factor_5_17]; decide
      have factor_5_19 : (106 : ZMod 32125373281) ^ 603316 = 18823826965 := by
        calc
          (106 : ZMod 32125373281) ^ 603316 = (106 : ZMod 32125373281) ^ (301658 + 301658) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 301658 * (106 : ZMod 32125373281) ^ 301658 := by rw [pow_add]
          _ = 18823826965 := by rw [factor_5_18]; decide
      have factor_5_20 : (106 : ZMod 32125373281) ^ 1206632 = 21887222782 := by
        calc
          (106 : ZMod 32125373281) ^ 1206632 = (106 : ZMod 32125373281) ^ (603316 + 603316) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 603316 * (106 : ZMod 32125373281) ^ 603316 := by rw [pow_add]
          _ = 21887222782 := by rw [factor_5_19]; decide
      have factor_5_21 : (106 : ZMod 32125373281) ^ 2413264 = 3137245357 := by
        calc
          (106 : ZMod 32125373281) ^ 2413264 = (106 : ZMod 32125373281) ^ (1206632 + 1206632) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1206632 * (106 : ZMod 32125373281) ^ 1206632 := by rw [pow_add]
          _ = 3137245357 := by rw [factor_5_20]; decide
      have factor_5_22 : (106 : ZMod 32125373281) ^ 4826528 = 24371554930 := by
        calc
          (106 : ZMod 32125373281) ^ 4826528 = (106 : ZMod 32125373281) ^ (2413264 + 2413264) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 2413264 * (106 : ZMod 32125373281) ^ 2413264 := by rw [pow_add]
          _ = 24371554930 := by rw [factor_5_21]; decide
      have factor_5_23 : (106 : ZMod 32125373281) ^ 9653056 = 22051465971 := by
        calc
          (106 : ZMod 32125373281) ^ 9653056 = (106 : ZMod 32125373281) ^ (4826528 + 4826528) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 4826528 * (106 : ZMod 32125373281) ^ 4826528 := by rw [pow_add]
          _ = 22051465971 := by rw [factor_5_22]; decide
      have factor_5_24 : (106 : ZMod 32125373281) ^ 19306113 = 20207956754 := by
        calc
          (106 : ZMod 32125373281) ^ 19306113 = (106 : ZMod 32125373281) ^ (9653056 + 9653056 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 9653056 * (106 : ZMod 32125373281) ^ 9653056) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 20207956754 := by rw [factor_5_23]; decide
      have factor_5_25 : (106 : ZMod 32125373281) ^ 38612227 = 13452009462 := by
        calc
          (106 : ZMod 32125373281) ^ 38612227 = (106 : ZMod 32125373281) ^ (19306113 + 19306113 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 19306113 * (106 : ZMod 32125373281) ^ 19306113) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 13452009462 := by rw [factor_5_24]; decide
      have factor_5_26 : (106 : ZMod 32125373281) ^ 77224455 = 31870283078 := by
        calc
          (106 : ZMod 32125373281) ^ 77224455 = (106 : ZMod 32125373281) ^ (38612227 + 38612227 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 38612227 * (106 : ZMod 32125373281) ^ 38612227) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 31870283078 := by rw [factor_5_25]; decide
      have factor_5_27 : (106 : ZMod 32125373281) ^ 154448910 = 7948597436 := by
        calc
          (106 : ZMod 32125373281) ^ 154448910 = (106 : ZMod 32125373281) ^ (77224455 + 77224455) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 77224455 * (106 : ZMod 32125373281) ^ 77224455 := by rw [pow_add]
          _ = 7948597436 := by rw [factor_5_26]; decide
      have factor_5_28 : (106 : ZMod 32125373281) ^ 308897820 = 30670472319 := by
        calc
          (106 : ZMod 32125373281) ^ 308897820 = (106 : ZMod 32125373281) ^ (154448910 + 154448910) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 154448910 * (106 : ZMod 32125373281) ^ 154448910 := by rw [pow_add]
          _ = 30670472319 := by rw [factor_5_27]; decide
      have factor_5_29 : (106 : ZMod 32125373281) ^ 617795640 = 11540468850 := by
        calc
          (106 : ZMod 32125373281) ^ 617795640 = (106 : ZMod 32125373281) ^ (308897820 + 308897820) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 308897820 * (106 : ZMod 32125373281) ^ 308897820 := by rw [pow_add]
          _ = 11540468850 := by rw [factor_5_28]; decide
      have factor_5_30 : (106 : ZMod 32125373281) ^ 1235591280 = 23243101408 := by
        calc
          (106 : ZMod 32125373281) ^ 1235591280 = (106 : ZMod 32125373281) ^ (617795640 + 617795640) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 617795640 * (106 : ZMod 32125373281) ^ 617795640 := by rw [pow_add]
          _ = 23243101408 := by rw [factor_5_29]; decide
      have factor_5_31 : (106 : ZMod 32125373281) ^ 2471182560 = 5619277168 := by
        calc
          (106 : ZMod 32125373281) ^ 2471182560 = (106 : ZMod 32125373281) ^ (1235591280 + 1235591280) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1235591280 * (106 : ZMod 32125373281) ^ 1235591280 := by rw [pow_add]
          _ = 5619277168 := by rw [factor_5_30]; decide
      change (106 : ZMod 32125373281) ^ 2471182560 ≠ 1
      rw [factor_5_31]
      decide
    ·
      have factor_6_0 : (106 : ZMod 32125373281) ^ 1 = 106 := by norm_num
      have factor_6_1 : (106 : ZMod 32125373281) ^ 3 = 1191016 := by
        calc
          (106 : ZMod 32125373281) ^ 3 = (106 : ZMod 32125373281) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 1 * (106 : ZMod 32125373281) ^ 1) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 1191016 := by rw [factor_6_0]; decide
      have factor_6_2 : (106 : ZMod 32125373281) ^ 7 = 16278944056 := by
        calc
          (106 : ZMod 32125373281) ^ 7 = (106 : ZMod 32125373281) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 3 * (106 : ZMod 32125373281) ^ 3) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 16278944056 := by rw [factor_6_1]; decide
      have factor_6_3 : (106 : ZMod 32125373281) ^ 14 = 10689995107 := by
        calc
          (106 : ZMod 32125373281) ^ 14 = (106 : ZMod 32125373281) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 7 * (106 : ZMod 32125373281) ^ 7 := by rw [pow_add]
          _ = 10689995107 := by rw [factor_6_2]; decide
      have factor_6_4 : (106 : ZMod 32125373281) ^ 28 = 5079651754 := by
        calc
          (106 : ZMod 32125373281) ^ 28 = (106 : ZMod 32125373281) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 14 * (106 : ZMod 32125373281) ^ 14 := by rw [pow_add]
          _ = 5079651754 := by rw [factor_6_3]; decide
      have factor_6_5 : (106 : ZMod 32125373281) ^ 56 = 11005222321 := by
        calc
          (106 : ZMod 32125373281) ^ 56 = (106 : ZMod 32125373281) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 28 * (106 : ZMod 32125373281) ^ 28 := by rw [pow_add]
          _ = 11005222321 := by rw [factor_6_4]; decide
      have factor_6_6 : (106 : ZMod 32125373281) ^ 112 = 17244363699 := by
        calc
          (106 : ZMod 32125373281) ^ 112 = (106 : ZMod 32125373281) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 56 * (106 : ZMod 32125373281) ^ 56 := by rw [pow_add]
          _ = 17244363699 := by rw [factor_6_5]; decide
      have factor_6_7 : (106 : ZMod 32125373281) ^ 225 = 5449615173 := by
        calc
          (106 : ZMod 32125373281) ^ 225 = (106 : ZMod 32125373281) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 112 * (106 : ZMod 32125373281) ^ 112) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 5449615173 := by rw [factor_6_6]; decide
      have factor_6_8 : (106 : ZMod 32125373281) ^ 450 = 27872843399 := by
        calc
          (106 : ZMod 32125373281) ^ 450 = (106 : ZMod 32125373281) ^ (225 + 225) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 225 * (106 : ZMod 32125373281) ^ 225 := by rw [pow_add]
          _ = 27872843399 := by rw [factor_6_7]; decide
      have factor_6_9 : (106 : ZMod 32125373281) ^ 901 = 28842045792 := by
        calc
          (106 : ZMod 32125373281) ^ 901 = (106 : ZMod 32125373281) ^ (450 + 450 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 450 * (106 : ZMod 32125373281) ^ 450) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 28842045792 := by rw [factor_6_8]; decide
      have factor_6_10 : (106 : ZMod 32125373281) ^ 1802 = 9580890966 := by
        calc
          (106 : ZMod 32125373281) ^ 1802 = (106 : ZMod 32125373281) ^ (901 + 901) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 901 * (106 : ZMod 32125373281) ^ 901 := by rw [pow_add]
          _ = 9580890966 := by rw [factor_6_9]; decide
      have factor_6_11 : (106 : ZMod 32125373281) ^ 3604 = 24117882345 := by
        calc
          (106 : ZMod 32125373281) ^ 3604 = (106 : ZMod 32125373281) ^ (1802 + 1802) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1802 * (106 : ZMod 32125373281) ^ 1802 := by rw [pow_add]
          _ = 24117882345 := by rw [factor_6_10]; decide
      have factor_6_12 : (106 : ZMod 32125373281) ^ 7208 = 25991140589 := by
        calc
          (106 : ZMod 32125373281) ^ 7208 = (106 : ZMod 32125373281) ^ (3604 + 3604) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 3604 * (106 : ZMod 32125373281) ^ 3604 := by rw [pow_add]
          _ = 25991140589 := by rw [factor_6_11]; decide
      have factor_6_13 : (106 : ZMod 32125373281) ^ 14417 = 2022716773 := by
        calc
          (106 : ZMod 32125373281) ^ 14417 = (106 : ZMod 32125373281) ^ (7208 + 7208 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 7208 * (106 : ZMod 32125373281) ^ 7208) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 2022716773 := by rw [factor_6_12]; decide
      have factor_6_14 : (106 : ZMod 32125373281) ^ 28834 = 10170536779 := by
        calc
          (106 : ZMod 32125373281) ^ 28834 = (106 : ZMod 32125373281) ^ (14417 + 14417) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 14417 * (106 : ZMod 32125373281) ^ 14417 := by rw [pow_add]
          _ = 10170536779 := by rw [factor_6_13]; decide
      have factor_6_15 : (106 : ZMod 32125373281) ^ 57669 = 31744803660 := by
        calc
          (106 : ZMod 32125373281) ^ 57669 = (106 : ZMod 32125373281) ^ (28834 + 28834 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 28834 * (106 : ZMod 32125373281) ^ 28834) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 31744803660 := by rw [factor_6_14]; decide
      have factor_6_16 : (106 : ZMod 32125373281) ^ 115339 = 31576819295 := by
        calc
          (106 : ZMod 32125373281) ^ 115339 = (106 : ZMod 32125373281) ^ (57669 + 57669 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 57669 * (106 : ZMod 32125373281) ^ 57669) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 31576819295 := by rw [factor_6_15]; decide
      have factor_6_17 : (106 : ZMod 32125373281) ^ 230679 = 8279922650 := by
        calc
          (106 : ZMod 32125373281) ^ 230679 = (106 : ZMod 32125373281) ^ (115339 + 115339 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 115339 * (106 : ZMod 32125373281) ^ 115339) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 8279922650 := by rw [factor_6_16]; decide
      have factor_6_18 : (106 : ZMod 32125373281) ^ 461359 = 10443721995 := by
        calc
          (106 : ZMod 32125373281) ^ 461359 = (106 : ZMod 32125373281) ^ (230679 + 230679 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 230679 * (106 : ZMod 32125373281) ^ 230679) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 10443721995 := by rw [factor_6_17]; decide
      have factor_6_19 : (106 : ZMod 32125373281) ^ 922718 = 18398950686 := by
        calc
          (106 : ZMod 32125373281) ^ 922718 = (106 : ZMod 32125373281) ^ (461359 + 461359) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 461359 * (106 : ZMod 32125373281) ^ 461359 := by rw [pow_add]
          _ = 18398950686 := by rw [factor_6_18]; decide
      have factor_6_20 : (106 : ZMod 32125373281) ^ 1845437 = 23165231319 := by
        calc
          (106 : ZMod 32125373281) ^ 1845437 = (106 : ZMod 32125373281) ^ (922718 + 922718 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 922718 * (106 : ZMod 32125373281) ^ 922718) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 23165231319 := by rw [factor_6_19]; decide
      have factor_6_21 : (106 : ZMod 32125373281) ^ 3690874 = 25644842921 := by
        calc
          (106 : ZMod 32125373281) ^ 3690874 = (106 : ZMod 32125373281) ^ (1845437 + 1845437) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1845437 * (106 : ZMod 32125373281) ^ 1845437 := by rw [pow_add]
          _ = 25644842921 := by rw [factor_6_20]; decide
      have factor_6_22 : (106 : ZMod 32125373281) ^ 7381749 = 25723330717 := by
        calc
          (106 : ZMod 32125373281) ^ 7381749 = (106 : ZMod 32125373281) ^ (3690874 + 3690874 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 3690874 * (106 : ZMod 32125373281) ^ 3690874) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 25723330717 := by rw [factor_6_21]; decide
      have factor_6_23 : (106 : ZMod 32125373281) ^ 14763498 = 2547254529 := by
        calc
          (106 : ZMod 32125373281) ^ 14763498 = (106 : ZMod 32125373281) ^ (7381749 + 7381749) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 7381749 * (106 : ZMod 32125373281) ^ 7381749 := by rw [pow_add]
          _ = 2547254529 := by rw [factor_6_22]; decide
      have factor_6_24 : (106 : ZMod 32125373281) ^ 29526997 = 15326312988 := by
        calc
          (106 : ZMod 32125373281) ^ 29526997 = (106 : ZMod 32125373281) ^ (14763498 + 14763498 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 14763498 * (106 : ZMod 32125373281) ^ 14763498) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 15326312988 := by rw [factor_6_23]; decide
      have factor_6_25 : (106 : ZMod 32125373281) ^ 59053995 = 8284621468 := by
        calc
          (106 : ZMod 32125373281) ^ 59053995 = (106 : ZMod 32125373281) ^ (29526997 + 29526997 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 29526997 * (106 : ZMod 32125373281) ^ 29526997) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 8284621468 := by rw [factor_6_24]; decide
      have factor_6_26 : (106 : ZMod 32125373281) ^ 118107990 = 9480683902 := by
        calc
          (106 : ZMod 32125373281) ^ 118107990 = (106 : ZMod 32125373281) ^ (59053995 + 59053995) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 59053995 * (106 : ZMod 32125373281) ^ 59053995 := by rw [pow_add]
          _ = 9480683902 := by rw [factor_6_25]; decide
      have factor_6_27 : (106 : ZMod 32125373281) ^ 236215980 = 8476309246 := by
        calc
          (106 : ZMod 32125373281) ^ 236215980 = (106 : ZMod 32125373281) ^ (118107990 + 118107990) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 118107990 * (106 : ZMod 32125373281) ^ 118107990 := by rw [pow_add]
          _ = 8476309246 := by rw [factor_6_26]; decide
      have factor_6_28 : (106 : ZMod 32125373281) ^ 472431960 = 22220485417 := by
        calc
          (106 : ZMod 32125373281) ^ 472431960 = (106 : ZMod 32125373281) ^ (236215980 + 236215980) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 236215980 * (106 : ZMod 32125373281) ^ 236215980 := by rw [pow_add]
          _ = 22220485417 := by rw [factor_6_27]; decide
      have factor_6_29 : (106 : ZMod 32125373281) ^ 944863920 = 9972572258 := by
        calc
          (106 : ZMod 32125373281) ^ 944863920 = (106 : ZMod 32125373281) ^ (472431960 + 472431960) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 472431960 * (106 : ZMod 32125373281) ^ 472431960 := by rw [pow_add]
          _ = 9972572258 := by rw [factor_6_28]; decide
      have factor_6_30 : (106 : ZMod 32125373281) ^ 1889727840 = 21151254289 := by
        calc
          (106 : ZMod 32125373281) ^ 1889727840 = (106 : ZMod 32125373281) ^ (944863920 + 944863920) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 944863920 * (106 : ZMod 32125373281) ^ 944863920 := by rw [pow_add]
          _ = 21151254289 := by rw [factor_6_29]; decide
      change (106 : ZMod 32125373281) ^ 1889727840 ≠ 1
      rw [factor_6_30]
      decide
    ·
      have factor_7_0 : (106 : ZMod 32125373281) ^ 1 = 106 := by norm_num
      have factor_7_1 : (106 : ZMod 32125373281) ^ 3 = 1191016 := by
        calc
          (106 : ZMod 32125373281) ^ 3 = (106 : ZMod 32125373281) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 1 * (106 : ZMod 32125373281) ^ 1) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 1191016 := by rw [factor_7_0]; decide
      have factor_7_2 : (106 : ZMod 32125373281) ^ 6 = 5002687892 := by
        calc
          (106 : ZMod 32125373281) ^ 6 = (106 : ZMod 32125373281) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 3 * (106 : ZMod 32125373281) ^ 3 := by rw [pow_add]
          _ = 5002687892 := by rw [factor_7_1]; decide
      have factor_7_3 : (106 : ZMod 32125373281) ^ 12 = 12309578317 := by
        calc
          (106 : ZMod 32125373281) ^ 12 = (106 : ZMod 32125373281) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 6 * (106 : ZMod 32125373281) ^ 6 := by rw [pow_add]
          _ = 12309578317 := by rw [factor_7_2]; decide
      have factor_7_4 : (106 : ZMod 32125373281) ^ 25 = 22287269242 := by
        calc
          (106 : ZMod 32125373281) ^ 25 = (106 : ZMod 32125373281) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 12 * (106 : ZMod 32125373281) ^ 12) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 22287269242 := by rw [factor_7_3]; decide
      have factor_7_5 : (106 : ZMod 32125373281) ^ 50 = 1461527917 := by
        calc
          (106 : ZMod 32125373281) ^ 50 = (106 : ZMod 32125373281) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 25 * (106 : ZMod 32125373281) ^ 25 := by rw [pow_add]
          _ = 1461527917 := by rw [factor_7_4]; decide
      have factor_7_6 : (106 : ZMod 32125373281) ^ 100 = 12286600042 := by
        calc
          (106 : ZMod 32125373281) ^ 100 = (106 : ZMod 32125373281) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 50 * (106 : ZMod 32125373281) ^ 50 := by rw [pow_add]
          _ = 12286600042 := by rw [factor_7_5]; decide
      have factor_7_7 : (106 : ZMod 32125373281) ^ 201 = 3708124425 := by
        calc
          (106 : ZMod 32125373281) ^ 201 = (106 : ZMod 32125373281) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 100 * (106 : ZMod 32125373281) ^ 100) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 3708124425 := by rw [factor_7_6]; decide
      have factor_7_8 : (106 : ZMod 32125373281) ^ 403 = 28491971739 := by
        calc
          (106 : ZMod 32125373281) ^ 403 = (106 : ZMod 32125373281) ^ (201 + 201 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 201 * (106 : ZMod 32125373281) ^ 201) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 28491971739 := by rw [factor_7_7]; decide
      have factor_7_9 : (106 : ZMod 32125373281) ^ 806 = 22495900622 := by
        calc
          (106 : ZMod 32125373281) ^ 806 = (106 : ZMod 32125373281) ^ (403 + 403) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 403 * (106 : ZMod 32125373281) ^ 403 := by rw [pow_add]
          _ = 22495900622 := by rw [factor_7_8]; decide
      have factor_7_10 : (106 : ZMod 32125373281) ^ 1612 = 9630424859 := by
        calc
          (106 : ZMod 32125373281) ^ 1612 = (106 : ZMod 32125373281) ^ (806 + 806) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 806 * (106 : ZMod 32125373281) ^ 806 := by rw [pow_add]
          _ = 9630424859 := by rw [factor_7_9]; decide
      have factor_7_11 : (106 : ZMod 32125373281) ^ 3224 = 703633113 := by
        calc
          (106 : ZMod 32125373281) ^ 3224 = (106 : ZMod 32125373281) ^ (1612 + 1612) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1612 * (106 : ZMod 32125373281) ^ 1612 := by rw [pow_add]
          _ = 703633113 := by rw [factor_7_10]; decide
      have factor_7_12 : (106 : ZMod 32125373281) ^ 6449 = 21112973242 := by
        calc
          (106 : ZMod 32125373281) ^ 6449 = (106 : ZMod 32125373281) ^ (3224 + 3224 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 3224 * (106 : ZMod 32125373281) ^ 3224) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 21112973242 := by rw [factor_7_11]; decide
      have factor_7_13 : (106 : ZMod 32125373281) ^ 12899 = 12353727691 := by
        calc
          (106 : ZMod 32125373281) ^ 12899 = (106 : ZMod 32125373281) ^ (6449 + 6449 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 6449 * (106 : ZMod 32125373281) ^ 6449) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 12353727691 := by rw [factor_7_12]; decide
      have factor_7_14 : (106 : ZMod 32125373281) ^ 25799 = 10827557766 := by
        calc
          (106 : ZMod 32125373281) ^ 25799 = (106 : ZMod 32125373281) ^ (12899 + 12899 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 12899 * (106 : ZMod 32125373281) ^ 12899) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 10827557766 := by rw [factor_7_13]; decide
      have factor_7_15 : (106 : ZMod 32125373281) ^ 51599 = 14493281510 := by
        calc
          (106 : ZMod 32125373281) ^ 51599 = (106 : ZMod 32125373281) ^ (25799 + 25799 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 25799 * (106 : ZMod 32125373281) ^ 25799) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 14493281510 := by rw [factor_7_14]; decide
      have factor_7_16 : (106 : ZMod 32125373281) ^ 103198 = 3885542930 := by
        calc
          (106 : ZMod 32125373281) ^ 103198 = (106 : ZMod 32125373281) ^ (51599 + 51599) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 51599 * (106 : ZMod 32125373281) ^ 51599 := by rw [pow_add]
          _ = 3885542930 := by rw [factor_7_15]; decide
      have factor_7_17 : (106 : ZMod 32125373281) ^ 206397 = 11057296785 := by
        calc
          (106 : ZMod 32125373281) ^ 206397 = (106 : ZMod 32125373281) ^ (103198 + 103198 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 103198 * (106 : ZMod 32125373281) ^ 103198) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 11057296785 := by rw [factor_7_16]; decide
      have factor_7_18 : (106 : ZMod 32125373281) ^ 412795 = 30582197303 := by
        calc
          (106 : ZMod 32125373281) ^ 412795 = (106 : ZMod 32125373281) ^ (206397 + 206397 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 206397 * (106 : ZMod 32125373281) ^ 206397) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 30582197303 := by rw [factor_7_17]; decide
      have factor_7_19 : (106 : ZMod 32125373281) ^ 825590 = 19099292409 := by
        calc
          (106 : ZMod 32125373281) ^ 825590 = (106 : ZMod 32125373281) ^ (412795 + 412795) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 412795 * (106 : ZMod 32125373281) ^ 412795 := by rw [pow_add]
          _ = 19099292409 := by rw [factor_7_18]; decide
      have factor_7_20 : (106 : ZMod 32125373281) ^ 1651180 = 4452362339 := by
        calc
          (106 : ZMod 32125373281) ^ 1651180 = (106 : ZMod 32125373281) ^ (825590 + 825590) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 825590 * (106 : ZMod 32125373281) ^ 825590 := by rw [pow_add]
          _ = 4452362339 := by rw [factor_7_19]; decide
      have factor_7_21 : (106 : ZMod 32125373281) ^ 3302361 = 12461519181 := by
        calc
          (106 : ZMod 32125373281) ^ 3302361 = (106 : ZMod 32125373281) ^ (1651180 + 1651180 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 1651180 * (106 : ZMod 32125373281) ^ 1651180) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 12461519181 := by rw [factor_7_20]; decide
      have factor_7_22 : (106 : ZMod 32125373281) ^ 6604723 = 12734101771 := by
        calc
          (106 : ZMod 32125373281) ^ 6604723 = (106 : ZMod 32125373281) ^ (3302361 + 3302361 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 3302361 * (106 : ZMod 32125373281) ^ 3302361) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 12734101771 := by rw [factor_7_21]; decide
      have factor_7_23 : (106 : ZMod 32125373281) ^ 13209446 = 5994783227 := by
        calc
          (106 : ZMod 32125373281) ^ 13209446 = (106 : ZMod 32125373281) ^ (6604723 + 6604723) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 6604723 * (106 : ZMod 32125373281) ^ 6604723 := by rw [pow_add]
          _ = 5994783227 := by rw [factor_7_22]; decide
      have factor_7_24 : (106 : ZMod 32125373281) ^ 26418892 = 30298311151 := by
        calc
          (106 : ZMod 32125373281) ^ 26418892 = (106 : ZMod 32125373281) ^ (13209446 + 13209446) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 13209446 * (106 : ZMod 32125373281) ^ 13209446 := by rw [pow_add]
          _ = 30298311151 := by rw [factor_7_23]; decide
      have factor_7_25 : (106 : ZMod 32125373281) ^ 52837785 = 28945650590 := by
        calc
          (106 : ZMod 32125373281) ^ 52837785 = (106 : ZMod 32125373281) ^ (26418892 + 26418892 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 26418892 * (106 : ZMod 32125373281) ^ 26418892) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 28945650590 := by rw [factor_7_24]; decide
      have factor_7_26 : (106 : ZMod 32125373281) ^ 105675570 = 2549894437 := by
        calc
          (106 : ZMod 32125373281) ^ 105675570 = (106 : ZMod 32125373281) ^ (52837785 + 52837785) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 52837785 * (106 : ZMod 32125373281) ^ 52837785 := by rw [pow_add]
          _ = 2549894437 := by rw [factor_7_25]; decide
      have factor_7_27 : (106 : ZMod 32125373281) ^ 211351140 = 10629825148 := by
        calc
          (106 : ZMod 32125373281) ^ 211351140 = (106 : ZMod 32125373281) ^ (105675570 + 105675570) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 105675570 * (106 : ZMod 32125373281) ^ 105675570 := by rw [pow_add]
          _ = 10629825148 := by rw [factor_7_26]; decide
      have factor_7_28 : (106 : ZMod 32125373281) ^ 422702280 = 31350519659 := by
        calc
          (106 : ZMod 32125373281) ^ 422702280 = (106 : ZMod 32125373281) ^ (211351140 + 211351140) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 211351140 * (106 : ZMod 32125373281) ^ 211351140 := by rw [pow_add]
          _ = 31350519659 := by rw [factor_7_27]; decide
      have factor_7_29 : (106 : ZMod 32125373281) ^ 845404560 = 30946534626 := by
        calc
          (106 : ZMod 32125373281) ^ 845404560 = (106 : ZMod 32125373281) ^ (422702280 + 422702280) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 422702280 * (106 : ZMod 32125373281) ^ 422702280 := by rw [pow_add]
          _ = 30946534626 := by rw [factor_7_28]; decide
      have factor_7_30 : (106 : ZMod 32125373281) ^ 1690809120 = 2601453691 := by
        calc
          (106 : ZMod 32125373281) ^ 1690809120 = (106 : ZMod 32125373281) ^ (845404560 + 845404560) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 845404560 * (106 : ZMod 32125373281) ^ 845404560 := by rw [pow_add]
          _ = 2601453691 := by rw [factor_7_29]; decide
      change (106 : ZMod 32125373281) ^ 1690809120 ≠ 1
      rw [factor_7_30]
      decide
    ·
      have factor_8_0 : (106 : ZMod 32125373281) ^ 1 = 106 := by norm_num
      have factor_8_1 : (106 : ZMod 32125373281) ^ 2 = 11236 := by
        calc
          (106 : ZMod 32125373281) ^ 2 = (106 : ZMod 32125373281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1 * (106 : ZMod 32125373281) ^ 1 := by rw [pow_add]
          _ = 11236 := by rw [factor_8_0]; decide
      have factor_8_2 : (106 : ZMod 32125373281) ^ 5 = 13382255776 := by
        calc
          (106 : ZMod 32125373281) ^ 5 = (106 : ZMod 32125373281) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 2 * (106 : ZMod 32125373281) ^ 2) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 13382255776 := by rw [factor_8_1]; decide
      have factor_8_3 : (106 : ZMod 32125373281) ^ 10 = 16924385371 := by
        calc
          (106 : ZMod 32125373281) ^ 10 = (106 : ZMod 32125373281) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 5 * (106 : ZMod 32125373281) ^ 5 := by rw [pow_add]
          _ = 16924385371 := by rw [factor_8_2]; decide
      have factor_8_4 : (106 : ZMod 32125373281) ^ 20 = 18843299770 := by
        calc
          (106 : ZMod 32125373281) ^ 20 = (106 : ZMod 32125373281) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 10 * (106 : ZMod 32125373281) ^ 10 := by rw [pow_add]
          _ = 18843299770 := by rw [factor_8_3]; decide
      have factor_8_5 : (106 : ZMod 32125373281) ^ 41 = 18074901229 := by
        calc
          (106 : ZMod 32125373281) ^ 41 = (106 : ZMod 32125373281) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 20 * (106 : ZMod 32125373281) ^ 20) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 18074901229 := by rw [factor_8_4]; decide
      have factor_8_6 : (106 : ZMod 32125373281) ^ 83 = 12827975031 := by
        calc
          (106 : ZMod 32125373281) ^ 83 = (106 : ZMod 32125373281) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 41 * (106 : ZMod 32125373281) ^ 41) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 12827975031 := by rw [factor_8_5]; decide
      have factor_8_7 : (106 : ZMod 32125373281) ^ 166 = 14777480956 := by
        calc
          (106 : ZMod 32125373281) ^ 166 = (106 : ZMod 32125373281) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 83 * (106 : ZMod 32125373281) ^ 83 := by rw [pow_add]
          _ = 14777480956 := by rw [factor_8_6]; decide
      have factor_8_8 : (106 : ZMod 32125373281) ^ 333 = 21308988411 := by
        calc
          (106 : ZMod 32125373281) ^ 333 = (106 : ZMod 32125373281) ^ (166 + 166 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 166 * (106 : ZMod 32125373281) ^ 166) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 21308988411 := by rw [factor_8_7]; decide
      have factor_8_9 : (106 : ZMod 32125373281) ^ 666 = 4001219066 := by
        calc
          (106 : ZMod 32125373281) ^ 666 = (106 : ZMod 32125373281) ^ (333 + 333) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 333 * (106 : ZMod 32125373281) ^ 333 := by rw [pow_add]
          _ = 4001219066 := by rw [factor_8_8]; decide
      have factor_8_10 : (106 : ZMod 32125373281) ^ 1332 = 29923283246 := by
        calc
          (106 : ZMod 32125373281) ^ 1332 = (106 : ZMod 32125373281) ^ (666 + 666) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 666 * (106 : ZMod 32125373281) ^ 666 := by rw [pow_add]
          _ = 29923283246 := by rw [factor_8_9]; decide
      have factor_8_11 : (106 : ZMod 32125373281) ^ 2664 = 7676934943 := by
        calc
          (106 : ZMod 32125373281) ^ 2664 = (106 : ZMod 32125373281) ^ (1332 + 1332) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 1332 * (106 : ZMod 32125373281) ^ 1332 := by rw [pow_add]
          _ = 7676934943 := by rw [factor_8_10]; decide
      have factor_8_12 : (106 : ZMod 32125373281) ^ 5328 = 17573231121 := by
        calc
          (106 : ZMod 32125373281) ^ 5328 = (106 : ZMod 32125373281) ^ (2664 + 2664) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 2664 * (106 : ZMod 32125373281) ^ 2664 := by rw [pow_add]
          _ = 17573231121 := by rw [factor_8_11]; decide
      have factor_8_13 : (106 : ZMod 32125373281) ^ 10656 = 18290284996 := by
        calc
          (106 : ZMod 32125373281) ^ 10656 = (106 : ZMod 32125373281) ^ (5328 + 5328) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 5328 * (106 : ZMod 32125373281) ^ 5328 := by rw [pow_add]
          _ = 18290284996 := by rw [factor_8_12]; decide
      have factor_8_14 : (106 : ZMod 32125373281) ^ 21312 = 10017172379 := by
        calc
          (106 : ZMod 32125373281) ^ 21312 = (106 : ZMod 32125373281) ^ (10656 + 10656) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 10656 * (106 : ZMod 32125373281) ^ 10656 := by rw [pow_add]
          _ = 10017172379 := by rw [factor_8_13]; decide
      have factor_8_15 : (106 : ZMod 32125373281) ^ 42625 = 31598888816 := by
        calc
          (106 : ZMod 32125373281) ^ 42625 = (106 : ZMod 32125373281) ^ (21312 + 21312 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 21312 * (106 : ZMod 32125373281) ^ 21312) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 31598888816 := by rw [factor_8_14]; decide
      have factor_8_16 : (106 : ZMod 32125373281) ^ 85251 = 16905002809 := by
        calc
          (106 : ZMod 32125373281) ^ 85251 = (106 : ZMod 32125373281) ^ (42625 + 42625 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 42625 * (106 : ZMod 32125373281) ^ 42625) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 16905002809 := by rw [factor_8_15]; decide
      have factor_8_17 : (106 : ZMod 32125373281) ^ 170502 = 4935451194 := by
        calc
          (106 : ZMod 32125373281) ^ 170502 = (106 : ZMod 32125373281) ^ (85251 + 85251) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 85251 * (106 : ZMod 32125373281) ^ 85251 := by rw [pow_add]
          _ = 4935451194 := by rw [factor_8_16]; decide
      have factor_8_18 : (106 : ZMod 32125373281) ^ 341004 = 23770880446 := by
        calc
          (106 : ZMod 32125373281) ^ 341004 = (106 : ZMod 32125373281) ^ (170502 + 170502) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 170502 * (106 : ZMod 32125373281) ^ 170502 := by rw [pow_add]
          _ = 23770880446 := by rw [factor_8_17]; decide
      have factor_8_19 : (106 : ZMod 32125373281) ^ 682009 = 15883071229 := by
        calc
          (106 : ZMod 32125373281) ^ 682009 = (106 : ZMod 32125373281) ^ (341004 + 341004 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 341004 * (106 : ZMod 32125373281) ^ 341004) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 15883071229 := by rw [factor_8_18]; decide
      have factor_8_20 : (106 : ZMod 32125373281) ^ 1364018 = 6777139729 := by
        calc
          (106 : ZMod 32125373281) ^ 1364018 = (106 : ZMod 32125373281) ^ (682009 + 682009) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 682009 * (106 : ZMod 32125373281) ^ 682009 := by rw [pow_add]
          _ = 6777139729 := by rw [factor_8_19]; decide
      have factor_8_21 : (106 : ZMod 32125373281) ^ 2728037 = 17506672579 := by
        calc
          (106 : ZMod 32125373281) ^ 2728037 = (106 : ZMod 32125373281) ^ (1364018 + 1364018 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 1364018 * (106 : ZMod 32125373281) ^ 1364018) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 17506672579 := by rw [factor_8_20]; decide
      have factor_8_22 : (106 : ZMod 32125373281) ^ 5456075 = 665910753 := by
        calc
          (106 : ZMod 32125373281) ^ 5456075 = (106 : ZMod 32125373281) ^ (2728037 + 2728037 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 2728037 * (106 : ZMod 32125373281) ^ 2728037) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 665910753 := by rw [factor_8_21]; decide
      have factor_8_23 : (106 : ZMod 32125373281) ^ 10912151 = 7283722607 := by
        calc
          (106 : ZMod 32125373281) ^ 10912151 = (106 : ZMod 32125373281) ^ (5456075 + 5456075 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 5456075 * (106 : ZMod 32125373281) ^ 5456075) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 7283722607 := by rw [factor_8_22]; decide
      have factor_8_24 : (106 : ZMod 32125373281) ^ 21824302 = 490869969 := by
        calc
          (106 : ZMod 32125373281) ^ 21824302 = (106 : ZMod 32125373281) ^ (10912151 + 10912151) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 10912151 * (106 : ZMod 32125373281) ^ 10912151 := by rw [pow_add]
          _ = 490869969 := by rw [factor_8_23]; decide
      have factor_8_25 : (106 : ZMod 32125373281) ^ 43648605 = 2087724643 := by
        calc
          (106 : ZMod 32125373281) ^ 43648605 = (106 : ZMod 32125373281) ^ (21824302 + 21824302 + 1) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = ((106 : ZMod 32125373281) ^ 21824302 * (106 : ZMod 32125373281) ^ 21824302) * (106 : ZMod 32125373281) := by rw [pow_succ, pow_add]
          _ = 2087724643 := by rw [factor_8_24]; decide
      have factor_8_26 : (106 : ZMod 32125373281) ^ 87297210 = 2898829982 := by
        calc
          (106 : ZMod 32125373281) ^ 87297210 = (106 : ZMod 32125373281) ^ (43648605 + 43648605) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 43648605 * (106 : ZMod 32125373281) ^ 43648605 := by rw [pow_add]
          _ = 2898829982 := by rw [factor_8_25]; decide
      have factor_8_27 : (106 : ZMod 32125373281) ^ 174594420 = 27698779079 := by
        calc
          (106 : ZMod 32125373281) ^ 174594420 = (106 : ZMod 32125373281) ^ (87297210 + 87297210) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 87297210 * (106 : ZMod 32125373281) ^ 87297210 := by rw [pow_add]
          _ = 27698779079 := by rw [factor_8_26]; decide
      have factor_8_28 : (106 : ZMod 32125373281) ^ 349188840 = 12130206533 := by
        calc
          (106 : ZMod 32125373281) ^ 349188840 = (106 : ZMod 32125373281) ^ (174594420 + 174594420) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 174594420 * (106 : ZMod 32125373281) ^ 174594420 := by rw [pow_add]
          _ = 12130206533 := by rw [factor_8_27]; decide
      have factor_8_29 : (106 : ZMod 32125373281) ^ 698377680 = 4525198455 := by
        calc
          (106 : ZMod 32125373281) ^ 698377680 = (106 : ZMod 32125373281) ^ (349188840 + 349188840) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 349188840 * (106 : ZMod 32125373281) ^ 349188840 := by rw [pow_add]
          _ = 4525198455 := by rw [factor_8_28]; decide
      have factor_8_30 : (106 : ZMod 32125373281) ^ 1396755360 = 20347127223 := by
        calc
          (106 : ZMod 32125373281) ^ 1396755360 = (106 : ZMod 32125373281) ^ (698377680 + 698377680) :=
            congrArg (fun n : ℕ => (106 : ZMod 32125373281) ^ n) (by norm_num)
          _ = (106 : ZMod 32125373281) ^ 698377680 * (106 : ZMod 32125373281) ^ 698377680 := by rw [pow_add]
          _ = 20347127223 := by rw [factor_8_29]; decide
      change (106 : ZMod 32125373281) ^ 1396755360 ≠ 1
      rw [factor_8_30]
      decide

#print axioms prime_lucas_32125373281

end TotientTailPeriodKiller
end Erdos249257
