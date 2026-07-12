import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=27 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_4015671661 : Nat.Prime 4015671661 := by
  apply lucas_primality 4015671661 (6 : ZMod 4015671661)
  ·
      have fermat_0 : (6 : ZMod 4015671661) ^ 1 = 6 := by norm_num
      have fermat_1 : (6 : ZMod 4015671661) ^ 3 = 216 := by
        calc
          (6 : ZMod 4015671661) ^ 3 = (6 : ZMod 4015671661) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 1 * (6 : ZMod 4015671661) ^ 1) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [fermat_0]; decide
      have fermat_2 : (6 : ZMod 4015671661) ^ 7 = 279936 := by
        calc
          (6 : ZMod 4015671661) ^ 7 = (6 : ZMod 4015671661) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 3 * (6 : ZMod 4015671661) ^ 3) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 279936 := by rw [fermat_1]; decide
      have fermat_3 : (6 : ZMod 4015671661) ^ 14 = 2066402537 := by
        calc
          (6 : ZMod 4015671661) ^ 14 = (6 : ZMod 4015671661) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 7 * (6 : ZMod 4015671661) ^ 7 := by rw [pow_add]
          _ = 2066402537 := by rw [fermat_2]; decide
      have fermat_4 : (6 : ZMod 4015671661) ^ 29 = 3265708735 := by
        calc
          (6 : ZMod 4015671661) ^ 29 = (6 : ZMod 4015671661) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 14 * (6 : ZMod 4015671661) ^ 14) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3265708735 := by rw [fermat_3]; decide
      have fermat_5 : (6 : ZMod 4015671661) ^ 59 = 692986925 := by
        calc
          (6 : ZMod 4015671661) ^ 59 = (6 : ZMod 4015671661) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 29 * (6 : ZMod 4015671661) ^ 29) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 692986925 := by rw [fermat_4]; decide
      have fermat_6 : (6 : ZMod 4015671661) ^ 119 = 2874724175 := by
        calc
          (6 : ZMod 4015671661) ^ 119 = (6 : ZMod 4015671661) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 59 * (6 : ZMod 4015671661) ^ 59) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2874724175 := by rw [fermat_5]; decide
      have fermat_7 : (6 : ZMod 4015671661) ^ 239 = 93508656 := by
        calc
          (6 : ZMod 4015671661) ^ 239 = (6 : ZMod 4015671661) ^ (119 + 119 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 119 * (6 : ZMod 4015671661) ^ 119) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 93508656 := by rw [fermat_6]; decide
      have fermat_8 : (6 : ZMod 4015671661) ^ 478 = 708085140 := by
        calc
          (6 : ZMod 4015671661) ^ 478 = (6 : ZMod 4015671661) ^ (239 + 239) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 239 * (6 : ZMod 4015671661) ^ 239 := by rw [pow_add]
          _ = 708085140 := by rw [fermat_7]; decide
      have fermat_9 : (6 : ZMod 4015671661) ^ 957 = 1009850986 := by
        calc
          (6 : ZMod 4015671661) ^ 957 = (6 : ZMod 4015671661) ^ (478 + 478 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 478 * (6 : ZMod 4015671661) ^ 478) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1009850986 := by rw [fermat_8]; decide
      have fermat_10 : (6 : ZMod 4015671661) ^ 1914 = 703682616 := by
        calc
          (6 : ZMod 4015671661) ^ 1914 = (6 : ZMod 4015671661) ^ (957 + 957) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 957 * (6 : ZMod 4015671661) ^ 957 := by rw [pow_add]
          _ = 703682616 := by rw [fermat_9]; decide
      have fermat_11 : (6 : ZMod 4015671661) ^ 3829 = 1326403230 := by
        calc
          (6 : ZMod 4015671661) ^ 3829 = (6 : ZMod 4015671661) ^ (1914 + 1914 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 1914 * (6 : ZMod 4015671661) ^ 1914) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1326403230 := by rw [fermat_10]; decide
      have fermat_12 : (6 : ZMod 4015671661) ^ 7659 = 3269707827 := by
        calc
          (6 : ZMod 4015671661) ^ 7659 = (6 : ZMod 4015671661) ^ (3829 + 3829 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 3829 * (6 : ZMod 4015671661) ^ 3829) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3269707827 := by rw [fermat_11]; decide
      have fermat_13 : (6 : ZMod 4015671661) ^ 15318 = 2918920922 := by
        calc
          (6 : ZMod 4015671661) ^ 15318 = (6 : ZMod 4015671661) ^ (7659 + 7659) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 7659 * (6 : ZMod 4015671661) ^ 7659 := by rw [pow_add]
          _ = 2918920922 := by rw [fermat_12]; decide
      have fermat_14 : (6 : ZMod 4015671661) ^ 30637 = 119395231 := by
        calc
          (6 : ZMod 4015671661) ^ 30637 = (6 : ZMod 4015671661) ^ (15318 + 15318 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 15318 * (6 : ZMod 4015671661) ^ 15318) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 119395231 := by rw [fermat_13]; decide
      have fermat_15 : (6 : ZMod 4015671661) ^ 61274 = 403174444 := by
        calc
          (6 : ZMod 4015671661) ^ 61274 = (6 : ZMod 4015671661) ^ (30637 + 30637) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 30637 * (6 : ZMod 4015671661) ^ 30637 := by rw [pow_add]
          _ = 403174444 := by rw [fermat_14]; decide
      have fermat_16 : (6 : ZMod 4015671661) ^ 122548 = 2028347421 := by
        calc
          (6 : ZMod 4015671661) ^ 122548 = (6 : ZMod 4015671661) ^ (61274 + 61274) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 61274 * (6 : ZMod 4015671661) ^ 61274 := by rw [pow_add]
          _ = 2028347421 := by rw [fermat_15]; decide
      have fermat_17 : (6 : ZMod 4015671661) ^ 245097 = 2478977847 := by
        calc
          (6 : ZMod 4015671661) ^ 245097 = (6 : ZMod 4015671661) ^ (122548 + 122548 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 122548 * (6 : ZMod 4015671661) ^ 122548) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2478977847 := by rw [fermat_16]; decide
      have fermat_18 : (6 : ZMod 4015671661) ^ 490194 = 2296698749 := by
        calc
          (6 : ZMod 4015671661) ^ 490194 = (6 : ZMod 4015671661) ^ (245097 + 245097) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 245097 * (6 : ZMod 4015671661) ^ 245097 := by rw [pow_add]
          _ = 2296698749 := by rw [fermat_17]; decide
      have fermat_19 : (6 : ZMod 4015671661) ^ 980388 = 2687992592 := by
        calc
          (6 : ZMod 4015671661) ^ 980388 = (6 : ZMod 4015671661) ^ (490194 + 490194) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 490194 * (6 : ZMod 4015671661) ^ 490194 := by rw [pow_add]
          _ = 2687992592 := by rw [fermat_18]; decide
      have fermat_20 : (6 : ZMod 4015671661) ^ 1960777 = 3522104543 := by
        calc
          (6 : ZMod 4015671661) ^ 1960777 = (6 : ZMod 4015671661) ^ (980388 + 980388 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 980388 * (6 : ZMod 4015671661) ^ 980388) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3522104543 := by rw [fermat_19]; decide
      have fermat_21 : (6 : ZMod 4015671661) ^ 3921554 = 3338361118 := by
        calc
          (6 : ZMod 4015671661) ^ 3921554 = (6 : ZMod 4015671661) ^ (1960777 + 1960777) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 1960777 * (6 : ZMod 4015671661) ^ 1960777 := by rw [pow_add]
          _ = 3338361118 := by rw [fermat_20]; decide
      have fermat_22 : (6 : ZMod 4015671661) ^ 7843108 = 68258778 := by
        calc
          (6 : ZMod 4015671661) ^ 7843108 = (6 : ZMod 4015671661) ^ (3921554 + 3921554) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 3921554 * (6 : ZMod 4015671661) ^ 3921554 := by rw [pow_add]
          _ = 68258778 := by rw [fermat_21]; decide
      have fermat_23 : (6 : ZMod 4015671661) ^ 15686217 = 558355528 := by
        calc
          (6 : ZMod 4015671661) ^ 15686217 = (6 : ZMod 4015671661) ^ (7843108 + 7843108 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 7843108 * (6 : ZMod 4015671661) ^ 7843108) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 558355528 := by rw [fermat_22]; decide
      have fermat_24 : (6 : ZMod 4015671661) ^ 31372434 = 1759836412 := by
        calc
          (6 : ZMod 4015671661) ^ 31372434 = (6 : ZMod 4015671661) ^ (15686217 + 15686217) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 15686217 * (6 : ZMod 4015671661) ^ 15686217 := by rw [pow_add]
          _ = 1759836412 := by rw [fermat_23]; decide
      have fermat_25 : (6 : ZMod 4015671661) ^ 62744869 = 3903632676 := by
        calc
          (6 : ZMod 4015671661) ^ 62744869 = (6 : ZMod 4015671661) ^ (31372434 + 31372434 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 31372434 * (6 : ZMod 4015671661) ^ 31372434) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3903632676 := by rw [fermat_24]; decide
      have fermat_26 : (6 : ZMod 4015671661) ^ 125489739 = 1271839852 := by
        calc
          (6 : ZMod 4015671661) ^ 125489739 = (6 : ZMod 4015671661) ^ (62744869 + 62744869 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 62744869 * (6 : ZMod 4015671661) ^ 62744869) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1271839852 := by rw [fermat_25]; decide
      have fermat_27 : (6 : ZMod 4015671661) ^ 250979478 = 2074573971 := by
        calc
          (6 : ZMod 4015671661) ^ 250979478 = (6 : ZMod 4015671661) ^ (125489739 + 125489739) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 125489739 * (6 : ZMod 4015671661) ^ 125489739 := by rw [pow_add]
          _ = 2074573971 := by rw [fermat_26]; decide
      have fermat_28 : (6 : ZMod 4015671661) ^ 501958957 = 1118120016 := by
        calc
          (6 : ZMod 4015671661) ^ 501958957 = (6 : ZMod 4015671661) ^ (250979478 + 250979478 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 250979478 * (6 : ZMod 4015671661) ^ 250979478) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1118120016 := by rw [fermat_27]; decide
      have fermat_29 : (6 : ZMod 4015671661) ^ 1003917915 = 371169909 := by
        calc
          (6 : ZMod 4015671661) ^ 1003917915 = (6 : ZMod 4015671661) ^ (501958957 + 501958957 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 501958957 * (6 : ZMod 4015671661) ^ 501958957) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 371169909 := by rw [fermat_28]; decide
      have fermat_30 : (6 : ZMod 4015671661) ^ 2007835830 = 4015671660 := by
        calc
          (6 : ZMod 4015671661) ^ 2007835830 = (6 : ZMod 4015671661) ^ (1003917915 + 1003917915) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 1003917915 * (6 : ZMod 4015671661) ^ 1003917915 := by rw [pow_add]
          _ = 4015671660 := by rw [fermat_29]; decide
      have fermat_31 : (6 : ZMod 4015671661) ^ 4015671660 = 1 := by
        calc
          (6 : ZMod 4015671661) ^ 4015671660 = (6 : ZMod 4015671661) ^ (2007835830 + 2007835830) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 2007835830 * (6 : ZMod 4015671661) ^ 2007835830 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 4015671661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (6 : ZMod 4015671661) ^ 1 = 6 := by norm_num
      have factor_0_1 : (6 : ZMod 4015671661) ^ 3 = 216 := by
        calc
          (6 : ZMod 4015671661) ^ 3 = (6 : ZMod 4015671661) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 1 * (6 : ZMod 4015671661) ^ 1) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_0_0]; decide
      have factor_0_2 : (6 : ZMod 4015671661) ^ 7 = 279936 := by
        calc
          (6 : ZMod 4015671661) ^ 7 = (6 : ZMod 4015671661) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 3 * (6 : ZMod 4015671661) ^ 3) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 279936 := by rw [factor_0_1]; decide
      have factor_0_3 : (6 : ZMod 4015671661) ^ 14 = 2066402537 := by
        calc
          (6 : ZMod 4015671661) ^ 14 = (6 : ZMod 4015671661) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 7 * (6 : ZMod 4015671661) ^ 7 := by rw [pow_add]
          _ = 2066402537 := by rw [factor_0_2]; decide
      have factor_0_4 : (6 : ZMod 4015671661) ^ 29 = 3265708735 := by
        calc
          (6 : ZMod 4015671661) ^ 29 = (6 : ZMod 4015671661) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 14 * (6 : ZMod 4015671661) ^ 14) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3265708735 := by rw [factor_0_3]; decide
      have factor_0_5 : (6 : ZMod 4015671661) ^ 59 = 692986925 := by
        calc
          (6 : ZMod 4015671661) ^ 59 = (6 : ZMod 4015671661) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 29 * (6 : ZMod 4015671661) ^ 29) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 692986925 := by rw [factor_0_4]; decide
      have factor_0_6 : (6 : ZMod 4015671661) ^ 119 = 2874724175 := by
        calc
          (6 : ZMod 4015671661) ^ 119 = (6 : ZMod 4015671661) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 59 * (6 : ZMod 4015671661) ^ 59) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2874724175 := by rw [factor_0_5]; decide
      have factor_0_7 : (6 : ZMod 4015671661) ^ 239 = 93508656 := by
        calc
          (6 : ZMod 4015671661) ^ 239 = (6 : ZMod 4015671661) ^ (119 + 119 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 119 * (6 : ZMod 4015671661) ^ 119) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 93508656 := by rw [factor_0_6]; decide
      have factor_0_8 : (6 : ZMod 4015671661) ^ 478 = 708085140 := by
        calc
          (6 : ZMod 4015671661) ^ 478 = (6 : ZMod 4015671661) ^ (239 + 239) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 239 * (6 : ZMod 4015671661) ^ 239 := by rw [pow_add]
          _ = 708085140 := by rw [factor_0_7]; decide
      have factor_0_9 : (6 : ZMod 4015671661) ^ 957 = 1009850986 := by
        calc
          (6 : ZMod 4015671661) ^ 957 = (6 : ZMod 4015671661) ^ (478 + 478 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 478 * (6 : ZMod 4015671661) ^ 478) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1009850986 := by rw [factor_0_8]; decide
      have factor_0_10 : (6 : ZMod 4015671661) ^ 1914 = 703682616 := by
        calc
          (6 : ZMod 4015671661) ^ 1914 = (6 : ZMod 4015671661) ^ (957 + 957) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 957 * (6 : ZMod 4015671661) ^ 957 := by rw [pow_add]
          _ = 703682616 := by rw [factor_0_9]; decide
      have factor_0_11 : (6 : ZMod 4015671661) ^ 3829 = 1326403230 := by
        calc
          (6 : ZMod 4015671661) ^ 3829 = (6 : ZMod 4015671661) ^ (1914 + 1914 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 1914 * (6 : ZMod 4015671661) ^ 1914) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1326403230 := by rw [factor_0_10]; decide
      have factor_0_12 : (6 : ZMod 4015671661) ^ 7659 = 3269707827 := by
        calc
          (6 : ZMod 4015671661) ^ 7659 = (6 : ZMod 4015671661) ^ (3829 + 3829 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 3829 * (6 : ZMod 4015671661) ^ 3829) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3269707827 := by rw [factor_0_11]; decide
      have factor_0_13 : (6 : ZMod 4015671661) ^ 15318 = 2918920922 := by
        calc
          (6 : ZMod 4015671661) ^ 15318 = (6 : ZMod 4015671661) ^ (7659 + 7659) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 7659 * (6 : ZMod 4015671661) ^ 7659 := by rw [pow_add]
          _ = 2918920922 := by rw [factor_0_12]; decide
      have factor_0_14 : (6 : ZMod 4015671661) ^ 30637 = 119395231 := by
        calc
          (6 : ZMod 4015671661) ^ 30637 = (6 : ZMod 4015671661) ^ (15318 + 15318 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 15318 * (6 : ZMod 4015671661) ^ 15318) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 119395231 := by rw [factor_0_13]; decide
      have factor_0_15 : (6 : ZMod 4015671661) ^ 61274 = 403174444 := by
        calc
          (6 : ZMod 4015671661) ^ 61274 = (6 : ZMod 4015671661) ^ (30637 + 30637) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 30637 * (6 : ZMod 4015671661) ^ 30637 := by rw [pow_add]
          _ = 403174444 := by rw [factor_0_14]; decide
      have factor_0_16 : (6 : ZMod 4015671661) ^ 122548 = 2028347421 := by
        calc
          (6 : ZMod 4015671661) ^ 122548 = (6 : ZMod 4015671661) ^ (61274 + 61274) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 61274 * (6 : ZMod 4015671661) ^ 61274 := by rw [pow_add]
          _ = 2028347421 := by rw [factor_0_15]; decide
      have factor_0_17 : (6 : ZMod 4015671661) ^ 245097 = 2478977847 := by
        calc
          (6 : ZMod 4015671661) ^ 245097 = (6 : ZMod 4015671661) ^ (122548 + 122548 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 122548 * (6 : ZMod 4015671661) ^ 122548) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2478977847 := by rw [factor_0_16]; decide
      have factor_0_18 : (6 : ZMod 4015671661) ^ 490194 = 2296698749 := by
        calc
          (6 : ZMod 4015671661) ^ 490194 = (6 : ZMod 4015671661) ^ (245097 + 245097) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 245097 * (6 : ZMod 4015671661) ^ 245097 := by rw [pow_add]
          _ = 2296698749 := by rw [factor_0_17]; decide
      have factor_0_19 : (6 : ZMod 4015671661) ^ 980388 = 2687992592 := by
        calc
          (6 : ZMod 4015671661) ^ 980388 = (6 : ZMod 4015671661) ^ (490194 + 490194) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 490194 * (6 : ZMod 4015671661) ^ 490194 := by rw [pow_add]
          _ = 2687992592 := by rw [factor_0_18]; decide
      have factor_0_20 : (6 : ZMod 4015671661) ^ 1960777 = 3522104543 := by
        calc
          (6 : ZMod 4015671661) ^ 1960777 = (6 : ZMod 4015671661) ^ (980388 + 980388 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 980388 * (6 : ZMod 4015671661) ^ 980388) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3522104543 := by rw [factor_0_19]; decide
      have factor_0_21 : (6 : ZMod 4015671661) ^ 3921554 = 3338361118 := by
        calc
          (6 : ZMod 4015671661) ^ 3921554 = (6 : ZMod 4015671661) ^ (1960777 + 1960777) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 1960777 * (6 : ZMod 4015671661) ^ 1960777 := by rw [pow_add]
          _ = 3338361118 := by rw [factor_0_20]; decide
      have factor_0_22 : (6 : ZMod 4015671661) ^ 7843108 = 68258778 := by
        calc
          (6 : ZMod 4015671661) ^ 7843108 = (6 : ZMod 4015671661) ^ (3921554 + 3921554) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 3921554 * (6 : ZMod 4015671661) ^ 3921554 := by rw [pow_add]
          _ = 68258778 := by rw [factor_0_21]; decide
      have factor_0_23 : (6 : ZMod 4015671661) ^ 15686217 = 558355528 := by
        calc
          (6 : ZMod 4015671661) ^ 15686217 = (6 : ZMod 4015671661) ^ (7843108 + 7843108 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 7843108 * (6 : ZMod 4015671661) ^ 7843108) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 558355528 := by rw [factor_0_22]; decide
      have factor_0_24 : (6 : ZMod 4015671661) ^ 31372434 = 1759836412 := by
        calc
          (6 : ZMod 4015671661) ^ 31372434 = (6 : ZMod 4015671661) ^ (15686217 + 15686217) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 15686217 * (6 : ZMod 4015671661) ^ 15686217 := by rw [pow_add]
          _ = 1759836412 := by rw [factor_0_23]; decide
      have factor_0_25 : (6 : ZMod 4015671661) ^ 62744869 = 3903632676 := by
        calc
          (6 : ZMod 4015671661) ^ 62744869 = (6 : ZMod 4015671661) ^ (31372434 + 31372434 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 31372434 * (6 : ZMod 4015671661) ^ 31372434) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3903632676 := by rw [factor_0_24]; decide
      have factor_0_26 : (6 : ZMod 4015671661) ^ 125489739 = 1271839852 := by
        calc
          (6 : ZMod 4015671661) ^ 125489739 = (6 : ZMod 4015671661) ^ (62744869 + 62744869 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 62744869 * (6 : ZMod 4015671661) ^ 62744869) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1271839852 := by rw [factor_0_25]; decide
      have factor_0_27 : (6 : ZMod 4015671661) ^ 250979478 = 2074573971 := by
        calc
          (6 : ZMod 4015671661) ^ 250979478 = (6 : ZMod 4015671661) ^ (125489739 + 125489739) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 125489739 * (6 : ZMod 4015671661) ^ 125489739 := by rw [pow_add]
          _ = 2074573971 := by rw [factor_0_26]; decide
      have factor_0_28 : (6 : ZMod 4015671661) ^ 501958957 = 1118120016 := by
        calc
          (6 : ZMod 4015671661) ^ 501958957 = (6 : ZMod 4015671661) ^ (250979478 + 250979478 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 250979478 * (6 : ZMod 4015671661) ^ 250979478) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1118120016 := by rw [factor_0_27]; decide
      have factor_0_29 : (6 : ZMod 4015671661) ^ 1003917915 = 371169909 := by
        calc
          (6 : ZMod 4015671661) ^ 1003917915 = (6 : ZMod 4015671661) ^ (501958957 + 501958957 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 501958957 * (6 : ZMod 4015671661) ^ 501958957) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 371169909 := by rw [factor_0_28]; decide
      have factor_0_30 : (6 : ZMod 4015671661) ^ 2007835830 = 4015671660 := by
        calc
          (6 : ZMod 4015671661) ^ 2007835830 = (6 : ZMod 4015671661) ^ (1003917915 + 1003917915) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 1003917915 * (6 : ZMod 4015671661) ^ 1003917915 := by rw [pow_add]
          _ = 4015671660 := by rw [factor_0_29]; decide
      change (6 : ZMod 4015671661) ^ 2007835830 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (6 : ZMod 4015671661) ^ 1 = 6 := by norm_num
      have factor_1_1 : (6 : ZMod 4015671661) ^ 2 = 36 := by
        calc
          (6 : ZMod 4015671661) ^ 2 = (6 : ZMod 4015671661) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 1 * (6 : ZMod 4015671661) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_1_0]; decide
      have factor_1_2 : (6 : ZMod 4015671661) ^ 4 = 1296 := by
        calc
          (6 : ZMod 4015671661) ^ 4 = (6 : ZMod 4015671661) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 2 * (6 : ZMod 4015671661) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_1_1]; decide
      have factor_1_3 : (6 : ZMod 4015671661) ^ 9 = 10077696 := by
        calc
          (6 : ZMod 4015671661) ^ 9 = (6 : ZMod 4015671661) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 4 * (6 : ZMod 4015671661) ^ 4) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 10077696 := by rw [factor_1_2]; decide
      have factor_1_4 : (6 : ZMod 4015671661) ^ 19 = 1643812051 := by
        calc
          (6 : ZMod 4015671661) ^ 19 = (6 : ZMod 4015671661) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 9 * (6 : ZMod 4015671661) ^ 9) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1643812051 := by rw [factor_1_3]; decide
      have factor_1_5 : (6 : ZMod 4015671661) ^ 39 = 3600375929 := by
        calc
          (6 : ZMod 4015671661) ^ 39 = (6 : ZMod 4015671661) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 19 * (6 : ZMod 4015671661) ^ 19) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3600375929 := by rw [factor_1_4]; decide
      have factor_1_6 : (6 : ZMod 4015671661) ^ 79 = 2852181659 := by
        calc
          (6 : ZMod 4015671661) ^ 79 = (6 : ZMod 4015671661) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 39 * (6 : ZMod 4015671661) ^ 39) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2852181659 := by rw [factor_1_5]; decide
      have factor_1_7 : (6 : ZMod 4015671661) ^ 159 = 589635735 := by
        calc
          (6 : ZMod 4015671661) ^ 159 = (6 : ZMod 4015671661) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 79 * (6 : ZMod 4015671661) ^ 79) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 589635735 := by rw [factor_1_6]; decide
      have factor_1_8 : (6 : ZMod 4015671661) ^ 319 = 2918894201 := by
        calc
          (6 : ZMod 4015671661) ^ 319 = (6 : ZMod 4015671661) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 159 * (6 : ZMod 4015671661) ^ 159) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2918894201 := by rw [factor_1_7]; decide
      have factor_1_9 : (6 : ZMod 4015671661) ^ 638 = 3889733779 := by
        calc
          (6 : ZMod 4015671661) ^ 638 = (6 : ZMod 4015671661) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 319 * (6 : ZMod 4015671661) ^ 319 := by rw [pow_add]
          _ = 3889733779 := by rw [factor_1_8]; decide
      have factor_1_10 : (6 : ZMod 4015671661) ^ 1276 = 1126628731 := by
        calc
          (6 : ZMod 4015671661) ^ 1276 = (6 : ZMod 4015671661) ^ (638 + 638) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 638 * (6 : ZMod 4015671661) ^ 638 := by rw [pow_add]
          _ = 1126628731 := by rw [factor_1_9]; decide
      have factor_1_11 : (6 : ZMod 4015671661) ^ 2553 = 1249127998 := by
        calc
          (6 : ZMod 4015671661) ^ 2553 = (6 : ZMod 4015671661) ^ (1276 + 1276 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 1276 * (6 : ZMod 4015671661) ^ 1276) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1249127998 := by rw [factor_1_10]; decide
      have factor_1_12 : (6 : ZMod 4015671661) ^ 5106 = 452055832 := by
        calc
          (6 : ZMod 4015671661) ^ 5106 = (6 : ZMod 4015671661) ^ (2553 + 2553) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 2553 * (6 : ZMod 4015671661) ^ 2553 := by rw [pow_add]
          _ = 452055832 := by rw [factor_1_11]; decide
      have factor_1_13 : (6 : ZMod 4015671661) ^ 10212 = 343056245 := by
        calc
          (6 : ZMod 4015671661) ^ 10212 = (6 : ZMod 4015671661) ^ (5106 + 5106) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 5106 * (6 : ZMod 4015671661) ^ 5106 := by rw [pow_add]
          _ = 343056245 := by rw [factor_1_12]; decide
      have factor_1_14 : (6 : ZMod 4015671661) ^ 20424 = 704870111 := by
        calc
          (6 : ZMod 4015671661) ^ 20424 = (6 : ZMod 4015671661) ^ (10212 + 10212) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 10212 * (6 : ZMod 4015671661) ^ 10212 := by rw [pow_add]
          _ = 704870111 := by rw [factor_1_13]; decide
      have factor_1_15 : (6 : ZMod 4015671661) ^ 40849 = 2916615118 := by
        calc
          (6 : ZMod 4015671661) ^ 40849 = (6 : ZMod 4015671661) ^ (20424 + 20424 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 20424 * (6 : ZMod 4015671661) ^ 20424) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2916615118 := by rw [factor_1_14]; decide
      have factor_1_16 : (6 : ZMod 4015671661) ^ 81699 = 3100258667 := by
        calc
          (6 : ZMod 4015671661) ^ 81699 = (6 : ZMod 4015671661) ^ (40849 + 40849 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 40849 * (6 : ZMod 4015671661) ^ 40849) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3100258667 := by rw [factor_1_15]; decide
      have factor_1_17 : (6 : ZMod 4015671661) ^ 163398 = 100937420 := by
        calc
          (6 : ZMod 4015671661) ^ 163398 = (6 : ZMod 4015671661) ^ (81699 + 81699) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 81699 * (6 : ZMod 4015671661) ^ 81699 := by rw [pow_add]
          _ = 100937420 := by rw [factor_1_16]; decide
      have factor_1_18 : (6 : ZMod 4015671661) ^ 326796 = 1401550250 := by
        calc
          (6 : ZMod 4015671661) ^ 326796 = (6 : ZMod 4015671661) ^ (163398 + 163398) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 163398 * (6 : ZMod 4015671661) ^ 163398 := by rw [pow_add]
          _ = 1401550250 := by rw [factor_1_17]; decide
      have factor_1_19 : (6 : ZMod 4015671661) ^ 653592 = 586094928 := by
        calc
          (6 : ZMod 4015671661) ^ 653592 = (6 : ZMod 4015671661) ^ (326796 + 326796) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 326796 * (6 : ZMod 4015671661) ^ 326796 := by rw [pow_add]
          _ = 586094928 := by rw [factor_1_18]; decide
      have factor_1_20 : (6 : ZMod 4015671661) ^ 1307184 = 558039653 := by
        calc
          (6 : ZMod 4015671661) ^ 1307184 = (6 : ZMod 4015671661) ^ (653592 + 653592) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 653592 * (6 : ZMod 4015671661) ^ 653592 := by rw [pow_add]
          _ = 558039653 := by rw [factor_1_19]; decide
      have factor_1_21 : (6 : ZMod 4015671661) ^ 2614369 = 3927722478 := by
        calc
          (6 : ZMod 4015671661) ^ 2614369 = (6 : ZMod 4015671661) ^ (1307184 + 1307184 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 1307184 * (6 : ZMod 4015671661) ^ 1307184) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3927722478 := by rw [factor_1_20]; decide
      have factor_1_22 : (6 : ZMod 4015671661) ^ 5228739 = 2544828007 := by
        calc
          (6 : ZMod 4015671661) ^ 5228739 = (6 : ZMod 4015671661) ^ (2614369 + 2614369 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 2614369 * (6 : ZMod 4015671661) ^ 2614369) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2544828007 := by rw [factor_1_21]; decide
      have factor_1_23 : (6 : ZMod 4015671661) ^ 10457478 = 1322499149 := by
        calc
          (6 : ZMod 4015671661) ^ 10457478 = (6 : ZMod 4015671661) ^ (5228739 + 5228739) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 5228739 * (6 : ZMod 4015671661) ^ 5228739 := by rw [pow_add]
          _ = 1322499149 := by rw [factor_1_22]; decide
      have factor_1_24 : (6 : ZMod 4015671661) ^ 20914956 = 207278448 := by
        calc
          (6 : ZMod 4015671661) ^ 20914956 = (6 : ZMod 4015671661) ^ (10457478 + 10457478) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 10457478 * (6 : ZMod 4015671661) ^ 10457478 := by rw [pow_add]
          _ = 207278448 := by rw [factor_1_23]; decide
      have factor_1_25 : (6 : ZMod 4015671661) ^ 41829913 = 3424732343 := by
        calc
          (6 : ZMod 4015671661) ^ 41829913 = (6 : ZMod 4015671661) ^ (20914956 + 20914956 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 20914956 * (6 : ZMod 4015671661) ^ 20914956) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3424732343 := by rw [factor_1_24]; decide
      have factor_1_26 : (6 : ZMod 4015671661) ^ 83659826 = 670699253 := by
        calc
          (6 : ZMod 4015671661) ^ 83659826 = (6 : ZMod 4015671661) ^ (41829913 + 41829913) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 41829913 * (6 : ZMod 4015671661) ^ 41829913 := by rw [pow_add]
          _ = 670699253 := by rw [factor_1_25]; decide
      have factor_1_27 : (6 : ZMod 4015671661) ^ 167319652 = 908782424 := by
        calc
          (6 : ZMod 4015671661) ^ 167319652 = (6 : ZMod 4015671661) ^ (83659826 + 83659826) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 83659826 * (6 : ZMod 4015671661) ^ 83659826 := by rw [pow_add]
          _ = 908782424 := by rw [factor_1_26]; decide
      have factor_1_28 : (6 : ZMod 4015671661) ^ 334639305 = 295063157 := by
        calc
          (6 : ZMod 4015671661) ^ 334639305 = (6 : ZMod 4015671661) ^ (167319652 + 167319652 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 167319652 * (6 : ZMod 4015671661) ^ 167319652) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 295063157 := by rw [factor_1_27]; decide
      have factor_1_29 : (6 : ZMod 4015671661) ^ 669278610 = 3244881846 := by
        calc
          (6 : ZMod 4015671661) ^ 669278610 = (6 : ZMod 4015671661) ^ (334639305 + 334639305) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 334639305 * (6 : ZMod 4015671661) ^ 334639305 := by rw [pow_add]
          _ = 3244881846 := by rw [factor_1_28]; decide
      have factor_1_30 : (6 : ZMod 4015671661) ^ 1338557220 = 3244881845 := by
        calc
          (6 : ZMod 4015671661) ^ 1338557220 = (6 : ZMod 4015671661) ^ (669278610 + 669278610) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 669278610 * (6 : ZMod 4015671661) ^ 669278610 := by rw [pow_add]
          _ = 3244881845 := by rw [factor_1_29]; decide
      change (6 : ZMod 4015671661) ^ 1338557220 ≠ 1
      rw [factor_1_30]
      decide
    ·
      have factor_2_0 : (6 : ZMod 4015671661) ^ 1 = 6 := by norm_num
      have factor_2_1 : (6 : ZMod 4015671661) ^ 2 = 36 := by
        calc
          (6 : ZMod 4015671661) ^ 2 = (6 : ZMod 4015671661) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 1 * (6 : ZMod 4015671661) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_2_0]; decide
      have factor_2_2 : (6 : ZMod 4015671661) ^ 5 = 7776 := by
        calc
          (6 : ZMod 4015671661) ^ 5 = (6 : ZMod 4015671661) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 2 * (6 : ZMod 4015671661) ^ 2) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_2_1]; decide
      have factor_2_3 : (6 : ZMod 4015671661) ^ 11 = 362797056 := by
        calc
          (6 : ZMod 4015671661) ^ 11 = (6 : ZMod 4015671661) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 5 * (6 : ZMod 4015671661) ^ 5) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 362797056 := by rw [factor_2_2]; decide
      have factor_2_4 : (6 : ZMod 4015671661) ^ 23 = 2074437766 := by
        calc
          (6 : ZMod 4015671661) ^ 23 = (6 : ZMod 4015671661) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 11 * (6 : ZMod 4015671661) ^ 11) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2074437766 := by rw [factor_2_3]; decide
      have factor_2_5 : (6 : ZMod 4015671661) ^ 47 = 874003432 := by
        calc
          (6 : ZMod 4015671661) ^ 47 = (6 : ZMod 4015671661) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 23 * (6 : ZMod 4015671661) ^ 23) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 874003432 := by rw [factor_2_4]; decide
      have factor_2_6 : (6 : ZMod 4015671661) ^ 95 = 528924003 := by
        calc
          (6 : ZMod 4015671661) ^ 95 = (6 : ZMod 4015671661) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 47 * (6 : ZMod 4015671661) ^ 47) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 528924003 := by rw [factor_2_5]; decide
      have factor_2_7 : (6 : ZMod 4015671661) ^ 191 = 1249948854 := by
        calc
          (6 : ZMod 4015671661) ^ 191 = (6 : ZMod 4015671661) ^ (95 + 95 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 95 * (6 : ZMod 4015671661) ^ 95) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1249948854 := by rw [factor_2_6]; decide
      have factor_2_8 : (6 : ZMod 4015671661) ^ 382 = 906489260 := by
        calc
          (6 : ZMod 4015671661) ^ 382 = (6 : ZMod 4015671661) ^ (191 + 191) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 191 * (6 : ZMod 4015671661) ^ 191 := by rw [pow_add]
          _ = 906489260 := by rw [factor_2_7]; decide
      have factor_2_9 : (6 : ZMod 4015671661) ^ 765 = 3363205767 := by
        calc
          (6 : ZMod 4015671661) ^ 765 = (6 : ZMod 4015671661) ^ (382 + 382 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 382 * (6 : ZMod 4015671661) ^ 382) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3363205767 := by rw [factor_2_8]; decide
      have factor_2_10 : (6 : ZMod 4015671661) ^ 1531 = 1016790052 := by
        calc
          (6 : ZMod 4015671661) ^ 1531 = (6 : ZMod 4015671661) ^ (765 + 765 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 765 * (6 : ZMod 4015671661) ^ 765) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1016790052 := by rw [factor_2_9]; decide
      have factor_2_11 : (6 : ZMod 4015671661) ^ 3063 = 127252713 := by
        calc
          (6 : ZMod 4015671661) ^ 3063 = (6 : ZMod 4015671661) ^ (1531 + 1531 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 1531 * (6 : ZMod 4015671661) ^ 1531) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 127252713 := by rw [factor_2_10]; decide
      have factor_2_12 : (6 : ZMod 4015671661) ^ 6127 = 625176029 := by
        calc
          (6 : ZMod 4015671661) ^ 6127 = (6 : ZMod 4015671661) ^ (3063 + 3063 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 3063 * (6 : ZMod 4015671661) ^ 3063) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 625176029 := by rw [factor_2_11]; decide
      have factor_2_13 : (6 : ZMod 4015671661) ^ 12254 = 1474065145 := by
        calc
          (6 : ZMod 4015671661) ^ 12254 = (6 : ZMod 4015671661) ^ (6127 + 6127) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 6127 * (6 : ZMod 4015671661) ^ 6127 := by rw [pow_add]
          _ = 1474065145 := by rw [factor_2_12]; decide
      have factor_2_14 : (6 : ZMod 4015671661) ^ 24509 = 1902310527 := by
        calc
          (6 : ZMod 4015671661) ^ 24509 = (6 : ZMod 4015671661) ^ (12254 + 12254 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 12254 * (6 : ZMod 4015671661) ^ 12254) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1902310527 := by rw [factor_2_13]; decide
      have factor_2_15 : (6 : ZMod 4015671661) ^ 49019 = 3897403287 := by
        calc
          (6 : ZMod 4015671661) ^ 49019 = (6 : ZMod 4015671661) ^ (24509 + 24509 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 24509 * (6 : ZMod 4015671661) ^ 24509) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3897403287 := by rw [factor_2_14]; decide
      have factor_2_16 : (6 : ZMod 4015671661) ^ 98038 = 680650371 := by
        calc
          (6 : ZMod 4015671661) ^ 98038 = (6 : ZMod 4015671661) ^ (49019 + 49019) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 49019 * (6 : ZMod 4015671661) ^ 49019 := by rw [pow_add]
          _ = 680650371 := by rw [factor_2_15]; decide
      have factor_2_17 : (6 : ZMod 4015671661) ^ 196077 = 950429496 := by
        calc
          (6 : ZMod 4015671661) ^ 196077 = (6 : ZMod 4015671661) ^ (98038 + 98038 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 98038 * (6 : ZMod 4015671661) ^ 98038) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 950429496 := by rw [factor_2_16]; decide
      have factor_2_18 : (6 : ZMod 4015671661) ^ 392155 = 1750191933 := by
        calc
          (6 : ZMod 4015671661) ^ 392155 = (6 : ZMod 4015671661) ^ (196077 + 196077 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 196077 * (6 : ZMod 4015671661) ^ 196077) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1750191933 := by rw [factor_2_17]; decide
      have factor_2_19 : (6 : ZMod 4015671661) ^ 784310 = 3202766122 := by
        calc
          (6 : ZMod 4015671661) ^ 784310 = (6 : ZMod 4015671661) ^ (392155 + 392155) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 392155 * (6 : ZMod 4015671661) ^ 392155 := by rw [pow_add]
          _ = 3202766122 := by rw [factor_2_18]; decide
      have factor_2_20 : (6 : ZMod 4015671661) ^ 1568621 = 3092543376 := by
        calc
          (6 : ZMod 4015671661) ^ 1568621 = (6 : ZMod 4015671661) ^ (784310 + 784310 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 784310 * (6 : ZMod 4015671661) ^ 784310) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3092543376 := by rw [factor_2_19]; decide
      have factor_2_21 : (6 : ZMod 4015671661) ^ 3137243 = 869621930 := by
        calc
          (6 : ZMod 4015671661) ^ 3137243 = (6 : ZMod 4015671661) ^ (1568621 + 1568621 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 1568621 * (6 : ZMod 4015671661) ^ 1568621) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 869621930 := by rw [factor_2_20]; decide
      have factor_2_22 : (6 : ZMod 4015671661) ^ 6274486 = 2965710438 := by
        calc
          (6 : ZMod 4015671661) ^ 6274486 = (6 : ZMod 4015671661) ^ (3137243 + 3137243) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 3137243 * (6 : ZMod 4015671661) ^ 3137243 := by rw [pow_add]
          _ = 2965710438 := by rw [factor_2_21]; decide
      have factor_2_23 : (6 : ZMod 4015671661) ^ 12548973 = 565764109 := by
        calc
          (6 : ZMod 4015671661) ^ 12548973 = (6 : ZMod 4015671661) ^ (6274486 + 6274486 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 6274486 * (6 : ZMod 4015671661) ^ 6274486) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 565764109 := by rw [factor_2_22]; decide
      have factor_2_24 : (6 : ZMod 4015671661) ^ 25097947 = 1382393587 := by
        calc
          (6 : ZMod 4015671661) ^ 25097947 = (6 : ZMod 4015671661) ^ (12548973 + 12548973 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 12548973 * (6 : ZMod 4015671661) ^ 12548973) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1382393587 := by rw [factor_2_23]; decide
      have factor_2_25 : (6 : ZMod 4015671661) ^ 50195895 = 3261745636 := by
        calc
          (6 : ZMod 4015671661) ^ 50195895 = (6 : ZMod 4015671661) ^ (25097947 + 25097947 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 25097947 * (6 : ZMod 4015671661) ^ 25097947) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3261745636 := by rw [factor_2_24]; decide
      have factor_2_26 : (6 : ZMod 4015671661) ^ 100391791 = 2188692958 := by
        calc
          (6 : ZMod 4015671661) ^ 100391791 = (6 : ZMod 4015671661) ^ (50195895 + 50195895 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 50195895 * (6 : ZMod 4015671661) ^ 50195895) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2188692958 := by rw [factor_2_25]; decide
      have factor_2_27 : (6 : ZMod 4015671661) ^ 200783583 = 584055715 := by
        calc
          (6 : ZMod 4015671661) ^ 200783583 = (6 : ZMod 4015671661) ^ (100391791 + 100391791 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 100391791 * (6 : ZMod 4015671661) ^ 100391791) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 584055715 := by rw [factor_2_26]; decide
      have factor_2_28 : (6 : ZMod 4015671661) ^ 401567166 = 2553603453 := by
        calc
          (6 : ZMod 4015671661) ^ 401567166 = (6 : ZMod 4015671661) ^ (200783583 + 200783583) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 200783583 * (6 : ZMod 4015671661) ^ 200783583 := by rw [pow_add]
          _ = 2553603453 := by rw [factor_2_27]; decide
      have factor_2_29 : (6 : ZMod 4015671661) ^ 803134332 = 3906232709 := by
        calc
          (6 : ZMod 4015671661) ^ 803134332 = (6 : ZMod 4015671661) ^ (401567166 + 401567166) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 401567166 * (6 : ZMod 4015671661) ^ 401567166 := by rw [pow_add]
          _ = 3906232709 := by rw [factor_2_28]; decide
      change (6 : ZMod 4015671661) ^ 803134332 ≠ 1
      rw [factor_2_29]
      decide
    ·
      have factor_3_0 : (6 : ZMod 4015671661) ^ 1 = 6 := by norm_num
      have factor_3_1 : (6 : ZMod 4015671661) ^ 2 = 36 := by
        calc
          (6 : ZMod 4015671661) ^ 2 = (6 : ZMod 4015671661) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 1 * (6 : ZMod 4015671661) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_3_0]; decide
      have factor_3_2 : (6 : ZMod 4015671661) ^ 4 = 1296 := by
        calc
          (6 : ZMod 4015671661) ^ 4 = (6 : ZMod 4015671661) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 2 * (6 : ZMod 4015671661) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_3_1]; decide
      have factor_3_3 : (6 : ZMod 4015671661) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 4015671661) ^ 8 = (6 : ZMod 4015671661) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 4 * (6 : ZMod 4015671661) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_3_2]; decide
      have factor_3_4 : (6 : ZMod 4015671661) ^ 17 = 603393621 := by
        calc
          (6 : ZMod 4015671661) ^ 17 = (6 : ZMod 4015671661) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 8 * (6 : ZMod 4015671661) ^ 8) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 603393621 := by rw [factor_3_3]; decide
      have factor_3_5 : (6 : ZMod 4015671661) ^ 34 = 3059210857 := by
        calc
          (6 : ZMod 4015671661) ^ 34 = (6 : ZMod 4015671661) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 17 * (6 : ZMod 4015671661) ^ 17 := by rw [pow_add]
          _ = 3059210857 := by rw [factor_3_4]; decide
      have factor_3_6 : (6 : ZMod 4015671661) ^ 68 = 757076446 := by
        calc
          (6 : ZMod 4015671661) ^ 68 = (6 : ZMod 4015671661) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 34 * (6 : ZMod 4015671661) ^ 34 := by rw [pow_add]
          _ = 757076446 := by rw [factor_3_5]; decide
      have factor_3_7 : (6 : ZMod 4015671661) ^ 136 = 1977602102 := by
        calc
          (6 : ZMod 4015671661) ^ 136 = (6 : ZMod 4015671661) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 68 * (6 : ZMod 4015671661) ^ 68 := by rw [pow_add]
          _ = 1977602102 := by rw [factor_3_6]; decide
      have factor_3_8 : (6 : ZMod 4015671661) ^ 273 = 204477117 := by
        calc
          (6 : ZMod 4015671661) ^ 273 = (6 : ZMod 4015671661) ^ (136 + 136 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 136 * (6 : ZMod 4015671661) ^ 136) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 204477117 := by rw [factor_3_7]; decide
      have factor_3_9 : (6 : ZMod 4015671661) ^ 547 = 2867239076 := by
        calc
          (6 : ZMod 4015671661) ^ 547 = (6 : ZMod 4015671661) ^ (273 + 273 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 273 * (6 : ZMod 4015671661) ^ 273) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2867239076 := by rw [factor_3_8]; decide
      have factor_3_10 : (6 : ZMod 4015671661) ^ 1094 = 189795065 := by
        calc
          (6 : ZMod 4015671661) ^ 1094 = (6 : ZMod 4015671661) ^ (547 + 547) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 547 * (6 : ZMod 4015671661) ^ 547 := by rw [pow_add]
          _ = 189795065 := by rw [factor_3_9]; decide
      have factor_3_11 : (6 : ZMod 4015671661) ^ 2188 = 1693206469 := by
        calc
          (6 : ZMod 4015671661) ^ 2188 = (6 : ZMod 4015671661) ^ (1094 + 1094) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 1094 * (6 : ZMod 4015671661) ^ 1094 := by rw [pow_add]
          _ = 1693206469 := by rw [factor_3_10]; decide
      have factor_3_12 : (6 : ZMod 4015671661) ^ 4376 = 2889707281 := by
        calc
          (6 : ZMod 4015671661) ^ 4376 = (6 : ZMod 4015671661) ^ (2188 + 2188) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 2188 * (6 : ZMod 4015671661) ^ 2188 := by rw [pow_add]
          _ = 2889707281 := by rw [factor_3_11]; decide
      have factor_3_13 : (6 : ZMod 4015671661) ^ 8753 = 293181520 := by
        calc
          (6 : ZMod 4015671661) ^ 8753 = (6 : ZMod 4015671661) ^ (4376 + 4376 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 4376 * (6 : ZMod 4015671661) ^ 4376) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 293181520 := by rw [factor_3_12]; decide
      have factor_3_14 : (6 : ZMod 4015671661) ^ 17506 = 3969536993 := by
        calc
          (6 : ZMod 4015671661) ^ 17506 = (6 : ZMod 4015671661) ^ (8753 + 8753) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 8753 * (6 : ZMod 4015671661) ^ 8753 := by rw [pow_add]
          _ = 3969536993 := by rw [factor_3_13]; decide
      have factor_3_15 : (6 : ZMod 4015671661) ^ 35013 = 3300420533 := by
        calc
          (6 : ZMod 4015671661) ^ 35013 = (6 : ZMod 4015671661) ^ (17506 + 17506 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 17506 * (6 : ZMod 4015671661) ^ 17506) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3300420533 := by rw [factor_3_14]; decide
      have factor_3_16 : (6 : ZMod 4015671661) ^ 70027 = 1171052702 := by
        calc
          (6 : ZMod 4015671661) ^ 70027 = (6 : ZMod 4015671661) ^ (35013 + 35013 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 35013 * (6 : ZMod 4015671661) ^ 35013) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1171052702 := by rw [factor_3_15]; decide
      have factor_3_17 : (6 : ZMod 4015671661) ^ 140055 = 1716957820 := by
        calc
          (6 : ZMod 4015671661) ^ 140055 = (6 : ZMod 4015671661) ^ (70027 + 70027 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 70027 * (6 : ZMod 4015671661) ^ 70027) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1716957820 := by rw [factor_3_16]; decide
      have factor_3_18 : (6 : ZMod 4015671661) ^ 280111 = 904222928 := by
        calc
          (6 : ZMod 4015671661) ^ 280111 = (6 : ZMod 4015671661) ^ (140055 + 140055 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 140055 * (6 : ZMod 4015671661) ^ 140055) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 904222928 := by rw [factor_3_17]; decide
      have factor_3_19 : (6 : ZMod 4015671661) ^ 560222 = 2699366524 := by
        calc
          (6 : ZMod 4015671661) ^ 560222 = (6 : ZMod 4015671661) ^ (280111 + 280111) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 280111 * (6 : ZMod 4015671661) ^ 280111 := by rw [pow_add]
          _ = 2699366524 := by rw [factor_3_18]; decide
      have factor_3_20 : (6 : ZMod 4015671661) ^ 1120444 = 2372328266 := by
        calc
          (6 : ZMod 4015671661) ^ 1120444 = (6 : ZMod 4015671661) ^ (560222 + 560222) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 560222 * (6 : ZMod 4015671661) ^ 560222 := by rw [pow_add]
          _ = 2372328266 := by rw [factor_3_19]; decide
      have factor_3_21 : (6 : ZMod 4015671661) ^ 2240888 = 312965102 := by
        calc
          (6 : ZMod 4015671661) ^ 2240888 = (6 : ZMod 4015671661) ^ (1120444 + 1120444) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 1120444 * (6 : ZMod 4015671661) ^ 1120444 := by rw [pow_add]
          _ = 312965102 := by rw [factor_3_20]; decide
      have factor_3_22 : (6 : ZMod 4015671661) ^ 4481776 = 44624018 := by
        calc
          (6 : ZMod 4015671661) ^ 4481776 = (6 : ZMod 4015671661) ^ (2240888 + 2240888) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 2240888 * (6 : ZMod 4015671661) ^ 2240888 := by rw [pow_add]
          _ = 44624018 := by rw [factor_3_21]; decide
      have factor_3_23 : (6 : ZMod 4015671661) ^ 8963552 = 3687864322 := by
        calc
          (6 : ZMod 4015671661) ^ 8963552 = (6 : ZMod 4015671661) ^ (4481776 + 4481776) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 4481776 * (6 : ZMod 4015671661) ^ 4481776 := by rw [pow_add]
          _ = 3687864322 := by rw [factor_3_22]; decide
      have factor_3_24 : (6 : ZMod 4015671661) ^ 17927105 = 3462260940 := by
        calc
          (6 : ZMod 4015671661) ^ 17927105 = (6 : ZMod 4015671661) ^ (8963552 + 8963552 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 8963552 * (6 : ZMod 4015671661) ^ 8963552) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3462260940 := by rw [factor_3_23]; decide
      have factor_3_25 : (6 : ZMod 4015671661) ^ 35854211 = 713392034 := by
        calc
          (6 : ZMod 4015671661) ^ 35854211 = (6 : ZMod 4015671661) ^ (17927105 + 17927105 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 17927105 * (6 : ZMod 4015671661) ^ 17927105) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 713392034 := by rw [factor_3_24]; decide
      have factor_3_26 : (6 : ZMod 4015671661) ^ 71708422 = 2240946707 := by
        calc
          (6 : ZMod 4015671661) ^ 71708422 = (6 : ZMod 4015671661) ^ (35854211 + 35854211) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 35854211 * (6 : ZMod 4015671661) ^ 35854211 := by rw [pow_add]
          _ = 2240946707 := by rw [factor_3_25]; decide
      have factor_3_27 : (6 : ZMod 4015671661) ^ 143416845 = 2639615190 := by
        calc
          (6 : ZMod 4015671661) ^ 143416845 = (6 : ZMod 4015671661) ^ (71708422 + 71708422 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 71708422 * (6 : ZMod 4015671661) ^ 71708422) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2639615190 := by rw [factor_3_26]; decide
      have factor_3_28 : (6 : ZMod 4015671661) ^ 286833690 = 176256204 := by
        calc
          (6 : ZMod 4015671661) ^ 286833690 = (6 : ZMod 4015671661) ^ (143416845 + 143416845) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 143416845 * (6 : ZMod 4015671661) ^ 143416845 := by rw [pow_add]
          _ = 176256204 := by rw [factor_3_27]; decide
      have factor_3_29 : (6 : ZMod 4015671661) ^ 573667380 = 1529735044 := by
        calc
          (6 : ZMod 4015671661) ^ 573667380 = (6 : ZMod 4015671661) ^ (286833690 + 286833690) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 286833690 * (6 : ZMod 4015671661) ^ 286833690 := by rw [pow_add]
          _ = 1529735044 := by rw [factor_3_28]; decide
      change (6 : ZMod 4015671661) ^ 573667380 ≠ 1
      rw [factor_3_29]
      decide
    ·
      have factor_4_0 : (6 : ZMod 4015671661) ^ 1 = 6 := by norm_num
      have factor_4_1 : (6 : ZMod 4015671661) ^ 2 = 36 := by
        calc
          (6 : ZMod 4015671661) ^ 2 = (6 : ZMod 4015671661) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 1 * (6 : ZMod 4015671661) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_4_0]; decide
      have factor_4_2 : (6 : ZMod 4015671661) ^ 5 = 7776 := by
        calc
          (6 : ZMod 4015671661) ^ 5 = (6 : ZMod 4015671661) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 2 * (6 : ZMod 4015671661) ^ 2) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_4_1]; decide
      have factor_4_3 : (6 : ZMod 4015671661) ^ 10 = 60466176 := by
        calc
          (6 : ZMod 4015671661) ^ 10 = (6 : ZMod 4015671661) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 5 * (6 : ZMod 4015671661) ^ 5 := by rw [pow_add]
          _ = 60466176 := by rw [factor_4_2]; decide
      have factor_4_4 : (6 : ZMod 4015671661) ^ 21 = 2957830582 := by
        calc
          (6 : ZMod 4015671661) ^ 21 = (6 : ZMod 4015671661) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 10 * (6 : ZMod 4015671661) ^ 10) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2957830582 := by rw [factor_4_3]; decide
      have factor_4_5 : (6 : ZMod 4015671661) ^ 43 = 3892405563 := by
        calc
          (6 : ZMod 4015671661) ^ 43 = (6 : ZMod 4015671661) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 21 * (6 : ZMod 4015671661) ^ 21) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3892405563 := by rw [factor_4_4]; decide
      have factor_4_6 : (6 : ZMod 4015671661) ^ 87 = 2159283096 := by
        calc
          (6 : ZMod 4015671661) ^ 87 = (6 : ZMod 4015671661) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 43 * (6 : ZMod 4015671661) ^ 43) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2159283096 := by rw [factor_4_5]; decide
      have factor_4_7 : (6 : ZMod 4015671661) ^ 174 = 1554092485 := by
        calc
          (6 : ZMod 4015671661) ^ 174 = (6 : ZMod 4015671661) ^ (87 + 87) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 87 * (6 : ZMod 4015671661) ^ 87 := by rw [pow_add]
          _ = 1554092485 := by rw [factor_4_6]; decide
      have factor_4_8 : (6 : ZMod 4015671661) ^ 348 = 2340057131 := by
        calc
          (6 : ZMod 4015671661) ^ 348 = (6 : ZMod 4015671661) ^ (174 + 174) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 174 * (6 : ZMod 4015671661) ^ 174 := by rw [pow_add]
          _ = 2340057131 := by rw [factor_4_7]; decide
      have factor_4_9 : (6 : ZMod 4015671661) ^ 696 = 2912093742 := by
        calc
          (6 : ZMod 4015671661) ^ 696 = (6 : ZMod 4015671661) ^ (348 + 348) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 348 * (6 : ZMod 4015671661) ^ 348 := by rw [pow_add]
          _ = 2912093742 := by rw [factor_4_8]; decide
      have factor_4_10 : (6 : ZMod 4015671661) ^ 1392 = 1777878202 := by
        calc
          (6 : ZMod 4015671661) ^ 1392 = (6 : ZMod 4015671661) ^ (696 + 696) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 696 * (6 : ZMod 4015671661) ^ 696 := by rw [pow_add]
          _ = 1777878202 := by rw [factor_4_9]; decide
      have factor_4_11 : (6 : ZMod 4015671661) ^ 2785 = 2588595077 := by
        calc
          (6 : ZMod 4015671661) ^ 2785 = (6 : ZMod 4015671661) ^ (1392 + 1392 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 1392 * (6 : ZMod 4015671661) ^ 1392) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2588595077 := by rw [factor_4_10]; decide
      have factor_4_12 : (6 : ZMod 4015671661) ^ 5570 = 2931676953 := by
        calc
          (6 : ZMod 4015671661) ^ 5570 = (6 : ZMod 4015671661) ^ (2785 + 2785) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 2785 * (6 : ZMod 4015671661) ^ 2785 := by rw [pow_add]
          _ = 2931676953 := by rw [factor_4_11]; decide
      have factor_4_13 : (6 : ZMod 4015671661) ^ 11140 = 715361852 := by
        calc
          (6 : ZMod 4015671661) ^ 11140 = (6 : ZMod 4015671661) ^ (5570 + 5570) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 5570 * (6 : ZMod 4015671661) ^ 5570 := by rw [pow_add]
          _ = 715361852 := by rw [factor_4_12]; decide
      have factor_4_14 : (6 : ZMod 4015671661) ^ 22281 = 3198927325 := by
        calc
          (6 : ZMod 4015671661) ^ 22281 = (6 : ZMod 4015671661) ^ (11140 + 11140 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 11140 * (6 : ZMod 4015671661) ^ 11140) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3198927325 := by rw [factor_4_13]; decide
      have factor_4_15 : (6 : ZMod 4015671661) ^ 44563 = 2920941545 := by
        calc
          (6 : ZMod 4015671661) ^ 44563 = (6 : ZMod 4015671661) ^ (22281 + 22281 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 22281 * (6 : ZMod 4015671661) ^ 22281) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2920941545 := by rw [factor_4_14]; decide
      have factor_4_16 : (6 : ZMod 4015671661) ^ 89126 = 169294189 := by
        calc
          (6 : ZMod 4015671661) ^ 89126 = (6 : ZMod 4015671661) ^ (44563 + 44563) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 44563 * (6 : ZMod 4015671661) ^ 44563 := by rw [pow_add]
          _ = 169294189 := by rw [factor_4_15]; decide
      have factor_4_17 : (6 : ZMod 4015671661) ^ 178252 = 3167443334 := by
        calc
          (6 : ZMod 4015671661) ^ 178252 = (6 : ZMod 4015671661) ^ (89126 + 89126) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 89126 * (6 : ZMod 4015671661) ^ 89126 := by rw [pow_add]
          _ = 3167443334 := by rw [factor_4_16]; decide
      have factor_4_18 : (6 : ZMod 4015671661) ^ 356504 = 1949952062 := by
        calc
          (6 : ZMod 4015671661) ^ 356504 = (6 : ZMod 4015671661) ^ (178252 + 178252) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 178252 * (6 : ZMod 4015671661) ^ 178252 := by rw [pow_add]
          _ = 1949952062 := by rw [factor_4_17]; decide
      have factor_4_19 : (6 : ZMod 4015671661) ^ 713009 = 2755197082 := by
        calc
          (6 : ZMod 4015671661) ^ 713009 = (6 : ZMod 4015671661) ^ (356504 + 356504 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 356504 * (6 : ZMod 4015671661) ^ 356504) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2755197082 := by rw [factor_4_18]; decide
      have factor_4_20 : (6 : ZMod 4015671661) ^ 1426019 = 3147766794 := by
        calc
          (6 : ZMod 4015671661) ^ 1426019 = (6 : ZMod 4015671661) ^ (713009 + 713009 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 713009 * (6 : ZMod 4015671661) ^ 713009) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3147766794 := by rw [factor_4_19]; decide
      have factor_4_21 : (6 : ZMod 4015671661) ^ 2852039 = 3446992418 := by
        calc
          (6 : ZMod 4015671661) ^ 2852039 = (6 : ZMod 4015671661) ^ (1426019 + 1426019 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 1426019 * (6 : ZMod 4015671661) ^ 1426019) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3446992418 := by rw [factor_4_20]; decide
      have factor_4_22 : (6 : ZMod 4015671661) ^ 5704079 = 2545218853 := by
        calc
          (6 : ZMod 4015671661) ^ 5704079 = (6 : ZMod 4015671661) ^ (2852039 + 2852039 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 2852039 * (6 : ZMod 4015671661) ^ 2852039) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2545218853 := by rw [factor_4_21]; decide
      have factor_4_23 : (6 : ZMod 4015671661) ^ 11408158 = 1801608394 := by
        calc
          (6 : ZMod 4015671661) ^ 11408158 = (6 : ZMod 4015671661) ^ (5704079 + 5704079) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 5704079 * (6 : ZMod 4015671661) ^ 5704079 := by rw [pow_add]
          _ = 1801608394 := by rw [factor_4_22]; decide
      have factor_4_24 : (6 : ZMod 4015671661) ^ 22816316 = 877405633 := by
        calc
          (6 : ZMod 4015671661) ^ 22816316 = (6 : ZMod 4015671661) ^ (11408158 + 11408158) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 11408158 * (6 : ZMod 4015671661) ^ 11408158 := by rw [pow_add]
          _ = 877405633 := by rw [factor_4_23]; decide
      have factor_4_25 : (6 : ZMod 4015671661) ^ 45632632 = 1405510368 := by
        calc
          (6 : ZMod 4015671661) ^ 45632632 = (6 : ZMod 4015671661) ^ (22816316 + 22816316) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 22816316 * (6 : ZMod 4015671661) ^ 22816316 := by rw [pow_add]
          _ = 1405510368 := by rw [factor_4_24]; decide
      have factor_4_26 : (6 : ZMod 4015671661) ^ 91265265 = 2892805169 := by
        calc
          (6 : ZMod 4015671661) ^ 91265265 = (6 : ZMod 4015671661) ^ (45632632 + 45632632 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 45632632 * (6 : ZMod 4015671661) ^ 45632632) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2892805169 := by rw [factor_4_25]; decide
      have factor_4_27 : (6 : ZMod 4015671661) ^ 182530530 = 3352824931 := by
        calc
          (6 : ZMod 4015671661) ^ 182530530 = (6 : ZMod 4015671661) ^ (91265265 + 91265265) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 91265265 * (6 : ZMod 4015671661) ^ 91265265 := by rw [pow_add]
          _ = 3352824931 := by rw [factor_4_26]; decide
      have factor_4_28 : (6 : ZMod 4015671661) ^ 365061060 = 3537151964 := by
        calc
          (6 : ZMod 4015671661) ^ 365061060 = (6 : ZMod 4015671661) ^ (182530530 + 182530530) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 182530530 * (6 : ZMod 4015671661) ^ 182530530 := by rw [pow_add]
          _ = 3537151964 := by rw [factor_4_27]; decide
      change (6 : ZMod 4015671661) ^ 365061060 ≠ 1
      rw [factor_4_28]
      decide
    ·
      have factor_5_0 : (6 : ZMod 4015671661) ^ 1 = 6 := by norm_num
      have factor_5_1 : (6 : ZMod 4015671661) ^ 2 = 36 := by
        calc
          (6 : ZMod 4015671661) ^ 2 = (6 : ZMod 4015671661) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 1 * (6 : ZMod 4015671661) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_5_0]; decide
      have factor_5_2 : (6 : ZMod 4015671661) ^ 4 = 1296 := by
        calc
          (6 : ZMod 4015671661) ^ 4 = (6 : ZMod 4015671661) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 2 * (6 : ZMod 4015671661) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_5_1]; decide
      have factor_5_3 : (6 : ZMod 4015671661) ^ 9 = 10077696 := by
        calc
          (6 : ZMod 4015671661) ^ 9 = (6 : ZMod 4015671661) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 4 * (6 : ZMod 4015671661) ^ 4) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 10077696 := by rw [factor_5_2]; decide
      have factor_5_4 : (6 : ZMod 4015671661) ^ 18 = 3620361726 := by
        calc
          (6 : ZMod 4015671661) ^ 18 = (6 : ZMod 4015671661) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 9 * (6 : ZMod 4015671661) ^ 9 := by rw [pow_add]
          _ = 3620361726 := by rw [factor_5_3]; decide
      have factor_5_5 : (6 : ZMod 4015671661) ^ 36 = 1708456005 := by
        calc
          (6 : ZMod 4015671661) ^ 36 = (6 : ZMod 4015671661) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 18 * (6 : ZMod 4015671661) ^ 18 := by rw [pow_add]
          _ = 1708456005 := by rw [factor_5_4]; decide
      have factor_5_6 : (6 : ZMod 4015671661) ^ 73 = 51789070 := by
        calc
          (6 : ZMod 4015671661) ^ 73 = (6 : ZMod 4015671661) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 36 * (6 : ZMod 4015671661) ^ 36) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 51789070 := by rw [factor_5_5]; decide
      have factor_5_7 : (6 : ZMod 4015671661) ^ 147 = 3074198340 := by
        calc
          (6 : ZMod 4015671661) ^ 147 = (6 : ZMod 4015671661) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 73 * (6 : ZMod 4015671661) ^ 73) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3074198340 := by rw [factor_5_6]; decide
      have factor_5_8 : (6 : ZMod 4015671661) ^ 294 = 490183892 := by
        calc
          (6 : ZMod 4015671661) ^ 294 = (6 : ZMod 4015671661) ^ (147 + 147) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 147 * (6 : ZMod 4015671661) ^ 147 := by rw [pow_add]
          _ = 490183892 := by rw [factor_5_7]; decide
      have factor_5_9 : (6 : ZMod 4015671661) ^ 589 = 1509087438 := by
        calc
          (6 : ZMod 4015671661) ^ 589 = (6 : ZMod 4015671661) ^ (294 + 294 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 294 * (6 : ZMod 4015671661) ^ 294) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1509087438 := by rw [factor_5_8]; decide
      have factor_5_10 : (6 : ZMod 4015671661) ^ 1178 = 189461646 := by
        calc
          (6 : ZMod 4015671661) ^ 1178 = (6 : ZMod 4015671661) ^ (589 + 589) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 589 * (6 : ZMod 4015671661) ^ 589 := by rw [pow_add]
          _ = 189461646 := by rw [factor_5_9]; decide
      have factor_5_11 : (6 : ZMod 4015671661) ^ 2356 = 3800486450 := by
        calc
          (6 : ZMod 4015671661) ^ 2356 = (6 : ZMod 4015671661) ^ (1178 + 1178) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 1178 * (6 : ZMod 4015671661) ^ 1178 := by rw [pow_add]
          _ = 3800486450 := by rw [factor_5_10]; decide
      have factor_5_12 : (6 : ZMod 4015671661) ^ 4713 = 3491339159 := by
        calc
          (6 : ZMod 4015671661) ^ 4713 = (6 : ZMod 4015671661) ^ (2356 + 2356 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 2356 * (6 : ZMod 4015671661) ^ 2356) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3491339159 := by rw [factor_5_11]; decide
      have factor_5_13 : (6 : ZMod 4015671661) ^ 9426 = 1121314833 := by
        calc
          (6 : ZMod 4015671661) ^ 9426 = (6 : ZMod 4015671661) ^ (4713 + 4713) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 4713 * (6 : ZMod 4015671661) ^ 4713 := by rw [pow_add]
          _ = 1121314833 := by rw [factor_5_12]; decide
      have factor_5_14 : (6 : ZMod 4015671661) ^ 18853 = 1564975673 := by
        calc
          (6 : ZMod 4015671661) ^ 18853 = (6 : ZMod 4015671661) ^ (9426 + 9426 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 9426 * (6 : ZMod 4015671661) ^ 9426) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1564975673 := by rw [factor_5_13]; decide
      have factor_5_15 : (6 : ZMod 4015671661) ^ 37707 = 3750072254 := by
        calc
          (6 : ZMod 4015671661) ^ 37707 = (6 : ZMod 4015671661) ^ (18853 + 18853 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 18853 * (6 : ZMod 4015671661) ^ 18853) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3750072254 := by rw [factor_5_14]; decide
      have factor_5_16 : (6 : ZMod 4015671661) ^ 75414 = 1948622614 := by
        calc
          (6 : ZMod 4015671661) ^ 75414 = (6 : ZMod 4015671661) ^ (37707 + 37707) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 37707 * (6 : ZMod 4015671661) ^ 37707 := by rw [pow_add]
          _ = 1948622614 := by rw [factor_5_15]; decide
      have factor_5_17 : (6 : ZMod 4015671661) ^ 150829 = 3641934162 := by
        calc
          (6 : ZMod 4015671661) ^ 150829 = (6 : ZMod 4015671661) ^ (75414 + 75414 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 75414 * (6 : ZMod 4015671661) ^ 75414) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3641934162 := by rw [factor_5_16]; decide
      have factor_5_18 : (6 : ZMod 4015671661) ^ 301658 = 587632351 := by
        calc
          (6 : ZMod 4015671661) ^ 301658 = (6 : ZMod 4015671661) ^ (150829 + 150829) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 150829 * (6 : ZMod 4015671661) ^ 150829 := by rw [pow_add]
          _ = 587632351 := by rw [factor_5_17]; decide
      have factor_5_19 : (6 : ZMod 4015671661) ^ 603316 = 1529541422 := by
        calc
          (6 : ZMod 4015671661) ^ 603316 = (6 : ZMod 4015671661) ^ (301658 + 301658) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 301658 * (6 : ZMod 4015671661) ^ 301658 := by rw [pow_add]
          _ = 1529541422 := by rw [factor_5_18]; decide
      have factor_5_20 : (6 : ZMod 4015671661) ^ 1206632 = 2068326689 := by
        calc
          (6 : ZMod 4015671661) ^ 1206632 = (6 : ZMod 4015671661) ^ (603316 + 603316) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 603316 * (6 : ZMod 4015671661) ^ 603316 := by rw [pow_add]
          _ = 2068326689 := by rw [factor_5_19]; decide
      have factor_5_21 : (6 : ZMod 4015671661) ^ 2413264 = 2705570992 := by
        calc
          (6 : ZMod 4015671661) ^ 2413264 = (6 : ZMod 4015671661) ^ (1206632 + 1206632) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 1206632 * (6 : ZMod 4015671661) ^ 1206632 := by rw [pow_add]
          _ = 2705570992 := by rw [factor_5_20]; decide
      have factor_5_22 : (6 : ZMod 4015671661) ^ 4826528 = 2630145262 := by
        calc
          (6 : ZMod 4015671661) ^ 4826528 = (6 : ZMod 4015671661) ^ (2413264 + 2413264) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 2413264 * (6 : ZMod 4015671661) ^ 2413264 := by rw [pow_add]
          _ = 2630145262 := by rw [factor_5_21]; decide
      have factor_5_23 : (6 : ZMod 4015671661) ^ 9653056 = 1711016962 := by
        calc
          (6 : ZMod 4015671661) ^ 9653056 = (6 : ZMod 4015671661) ^ (4826528 + 4826528) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 4826528 * (6 : ZMod 4015671661) ^ 4826528 := by rw [pow_add]
          _ = 1711016962 := by rw [factor_5_22]; decide
      have factor_5_24 : (6 : ZMod 4015671661) ^ 19306113 = 828392303 := by
        calc
          (6 : ZMod 4015671661) ^ 19306113 = (6 : ZMod 4015671661) ^ (9653056 + 9653056 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 9653056 * (6 : ZMod 4015671661) ^ 9653056) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 828392303 := by rw [factor_5_23]; decide
      have factor_5_25 : (6 : ZMod 4015671661) ^ 38612227 = 2351381253 := by
        calc
          (6 : ZMod 4015671661) ^ 38612227 = (6 : ZMod 4015671661) ^ (19306113 + 19306113 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 19306113 * (6 : ZMod 4015671661) ^ 19306113) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2351381253 := by rw [factor_5_24]; decide
      have factor_5_26 : (6 : ZMod 4015671661) ^ 77224455 = 2093921144 := by
        calc
          (6 : ZMod 4015671661) ^ 77224455 = (6 : ZMod 4015671661) ^ (38612227 + 38612227 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 38612227 * (6 : ZMod 4015671661) ^ 38612227) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2093921144 := by rw [factor_5_25]; decide
      have factor_5_27 : (6 : ZMod 4015671661) ^ 154448910 = 3102071188 := by
        calc
          (6 : ZMod 4015671661) ^ 154448910 = (6 : ZMod 4015671661) ^ (77224455 + 77224455) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 77224455 * (6 : ZMod 4015671661) ^ 77224455 := by rw [pow_add]
          _ = 3102071188 := by rw [factor_5_26]; decide
      have factor_5_28 : (6 : ZMod 4015671661) ^ 308897820 = 475440680 := by
        calc
          (6 : ZMod 4015671661) ^ 308897820 = (6 : ZMod 4015671661) ^ (154448910 + 154448910) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 154448910 * (6 : ZMod 4015671661) ^ 154448910 := by rw [pow_add]
          _ = 475440680 := by rw [factor_5_27]; decide
      change (6 : ZMod 4015671661) ^ 308897820 ≠ 1
      rw [factor_5_28]
      decide
    ·
      have factor_6_0 : (6 : ZMod 4015671661) ^ 1 = 6 := by norm_num
      have factor_6_1 : (6 : ZMod 4015671661) ^ 3 = 216 := by
        calc
          (6 : ZMod 4015671661) ^ 3 = (6 : ZMod 4015671661) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 1 * (6 : ZMod 4015671661) ^ 1) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_6_0]; decide
      have factor_6_2 : (6 : ZMod 4015671661) ^ 7 = 279936 := by
        calc
          (6 : ZMod 4015671661) ^ 7 = (6 : ZMod 4015671661) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 3 * (6 : ZMod 4015671661) ^ 3) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 279936 := by rw [factor_6_1]; decide
      have factor_6_3 : (6 : ZMod 4015671661) ^ 14 = 2066402537 := by
        calc
          (6 : ZMod 4015671661) ^ 14 = (6 : ZMod 4015671661) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 7 * (6 : ZMod 4015671661) ^ 7 := by rw [pow_add]
          _ = 2066402537 := by rw [factor_6_2]; decide
      have factor_6_4 : (6 : ZMod 4015671661) ^ 28 = 3890677840 := by
        calc
          (6 : ZMod 4015671661) ^ 28 = (6 : ZMod 4015671661) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 14 * (6 : ZMod 4015671661) ^ 14 := by rw [pow_add]
          _ = 3890677840 := by rw [factor_6_3]; decide
      have factor_6_5 : (6 : ZMod 4015671661) ^ 56 = 2810460221 := by
        calc
          (6 : ZMod 4015671661) ^ 56 = (6 : ZMod 4015671661) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 28 * (6 : ZMod 4015671661) ^ 28 := by rw [pow_add]
          _ = 2810460221 := by rw [factor_6_4]; decide
      have factor_6_6 : (6 : ZMod 4015671661) ^ 112 = 1069871981 := by
        calc
          (6 : ZMod 4015671661) ^ 112 = (6 : ZMod 4015671661) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 56 * (6 : ZMod 4015671661) ^ 56 := by rw [pow_add]
          _ = 1069871981 := by rw [factor_6_5]; decide
      have factor_6_7 : (6 : ZMod 4015671661) ^ 225 = 152634412 := by
        calc
          (6 : ZMod 4015671661) ^ 225 = (6 : ZMod 4015671661) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 112 * (6 : ZMod 4015671661) ^ 112) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 152634412 := by rw [factor_6_6]; decide
      have factor_6_8 : (6 : ZMod 4015671661) ^ 450 = 3253203059 := by
        calc
          (6 : ZMod 4015671661) ^ 450 = (6 : ZMod 4015671661) ^ (225 + 225) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 225 * (6 : ZMod 4015671661) ^ 225 := by rw [pow_add]
          _ = 3253203059 := by rw [factor_6_7]; decide
      have factor_6_9 : (6 : ZMod 4015671661) ^ 901 = 3666015887 := by
        calc
          (6 : ZMod 4015671661) ^ 901 = (6 : ZMod 4015671661) ^ (450 + 450 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 450 * (6 : ZMod 4015671661) ^ 450) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3666015887 := by rw [factor_6_8]; decide
      have factor_6_10 : (6 : ZMod 4015671661) ^ 1802 = 626861949 := by
        calc
          (6 : ZMod 4015671661) ^ 1802 = (6 : ZMod 4015671661) ^ (901 + 901) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 901 * (6 : ZMod 4015671661) ^ 901 := by rw [pow_add]
          _ = 626861949 := by rw [factor_6_9]; decide
      have factor_6_11 : (6 : ZMod 4015671661) ^ 3604 = 3549001916 := by
        calc
          (6 : ZMod 4015671661) ^ 3604 = (6 : ZMod 4015671661) ^ (1802 + 1802) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 1802 * (6 : ZMod 4015671661) ^ 1802 := by rw [pow_add]
          _ = 3549001916 := by rw [factor_6_10]; decide
      have factor_6_12 : (6 : ZMod 4015671661) ^ 7208 = 2675268562 := by
        calc
          (6 : ZMod 4015671661) ^ 7208 = (6 : ZMod 4015671661) ^ (3604 + 3604) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 3604 * (6 : ZMod 4015671661) ^ 3604 := by rw [pow_add]
          _ = 2675268562 := by rw [factor_6_11]; decide
      have factor_6_13 : (6 : ZMod 4015671661) ^ 14417 = 1162443400 := by
        calc
          (6 : ZMod 4015671661) ^ 14417 = (6 : ZMod 4015671661) ^ (7208 + 7208 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 7208 * (6 : ZMod 4015671661) ^ 7208) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1162443400 := by rw [factor_6_12]; decide
      have factor_6_14 : (6 : ZMod 4015671661) ^ 28834 = 3826308276 := by
        calc
          (6 : ZMod 4015671661) ^ 28834 = (6 : ZMod 4015671661) ^ (14417 + 14417) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 14417 * (6 : ZMod 4015671661) ^ 14417 := by rw [pow_add]
          _ = 3826308276 := by rw [factor_6_13]; decide
      have factor_6_15 : (6 : ZMod 4015671661) ^ 57669 = 3992775347 := by
        calc
          (6 : ZMod 4015671661) ^ 57669 = (6 : ZMod 4015671661) ^ (28834 + 28834 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 28834 * (6 : ZMod 4015671661) ^ 28834) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3992775347 := by rw [factor_6_14]; decide
      have factor_6_16 : (6 : ZMod 4015671661) ^ 115339 = 3682031564 := by
        calc
          (6 : ZMod 4015671661) ^ 115339 = (6 : ZMod 4015671661) ^ (57669 + 57669 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 57669 * (6 : ZMod 4015671661) ^ 57669) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3682031564 := by rw [factor_6_15]; decide
      have factor_6_17 : (6 : ZMod 4015671661) ^ 230679 = 959160758 := by
        calc
          (6 : ZMod 4015671661) ^ 230679 = (6 : ZMod 4015671661) ^ (115339 + 115339 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 115339 * (6 : ZMod 4015671661) ^ 115339) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 959160758 := by rw [factor_6_16]; decide
      have factor_6_18 : (6 : ZMod 4015671661) ^ 461359 = 748803765 := by
        calc
          (6 : ZMod 4015671661) ^ 461359 = (6 : ZMod 4015671661) ^ (230679 + 230679 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 230679 * (6 : ZMod 4015671661) ^ 230679) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 748803765 := by rw [factor_6_17]; decide
      have factor_6_19 : (6 : ZMod 4015671661) ^ 922718 = 966183593 := by
        calc
          (6 : ZMod 4015671661) ^ 922718 = (6 : ZMod 4015671661) ^ (461359 + 461359) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 461359 * (6 : ZMod 4015671661) ^ 461359 := by rw [pow_add]
          _ = 966183593 := by rw [factor_6_18]; decide
      have factor_6_20 : (6 : ZMod 4015671661) ^ 1845437 = 1763600765 := by
        calc
          (6 : ZMod 4015671661) ^ 1845437 = (6 : ZMod 4015671661) ^ (922718 + 922718 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 922718 * (6 : ZMod 4015671661) ^ 922718) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1763600765 := by rw [factor_6_19]; decide
      have factor_6_21 : (6 : ZMod 4015671661) ^ 3690874 = 3652920163 := by
        calc
          (6 : ZMod 4015671661) ^ 3690874 = (6 : ZMod 4015671661) ^ (1845437 + 1845437) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 1845437 * (6 : ZMod 4015671661) ^ 1845437 := by rw [pow_add]
          _ = 3652920163 := by rw [factor_6_20]; decide
      have factor_6_22 : (6 : ZMod 4015671661) ^ 7381749 = 820292442 := by
        calc
          (6 : ZMod 4015671661) ^ 7381749 = (6 : ZMod 4015671661) ^ (3690874 + 3690874 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 3690874 * (6 : ZMod 4015671661) ^ 3690874) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 820292442 := by rw [factor_6_21]; decide
      have factor_6_23 : (6 : ZMod 4015671661) ^ 14763498 = 1241067761 := by
        calc
          (6 : ZMod 4015671661) ^ 14763498 = (6 : ZMod 4015671661) ^ (7381749 + 7381749) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 7381749 * (6 : ZMod 4015671661) ^ 7381749 := by rw [pow_add]
          _ = 1241067761 := by rw [factor_6_22]; decide
      have factor_6_24 : (6 : ZMod 4015671661) ^ 29526997 = 1574053188 := by
        calc
          (6 : ZMod 4015671661) ^ 29526997 = (6 : ZMod 4015671661) ^ (14763498 + 14763498 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 14763498 * (6 : ZMod 4015671661) ^ 14763498) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1574053188 := by rw [factor_6_23]; decide
      have factor_6_25 : (6 : ZMod 4015671661) ^ 59053995 = 3159958457 := by
        calc
          (6 : ZMod 4015671661) ^ 59053995 = (6 : ZMod 4015671661) ^ (29526997 + 29526997 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 29526997 * (6 : ZMod 4015671661) ^ 29526997) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3159958457 := by rw [factor_6_24]; decide
      have factor_6_26 : (6 : ZMod 4015671661) ^ 118107990 = 1450984444 := by
        calc
          (6 : ZMod 4015671661) ^ 118107990 = (6 : ZMod 4015671661) ^ (59053995 + 59053995) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 59053995 * (6 : ZMod 4015671661) ^ 59053995 := by rw [pow_add]
          _ = 1450984444 := by rw [factor_6_25]; decide
      have factor_6_27 : (6 : ZMod 4015671661) ^ 236215980 = 2136636676 := by
        calc
          (6 : ZMod 4015671661) ^ 236215980 = (6 : ZMod 4015671661) ^ (118107990 + 118107990) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 118107990 * (6 : ZMod 4015671661) ^ 118107990 := by rw [pow_add]
          _ = 2136636676 := by rw [factor_6_26]; decide
      change (6 : ZMod 4015671661) ^ 236215980 ≠ 1
      rw [factor_6_27]
      decide
    ·
      have factor_7_0 : (6 : ZMod 4015671661) ^ 1 = 6 := by norm_num
      have factor_7_1 : (6 : ZMod 4015671661) ^ 3 = 216 := by
        calc
          (6 : ZMod 4015671661) ^ 3 = (6 : ZMod 4015671661) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 1 * (6 : ZMod 4015671661) ^ 1) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_7_0]; decide
      have factor_7_2 : (6 : ZMod 4015671661) ^ 6 = 46656 := by
        calc
          (6 : ZMod 4015671661) ^ 6 = (6 : ZMod 4015671661) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 3 * (6 : ZMod 4015671661) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [factor_7_1]; decide
      have factor_7_3 : (6 : ZMod 4015671661) ^ 12 = 2176782336 := by
        calc
          (6 : ZMod 4015671661) ^ 12 = (6 : ZMod 4015671661) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 6 * (6 : ZMod 4015671661) ^ 6 := by rw [pow_add]
          _ = 2176782336 := by rw [factor_7_2]; decide
      have factor_7_4 : (6 : ZMod 4015671661) ^ 25 = 2397669678 := by
        calc
          (6 : ZMod 4015671661) ^ 25 = (6 : ZMod 4015671661) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 12 * (6 : ZMod 4015671661) ^ 12) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2397669678 := by rw [factor_7_3]; decide
      have factor_7_5 : (6 : ZMod 4015671661) ^ 50 = 48173245 := by
        calc
          (6 : ZMod 4015671661) ^ 50 = (6 : ZMod 4015671661) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 25 * (6 : ZMod 4015671661) ^ 25 := by rw [pow_add]
          _ = 48173245 := by rw [factor_7_4]; decide
      have factor_7_6 : (6 : ZMod 4015671661) ^ 100 = 865266464 := by
        calc
          (6 : ZMod 4015671661) ^ 100 = (6 : ZMod 4015671661) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 50 * (6 : ZMod 4015671661) ^ 50 := by rw [pow_add]
          _ = 865266464 := by rw [factor_7_5]; decide
      have factor_7_7 : (6 : ZMod 4015671661) ^ 201 = 448113917 := by
        calc
          (6 : ZMod 4015671661) ^ 201 = (6 : ZMod 4015671661) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 100 * (6 : ZMod 4015671661) ^ 100) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 448113917 := by rw [factor_7_6]; decide
      have factor_7_8 : (6 : ZMod 4015671661) ^ 403 = 2520269497 := by
        calc
          (6 : ZMod 4015671661) ^ 403 = (6 : ZMod 4015671661) ^ (201 + 201 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 201 * (6 : ZMod 4015671661) ^ 201) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2520269497 := by rw [factor_7_7]; decide
      have factor_7_9 : (6 : ZMod 4015671661) ^ 806 = 2027251898 := by
        calc
          (6 : ZMod 4015671661) ^ 806 = (6 : ZMod 4015671661) ^ (403 + 403) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 403 * (6 : ZMod 4015671661) ^ 403 := by rw [pow_add]
          _ = 2027251898 := by rw [factor_7_8]; decide
      have factor_7_10 : (6 : ZMod 4015671661) ^ 1612 = 3464726944 := by
        calc
          (6 : ZMod 4015671661) ^ 1612 = (6 : ZMod 4015671661) ^ (806 + 806) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 806 * (6 : ZMod 4015671661) ^ 806 := by rw [pow_add]
          _ = 3464726944 := by rw [factor_7_9]; decide
      have factor_7_11 : (6 : ZMod 4015671661) ^ 3224 = 2059868680 := by
        calc
          (6 : ZMod 4015671661) ^ 3224 = (6 : ZMod 4015671661) ^ (1612 + 1612) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 1612 * (6 : ZMod 4015671661) ^ 1612 := by rw [pow_add]
          _ = 2059868680 := by rw [factor_7_10]; decide
      have factor_7_12 : (6 : ZMod 4015671661) ^ 6449 = 2360578635 := by
        calc
          (6 : ZMod 4015671661) ^ 6449 = (6 : ZMod 4015671661) ^ (3224 + 3224 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 3224 * (6 : ZMod 4015671661) ^ 3224) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2360578635 := by rw [factor_7_11]; decide
      have factor_7_13 : (6 : ZMod 4015671661) ^ 12899 = 3794303234 := by
        calc
          (6 : ZMod 4015671661) ^ 12899 = (6 : ZMod 4015671661) ^ (6449 + 6449 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 6449 * (6 : ZMod 4015671661) ^ 6449) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3794303234 := by rw [factor_7_12]; decide
      have factor_7_14 : (6 : ZMod 4015671661) ^ 25799 = 1858114230 := by
        calc
          (6 : ZMod 4015671661) ^ 25799 = (6 : ZMod 4015671661) ^ (12899 + 12899 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 12899 * (6 : ZMod 4015671661) ^ 12899) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1858114230 := by rw [factor_7_13]; decide
      have factor_7_15 : (6 : ZMod 4015671661) ^ 51599 = 3428267561 := by
        calc
          (6 : ZMod 4015671661) ^ 51599 = (6 : ZMod 4015671661) ^ (25799 + 25799 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 25799 * (6 : ZMod 4015671661) ^ 25799) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3428267561 := by rw [factor_7_14]; decide
      have factor_7_16 : (6 : ZMod 4015671661) ^ 103198 = 979130750 := by
        calc
          (6 : ZMod 4015671661) ^ 103198 = (6 : ZMod 4015671661) ^ (51599 + 51599) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 51599 * (6 : ZMod 4015671661) ^ 51599 := by rw [pow_add]
          _ = 979130750 := by rw [factor_7_15]; decide
      have factor_7_17 : (6 : ZMod 4015671661) ^ 206397 = 3158572515 := by
        calc
          (6 : ZMod 4015671661) ^ 206397 = (6 : ZMod 4015671661) ^ (103198 + 103198 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 103198 * (6 : ZMod 4015671661) ^ 103198) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3158572515 := by rw [factor_7_16]; decide
      have factor_7_18 : (6 : ZMod 4015671661) ^ 412795 = 2445109591 := by
        calc
          (6 : ZMod 4015671661) ^ 412795 = (6 : ZMod 4015671661) ^ (206397 + 206397 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 206397 * (6 : ZMod 4015671661) ^ 206397) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2445109591 := by rw [factor_7_17]; decide
      have factor_7_19 : (6 : ZMod 4015671661) ^ 825590 = 2157726454 := by
        calc
          (6 : ZMod 4015671661) ^ 825590 = (6 : ZMod 4015671661) ^ (412795 + 412795) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 412795 * (6 : ZMod 4015671661) ^ 412795 := by rw [pow_add]
          _ = 2157726454 := by rw [factor_7_18]; decide
      have factor_7_20 : (6 : ZMod 4015671661) ^ 1651180 = 962276818 := by
        calc
          (6 : ZMod 4015671661) ^ 1651180 = (6 : ZMod 4015671661) ^ (825590 + 825590) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 825590 * (6 : ZMod 4015671661) ^ 825590 := by rw [pow_add]
          _ = 962276818 := by rw [factor_7_19]; decide
      have factor_7_21 : (6 : ZMod 4015671661) ^ 3302361 = 3930310683 := by
        calc
          (6 : ZMod 4015671661) ^ 3302361 = (6 : ZMod 4015671661) ^ (1651180 + 1651180 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 1651180 * (6 : ZMod 4015671661) ^ 1651180) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3930310683 := by rw [factor_7_20]; decide
      have factor_7_22 : (6 : ZMod 4015671661) ^ 6604723 = 606942414 := by
        calc
          (6 : ZMod 4015671661) ^ 6604723 = (6 : ZMod 4015671661) ^ (3302361 + 3302361 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 3302361 * (6 : ZMod 4015671661) ^ 3302361) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 606942414 := by rw [factor_7_21]; decide
      have factor_7_23 : (6 : ZMod 4015671661) ^ 13209446 = 417171114 := by
        calc
          (6 : ZMod 4015671661) ^ 13209446 = (6 : ZMod 4015671661) ^ (6604723 + 6604723) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 6604723 * (6 : ZMod 4015671661) ^ 6604723 := by rw [pow_add]
          _ = 417171114 := by rw [factor_7_22]; decide
      have factor_7_24 : (6 : ZMod 4015671661) ^ 26418892 = 1733222117 := by
        calc
          (6 : ZMod 4015671661) ^ 26418892 = (6 : ZMod 4015671661) ^ (13209446 + 13209446) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 13209446 * (6 : ZMod 4015671661) ^ 13209446 := by rw [pow_add]
          _ = 1733222117 := by rw [factor_7_23]; decide
      have factor_7_25 : (6 : ZMod 4015671661) ^ 52837785 = 3088022588 := by
        calc
          (6 : ZMod 4015671661) ^ 52837785 = (6 : ZMod 4015671661) ^ (26418892 + 26418892 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 26418892 * (6 : ZMod 4015671661) ^ 26418892) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3088022588 := by rw [factor_7_24]; decide
      have factor_7_26 : (6 : ZMod 4015671661) ^ 105675570 = 1733343153 := by
        calc
          (6 : ZMod 4015671661) ^ 105675570 = (6 : ZMod 4015671661) ^ (52837785 + 52837785) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 52837785 * (6 : ZMod 4015671661) ^ 52837785 := by rw [pow_add]
          _ = 1733343153 := by rw [factor_7_25]; decide
      have factor_7_27 : (6 : ZMod 4015671661) ^ 211351140 = 916633346 := by
        calc
          (6 : ZMod 4015671661) ^ 211351140 = (6 : ZMod 4015671661) ^ (105675570 + 105675570) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 105675570 * (6 : ZMod 4015671661) ^ 105675570 := by rw [pow_add]
          _ = 916633346 := by rw [factor_7_26]; decide
      change (6 : ZMod 4015671661) ^ 211351140 ≠ 1
      rw [factor_7_27]
      decide
    ·
      have factor_8_0 : (6 : ZMod 4015671661) ^ 1 = 6 := by norm_num
      have factor_8_1 : (6 : ZMod 4015671661) ^ 2 = 36 := by
        calc
          (6 : ZMod 4015671661) ^ 2 = (6 : ZMod 4015671661) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 1 * (6 : ZMod 4015671661) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_8_0]; decide
      have factor_8_2 : (6 : ZMod 4015671661) ^ 5 = 7776 := by
        calc
          (6 : ZMod 4015671661) ^ 5 = (6 : ZMod 4015671661) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 2 * (6 : ZMod 4015671661) ^ 2) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_8_1]; decide
      have factor_8_3 : (6 : ZMod 4015671661) ^ 10 = 60466176 := by
        calc
          (6 : ZMod 4015671661) ^ 10 = (6 : ZMod 4015671661) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 5 * (6 : ZMod 4015671661) ^ 5 := by rw [pow_add]
          _ = 60466176 := by rw [factor_8_2]; decide
      have factor_8_4 : (6 : ZMod 4015671661) ^ 20 = 1831528984 := by
        calc
          (6 : ZMod 4015671661) ^ 20 = (6 : ZMod 4015671661) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 10 * (6 : ZMod 4015671661) ^ 10 := by rw [pow_add]
          _ = 1831528984 := by rw [factor_8_3]; decide
      have factor_8_5 : (6 : ZMod 4015671661) ^ 41 = 1112040292 := by
        calc
          (6 : ZMod 4015671661) ^ 41 = (6 : ZMod 4015671661) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 20 * (6 : ZMod 4015671661) ^ 20) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1112040292 := by rw [factor_8_4]; decide
      have factor_8_6 : (6 : ZMod 4015671661) ^ 83 = 2009501944 := by
        calc
          (6 : ZMod 4015671661) ^ 83 = (6 : ZMod 4015671661) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 41 * (6 : ZMod 4015671661) ^ 41) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2009501944 := by rw [factor_8_5]; decide
      have factor_8_7 : (6 : ZMod 4015671661) ^ 166 = 101159216 := by
        calc
          (6 : ZMod 4015671661) ^ 166 = (6 : ZMod 4015671661) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 83 * (6 : ZMod 4015671661) ^ 83 := by rw [pow_add]
          _ = 101159216 := by rw [factor_8_6]; decide
      have factor_8_8 : (6 : ZMod 4015671661) ^ 333 = 137003900 := by
        calc
          (6 : ZMod 4015671661) ^ 333 = (6 : ZMod 4015671661) ^ (166 + 166 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 166 * (6 : ZMod 4015671661) ^ 166) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 137003900 := by rw [factor_8_7]; decide
      have factor_8_9 : (6 : ZMod 4015671661) ^ 666 = 74677156 := by
        calc
          (6 : ZMod 4015671661) ^ 666 = (6 : ZMod 4015671661) ^ (333 + 333) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 333 * (6 : ZMod 4015671661) ^ 333 := by rw [pow_add]
          _ = 74677156 := by rw [factor_8_8]; decide
      have factor_8_10 : (6 : ZMod 4015671661) ^ 1332 = 1953811128 := by
        calc
          (6 : ZMod 4015671661) ^ 1332 = (6 : ZMod 4015671661) ^ (666 + 666) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 666 * (6 : ZMod 4015671661) ^ 666 := by rw [pow_add]
          _ = 1953811128 := by rw [factor_8_9]; decide
      have factor_8_11 : (6 : ZMod 4015671661) ^ 2664 = 1015319232 := by
        calc
          (6 : ZMod 4015671661) ^ 2664 = (6 : ZMod 4015671661) ^ (1332 + 1332) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 1332 * (6 : ZMod 4015671661) ^ 1332 := by rw [pow_add]
          _ = 1015319232 := by rw [factor_8_10]; decide
      have factor_8_12 : (6 : ZMod 4015671661) ^ 5328 = 3484905697 := by
        calc
          (6 : ZMod 4015671661) ^ 5328 = (6 : ZMod 4015671661) ^ (2664 + 2664) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 2664 * (6 : ZMod 4015671661) ^ 2664 := by rw [pow_add]
          _ = 3484905697 := by rw [factor_8_11]; decide
      have factor_8_13 : (6 : ZMod 4015671661) ^ 10656 = 2244024504 := by
        calc
          (6 : ZMod 4015671661) ^ 10656 = (6 : ZMod 4015671661) ^ (5328 + 5328) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 5328 * (6 : ZMod 4015671661) ^ 5328 := by rw [pow_add]
          _ = 2244024504 := by rw [factor_8_12]; decide
      have factor_8_14 : (6 : ZMod 4015671661) ^ 21312 = 200267142 := by
        calc
          (6 : ZMod 4015671661) ^ 21312 = (6 : ZMod 4015671661) ^ (10656 + 10656) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 10656 * (6 : ZMod 4015671661) ^ 10656 := by rw [pow_add]
          _ = 200267142 := by rw [factor_8_13]; decide
      have factor_8_15 : (6 : ZMod 4015671661) ^ 42625 = 3175294096 := by
        calc
          (6 : ZMod 4015671661) ^ 42625 = (6 : ZMod 4015671661) ^ (21312 + 21312 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 21312 * (6 : ZMod 4015671661) ^ 21312) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3175294096 := by rw [factor_8_14]; decide
      have factor_8_16 : (6 : ZMod 4015671661) ^ 85251 = 766082425 := by
        calc
          (6 : ZMod 4015671661) ^ 85251 = (6 : ZMod 4015671661) ^ (42625 + 42625 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 42625 * (6 : ZMod 4015671661) ^ 42625) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 766082425 := by rw [factor_8_15]; decide
      have factor_8_17 : (6 : ZMod 4015671661) ^ 170502 = 373844150 := by
        calc
          (6 : ZMod 4015671661) ^ 170502 = (6 : ZMod 4015671661) ^ (85251 + 85251) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 85251 * (6 : ZMod 4015671661) ^ 85251 := by rw [pow_add]
          _ = 373844150 := by rw [factor_8_16]; decide
      have factor_8_18 : (6 : ZMod 4015671661) ^ 341004 = 3772922356 := by
        calc
          (6 : ZMod 4015671661) ^ 341004 = (6 : ZMod 4015671661) ^ (170502 + 170502) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 170502 * (6 : ZMod 4015671661) ^ 170502 := by rw [pow_add]
          _ = 3772922356 := by rw [factor_8_17]; decide
      have factor_8_19 : (6 : ZMod 4015671661) ^ 682009 = 1268419809 := by
        calc
          (6 : ZMod 4015671661) ^ 682009 = (6 : ZMod 4015671661) ^ (341004 + 341004 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 341004 * (6 : ZMod 4015671661) ^ 341004) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1268419809 := by rw [factor_8_18]; decide
      have factor_8_20 : (6 : ZMod 4015671661) ^ 1364018 = 2018227201 := by
        calc
          (6 : ZMod 4015671661) ^ 1364018 = (6 : ZMod 4015671661) ^ (682009 + 682009) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 682009 * (6 : ZMod 4015671661) ^ 682009 := by rw [pow_add]
          _ = 2018227201 := by rw [factor_8_19]; decide
      have factor_8_21 : (6 : ZMod 4015671661) ^ 2728037 = 1042931373 := by
        calc
          (6 : ZMod 4015671661) ^ 2728037 = (6 : ZMod 4015671661) ^ (1364018 + 1364018 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 1364018 * (6 : ZMod 4015671661) ^ 1364018) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 1042931373 := by rw [factor_8_20]; decide
      have factor_8_22 : (6 : ZMod 4015671661) ^ 5456075 = 3888358764 := by
        calc
          (6 : ZMod 4015671661) ^ 5456075 = (6 : ZMod 4015671661) ^ (2728037 + 2728037 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 2728037 * (6 : ZMod 4015671661) ^ 2728037) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 3888358764 := by rw [factor_8_21]; decide
      have factor_8_23 : (6 : ZMod 4015671661) ^ 10912151 = 2545217518 := by
        calc
          (6 : ZMod 4015671661) ^ 10912151 = (6 : ZMod 4015671661) ^ (5456075 + 5456075 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 5456075 * (6 : ZMod 4015671661) ^ 5456075) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2545217518 := by rw [factor_8_22]; decide
      have factor_8_24 : (6 : ZMod 4015671661) ^ 21824302 = 585503521 := by
        calc
          (6 : ZMod 4015671661) ^ 21824302 = (6 : ZMod 4015671661) ^ (10912151 + 10912151) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 10912151 * (6 : ZMod 4015671661) ^ 10912151 := by rw [pow_add]
          _ = 585503521 := by rw [factor_8_23]; decide
      have factor_8_25 : (6 : ZMod 4015671661) ^ 43648605 = 2777543201 := by
        calc
          (6 : ZMod 4015671661) ^ 43648605 = (6 : ZMod 4015671661) ^ (21824302 + 21824302 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = ((6 : ZMod 4015671661) ^ 21824302 * (6 : ZMod 4015671661) ^ 21824302) * (6 : ZMod 4015671661) := by rw [pow_succ, pow_add]
          _ = 2777543201 := by rw [factor_8_24]; decide
      have factor_8_26 : (6 : ZMod 4015671661) ^ 87297210 = 3176812564 := by
        calc
          (6 : ZMod 4015671661) ^ 87297210 = (6 : ZMod 4015671661) ^ (43648605 + 43648605) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 43648605 * (6 : ZMod 4015671661) ^ 43648605 := by rw [pow_add]
          _ = 3176812564 := by rw [factor_8_25]; decide
      have factor_8_27 : (6 : ZMod 4015671661) ^ 174594420 = 3514029758 := by
        calc
          (6 : ZMod 4015671661) ^ 174594420 = (6 : ZMod 4015671661) ^ (87297210 + 87297210) :=
            congrArg (fun n : ℕ => (6 : ZMod 4015671661) ^ n) (by norm_num)
          _ = (6 : ZMod 4015671661) ^ 87297210 * (6 : ZMod 4015671661) ^ 87297210 := by rw [pow_add]
          _ = 3514029758 := by rw [factor_8_26]; decide
      change (6 : ZMod 4015671661) ^ 174594420 ≠ 1
      rw [factor_8_27]
      decide

#print axioms prime_lucas_4015671661

end TotientTailPeriodKiller
end Erdos249257
