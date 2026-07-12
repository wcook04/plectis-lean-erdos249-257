import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime126278983

/-! A bounded Lucas certificate for one t=27 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_3030695593 : Nat.Prime 3030695593 := by
  apply lucas_primality 3030695593 (5 : ZMod 3030695593)
  ·
      have fermat_0 : (5 : ZMod 3030695593) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 3030695593) ^ 2 = 25 := by
        calc
          (5 : ZMod 3030695593) ^ 2 = (5 : ZMod 3030695593) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 1 * (5 : ZMod 3030695593) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 3030695593) ^ 5 = 3125 := by
        calc
          (5 : ZMod 3030695593) ^ 5 = (5 : ZMod 3030695593) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 2 * (5 : ZMod 3030695593) ^ 2) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 3030695593) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 3030695593) ^ 11 = (5 : ZMod 3030695593) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 5 * (5 : ZMod 3030695593) ^ 5) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 3030695593) ^ 22 = 1212609978 := by
        calc
          (5 : ZMod 3030695593) ^ 22 = (5 : ZMod 3030695593) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 11 * (5 : ZMod 3030695593) ^ 11 := by rw [pow_add]
          _ = 1212609978 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 3030695593) ^ 45 = 491611353 := by
        calc
          (5 : ZMod 3030695593) ^ 45 = (5 : ZMod 3030695593) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 22 * (5 : ZMod 3030695593) ^ 22) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 491611353 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 3030695593) ^ 90 = 2477205868 := by
        calc
          (5 : ZMod 3030695593) ^ 90 = (5 : ZMod 3030695593) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 45 * (5 : ZMod 3030695593) ^ 45 := by rw [pow_add]
          _ = 2477205868 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 3030695593) ^ 180 = 446208083 := by
        calc
          (5 : ZMod 3030695593) ^ 180 = (5 : ZMod 3030695593) ^ (90 + 90) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 90 * (5 : ZMod 3030695593) ^ 90 := by rw [pow_add]
          _ = 446208083 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 3030695593) ^ 361 = 1390270670 := by
        calc
          (5 : ZMod 3030695593) ^ 361 = (5 : ZMod 3030695593) ^ (180 + 180 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 180 * (5 : ZMod 3030695593) ^ 180) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 1390270670 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 3030695593) ^ 722 = 2853014719 := by
        calc
          (5 : ZMod 3030695593) ^ 722 = (5 : ZMod 3030695593) ^ (361 + 361) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 361 * (5 : ZMod 3030695593) ^ 361 := by rw [pow_add]
          _ = 2853014719 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 3030695593) ^ 1445 = 287501742 := by
        calc
          (5 : ZMod 3030695593) ^ 1445 = (5 : ZMod 3030695593) ^ (722 + 722 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 722 * (5 : ZMod 3030695593) ^ 722) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 287501742 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 3030695593) ^ 2890 = 2725427677 := by
        calc
          (5 : ZMod 3030695593) ^ 2890 = (5 : ZMod 3030695593) ^ (1445 + 1445) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 1445 * (5 : ZMod 3030695593) ^ 1445 := by rw [pow_add]
          _ = 2725427677 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 3030695593) ^ 5780 = 2661693003 := by
        calc
          (5 : ZMod 3030695593) ^ 5780 = (5 : ZMod 3030695593) ^ (2890 + 2890) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 2890 * (5 : ZMod 3030695593) ^ 2890 := by rw [pow_add]
          _ = 2661693003 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 3030695593) ^ 11561 = 2269307214 := by
        calc
          (5 : ZMod 3030695593) ^ 11561 = (5 : ZMod 3030695593) ^ (5780 + 5780 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 5780 * (5 : ZMod 3030695593) ^ 5780) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2269307214 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 3030695593) ^ 23122 = 1451484310 := by
        calc
          (5 : ZMod 3030695593) ^ 23122 = (5 : ZMod 3030695593) ^ (11561 + 11561) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 11561 * (5 : ZMod 3030695593) ^ 11561 := by rw [pow_add]
          _ = 1451484310 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 3030695593) ^ 46244 = 709459999 := by
        calc
          (5 : ZMod 3030695593) ^ 46244 = (5 : ZMod 3030695593) ^ (23122 + 23122) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 23122 * (5 : ZMod 3030695593) ^ 23122 := by rw [pow_add]
          _ = 709459999 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 3030695593) ^ 92489 = 16462800 := by
        calc
          (5 : ZMod 3030695593) ^ 92489 = (5 : ZMod 3030695593) ^ (46244 + 46244 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 46244 * (5 : ZMod 3030695593) ^ 46244) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 16462800 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 3030695593) ^ 184978 = 799740382 := by
        calc
          (5 : ZMod 3030695593) ^ 184978 = (5 : ZMod 3030695593) ^ (92489 + 92489) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 92489 * (5 : ZMod 3030695593) ^ 92489 := by rw [pow_add]
          _ = 799740382 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 3030695593) ^ 369957 = 2809585795 := by
        calc
          (5 : ZMod 3030695593) ^ 369957 = (5 : ZMod 3030695593) ^ (184978 + 184978 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 184978 * (5 : ZMod 3030695593) ^ 184978) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2809585795 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 3030695593) ^ 739915 = 2327507492 := by
        calc
          (5 : ZMod 3030695593) ^ 739915 = (5 : ZMod 3030695593) ^ (369957 + 369957 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 369957 * (5 : ZMod 3030695593) ^ 369957) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2327507492 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 3030695593) ^ 1479831 = 2050913426 := by
        calc
          (5 : ZMod 3030695593) ^ 1479831 = (5 : ZMod 3030695593) ^ (739915 + 739915 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 739915 * (5 : ZMod 3030695593) ^ 739915) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2050913426 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 3030695593) ^ 2959663 = 997659711 := by
        calc
          (5 : ZMod 3030695593) ^ 2959663 = (5 : ZMod 3030695593) ^ (1479831 + 1479831 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 1479831 * (5 : ZMod 3030695593) ^ 1479831) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 997659711 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 3030695593) ^ 5919327 = 2259010718 := by
        calc
          (5 : ZMod 3030695593) ^ 5919327 = (5 : ZMod 3030695593) ^ (2959663 + 2959663 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 2959663 * (5 : ZMod 3030695593) ^ 2959663) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2259010718 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 3030695593) ^ 11838654 = 34425177 := by
        calc
          (5 : ZMod 3030695593) ^ 11838654 = (5 : ZMod 3030695593) ^ (5919327 + 5919327) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 5919327 * (5 : ZMod 3030695593) ^ 5919327 := by rw [pow_add]
          _ = 34425177 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 3030695593) ^ 23677309 = 2599448288 := by
        calc
          (5 : ZMod 3030695593) ^ 23677309 = (5 : ZMod 3030695593) ^ (11838654 + 11838654 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 11838654 * (5 : ZMod 3030695593) ^ 11838654) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2599448288 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 3030695593) ^ 47354618 = 544623468 := by
        calc
          (5 : ZMod 3030695593) ^ 47354618 = (5 : ZMod 3030695593) ^ (23677309 + 23677309) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 23677309 * (5 : ZMod 3030695593) ^ 23677309 := by rw [pow_add]
          _ = 544623468 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 3030695593) ^ 94709237 = 2513238199 := by
        calc
          (5 : ZMod 3030695593) ^ 94709237 = (5 : ZMod 3030695593) ^ (47354618 + 47354618 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 47354618 * (5 : ZMod 3030695593) ^ 47354618) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2513238199 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 3030695593) ^ 189418474 = 1968507691 := by
        calc
          (5 : ZMod 3030695593) ^ 189418474 = (5 : ZMod 3030695593) ^ (94709237 + 94709237) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 94709237 * (5 : ZMod 3030695593) ^ 94709237 := by rw [pow_add]
          _ = 1968507691 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 3030695593) ^ 378836949 = 1315939556 := by
        calc
          (5 : ZMod 3030695593) ^ 378836949 = (5 : ZMod 3030695593) ^ (189418474 + 189418474 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 189418474 * (5 : ZMod 3030695593) ^ 189418474) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 1315939556 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 3030695593) ^ 757673898 = 1140707263 := by
        calc
          (5 : ZMod 3030695593) ^ 757673898 = (5 : ZMod 3030695593) ^ (378836949 + 378836949) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 378836949 * (5 : ZMod 3030695593) ^ 378836949 := by rw [pow_add]
          _ = 1140707263 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 3030695593) ^ 1515347796 = 3030695592 := by
        calc
          (5 : ZMod 3030695593) ^ 1515347796 = (5 : ZMod 3030695593) ^ (757673898 + 757673898) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 757673898 * (5 : ZMod 3030695593) ^ 757673898 := by rw [pow_add]
          _ = 3030695592 := by rw [fermat_29]; decide
      have fermat_31 : (5 : ZMod 3030695593) ^ 3030695592 = 1 := by
        calc
          (5 : ZMod 3030695593) ^ 3030695592 = (5 : ZMod 3030695593) ^ (1515347796 + 1515347796) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 1515347796 * (5 : ZMod 3030695593) ^ 1515347796 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (126278983, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (126278983, 1)] : List FactorBlock).map factorBlockValue).prod = 3030695593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_126278983) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 3030695593) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 3030695593) ^ 2 = 25 := by
        calc
          (5 : ZMod 3030695593) ^ 2 = (5 : ZMod 3030695593) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 1 * (5 : ZMod 3030695593) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 3030695593) ^ 5 = 3125 := by
        calc
          (5 : ZMod 3030695593) ^ 5 = (5 : ZMod 3030695593) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 2 * (5 : ZMod 3030695593) ^ 2) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 3030695593) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 3030695593) ^ 11 = (5 : ZMod 3030695593) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 5 * (5 : ZMod 3030695593) ^ 5) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 3030695593) ^ 22 = 1212609978 := by
        calc
          (5 : ZMod 3030695593) ^ 22 = (5 : ZMod 3030695593) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 11 * (5 : ZMod 3030695593) ^ 11 := by rw [pow_add]
          _ = 1212609978 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 3030695593) ^ 45 = 491611353 := by
        calc
          (5 : ZMod 3030695593) ^ 45 = (5 : ZMod 3030695593) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 22 * (5 : ZMod 3030695593) ^ 22) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 491611353 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 3030695593) ^ 90 = 2477205868 := by
        calc
          (5 : ZMod 3030695593) ^ 90 = (5 : ZMod 3030695593) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 45 * (5 : ZMod 3030695593) ^ 45 := by rw [pow_add]
          _ = 2477205868 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 3030695593) ^ 180 = 446208083 := by
        calc
          (5 : ZMod 3030695593) ^ 180 = (5 : ZMod 3030695593) ^ (90 + 90) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 90 * (5 : ZMod 3030695593) ^ 90 := by rw [pow_add]
          _ = 446208083 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 3030695593) ^ 361 = 1390270670 := by
        calc
          (5 : ZMod 3030695593) ^ 361 = (5 : ZMod 3030695593) ^ (180 + 180 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 180 * (5 : ZMod 3030695593) ^ 180) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 1390270670 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 3030695593) ^ 722 = 2853014719 := by
        calc
          (5 : ZMod 3030695593) ^ 722 = (5 : ZMod 3030695593) ^ (361 + 361) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 361 * (5 : ZMod 3030695593) ^ 361 := by rw [pow_add]
          _ = 2853014719 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 3030695593) ^ 1445 = 287501742 := by
        calc
          (5 : ZMod 3030695593) ^ 1445 = (5 : ZMod 3030695593) ^ (722 + 722 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 722 * (5 : ZMod 3030695593) ^ 722) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 287501742 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 3030695593) ^ 2890 = 2725427677 := by
        calc
          (5 : ZMod 3030695593) ^ 2890 = (5 : ZMod 3030695593) ^ (1445 + 1445) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 1445 * (5 : ZMod 3030695593) ^ 1445 := by rw [pow_add]
          _ = 2725427677 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 3030695593) ^ 5780 = 2661693003 := by
        calc
          (5 : ZMod 3030695593) ^ 5780 = (5 : ZMod 3030695593) ^ (2890 + 2890) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 2890 * (5 : ZMod 3030695593) ^ 2890 := by rw [pow_add]
          _ = 2661693003 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 3030695593) ^ 11561 = 2269307214 := by
        calc
          (5 : ZMod 3030695593) ^ 11561 = (5 : ZMod 3030695593) ^ (5780 + 5780 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 5780 * (5 : ZMod 3030695593) ^ 5780) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2269307214 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 3030695593) ^ 23122 = 1451484310 := by
        calc
          (5 : ZMod 3030695593) ^ 23122 = (5 : ZMod 3030695593) ^ (11561 + 11561) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 11561 * (5 : ZMod 3030695593) ^ 11561 := by rw [pow_add]
          _ = 1451484310 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 3030695593) ^ 46244 = 709459999 := by
        calc
          (5 : ZMod 3030695593) ^ 46244 = (5 : ZMod 3030695593) ^ (23122 + 23122) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 23122 * (5 : ZMod 3030695593) ^ 23122 := by rw [pow_add]
          _ = 709459999 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 3030695593) ^ 92489 = 16462800 := by
        calc
          (5 : ZMod 3030695593) ^ 92489 = (5 : ZMod 3030695593) ^ (46244 + 46244 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 46244 * (5 : ZMod 3030695593) ^ 46244) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 16462800 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 3030695593) ^ 184978 = 799740382 := by
        calc
          (5 : ZMod 3030695593) ^ 184978 = (5 : ZMod 3030695593) ^ (92489 + 92489) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 92489 * (5 : ZMod 3030695593) ^ 92489 := by rw [pow_add]
          _ = 799740382 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 3030695593) ^ 369957 = 2809585795 := by
        calc
          (5 : ZMod 3030695593) ^ 369957 = (5 : ZMod 3030695593) ^ (184978 + 184978 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 184978 * (5 : ZMod 3030695593) ^ 184978) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2809585795 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 3030695593) ^ 739915 = 2327507492 := by
        calc
          (5 : ZMod 3030695593) ^ 739915 = (5 : ZMod 3030695593) ^ (369957 + 369957 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 369957 * (5 : ZMod 3030695593) ^ 369957) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2327507492 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 3030695593) ^ 1479831 = 2050913426 := by
        calc
          (5 : ZMod 3030695593) ^ 1479831 = (5 : ZMod 3030695593) ^ (739915 + 739915 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 739915 * (5 : ZMod 3030695593) ^ 739915) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2050913426 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 3030695593) ^ 2959663 = 997659711 := by
        calc
          (5 : ZMod 3030695593) ^ 2959663 = (5 : ZMod 3030695593) ^ (1479831 + 1479831 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 1479831 * (5 : ZMod 3030695593) ^ 1479831) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 997659711 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 3030695593) ^ 5919327 = 2259010718 := by
        calc
          (5 : ZMod 3030695593) ^ 5919327 = (5 : ZMod 3030695593) ^ (2959663 + 2959663 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 2959663 * (5 : ZMod 3030695593) ^ 2959663) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2259010718 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 3030695593) ^ 11838654 = 34425177 := by
        calc
          (5 : ZMod 3030695593) ^ 11838654 = (5 : ZMod 3030695593) ^ (5919327 + 5919327) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 5919327 * (5 : ZMod 3030695593) ^ 5919327 := by rw [pow_add]
          _ = 34425177 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 3030695593) ^ 23677309 = 2599448288 := by
        calc
          (5 : ZMod 3030695593) ^ 23677309 = (5 : ZMod 3030695593) ^ (11838654 + 11838654 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 11838654 * (5 : ZMod 3030695593) ^ 11838654) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2599448288 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 3030695593) ^ 47354618 = 544623468 := by
        calc
          (5 : ZMod 3030695593) ^ 47354618 = (5 : ZMod 3030695593) ^ (23677309 + 23677309) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 23677309 * (5 : ZMod 3030695593) ^ 23677309 := by rw [pow_add]
          _ = 544623468 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 3030695593) ^ 94709237 = 2513238199 := by
        calc
          (5 : ZMod 3030695593) ^ 94709237 = (5 : ZMod 3030695593) ^ (47354618 + 47354618 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 47354618 * (5 : ZMod 3030695593) ^ 47354618) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2513238199 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 3030695593) ^ 189418474 = 1968507691 := by
        calc
          (5 : ZMod 3030695593) ^ 189418474 = (5 : ZMod 3030695593) ^ (94709237 + 94709237) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 94709237 * (5 : ZMod 3030695593) ^ 94709237 := by rw [pow_add]
          _ = 1968507691 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 3030695593) ^ 378836949 = 1315939556 := by
        calc
          (5 : ZMod 3030695593) ^ 378836949 = (5 : ZMod 3030695593) ^ (189418474 + 189418474 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 189418474 * (5 : ZMod 3030695593) ^ 189418474) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 1315939556 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 3030695593) ^ 757673898 = 1140707263 := by
        calc
          (5 : ZMod 3030695593) ^ 757673898 = (5 : ZMod 3030695593) ^ (378836949 + 378836949) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 378836949 * (5 : ZMod 3030695593) ^ 378836949 := by rw [pow_add]
          _ = 1140707263 := by rw [factor_0_28]; decide
      have factor_0_30 : (5 : ZMod 3030695593) ^ 1515347796 = 3030695592 := by
        calc
          (5 : ZMod 3030695593) ^ 1515347796 = (5 : ZMod 3030695593) ^ (757673898 + 757673898) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 757673898 * (5 : ZMod 3030695593) ^ 757673898 := by rw [pow_add]
          _ = 3030695592 := by rw [factor_0_29]; decide
      change (5 : ZMod 3030695593) ^ 1515347796 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (5 : ZMod 3030695593) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 3030695593) ^ 3 = 125 := by
        calc
          (5 : ZMod 3030695593) ^ 3 = (5 : ZMod 3030695593) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 1 * (5 : ZMod 3030695593) ^ 1) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 3030695593) ^ 7 = 78125 := by
        calc
          (5 : ZMod 3030695593) ^ 7 = (5 : ZMod 3030695593) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 3 * (5 : ZMod 3030695593) ^ 3) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 3030695593) ^ 15 = 210622195 := by
        calc
          (5 : ZMod 3030695593) ^ 15 = (5 : ZMod 3030695593) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 7 * (5 : ZMod 3030695593) ^ 7) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 210622195 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 3030695593) ^ 30 = 2297035094 := by
        calc
          (5 : ZMod 3030695593) ^ 30 = (5 : ZMod 3030695593) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 15 * (5 : ZMod 3030695593) ^ 15 := by rw [pow_add]
          _ = 2297035094 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 3030695593) ^ 60 = 1795728095 := by
        calc
          (5 : ZMod 3030695593) ^ 60 = (5 : ZMod 3030695593) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 30 * (5 : ZMod 3030695593) ^ 30 := by rw [pow_add]
          _ = 1795728095 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 3030695593) ^ 120 = 1086098366 := by
        calc
          (5 : ZMod 3030695593) ^ 120 = (5 : ZMod 3030695593) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 60 * (5 : ZMod 3030695593) ^ 60 := by rw [pow_add]
          _ = 1086098366 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 3030695593) ^ 240 = 407585718 := by
        calc
          (5 : ZMod 3030695593) ^ 240 = (5 : ZMod 3030695593) ^ (120 + 120) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 120 * (5 : ZMod 3030695593) ^ 120 := by rw [pow_add]
          _ = 407585718 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 3030695593) ^ 481 = 2974172936 := by
        calc
          (5 : ZMod 3030695593) ^ 481 = (5 : ZMod 3030695593) ^ (240 + 240 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 240 * (5 : ZMod 3030695593) ^ 240) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2974172936 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 3030695593) ^ 963 = 2852111123 := by
        calc
          (5 : ZMod 3030695593) ^ 963 = (5 : ZMod 3030695593) ^ (481 + 481 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 481 * (5 : ZMod 3030695593) ^ 481) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2852111123 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 3030695593) ^ 1926 = 117528031 := by
        calc
          (5 : ZMod 3030695593) ^ 1926 = (5 : ZMod 3030695593) ^ (963 + 963) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 963 * (5 : ZMod 3030695593) ^ 963 := by rw [pow_add]
          _ = 117528031 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 3030695593) ^ 3853 = 2120414415 := by
        calc
          (5 : ZMod 3030695593) ^ 3853 = (5 : ZMod 3030695593) ^ (1926 + 1926 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 1926 * (5 : ZMod 3030695593) ^ 1926) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2120414415 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 3030695593) ^ 7707 = 2507386918 := by
        calc
          (5 : ZMod 3030695593) ^ 7707 = (5 : ZMod 3030695593) ^ (3853 + 3853 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 3853 * (5 : ZMod 3030695593) ^ 3853) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2507386918 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 3030695593) ^ 15414 = 613525333 := by
        calc
          (5 : ZMod 3030695593) ^ 15414 = (5 : ZMod 3030695593) ^ (7707 + 7707) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 7707 * (5 : ZMod 3030695593) ^ 7707 := by rw [pow_add]
          _ = 613525333 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 3030695593) ^ 30829 = 1240548516 := by
        calc
          (5 : ZMod 3030695593) ^ 30829 = (5 : ZMod 3030695593) ^ (15414 + 15414 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 15414 * (5 : ZMod 3030695593) ^ 15414) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 1240548516 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 3030695593) ^ 61659 = 259501271 := by
        calc
          (5 : ZMod 3030695593) ^ 61659 = (5 : ZMod 3030695593) ^ (30829 + 30829 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 30829 * (5 : ZMod 3030695593) ^ 30829) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 259501271 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 3030695593) ^ 123319 = 1946839161 := by
        calc
          (5 : ZMod 3030695593) ^ 123319 = (5 : ZMod 3030695593) ^ (61659 + 61659 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 61659 * (5 : ZMod 3030695593) ^ 61659) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 1946839161 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 3030695593) ^ 246638 = 1778934730 := by
        calc
          (5 : ZMod 3030695593) ^ 246638 = (5 : ZMod 3030695593) ^ (123319 + 123319) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 123319 * (5 : ZMod 3030695593) ^ 123319 := by rw [pow_add]
          _ = 1778934730 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 3030695593) ^ 493277 = 2132220189 := by
        calc
          (5 : ZMod 3030695593) ^ 493277 = (5 : ZMod 3030695593) ^ (246638 + 246638 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 246638 * (5 : ZMod 3030695593) ^ 246638) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2132220189 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 3030695593) ^ 986554 = 458652173 := by
        calc
          (5 : ZMod 3030695593) ^ 986554 = (5 : ZMod 3030695593) ^ (493277 + 493277) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 493277 * (5 : ZMod 3030695593) ^ 493277 := by rw [pow_add]
          _ = 458652173 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 3030695593) ^ 1973109 = 2941232297 := by
        calc
          (5 : ZMod 3030695593) ^ 1973109 = (5 : ZMod 3030695593) ^ (986554 + 986554 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 986554 * (5 : ZMod 3030695593) ^ 986554) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2941232297 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 3030695593) ^ 3946218 = 2199106520 := by
        calc
          (5 : ZMod 3030695593) ^ 3946218 = (5 : ZMod 3030695593) ^ (1973109 + 1973109) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 1973109 * (5 : ZMod 3030695593) ^ 1973109 := by rw [pow_add]
          _ = 2199106520 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 3030695593) ^ 7892436 = 2769925498 := by
        calc
          (5 : ZMod 3030695593) ^ 7892436 = (5 : ZMod 3030695593) ^ (3946218 + 3946218) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 3946218 * (5 : ZMod 3030695593) ^ 3946218 := by rw [pow_add]
          _ = 2769925498 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 3030695593) ^ 15784872 = 1012193884 := by
        calc
          (5 : ZMod 3030695593) ^ 15784872 = (5 : ZMod 3030695593) ^ (7892436 + 7892436) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 7892436 * (5 : ZMod 3030695593) ^ 7892436 := by rw [pow_add]
          _ = 1012193884 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 3030695593) ^ 31569745 = 1005126610 := by
        calc
          (5 : ZMod 3030695593) ^ 31569745 = (5 : ZMod 3030695593) ^ (15784872 + 15784872 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 15784872 * (5 : ZMod 3030695593) ^ 15784872) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 1005126610 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 3030695593) ^ 63139491 = 2576212506 := by
        calc
          (5 : ZMod 3030695593) ^ 63139491 = (5 : ZMod 3030695593) ^ (31569745 + 31569745 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 31569745 * (5 : ZMod 3030695593) ^ 31569745) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 2576212506 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 3030695593) ^ 126278983 = 1644807645 := by
        calc
          (5 : ZMod 3030695593) ^ 126278983 = (5 : ZMod 3030695593) ^ (63139491 + 63139491 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 63139491 * (5 : ZMod 3030695593) ^ 63139491) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 1644807645 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 3030695593) ^ 252557966 = 1943028892 := by
        calc
          (5 : ZMod 3030695593) ^ 252557966 = (5 : ZMod 3030695593) ^ (126278983 + 126278983) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 126278983 * (5 : ZMod 3030695593) ^ 126278983 := by rw [pow_add]
          _ = 1943028892 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 3030695593) ^ 505115932 = 2170416172 := by
        calc
          (5 : ZMod 3030695593) ^ 505115932 = (5 : ZMod 3030695593) ^ (252557966 + 252557966) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 252557966 * (5 : ZMod 3030695593) ^ 252557966 := by rw [pow_add]
          _ = 2170416172 := by rw [factor_1_27]; decide
      have factor_1_29 : (5 : ZMod 3030695593) ^ 1010231864 = 2170416171 := by
        calc
          (5 : ZMod 3030695593) ^ 1010231864 = (5 : ZMod 3030695593) ^ (505115932 + 505115932) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 505115932 * (5 : ZMod 3030695593) ^ 505115932 := by rw [pow_add]
          _ = 2170416171 := by rw [factor_1_28]; decide
      change (5 : ZMod 3030695593) ^ 1010231864 ≠ 1
      rw [factor_1_29]
      decide
    ·
      have factor_2_0 : (5 : ZMod 3030695593) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 3030695593) ^ 3 = 125 := by
        calc
          (5 : ZMod 3030695593) ^ 3 = (5 : ZMod 3030695593) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = ((5 : ZMod 3030695593) ^ 1 * (5 : ZMod 3030695593) ^ 1) * (5 : ZMod 3030695593) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 3030695593) ^ 6 = 15625 := by
        calc
          (5 : ZMod 3030695593) ^ 6 = (5 : ZMod 3030695593) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 3 * (5 : ZMod 3030695593) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 3030695593) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 3030695593) ^ 12 = (5 : ZMod 3030695593) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 6 * (5 : ZMod 3030695593) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 3030695593) ^ 24 = 8293520 := by
        calc
          (5 : ZMod 3030695593) ^ 24 = (5 : ZMod 3030695593) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 3030695593) ^ n) (by norm_num)
          _ = (5 : ZMod 3030695593) ^ 12 * (5 : ZMod 3030695593) ^ 12 := by rw [pow_add]
          _ = 8293520 := by rw [factor_2_3]; decide
      change (5 : ZMod 3030695593) ^ 24 ≠ 1
      rw [factor_2_4]
      decide

#print axioms prime_lucas_3030695593

end TotientTailPeriodKiller
end Erdos249257
