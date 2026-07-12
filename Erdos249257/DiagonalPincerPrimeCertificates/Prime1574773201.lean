import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1574773201 : Nat.Prime 1574773201 := by
  apply lucas_primality 1574773201 (34 : ZMod 1574773201)
  ·
      have fermat_0 : (34 : ZMod 1574773201) ^ 1 = 34 := by norm_num
      have fermat_1 : (34 : ZMod 1574773201) ^ 2 = 1156 := by
        calc
          (34 : ZMod 1574773201) ^ 2 = (34 : ZMod 1574773201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 1 * (34 : ZMod 1574773201) ^ 1 := by rw [pow_add]
          _ = 1156 := by rw [fermat_0]; decide
      have fermat_2 : (34 : ZMod 1574773201) ^ 5 = 45435424 := by
        calc
          (34 : ZMod 1574773201) ^ 5 = (34 : ZMod 1574773201) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 2 * (34 : ZMod 1574773201) ^ 2) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 45435424 := by rw [fermat_1]; decide
      have fermat_3 : (34 : ZMod 1574773201) ^ 11 = 517510021 := by
        calc
          (34 : ZMod 1574773201) ^ 11 = (34 : ZMod 1574773201) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 5 * (34 : ZMod 1574773201) ^ 5) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 517510021 := by rw [fermat_2]; decide
      have fermat_4 : (34 : ZMod 1574773201) ^ 23 = 1545814566 := by
        calc
          (34 : ZMod 1574773201) ^ 23 = (34 : ZMod 1574773201) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 11 * (34 : ZMod 1574773201) ^ 11) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1545814566 := by rw [fermat_3]; decide
      have fermat_5 : (34 : ZMod 1574773201) ^ 46 = 1166520303 := by
        calc
          (34 : ZMod 1574773201) ^ 46 = (34 : ZMod 1574773201) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 23 * (34 : ZMod 1574773201) ^ 23 := by rw [pow_add]
          _ = 1166520303 := by rw [fermat_4]; decide
      have fermat_6 : (34 : ZMod 1574773201) ^ 93 = 1331967947 := by
        calc
          (34 : ZMod 1574773201) ^ 93 = (34 : ZMod 1574773201) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 46 * (34 : ZMod 1574773201) ^ 46) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1331967947 := by rw [fermat_5]; decide
      have fermat_7 : (34 : ZMod 1574773201) ^ 187 = 1452306029 := by
        calc
          (34 : ZMod 1574773201) ^ 187 = (34 : ZMod 1574773201) ^ (93 + 93 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 93 * (34 : ZMod 1574773201) ^ 93) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1452306029 := by rw [fermat_6]; decide
      have fermat_8 : (34 : ZMod 1574773201) ^ 375 = 905096783 := by
        calc
          (34 : ZMod 1574773201) ^ 375 = (34 : ZMod 1574773201) ^ (187 + 187 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 187 * (34 : ZMod 1574773201) ^ 187) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 905096783 := by rw [fermat_7]; decide
      have fermat_9 : (34 : ZMod 1574773201) ^ 750 = 567841878 := by
        calc
          (34 : ZMod 1574773201) ^ 750 = (34 : ZMod 1574773201) ^ (375 + 375) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 375 * (34 : ZMod 1574773201) ^ 375 := by rw [pow_add]
          _ = 567841878 := by rw [fermat_8]; decide
      have fermat_10 : (34 : ZMod 1574773201) ^ 1501 = 9961101 := by
        calc
          (34 : ZMod 1574773201) ^ 1501 = (34 : ZMod 1574773201) ^ (750 + 750 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 750 * (34 : ZMod 1574773201) ^ 750) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 9961101 := by rw [fermat_9]; decide
      have fermat_11 : (34 : ZMod 1574773201) ^ 3003 = 1292549358 := by
        calc
          (34 : ZMod 1574773201) ^ 3003 = (34 : ZMod 1574773201) ^ (1501 + 1501 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 1501 * (34 : ZMod 1574773201) ^ 1501) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1292549358 := by rw [fermat_10]; decide
      have fermat_12 : (34 : ZMod 1574773201) ^ 6007 = 161761838 := by
        calc
          (34 : ZMod 1574773201) ^ 6007 = (34 : ZMod 1574773201) ^ (3003 + 3003 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 3003 * (34 : ZMod 1574773201) ^ 3003) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 161761838 := by rw [fermat_11]; decide
      have fermat_13 : (34 : ZMod 1574773201) ^ 12014 = 891547552 := by
        calc
          (34 : ZMod 1574773201) ^ 12014 = (34 : ZMod 1574773201) ^ (6007 + 6007) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 6007 * (34 : ZMod 1574773201) ^ 6007 := by rw [pow_add]
          _ = 891547552 := by rw [fermat_12]; decide
      have fermat_14 : (34 : ZMod 1574773201) ^ 24029 = 1015128935 := by
        calc
          (34 : ZMod 1574773201) ^ 24029 = (34 : ZMod 1574773201) ^ (12014 + 12014 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 12014 * (34 : ZMod 1574773201) ^ 12014) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1015128935 := by rw [fermat_13]; decide
      have fermat_15 : (34 : ZMod 1574773201) ^ 48058 = 1008547092 := by
        calc
          (34 : ZMod 1574773201) ^ 48058 = (34 : ZMod 1574773201) ^ (24029 + 24029) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 24029 * (34 : ZMod 1574773201) ^ 24029 := by rw [pow_add]
          _ = 1008547092 := by rw [fermat_14]; decide
      have fermat_16 : (34 : ZMod 1574773201) ^ 96116 = 1462553386 := by
        calc
          (34 : ZMod 1574773201) ^ 96116 = (34 : ZMod 1574773201) ^ (48058 + 48058) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 48058 * (34 : ZMod 1574773201) ^ 48058 := by rw [pow_add]
          _ = 1462553386 := by rw [fermat_15]; decide
      have fermat_17 : (34 : ZMod 1574773201) ^ 192233 = 663940616 := by
        calc
          (34 : ZMod 1574773201) ^ 192233 = (34 : ZMod 1574773201) ^ (96116 + 96116 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 96116 * (34 : ZMod 1574773201) ^ 96116) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 663940616 := by rw [fermat_16]; decide
      have fermat_18 : (34 : ZMod 1574773201) ^ 384466 = 504909648 := by
        calc
          (34 : ZMod 1574773201) ^ 384466 = (34 : ZMod 1574773201) ^ (192233 + 192233) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 192233 * (34 : ZMod 1574773201) ^ 192233 := by rw [pow_add]
          _ = 504909648 := by rw [fermat_17]; decide
      have fermat_19 : (34 : ZMod 1574773201) ^ 768932 = 903892693 := by
        calc
          (34 : ZMod 1574773201) ^ 768932 = (34 : ZMod 1574773201) ^ (384466 + 384466) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 384466 * (34 : ZMod 1574773201) ^ 384466 := by rw [pow_add]
          _ = 903892693 := by rw [fermat_18]; decide
      have fermat_20 : (34 : ZMod 1574773201) ^ 1537864 = 1351978213 := by
        calc
          (34 : ZMod 1574773201) ^ 1537864 = (34 : ZMod 1574773201) ^ (768932 + 768932) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 768932 * (34 : ZMod 1574773201) ^ 768932 := by rw [pow_add]
          _ = 1351978213 := by rw [fermat_19]; decide
      have fermat_21 : (34 : ZMod 1574773201) ^ 3075728 = 1066036865 := by
        calc
          (34 : ZMod 1574773201) ^ 3075728 = (34 : ZMod 1574773201) ^ (1537864 + 1537864) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 1537864 * (34 : ZMod 1574773201) ^ 1537864 := by rw [pow_add]
          _ = 1066036865 := by rw [fermat_20]; decide
      have fermat_22 : (34 : ZMod 1574773201) ^ 6151457 = 1005799678 := by
        calc
          (34 : ZMod 1574773201) ^ 6151457 = (34 : ZMod 1574773201) ^ (3075728 + 3075728 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 3075728 * (34 : ZMod 1574773201) ^ 3075728) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1005799678 := by rw [fermat_21]; decide
      have fermat_23 : (34 : ZMod 1574773201) ^ 12302915 = 220363184 := by
        calc
          (34 : ZMod 1574773201) ^ 12302915 = (34 : ZMod 1574773201) ^ (6151457 + 6151457 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 6151457 * (34 : ZMod 1574773201) ^ 6151457) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 220363184 := by rw [fermat_22]; decide
      have fermat_24 : (34 : ZMod 1574773201) ^ 24605831 = 1352376616 := by
        calc
          (34 : ZMod 1574773201) ^ 24605831 = (34 : ZMod 1574773201) ^ (12302915 + 12302915 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 12302915 * (34 : ZMod 1574773201) ^ 12302915) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1352376616 := by rw [fermat_23]; decide
      have fermat_25 : (34 : ZMod 1574773201) ^ 49211662 = 538634375 := by
        calc
          (34 : ZMod 1574773201) ^ 49211662 = (34 : ZMod 1574773201) ^ (24605831 + 24605831) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 24605831 * (34 : ZMod 1574773201) ^ 24605831 := by rw [pow_add]
          _ = 538634375 := by rw [fermat_24]; decide
      have fermat_26 : (34 : ZMod 1574773201) ^ 98423325 = 1029425214 := by
        calc
          (34 : ZMod 1574773201) ^ 98423325 = (34 : ZMod 1574773201) ^ (49211662 + 49211662 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 49211662 * (34 : ZMod 1574773201) ^ 49211662) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1029425214 := by rw [fermat_25]; decide
      have fermat_27 : (34 : ZMod 1574773201) ^ 196846650 = 991270367 := by
        calc
          (34 : ZMod 1574773201) ^ 196846650 = (34 : ZMod 1574773201) ^ (98423325 + 98423325) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 98423325 * (34 : ZMod 1574773201) ^ 98423325 := by rw [pow_add]
          _ = 991270367 := by rw [fermat_26]; decide
      have fermat_28 : (34 : ZMod 1574773201) ^ 393693300 = 861037466 := by
        calc
          (34 : ZMod 1574773201) ^ 393693300 = (34 : ZMod 1574773201) ^ (196846650 + 196846650) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 196846650 * (34 : ZMod 1574773201) ^ 196846650 := by rw [pow_add]
          _ = 861037466 := by rw [fermat_27]; decide
      have fermat_29 : (34 : ZMod 1574773201) ^ 787386600 = 1574773200 := by
        calc
          (34 : ZMod 1574773201) ^ 787386600 = (34 : ZMod 1574773201) ^ (393693300 + 393693300) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 393693300 * (34 : ZMod 1574773201) ^ 393693300 := by rw [pow_add]
          _ = 1574773200 := by rw [fermat_28]; decide
      have fermat_30 : (34 : ZMod 1574773201) ^ 1574773200 = 1 := by
        calc
          (34 : ZMod 1574773201) ^ 1574773200 = (34 : ZMod 1574773201) ^ (787386600 + 787386600) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 787386600 * (34 : ZMod 1574773201) ^ 787386600 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 1574773201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (34 : ZMod 1574773201) ^ 1 = 34 := by norm_num
      have factor_0_1 : (34 : ZMod 1574773201) ^ 2 = 1156 := by
        calc
          (34 : ZMod 1574773201) ^ 2 = (34 : ZMod 1574773201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 1 * (34 : ZMod 1574773201) ^ 1 := by rw [pow_add]
          _ = 1156 := by rw [factor_0_0]; decide
      have factor_0_2 : (34 : ZMod 1574773201) ^ 5 = 45435424 := by
        calc
          (34 : ZMod 1574773201) ^ 5 = (34 : ZMod 1574773201) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 2 * (34 : ZMod 1574773201) ^ 2) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 45435424 := by rw [factor_0_1]; decide
      have factor_0_3 : (34 : ZMod 1574773201) ^ 11 = 517510021 := by
        calc
          (34 : ZMod 1574773201) ^ 11 = (34 : ZMod 1574773201) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 5 * (34 : ZMod 1574773201) ^ 5) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 517510021 := by rw [factor_0_2]; decide
      have factor_0_4 : (34 : ZMod 1574773201) ^ 23 = 1545814566 := by
        calc
          (34 : ZMod 1574773201) ^ 23 = (34 : ZMod 1574773201) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 11 * (34 : ZMod 1574773201) ^ 11) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1545814566 := by rw [factor_0_3]; decide
      have factor_0_5 : (34 : ZMod 1574773201) ^ 46 = 1166520303 := by
        calc
          (34 : ZMod 1574773201) ^ 46 = (34 : ZMod 1574773201) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 23 * (34 : ZMod 1574773201) ^ 23 := by rw [pow_add]
          _ = 1166520303 := by rw [factor_0_4]; decide
      have factor_0_6 : (34 : ZMod 1574773201) ^ 93 = 1331967947 := by
        calc
          (34 : ZMod 1574773201) ^ 93 = (34 : ZMod 1574773201) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 46 * (34 : ZMod 1574773201) ^ 46) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1331967947 := by rw [factor_0_5]; decide
      have factor_0_7 : (34 : ZMod 1574773201) ^ 187 = 1452306029 := by
        calc
          (34 : ZMod 1574773201) ^ 187 = (34 : ZMod 1574773201) ^ (93 + 93 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 93 * (34 : ZMod 1574773201) ^ 93) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1452306029 := by rw [factor_0_6]; decide
      have factor_0_8 : (34 : ZMod 1574773201) ^ 375 = 905096783 := by
        calc
          (34 : ZMod 1574773201) ^ 375 = (34 : ZMod 1574773201) ^ (187 + 187 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 187 * (34 : ZMod 1574773201) ^ 187) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 905096783 := by rw [factor_0_7]; decide
      have factor_0_9 : (34 : ZMod 1574773201) ^ 750 = 567841878 := by
        calc
          (34 : ZMod 1574773201) ^ 750 = (34 : ZMod 1574773201) ^ (375 + 375) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 375 * (34 : ZMod 1574773201) ^ 375 := by rw [pow_add]
          _ = 567841878 := by rw [factor_0_8]; decide
      have factor_0_10 : (34 : ZMod 1574773201) ^ 1501 = 9961101 := by
        calc
          (34 : ZMod 1574773201) ^ 1501 = (34 : ZMod 1574773201) ^ (750 + 750 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 750 * (34 : ZMod 1574773201) ^ 750) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 9961101 := by rw [factor_0_9]; decide
      have factor_0_11 : (34 : ZMod 1574773201) ^ 3003 = 1292549358 := by
        calc
          (34 : ZMod 1574773201) ^ 3003 = (34 : ZMod 1574773201) ^ (1501 + 1501 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 1501 * (34 : ZMod 1574773201) ^ 1501) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1292549358 := by rw [factor_0_10]; decide
      have factor_0_12 : (34 : ZMod 1574773201) ^ 6007 = 161761838 := by
        calc
          (34 : ZMod 1574773201) ^ 6007 = (34 : ZMod 1574773201) ^ (3003 + 3003 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 3003 * (34 : ZMod 1574773201) ^ 3003) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 161761838 := by rw [factor_0_11]; decide
      have factor_0_13 : (34 : ZMod 1574773201) ^ 12014 = 891547552 := by
        calc
          (34 : ZMod 1574773201) ^ 12014 = (34 : ZMod 1574773201) ^ (6007 + 6007) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 6007 * (34 : ZMod 1574773201) ^ 6007 := by rw [pow_add]
          _ = 891547552 := by rw [factor_0_12]; decide
      have factor_0_14 : (34 : ZMod 1574773201) ^ 24029 = 1015128935 := by
        calc
          (34 : ZMod 1574773201) ^ 24029 = (34 : ZMod 1574773201) ^ (12014 + 12014 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 12014 * (34 : ZMod 1574773201) ^ 12014) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1015128935 := by rw [factor_0_13]; decide
      have factor_0_15 : (34 : ZMod 1574773201) ^ 48058 = 1008547092 := by
        calc
          (34 : ZMod 1574773201) ^ 48058 = (34 : ZMod 1574773201) ^ (24029 + 24029) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 24029 * (34 : ZMod 1574773201) ^ 24029 := by rw [pow_add]
          _ = 1008547092 := by rw [factor_0_14]; decide
      have factor_0_16 : (34 : ZMod 1574773201) ^ 96116 = 1462553386 := by
        calc
          (34 : ZMod 1574773201) ^ 96116 = (34 : ZMod 1574773201) ^ (48058 + 48058) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 48058 * (34 : ZMod 1574773201) ^ 48058 := by rw [pow_add]
          _ = 1462553386 := by rw [factor_0_15]; decide
      have factor_0_17 : (34 : ZMod 1574773201) ^ 192233 = 663940616 := by
        calc
          (34 : ZMod 1574773201) ^ 192233 = (34 : ZMod 1574773201) ^ (96116 + 96116 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 96116 * (34 : ZMod 1574773201) ^ 96116) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 663940616 := by rw [factor_0_16]; decide
      have factor_0_18 : (34 : ZMod 1574773201) ^ 384466 = 504909648 := by
        calc
          (34 : ZMod 1574773201) ^ 384466 = (34 : ZMod 1574773201) ^ (192233 + 192233) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 192233 * (34 : ZMod 1574773201) ^ 192233 := by rw [pow_add]
          _ = 504909648 := by rw [factor_0_17]; decide
      have factor_0_19 : (34 : ZMod 1574773201) ^ 768932 = 903892693 := by
        calc
          (34 : ZMod 1574773201) ^ 768932 = (34 : ZMod 1574773201) ^ (384466 + 384466) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 384466 * (34 : ZMod 1574773201) ^ 384466 := by rw [pow_add]
          _ = 903892693 := by rw [factor_0_18]; decide
      have factor_0_20 : (34 : ZMod 1574773201) ^ 1537864 = 1351978213 := by
        calc
          (34 : ZMod 1574773201) ^ 1537864 = (34 : ZMod 1574773201) ^ (768932 + 768932) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 768932 * (34 : ZMod 1574773201) ^ 768932 := by rw [pow_add]
          _ = 1351978213 := by rw [factor_0_19]; decide
      have factor_0_21 : (34 : ZMod 1574773201) ^ 3075728 = 1066036865 := by
        calc
          (34 : ZMod 1574773201) ^ 3075728 = (34 : ZMod 1574773201) ^ (1537864 + 1537864) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 1537864 * (34 : ZMod 1574773201) ^ 1537864 := by rw [pow_add]
          _ = 1066036865 := by rw [factor_0_20]; decide
      have factor_0_22 : (34 : ZMod 1574773201) ^ 6151457 = 1005799678 := by
        calc
          (34 : ZMod 1574773201) ^ 6151457 = (34 : ZMod 1574773201) ^ (3075728 + 3075728 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 3075728 * (34 : ZMod 1574773201) ^ 3075728) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1005799678 := by rw [factor_0_21]; decide
      have factor_0_23 : (34 : ZMod 1574773201) ^ 12302915 = 220363184 := by
        calc
          (34 : ZMod 1574773201) ^ 12302915 = (34 : ZMod 1574773201) ^ (6151457 + 6151457 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 6151457 * (34 : ZMod 1574773201) ^ 6151457) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 220363184 := by rw [factor_0_22]; decide
      have factor_0_24 : (34 : ZMod 1574773201) ^ 24605831 = 1352376616 := by
        calc
          (34 : ZMod 1574773201) ^ 24605831 = (34 : ZMod 1574773201) ^ (12302915 + 12302915 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 12302915 * (34 : ZMod 1574773201) ^ 12302915) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1352376616 := by rw [factor_0_23]; decide
      have factor_0_25 : (34 : ZMod 1574773201) ^ 49211662 = 538634375 := by
        calc
          (34 : ZMod 1574773201) ^ 49211662 = (34 : ZMod 1574773201) ^ (24605831 + 24605831) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 24605831 * (34 : ZMod 1574773201) ^ 24605831 := by rw [pow_add]
          _ = 538634375 := by rw [factor_0_24]; decide
      have factor_0_26 : (34 : ZMod 1574773201) ^ 98423325 = 1029425214 := by
        calc
          (34 : ZMod 1574773201) ^ 98423325 = (34 : ZMod 1574773201) ^ (49211662 + 49211662 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 49211662 * (34 : ZMod 1574773201) ^ 49211662) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1029425214 := by rw [factor_0_25]; decide
      have factor_0_27 : (34 : ZMod 1574773201) ^ 196846650 = 991270367 := by
        calc
          (34 : ZMod 1574773201) ^ 196846650 = (34 : ZMod 1574773201) ^ (98423325 + 98423325) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 98423325 * (34 : ZMod 1574773201) ^ 98423325 := by rw [pow_add]
          _ = 991270367 := by rw [factor_0_26]; decide
      have factor_0_28 : (34 : ZMod 1574773201) ^ 393693300 = 861037466 := by
        calc
          (34 : ZMod 1574773201) ^ 393693300 = (34 : ZMod 1574773201) ^ (196846650 + 196846650) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 196846650 * (34 : ZMod 1574773201) ^ 196846650 := by rw [pow_add]
          _ = 861037466 := by rw [factor_0_27]; decide
      have factor_0_29 : (34 : ZMod 1574773201) ^ 787386600 = 1574773200 := by
        calc
          (34 : ZMod 1574773201) ^ 787386600 = (34 : ZMod 1574773201) ^ (393693300 + 393693300) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 393693300 * (34 : ZMod 1574773201) ^ 393693300 := by rw [pow_add]
          _ = 1574773200 := by rw [factor_0_28]; decide
      change (34 : ZMod 1574773201) ^ 787386600 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (34 : ZMod 1574773201) ^ 1 = 34 := by norm_num
      have factor_1_1 : (34 : ZMod 1574773201) ^ 3 = 39304 := by
        calc
          (34 : ZMod 1574773201) ^ 3 = (34 : ZMod 1574773201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 1 * (34 : ZMod 1574773201) ^ 1) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 39304 := by rw [factor_1_0]; decide
      have factor_1_2 : (34 : ZMod 1574773201) ^ 7 = 555834511 := by
        calc
          (34 : ZMod 1574773201) ^ 7 = (34 : ZMod 1574773201) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 3 * (34 : ZMod 1574773201) ^ 3) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 555834511 := by rw [factor_1_1]; decide
      have factor_1_3 : (34 : ZMod 1574773201) ^ 15 = 895884303 := by
        calc
          (34 : ZMod 1574773201) ^ 15 = (34 : ZMod 1574773201) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 7 * (34 : ZMod 1574773201) ^ 7) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 895884303 := by rw [factor_1_2]; decide
      have factor_1_4 : (34 : ZMod 1574773201) ^ 31 = 1028278466 := by
        calc
          (34 : ZMod 1574773201) ^ 31 = (34 : ZMod 1574773201) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 15 * (34 : ZMod 1574773201) ^ 15) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1028278466 := by rw [factor_1_3]; decide
      have factor_1_5 : (34 : ZMod 1574773201) ^ 62 = 347160544 := by
        calc
          (34 : ZMod 1574773201) ^ 62 = (34 : ZMod 1574773201) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 31 * (34 : ZMod 1574773201) ^ 31 := by rw [pow_add]
          _ = 347160544 := by rw [factor_1_4]; decide
      have factor_1_6 : (34 : ZMod 1574773201) ^ 125 = 1397609969 := by
        calc
          (34 : ZMod 1574773201) ^ 125 = (34 : ZMod 1574773201) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 62 * (34 : ZMod 1574773201) ^ 62) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1397609969 := by rw [factor_1_5]; decide
      have factor_1_7 : (34 : ZMod 1574773201) ^ 250 = 1379235221 := by
        calc
          (34 : ZMod 1574773201) ^ 250 = (34 : ZMod 1574773201) ^ (125 + 125) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 125 * (34 : ZMod 1574773201) ^ 125 := by rw [pow_add]
          _ = 1379235221 := by rw [factor_1_6]; decide
      have factor_1_8 : (34 : ZMod 1574773201) ^ 500 = 420727449 := by
        calc
          (34 : ZMod 1574773201) ^ 500 = (34 : ZMod 1574773201) ^ (250 + 250) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 250 * (34 : ZMod 1574773201) ^ 250 := by rw [pow_add]
          _ = 420727449 := by rw [factor_1_7]; decide
      have factor_1_9 : (34 : ZMod 1574773201) ^ 1001 = 1249256006 := by
        calc
          (34 : ZMod 1574773201) ^ 1001 = (34 : ZMod 1574773201) ^ (500 + 500 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 500 * (34 : ZMod 1574773201) ^ 500) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1249256006 := by rw [factor_1_8]; decide
      have factor_1_10 : (34 : ZMod 1574773201) ^ 2002 = 1118714029 := by
        calc
          (34 : ZMod 1574773201) ^ 2002 = (34 : ZMod 1574773201) ^ (1001 + 1001) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 1001 * (34 : ZMod 1574773201) ^ 1001 := by rw [pow_add]
          _ = 1118714029 := by rw [factor_1_9]; decide
      have factor_1_11 : (34 : ZMod 1574773201) ^ 4004 = 1027028243 := by
        calc
          (34 : ZMod 1574773201) ^ 4004 = (34 : ZMod 1574773201) ^ (2002 + 2002) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 2002 * (34 : ZMod 1574773201) ^ 2002 := by rw [pow_add]
          _ = 1027028243 := by rw [factor_1_10]; decide
      have factor_1_12 : (34 : ZMod 1574773201) ^ 8009 = 334684991 := by
        calc
          (34 : ZMod 1574773201) ^ 8009 = (34 : ZMod 1574773201) ^ (4004 + 4004 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 4004 * (34 : ZMod 1574773201) ^ 4004) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 334684991 := by rw [factor_1_11]; decide
      have factor_1_13 : (34 : ZMod 1574773201) ^ 16019 = 1343284770 := by
        calc
          (34 : ZMod 1574773201) ^ 16019 = (34 : ZMod 1574773201) ^ (8009 + 8009 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 8009 * (34 : ZMod 1574773201) ^ 8009) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1343284770 := by rw [factor_1_12]; decide
      have factor_1_14 : (34 : ZMod 1574773201) ^ 32038 = 976696637 := by
        calc
          (34 : ZMod 1574773201) ^ 32038 = (34 : ZMod 1574773201) ^ (16019 + 16019) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 16019 * (34 : ZMod 1574773201) ^ 16019 := by rw [pow_add]
          _ = 976696637 := by rw [factor_1_13]; decide
      have factor_1_15 : (34 : ZMod 1574773201) ^ 64077 = 1268847703 := by
        calc
          (34 : ZMod 1574773201) ^ 64077 = (34 : ZMod 1574773201) ^ (32038 + 32038 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 32038 * (34 : ZMod 1574773201) ^ 32038) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1268847703 := by rw [factor_1_14]; decide
      have factor_1_16 : (34 : ZMod 1574773201) ^ 128155 = 773521550 := by
        calc
          (34 : ZMod 1574773201) ^ 128155 = (34 : ZMod 1574773201) ^ (64077 + 64077 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 64077 * (34 : ZMod 1574773201) ^ 64077) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 773521550 := by rw [factor_1_15]; decide
      have factor_1_17 : (34 : ZMod 1574773201) ^ 256310 = 367935376 := by
        calc
          (34 : ZMod 1574773201) ^ 256310 = (34 : ZMod 1574773201) ^ (128155 + 128155) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 128155 * (34 : ZMod 1574773201) ^ 128155 := by rw [pow_add]
          _ = 367935376 := by rw [factor_1_16]; decide
      have factor_1_18 : (34 : ZMod 1574773201) ^ 512621 = 1380526241 := by
        calc
          (34 : ZMod 1574773201) ^ 512621 = (34 : ZMod 1574773201) ^ (256310 + 256310 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 256310 * (34 : ZMod 1574773201) ^ 256310) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1380526241 := by rw [factor_1_17]; decide
      have factor_1_19 : (34 : ZMod 1574773201) ^ 1025242 = 618641400 := by
        calc
          (34 : ZMod 1574773201) ^ 1025242 = (34 : ZMod 1574773201) ^ (512621 + 512621) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 512621 * (34 : ZMod 1574773201) ^ 512621 := by rw [pow_add]
          _ = 618641400 := by rw [factor_1_18]; decide
      have factor_1_20 : (34 : ZMod 1574773201) ^ 2050485 = 1290964905 := by
        calc
          (34 : ZMod 1574773201) ^ 2050485 = (34 : ZMod 1574773201) ^ (1025242 + 1025242 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 1025242 * (34 : ZMod 1574773201) ^ 1025242) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1290964905 := by rw [factor_1_19]; decide
      have factor_1_21 : (34 : ZMod 1574773201) ^ 4100971 = 563785728 := by
        calc
          (34 : ZMod 1574773201) ^ 4100971 = (34 : ZMod 1574773201) ^ (2050485 + 2050485 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 2050485 * (34 : ZMod 1574773201) ^ 2050485) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 563785728 := by rw [factor_1_20]; decide
      have factor_1_22 : (34 : ZMod 1574773201) ^ 8201943 = 777555194 := by
        calc
          (34 : ZMod 1574773201) ^ 8201943 = (34 : ZMod 1574773201) ^ (4100971 + 4100971 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 4100971 * (34 : ZMod 1574773201) ^ 4100971) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 777555194 := by rw [factor_1_21]; decide
      have factor_1_23 : (34 : ZMod 1574773201) ^ 16403887 = 287133982 := by
        calc
          (34 : ZMod 1574773201) ^ 16403887 = (34 : ZMod 1574773201) ^ (8201943 + 8201943 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 8201943 * (34 : ZMod 1574773201) ^ 8201943) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 287133982 := by rw [factor_1_22]; decide
      have factor_1_24 : (34 : ZMod 1574773201) ^ 32807775 = 998319274 := by
        calc
          (34 : ZMod 1574773201) ^ 32807775 = (34 : ZMod 1574773201) ^ (16403887 + 16403887 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 16403887 * (34 : ZMod 1574773201) ^ 16403887) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 998319274 := by rw [factor_1_23]; decide
      have factor_1_25 : (34 : ZMod 1574773201) ^ 65615550 = 708835369 := by
        calc
          (34 : ZMod 1574773201) ^ 65615550 = (34 : ZMod 1574773201) ^ (32807775 + 32807775) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 32807775 * (34 : ZMod 1574773201) ^ 32807775 := by rw [pow_add]
          _ = 708835369 := by rw [factor_1_24]; decide
      have factor_1_26 : (34 : ZMod 1574773201) ^ 131231100 = 323036680 := by
        calc
          (34 : ZMod 1574773201) ^ 131231100 = (34 : ZMod 1574773201) ^ (65615550 + 65615550) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 65615550 * (34 : ZMod 1574773201) ^ 65615550 := by rw [pow_add]
          _ = 323036680 := by rw [factor_1_25]; decide
      have factor_1_27 : (34 : ZMod 1574773201) ^ 262462200 = 861506778 := by
        calc
          (34 : ZMod 1574773201) ^ 262462200 = (34 : ZMod 1574773201) ^ (131231100 + 131231100) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 131231100 * (34 : ZMod 1574773201) ^ 131231100 := by rw [pow_add]
          _ = 861506778 := by rw [factor_1_26]; decide
      have factor_1_28 : (34 : ZMod 1574773201) ^ 524924400 = 861506777 := by
        calc
          (34 : ZMod 1574773201) ^ 524924400 = (34 : ZMod 1574773201) ^ (262462200 + 262462200) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 262462200 * (34 : ZMod 1574773201) ^ 262462200 := by rw [pow_add]
          _ = 861506777 := by rw [factor_1_27]; decide
      change (34 : ZMod 1574773201) ^ 524924400 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (34 : ZMod 1574773201) ^ 1 = 34 := by norm_num
      have factor_2_1 : (34 : ZMod 1574773201) ^ 2 = 1156 := by
        calc
          (34 : ZMod 1574773201) ^ 2 = (34 : ZMod 1574773201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 1 * (34 : ZMod 1574773201) ^ 1 := by rw [pow_add]
          _ = 1156 := by rw [factor_2_0]; decide
      have factor_2_2 : (34 : ZMod 1574773201) ^ 4 = 1336336 := by
        calc
          (34 : ZMod 1574773201) ^ 4 = (34 : ZMod 1574773201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 2 * (34 : ZMod 1574773201) ^ 2 := by rw [pow_add]
          _ = 1336336 := by rw [factor_2_1]; decide
      have factor_2_3 : (34 : ZMod 1574773201) ^ 9 = 37228708 := by
        calc
          (34 : ZMod 1574773201) ^ 9 = (34 : ZMod 1574773201) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 4 * (34 : ZMod 1574773201) ^ 4) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 37228708 := by rw [factor_2_2]; decide
      have factor_2_4 : (34 : ZMod 1574773201) ^ 18 = 1482643953 := by
        calc
          (34 : ZMod 1574773201) ^ 18 = (34 : ZMod 1574773201) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 9 * (34 : ZMod 1574773201) ^ 9 := by rw [pow_add]
          _ = 1482643953 := by rw [factor_2_3]; decide
      have factor_2_5 : (34 : ZMod 1574773201) ^ 37 = 196858885 := by
        calc
          (34 : ZMod 1574773201) ^ 37 = (34 : ZMod 1574773201) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 18 * (34 : ZMod 1574773201) ^ 18) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 196858885 := by rw [factor_2_4]; decide
      have factor_2_6 : (34 : ZMod 1574773201) ^ 75 = 1103388988 := by
        calc
          (34 : ZMod 1574773201) ^ 75 = (34 : ZMod 1574773201) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 37 * (34 : ZMod 1574773201) ^ 37) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1103388988 := by rw [factor_2_5]; decide
      have factor_2_7 : (34 : ZMod 1574773201) ^ 150 = 1275572533 := by
        calc
          (34 : ZMod 1574773201) ^ 150 = (34 : ZMod 1574773201) ^ (75 + 75) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 75 * (34 : ZMod 1574773201) ^ 75 := by rw [pow_add]
          _ = 1275572533 := by rw [factor_2_6]; decide
      have factor_2_8 : (34 : ZMod 1574773201) ^ 300 = 486018083 := by
        calc
          (34 : ZMod 1574773201) ^ 300 = (34 : ZMod 1574773201) ^ (150 + 150) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 150 * (34 : ZMod 1574773201) ^ 150 := by rw [pow_add]
          _ = 486018083 := by rw [factor_2_7]; decide
      have factor_2_9 : (34 : ZMod 1574773201) ^ 600 = 1531672816 := by
        calc
          (34 : ZMod 1574773201) ^ 600 = (34 : ZMod 1574773201) ^ (300 + 300) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 300 * (34 : ZMod 1574773201) ^ 300 := by rw [pow_add]
          _ = 1531672816 := by rw [factor_2_8]; decide
      have factor_2_10 : (34 : ZMod 1574773201) ^ 1201 = 228809571 := by
        calc
          (34 : ZMod 1574773201) ^ 1201 = (34 : ZMod 1574773201) ^ (600 + 600 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 600 * (34 : ZMod 1574773201) ^ 600) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 228809571 := by rw [factor_2_9]; decide
      have factor_2_11 : (34 : ZMod 1574773201) ^ 2402 = 1258586334 := by
        calc
          (34 : ZMod 1574773201) ^ 2402 = (34 : ZMod 1574773201) ^ (1201 + 1201) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 1201 * (34 : ZMod 1574773201) ^ 1201 := by rw [pow_add]
          _ = 1258586334 := by rw [factor_2_10]; decide
      have factor_2_12 : (34 : ZMod 1574773201) ^ 4805 = 551106806 := by
        calc
          (34 : ZMod 1574773201) ^ 4805 = (34 : ZMod 1574773201) ^ (2402 + 2402 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 2402 * (34 : ZMod 1574773201) ^ 2402) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 551106806 := by rw [factor_2_11]; decide
      have factor_2_13 : (34 : ZMod 1574773201) ^ 9611 = 877162336 := by
        calc
          (34 : ZMod 1574773201) ^ 9611 = (34 : ZMod 1574773201) ^ (4805 + 4805 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 4805 * (34 : ZMod 1574773201) ^ 4805) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 877162336 := by rw [factor_2_12]; decide
      have factor_2_14 : (34 : ZMod 1574773201) ^ 19223 = 1428011791 := by
        calc
          (34 : ZMod 1574773201) ^ 19223 = (34 : ZMod 1574773201) ^ (9611 + 9611 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 9611 * (34 : ZMod 1574773201) ^ 9611) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1428011791 := by rw [factor_2_13]; decide
      have factor_2_15 : (34 : ZMod 1574773201) ^ 38446 = 1401253032 := by
        calc
          (34 : ZMod 1574773201) ^ 38446 = (34 : ZMod 1574773201) ^ (19223 + 19223) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 19223 * (34 : ZMod 1574773201) ^ 19223 := by rw [pow_add]
          _ = 1401253032 := by rw [factor_2_14]; decide
      have factor_2_16 : (34 : ZMod 1574773201) ^ 76893 = 981653225 := by
        calc
          (34 : ZMod 1574773201) ^ 76893 = (34 : ZMod 1574773201) ^ (38446 + 38446 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 38446 * (34 : ZMod 1574773201) ^ 38446) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 981653225 := by rw [factor_2_15]; decide
      have factor_2_17 : (34 : ZMod 1574773201) ^ 153786 = 925532449 := by
        calc
          (34 : ZMod 1574773201) ^ 153786 = (34 : ZMod 1574773201) ^ (76893 + 76893) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 76893 * (34 : ZMod 1574773201) ^ 76893 := by rw [pow_add]
          _ = 925532449 := by rw [factor_2_16]; decide
      have factor_2_18 : (34 : ZMod 1574773201) ^ 307572 = 208338907 := by
        calc
          (34 : ZMod 1574773201) ^ 307572 = (34 : ZMod 1574773201) ^ (153786 + 153786) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 153786 * (34 : ZMod 1574773201) ^ 153786 := by rw [pow_add]
          _ = 208338907 := by rw [factor_2_17]; decide
      have factor_2_19 : (34 : ZMod 1574773201) ^ 615145 = 767555332 := by
        calc
          (34 : ZMod 1574773201) ^ 615145 = (34 : ZMod 1574773201) ^ (307572 + 307572 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 307572 * (34 : ZMod 1574773201) ^ 307572) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 767555332 := by rw [factor_2_18]; decide
      have factor_2_20 : (34 : ZMod 1574773201) ^ 1230291 = 202152677 := by
        calc
          (34 : ZMod 1574773201) ^ 1230291 = (34 : ZMod 1574773201) ^ (615145 + 615145 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 615145 * (34 : ZMod 1574773201) ^ 615145) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 202152677 := by rw [factor_2_19]; decide
      have factor_2_21 : (34 : ZMod 1574773201) ^ 2460583 = 294820640 := by
        calc
          (34 : ZMod 1574773201) ^ 2460583 = (34 : ZMod 1574773201) ^ (1230291 + 1230291 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 1230291 * (34 : ZMod 1574773201) ^ 1230291) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 294820640 := by rw [factor_2_20]; decide
      have factor_2_22 : (34 : ZMod 1574773201) ^ 4921166 = 1358434453 := by
        calc
          (34 : ZMod 1574773201) ^ 4921166 = (34 : ZMod 1574773201) ^ (2460583 + 2460583) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 2460583 * (34 : ZMod 1574773201) ^ 2460583 := by rw [pow_add]
          _ = 1358434453 := by rw [factor_2_21]; decide
      have factor_2_23 : (34 : ZMod 1574773201) ^ 9842332 = 655383781 := by
        calc
          (34 : ZMod 1574773201) ^ 9842332 = (34 : ZMod 1574773201) ^ (4921166 + 4921166) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 4921166 * (34 : ZMod 1574773201) ^ 4921166 := by rw [pow_add]
          _ = 655383781 := by rw [factor_2_22]; decide
      have factor_2_24 : (34 : ZMod 1574773201) ^ 19684665 = 973382944 := by
        calc
          (34 : ZMod 1574773201) ^ 19684665 = (34 : ZMod 1574773201) ^ (9842332 + 9842332 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 9842332 * (34 : ZMod 1574773201) ^ 9842332) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 973382944 := by rw [factor_2_23]; decide
      have factor_2_25 : (34 : ZMod 1574773201) ^ 39369330 = 1250057079 := by
        calc
          (34 : ZMod 1574773201) ^ 39369330 = (34 : ZMod 1574773201) ^ (19684665 + 19684665) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 19684665 * (34 : ZMod 1574773201) ^ 19684665 := by rw [pow_add]
          _ = 1250057079 := by rw [factor_2_24]; decide
      have factor_2_26 : (34 : ZMod 1574773201) ^ 78738660 = 1346913256 := by
        calc
          (34 : ZMod 1574773201) ^ 78738660 = (34 : ZMod 1574773201) ^ (39369330 + 39369330) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 39369330 * (34 : ZMod 1574773201) ^ 39369330 := by rw [pow_add]
          _ = 1346913256 := by rw [factor_2_25]; decide
      have factor_2_27 : (34 : ZMod 1574773201) ^ 157477320 = 206423100 := by
        calc
          (34 : ZMod 1574773201) ^ 157477320 = (34 : ZMod 1574773201) ^ (78738660 + 78738660) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 78738660 * (34 : ZMod 1574773201) ^ 78738660 := by rw [pow_add]
          _ = 206423100 := by rw [factor_2_26]; decide
      have factor_2_28 : (34 : ZMod 1574773201) ^ 314954640 = 1056549021 := by
        calc
          (34 : ZMod 1574773201) ^ 314954640 = (34 : ZMod 1574773201) ^ (157477320 + 157477320) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 157477320 * (34 : ZMod 1574773201) ^ 157477320 := by rw [pow_add]
          _ = 1056549021 := by rw [factor_2_27]; decide
      change (34 : ZMod 1574773201) ^ 314954640 ≠ 1
      rw [factor_2_28]
      decide
    ·
      have factor_3_0 : (34 : ZMod 1574773201) ^ 1 = 34 := by norm_num
      have factor_3_1 : (34 : ZMod 1574773201) ^ 3 = 39304 := by
        calc
          (34 : ZMod 1574773201) ^ 3 = (34 : ZMod 1574773201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 1 * (34 : ZMod 1574773201) ^ 1) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 39304 := by rw [factor_3_0]; decide
      have factor_3_2 : (34 : ZMod 1574773201) ^ 6 = 1544804416 := by
        calc
          (34 : ZMod 1574773201) ^ 6 = (34 : ZMod 1574773201) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 3 * (34 : ZMod 1574773201) ^ 3 := by rw [pow_add]
          _ = 1544804416 := by rw [factor_3_1]; decide
      have factor_3_3 : (34 : ZMod 1574773201) ^ 13 = 1402541097 := by
        calc
          (34 : ZMod 1574773201) ^ 13 = (34 : ZMod 1574773201) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 6 * (34 : ZMod 1574773201) ^ 6) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1402541097 := by rw [factor_3_2]; decide
      have factor_3_4 : (34 : ZMod 1574773201) ^ 26 = 370834283 := by
        calc
          (34 : ZMod 1574773201) ^ 26 = (34 : ZMod 1574773201) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 13 * (34 : ZMod 1574773201) ^ 13 := by rw [pow_add]
          _ = 370834283 := by rw [factor_3_3]; decide
      have factor_3_5 : (34 : ZMod 1574773201) ^ 53 = 1482440330 := by
        calc
          (34 : ZMod 1574773201) ^ 53 = (34 : ZMod 1574773201) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 26 * (34 : ZMod 1574773201) ^ 26) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1482440330 := by rw [factor_3_4]; decide
      have factor_3_6 : (34 : ZMod 1574773201) ^ 107 = 1116677392 := by
        calc
          (34 : ZMod 1574773201) ^ 107 = (34 : ZMod 1574773201) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 53 * (34 : ZMod 1574773201) ^ 53) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1116677392 := by rw [factor_3_5]; decide
      have factor_3_7 : (34 : ZMod 1574773201) ^ 214 = 497040473 := by
        calc
          (34 : ZMod 1574773201) ^ 214 = (34 : ZMod 1574773201) ^ (107 + 107) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 107 * (34 : ZMod 1574773201) ^ 107 := by rw [pow_add]
          _ = 497040473 := by rw [factor_3_6]; decide
      have factor_3_8 : (34 : ZMod 1574773201) ^ 429 = 282079235 := by
        calc
          (34 : ZMod 1574773201) ^ 429 = (34 : ZMod 1574773201) ^ (214 + 214 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 214 * (34 : ZMod 1574773201) ^ 214) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 282079235 := by rw [factor_3_7]; decide
      have factor_3_9 : (34 : ZMod 1574773201) ^ 858 = 159855743 := by
        calc
          (34 : ZMod 1574773201) ^ 858 = (34 : ZMod 1574773201) ^ (429 + 429) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 429 * (34 : ZMod 1574773201) ^ 429 := by rw [pow_add]
          _ = 159855743 := by rw [factor_3_8]; decide
      have factor_3_10 : (34 : ZMod 1574773201) ^ 1716 = 1239269441 := by
        calc
          (34 : ZMod 1574773201) ^ 1716 = (34 : ZMod 1574773201) ^ (858 + 858) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 858 * (34 : ZMod 1574773201) ^ 858 := by rw [pow_add]
          _ = 1239269441 := by rw [factor_3_9]; decide
      have factor_3_11 : (34 : ZMod 1574773201) ^ 3432 = 276354880 := by
        calc
          (34 : ZMod 1574773201) ^ 3432 = (34 : ZMod 1574773201) ^ (1716 + 1716) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 1716 * (34 : ZMod 1574773201) ^ 1716 := by rw [pow_add]
          _ = 276354880 := by rw [factor_3_10]; decide
      have factor_3_12 : (34 : ZMod 1574773201) ^ 6865 = 179834737 := by
        calc
          (34 : ZMod 1574773201) ^ 6865 = (34 : ZMod 1574773201) ^ (3432 + 3432 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 3432 * (34 : ZMod 1574773201) ^ 3432) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 179834737 := by rw [factor_3_11]; decide
      have factor_3_13 : (34 : ZMod 1574773201) ^ 13730 = 1218552941 := by
        calc
          (34 : ZMod 1574773201) ^ 13730 = (34 : ZMod 1574773201) ^ (6865 + 6865) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 6865 * (34 : ZMod 1574773201) ^ 6865 := by rw [pow_add]
          _ = 1218552941 := by rw [factor_3_12]; decide
      have factor_3_14 : (34 : ZMod 1574773201) ^ 27461 = 91541557 := by
        calc
          (34 : ZMod 1574773201) ^ 27461 = (34 : ZMod 1574773201) ^ (13730 + 13730 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 13730 * (34 : ZMod 1574773201) ^ 13730) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 91541557 := by rw [factor_3_13]; decide
      have factor_3_15 : (34 : ZMod 1574773201) ^ 54923 = 1502345921 := by
        calc
          (34 : ZMod 1574773201) ^ 54923 = (34 : ZMod 1574773201) ^ (27461 + 27461 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 27461 * (34 : ZMod 1574773201) ^ 27461) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1502345921 := by rw [factor_3_14]; decide
      have factor_3_16 : (34 : ZMod 1574773201) ^ 109847 = 1459655349 := by
        calc
          (34 : ZMod 1574773201) ^ 109847 = (34 : ZMod 1574773201) ^ (54923 + 54923 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 54923 * (34 : ZMod 1574773201) ^ 54923) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1459655349 := by rw [factor_3_15]; decide
      have factor_3_17 : (34 : ZMod 1574773201) ^ 219694 = 220739448 := by
        calc
          (34 : ZMod 1574773201) ^ 219694 = (34 : ZMod 1574773201) ^ (109847 + 109847) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 109847 * (34 : ZMod 1574773201) ^ 109847 := by rw [pow_add]
          _ = 220739448 := by rw [factor_3_16]; decide
      have factor_3_18 : (34 : ZMod 1574773201) ^ 439389 = 1219770465 := by
        calc
          (34 : ZMod 1574773201) ^ 439389 = (34 : ZMod 1574773201) ^ (219694 + 219694 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 219694 * (34 : ZMod 1574773201) ^ 219694) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1219770465 := by rw [factor_3_17]; decide
      have factor_3_19 : (34 : ZMod 1574773201) ^ 878779 = 1223598229 := by
        calc
          (34 : ZMod 1574773201) ^ 878779 = (34 : ZMod 1574773201) ^ (439389 + 439389 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 439389 * (34 : ZMod 1574773201) ^ 439389) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1223598229 := by rw [factor_3_18]; decide
      have factor_3_20 : (34 : ZMod 1574773201) ^ 1757559 = 1556666263 := by
        calc
          (34 : ZMod 1574773201) ^ 1757559 = (34 : ZMod 1574773201) ^ (878779 + 878779 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 878779 * (34 : ZMod 1574773201) ^ 878779) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1556666263 := by rw [factor_3_19]; decide
      have factor_3_21 : (34 : ZMod 1574773201) ^ 3515118 = 1297153649 := by
        calc
          (34 : ZMod 1574773201) ^ 3515118 = (34 : ZMod 1574773201) ^ (1757559 + 1757559) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 1757559 * (34 : ZMod 1574773201) ^ 1757559 := by rw [pow_add]
          _ = 1297153649 := by rw [factor_3_20]; decide
      have factor_3_22 : (34 : ZMod 1574773201) ^ 7030237 = 623890119 := by
        calc
          (34 : ZMod 1574773201) ^ 7030237 = (34 : ZMod 1574773201) ^ (3515118 + 3515118 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 3515118 * (34 : ZMod 1574773201) ^ 3515118) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 623890119 := by rw [factor_3_21]; decide
      have factor_3_23 : (34 : ZMod 1574773201) ^ 14060475 = 784834224 := by
        calc
          (34 : ZMod 1574773201) ^ 14060475 = (34 : ZMod 1574773201) ^ (7030237 + 7030237 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 7030237 * (34 : ZMod 1574773201) ^ 7030237) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 784834224 := by rw [factor_3_22]; decide
      have factor_3_24 : (34 : ZMod 1574773201) ^ 28120950 = 970145116 := by
        calc
          (34 : ZMod 1574773201) ^ 28120950 = (34 : ZMod 1574773201) ^ (14060475 + 14060475) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 14060475 * (34 : ZMod 1574773201) ^ 14060475 := by rw [pow_add]
          _ = 970145116 := by rw [factor_3_23]; decide
      have factor_3_25 : (34 : ZMod 1574773201) ^ 56241900 = 1137531409 := by
        calc
          (34 : ZMod 1574773201) ^ 56241900 = (34 : ZMod 1574773201) ^ (28120950 + 28120950) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 28120950 * (34 : ZMod 1574773201) ^ 28120950 := by rw [pow_add]
          _ = 1137531409 := by rw [factor_3_24]; decide
      have factor_3_26 : (34 : ZMod 1574773201) ^ 112483800 = 15229811 := by
        calc
          (34 : ZMod 1574773201) ^ 112483800 = (34 : ZMod 1574773201) ^ (56241900 + 56241900) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 56241900 * (34 : ZMod 1574773201) ^ 56241900 := by rw [pow_add]
          _ = 15229811 := by rw [factor_3_25]; decide
      have factor_3_27 : (34 : ZMod 1574773201) ^ 224967600 = 373093632 := by
        calc
          (34 : ZMod 1574773201) ^ 224967600 = (34 : ZMod 1574773201) ^ (112483800 + 112483800) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 112483800 * (34 : ZMod 1574773201) ^ 112483800 := by rw [pow_add]
          _ = 373093632 := by rw [factor_3_26]; decide
      change (34 : ZMod 1574773201) ^ 224967600 ≠ 1
      rw [factor_3_27]
      decide
    ·
      have factor_4_0 : (34 : ZMod 1574773201) ^ 1 = 34 := by norm_num
      have factor_4_1 : (34 : ZMod 1574773201) ^ 2 = 1156 := by
        calc
          (34 : ZMod 1574773201) ^ 2 = (34 : ZMod 1574773201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 1 * (34 : ZMod 1574773201) ^ 1 := by rw [pow_add]
          _ = 1156 := by rw [factor_4_0]; decide
      have factor_4_2 : (34 : ZMod 1574773201) ^ 4 = 1336336 := by
        calc
          (34 : ZMod 1574773201) ^ 4 = (34 : ZMod 1574773201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 2 * (34 : ZMod 1574773201) ^ 2 := by rw [pow_add]
          _ = 1336336 := by rw [factor_4_1]; decide
      have factor_4_3 : (34 : ZMod 1574773201) ^ 8 = 1094962 := by
        calc
          (34 : ZMod 1574773201) ^ 8 = (34 : ZMod 1574773201) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 4 * (34 : ZMod 1574773201) ^ 4 := by rw [pow_add]
          _ = 1094962 := by rw [factor_4_2]; decide
      have factor_4_4 : (34 : ZMod 1574773201) ^ 17 = 1016261211 := by
        calc
          (34 : ZMod 1574773201) ^ 17 = (34 : ZMod 1574773201) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 8 * (34 : ZMod 1574773201) ^ 8) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1016261211 := by rw [factor_4_3]; decide
      have factor_4_5 : (34 : ZMod 1574773201) ^ 34 = 477397200 := by
        calc
          (34 : ZMod 1574773201) ^ 34 = (34 : ZMod 1574773201) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 17 * (34 : ZMod 1574773201) ^ 17 := by rw [pow_add]
          _ = 477397200 := by rw [factor_4_4]; decide
      have factor_4_6 : (34 : ZMod 1574773201) ^ 68 = 389087213 := by
        calc
          (34 : ZMod 1574773201) ^ 68 = (34 : ZMod 1574773201) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 34 * (34 : ZMod 1574773201) ^ 34 := by rw [pow_add]
          _ = 389087213 := by rw [factor_4_5]; decide
      have factor_4_7 : (34 : ZMod 1574773201) ^ 136 = 1384154016 := by
        calc
          (34 : ZMod 1574773201) ^ 136 = (34 : ZMod 1574773201) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 68 * (34 : ZMod 1574773201) ^ 68 := by rw [pow_add]
          _ = 1384154016 := by rw [factor_4_6]; decide
      have factor_4_8 : (34 : ZMod 1574773201) ^ 273 = 207136736 := by
        calc
          (34 : ZMod 1574773201) ^ 273 = (34 : ZMod 1574773201) ^ (136 + 136 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 136 * (34 : ZMod 1574773201) ^ 136) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 207136736 := by rw [factor_4_7]; decide
      have factor_4_9 : (34 : ZMod 1574773201) ^ 546 = 848526905 := by
        calc
          (34 : ZMod 1574773201) ^ 546 = (34 : ZMod 1574773201) ^ (273 + 273) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 273 * (34 : ZMod 1574773201) ^ 273 := by rw [pow_add]
          _ = 848526905 := by rw [factor_4_8]; decide
      have factor_4_10 : (34 : ZMod 1574773201) ^ 1092 = 1232280459 := by
        calc
          (34 : ZMod 1574773201) ^ 1092 = (34 : ZMod 1574773201) ^ (546 + 546) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 546 * (34 : ZMod 1574773201) ^ 546 := by rw [pow_add]
          _ = 1232280459 := by rw [factor_4_9]; decide
      have factor_4_11 : (34 : ZMod 1574773201) ^ 2184 = 464901236 := by
        calc
          (34 : ZMod 1574773201) ^ 2184 = (34 : ZMod 1574773201) ^ (1092 + 1092) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 1092 * (34 : ZMod 1574773201) ^ 1092 := by rw [pow_add]
          _ = 464901236 := by rw [factor_4_10]; decide
      have factor_4_12 : (34 : ZMod 1574773201) ^ 4368 = 304329330 := by
        calc
          (34 : ZMod 1574773201) ^ 4368 = (34 : ZMod 1574773201) ^ (2184 + 2184) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 2184 * (34 : ZMod 1574773201) ^ 2184 := by rw [pow_add]
          _ = 304329330 := by rw [factor_4_11]; decide
      have factor_4_13 : (34 : ZMod 1574773201) ^ 8737 = 1427508569 := by
        calc
          (34 : ZMod 1574773201) ^ 8737 = (34 : ZMod 1574773201) ^ (4368 + 4368 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 4368 * (34 : ZMod 1574773201) ^ 4368) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1427508569 := by rw [factor_4_12]; decide
      have factor_4_14 : (34 : ZMod 1574773201) ^ 17475 = 718331549 := by
        calc
          (34 : ZMod 1574773201) ^ 17475 = (34 : ZMod 1574773201) ^ (8737 + 8737 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 8737 * (34 : ZMod 1574773201) ^ 8737) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 718331549 := by rw [factor_4_13]; decide
      have factor_4_15 : (34 : ZMod 1574773201) ^ 34951 = 668868742 := by
        calc
          (34 : ZMod 1574773201) ^ 34951 = (34 : ZMod 1574773201) ^ (17475 + 17475 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 17475 * (34 : ZMod 1574773201) ^ 17475) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 668868742 := by rw [factor_4_14]; decide
      have factor_4_16 : (34 : ZMod 1574773201) ^ 69902 = 1490371037 := by
        calc
          (34 : ZMod 1574773201) ^ 69902 = (34 : ZMod 1574773201) ^ (34951 + 34951) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 34951 * (34 : ZMod 1574773201) ^ 34951 := by rw [pow_add]
          _ = 1490371037 := by rw [factor_4_15]; decide
      have factor_4_17 : (34 : ZMod 1574773201) ^ 139805 = 1441114711 := by
        calc
          (34 : ZMod 1574773201) ^ 139805 = (34 : ZMod 1574773201) ^ (69902 + 69902 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 69902 * (34 : ZMod 1574773201) ^ 69902) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1441114711 := by rw [factor_4_16]; decide
      have factor_4_18 : (34 : ZMod 1574773201) ^ 279611 = 396869525 := by
        calc
          (34 : ZMod 1574773201) ^ 279611 = (34 : ZMod 1574773201) ^ (139805 + 139805 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 139805 * (34 : ZMod 1574773201) ^ 139805) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 396869525 := by rw [factor_4_17]; decide
      have factor_4_19 : (34 : ZMod 1574773201) ^ 559223 = 1027222565 := by
        calc
          (34 : ZMod 1574773201) ^ 559223 = (34 : ZMod 1574773201) ^ (279611 + 279611 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 279611 * (34 : ZMod 1574773201) ^ 279611) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1027222565 := by rw [factor_4_18]; decide
      have factor_4_20 : (34 : ZMod 1574773201) ^ 1118446 = 720933647 := by
        calc
          (34 : ZMod 1574773201) ^ 1118446 = (34 : ZMod 1574773201) ^ (559223 + 559223) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 559223 * (34 : ZMod 1574773201) ^ 559223 := by rw [pow_add]
          _ = 720933647 := by rw [factor_4_19]; decide
      have factor_4_21 : (34 : ZMod 1574773201) ^ 2236893 = 549243771 := by
        calc
          (34 : ZMod 1574773201) ^ 2236893 = (34 : ZMod 1574773201) ^ (1118446 + 1118446 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 1118446 * (34 : ZMod 1574773201) ^ 1118446) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 549243771 := by rw [factor_4_20]; decide
      have factor_4_22 : (34 : ZMod 1574773201) ^ 4473787 = 626387067 := by
        calc
          (34 : ZMod 1574773201) ^ 4473787 = (34 : ZMod 1574773201) ^ (2236893 + 2236893 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 2236893 * (34 : ZMod 1574773201) ^ 2236893) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 626387067 := by rw [factor_4_21]; decide
      have factor_4_23 : (34 : ZMod 1574773201) ^ 8947575 = 501115967 := by
        calc
          (34 : ZMod 1574773201) ^ 8947575 = (34 : ZMod 1574773201) ^ (4473787 + 4473787 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 4473787 * (34 : ZMod 1574773201) ^ 4473787) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 501115967 := by rw [factor_4_22]; decide
      have factor_4_24 : (34 : ZMod 1574773201) ^ 17895150 = 659264227 := by
        calc
          (34 : ZMod 1574773201) ^ 17895150 = (34 : ZMod 1574773201) ^ (8947575 + 8947575) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 8947575 * (34 : ZMod 1574773201) ^ 8947575 := by rw [pow_add]
          _ = 659264227 := by rw [factor_4_23]; decide
      have factor_4_25 : (34 : ZMod 1574773201) ^ 35790300 = 836748262 := by
        calc
          (34 : ZMod 1574773201) ^ 35790300 = (34 : ZMod 1574773201) ^ (17895150 + 17895150) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 17895150 * (34 : ZMod 1574773201) ^ 17895150 := by rw [pow_add]
          _ = 836748262 := by rw [factor_4_24]; decide
      have factor_4_26 : (34 : ZMod 1574773201) ^ 71580600 = 672780429 := by
        calc
          (34 : ZMod 1574773201) ^ 71580600 = (34 : ZMod 1574773201) ^ (35790300 + 35790300) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 35790300 * (34 : ZMod 1574773201) ^ 35790300 := by rw [pow_add]
          _ = 672780429 := by rw [factor_4_25]; decide
      have factor_4_27 : (34 : ZMod 1574773201) ^ 143161200 = 319881899 := by
        calc
          (34 : ZMod 1574773201) ^ 143161200 = (34 : ZMod 1574773201) ^ (71580600 + 71580600) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 71580600 * (34 : ZMod 1574773201) ^ 71580600 := by rw [pow_add]
          _ = 319881899 := by rw [factor_4_26]; decide
      change (34 : ZMod 1574773201) ^ 143161200 ≠ 1
      rw [factor_4_27]
      decide
    ·
      have factor_5_0 : (34 : ZMod 1574773201) ^ 1 = 34 := by norm_num
      have factor_5_1 : (34 : ZMod 1574773201) ^ 3 = 39304 := by
        calc
          (34 : ZMod 1574773201) ^ 3 = (34 : ZMod 1574773201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 1 * (34 : ZMod 1574773201) ^ 1) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 39304 := by rw [factor_5_0]; decide
      have factor_5_2 : (34 : ZMod 1574773201) ^ 7 = 555834511 := by
        calc
          (34 : ZMod 1574773201) ^ 7 = (34 : ZMod 1574773201) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 3 * (34 : ZMod 1574773201) ^ 3) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 555834511 := by rw [factor_5_1]; decide
      have factor_5_3 : (34 : ZMod 1574773201) ^ 14 = 443201268 := by
        calc
          (34 : ZMod 1574773201) ^ 14 = (34 : ZMod 1574773201) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 7 * (34 : ZMod 1574773201) ^ 7 := by rw [pow_add]
          _ = 443201268 := by rw [factor_5_2]; decide
      have factor_5_4 : (34 : ZMod 1574773201) ^ 28 = 346120476 := by
        calc
          (34 : ZMod 1574773201) ^ 28 = (34 : ZMod 1574773201) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 14 * (34 : ZMod 1574773201) ^ 14 := by rw [pow_add]
          _ = 346120476 := by rw [factor_5_3]; decide
      have factor_5_5 : (34 : ZMod 1574773201) ^ 57 = 465117297 := by
        calc
          (34 : ZMod 1574773201) ^ 57 = (34 : ZMod 1574773201) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 28 * (34 : ZMod 1574773201) ^ 28) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 465117297 := by rw [factor_5_4]; decide
      have factor_5_6 : (34 : ZMod 1574773201) ^ 115 = 831541463 := by
        calc
          (34 : ZMod 1574773201) ^ 115 = (34 : ZMod 1574773201) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 57 * (34 : ZMod 1574773201) ^ 57) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 831541463 := by rw [factor_5_5]; decide
      have factor_5_7 : (34 : ZMod 1574773201) ^ 231 = 242123628 := by
        calc
          (34 : ZMod 1574773201) ^ 231 = (34 : ZMod 1574773201) ^ (115 + 115 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 115 * (34 : ZMod 1574773201) ^ 115) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 242123628 := by rw [factor_5_6]; decide
      have factor_5_8 : (34 : ZMod 1574773201) ^ 462 = 773915931 := by
        calc
          (34 : ZMod 1574773201) ^ 462 = (34 : ZMod 1574773201) ^ (231 + 231) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 231 * (34 : ZMod 1574773201) ^ 231 := by rw [pow_add]
          _ = 773915931 := by rw [factor_5_7]; decide
      have factor_5_9 : (34 : ZMod 1574773201) ^ 924 = 576680102 := by
        calc
          (34 : ZMod 1574773201) ^ 924 = (34 : ZMod 1574773201) ^ (462 + 462) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 462 * (34 : ZMod 1574773201) ^ 462 := by rw [pow_add]
          _ = 576680102 := by rw [factor_5_8]; decide
      have factor_5_10 : (34 : ZMod 1574773201) ^ 1848 = 9841226 := by
        calc
          (34 : ZMod 1574773201) ^ 1848 = (34 : ZMod 1574773201) ^ (924 + 924) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 924 * (34 : ZMod 1574773201) ^ 924 := by rw [pow_add]
          _ = 9841226 := by rw [factor_5_9]; decide
      have factor_5_11 : (34 : ZMod 1574773201) ^ 3696 = 1177321576 := by
        calc
          (34 : ZMod 1574773201) ^ 3696 = (34 : ZMod 1574773201) ^ (1848 + 1848) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 1848 * (34 : ZMod 1574773201) ^ 1848 := by rw [pow_add]
          _ = 1177321576 := by rw [factor_5_10]; decide
      have factor_5_12 : (34 : ZMod 1574773201) ^ 7393 = 836183313 := by
        calc
          (34 : ZMod 1574773201) ^ 7393 = (34 : ZMod 1574773201) ^ (3696 + 3696 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 3696 * (34 : ZMod 1574773201) ^ 3696) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 836183313 := by rw [factor_5_11]; decide
      have factor_5_13 : (34 : ZMod 1574773201) ^ 14787 = 1001749573 := by
        calc
          (34 : ZMod 1574773201) ^ 14787 = (34 : ZMod 1574773201) ^ (7393 + 7393 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 7393 * (34 : ZMod 1574773201) ^ 7393) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1001749573 := by rw [factor_5_12]; decide
      have factor_5_14 : (34 : ZMod 1574773201) ^ 29574 = 1572555510 := by
        calc
          (34 : ZMod 1574773201) ^ 29574 = (34 : ZMod 1574773201) ^ (14787 + 14787) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 14787 * (34 : ZMod 1574773201) ^ 14787 := by rw [pow_add]
          _ = 1572555510 := by rw [factor_5_13]; decide
      have factor_5_15 : (34 : ZMod 1574773201) ^ 59148 = 136664758 := by
        calc
          (34 : ZMod 1574773201) ^ 59148 = (34 : ZMod 1574773201) ^ (29574 + 29574) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 29574 * (34 : ZMod 1574773201) ^ 29574 := by rw [pow_add]
          _ = 136664758 := by rw [factor_5_14]; decide
      have factor_5_16 : (34 : ZMod 1574773201) ^ 118297 = 779905149 := by
        calc
          (34 : ZMod 1574773201) ^ 118297 = (34 : ZMod 1574773201) ^ (59148 + 59148 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 59148 * (34 : ZMod 1574773201) ^ 59148) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 779905149 := by rw [factor_5_15]; decide
      have factor_5_17 : (34 : ZMod 1574773201) ^ 236594 = 1133743610 := by
        calc
          (34 : ZMod 1574773201) ^ 236594 = (34 : ZMod 1574773201) ^ (118297 + 118297) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 118297 * (34 : ZMod 1574773201) ^ 118297 := by rw [pow_add]
          _ = 1133743610 := by rw [factor_5_16]; decide
      have factor_5_18 : (34 : ZMod 1574773201) ^ 473189 = 268393399 := by
        calc
          (34 : ZMod 1574773201) ^ 473189 = (34 : ZMod 1574773201) ^ (236594 + 236594 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 236594 * (34 : ZMod 1574773201) ^ 236594) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 268393399 := by rw [factor_5_17]; decide
      have factor_5_19 : (34 : ZMod 1574773201) ^ 946378 = 742244096 := by
        calc
          (34 : ZMod 1574773201) ^ 946378 = (34 : ZMod 1574773201) ^ (473189 + 473189) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 473189 * (34 : ZMod 1574773201) ^ 473189 := by rw [pow_add]
          _ = 742244096 := by rw [factor_5_18]; decide
      have factor_5_20 : (34 : ZMod 1574773201) ^ 1892756 = 609445964 := by
        calc
          (34 : ZMod 1574773201) ^ 1892756 = (34 : ZMod 1574773201) ^ (946378 + 946378) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 946378 * (34 : ZMod 1574773201) ^ 946378 := by rw [pow_add]
          _ = 609445964 := by rw [factor_5_19]; decide
      have factor_5_21 : (34 : ZMod 1574773201) ^ 3785512 = 1013972728 := by
        calc
          (34 : ZMod 1574773201) ^ 3785512 = (34 : ZMod 1574773201) ^ (1892756 + 1892756) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 1892756 * (34 : ZMod 1574773201) ^ 1892756 := by rw [pow_add]
          _ = 1013972728 := by rw [factor_5_20]; decide
      have factor_5_22 : (34 : ZMod 1574773201) ^ 7571025 = 1119382545 := by
        calc
          (34 : ZMod 1574773201) ^ 7571025 = (34 : ZMod 1574773201) ^ (3785512 + 3785512 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 3785512 * (34 : ZMod 1574773201) ^ 3785512) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1119382545 := by rw [factor_5_21]; decide
      have factor_5_23 : (34 : ZMod 1574773201) ^ 15142050 = 1354609920 := by
        calc
          (34 : ZMod 1574773201) ^ 15142050 = (34 : ZMod 1574773201) ^ (7571025 + 7571025) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 7571025 * (34 : ZMod 1574773201) ^ 7571025 := by rw [pow_add]
          _ = 1354609920 := by rw [factor_5_22]; decide
      have factor_5_24 : (34 : ZMod 1574773201) ^ 30284100 = 1574254339 := by
        calc
          (34 : ZMod 1574773201) ^ 30284100 = (34 : ZMod 1574773201) ^ (15142050 + 15142050) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 15142050 * (34 : ZMod 1574773201) ^ 15142050 := by rw [pow_add]
          _ = 1574254339 := by rw [factor_5_23]; decide
      have factor_5_25 : (34 : ZMod 1574773201) ^ 60568200 = 1506330874 := by
        calc
          (34 : ZMod 1574773201) ^ 60568200 = (34 : ZMod 1574773201) ^ (30284100 + 30284100) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 30284100 * (34 : ZMod 1574773201) ^ 30284100 := by rw [pow_add]
          _ = 1506330874 := by rw [factor_5_24]; decide
      have factor_5_26 : (34 : ZMod 1574773201) ^ 121136400 = 266016309 := by
        calc
          (34 : ZMod 1574773201) ^ 121136400 = (34 : ZMod 1574773201) ^ (60568200 + 60568200) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 60568200 * (34 : ZMod 1574773201) ^ 60568200 := by rw [pow_add]
          _ = 266016309 := by rw [factor_5_25]; decide
      change (34 : ZMod 1574773201) ^ 121136400 ≠ 1
      rw [factor_5_26]
      decide
    ·
      have factor_6_0 : (34 : ZMod 1574773201) ^ 1 = 34 := by norm_num
      have factor_6_1 : (34 : ZMod 1574773201) ^ 2 = 1156 := by
        calc
          (34 : ZMod 1574773201) ^ 2 = (34 : ZMod 1574773201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 1 * (34 : ZMod 1574773201) ^ 1 := by rw [pow_add]
          _ = 1156 := by rw [factor_6_0]; decide
      have factor_6_2 : (34 : ZMod 1574773201) ^ 4 = 1336336 := by
        calc
          (34 : ZMod 1574773201) ^ 4 = (34 : ZMod 1574773201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 2 * (34 : ZMod 1574773201) ^ 2 := by rw [pow_add]
          _ = 1336336 := by rw [factor_6_1]; decide
      have factor_6_3 : (34 : ZMod 1574773201) ^ 9 = 37228708 := by
        calc
          (34 : ZMod 1574773201) ^ 9 = (34 : ZMod 1574773201) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 4 * (34 : ZMod 1574773201) ^ 4) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 37228708 := by rw [factor_6_2]; decide
      have factor_6_4 : (34 : ZMod 1574773201) ^ 19 = 17151970 := by
        calc
          (34 : ZMod 1574773201) ^ 19 = (34 : ZMod 1574773201) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 9 * (34 : ZMod 1574773201) ^ 9) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 17151970 := by rw [factor_6_3]; decide
      have factor_6_5 : (34 : ZMod 1574773201) ^ 39 = 801530116 := by
        calc
          (34 : ZMod 1574773201) ^ 39 = (34 : ZMod 1574773201) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 19 * (34 : ZMod 1574773201) ^ 19) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 801530116 := by rw [factor_6_4]; decide
      have factor_6_6 : (34 : ZMod 1574773201) ^ 79 = 484014844 := by
        calc
          (34 : ZMod 1574773201) ^ 79 = (34 : ZMod 1574773201) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 39 * (34 : ZMod 1574773201) ^ 39) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 484014844 := by rw [factor_6_5]; decide
      have factor_6_7 : (34 : ZMod 1574773201) ^ 158 = 880128223 := by
        calc
          (34 : ZMod 1574773201) ^ 158 = (34 : ZMod 1574773201) ^ (79 + 79) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 79 * (34 : ZMod 1574773201) ^ 79 := by rw [pow_add]
          _ = 880128223 := by rw [factor_6_6]; decide
      have factor_6_8 : (34 : ZMod 1574773201) ^ 316 = 68316662 := by
        calc
          (34 : ZMod 1574773201) ^ 316 = (34 : ZMod 1574773201) ^ (158 + 158) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 158 * (34 : ZMod 1574773201) ^ 158 := by rw [pow_add]
          _ = 68316662 := by rw [factor_6_7]; decide
      have factor_6_9 : (34 : ZMod 1574773201) ^ 632 = 1522379338 := by
        calc
          (34 : ZMod 1574773201) ^ 632 = (34 : ZMod 1574773201) ^ (316 + 316) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 316 * (34 : ZMod 1574773201) ^ 316 := by rw [pow_add]
          _ = 1522379338 := by rw [factor_6_8]; decide
      have factor_6_10 : (34 : ZMod 1574773201) ^ 1264 = 581997187 := by
        calc
          (34 : ZMod 1574773201) ^ 1264 = (34 : ZMod 1574773201) ^ (632 + 632) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 632 * (34 : ZMod 1574773201) ^ 632 := by rw [pow_add]
          _ = 581997187 := by rw [factor_6_9]; decide
      have factor_6_11 : (34 : ZMod 1574773201) ^ 2529 = 955273803 := by
        calc
          (34 : ZMod 1574773201) ^ 2529 = (34 : ZMod 1574773201) ^ (1264 + 1264 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 1264 * (34 : ZMod 1574773201) ^ 1264) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 955273803 := by rw [factor_6_10]; decide
      have factor_6_12 : (34 : ZMod 1574773201) ^ 5058 = 1161246985 := by
        calc
          (34 : ZMod 1574773201) ^ 5058 = (34 : ZMod 1574773201) ^ (2529 + 2529) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 2529 * (34 : ZMod 1574773201) ^ 2529 := by rw [pow_add]
          _ = 1161246985 := by rw [factor_6_11]; decide
      have factor_6_13 : (34 : ZMod 1574773201) ^ 10117 = 239841214 := by
        calc
          (34 : ZMod 1574773201) ^ 10117 = (34 : ZMod 1574773201) ^ (5058 + 5058 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 5058 * (34 : ZMod 1574773201) ^ 5058) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 239841214 := by rw [factor_6_12]; decide
      have factor_6_14 : (34 : ZMod 1574773201) ^ 20235 = 204764032 := by
        calc
          (34 : ZMod 1574773201) ^ 20235 = (34 : ZMod 1574773201) ^ (10117 + 10117 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 10117 * (34 : ZMod 1574773201) ^ 10117) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 204764032 := by rw [factor_6_13]; decide
      have factor_6_15 : (34 : ZMod 1574773201) ^ 40470 = 670189642 := by
        calc
          (34 : ZMod 1574773201) ^ 40470 = (34 : ZMod 1574773201) ^ (20235 + 20235) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 20235 * (34 : ZMod 1574773201) ^ 20235 := by rw [pow_add]
          _ = 670189642 := by rw [factor_6_14]; decide
      have factor_6_16 : (34 : ZMod 1574773201) ^ 80940 = 497258251 := by
        calc
          (34 : ZMod 1574773201) ^ 80940 = (34 : ZMod 1574773201) ^ (40470 + 40470) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 40470 * (34 : ZMod 1574773201) ^ 40470 := by rw [pow_add]
          _ = 497258251 := by rw [factor_6_15]; decide
      have factor_6_17 : (34 : ZMod 1574773201) ^ 161880 = 1329008653 := by
        calc
          (34 : ZMod 1574773201) ^ 161880 = (34 : ZMod 1574773201) ^ (80940 + 80940) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 80940 * (34 : ZMod 1574773201) ^ 80940 := by rw [pow_add]
          _ = 1329008653 := by rw [factor_6_16]; decide
      have factor_6_18 : (34 : ZMod 1574773201) ^ 323760 = 1098444640 := by
        calc
          (34 : ZMod 1574773201) ^ 323760 = (34 : ZMod 1574773201) ^ (161880 + 161880) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 161880 * (34 : ZMod 1574773201) ^ 161880 := by rw [pow_add]
          _ = 1098444640 := by rw [factor_6_17]; decide
      have factor_6_19 : (34 : ZMod 1574773201) ^ 647521 = 432735647 := by
        calc
          (34 : ZMod 1574773201) ^ 647521 = (34 : ZMod 1574773201) ^ (323760 + 323760 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 323760 * (34 : ZMod 1574773201) ^ 323760) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 432735647 := by rw [factor_6_18]; decide
      have factor_6_20 : (34 : ZMod 1574773201) ^ 1295043 = 367884592 := by
        calc
          (34 : ZMod 1574773201) ^ 1295043 = (34 : ZMod 1574773201) ^ (647521 + 647521 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 647521 * (34 : ZMod 1574773201) ^ 647521) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 367884592 := by rw [factor_6_19]; decide
      have factor_6_21 : (34 : ZMod 1574773201) ^ 2590087 = 1539147621 := by
        calc
          (34 : ZMod 1574773201) ^ 2590087 = (34 : ZMod 1574773201) ^ (1295043 + 1295043 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 1295043 * (34 : ZMod 1574773201) ^ 1295043) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1539147621 := by rw [factor_6_20]; decide
      have factor_6_22 : (34 : ZMod 1574773201) ^ 5180175 = 668696641 := by
        calc
          (34 : ZMod 1574773201) ^ 5180175 = (34 : ZMod 1574773201) ^ (2590087 + 2590087 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 2590087 * (34 : ZMod 1574773201) ^ 2590087) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 668696641 := by rw [factor_6_21]; decide
      have factor_6_23 : (34 : ZMod 1574773201) ^ 10360350 = 772593931 := by
        calc
          (34 : ZMod 1574773201) ^ 10360350 = (34 : ZMod 1574773201) ^ (5180175 + 5180175) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 5180175 * (34 : ZMod 1574773201) ^ 5180175 := by rw [pow_add]
          _ = 772593931 := by rw [factor_6_22]; decide
      have factor_6_24 : (34 : ZMod 1574773201) ^ 20720700 = 67097975 := by
        calc
          (34 : ZMod 1574773201) ^ 20720700 = (34 : ZMod 1574773201) ^ (10360350 + 10360350) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 10360350 * (34 : ZMod 1574773201) ^ 10360350 := by rw [pow_add]
          _ = 67097975 := by rw [factor_6_23]; decide
      have factor_6_25 : (34 : ZMod 1574773201) ^ 41441400 = 247483313 := by
        calc
          (34 : ZMod 1574773201) ^ 41441400 = (34 : ZMod 1574773201) ^ (20720700 + 20720700) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 20720700 * (34 : ZMod 1574773201) ^ 20720700 := by rw [pow_add]
          _ = 247483313 := by rw [factor_6_24]; decide
      have factor_6_26 : (34 : ZMod 1574773201) ^ 82882800 = 680271156 := by
        calc
          (34 : ZMod 1574773201) ^ 82882800 = (34 : ZMod 1574773201) ^ (41441400 + 41441400) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 41441400 * (34 : ZMod 1574773201) ^ 41441400 := by rw [pow_add]
          _ = 680271156 := by rw [factor_6_25]; decide
      change (34 : ZMod 1574773201) ^ 82882800 ≠ 1
      rw [factor_6_26]
      decide
    ·
      have factor_7_0 : (34 : ZMod 1574773201) ^ 1 = 34 := by norm_num
      have factor_7_1 : (34 : ZMod 1574773201) ^ 2 = 1156 := by
        calc
          (34 : ZMod 1574773201) ^ 2 = (34 : ZMod 1574773201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 1 * (34 : ZMod 1574773201) ^ 1 := by rw [pow_add]
          _ = 1156 := by rw [factor_7_0]; decide
      have factor_7_2 : (34 : ZMod 1574773201) ^ 4 = 1336336 := by
        calc
          (34 : ZMod 1574773201) ^ 4 = (34 : ZMod 1574773201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 2 * (34 : ZMod 1574773201) ^ 2 := by rw [pow_add]
          _ = 1336336 := by rw [factor_7_1]; decide
      have factor_7_3 : (34 : ZMod 1574773201) ^ 8 = 1094962 := by
        calc
          (34 : ZMod 1574773201) ^ 8 = (34 : ZMod 1574773201) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 4 * (34 : ZMod 1574773201) ^ 4 := by rw [pow_add]
          _ = 1094962 := by rw [factor_7_2]; decide
      have factor_7_4 : (34 : ZMod 1574773201) ^ 16 = 539375483 := by
        calc
          (34 : ZMod 1574773201) ^ 16 = (34 : ZMod 1574773201) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 8 * (34 : ZMod 1574773201) ^ 8 := by rw [pow_add]
          _ = 539375483 := by rw [factor_7_3]; decide
      have factor_7_5 : (34 : ZMod 1574773201) ^ 32 = 316457422 := by
        calc
          (34 : ZMod 1574773201) ^ 32 = (34 : ZMod 1574773201) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 16 * (34 : ZMod 1574773201) ^ 16 := by rw [pow_add]
          _ = 316457422 := by rw [factor_7_4]; decide
      have factor_7_6 : (34 : ZMod 1574773201) ^ 65 = 963007912 := by
        calc
          (34 : ZMod 1574773201) ^ 65 = (34 : ZMod 1574773201) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 32 * (34 : ZMod 1574773201) ^ 32) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 963007912 := by rw [factor_7_5]; decide
      have factor_7_7 : (34 : ZMod 1574773201) ^ 130 = 1298791554 := by
        calc
          (34 : ZMod 1574773201) ^ 130 = (34 : ZMod 1574773201) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 65 * (34 : ZMod 1574773201) ^ 65 := by rw [pow_add]
          _ = 1298791554 := by rw [factor_7_6]; decide
      have factor_7_8 : (34 : ZMod 1574773201) ^ 261 = 382042311 := by
        calc
          (34 : ZMod 1574773201) ^ 261 = (34 : ZMod 1574773201) ^ (130 + 130 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 130 * (34 : ZMod 1574773201) ^ 130) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 382042311 := by rw [factor_7_7]; decide
      have factor_7_9 : (34 : ZMod 1574773201) ^ 522 = 789540691 := by
        calc
          (34 : ZMod 1574773201) ^ 522 = (34 : ZMod 1574773201) ^ (261 + 261) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 261 * (34 : ZMod 1574773201) ^ 261 := by rw [pow_add]
          _ = 789540691 := by rw [factor_7_8]; decide
      have factor_7_10 : (34 : ZMod 1574773201) ^ 1044 = 430338744 := by
        calc
          (34 : ZMod 1574773201) ^ 1044 = (34 : ZMod 1574773201) ^ (522 + 522) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 522 * (34 : ZMod 1574773201) ^ 522 := by rw [pow_add]
          _ = 430338744 := by rw [factor_7_9]; decide
      have factor_7_11 : (34 : ZMod 1574773201) ^ 2089 = 1572705114 := by
        calc
          (34 : ZMod 1574773201) ^ 2089 = (34 : ZMod 1574773201) ^ (1044 + 1044 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 1044 * (34 : ZMod 1574773201) ^ 1044) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1572705114 := by rw [factor_7_10]; decide
      have factor_7_12 : (34 : ZMod 1574773201) ^ 4178 = 1474598854 := by
        calc
          (34 : ZMod 1574773201) ^ 4178 = (34 : ZMod 1574773201) ^ (2089 + 2089) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 2089 * (34 : ZMod 1574773201) ^ 2089 := by rw [pow_add]
          _ = 1474598854 := by rw [factor_7_11]; decide
      have factor_7_13 : (34 : ZMod 1574773201) ^ 8357 = 1372181100 := by
        calc
          (34 : ZMod 1574773201) ^ 8357 = (34 : ZMod 1574773201) ^ (4178 + 4178 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 4178 * (34 : ZMod 1574773201) ^ 4178) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1372181100 := by rw [factor_7_12]; decide
      have factor_7_14 : (34 : ZMod 1574773201) ^ 16715 = 574468735 := by
        calc
          (34 : ZMod 1574773201) ^ 16715 = (34 : ZMod 1574773201) ^ (8357 + 8357 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 8357 * (34 : ZMod 1574773201) ^ 8357) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 574468735 := by rw [factor_7_13]; decide
      have factor_7_15 : (34 : ZMod 1574773201) ^ 33431 = 67760418 := by
        calc
          (34 : ZMod 1574773201) ^ 33431 = (34 : ZMod 1574773201) ^ (16715 + 16715 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 16715 * (34 : ZMod 1574773201) ^ 16715) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 67760418 := by rw [factor_7_14]; decide
      have factor_7_16 : (34 : ZMod 1574773201) ^ 66863 = 362464002 := by
        calc
          (34 : ZMod 1574773201) ^ 66863 = (34 : ZMod 1574773201) ^ (33431 + 33431 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 33431 * (34 : ZMod 1574773201) ^ 33431) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 362464002 := by rw [factor_7_15]; decide
      have factor_7_17 : (34 : ZMod 1574773201) ^ 133727 = 814371495 := by
        calc
          (34 : ZMod 1574773201) ^ 133727 = (34 : ZMod 1574773201) ^ (66863 + 66863 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 66863 * (34 : ZMod 1574773201) ^ 66863) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 814371495 := by rw [factor_7_16]; decide
      have factor_7_18 : (34 : ZMod 1574773201) ^ 267454 = 1135474425 := by
        calc
          (34 : ZMod 1574773201) ^ 267454 = (34 : ZMod 1574773201) ^ (133727 + 133727) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 133727 * (34 : ZMod 1574773201) ^ 133727 := by rw [pow_add]
          _ = 1135474425 := by rw [factor_7_17]; decide
      have factor_7_19 : (34 : ZMod 1574773201) ^ 534909 = 1091381226 := by
        calc
          (34 : ZMod 1574773201) ^ 534909 = (34 : ZMod 1574773201) ^ (267454 + 267454 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 267454 * (34 : ZMod 1574773201) ^ 267454) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1091381226 := by rw [factor_7_18]; decide
      have factor_7_20 : (34 : ZMod 1574773201) ^ 1069818 = 1230268750 := by
        calc
          (34 : ZMod 1574773201) ^ 1069818 = (34 : ZMod 1574773201) ^ (534909 + 534909) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 534909 * (34 : ZMod 1574773201) ^ 534909 := by rw [pow_add]
          _ = 1230268750 := by rw [factor_7_19]; decide
      have factor_7_21 : (34 : ZMod 1574773201) ^ 2139637 = 517211295 := by
        calc
          (34 : ZMod 1574773201) ^ 2139637 = (34 : ZMod 1574773201) ^ (1069818 + 1069818 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 1069818 * (34 : ZMod 1574773201) ^ 1069818) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 517211295 := by rw [factor_7_20]; decide
      have factor_7_22 : (34 : ZMod 1574773201) ^ 4279275 = 1255311178 := by
        calc
          (34 : ZMod 1574773201) ^ 4279275 = (34 : ZMod 1574773201) ^ (2139637 + 2139637 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = ((34 : ZMod 1574773201) ^ 2139637 * (34 : ZMod 1574773201) ^ 2139637) * (34 : ZMod 1574773201) := by rw [pow_succ, pow_add]
          _ = 1255311178 := by rw [factor_7_21]; decide
      have factor_7_23 : (34 : ZMod 1574773201) ^ 8558550 = 602603347 := by
        calc
          (34 : ZMod 1574773201) ^ 8558550 = (34 : ZMod 1574773201) ^ (4279275 + 4279275) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 4279275 * (34 : ZMod 1574773201) ^ 4279275 := by rw [pow_add]
          _ = 602603347 := by rw [factor_7_22]; decide
      have factor_7_24 : (34 : ZMod 1574773201) ^ 17117100 = 525175170 := by
        calc
          (34 : ZMod 1574773201) ^ 17117100 = (34 : ZMod 1574773201) ^ (8558550 + 8558550) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 8558550 * (34 : ZMod 1574773201) ^ 8558550 := by rw [pow_add]
          _ = 525175170 := by rw [factor_7_23]; decide
      have factor_7_25 : (34 : ZMod 1574773201) ^ 34234200 = 1294296081 := by
        calc
          (34 : ZMod 1574773201) ^ 34234200 = (34 : ZMod 1574773201) ^ (17117100 + 17117100) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 17117100 * (34 : ZMod 1574773201) ^ 17117100 := by rw [pow_add]
          _ = 1294296081 := by rw [factor_7_24]; decide
      have factor_7_26 : (34 : ZMod 1574773201) ^ 68468400 = 682654042 := by
        calc
          (34 : ZMod 1574773201) ^ 68468400 = (34 : ZMod 1574773201) ^ (34234200 + 34234200) :=
            congrArg (fun n : ℕ => (34 : ZMod 1574773201) ^ n) (by norm_num)
          _ = (34 : ZMod 1574773201) ^ 34234200 * (34 : ZMod 1574773201) ^ 34234200 := by rw [pow_add]
          _ = 682654042 := by rw [factor_7_25]; decide
      change (34 : ZMod 1574773201) ^ 68468400 ≠ 1
      rw [factor_7_26]
      decide

#print axioms prime_lucas_1574773201

end TotientTailPeriodKiller
end Erdos249257
