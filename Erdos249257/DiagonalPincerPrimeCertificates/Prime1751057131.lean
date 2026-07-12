import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime58368571

/-! A bounded Lucas certificate for one t=32 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1751057131 : Nat.Prime 1751057131 := by
  apply lucas_primality 1751057131 (2 : ZMod 1751057131)
  ·
      have fermat_0 : (2 : ZMod 1751057131) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 1751057131) ^ 3 = 8 := by
        calc
          (2 : ZMod 1751057131) ^ 3 = (2 : ZMod 1751057131) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 1 * (2 : ZMod 1751057131) ^ 1) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 1751057131) ^ 6 = 64 := by
        calc
          (2 : ZMod 1751057131) ^ 6 = (2 : ZMod 1751057131) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 3 * (2 : ZMod 1751057131) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 1751057131) ^ 13 = 8192 := by
        calc
          (2 : ZMod 1751057131) ^ 13 = (2 : ZMod 1751057131) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 6 * (2 : ZMod 1751057131) ^ 6) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 1751057131) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 1751057131) ^ 26 = (2 : ZMod 1751057131) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 13 * (2 : ZMod 1751057131) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 1751057131) ^ 52 = 1509380535 := by
        calc
          (2 : ZMod 1751057131) ^ 52 = (2 : ZMod 1751057131) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 26 * (2 : ZMod 1751057131) ^ 26 := by rw [pow_add]
          _ = 1509380535 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 1751057131) ^ 104 = 55849437 := by
        calc
          (2 : ZMod 1751057131) ^ 104 = (2 : ZMod 1751057131) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 52 * (2 : ZMod 1751057131) ^ 52 := by rw [pow_add]
          _ = 55849437 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 1751057131) ^ 208 = 1545766669 := by
        calc
          (2 : ZMod 1751057131) ^ 208 = (2 : ZMod 1751057131) ^ (104 + 104) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 104 * (2 : ZMod 1751057131) ^ 104 := by rw [pow_add]
          _ = 1545766669 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 1751057131) ^ 417 = 844127236 := by
        calc
          (2 : ZMod 1751057131) ^ 417 = (2 : ZMod 1751057131) ^ (208 + 208 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 208 * (2 : ZMod 1751057131) ^ 208) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 844127236 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 1751057131) ^ 834 = 897923050 := by
        calc
          (2 : ZMod 1751057131) ^ 834 = (2 : ZMod 1751057131) ^ (417 + 417) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 417 * (2 : ZMod 1751057131) ^ 417 := by rw [pow_add]
          _ = 897923050 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 1751057131) ^ 1669 = 210247674 := by
        calc
          (2 : ZMod 1751057131) ^ 1669 = (2 : ZMod 1751057131) ^ (834 + 834 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 834 * (2 : ZMod 1751057131) ^ 834) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 210247674 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 1751057131) ^ 3339 = 1434955078 := by
        calc
          (2 : ZMod 1751057131) ^ 3339 = (2 : ZMod 1751057131) ^ (1669 + 1669 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 1669 * (2 : ZMod 1751057131) ^ 1669) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1434955078 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 1751057131) ^ 6679 = 1018408443 := by
        calc
          (2 : ZMod 1751057131) ^ 6679 = (2 : ZMod 1751057131) ^ (3339 + 3339 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 3339 * (2 : ZMod 1751057131) ^ 3339) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1018408443 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 1751057131) ^ 13359 = 1089459604 := by
        calc
          (2 : ZMod 1751057131) ^ 13359 = (2 : ZMod 1751057131) ^ (6679 + 6679 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 6679 * (2 : ZMod 1751057131) ^ 6679) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1089459604 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 1751057131) ^ 26719 = 1453170888 := by
        calc
          (2 : ZMod 1751057131) ^ 26719 = (2 : ZMod 1751057131) ^ (13359 + 13359 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 13359 * (2 : ZMod 1751057131) ^ 13359) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1453170888 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 1751057131) ^ 53438 = 1564810904 := by
        calc
          (2 : ZMod 1751057131) ^ 53438 = (2 : ZMod 1751057131) ^ (26719 + 26719) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 26719 * (2 : ZMod 1751057131) ^ 26719 := by rw [pow_add]
          _ = 1564810904 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 1751057131) ^ 106876 = 1531277348 := by
        calc
          (2 : ZMod 1751057131) ^ 106876 = (2 : ZMod 1751057131) ^ (53438 + 53438) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 53438 * (2 : ZMod 1751057131) ^ 53438 := by rw [pow_add]
          _ = 1531277348 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 1751057131) ^ 213752 = 411008011 := by
        calc
          (2 : ZMod 1751057131) ^ 213752 = (2 : ZMod 1751057131) ^ (106876 + 106876) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 106876 * (2 : ZMod 1751057131) ^ 106876 := by rw [pow_add]
          _ = 411008011 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 1751057131) ^ 427504 = 805369989 := by
        calc
          (2 : ZMod 1751057131) ^ 427504 = (2 : ZMod 1751057131) ^ (213752 + 213752) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 213752 * (2 : ZMod 1751057131) ^ 213752 := by rw [pow_add]
          _ = 805369989 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 1751057131) ^ 855008 = 1196915373 := by
        calc
          (2 : ZMod 1751057131) ^ 855008 = (2 : ZMod 1751057131) ^ (427504 + 427504) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 427504 * (2 : ZMod 1751057131) ^ 427504 := by rw [pow_add]
          _ = 1196915373 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 1751057131) ^ 1710016 = 1313679902 := by
        calc
          (2 : ZMod 1751057131) ^ 1710016 = (2 : ZMod 1751057131) ^ (855008 + 855008) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 855008 * (2 : ZMod 1751057131) ^ 855008 := by rw [pow_add]
          _ = 1313679902 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 1751057131) ^ 3420033 = 1284852084 := by
        calc
          (2 : ZMod 1751057131) ^ 3420033 = (2 : ZMod 1751057131) ^ (1710016 + 1710016 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 1710016 * (2 : ZMod 1751057131) ^ 1710016) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1284852084 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 1751057131) ^ 6840066 = 415935250 := by
        calc
          (2 : ZMod 1751057131) ^ 6840066 = (2 : ZMod 1751057131) ^ (3420033 + 3420033) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 3420033 * (2 : ZMod 1751057131) ^ 3420033 := by rw [pow_add]
          _ = 415935250 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 1751057131) ^ 13680133 = 1592465102 := by
        calc
          (2 : ZMod 1751057131) ^ 13680133 = (2 : ZMod 1751057131) ^ (6840066 + 6840066 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 6840066 * (2 : ZMod 1751057131) ^ 6840066) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1592465102 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 1751057131) ^ 27360267 = 1725495473 := by
        calc
          (2 : ZMod 1751057131) ^ 27360267 = (2 : ZMod 1751057131) ^ (13680133 + 13680133 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 13680133 * (2 : ZMod 1751057131) ^ 13680133) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1725495473 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 1751057131) ^ 54720535 = 293123938 := by
        calc
          (2 : ZMod 1751057131) ^ 54720535 = (2 : ZMod 1751057131) ^ (27360267 + 27360267 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 27360267 * (2 : ZMod 1751057131) ^ 27360267) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 293123938 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 1751057131) ^ 109441070 = 1259582204 := by
        calc
          (2 : ZMod 1751057131) ^ 109441070 = (2 : ZMod 1751057131) ^ (54720535 + 54720535) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 54720535 * (2 : ZMod 1751057131) ^ 54720535 := by rw [pow_add]
          _ = 1259582204 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 1751057131) ^ 218882141 = 999436801 := by
        calc
          (2 : ZMod 1751057131) ^ 218882141 = (2 : ZMod 1751057131) ^ (109441070 + 109441070 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 109441070 * (2 : ZMod 1751057131) ^ 109441070) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 999436801 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 1751057131) ^ 437764282 = 1599508184 := by
        calc
          (2 : ZMod 1751057131) ^ 437764282 = (2 : ZMod 1751057131) ^ (218882141 + 218882141) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 218882141 * (2 : ZMod 1751057131) ^ 218882141 := by rw [pow_add]
          _ = 1599508184 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 1751057131) ^ 875528565 = 1751057130 := by
        calc
          (2 : ZMod 1751057131) ^ 875528565 = (2 : ZMod 1751057131) ^ (437764282 + 437764282 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 437764282 * (2 : ZMod 1751057131) ^ 437764282) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1751057130 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 1751057131) ^ 1751057130 = 1 := by
        calc
          (2 : ZMod 1751057131) ^ 1751057130 = (2 : ZMod 1751057131) ^ (875528565 + 875528565) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 875528565 * (2 : ZMod 1751057131) ^ 875528565 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (58368571, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (58368571, 1)] : List FactorBlock).map factorBlockValue).prod = 1751057131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_58368571) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 1751057131) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 1751057131) ^ 3 = 8 := by
        calc
          (2 : ZMod 1751057131) ^ 3 = (2 : ZMod 1751057131) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 1 * (2 : ZMod 1751057131) ^ 1) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 1751057131) ^ 6 = 64 := by
        calc
          (2 : ZMod 1751057131) ^ 6 = (2 : ZMod 1751057131) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 3 * (2 : ZMod 1751057131) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 1751057131) ^ 13 = 8192 := by
        calc
          (2 : ZMod 1751057131) ^ 13 = (2 : ZMod 1751057131) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 6 * (2 : ZMod 1751057131) ^ 6) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 1751057131) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 1751057131) ^ 26 = (2 : ZMod 1751057131) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 13 * (2 : ZMod 1751057131) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 1751057131) ^ 52 = 1509380535 := by
        calc
          (2 : ZMod 1751057131) ^ 52 = (2 : ZMod 1751057131) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 26 * (2 : ZMod 1751057131) ^ 26 := by rw [pow_add]
          _ = 1509380535 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 1751057131) ^ 104 = 55849437 := by
        calc
          (2 : ZMod 1751057131) ^ 104 = (2 : ZMod 1751057131) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 52 * (2 : ZMod 1751057131) ^ 52 := by rw [pow_add]
          _ = 55849437 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 1751057131) ^ 208 = 1545766669 := by
        calc
          (2 : ZMod 1751057131) ^ 208 = (2 : ZMod 1751057131) ^ (104 + 104) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 104 * (2 : ZMod 1751057131) ^ 104 := by rw [pow_add]
          _ = 1545766669 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 1751057131) ^ 417 = 844127236 := by
        calc
          (2 : ZMod 1751057131) ^ 417 = (2 : ZMod 1751057131) ^ (208 + 208 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 208 * (2 : ZMod 1751057131) ^ 208) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 844127236 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 1751057131) ^ 834 = 897923050 := by
        calc
          (2 : ZMod 1751057131) ^ 834 = (2 : ZMod 1751057131) ^ (417 + 417) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 417 * (2 : ZMod 1751057131) ^ 417 := by rw [pow_add]
          _ = 897923050 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 1751057131) ^ 1669 = 210247674 := by
        calc
          (2 : ZMod 1751057131) ^ 1669 = (2 : ZMod 1751057131) ^ (834 + 834 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 834 * (2 : ZMod 1751057131) ^ 834) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 210247674 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 1751057131) ^ 3339 = 1434955078 := by
        calc
          (2 : ZMod 1751057131) ^ 3339 = (2 : ZMod 1751057131) ^ (1669 + 1669 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 1669 * (2 : ZMod 1751057131) ^ 1669) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1434955078 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 1751057131) ^ 6679 = 1018408443 := by
        calc
          (2 : ZMod 1751057131) ^ 6679 = (2 : ZMod 1751057131) ^ (3339 + 3339 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 3339 * (2 : ZMod 1751057131) ^ 3339) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1018408443 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 1751057131) ^ 13359 = 1089459604 := by
        calc
          (2 : ZMod 1751057131) ^ 13359 = (2 : ZMod 1751057131) ^ (6679 + 6679 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 6679 * (2 : ZMod 1751057131) ^ 6679) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1089459604 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 1751057131) ^ 26719 = 1453170888 := by
        calc
          (2 : ZMod 1751057131) ^ 26719 = (2 : ZMod 1751057131) ^ (13359 + 13359 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 13359 * (2 : ZMod 1751057131) ^ 13359) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1453170888 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 1751057131) ^ 53438 = 1564810904 := by
        calc
          (2 : ZMod 1751057131) ^ 53438 = (2 : ZMod 1751057131) ^ (26719 + 26719) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 26719 * (2 : ZMod 1751057131) ^ 26719 := by rw [pow_add]
          _ = 1564810904 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 1751057131) ^ 106876 = 1531277348 := by
        calc
          (2 : ZMod 1751057131) ^ 106876 = (2 : ZMod 1751057131) ^ (53438 + 53438) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 53438 * (2 : ZMod 1751057131) ^ 53438 := by rw [pow_add]
          _ = 1531277348 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 1751057131) ^ 213752 = 411008011 := by
        calc
          (2 : ZMod 1751057131) ^ 213752 = (2 : ZMod 1751057131) ^ (106876 + 106876) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 106876 * (2 : ZMod 1751057131) ^ 106876 := by rw [pow_add]
          _ = 411008011 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 1751057131) ^ 427504 = 805369989 := by
        calc
          (2 : ZMod 1751057131) ^ 427504 = (2 : ZMod 1751057131) ^ (213752 + 213752) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 213752 * (2 : ZMod 1751057131) ^ 213752 := by rw [pow_add]
          _ = 805369989 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 1751057131) ^ 855008 = 1196915373 := by
        calc
          (2 : ZMod 1751057131) ^ 855008 = (2 : ZMod 1751057131) ^ (427504 + 427504) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 427504 * (2 : ZMod 1751057131) ^ 427504 := by rw [pow_add]
          _ = 1196915373 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 1751057131) ^ 1710016 = 1313679902 := by
        calc
          (2 : ZMod 1751057131) ^ 1710016 = (2 : ZMod 1751057131) ^ (855008 + 855008) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 855008 * (2 : ZMod 1751057131) ^ 855008 := by rw [pow_add]
          _ = 1313679902 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 1751057131) ^ 3420033 = 1284852084 := by
        calc
          (2 : ZMod 1751057131) ^ 3420033 = (2 : ZMod 1751057131) ^ (1710016 + 1710016 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 1710016 * (2 : ZMod 1751057131) ^ 1710016) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1284852084 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 1751057131) ^ 6840066 = 415935250 := by
        calc
          (2 : ZMod 1751057131) ^ 6840066 = (2 : ZMod 1751057131) ^ (3420033 + 3420033) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 3420033 * (2 : ZMod 1751057131) ^ 3420033 := by rw [pow_add]
          _ = 415935250 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 1751057131) ^ 13680133 = 1592465102 := by
        calc
          (2 : ZMod 1751057131) ^ 13680133 = (2 : ZMod 1751057131) ^ (6840066 + 6840066 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 6840066 * (2 : ZMod 1751057131) ^ 6840066) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1592465102 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 1751057131) ^ 27360267 = 1725495473 := by
        calc
          (2 : ZMod 1751057131) ^ 27360267 = (2 : ZMod 1751057131) ^ (13680133 + 13680133 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 13680133 * (2 : ZMod 1751057131) ^ 13680133) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1725495473 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 1751057131) ^ 54720535 = 293123938 := by
        calc
          (2 : ZMod 1751057131) ^ 54720535 = (2 : ZMod 1751057131) ^ (27360267 + 27360267 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 27360267 * (2 : ZMod 1751057131) ^ 27360267) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 293123938 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 1751057131) ^ 109441070 = 1259582204 := by
        calc
          (2 : ZMod 1751057131) ^ 109441070 = (2 : ZMod 1751057131) ^ (54720535 + 54720535) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 54720535 * (2 : ZMod 1751057131) ^ 54720535 := by rw [pow_add]
          _ = 1259582204 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 1751057131) ^ 218882141 = 999436801 := by
        calc
          (2 : ZMod 1751057131) ^ 218882141 = (2 : ZMod 1751057131) ^ (109441070 + 109441070 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 109441070 * (2 : ZMod 1751057131) ^ 109441070) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 999436801 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 1751057131) ^ 437764282 = 1599508184 := by
        calc
          (2 : ZMod 1751057131) ^ 437764282 = (2 : ZMod 1751057131) ^ (218882141 + 218882141) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 218882141 * (2 : ZMod 1751057131) ^ 218882141 := by rw [pow_add]
          _ = 1599508184 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 1751057131) ^ 875528565 = 1751057130 := by
        calc
          (2 : ZMod 1751057131) ^ 875528565 = (2 : ZMod 1751057131) ^ (437764282 + 437764282 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 437764282 * (2 : ZMod 1751057131) ^ 437764282) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1751057130 := by rw [factor_0_28]; decide
      change (2 : ZMod 1751057131) ^ 875528565 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (2 : ZMod 1751057131) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 1751057131) ^ 2 = 4 := by
        calc
          (2 : ZMod 1751057131) ^ 2 = (2 : ZMod 1751057131) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 1 * (2 : ZMod 1751057131) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 1751057131) ^ 4 = 16 := by
        calc
          (2 : ZMod 1751057131) ^ 4 = (2 : ZMod 1751057131) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 2 * (2 : ZMod 1751057131) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 1751057131) ^ 8 = 256 := by
        calc
          (2 : ZMod 1751057131) ^ 8 = (2 : ZMod 1751057131) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 4 * (2 : ZMod 1751057131) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 1751057131) ^ 17 = 131072 := by
        calc
          (2 : ZMod 1751057131) ^ 17 = (2 : ZMod 1751057131) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 8 * (2 : ZMod 1751057131) ^ 8) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 1751057131) ^ 34 = 1420355005 := by
        calc
          (2 : ZMod 1751057131) ^ 34 = (2 : ZMod 1751057131) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 17 * (2 : ZMod 1751057131) ^ 17 := by rw [pow_add]
          _ = 1420355005 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 1751057131) ^ 69 = 1339766009 := by
        calc
          (2 : ZMod 1751057131) ^ 69 = (2 : ZMod 1751057131) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 34 * (2 : ZMod 1751057131) ^ 34) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1339766009 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 1751057131) ^ 139 = 1130349735 := by
        calc
          (2 : ZMod 1751057131) ^ 139 = (2 : ZMod 1751057131) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 69 * (2 : ZMod 1751057131) ^ 69) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1130349735 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 1751057131) ^ 278 = 650577649 := by
        calc
          (2 : ZMod 1751057131) ^ 278 = (2 : ZMod 1751057131) ^ (139 + 139) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 139 * (2 : ZMod 1751057131) ^ 139 := by rw [pow_add]
          _ = 650577649 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 1751057131) ^ 556 = 1278093541 := by
        calc
          (2 : ZMod 1751057131) ^ 556 = (2 : ZMod 1751057131) ^ (278 + 278) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 278 * (2 : ZMod 1751057131) ^ 278 := by rw [pow_add]
          _ = 1278093541 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 1751057131) ^ 1113 = 1323092827 := by
        calc
          (2 : ZMod 1751057131) ^ 1113 = (2 : ZMod 1751057131) ^ (556 + 556 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 556 * (2 : ZMod 1751057131) ^ 556) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1323092827 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 1751057131) ^ 2226 = 1651298979 := by
        calc
          (2 : ZMod 1751057131) ^ 2226 = (2 : ZMod 1751057131) ^ (1113 + 1113) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 1113 * (2 : ZMod 1751057131) ^ 1113 := by rw [pow_add]
          _ = 1651298979 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 1751057131) ^ 4453 = 909855756 := by
        calc
          (2 : ZMod 1751057131) ^ 4453 = (2 : ZMod 1751057131) ^ (2226 + 2226 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 2226 * (2 : ZMod 1751057131) ^ 2226) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 909855756 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 1751057131) ^ 8906 = 59652433 := by
        calc
          (2 : ZMod 1751057131) ^ 8906 = (2 : ZMod 1751057131) ^ (4453 + 4453) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 4453 * (2 : ZMod 1751057131) ^ 4453 := by rw [pow_add]
          _ = 59652433 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 1751057131) ^ 17812 = 263000708 := by
        calc
          (2 : ZMod 1751057131) ^ 17812 = (2 : ZMod 1751057131) ^ (8906 + 8906) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 8906 * (2 : ZMod 1751057131) ^ 8906 := by rw [pow_add]
          _ = 263000708 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 1751057131) ^ 35625 = 1060352231 := by
        calc
          (2 : ZMod 1751057131) ^ 35625 = (2 : ZMod 1751057131) ^ (17812 + 17812 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 17812 * (2 : ZMod 1751057131) ^ 17812) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1060352231 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 1751057131) ^ 71250 = 655701859 := by
        calc
          (2 : ZMod 1751057131) ^ 71250 = (2 : ZMod 1751057131) ^ (35625 + 35625) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 35625 * (2 : ZMod 1751057131) ^ 35625 := by rw [pow_add]
          _ = 655701859 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 1751057131) ^ 142501 = 790701203 := by
        calc
          (2 : ZMod 1751057131) ^ 142501 = (2 : ZMod 1751057131) ^ (71250 + 71250 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 71250 * (2 : ZMod 1751057131) ^ 71250) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 790701203 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 1751057131) ^ 285002 = 1511052804 := by
        calc
          (2 : ZMod 1751057131) ^ 285002 = (2 : ZMod 1751057131) ^ (142501 + 142501) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 142501 * (2 : ZMod 1751057131) ^ 142501 := by rw [pow_add]
          _ = 1511052804 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 1751057131) ^ 570005 = 538284396 := by
        calc
          (2 : ZMod 1751057131) ^ 570005 = (2 : ZMod 1751057131) ^ (285002 + 285002 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 285002 * (2 : ZMod 1751057131) ^ 285002) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 538284396 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 1751057131) ^ 1140011 = 1301008606 := by
        calc
          (2 : ZMod 1751057131) ^ 1140011 = (2 : ZMod 1751057131) ^ (570005 + 570005 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 570005 * (2 : ZMod 1751057131) ^ 570005) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1301008606 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 1751057131) ^ 2280022 = 1428955286 := by
        calc
          (2 : ZMod 1751057131) ^ 2280022 = (2 : ZMod 1751057131) ^ (1140011 + 1140011) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 1140011 * (2 : ZMod 1751057131) ^ 1140011 := by rw [pow_add]
          _ = 1428955286 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 1751057131) ^ 4560044 = 1115193242 := by
        calc
          (2 : ZMod 1751057131) ^ 4560044 = (2 : ZMod 1751057131) ^ (2280022 + 2280022) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 2280022 * (2 : ZMod 1751057131) ^ 2280022 := by rw [pow_add]
          _ = 1115193242 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 1751057131) ^ 9120089 = 242060019 := by
        calc
          (2 : ZMod 1751057131) ^ 9120089 = (2 : ZMod 1751057131) ^ (4560044 + 4560044 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 4560044 * (2 : ZMod 1751057131) ^ 4560044) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 242060019 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 1751057131) ^ 18240178 = 326552800 := by
        calc
          (2 : ZMod 1751057131) ^ 18240178 = (2 : ZMod 1751057131) ^ (9120089 + 9120089) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 9120089 * (2 : ZMod 1751057131) ^ 9120089 := by rw [pow_add]
          _ = 326552800 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 1751057131) ^ 36480356 = 1259379203 := by
        calc
          (2 : ZMod 1751057131) ^ 36480356 = (2 : ZMod 1751057131) ^ (18240178 + 18240178) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 18240178 * (2 : ZMod 1751057131) ^ 18240178 := by rw [pow_add]
          _ = 1259379203 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 1751057131) ^ 72960713 = 796575406 := by
        calc
          (2 : ZMod 1751057131) ^ 72960713 = (2 : ZMod 1751057131) ^ (36480356 + 36480356 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 36480356 * (2 : ZMod 1751057131) ^ 36480356) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 796575406 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 1751057131) ^ 145921427 = 838442681 := by
        calc
          (2 : ZMod 1751057131) ^ 145921427 = (2 : ZMod 1751057131) ^ (72960713 + 72960713 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 72960713 * (2 : ZMod 1751057131) ^ 72960713) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 838442681 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 1751057131) ^ 291842855 = 1393078132 := by
        calc
          (2 : ZMod 1751057131) ^ 291842855 = (2 : ZMod 1751057131) ^ (145921427 + 145921427 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 145921427 * (2 : ZMod 1751057131) ^ 145921427) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1393078132 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 1751057131) ^ 583685710 = 1393078131 := by
        calc
          (2 : ZMod 1751057131) ^ 583685710 = (2 : ZMod 1751057131) ^ (291842855 + 291842855) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 291842855 * (2 : ZMod 1751057131) ^ 291842855 := by rw [pow_add]
          _ = 1393078131 := by rw [factor_1_28]; decide
      change (2 : ZMod 1751057131) ^ 583685710 ≠ 1
      rw [factor_1_29]
      decide
    ·
      have factor_2_0 : (2 : ZMod 1751057131) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 1751057131) ^ 2 = 4 := by
        calc
          (2 : ZMod 1751057131) ^ 2 = (2 : ZMod 1751057131) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 1 * (2 : ZMod 1751057131) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 1751057131) ^ 5 = 32 := by
        calc
          (2 : ZMod 1751057131) ^ 5 = (2 : ZMod 1751057131) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 2 * (2 : ZMod 1751057131) ^ 2) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 1751057131) ^ 10 = 1024 := by
        calc
          (2 : ZMod 1751057131) ^ 10 = (2 : ZMod 1751057131) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 5 * (2 : ZMod 1751057131) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 1751057131) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 1751057131) ^ 20 = (2 : ZMod 1751057131) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 10 * (2 : ZMod 1751057131) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 1751057131) ^ 41 = 1446556147 := by
        calc
          (2 : ZMod 1751057131) ^ 41 = (2 : ZMod 1751057131) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 20 * (2 : ZMod 1751057131) ^ 20) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1446556147 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 1751057131) ^ 83 = 1225154371 := by
        calc
          (2 : ZMod 1751057131) ^ 83 = (2 : ZMod 1751057131) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 41 * (2 : ZMod 1751057131) ^ 41) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1225154371 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 1751057131) ^ 166 = 112128590 := by
        calc
          (2 : ZMod 1751057131) ^ 166 = (2 : ZMod 1751057131) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 83 * (2 : ZMod 1751057131) ^ 83 := by rw [pow_add]
          _ = 112128590 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 1751057131) ^ 333 = 461590747 := by
        calc
          (2 : ZMod 1751057131) ^ 333 = (2 : ZMod 1751057131) ^ (166 + 166 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 166 * (2 : ZMod 1751057131) ^ 166) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 461590747 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 1751057131) ^ 667 = 688469184 := by
        calc
          (2 : ZMod 1751057131) ^ 667 = (2 : ZMod 1751057131) ^ (333 + 333 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 333 * (2 : ZMod 1751057131) ^ 333) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 688469184 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 1751057131) ^ 1335 = 1688934016 := by
        calc
          (2 : ZMod 1751057131) ^ 1335 = (2 : ZMod 1751057131) ^ (667 + 667 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 667 * (2 : ZMod 1751057131) ^ 667) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1688934016 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 1751057131) ^ 2671 = 1060357786 := by
        calc
          (2 : ZMod 1751057131) ^ 2671 = (2 : ZMod 1751057131) ^ (1335 + 1335 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 1335 * (2 : ZMod 1751057131) ^ 1335) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1060357786 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 1751057131) ^ 5343 = 174937852 := by
        calc
          (2 : ZMod 1751057131) ^ 5343 = (2 : ZMod 1751057131) ^ (2671 + 2671 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 2671 * (2 : ZMod 1751057131) ^ 2671) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 174937852 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 1751057131) ^ 10687 = 636059878 := by
        calc
          (2 : ZMod 1751057131) ^ 10687 = (2 : ZMod 1751057131) ^ (5343 + 5343 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 5343 * (2 : ZMod 1751057131) ^ 5343) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 636059878 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 1751057131) ^ 21375 = 136891432 := by
        calc
          (2 : ZMod 1751057131) ^ 21375 = (2 : ZMod 1751057131) ^ (10687 + 10687 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 10687 * (2 : ZMod 1751057131) ^ 10687) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 136891432 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 1751057131) ^ 42750 = 570987758 := by
        calc
          (2 : ZMod 1751057131) ^ 42750 = (2 : ZMod 1751057131) ^ (21375 + 21375) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 21375 * (2 : ZMod 1751057131) ^ 21375 := by rw [pow_add]
          _ = 570987758 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 1751057131) ^ 85500 = 458275222 := by
        calc
          (2 : ZMod 1751057131) ^ 85500 = (2 : ZMod 1751057131) ^ (42750 + 42750) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 42750 * (2 : ZMod 1751057131) ^ 42750 := by rw [pow_add]
          _ = 458275222 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 1751057131) ^ 171001 = 1392342540 := by
        calc
          (2 : ZMod 1751057131) ^ 171001 = (2 : ZMod 1751057131) ^ (85500 + 85500 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 85500 * (2 : ZMod 1751057131) ^ 85500) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1392342540 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 1751057131) ^ 342003 = 632520827 := by
        calc
          (2 : ZMod 1751057131) ^ 342003 = (2 : ZMod 1751057131) ^ (171001 + 171001 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 171001 * (2 : ZMod 1751057131) ^ 171001) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 632520827 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 1751057131) ^ 684006 = 406205412 := by
        calc
          (2 : ZMod 1751057131) ^ 684006 = (2 : ZMod 1751057131) ^ (342003 + 342003) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 342003 * (2 : ZMod 1751057131) ^ 342003 := by rw [pow_add]
          _ = 406205412 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 1751057131) ^ 1368013 = 194729282 := by
        calc
          (2 : ZMod 1751057131) ^ 1368013 = (2 : ZMod 1751057131) ^ (684006 + 684006 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 684006 * (2 : ZMod 1751057131) ^ 684006) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 194729282 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 1751057131) ^ 2736026 = 885004324 := by
        calc
          (2 : ZMod 1751057131) ^ 2736026 = (2 : ZMod 1751057131) ^ (1368013 + 1368013) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 1368013 * (2 : ZMod 1751057131) ^ 1368013 := by rw [pow_add]
          _ = 885004324 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 1751057131) ^ 5472053 = 1209759505 := by
        calc
          (2 : ZMod 1751057131) ^ 5472053 = (2 : ZMod 1751057131) ^ (2736026 + 2736026 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 2736026 * (2 : ZMod 1751057131) ^ 2736026) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1209759505 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 1751057131) ^ 10944107 = 1149908833 := by
        calc
          (2 : ZMod 1751057131) ^ 10944107 = (2 : ZMod 1751057131) ^ (5472053 + 5472053 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 5472053 * (2 : ZMod 1751057131) ^ 5472053) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1149908833 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 1751057131) ^ 21888214 = 1594633279 := by
        calc
          (2 : ZMod 1751057131) ^ 21888214 = (2 : ZMod 1751057131) ^ (10944107 + 10944107) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 10944107 * (2 : ZMod 1751057131) ^ 10944107 := by rw [pow_add]
          _ = 1594633279 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 1751057131) ^ 43776428 = 139689570 := by
        calc
          (2 : ZMod 1751057131) ^ 43776428 = (2 : ZMod 1751057131) ^ (21888214 + 21888214) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 21888214 * (2 : ZMod 1751057131) ^ 21888214 := by rw [pow_add]
          _ = 139689570 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 1751057131) ^ 87552856 = 1164688226 := by
        calc
          (2 : ZMod 1751057131) ^ 87552856 = (2 : ZMod 1751057131) ^ (43776428 + 43776428) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 43776428 * (2 : ZMod 1751057131) ^ 43776428 := by rw [pow_add]
          _ = 1164688226 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 1751057131) ^ 175105713 = 1486383568 := by
        calc
          (2 : ZMod 1751057131) ^ 175105713 = (2 : ZMod 1751057131) ^ (87552856 + 87552856 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 87552856 * (2 : ZMod 1751057131) ^ 87552856) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 1486383568 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 1751057131) ^ 350211426 = 289067107 := by
        calc
          (2 : ZMod 1751057131) ^ 350211426 = (2 : ZMod 1751057131) ^ (175105713 + 175105713) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 175105713 * (2 : ZMod 1751057131) ^ 175105713 := by rw [pow_add]
          _ = 289067107 := by rw [factor_2_27]; decide
      change (2 : ZMod 1751057131) ^ 350211426 ≠ 1
      rw [factor_2_28]
      decide
    ·
      have factor_3_0 : (2 : ZMod 1751057131) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 1751057131) ^ 3 = 8 := by
        calc
          (2 : ZMod 1751057131) ^ 3 = (2 : ZMod 1751057131) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 1 * (2 : ZMod 1751057131) ^ 1) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 1751057131) ^ 7 = 128 := by
        calc
          (2 : ZMod 1751057131) ^ 7 = (2 : ZMod 1751057131) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 3 * (2 : ZMod 1751057131) ^ 3) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 1751057131) ^ 15 = 32768 := by
        calc
          (2 : ZMod 1751057131) ^ 15 = (2 : ZMod 1751057131) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = ((2 : ZMod 1751057131) ^ 7 * (2 : ZMod 1751057131) ^ 7) * (2 : ZMod 1751057131) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 1751057131) ^ 30 = 1073741824 := by
        calc
          (2 : ZMod 1751057131) ^ 30 = (2 : ZMod 1751057131) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 1751057131) ^ n) (by norm_num)
          _ = (2 : ZMod 1751057131) ^ 15 * (2 : ZMod 1751057131) ^ 15 := by rw [pow_add]
          _ = 1073741824 := by rw [factor_3_3]; decide
      change (2 : ZMod 1751057131) ^ 30 ≠ 1
      rw [factor_3_4]
      decide

#print axioms prime_lucas_1751057131

end TotientTailPeriodKiller
end Erdos249257
