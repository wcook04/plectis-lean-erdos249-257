import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_6601339447 : Nat.Prime 6601339447 := by
  apply lucas_primality 6601339447 (5 : ZMod 6601339447)
  ·
      have fermat_0 : (5 : ZMod 6601339447) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 6601339447) ^ 3 = 125 := by
        calc
          (5 : ZMod 6601339447) ^ 3 = (5 : ZMod 6601339447) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 1 * (5 : ZMod 6601339447) ^ 1) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 6601339447) ^ 6 = 15625 := by
        calc
          (5 : ZMod 6601339447) ^ 6 = (5 : ZMod 6601339447) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 3 * (5 : ZMod 6601339447) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 6601339447) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 6601339447) ^ 12 = (5 : ZMod 6601339447) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 6 * (5 : ZMod 6601339447) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 6601339447) ^ 24 = 2275363847 := by
        calc
          (5 : ZMod 6601339447) ^ 24 = (5 : ZMod 6601339447) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 12 * (5 : ZMod 6601339447) ^ 12 := by rw [pow_add]
          _ = 2275363847 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 6601339447) ^ 49 = 3032793849 := by
        calc
          (5 : ZMod 6601339447) ^ 49 = (5 : ZMod 6601339447) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 24 * (5 : ZMod 6601339447) ^ 24) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 3032793849 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 6601339447) ^ 98 = 1813062032 := by
        calc
          (5 : ZMod 6601339447) ^ 98 = (5 : ZMod 6601339447) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 49 * (5 : ZMod 6601339447) ^ 49 := by rw [pow_add]
          _ = 1813062032 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 6601339447) ^ 196 = 4490909755 := by
        calc
          (5 : ZMod 6601339447) ^ 196 = (5 : ZMod 6601339447) ^ (98 + 98) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 98 * (5 : ZMod 6601339447) ^ 98 := by rw [pow_add]
          _ = 4490909755 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 6601339447) ^ 393 = 6511664699 := by
        calc
          (5 : ZMod 6601339447) ^ 393 = (5 : ZMod 6601339447) ^ (196 + 196 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 196 * (5 : ZMod 6601339447) ^ 196) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 6511664699 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 6601339447) ^ 786 = 153372067 := by
        calc
          (5 : ZMod 6601339447) ^ 786 = (5 : ZMod 6601339447) ^ (393 + 393) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 393 * (5 : ZMod 6601339447) ^ 393 := by rw [pow_add]
          _ = 153372067 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 6601339447) ^ 1573 = 5378429988 := by
        calc
          (5 : ZMod 6601339447) ^ 1573 = (5 : ZMod 6601339447) ^ (786 + 786 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 786 * (5 : ZMod 6601339447) ^ 786) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 5378429988 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 6601339447) ^ 3147 = 4053081886 := by
        calc
          (5 : ZMod 6601339447) ^ 3147 = (5 : ZMod 6601339447) ^ (1573 + 1573 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 1573 * (5 : ZMod 6601339447) ^ 1573) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 4053081886 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 6601339447) ^ 6295 = 1273895072 := by
        calc
          (5 : ZMod 6601339447) ^ 6295 = (5 : ZMod 6601339447) ^ (3147 + 3147 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 3147 * (5 : ZMod 6601339447) ^ 3147) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 1273895072 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 6601339447) ^ 12591 = 5852332699 := by
        calc
          (5 : ZMod 6601339447) ^ 12591 = (5 : ZMod 6601339447) ^ (6295 + 6295 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 6295 * (5 : ZMod 6601339447) ^ 6295) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 5852332699 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 6601339447) ^ 25182 = 5403028059 := by
        calc
          (5 : ZMod 6601339447) ^ 25182 = (5 : ZMod 6601339447) ^ (12591 + 12591) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 12591 * (5 : ZMod 6601339447) ^ 12591 := by rw [pow_add]
          _ = 5403028059 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 6601339447) ^ 50364 = 4856873383 := by
        calc
          (5 : ZMod 6601339447) ^ 50364 = (5 : ZMod 6601339447) ^ (25182 + 25182) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 25182 * (5 : ZMod 6601339447) ^ 25182 := by rw [pow_add]
          _ = 4856873383 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 6601339447) ^ 100728 = 6070850859 := by
        calc
          (5 : ZMod 6601339447) ^ 100728 = (5 : ZMod 6601339447) ^ (50364 + 50364) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 50364 * (5 : ZMod 6601339447) ^ 50364 := by rw [pow_add]
          _ = 6070850859 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 6601339447) ^ 201456 = 4756478124 := by
        calc
          (5 : ZMod 6601339447) ^ 201456 = (5 : ZMod 6601339447) ^ (100728 + 100728) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 100728 * (5 : ZMod 6601339447) ^ 100728 := by rw [pow_add]
          _ = 4756478124 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 6601339447) ^ 402913 = 3253755221 := by
        calc
          (5 : ZMod 6601339447) ^ 402913 = (5 : ZMod 6601339447) ^ (201456 + 201456 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 201456 * (5 : ZMod 6601339447) ^ 201456) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 3253755221 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 6601339447) ^ 805827 = 5631913232 := by
        calc
          (5 : ZMod 6601339447) ^ 805827 = (5 : ZMod 6601339447) ^ (402913 + 402913 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 402913 * (5 : ZMod 6601339447) ^ 402913) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 5631913232 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 6601339447) ^ 1611655 = 1071258662 := by
        calc
          (5 : ZMod 6601339447) ^ 1611655 = (5 : ZMod 6601339447) ^ (805827 + 805827 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 805827 * (5 : ZMod 6601339447) ^ 805827) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 1071258662 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 6601339447) ^ 3223310 = 5537300395 := by
        calc
          (5 : ZMod 6601339447) ^ 3223310 = (5 : ZMod 6601339447) ^ (1611655 + 1611655) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 1611655 * (5 : ZMod 6601339447) ^ 1611655 := by rw [pow_add]
          _ = 5537300395 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 6601339447) ^ 6446620 = 4400155697 := by
        calc
          (5 : ZMod 6601339447) ^ 6446620 = (5 : ZMod 6601339447) ^ (3223310 + 3223310) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 3223310 * (5 : ZMod 6601339447) ^ 3223310 := by rw [pow_add]
          _ = 4400155697 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 6601339447) ^ 12893241 = 3200584522 := by
        calc
          (5 : ZMod 6601339447) ^ 12893241 = (5 : ZMod 6601339447) ^ (6446620 + 6446620 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 6446620 * (5 : ZMod 6601339447) ^ 6446620) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 3200584522 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 6601339447) ^ 25786482 = 5097927042 := by
        calc
          (5 : ZMod 6601339447) ^ 25786482 = (5 : ZMod 6601339447) ^ (12893241 + 12893241) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 12893241 * (5 : ZMod 6601339447) ^ 12893241 := by rw [pow_add]
          _ = 5097927042 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 6601339447) ^ 51572964 = 353174958 := by
        calc
          (5 : ZMod 6601339447) ^ 51572964 = (5 : ZMod 6601339447) ^ (25786482 + 25786482) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 25786482 * (5 : ZMod 6601339447) ^ 25786482 := by rw [pow_add]
          _ = 353174958 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 6601339447) ^ 103145928 = 4459016672 := by
        calc
          (5 : ZMod 6601339447) ^ 103145928 = (5 : ZMod 6601339447) ^ (51572964 + 51572964) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 51572964 * (5 : ZMod 6601339447) ^ 51572964 := by rw [pow_add]
          _ = 4459016672 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 6601339447) ^ 206291857 = 1062613558 := by
        calc
          (5 : ZMod 6601339447) ^ 206291857 = (5 : ZMod 6601339447) ^ (103145928 + 103145928 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 103145928 * (5 : ZMod 6601339447) ^ 103145928) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 1062613558 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 6601339447) ^ 412583715 = 1887113600 := by
        calc
          (5 : ZMod 6601339447) ^ 412583715 = (5 : ZMod 6601339447) ^ (206291857 + 206291857 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 206291857 * (5 : ZMod 6601339447) ^ 206291857) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 1887113600 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 6601339447) ^ 825167430 = 2080740396 := by
        calc
          (5 : ZMod 6601339447) ^ 825167430 = (5 : ZMod 6601339447) ^ (412583715 + 412583715) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 412583715 * (5 : ZMod 6601339447) ^ 412583715 := by rw [pow_add]
          _ = 2080740396 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 6601339447) ^ 1650334861 = 6152932670 := by
        calc
          (5 : ZMod 6601339447) ^ 1650334861 = (5 : ZMod 6601339447) ^ (825167430 + 825167430 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 825167430 * (5 : ZMod 6601339447) ^ 825167430) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 6152932670 := by rw [fermat_29]; decide
      have fermat_31 : (5 : ZMod 6601339447) ^ 3300669723 = 6601339446 := by
        calc
          (5 : ZMod 6601339447) ^ 3300669723 = (5 : ZMod 6601339447) ^ (1650334861 + 1650334861 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 1650334861 * (5 : ZMod 6601339447) ^ 1650334861) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 6601339446 := by rw [fermat_30]; decide
      have fermat_32 : (5 : ZMod 6601339447) ^ 6601339446 = 1 := by
        calc
          (5 : ZMod 6601339447) ^ 6601339446 = (5 : ZMod 6601339447) ^ (3300669723 + 3300669723) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 3300669723 * (5 : ZMod 6601339447) ^ 3300669723 := by rw [pow_add]
          _ = 1 := by rw [fermat_31]; decide
      simpa using fermat_32
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (43, 1), (1968199, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (43, 1), (1968199, 1)] : List FactorBlock).map factorBlockValue).prod = 6601339447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 6601339447) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 6601339447) ^ 3 = 125 := by
        calc
          (5 : ZMod 6601339447) ^ 3 = (5 : ZMod 6601339447) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 1 * (5 : ZMod 6601339447) ^ 1) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 6601339447) ^ 6 = 15625 := by
        calc
          (5 : ZMod 6601339447) ^ 6 = (5 : ZMod 6601339447) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 3 * (5 : ZMod 6601339447) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 6601339447) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 6601339447) ^ 12 = (5 : ZMod 6601339447) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 6 * (5 : ZMod 6601339447) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 6601339447) ^ 24 = 2275363847 := by
        calc
          (5 : ZMod 6601339447) ^ 24 = (5 : ZMod 6601339447) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 12 * (5 : ZMod 6601339447) ^ 12 := by rw [pow_add]
          _ = 2275363847 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 6601339447) ^ 49 = 3032793849 := by
        calc
          (5 : ZMod 6601339447) ^ 49 = (5 : ZMod 6601339447) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 24 * (5 : ZMod 6601339447) ^ 24) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 3032793849 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 6601339447) ^ 98 = 1813062032 := by
        calc
          (5 : ZMod 6601339447) ^ 98 = (5 : ZMod 6601339447) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 49 * (5 : ZMod 6601339447) ^ 49 := by rw [pow_add]
          _ = 1813062032 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 6601339447) ^ 196 = 4490909755 := by
        calc
          (5 : ZMod 6601339447) ^ 196 = (5 : ZMod 6601339447) ^ (98 + 98) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 98 * (5 : ZMod 6601339447) ^ 98 := by rw [pow_add]
          _ = 4490909755 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 6601339447) ^ 393 = 6511664699 := by
        calc
          (5 : ZMod 6601339447) ^ 393 = (5 : ZMod 6601339447) ^ (196 + 196 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 196 * (5 : ZMod 6601339447) ^ 196) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 6511664699 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 6601339447) ^ 786 = 153372067 := by
        calc
          (5 : ZMod 6601339447) ^ 786 = (5 : ZMod 6601339447) ^ (393 + 393) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 393 * (5 : ZMod 6601339447) ^ 393 := by rw [pow_add]
          _ = 153372067 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 6601339447) ^ 1573 = 5378429988 := by
        calc
          (5 : ZMod 6601339447) ^ 1573 = (5 : ZMod 6601339447) ^ (786 + 786 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 786 * (5 : ZMod 6601339447) ^ 786) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 5378429988 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 6601339447) ^ 3147 = 4053081886 := by
        calc
          (5 : ZMod 6601339447) ^ 3147 = (5 : ZMod 6601339447) ^ (1573 + 1573 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 1573 * (5 : ZMod 6601339447) ^ 1573) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 4053081886 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 6601339447) ^ 6295 = 1273895072 := by
        calc
          (5 : ZMod 6601339447) ^ 6295 = (5 : ZMod 6601339447) ^ (3147 + 3147 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 3147 * (5 : ZMod 6601339447) ^ 3147) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 1273895072 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 6601339447) ^ 12591 = 5852332699 := by
        calc
          (5 : ZMod 6601339447) ^ 12591 = (5 : ZMod 6601339447) ^ (6295 + 6295 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 6295 * (5 : ZMod 6601339447) ^ 6295) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 5852332699 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 6601339447) ^ 25182 = 5403028059 := by
        calc
          (5 : ZMod 6601339447) ^ 25182 = (5 : ZMod 6601339447) ^ (12591 + 12591) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 12591 * (5 : ZMod 6601339447) ^ 12591 := by rw [pow_add]
          _ = 5403028059 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 6601339447) ^ 50364 = 4856873383 := by
        calc
          (5 : ZMod 6601339447) ^ 50364 = (5 : ZMod 6601339447) ^ (25182 + 25182) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 25182 * (5 : ZMod 6601339447) ^ 25182 := by rw [pow_add]
          _ = 4856873383 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 6601339447) ^ 100728 = 6070850859 := by
        calc
          (5 : ZMod 6601339447) ^ 100728 = (5 : ZMod 6601339447) ^ (50364 + 50364) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 50364 * (5 : ZMod 6601339447) ^ 50364 := by rw [pow_add]
          _ = 6070850859 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 6601339447) ^ 201456 = 4756478124 := by
        calc
          (5 : ZMod 6601339447) ^ 201456 = (5 : ZMod 6601339447) ^ (100728 + 100728) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 100728 * (5 : ZMod 6601339447) ^ 100728 := by rw [pow_add]
          _ = 4756478124 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 6601339447) ^ 402913 = 3253755221 := by
        calc
          (5 : ZMod 6601339447) ^ 402913 = (5 : ZMod 6601339447) ^ (201456 + 201456 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 201456 * (5 : ZMod 6601339447) ^ 201456) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 3253755221 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 6601339447) ^ 805827 = 5631913232 := by
        calc
          (5 : ZMod 6601339447) ^ 805827 = (5 : ZMod 6601339447) ^ (402913 + 402913 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 402913 * (5 : ZMod 6601339447) ^ 402913) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 5631913232 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 6601339447) ^ 1611655 = 1071258662 := by
        calc
          (5 : ZMod 6601339447) ^ 1611655 = (5 : ZMod 6601339447) ^ (805827 + 805827 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 805827 * (5 : ZMod 6601339447) ^ 805827) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 1071258662 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 6601339447) ^ 3223310 = 5537300395 := by
        calc
          (5 : ZMod 6601339447) ^ 3223310 = (5 : ZMod 6601339447) ^ (1611655 + 1611655) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 1611655 * (5 : ZMod 6601339447) ^ 1611655 := by rw [pow_add]
          _ = 5537300395 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 6601339447) ^ 6446620 = 4400155697 := by
        calc
          (5 : ZMod 6601339447) ^ 6446620 = (5 : ZMod 6601339447) ^ (3223310 + 3223310) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 3223310 * (5 : ZMod 6601339447) ^ 3223310 := by rw [pow_add]
          _ = 4400155697 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 6601339447) ^ 12893241 = 3200584522 := by
        calc
          (5 : ZMod 6601339447) ^ 12893241 = (5 : ZMod 6601339447) ^ (6446620 + 6446620 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 6446620 * (5 : ZMod 6601339447) ^ 6446620) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 3200584522 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 6601339447) ^ 25786482 = 5097927042 := by
        calc
          (5 : ZMod 6601339447) ^ 25786482 = (5 : ZMod 6601339447) ^ (12893241 + 12893241) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 12893241 * (5 : ZMod 6601339447) ^ 12893241 := by rw [pow_add]
          _ = 5097927042 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 6601339447) ^ 51572964 = 353174958 := by
        calc
          (5 : ZMod 6601339447) ^ 51572964 = (5 : ZMod 6601339447) ^ (25786482 + 25786482) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 25786482 * (5 : ZMod 6601339447) ^ 25786482 := by rw [pow_add]
          _ = 353174958 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 6601339447) ^ 103145928 = 4459016672 := by
        calc
          (5 : ZMod 6601339447) ^ 103145928 = (5 : ZMod 6601339447) ^ (51572964 + 51572964) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 51572964 * (5 : ZMod 6601339447) ^ 51572964 := by rw [pow_add]
          _ = 4459016672 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 6601339447) ^ 206291857 = 1062613558 := by
        calc
          (5 : ZMod 6601339447) ^ 206291857 = (5 : ZMod 6601339447) ^ (103145928 + 103145928 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 103145928 * (5 : ZMod 6601339447) ^ 103145928) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 1062613558 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 6601339447) ^ 412583715 = 1887113600 := by
        calc
          (5 : ZMod 6601339447) ^ 412583715 = (5 : ZMod 6601339447) ^ (206291857 + 206291857 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 206291857 * (5 : ZMod 6601339447) ^ 206291857) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 1887113600 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 6601339447) ^ 825167430 = 2080740396 := by
        calc
          (5 : ZMod 6601339447) ^ 825167430 = (5 : ZMod 6601339447) ^ (412583715 + 412583715) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 412583715 * (5 : ZMod 6601339447) ^ 412583715 := by rw [pow_add]
          _ = 2080740396 := by rw [factor_0_28]; decide
      have factor_0_30 : (5 : ZMod 6601339447) ^ 1650334861 = 6152932670 := by
        calc
          (5 : ZMod 6601339447) ^ 1650334861 = (5 : ZMod 6601339447) ^ (825167430 + 825167430 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 825167430 * (5 : ZMod 6601339447) ^ 825167430) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 6152932670 := by rw [factor_0_29]; decide
      have factor_0_31 : (5 : ZMod 6601339447) ^ 3300669723 = 6601339446 := by
        calc
          (5 : ZMod 6601339447) ^ 3300669723 = (5 : ZMod 6601339447) ^ (1650334861 + 1650334861 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 1650334861 * (5 : ZMod 6601339447) ^ 1650334861) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 6601339446 := by rw [factor_0_30]; decide
      change (5 : ZMod 6601339447) ^ 3300669723 ≠ 1
      rw [factor_0_31]
      decide
    ·
      have factor_1_0 : (5 : ZMod 6601339447) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 6601339447) ^ 2 = 25 := by
        calc
          (5 : ZMod 6601339447) ^ 2 = (5 : ZMod 6601339447) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 1 * (5 : ZMod 6601339447) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 6601339447) ^ 4 = 625 := by
        calc
          (5 : ZMod 6601339447) ^ 4 = (5 : ZMod 6601339447) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 2 * (5 : ZMod 6601339447) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 6601339447) ^ 8 = 390625 := by
        calc
          (5 : ZMod 6601339447) ^ 8 = (5 : ZMod 6601339447) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 4 * (5 : ZMod 6601339447) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 6601339447) ^ 16 = 757083344 := by
        calc
          (5 : ZMod 6601339447) ^ 16 = (5 : ZMod 6601339447) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 8 * (5 : ZMod 6601339447) ^ 8 := by rw [pow_add]
          _ = 757083344 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 6601339447) ^ 32 = 3058250848 := by
        calc
          (5 : ZMod 6601339447) ^ 32 = (5 : ZMod 6601339447) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 16 * (5 : ZMod 6601339447) ^ 16 := by rw [pow_add]
          _ = 3058250848 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 6601339447) ^ 65 = 644176125 := by
        calc
          (5 : ZMod 6601339447) ^ 65 = (5 : ZMod 6601339447) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 32 * (5 : ZMod 6601339447) ^ 32) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 644176125 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 6601339447) ^ 131 = 4587561268 := by
        calc
          (5 : ZMod 6601339447) ^ 131 = (5 : ZMod 6601339447) ^ (65 + 65 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 65 * (5 : ZMod 6601339447) ^ 65) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 4587561268 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 6601339447) ^ 262 = 5489430212 := by
        calc
          (5 : ZMod 6601339447) ^ 262 = (5 : ZMod 6601339447) ^ (131 + 131) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 131 * (5 : ZMod 6601339447) ^ 131 := by rw [pow_add]
          _ = 5489430212 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 6601339447) ^ 524 = 3660031799 := by
        calc
          (5 : ZMod 6601339447) ^ 524 = (5 : ZMod 6601339447) ^ (262 + 262) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 262 * (5 : ZMod 6601339447) ^ 262 := by rw [pow_add]
          _ = 3660031799 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 6601339447) ^ 1049 = 5496550111 := by
        calc
          (5 : ZMod 6601339447) ^ 1049 = (5 : ZMod 6601339447) ^ (524 + 524 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 524 * (5 : ZMod 6601339447) ^ 524) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 5496550111 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 6601339447) ^ 2098 = 908459586 := by
        calc
          (5 : ZMod 6601339447) ^ 2098 = (5 : ZMod 6601339447) ^ (1049 + 1049) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 1049 * (5 : ZMod 6601339447) ^ 1049 := by rw [pow_add]
          _ = 908459586 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 6601339447) ^ 4197 = 3705049328 := by
        calc
          (5 : ZMod 6601339447) ^ 4197 = (5 : ZMod 6601339447) ^ (2098 + 2098 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 2098 * (5 : ZMod 6601339447) ^ 2098) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 3705049328 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 6601339447) ^ 8394 = 4124604974 := by
        calc
          (5 : ZMod 6601339447) ^ 8394 = (5 : ZMod 6601339447) ^ (4197 + 4197) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 4197 * (5 : ZMod 6601339447) ^ 4197 := by rw [pow_add]
          _ = 4124604974 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 6601339447) ^ 16788 = 63549654 := by
        calc
          (5 : ZMod 6601339447) ^ 16788 = (5 : ZMod 6601339447) ^ (8394 + 8394) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 8394 * (5 : ZMod 6601339447) ^ 8394 := by rw [pow_add]
          _ = 63549654 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 6601339447) ^ 33576 = 4279312950 := by
        calc
          (5 : ZMod 6601339447) ^ 33576 = (5 : ZMod 6601339447) ^ (16788 + 16788) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 16788 * (5 : ZMod 6601339447) ^ 16788 := by rw [pow_add]
          _ = 4279312950 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 6601339447) ^ 67152 = 6348500109 := by
        calc
          (5 : ZMod 6601339447) ^ 67152 = (5 : ZMod 6601339447) ^ (33576 + 33576) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 33576 * (5 : ZMod 6601339447) ^ 33576 := by rw [pow_add]
          _ = 6348500109 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 6601339447) ^ 134304 = 3163200106 := by
        calc
          (5 : ZMod 6601339447) ^ 134304 = (5 : ZMod 6601339447) ^ (67152 + 67152) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 67152 * (5 : ZMod 6601339447) ^ 67152 := by rw [pow_add]
          _ = 3163200106 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 6601339447) ^ 268609 = 108563092 := by
        calc
          (5 : ZMod 6601339447) ^ 268609 = (5 : ZMod 6601339447) ^ (134304 + 134304 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 134304 * (5 : ZMod 6601339447) ^ 134304) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 108563092 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 6601339447) ^ 537218 = 5914678922 := by
        calc
          (5 : ZMod 6601339447) ^ 537218 = (5 : ZMod 6601339447) ^ (268609 + 268609) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 268609 * (5 : ZMod 6601339447) ^ 268609 := by rw [pow_add]
          _ = 5914678922 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 6601339447) ^ 1074436 = 6385448184 := by
        calc
          (5 : ZMod 6601339447) ^ 1074436 = (5 : ZMod 6601339447) ^ (537218 + 537218) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 537218 * (5 : ZMod 6601339447) ^ 537218 := by rw [pow_add]
          _ = 6385448184 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 6601339447) ^ 2148873 = 1886995581 := by
        calc
          (5 : ZMod 6601339447) ^ 2148873 = (5 : ZMod 6601339447) ^ (1074436 + 1074436 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 1074436 * (5 : ZMod 6601339447) ^ 1074436) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 1886995581 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 6601339447) ^ 4297747 = 1531755834 := by
        calc
          (5 : ZMod 6601339447) ^ 4297747 = (5 : ZMod 6601339447) ^ (2148873 + 2148873 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 2148873 * (5 : ZMod 6601339447) ^ 2148873) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 1531755834 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 6601339447) ^ 8595494 = 4486489769 := by
        calc
          (5 : ZMod 6601339447) ^ 8595494 = (5 : ZMod 6601339447) ^ (4297747 + 4297747) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 4297747 * (5 : ZMod 6601339447) ^ 4297747 := by rw [pow_add]
          _ = 4486489769 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 6601339447) ^ 17190988 = 3129943350 := by
        calc
          (5 : ZMod 6601339447) ^ 17190988 = (5 : ZMod 6601339447) ^ (8595494 + 8595494) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 8595494 * (5 : ZMod 6601339447) ^ 8595494 := by rw [pow_add]
          _ = 3129943350 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 6601339447) ^ 34381976 = 1476567587 := by
        calc
          (5 : ZMod 6601339447) ^ 34381976 = (5 : ZMod 6601339447) ^ (17190988 + 17190988) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 17190988 * (5 : ZMod 6601339447) ^ 17190988 := by rw [pow_add]
          _ = 1476567587 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 6601339447) ^ 68763952 = 4847552496 := by
        calc
          (5 : ZMod 6601339447) ^ 68763952 = (5 : ZMod 6601339447) ^ (34381976 + 34381976) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 34381976 * (5 : ZMod 6601339447) ^ 34381976 := by rw [pow_add]
          _ = 4847552496 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 6601339447) ^ 137527905 = 3710028157 := by
        calc
          (5 : ZMod 6601339447) ^ 137527905 = (5 : ZMod 6601339447) ^ (68763952 + 68763952 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 68763952 * (5 : ZMod 6601339447) ^ 68763952) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 3710028157 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 6601339447) ^ 275055810 = 202437378 := by
        calc
          (5 : ZMod 6601339447) ^ 275055810 = (5 : ZMod 6601339447) ^ (137527905 + 137527905) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 137527905 * (5 : ZMod 6601339447) ^ 137527905 := by rw [pow_add]
          _ = 202437378 := by rw [factor_1_27]; decide
      have factor_1_29 : (5 : ZMod 6601339447) ^ 550111620 = 1170080082 := by
        calc
          (5 : ZMod 6601339447) ^ 550111620 = (5 : ZMod 6601339447) ^ (275055810 + 275055810) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 275055810 * (5 : ZMod 6601339447) ^ 275055810 := by rw [pow_add]
          _ = 1170080082 := by rw [factor_1_28]; decide
      have factor_1_30 : (5 : ZMod 6601339447) ^ 1100223241 = 571419136 := by
        calc
          (5 : ZMod 6601339447) ^ 1100223241 = (5 : ZMod 6601339447) ^ (550111620 + 550111620 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 550111620 * (5 : ZMod 6601339447) ^ 550111620) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 571419136 := by rw [factor_1_29]; decide
      have factor_1_31 : (5 : ZMod 6601339447) ^ 2200446482 = 571419135 := by
        calc
          (5 : ZMod 6601339447) ^ 2200446482 = (5 : ZMod 6601339447) ^ (1100223241 + 1100223241) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 1100223241 * (5 : ZMod 6601339447) ^ 1100223241 := by rw [pow_add]
          _ = 571419135 := by rw [factor_1_30]; decide
      change (5 : ZMod 6601339447) ^ 2200446482 ≠ 1
      rw [factor_1_31]
      decide
    ·
      have factor_2_0 : (5 : ZMod 6601339447) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 6601339447) ^ 3 = 125 := by
        calc
          (5 : ZMod 6601339447) ^ 3 = (5 : ZMod 6601339447) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 1 * (5 : ZMod 6601339447) ^ 1) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 6601339447) ^ 7 = 78125 := by
        calc
          (5 : ZMod 6601339447) ^ 7 = (5 : ZMod 6601339447) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 3 * (5 : ZMod 6601339447) ^ 3) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 6601339447) ^ 15 = 4112220337 := by
        calc
          (5 : ZMod 6601339447) ^ 15 = (5 : ZMod 6601339447) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 7 * (5 : ZMod 6601339447) ^ 7) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 4112220337 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 6601339447) ^ 30 = 4347187280 := by
        calc
          (5 : ZMod 6601339447) ^ 30 = (5 : ZMod 6601339447) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 15 * (5 : ZMod 6601339447) ^ 15 := by rw [pow_add]
          _ = 4347187280 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 6601339447) ^ 60 = 792366870 := by
        calc
          (5 : ZMod 6601339447) ^ 60 = (5 : ZMod 6601339447) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 30 * (5 : ZMod 6601339447) ^ 30 := by rw [pow_add]
          _ = 792366870 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 6601339447) ^ 121 = 3485808 := by
        calc
          (5 : ZMod 6601339447) ^ 121 = (5 : ZMod 6601339447) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 60 * (5 : ZMod 6601339447) ^ 60) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 3485808 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 6601339447) ^ 242 = 4392830384 := by
        calc
          (5 : ZMod 6601339447) ^ 242 = (5 : ZMod 6601339447) ^ (121 + 121) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 121 * (5 : ZMod 6601339447) ^ 121 := by rw [pow_add]
          _ = 4392830384 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 6601339447) ^ 484 = 5484882702 := by
        calc
          (5 : ZMod 6601339447) ^ 484 = (5 : ZMod 6601339447) ^ (242 + 242) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 242 * (5 : ZMod 6601339447) ^ 242 := by rw [pow_add]
          _ = 5484882702 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 6601339447) ^ 968 = 2092835309 := by
        calc
          (5 : ZMod 6601339447) ^ 968 = (5 : ZMod 6601339447) ^ (484 + 484) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 484 * (5 : ZMod 6601339447) ^ 484 := by rw [pow_add]
          _ = 2092835309 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 6601339447) ^ 1937 = 4679181497 := by
        calc
          (5 : ZMod 6601339447) ^ 1937 = (5 : ZMod 6601339447) ^ (968 + 968 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 968 * (5 : ZMod 6601339447) ^ 968) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 4679181497 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 6601339447) ^ 3874 = 5992345671 := by
        calc
          (5 : ZMod 6601339447) ^ 3874 = (5 : ZMod 6601339447) ^ (1937 + 1937) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 1937 * (5 : ZMod 6601339447) ^ 1937 := by rw [pow_add]
          _ = 5992345671 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 6601339447) ^ 7748 = 3011529796 := by
        calc
          (5 : ZMod 6601339447) ^ 7748 = (5 : ZMod 6601339447) ^ (3874 + 3874) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 3874 * (5 : ZMod 6601339447) ^ 3874 := by rw [pow_add]
          _ = 3011529796 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 6601339447) ^ 15496 = 1653884470 := by
        calc
          (5 : ZMod 6601339447) ^ 15496 = (5 : ZMod 6601339447) ^ (7748 + 7748) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 7748 * (5 : ZMod 6601339447) ^ 7748 := by rw [pow_add]
          _ = 1653884470 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 6601339447) ^ 30993 = 773548473 := by
        calc
          (5 : ZMod 6601339447) ^ 30993 = (5 : ZMod 6601339447) ^ (15496 + 15496 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 15496 * (5 : ZMod 6601339447) ^ 15496) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 773548473 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 6601339447) ^ 61986 = 945738295 := by
        calc
          (5 : ZMod 6601339447) ^ 61986 = (5 : ZMod 6601339447) ^ (30993 + 30993) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 30993 * (5 : ZMod 6601339447) ^ 30993 := by rw [pow_add]
          _ = 945738295 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 6601339447) ^ 123973 = 657524038 := by
        calc
          (5 : ZMod 6601339447) ^ 123973 = (5 : ZMod 6601339447) ^ (61986 + 61986 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 61986 * (5 : ZMod 6601339447) ^ 61986) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 657524038 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 6601339447) ^ 247946 = 6490186976 := by
        calc
          (5 : ZMod 6601339447) ^ 247946 = (5 : ZMod 6601339447) ^ (123973 + 123973) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 123973 * (5 : ZMod 6601339447) ^ 123973 := by rw [pow_add]
          _ = 6490186976 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 6601339447) ^ 495893 = 1500241361 := by
        calc
          (5 : ZMod 6601339447) ^ 495893 = (5 : ZMod 6601339447) ^ (247946 + 247946 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 247946 * (5 : ZMod 6601339447) ^ 247946) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 1500241361 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 6601339447) ^ 991787 = 4783525974 := by
        calc
          (5 : ZMod 6601339447) ^ 991787 = (5 : ZMod 6601339447) ^ (495893 + 495893 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 495893 * (5 : ZMod 6601339447) ^ 495893) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 4783525974 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 6601339447) ^ 1983575 = 4649243945 := by
        calc
          (5 : ZMod 6601339447) ^ 1983575 = (5 : ZMod 6601339447) ^ (991787 + 991787 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 991787 * (5 : ZMod 6601339447) ^ 991787) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 4649243945 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 6601339447) ^ 3967151 = 506962834 := by
        calc
          (5 : ZMod 6601339447) ^ 3967151 = (5 : ZMod 6601339447) ^ (1983575 + 1983575 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 1983575 * (5 : ZMod 6601339447) ^ 1983575) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 506962834 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 6601339447) ^ 7934302 = 6491334474 := by
        calc
          (5 : ZMod 6601339447) ^ 7934302 = (5 : ZMod 6601339447) ^ (3967151 + 3967151) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 3967151 * (5 : ZMod 6601339447) ^ 3967151 := by rw [pow_add]
          _ = 6491334474 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 6601339447) ^ 15868604 = 508269960 := by
        calc
          (5 : ZMod 6601339447) ^ 15868604 = (5 : ZMod 6601339447) ^ (7934302 + 7934302) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 7934302 * (5 : ZMod 6601339447) ^ 7934302 := by rw [pow_add]
          _ = 508269960 := by rw [factor_2_22]; decide
      have factor_2_24 : (5 : ZMod 6601339447) ^ 31737208 = 2808751896 := by
        calc
          (5 : ZMod 6601339447) ^ 31737208 = (5 : ZMod 6601339447) ^ (15868604 + 15868604) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 15868604 * (5 : ZMod 6601339447) ^ 15868604 := by rw [pow_add]
          _ = 2808751896 := by rw [factor_2_23]; decide
      have factor_2_25 : (5 : ZMod 6601339447) ^ 63474417 = 6351837253 := by
        calc
          (5 : ZMod 6601339447) ^ 63474417 = (5 : ZMod 6601339447) ^ (31737208 + 31737208 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 31737208 * (5 : ZMod 6601339447) ^ 31737208) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 6351837253 := by rw [factor_2_24]; decide
      have factor_2_26 : (5 : ZMod 6601339447) ^ 126948835 = 4404716800 := by
        calc
          (5 : ZMod 6601339447) ^ 126948835 = (5 : ZMod 6601339447) ^ (63474417 + 63474417 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 63474417 * (5 : ZMod 6601339447) ^ 63474417) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 4404716800 := by rw [factor_2_25]; decide
      have factor_2_27 : (5 : ZMod 6601339447) ^ 253897671 = 6083728325 := by
        calc
          (5 : ZMod 6601339447) ^ 253897671 = (5 : ZMod 6601339447) ^ (126948835 + 126948835 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 126948835 * (5 : ZMod 6601339447) ^ 126948835) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 6083728325 := by rw [factor_2_26]; decide
      have factor_2_28 : (5 : ZMod 6601339447) ^ 507795342 = 3962798819 := by
        calc
          (5 : ZMod 6601339447) ^ 507795342 = (5 : ZMod 6601339447) ^ (253897671 + 253897671) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 253897671 * (5 : ZMod 6601339447) ^ 253897671 := by rw [pow_add]
          _ = 3962798819 := by rw [factor_2_27]; decide
      change (5 : ZMod 6601339447) ^ 507795342 ≠ 1
      rw [factor_2_28]
      decide
    ·
      have factor_3_0 : (5 : ZMod 6601339447) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 6601339447) ^ 2 = 25 := by
        calc
          (5 : ZMod 6601339447) ^ 2 = (5 : ZMod 6601339447) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 1 * (5 : ZMod 6601339447) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 6601339447) ^ 4 = 625 := by
        calc
          (5 : ZMod 6601339447) ^ 4 = (5 : ZMod 6601339447) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 2 * (5 : ZMod 6601339447) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 6601339447) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 6601339447) ^ 9 = (5 : ZMod 6601339447) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 4 * (5 : ZMod 6601339447) ^ 4) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 6601339447) ^ 18 = 5724404706 := by
        calc
          (5 : ZMod 6601339447) ^ 18 = (5 : ZMod 6601339447) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 9 * (5 : ZMod 6601339447) ^ 9 := by rw [pow_add]
          _ = 5724404706 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 6601339447) ^ 36 = 3619679817 := by
        calc
          (5 : ZMod 6601339447) ^ 36 = (5 : ZMod 6601339447) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 18 * (5 : ZMod 6601339447) ^ 18 := by rw [pow_add]
          _ = 3619679817 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 6601339447) ^ 73 = 1441787379 := by
        calc
          (5 : ZMod 6601339447) ^ 73 = (5 : ZMod 6601339447) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 36 * (5 : ZMod 6601339447) ^ 36) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 1441787379 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 6601339447) ^ 146 = 6005532214 := by
        calc
          (5 : ZMod 6601339447) ^ 146 = (5 : ZMod 6601339447) ^ (73 + 73) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 73 * (5 : ZMod 6601339447) ^ 73 := by rw [pow_add]
          _ = 6005532214 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 6601339447) ^ 292 = 2489406588 := by
        calc
          (5 : ZMod 6601339447) ^ 292 = (5 : ZMod 6601339447) ^ (146 + 146) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 146 * (5 : ZMod 6601339447) ^ 146 := by rw [pow_add]
          _ = 2489406588 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 6601339447) ^ 585 = 1977537634 := by
        calc
          (5 : ZMod 6601339447) ^ 585 = (5 : ZMod 6601339447) ^ (292 + 292 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 292 * (5 : ZMod 6601339447) ^ 292) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 1977537634 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 6601339447) ^ 1171 = 3098879072 := by
        calc
          (5 : ZMod 6601339447) ^ 1171 = (5 : ZMod 6601339447) ^ (585 + 585 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 585 * (5 : ZMod 6601339447) ^ 585) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 3098879072 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 6601339447) ^ 2342 = 4086474606 := by
        calc
          (5 : ZMod 6601339447) ^ 2342 = (5 : ZMod 6601339447) ^ (1171 + 1171) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 1171 * (5 : ZMod 6601339447) ^ 1171 := by rw [pow_add]
          _ = 4086474606 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 6601339447) ^ 4685 = 3471197741 := by
        calc
          (5 : ZMod 6601339447) ^ 4685 = (5 : ZMod 6601339447) ^ (2342 + 2342 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 2342 * (5 : ZMod 6601339447) ^ 2342) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 3471197741 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 6601339447) ^ 9370 = 1755275929 := by
        calc
          (5 : ZMod 6601339447) ^ 9370 = (5 : ZMod 6601339447) ^ (4685 + 4685) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 4685 * (5 : ZMod 6601339447) ^ 4685 := by rw [pow_add]
          _ = 1755275929 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 6601339447) ^ 18740 = 2887750011 := by
        calc
          (5 : ZMod 6601339447) ^ 18740 = (5 : ZMod 6601339447) ^ (9370 + 9370) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 9370 * (5 : ZMod 6601339447) ^ 9370 := by rw [pow_add]
          _ = 2887750011 := by rw [factor_3_13]; decide
      have factor_3_15 : (5 : ZMod 6601339447) ^ 37480 = 1315917465 := by
        calc
          (5 : ZMod 6601339447) ^ 37480 = (5 : ZMod 6601339447) ^ (18740 + 18740) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 18740 * (5 : ZMod 6601339447) ^ 18740 := by rw [pow_add]
          _ = 1315917465 := by rw [factor_3_14]; decide
      have factor_3_16 : (5 : ZMod 6601339447) ^ 74960 = 944426300 := by
        calc
          (5 : ZMod 6601339447) ^ 74960 = (5 : ZMod 6601339447) ^ (37480 + 37480) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 37480 * (5 : ZMod 6601339447) ^ 37480 := by rw [pow_add]
          _ = 944426300 := by rw [factor_3_15]; decide
      have factor_3_17 : (5 : ZMod 6601339447) ^ 149921 = 2679867400 := by
        calc
          (5 : ZMod 6601339447) ^ 149921 = (5 : ZMod 6601339447) ^ (74960 + 74960 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 74960 * (5 : ZMod 6601339447) ^ 74960) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 2679867400 := by rw [factor_3_16]; decide
      have factor_3_18 : (5 : ZMod 6601339447) ^ 299842 = 1904834903 := by
        calc
          (5 : ZMod 6601339447) ^ 299842 = (5 : ZMod 6601339447) ^ (149921 + 149921) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 149921 * (5 : ZMod 6601339447) ^ 149921 := by rw [pow_add]
          _ = 1904834903 := by rw [factor_3_17]; decide
      have factor_3_19 : (5 : ZMod 6601339447) ^ 599685 = 1275949428 := by
        calc
          (5 : ZMod 6601339447) ^ 599685 = (5 : ZMod 6601339447) ^ (299842 + 299842 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 299842 * (5 : ZMod 6601339447) ^ 299842) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 1275949428 := by rw [factor_3_18]; decide
      have factor_3_20 : (5 : ZMod 6601339447) ^ 1199371 = 6207322734 := by
        calc
          (5 : ZMod 6601339447) ^ 1199371 = (5 : ZMod 6601339447) ^ (599685 + 599685 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 599685 * (5 : ZMod 6601339447) ^ 599685) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 6207322734 := by rw [factor_3_19]; decide
      have factor_3_21 : (5 : ZMod 6601339447) ^ 2398742 = 4439163253 := by
        calc
          (5 : ZMod 6601339447) ^ 2398742 = (5 : ZMod 6601339447) ^ (1199371 + 1199371) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 1199371 * (5 : ZMod 6601339447) ^ 1199371 := by rw [pow_add]
          _ = 4439163253 := by rw [factor_3_20]; decide
      have factor_3_22 : (5 : ZMod 6601339447) ^ 4797485 = 5088984551 := by
        calc
          (5 : ZMod 6601339447) ^ 4797485 = (5 : ZMod 6601339447) ^ (2398742 + 2398742 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 2398742 * (5 : ZMod 6601339447) ^ 2398742) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 5088984551 := by rw [factor_3_21]; decide
      have factor_3_23 : (5 : ZMod 6601339447) ^ 9594970 = 453614308 := by
        calc
          (5 : ZMod 6601339447) ^ 9594970 = (5 : ZMod 6601339447) ^ (4797485 + 4797485) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 4797485 * (5 : ZMod 6601339447) ^ 4797485 := by rw [pow_add]
          _ = 453614308 := by rw [factor_3_22]; decide
      have factor_3_24 : (5 : ZMod 6601339447) ^ 19189940 = 4815971907 := by
        calc
          (5 : ZMod 6601339447) ^ 19189940 = (5 : ZMod 6601339447) ^ (9594970 + 9594970) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 9594970 * (5 : ZMod 6601339447) ^ 9594970 := by rw [pow_add]
          _ = 4815971907 := by rw [factor_3_23]; decide
      have factor_3_25 : (5 : ZMod 6601339447) ^ 38379880 = 4168484882 := by
        calc
          (5 : ZMod 6601339447) ^ 38379880 = (5 : ZMod 6601339447) ^ (19189940 + 19189940) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 19189940 * (5 : ZMod 6601339447) ^ 19189940 := by rw [pow_add]
          _ = 4168484882 := by rw [factor_3_24]; decide
      have factor_3_26 : (5 : ZMod 6601339447) ^ 76759761 = 23294998 := by
        calc
          (5 : ZMod 6601339447) ^ 76759761 = (5 : ZMod 6601339447) ^ (38379880 + 38379880 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 38379880 * (5 : ZMod 6601339447) ^ 38379880) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 23294998 := by rw [factor_3_25]; decide
      have factor_3_27 : (5 : ZMod 6601339447) ^ 153519522 = 423918816 := by
        calc
          (5 : ZMod 6601339447) ^ 153519522 = (5 : ZMod 6601339447) ^ (76759761 + 76759761) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 76759761 * (5 : ZMod 6601339447) ^ 76759761 := by rw [pow_add]
          _ = 423918816 := by rw [factor_3_26]; decide
      change (5 : ZMod 6601339447) ^ 153519522 ≠ 1
      rw [factor_3_27]
      decide
    ·
      have factor_4_0 : (5 : ZMod 6601339447) ^ 1 = 5 := by norm_num
      have factor_4_1 : (5 : ZMod 6601339447) ^ 3 = 125 := by
        calc
          (5 : ZMod 6601339447) ^ 3 = (5 : ZMod 6601339447) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 1 * (5 : ZMod 6601339447) ^ 1) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_4_0]; decide
      have factor_4_2 : (5 : ZMod 6601339447) ^ 6 = 15625 := by
        calc
          (5 : ZMod 6601339447) ^ 6 = (5 : ZMod 6601339447) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 3 * (5 : ZMod 6601339447) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_4_1]; decide
      have factor_4_3 : (5 : ZMod 6601339447) ^ 13 = 1220703125 := by
        calc
          (5 : ZMod 6601339447) ^ 13 = (5 : ZMod 6601339447) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 6 * (5 : ZMod 6601339447) ^ 6) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 1220703125 := by rw [factor_4_2]; decide
      have factor_4_4 : (5 : ZMod 6601339447) ^ 26 = 4073380599 := by
        calc
          (5 : ZMod 6601339447) ^ 26 = (5 : ZMod 6601339447) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 13 * (5 : ZMod 6601339447) ^ 13 := by rw [pow_add]
          _ = 4073380599 := by rw [factor_4_3]; decide
      have factor_4_5 : (5 : ZMod 6601339447) ^ 52 = 2822882646 := by
        calc
          (5 : ZMod 6601339447) ^ 52 = (5 : ZMod 6601339447) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 26 * (5 : ZMod 6601339447) ^ 26 := by rw [pow_add]
          _ = 2822882646 := by rw [factor_4_4]; decide
      have factor_4_6 : (5 : ZMod 6601339447) ^ 104 = 2746682923 := by
        calc
          (5 : ZMod 6601339447) ^ 104 = (5 : ZMod 6601339447) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 52 * (5 : ZMod 6601339447) ^ 52 := by rw [pow_add]
          _ = 2746682923 := by rw [factor_4_5]; decide
      have factor_4_7 : (5 : ZMod 6601339447) ^ 209 = 2058016761 := by
        calc
          (5 : ZMod 6601339447) ^ 209 = (5 : ZMod 6601339447) ^ (104 + 104 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 104 * (5 : ZMod 6601339447) ^ 104) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 2058016761 := by rw [factor_4_6]; decide
      have factor_4_8 : (5 : ZMod 6601339447) ^ 419 = 3012351505 := by
        calc
          (5 : ZMod 6601339447) ^ 419 = (5 : ZMod 6601339447) ^ (209 + 209 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 209 * (5 : ZMod 6601339447) ^ 209) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 3012351505 := by rw [factor_4_7]; decide
      have factor_4_9 : (5 : ZMod 6601339447) ^ 838 = 3377643316 := by
        calc
          (5 : ZMod 6601339447) ^ 838 = (5 : ZMod 6601339447) ^ (419 + 419) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 419 * (5 : ZMod 6601339447) ^ 419 := by rw [pow_add]
          _ = 3377643316 := by rw [factor_4_8]; decide
      have factor_4_10 : (5 : ZMod 6601339447) ^ 1677 = 5359299418 := by
        calc
          (5 : ZMod 6601339447) ^ 1677 = (5 : ZMod 6601339447) ^ (838 + 838 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = ((5 : ZMod 6601339447) ^ 838 * (5 : ZMod 6601339447) ^ 838) * (5 : ZMod 6601339447) := by rw [pow_succ, pow_add]
          _ = 5359299418 := by rw [factor_4_9]; decide
      have factor_4_11 : (5 : ZMod 6601339447) ^ 3354 = 2796210562 := by
        calc
          (5 : ZMod 6601339447) ^ 3354 = (5 : ZMod 6601339447) ^ (1677 + 1677) :=
            congrArg (fun n : ℕ => (5 : ZMod 6601339447) ^ n) (by norm_num)
          _ = (5 : ZMod 6601339447) ^ 1677 * (5 : ZMod 6601339447) ^ 1677 := by rw [pow_add]
          _ = 2796210562 := by rw [factor_4_10]; decide
      change (5 : ZMod 6601339447) ^ 3354 ≠ 1
      rw [factor_4_11]
      decide

#print axioms prime_lucas_6601339447

end TotientTailPeriodKiller
end Erdos249257
