import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_49571861 : Nat.Prime 49571861 := by
  apply lucas_primality 49571861 (2 : ZMod 49571861)
  ·
      have fermat_0 : (2 : ZMod 49571861) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 49571861) ^ 2 = 4 := by
        calc
          (2 : ZMod 49571861) ^ 2 = (2 : ZMod 49571861) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 1 * (2 : ZMod 49571861) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 49571861) ^ 5 = 32 := by
        calc
          (2 : ZMod 49571861) ^ 5 = (2 : ZMod 49571861) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 2 * (2 : ZMod 49571861) ^ 2) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 49571861) ^ 11 = 2048 := by
        calc
          (2 : ZMod 49571861) ^ 11 = (2 : ZMod 49571861) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 5 * (2 : ZMod 49571861) ^ 5) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 49571861) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 49571861) ^ 23 = (2 : ZMod 49571861) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 11 * (2 : ZMod 49571861) ^ 11) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 49571861) ^ 47 = 664668 := by
        calc
          (2 : ZMod 49571861) ^ 47 = (2 : ZMod 49571861) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 23 * (2 : ZMod 49571861) ^ 23) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 664668 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 49571861) ^ 94 = 48696853 := by
        calc
          (2 : ZMod 49571861) ^ 94 = (2 : ZMod 49571861) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 47 * (2 : ZMod 49571861) ^ 47 := by rw [pow_add]
          _ = 48696853 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 49571861) ^ 189 = 3213838 := by
        calc
          (2 : ZMod 49571861) ^ 189 = (2 : ZMod 49571861) ^ (94 + 94 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 94 * (2 : ZMod 49571861) ^ 94) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 3213838 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 49571861) ^ 378 = 11304145 := by
        calc
          (2 : ZMod 49571861) ^ 378 = (2 : ZMod 49571861) ^ (189 + 189) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 189 * (2 : ZMod 49571861) ^ 189 := by rw [pow_add]
          _ = 11304145 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 49571861) ^ 756 = 27775719 := by
        calc
          (2 : ZMod 49571861) ^ 756 = (2 : ZMod 49571861) ^ (378 + 378) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 378 * (2 : ZMod 49571861) ^ 378 := by rw [pow_add]
          _ = 27775719 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 49571861) ^ 1512 = 24906247 := by
        calc
          (2 : ZMod 49571861) ^ 1512 = (2 : ZMod 49571861) ^ (756 + 756) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 756 * (2 : ZMod 49571861) ^ 756 := by rw [pow_add]
          _ = 24906247 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 49571861) ^ 3025 = 26939451 := by
        calc
          (2 : ZMod 49571861) ^ 3025 = (2 : ZMod 49571861) ^ (1512 + 1512 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 1512 * (2 : ZMod 49571861) ^ 1512) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 26939451 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 49571861) ^ 6051 = 34105783 := by
        calc
          (2 : ZMod 49571861) ^ 6051 = (2 : ZMod 49571861) ^ (3025 + 3025 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 3025 * (2 : ZMod 49571861) ^ 3025) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 34105783 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 49571861) ^ 12102 = 21672035 := by
        calc
          (2 : ZMod 49571861) ^ 12102 = (2 : ZMod 49571861) ^ (6051 + 6051) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 6051 * (2 : ZMod 49571861) ^ 6051 := by rw [pow_add]
          _ = 21672035 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 49571861) ^ 24205 = 4845127 := by
        calc
          (2 : ZMod 49571861) ^ 24205 = (2 : ZMod 49571861) ^ (12102 + 12102 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 12102 * (2 : ZMod 49571861) ^ 12102) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 4845127 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 49571861) ^ 48410 = 5150969 := by
        calc
          (2 : ZMod 49571861) ^ 48410 = (2 : ZMod 49571861) ^ (24205 + 24205) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 24205 * (2 : ZMod 49571861) ^ 24205 := by rw [pow_add]
          _ = 5150969 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 49571861) ^ 96820 = 35332209 := by
        calc
          (2 : ZMod 49571861) ^ 96820 = (2 : ZMod 49571861) ^ (48410 + 48410) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 48410 * (2 : ZMod 49571861) ^ 48410 := by rw [pow_add]
          _ = 35332209 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 49571861) ^ 193640 = 39427646 := by
        calc
          (2 : ZMod 49571861) ^ 193640 = (2 : ZMod 49571861) ^ (96820 + 96820) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 96820 * (2 : ZMod 49571861) ^ 96820 := by rw [pow_add]
          _ = 39427646 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 49571861) ^ 387280 = 11869128 := by
        calc
          (2 : ZMod 49571861) ^ 387280 = (2 : ZMod 49571861) ^ (193640 + 193640) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 193640 * (2 : ZMod 49571861) ^ 193640 := by rw [pow_add]
          _ = 11869128 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 49571861) ^ 774560 = 9722646 := by
        calc
          (2 : ZMod 49571861) ^ 774560 = (2 : ZMod 49571861) ^ (387280 + 387280) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 387280 * (2 : ZMod 49571861) ^ 387280 := by rw [pow_add]
          _ = 9722646 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 49571861) ^ 1549120 = 24203891 := by
        calc
          (2 : ZMod 49571861) ^ 1549120 = (2 : ZMod 49571861) ^ (774560 + 774560) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 774560 * (2 : ZMod 49571861) ^ 774560 := by rw [pow_add]
          _ = 24203891 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 49571861) ^ 3098241 = 16548903 := by
        calc
          (2 : ZMod 49571861) ^ 3098241 = (2 : ZMod 49571861) ^ (1549120 + 1549120 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 1549120 * (2 : ZMod 49571861) ^ 1549120) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 16548903 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 49571861) ^ 6196482 = 66979 := by
        calc
          (2 : ZMod 49571861) ^ 6196482 = (2 : ZMod 49571861) ^ (3098241 + 3098241) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 3098241 * (2 : ZMod 49571861) ^ 3098241 := by rw [pow_add]
          _ = 66979 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 49571861) ^ 12392965 = 49437902 := by
        calc
          (2 : ZMod 49571861) ^ 12392965 = (2 : ZMod 49571861) ^ (6196482 + 6196482 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 6196482 * (2 : ZMod 49571861) ^ 6196482) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 49437902 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 49571861) ^ 24785930 = 49571860 := by
        calc
          (2 : ZMod 49571861) ^ 24785930 = (2 : ZMod 49571861) ^ (12392965 + 12392965) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 12392965 * (2 : ZMod 49571861) ^ 12392965 := by rw [pow_add]
          _ = 49571860 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 49571861) ^ 49571860 = 1 := by
        calc
          (2 : ZMod 49571861) ^ 49571860 = (2 : ZMod 49571861) ^ (24785930 + 24785930) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 24785930 * (2 : ZMod 49571861) ^ 24785930 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (13, 1), (37, 1), (5153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (13, 1), (37, 1), (5153, 1)] : List FactorBlock).map factorBlockValue).prod = 49571861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 49571861) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 49571861) ^ 2 = 4 := by
        calc
          (2 : ZMod 49571861) ^ 2 = (2 : ZMod 49571861) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 1 * (2 : ZMod 49571861) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 49571861) ^ 5 = 32 := by
        calc
          (2 : ZMod 49571861) ^ 5 = (2 : ZMod 49571861) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 2 * (2 : ZMod 49571861) ^ 2) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 49571861) ^ 11 = 2048 := by
        calc
          (2 : ZMod 49571861) ^ 11 = (2 : ZMod 49571861) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 5 * (2 : ZMod 49571861) ^ 5) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 49571861) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 49571861) ^ 23 = (2 : ZMod 49571861) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 11 * (2 : ZMod 49571861) ^ 11) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 49571861) ^ 47 = 664668 := by
        calc
          (2 : ZMod 49571861) ^ 47 = (2 : ZMod 49571861) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 23 * (2 : ZMod 49571861) ^ 23) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 664668 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 49571861) ^ 94 = 48696853 := by
        calc
          (2 : ZMod 49571861) ^ 94 = (2 : ZMod 49571861) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 47 * (2 : ZMod 49571861) ^ 47 := by rw [pow_add]
          _ = 48696853 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 49571861) ^ 189 = 3213838 := by
        calc
          (2 : ZMod 49571861) ^ 189 = (2 : ZMod 49571861) ^ (94 + 94 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 94 * (2 : ZMod 49571861) ^ 94) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 3213838 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 49571861) ^ 378 = 11304145 := by
        calc
          (2 : ZMod 49571861) ^ 378 = (2 : ZMod 49571861) ^ (189 + 189) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 189 * (2 : ZMod 49571861) ^ 189 := by rw [pow_add]
          _ = 11304145 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 49571861) ^ 756 = 27775719 := by
        calc
          (2 : ZMod 49571861) ^ 756 = (2 : ZMod 49571861) ^ (378 + 378) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 378 * (2 : ZMod 49571861) ^ 378 := by rw [pow_add]
          _ = 27775719 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 49571861) ^ 1512 = 24906247 := by
        calc
          (2 : ZMod 49571861) ^ 1512 = (2 : ZMod 49571861) ^ (756 + 756) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 756 * (2 : ZMod 49571861) ^ 756 := by rw [pow_add]
          _ = 24906247 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 49571861) ^ 3025 = 26939451 := by
        calc
          (2 : ZMod 49571861) ^ 3025 = (2 : ZMod 49571861) ^ (1512 + 1512 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 1512 * (2 : ZMod 49571861) ^ 1512) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 26939451 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 49571861) ^ 6051 = 34105783 := by
        calc
          (2 : ZMod 49571861) ^ 6051 = (2 : ZMod 49571861) ^ (3025 + 3025 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 3025 * (2 : ZMod 49571861) ^ 3025) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 34105783 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 49571861) ^ 12102 = 21672035 := by
        calc
          (2 : ZMod 49571861) ^ 12102 = (2 : ZMod 49571861) ^ (6051 + 6051) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 6051 * (2 : ZMod 49571861) ^ 6051 := by rw [pow_add]
          _ = 21672035 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 49571861) ^ 24205 = 4845127 := by
        calc
          (2 : ZMod 49571861) ^ 24205 = (2 : ZMod 49571861) ^ (12102 + 12102 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 12102 * (2 : ZMod 49571861) ^ 12102) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 4845127 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 49571861) ^ 48410 = 5150969 := by
        calc
          (2 : ZMod 49571861) ^ 48410 = (2 : ZMod 49571861) ^ (24205 + 24205) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 24205 * (2 : ZMod 49571861) ^ 24205 := by rw [pow_add]
          _ = 5150969 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 49571861) ^ 96820 = 35332209 := by
        calc
          (2 : ZMod 49571861) ^ 96820 = (2 : ZMod 49571861) ^ (48410 + 48410) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 48410 * (2 : ZMod 49571861) ^ 48410 := by rw [pow_add]
          _ = 35332209 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 49571861) ^ 193640 = 39427646 := by
        calc
          (2 : ZMod 49571861) ^ 193640 = (2 : ZMod 49571861) ^ (96820 + 96820) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 96820 * (2 : ZMod 49571861) ^ 96820 := by rw [pow_add]
          _ = 39427646 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 49571861) ^ 387280 = 11869128 := by
        calc
          (2 : ZMod 49571861) ^ 387280 = (2 : ZMod 49571861) ^ (193640 + 193640) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 193640 * (2 : ZMod 49571861) ^ 193640 := by rw [pow_add]
          _ = 11869128 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 49571861) ^ 774560 = 9722646 := by
        calc
          (2 : ZMod 49571861) ^ 774560 = (2 : ZMod 49571861) ^ (387280 + 387280) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 387280 * (2 : ZMod 49571861) ^ 387280 := by rw [pow_add]
          _ = 9722646 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 49571861) ^ 1549120 = 24203891 := by
        calc
          (2 : ZMod 49571861) ^ 1549120 = (2 : ZMod 49571861) ^ (774560 + 774560) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 774560 * (2 : ZMod 49571861) ^ 774560 := by rw [pow_add]
          _ = 24203891 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 49571861) ^ 3098241 = 16548903 := by
        calc
          (2 : ZMod 49571861) ^ 3098241 = (2 : ZMod 49571861) ^ (1549120 + 1549120 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 1549120 * (2 : ZMod 49571861) ^ 1549120) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 16548903 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 49571861) ^ 6196482 = 66979 := by
        calc
          (2 : ZMod 49571861) ^ 6196482 = (2 : ZMod 49571861) ^ (3098241 + 3098241) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 3098241 * (2 : ZMod 49571861) ^ 3098241 := by rw [pow_add]
          _ = 66979 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 49571861) ^ 12392965 = 49437902 := by
        calc
          (2 : ZMod 49571861) ^ 12392965 = (2 : ZMod 49571861) ^ (6196482 + 6196482 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 6196482 * (2 : ZMod 49571861) ^ 6196482) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 49437902 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 49571861) ^ 24785930 = 49571860 := by
        calc
          (2 : ZMod 49571861) ^ 24785930 = (2 : ZMod 49571861) ^ (12392965 + 12392965) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 12392965 * (2 : ZMod 49571861) ^ 12392965 := by rw [pow_add]
          _ = 49571860 := by rw [factor_0_23]; decide
      change (2 : ZMod 49571861) ^ 24785930 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (2 : ZMod 49571861) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 49571861) ^ 2 = 4 := by
        calc
          (2 : ZMod 49571861) ^ 2 = (2 : ZMod 49571861) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 1 * (2 : ZMod 49571861) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 49571861) ^ 4 = 16 := by
        calc
          (2 : ZMod 49571861) ^ 4 = (2 : ZMod 49571861) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 2 * (2 : ZMod 49571861) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 49571861) ^ 9 = 512 := by
        calc
          (2 : ZMod 49571861) ^ 9 = (2 : ZMod 49571861) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 4 * (2 : ZMod 49571861) ^ 4) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 49571861) ^ 18 = 262144 := by
        calc
          (2 : ZMod 49571861) ^ 18 = (2 : ZMod 49571861) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 9 * (2 : ZMod 49571861) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 49571861) ^ 37 = 25754780 := by
        calc
          (2 : ZMod 49571861) ^ 37 = (2 : ZMod 49571861) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 18 * (2 : ZMod 49571861) ^ 18) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 25754780 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 49571861) ^ 75 = 27545300 := by
        calc
          (2 : ZMod 49571861) ^ 75 = (2 : ZMod 49571861) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 37 * (2 : ZMod 49571861) ^ 37) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 27545300 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 49571861) ^ 151 = 37021096 := by
        calc
          (2 : ZMod 49571861) ^ 151 = (2 : ZMod 49571861) ^ (75 + 75 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 75 * (2 : ZMod 49571861) ^ 75) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 37021096 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 49571861) ^ 302 = 24981602 := by
        calc
          (2 : ZMod 49571861) ^ 302 = (2 : ZMod 49571861) ^ (151 + 151) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 151 * (2 : ZMod 49571861) ^ 151 := by rw [pow_add]
          _ = 24981602 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 49571861) ^ 605 = 10932510 := by
        calc
          (2 : ZMod 49571861) ^ 605 = (2 : ZMod 49571861) ^ (302 + 302 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 302 * (2 : ZMod 49571861) ^ 302) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 10932510 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 49571861) ^ 1210 = 35154660 := by
        calc
          (2 : ZMod 49571861) ^ 1210 = (2 : ZMod 49571861) ^ (605 + 605) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 605 * (2 : ZMod 49571861) ^ 605 := by rw [pow_add]
          _ = 35154660 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 49571861) ^ 2420 = 28779764 := by
        calc
          (2 : ZMod 49571861) ^ 2420 = (2 : ZMod 49571861) ^ (1210 + 1210) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 1210 * (2 : ZMod 49571861) ^ 1210 := by rw [pow_add]
          _ = 28779764 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 49571861) ^ 4841 = 10981296 := by
        calc
          (2 : ZMod 49571861) ^ 4841 = (2 : ZMod 49571861) ^ (2420 + 2420 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 2420 * (2 : ZMod 49571861) ^ 2420) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 10981296 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 49571861) ^ 9682 = 5767989 := by
        calc
          (2 : ZMod 49571861) ^ 9682 = (2 : ZMod 49571861) ^ (4841 + 4841) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 4841 * (2 : ZMod 49571861) ^ 4841 := by rw [pow_add]
          _ = 5767989 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 49571861) ^ 19364 = 38312581 := by
        calc
          (2 : ZMod 49571861) ^ 19364 = (2 : ZMod 49571861) ^ (9682 + 9682) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 9682 * (2 : ZMod 49571861) ^ 9682 := by rw [pow_add]
          _ = 38312581 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 49571861) ^ 38728 = 26686575 := by
        calc
          (2 : ZMod 49571861) ^ 38728 = (2 : ZMod 49571861) ^ (19364 + 19364) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 19364 * (2 : ZMod 49571861) ^ 19364 := by rw [pow_add]
          _ = 26686575 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 49571861) ^ 77456 = 36467623 := by
        calc
          (2 : ZMod 49571861) ^ 77456 = (2 : ZMod 49571861) ^ (38728 + 38728) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 38728 * (2 : ZMod 49571861) ^ 38728 := by rw [pow_add]
          _ = 36467623 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 49571861) ^ 154912 = 12592181 := by
        calc
          (2 : ZMod 49571861) ^ 154912 = (2 : ZMod 49571861) ^ (77456 + 77456) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 77456 * (2 : ZMod 49571861) ^ 77456 := by rw [pow_add]
          _ = 12592181 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 49571861) ^ 309824 = 38720972 := by
        calc
          (2 : ZMod 49571861) ^ 309824 = (2 : ZMod 49571861) ^ (154912 + 154912) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 154912 * (2 : ZMod 49571861) ^ 154912 := by rw [pow_add]
          _ = 38720972 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 49571861) ^ 619648 = 46283368 := by
        calc
          (2 : ZMod 49571861) ^ 619648 = (2 : ZMod 49571861) ^ (309824 + 309824) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 309824 * (2 : ZMod 49571861) ^ 309824 := by rw [pow_add]
          _ = 46283368 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 49571861) ^ 1239296 = 35162038 := by
        calc
          (2 : ZMod 49571861) ^ 1239296 = (2 : ZMod 49571861) ^ (619648 + 619648) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 619648 * (2 : ZMod 49571861) ^ 619648 := by rw [pow_add]
          _ = 35162038 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 49571861) ^ 2478593 = 12560764 := by
        calc
          (2 : ZMod 49571861) ^ 2478593 = (2 : ZMod 49571861) ^ (1239296 + 1239296 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 1239296 * (2 : ZMod 49571861) ^ 1239296) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 12560764 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 49571861) ^ 4957186 = 33684108 := by
        calc
          (2 : ZMod 49571861) ^ 4957186 = (2 : ZMod 49571861) ^ (2478593 + 2478593) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 2478593 * (2 : ZMod 49571861) ^ 2478593 := by rw [pow_add]
          _ = 33684108 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 49571861) ^ 9914372 = 35599094 := by
        calc
          (2 : ZMod 49571861) ^ 9914372 = (2 : ZMod 49571861) ^ (4957186 + 4957186) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 4957186 * (2 : ZMod 49571861) ^ 4957186 := by rw [pow_add]
          _ = 35599094 := by rw [factor_1_22]; decide
      change (2 : ZMod 49571861) ^ 9914372 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (2 : ZMod 49571861) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 49571861) ^ 3 = 8 := by
        calc
          (2 : ZMod 49571861) ^ 3 = (2 : ZMod 49571861) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 1 * (2 : ZMod 49571861) ^ 1) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 49571861) ^ 7 = 128 := by
        calc
          (2 : ZMod 49571861) ^ 7 = (2 : ZMod 49571861) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 3 * (2 : ZMod 49571861) ^ 3) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 49571861) ^ 14 = 16384 := by
        calc
          (2 : ZMod 49571861) ^ 14 = (2 : ZMod 49571861) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 7 * (2 : ZMod 49571861) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 49571861) ^ 29 = 41152302 := by
        calc
          (2 : ZMod 49571861) ^ 29 = (2 : ZMod 49571861) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 14 * (2 : ZMod 49571861) ^ 14) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 41152302 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 49571861) ^ 58 = 22799817 := by
        calc
          (2 : ZMod 49571861) ^ 58 = (2 : ZMod 49571861) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 29 * (2 : ZMod 49571861) ^ 29 := by rw [pow_add]
          _ = 22799817 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 49571861) ^ 116 = 3174703 := by
        calc
          (2 : ZMod 49571861) ^ 116 = (2 : ZMod 49571861) ^ (58 + 58) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 58 * (2 : ZMod 49571861) ^ 58 := by rw [pow_add]
          _ = 3174703 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 49571861) ^ 232 = 36218994 := by
        calc
          (2 : ZMod 49571861) ^ 232 = (2 : ZMod 49571861) ^ (116 + 116) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 116 * (2 : ZMod 49571861) ^ 116 := by rw [pow_add]
          _ = 36218994 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 49571861) ^ 465 = 7396079 := by
        calc
          (2 : ZMod 49571861) ^ 465 = (2 : ZMod 49571861) ^ (232 + 232 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 232 * (2 : ZMod 49571861) ^ 232) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 7396079 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 49571861) ^ 930 = 30823073 := by
        calc
          (2 : ZMod 49571861) ^ 930 = (2 : ZMod 49571861) ^ (465 + 465) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 465 * (2 : ZMod 49571861) ^ 465 := by rw [pow_add]
          _ = 30823073 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 49571861) ^ 1861 = 21612568 := by
        calc
          (2 : ZMod 49571861) ^ 1861 = (2 : ZMod 49571861) ^ (930 + 930 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 930 * (2 : ZMod 49571861) ^ 930) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 21612568 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 49571861) ^ 3723 = 31636775 := by
        calc
          (2 : ZMod 49571861) ^ 3723 = (2 : ZMod 49571861) ^ (1861 + 1861 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 1861 * (2 : ZMod 49571861) ^ 1861) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 31636775 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 49571861) ^ 7447 = 29675494 := by
        calc
          (2 : ZMod 49571861) ^ 7447 = (2 : ZMod 49571861) ^ (3723 + 3723 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 3723 * (2 : ZMod 49571861) ^ 3723) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 29675494 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 49571861) ^ 14895 = 8546642 := by
        calc
          (2 : ZMod 49571861) ^ 14895 = (2 : ZMod 49571861) ^ (7447 + 7447 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 7447 * (2 : ZMod 49571861) ^ 7447) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 8546642 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 49571861) ^ 29790 = 10427305 := by
        calc
          (2 : ZMod 49571861) ^ 29790 = (2 : ZMod 49571861) ^ (14895 + 14895) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 14895 * (2 : ZMod 49571861) ^ 14895 := by rw [pow_add]
          _ = 10427305 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 49571861) ^ 59581 = 758740 := by
        calc
          (2 : ZMod 49571861) ^ 59581 = (2 : ZMod 49571861) ^ (29790 + 29790 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 29790 * (2 : ZMod 49571861) ^ 29790) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 758740 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 49571861) ^ 119163 = 16731614 := by
        calc
          (2 : ZMod 49571861) ^ 119163 = (2 : ZMod 49571861) ^ (59581 + 59581 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 59581 * (2 : ZMod 49571861) ^ 59581) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 16731614 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 49571861) ^ 238326 = 33850862 := by
        calc
          (2 : ZMod 49571861) ^ 238326 = (2 : ZMod 49571861) ^ (119163 + 119163) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 119163 * (2 : ZMod 49571861) ^ 119163 := by rw [pow_add]
          _ = 33850862 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 49571861) ^ 476652 = 26604494 := by
        calc
          (2 : ZMod 49571861) ^ 476652 = (2 : ZMod 49571861) ^ (238326 + 238326) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 238326 * (2 : ZMod 49571861) ^ 238326 := by rw [pow_add]
          _ = 26604494 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 49571861) ^ 953305 = 47351626 := by
        calc
          (2 : ZMod 49571861) ^ 953305 = (2 : ZMod 49571861) ^ (476652 + 476652 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 476652 * (2 : ZMod 49571861) ^ 476652) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 47351626 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 49571861) ^ 1906610 = 17597385 := by
        calc
          (2 : ZMod 49571861) ^ 1906610 = (2 : ZMod 49571861) ^ (953305 + 953305) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 953305 * (2 : ZMod 49571861) ^ 953305 := by rw [pow_add]
          _ = 17597385 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 49571861) ^ 3813220 = 28522236 := by
        calc
          (2 : ZMod 49571861) ^ 3813220 = (2 : ZMod 49571861) ^ (1906610 + 1906610) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 1906610 * (2 : ZMod 49571861) ^ 1906610 := by rw [pow_add]
          _ = 28522236 := by rw [factor_2_20]; decide
      change (2 : ZMod 49571861) ^ 3813220 ≠ 1
      rw [factor_2_21]
      decide
    ·
      have factor_3_0 : (2 : ZMod 49571861) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 49571861) ^ 2 = 4 := by
        calc
          (2 : ZMod 49571861) ^ 2 = (2 : ZMod 49571861) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 1 * (2 : ZMod 49571861) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 49571861) ^ 5 = 32 := by
        calc
          (2 : ZMod 49571861) ^ 5 = (2 : ZMod 49571861) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 2 * (2 : ZMod 49571861) ^ 2) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 49571861) ^ 10 = 1024 := by
        calc
          (2 : ZMod 49571861) ^ 10 = (2 : ZMod 49571861) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 5 * (2 : ZMod 49571861) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 49571861) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 49571861) ^ 20 = (2 : ZMod 49571861) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 10 * (2 : ZMod 49571861) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 49571861) ^ 40 = 7750796 := by
        calc
          (2 : ZMod 49571861) ^ 40 = (2 : ZMod 49571861) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 20 * (2 : ZMod 49571861) ^ 20 := by rw [pow_add]
          _ = 7750796 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 49571861) ^ 81 = 27884065 := by
        calc
          (2 : ZMod 49571861) ^ 81 = (2 : ZMod 49571861) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 40 * (2 : ZMod 49571861) ^ 40) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 27884065 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 49571861) ^ 163 = 47658278 := by
        calc
          (2 : ZMod 49571861) ^ 163 = (2 : ZMod 49571861) ^ (81 + 81 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 81 * (2 : ZMod 49571861) ^ 81) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 47658278 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 49571861) ^ 327 = 1767221 := by
        calc
          (2 : ZMod 49571861) ^ 327 = (2 : ZMod 49571861) ^ (163 + 163 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 163 * (2 : ZMod 49571861) ^ 163) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 1767221 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 49571861) ^ 654 = 42819841 := by
        calc
          (2 : ZMod 49571861) ^ 654 = (2 : ZMod 49571861) ^ (327 + 327) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 327 * (2 : ZMod 49571861) ^ 327 := by rw [pow_add]
          _ = 42819841 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 49571861) ^ 1308 = 20674530 := by
        calc
          (2 : ZMod 49571861) ^ 1308 = (2 : ZMod 49571861) ^ (654 + 654) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 654 * (2 : ZMod 49571861) ^ 654 := by rw [pow_add]
          _ = 20674530 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 49571861) ^ 2616 = 43224184 := by
        calc
          (2 : ZMod 49571861) ^ 2616 = (2 : ZMod 49571861) ^ (1308 + 1308) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 1308 * (2 : ZMod 49571861) ^ 1308 := by rw [pow_add]
          _ = 43224184 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 49571861) ^ 5233 = 6476618 := by
        calc
          (2 : ZMod 49571861) ^ 5233 = (2 : ZMod 49571861) ^ (2616 + 2616 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 2616 * (2 : ZMod 49571861) ^ 2616) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 6476618 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 49571861) ^ 10467 = 24185054 := by
        calc
          (2 : ZMod 49571861) ^ 10467 = (2 : ZMod 49571861) ^ (5233 + 5233 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 5233 * (2 : ZMod 49571861) ^ 5233) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 24185054 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 49571861) ^ 20934 = 8311624 := by
        calc
          (2 : ZMod 49571861) ^ 20934 = (2 : ZMod 49571861) ^ (10467 + 10467) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 10467 * (2 : ZMod 49571861) ^ 10467 := by rw [pow_add]
          _ = 8311624 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 49571861) ^ 41868 = 45458942 := by
        calc
          (2 : ZMod 49571861) ^ 41868 = (2 : ZMod 49571861) ^ (20934 + 20934) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 20934 * (2 : ZMod 49571861) ^ 20934 := by rw [pow_add]
          _ = 45458942 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 49571861) ^ 83736 = 2565477 := by
        calc
          (2 : ZMod 49571861) ^ 83736 = (2 : ZMod 49571861) ^ (41868 + 41868) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 41868 * (2 : ZMod 49571861) ^ 41868 := by rw [pow_add]
          _ = 2565477 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 49571861) ^ 167472 = 16252559 := by
        calc
          (2 : ZMod 49571861) ^ 167472 = (2 : ZMod 49571861) ^ (83736 + 83736) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 83736 * (2 : ZMod 49571861) ^ 83736 := by rw [pow_add]
          _ = 16252559 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 49571861) ^ 334945 = 10099221 := by
        calc
          (2 : ZMod 49571861) ^ 334945 = (2 : ZMod 49571861) ^ (167472 + 167472 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 167472 * (2 : ZMod 49571861) ^ 167472) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 10099221 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 49571861) ^ 669890 = 12083758 := by
        calc
          (2 : ZMod 49571861) ^ 669890 = (2 : ZMod 49571861) ^ (334945 + 334945) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 334945 * (2 : ZMod 49571861) ^ 334945 := by rw [pow_add]
          _ = 12083758 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 49571861) ^ 1339780 = 19084238 := by
        calc
          (2 : ZMod 49571861) ^ 1339780 = (2 : ZMod 49571861) ^ (669890 + 669890) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 669890 * (2 : ZMod 49571861) ^ 669890 := by rw [pow_add]
          _ = 19084238 := by rw [factor_3_19]; decide
      change (2 : ZMod 49571861) ^ 1339780 ≠ 1
      rw [factor_3_20]
      decide
    ·
      have factor_4_0 : (2 : ZMod 49571861) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 49571861) ^ 2 = 4 := by
        calc
          (2 : ZMod 49571861) ^ 2 = (2 : ZMod 49571861) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 1 * (2 : ZMod 49571861) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 49571861) ^ 4 = 16 := by
        calc
          (2 : ZMod 49571861) ^ 4 = (2 : ZMod 49571861) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 2 * (2 : ZMod 49571861) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 49571861) ^ 9 = 512 := by
        calc
          (2 : ZMod 49571861) ^ 9 = (2 : ZMod 49571861) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 4 * (2 : ZMod 49571861) ^ 4) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 49571861) ^ 18 = 262144 := by
        calc
          (2 : ZMod 49571861) ^ 18 = (2 : ZMod 49571861) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 9 * (2 : ZMod 49571861) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 49571861) ^ 37 = 25754780 := by
        calc
          (2 : ZMod 49571861) ^ 37 = (2 : ZMod 49571861) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 18 * (2 : ZMod 49571861) ^ 18) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 25754780 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 49571861) ^ 75 = 27545300 := by
        calc
          (2 : ZMod 49571861) ^ 75 = (2 : ZMod 49571861) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 37 * (2 : ZMod 49571861) ^ 37) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 27545300 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 49571861) ^ 150 = 18510548 := by
        calc
          (2 : ZMod 49571861) ^ 150 = (2 : ZMod 49571861) ^ (75 + 75) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 75 * (2 : ZMod 49571861) ^ 75 := by rw [pow_add]
          _ = 18510548 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 49571861) ^ 300 = 31031331 := by
        calc
          (2 : ZMod 49571861) ^ 300 = (2 : ZMod 49571861) ^ (150 + 150) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 150 * (2 : ZMod 49571861) ^ 150 := by rw [pow_add]
          _ = 31031331 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 49571861) ^ 601 = 31665695 := by
        calc
          (2 : ZMod 49571861) ^ 601 = (2 : ZMod 49571861) ^ (300 + 300 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 300 * (2 : ZMod 49571861) ^ 300) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 31665695 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 49571861) ^ 1202 = 33443417 := by
        calc
          (2 : ZMod 49571861) ^ 1202 = (2 : ZMod 49571861) ^ (601 + 601) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 601 * (2 : ZMod 49571861) ^ 601 := by rw [pow_add]
          _ = 33443417 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 49571861) ^ 2405 = 2270098 := by
        calc
          (2 : ZMod 49571861) ^ 2405 = (2 : ZMod 49571861) ^ (1202 + 1202 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = ((2 : ZMod 49571861) ^ 1202 * (2 : ZMod 49571861) ^ 1202) * (2 : ZMod 49571861) := by rw [pow_succ, pow_add]
          _ = 2270098 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 49571861) ^ 4810 = 2975627 := by
        calc
          (2 : ZMod 49571861) ^ 4810 = (2 : ZMod 49571861) ^ (2405 + 2405) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 2405 * (2 : ZMod 49571861) ^ 2405 := by rw [pow_add]
          _ = 2975627 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 49571861) ^ 9620 = 28518753 := by
        calc
          (2 : ZMod 49571861) ^ 9620 = (2 : ZMod 49571861) ^ (4810 + 4810) :=
            congrArg (fun n : ℕ => (2 : ZMod 49571861) ^ n) (by norm_num)
          _ = (2 : ZMod 49571861) ^ 4810 * (2 : ZMod 49571861) ^ 4810 := by rw [pow_add]
          _ = 28518753 := by rw [factor_4_12]; decide
      change (2 : ZMod 49571861) ^ 9620 ≠ 1
      rw [factor_4_13]
      decide

#print axioms prime_lucas_49571861

end TotientTailPeriodKiller
end Erdos249257
