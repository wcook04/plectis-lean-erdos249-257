import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_421119071 : Nat.Prime 421119071 := by
  apply lucas_primality 421119071 (7 : ZMod 421119071)
  ·
      have fermat_0 : (7 : ZMod 421119071) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 421119071) ^ 3 = 343 := by
        calc
          (7 : ZMod 421119071) ^ 3 = (7 : ZMod 421119071) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 1 * (7 : ZMod 421119071) ^ 1) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 421119071) ^ 6 = 117649 := by
        calc
          (7 : ZMod 421119071) ^ 6 = (7 : ZMod 421119071) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 3 * (7 : ZMod 421119071) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 421119071) ^ 12 = 365476929 := by
        calc
          (7 : ZMod 421119071) ^ 12 = (7 : ZMod 421119071) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 6 * (7 : ZMod 421119071) ^ 6 := by rw [pow_add]
          _ = 365476929 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 421119071) ^ 25 = 337072152 := by
        calc
          (7 : ZMod 421119071) ^ 25 = (7 : ZMod 421119071) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 12 * (7 : ZMod 421119071) ^ 12) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 337072152 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 421119071) ^ 50 = 28031952 := by
        calc
          (7 : ZMod 421119071) ^ 50 = (7 : ZMod 421119071) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 25 * (7 : ZMod 421119071) ^ 25 := by rw [pow_add]
          _ = 28031952 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 421119071) ^ 100 = 254564357 := by
        calc
          (7 : ZMod 421119071) ^ 100 = (7 : ZMod 421119071) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 50 * (7 : ZMod 421119071) ^ 50 := by rw [pow_add]
          _ = 254564357 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 421119071) ^ 200 = 176490608 := by
        calc
          (7 : ZMod 421119071) ^ 200 = (7 : ZMod 421119071) ^ (100 + 100) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 100 * (7 : ZMod 421119071) ^ 100 := by rw [pow_add]
          _ = 176490608 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 421119071) ^ 401 = 374622650 := by
        calc
          (7 : ZMod 421119071) ^ 401 = (7 : ZMod 421119071) ^ (200 + 200 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 200 * (7 : ZMod 421119071) ^ 200) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 374622650 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 421119071) ^ 803 = 159156345 := by
        calc
          (7 : ZMod 421119071) ^ 803 = (7 : ZMod 421119071) ^ (401 + 401 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 401 * (7 : ZMod 421119071) ^ 401) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 159156345 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 421119071) ^ 1606 = 70537534 := by
        calc
          (7 : ZMod 421119071) ^ 1606 = (7 : ZMod 421119071) ^ (803 + 803) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 803 * (7 : ZMod 421119071) ^ 803 := by rw [pow_add]
          _ = 70537534 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 421119071) ^ 3212 = 401863535 := by
        calc
          (7 : ZMod 421119071) ^ 3212 = (7 : ZMod 421119071) ^ (1606 + 1606) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 1606 * (7 : ZMod 421119071) ^ 1606 := by rw [pow_add]
          _ = 401863535 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 421119071) ^ 6425 = 399477860 := by
        calc
          (7 : ZMod 421119071) ^ 6425 = (7 : ZMod 421119071) ^ (3212 + 3212 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 3212 * (7 : ZMod 421119071) ^ 3212) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 399477860 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 421119071) ^ 12851 = 235210700 := by
        calc
          (7 : ZMod 421119071) ^ 12851 = (7 : ZMod 421119071) ^ (6425 + 6425 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 6425 * (7 : ZMod 421119071) ^ 6425) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 235210700 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 421119071) ^ 25703 = 162989690 := by
        calc
          (7 : ZMod 421119071) ^ 25703 = (7 : ZMod 421119071) ^ (12851 + 12851 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 12851 * (7 : ZMod 421119071) ^ 12851) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 162989690 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 421119071) ^ 51406 = 240250002 := by
        calc
          (7 : ZMod 421119071) ^ 51406 = (7 : ZMod 421119071) ^ (25703 + 25703) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 25703 * (7 : ZMod 421119071) ^ 25703 := by rw [pow_add]
          _ = 240250002 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 421119071) ^ 102812 = 408371942 := by
        calc
          (7 : ZMod 421119071) ^ 102812 = (7 : ZMod 421119071) ^ (51406 + 51406) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 51406 * (7 : ZMod 421119071) ^ 51406 := by rw [pow_add]
          _ = 408371942 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 421119071) ^ 205624 = 83078220 := by
        calc
          (7 : ZMod 421119071) ^ 205624 = (7 : ZMod 421119071) ^ (102812 + 102812) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 102812 * (7 : ZMod 421119071) ^ 102812 := by rw [pow_add]
          _ = 83078220 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 421119071) ^ 411249 = 40497939 := by
        calc
          (7 : ZMod 421119071) ^ 411249 = (7 : ZMod 421119071) ^ (205624 + 205624 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 205624 * (7 : ZMod 421119071) ^ 205624) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 40497939 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 421119071) ^ 822498 = 309474399 := by
        calc
          (7 : ZMod 421119071) ^ 822498 = (7 : ZMod 421119071) ^ (411249 + 411249) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 411249 * (7 : ZMod 421119071) ^ 411249 := by rw [pow_add]
          _ = 309474399 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 421119071) ^ 1644996 = 377801410 := by
        calc
          (7 : ZMod 421119071) ^ 1644996 = (7 : ZMod 421119071) ^ (822498 + 822498) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 822498 * (7 : ZMod 421119071) ^ 822498 := by rw [pow_add]
          _ = 377801410 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 421119071) ^ 3289992 = 345782618 := by
        calc
          (7 : ZMod 421119071) ^ 3289992 = (7 : ZMod 421119071) ^ (1644996 + 1644996) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 1644996 * (7 : ZMod 421119071) ^ 1644996 := by rw [pow_add]
          _ = 345782618 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 421119071) ^ 6579985 = 49741313 := by
        calc
          (7 : ZMod 421119071) ^ 6579985 = (7 : ZMod 421119071) ^ (3289992 + 3289992 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 3289992 * (7 : ZMod 421119071) ^ 3289992) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 49741313 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 421119071) ^ 13159970 = 288951166 := by
        calc
          (7 : ZMod 421119071) ^ 13159970 = (7 : ZMod 421119071) ^ (6579985 + 6579985) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 6579985 * (7 : ZMod 421119071) ^ 6579985 := by rw [pow_add]
          _ = 288951166 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 421119071) ^ 26319941 = 379051640 := by
        calc
          (7 : ZMod 421119071) ^ 26319941 = (7 : ZMod 421119071) ^ (13159970 + 13159970 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 13159970 * (7 : ZMod 421119071) ^ 13159970) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 379051640 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 421119071) ^ 52639883 = 131016156 := by
        calc
          (7 : ZMod 421119071) ^ 52639883 = (7 : ZMod 421119071) ^ (26319941 + 26319941 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 26319941 * (7 : ZMod 421119071) ^ 26319941) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 131016156 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 421119071) ^ 105279767 = 24516914 := by
        calc
          (7 : ZMod 421119071) ^ 105279767 = (7 : ZMod 421119071) ^ (52639883 + 52639883 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 52639883 * (7 : ZMod 421119071) ^ 52639883) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 24516914 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 421119071) ^ 210559535 = 421119070 := by
        calc
          (7 : ZMod 421119071) ^ 210559535 = (7 : ZMod 421119071) ^ (105279767 + 105279767 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 105279767 * (7 : ZMod 421119071) ^ 105279767) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 421119070 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 421119071) ^ 421119070 = 1 := by
        calc
          (7 : ZMod 421119071) ^ 421119070 = (7 : ZMod 421119071) ^ (210559535 + 210559535) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 210559535 * (7 : ZMod 421119071) ^ 210559535 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17, 1), (2477171, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17, 1), (2477171, 1)] : List FactorBlock).map factorBlockValue).prod = 421119071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 421119071) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 421119071) ^ 3 = 343 := by
        calc
          (7 : ZMod 421119071) ^ 3 = (7 : ZMod 421119071) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 1 * (7 : ZMod 421119071) ^ 1) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 421119071) ^ 6 = 117649 := by
        calc
          (7 : ZMod 421119071) ^ 6 = (7 : ZMod 421119071) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 3 * (7 : ZMod 421119071) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 421119071) ^ 12 = 365476929 := by
        calc
          (7 : ZMod 421119071) ^ 12 = (7 : ZMod 421119071) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 6 * (7 : ZMod 421119071) ^ 6 := by rw [pow_add]
          _ = 365476929 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 421119071) ^ 25 = 337072152 := by
        calc
          (7 : ZMod 421119071) ^ 25 = (7 : ZMod 421119071) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 12 * (7 : ZMod 421119071) ^ 12) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 337072152 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 421119071) ^ 50 = 28031952 := by
        calc
          (7 : ZMod 421119071) ^ 50 = (7 : ZMod 421119071) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 25 * (7 : ZMod 421119071) ^ 25 := by rw [pow_add]
          _ = 28031952 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 421119071) ^ 100 = 254564357 := by
        calc
          (7 : ZMod 421119071) ^ 100 = (7 : ZMod 421119071) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 50 * (7 : ZMod 421119071) ^ 50 := by rw [pow_add]
          _ = 254564357 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 421119071) ^ 200 = 176490608 := by
        calc
          (7 : ZMod 421119071) ^ 200 = (7 : ZMod 421119071) ^ (100 + 100) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 100 * (7 : ZMod 421119071) ^ 100 := by rw [pow_add]
          _ = 176490608 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 421119071) ^ 401 = 374622650 := by
        calc
          (7 : ZMod 421119071) ^ 401 = (7 : ZMod 421119071) ^ (200 + 200 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 200 * (7 : ZMod 421119071) ^ 200) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 374622650 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 421119071) ^ 803 = 159156345 := by
        calc
          (7 : ZMod 421119071) ^ 803 = (7 : ZMod 421119071) ^ (401 + 401 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 401 * (7 : ZMod 421119071) ^ 401) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 159156345 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 421119071) ^ 1606 = 70537534 := by
        calc
          (7 : ZMod 421119071) ^ 1606 = (7 : ZMod 421119071) ^ (803 + 803) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 803 * (7 : ZMod 421119071) ^ 803 := by rw [pow_add]
          _ = 70537534 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 421119071) ^ 3212 = 401863535 := by
        calc
          (7 : ZMod 421119071) ^ 3212 = (7 : ZMod 421119071) ^ (1606 + 1606) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 1606 * (7 : ZMod 421119071) ^ 1606 := by rw [pow_add]
          _ = 401863535 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 421119071) ^ 6425 = 399477860 := by
        calc
          (7 : ZMod 421119071) ^ 6425 = (7 : ZMod 421119071) ^ (3212 + 3212 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 3212 * (7 : ZMod 421119071) ^ 3212) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 399477860 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 421119071) ^ 12851 = 235210700 := by
        calc
          (7 : ZMod 421119071) ^ 12851 = (7 : ZMod 421119071) ^ (6425 + 6425 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 6425 * (7 : ZMod 421119071) ^ 6425) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 235210700 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 421119071) ^ 25703 = 162989690 := by
        calc
          (7 : ZMod 421119071) ^ 25703 = (7 : ZMod 421119071) ^ (12851 + 12851 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 12851 * (7 : ZMod 421119071) ^ 12851) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 162989690 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 421119071) ^ 51406 = 240250002 := by
        calc
          (7 : ZMod 421119071) ^ 51406 = (7 : ZMod 421119071) ^ (25703 + 25703) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 25703 * (7 : ZMod 421119071) ^ 25703 := by rw [pow_add]
          _ = 240250002 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 421119071) ^ 102812 = 408371942 := by
        calc
          (7 : ZMod 421119071) ^ 102812 = (7 : ZMod 421119071) ^ (51406 + 51406) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 51406 * (7 : ZMod 421119071) ^ 51406 := by rw [pow_add]
          _ = 408371942 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 421119071) ^ 205624 = 83078220 := by
        calc
          (7 : ZMod 421119071) ^ 205624 = (7 : ZMod 421119071) ^ (102812 + 102812) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 102812 * (7 : ZMod 421119071) ^ 102812 := by rw [pow_add]
          _ = 83078220 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 421119071) ^ 411249 = 40497939 := by
        calc
          (7 : ZMod 421119071) ^ 411249 = (7 : ZMod 421119071) ^ (205624 + 205624 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 205624 * (7 : ZMod 421119071) ^ 205624) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 40497939 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 421119071) ^ 822498 = 309474399 := by
        calc
          (7 : ZMod 421119071) ^ 822498 = (7 : ZMod 421119071) ^ (411249 + 411249) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 411249 * (7 : ZMod 421119071) ^ 411249 := by rw [pow_add]
          _ = 309474399 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 421119071) ^ 1644996 = 377801410 := by
        calc
          (7 : ZMod 421119071) ^ 1644996 = (7 : ZMod 421119071) ^ (822498 + 822498) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 822498 * (7 : ZMod 421119071) ^ 822498 := by rw [pow_add]
          _ = 377801410 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 421119071) ^ 3289992 = 345782618 := by
        calc
          (7 : ZMod 421119071) ^ 3289992 = (7 : ZMod 421119071) ^ (1644996 + 1644996) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 1644996 * (7 : ZMod 421119071) ^ 1644996 := by rw [pow_add]
          _ = 345782618 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 421119071) ^ 6579985 = 49741313 := by
        calc
          (7 : ZMod 421119071) ^ 6579985 = (7 : ZMod 421119071) ^ (3289992 + 3289992 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 3289992 * (7 : ZMod 421119071) ^ 3289992) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 49741313 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 421119071) ^ 13159970 = 288951166 := by
        calc
          (7 : ZMod 421119071) ^ 13159970 = (7 : ZMod 421119071) ^ (6579985 + 6579985) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 6579985 * (7 : ZMod 421119071) ^ 6579985 := by rw [pow_add]
          _ = 288951166 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 421119071) ^ 26319941 = 379051640 := by
        calc
          (7 : ZMod 421119071) ^ 26319941 = (7 : ZMod 421119071) ^ (13159970 + 13159970 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 13159970 * (7 : ZMod 421119071) ^ 13159970) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 379051640 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 421119071) ^ 52639883 = 131016156 := by
        calc
          (7 : ZMod 421119071) ^ 52639883 = (7 : ZMod 421119071) ^ (26319941 + 26319941 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 26319941 * (7 : ZMod 421119071) ^ 26319941) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 131016156 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 421119071) ^ 105279767 = 24516914 := by
        calc
          (7 : ZMod 421119071) ^ 105279767 = (7 : ZMod 421119071) ^ (52639883 + 52639883 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 52639883 * (7 : ZMod 421119071) ^ 52639883) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 24516914 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 421119071) ^ 210559535 = 421119070 := by
        calc
          (7 : ZMod 421119071) ^ 210559535 = (7 : ZMod 421119071) ^ (105279767 + 105279767 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 105279767 * (7 : ZMod 421119071) ^ 105279767) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 421119070 := by rw [factor_0_26]; decide
      change (7 : ZMod 421119071) ^ 210559535 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (7 : ZMod 421119071) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 421119071) ^ 2 = 49 := by
        calc
          (7 : ZMod 421119071) ^ 2 = (7 : ZMod 421119071) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 1 * (7 : ZMod 421119071) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 421119071) ^ 5 = 16807 := by
        calc
          (7 : ZMod 421119071) ^ 5 = (7 : ZMod 421119071) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 2 * (7 : ZMod 421119071) ^ 2) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 421119071) ^ 10 = 282475249 := by
        calc
          (7 : ZMod 421119071) ^ 10 = (7 : ZMod 421119071) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 5 * (7 : ZMod 421119071) ^ 5 := by rw [pow_add]
          _ = 282475249 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 421119071) ^ 20 = 99417887 := by
        calc
          (7 : ZMod 421119071) ^ 20 = (7 : ZMod 421119071) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 10 * (7 : ZMod 421119071) ^ 10 := by rw [pow_add]
          _ = 99417887 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 421119071) ^ 40 = 251089382 := by
        calc
          (7 : ZMod 421119071) ^ 40 = (7 : ZMod 421119071) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 20 * (7 : ZMod 421119071) ^ 20 := by rw [pow_add]
          _ = 251089382 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 421119071) ^ 80 = 137724068 := by
        calc
          (7 : ZMod 421119071) ^ 80 = (7 : ZMod 421119071) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 40 * (7 : ZMod 421119071) ^ 40 := by rw [pow_add]
          _ = 137724068 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 421119071) ^ 160 = 46207924 := by
        calc
          (7 : ZMod 421119071) ^ 160 = (7 : ZMod 421119071) ^ (80 + 80) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 80 * (7 : ZMod 421119071) ^ 80 := by rw [pow_add]
          _ = 46207924 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 421119071) ^ 321 = 59900134 := by
        calc
          (7 : ZMod 421119071) ^ 321 = (7 : ZMod 421119071) ^ (160 + 160 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 160 * (7 : ZMod 421119071) ^ 160) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 59900134 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 421119071) ^ 642 = 185459549 := by
        calc
          (7 : ZMod 421119071) ^ 642 = (7 : ZMod 421119071) ^ (321 + 321) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 321 * (7 : ZMod 421119071) ^ 321 := by rw [pow_add]
          _ = 185459549 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 421119071) ^ 1285 = 117303616 := by
        calc
          (7 : ZMod 421119071) ^ 1285 = (7 : ZMod 421119071) ^ (642 + 642 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 642 * (7 : ZMod 421119071) ^ 642) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 117303616 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 421119071) ^ 2570 = 249270244 := by
        calc
          (7 : ZMod 421119071) ^ 2570 = (7 : ZMod 421119071) ^ (1285 + 1285) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 1285 * (7 : ZMod 421119071) ^ 1285 := by rw [pow_add]
          _ = 249270244 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 421119071) ^ 5140 = 112104849 := by
        calc
          (7 : ZMod 421119071) ^ 5140 = (7 : ZMod 421119071) ^ (2570 + 2570) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 2570 * (7 : ZMod 421119071) ^ 2570 := by rw [pow_add]
          _ = 112104849 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 421119071) ^ 10281 = 36607540 := by
        calc
          (7 : ZMod 421119071) ^ 10281 = (7 : ZMod 421119071) ^ (5140 + 5140 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 5140 * (7 : ZMod 421119071) ^ 5140) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 36607540 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 421119071) ^ 20562 = 346613927 := by
        calc
          (7 : ZMod 421119071) ^ 20562 = (7 : ZMod 421119071) ^ (10281 + 10281) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 10281 * (7 : ZMod 421119071) ^ 10281 := by rw [pow_add]
          _ = 346613927 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 421119071) ^ 41124 = 74072272 := by
        calc
          (7 : ZMod 421119071) ^ 41124 = (7 : ZMod 421119071) ^ (20562 + 20562) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 20562 * (7 : ZMod 421119071) ^ 20562 := by rw [pow_add]
          _ = 74072272 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 421119071) ^ 82249 = 418970468 := by
        calc
          (7 : ZMod 421119071) ^ 82249 = (7 : ZMod 421119071) ^ (41124 + 41124 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 41124 * (7 : ZMod 421119071) ^ 41124) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 418970468 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 421119071) ^ 164499 = 49809936 := by
        calc
          (7 : ZMod 421119071) ^ 164499 = (7 : ZMod 421119071) ^ (82249 + 82249 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 82249 * (7 : ZMod 421119071) ^ 82249) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 49809936 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 421119071) ^ 328999 = 278476291 := by
        calc
          (7 : ZMod 421119071) ^ 328999 = (7 : ZMod 421119071) ^ (164499 + 164499 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 164499 * (7 : ZMod 421119071) ^ 164499) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 278476291 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 421119071) ^ 657998 = 150635148 := by
        calc
          (7 : ZMod 421119071) ^ 657998 = (7 : ZMod 421119071) ^ (328999 + 328999) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 328999 * (7 : ZMod 421119071) ^ 328999 := by rw [pow_add]
          _ = 150635148 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 421119071) ^ 1315997 = 78842467 := by
        calc
          (7 : ZMod 421119071) ^ 1315997 = (7 : ZMod 421119071) ^ (657998 + 657998 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 657998 * (7 : ZMod 421119071) ^ 657998) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 78842467 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 421119071) ^ 2631994 = 206805799 := by
        calc
          (7 : ZMod 421119071) ^ 2631994 = (7 : ZMod 421119071) ^ (1315997 + 1315997) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 1315997 * (7 : ZMod 421119071) ^ 1315997 := by rw [pow_add]
          _ = 206805799 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 421119071) ^ 5263988 = 419994611 := by
        calc
          (7 : ZMod 421119071) ^ 5263988 = (7 : ZMod 421119071) ^ (2631994 + 2631994) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 2631994 * (7 : ZMod 421119071) ^ 2631994 := by rw [pow_add]
          _ = 419994611 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 421119071) ^ 10527976 = 210840458 := by
        calc
          (7 : ZMod 421119071) ^ 10527976 = (7 : ZMod 421119071) ^ (5263988 + 5263988) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 5263988 * (7 : ZMod 421119071) ^ 5263988 := by rw [pow_add]
          _ = 210840458 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 421119071) ^ 21055953 = 229775195 := by
        calc
          (7 : ZMod 421119071) ^ 21055953 = (7 : ZMod 421119071) ^ (10527976 + 10527976 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 10527976 * (7 : ZMod 421119071) ^ 10527976) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 229775195 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 421119071) ^ 42111907 = 154117102 := by
        calc
          (7 : ZMod 421119071) ^ 42111907 = (7 : ZMod 421119071) ^ (21055953 + 21055953 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 21055953 * (7 : ZMod 421119071) ^ 21055953) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 154117102 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 421119071) ^ 84223814 = 319567672 := by
        calc
          (7 : ZMod 421119071) ^ 84223814 = (7 : ZMod 421119071) ^ (42111907 + 42111907) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 42111907 * (7 : ZMod 421119071) ^ 42111907 := by rw [pow_add]
          _ = 319567672 := by rw [factor_1_25]; decide
      change (7 : ZMod 421119071) ^ 84223814 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (7 : ZMod 421119071) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 421119071) ^ 2 = 49 := by
        calc
          (7 : ZMod 421119071) ^ 2 = (7 : ZMod 421119071) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 1 * (7 : ZMod 421119071) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 421119071) ^ 5 = 16807 := by
        calc
          (7 : ZMod 421119071) ^ 5 = (7 : ZMod 421119071) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 2 * (7 : ZMod 421119071) ^ 2) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 421119071) ^ 11 = 292850459 := by
        calc
          (7 : ZMod 421119071) ^ 11 = (7 : ZMod 421119071) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 5 * (7 : ZMod 421119071) ^ 5) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 292850459 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 421119071) ^ 23 = 410809561 := by
        calc
          (7 : ZMod 421119071) ^ 23 = (7 : ZMod 421119071) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 11 * (7 : ZMod 421119071) ^ 11) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 410809561 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 421119071) ^ 47 = 384368225 := by
        calc
          (7 : ZMod 421119071) ^ 47 = (7 : ZMod 421119071) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 23 * (7 : ZMod 421119071) ^ 23) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 384368225 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 421119071) ^ 94 = 226989599 := by
        calc
          (7 : ZMod 421119071) ^ 94 = (7 : ZMod 421119071) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 47 * (7 : ZMod 421119071) ^ 47 := by rw [pow_add]
          _ = 226989599 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 421119071) ^ 188 = 81644167 := by
        calc
          (7 : ZMod 421119071) ^ 188 = (7 : ZMod 421119071) ^ (94 + 94) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 94 * (7 : ZMod 421119071) ^ 94 := by rw [pow_add]
          _ = 81644167 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 421119071) ^ 377 = 274902341 := by
        calc
          (7 : ZMod 421119071) ^ 377 = (7 : ZMod 421119071) ^ (188 + 188 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 188 * (7 : ZMod 421119071) ^ 188) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 274902341 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 421119071) ^ 755 = 308522580 := by
        calc
          (7 : ZMod 421119071) ^ 755 = (7 : ZMod 421119071) ^ (377 + 377 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 377 * (7 : ZMod 421119071) ^ 377) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 308522580 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 421119071) ^ 1511 = 240907993 := by
        calc
          (7 : ZMod 421119071) ^ 1511 = (7 : ZMod 421119071) ^ (755 + 755 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 755 * (7 : ZMod 421119071) ^ 755) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 240907993 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 421119071) ^ 3023 = 415265528 := by
        calc
          (7 : ZMod 421119071) ^ 3023 = (7 : ZMod 421119071) ^ (1511 + 1511 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 1511 * (7 : ZMod 421119071) ^ 1511) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 415265528 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 421119071) ^ 6047 = 234920035 := by
        calc
          (7 : ZMod 421119071) ^ 6047 = (7 : ZMod 421119071) ^ (3023 + 3023 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 3023 * (7 : ZMod 421119071) ^ 3023) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 234920035 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 421119071) ^ 12095 = 174024712 := by
        calc
          (7 : ZMod 421119071) ^ 12095 = (7 : ZMod 421119071) ^ (6047 + 6047 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 6047 * (7 : ZMod 421119071) ^ 6047) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 174024712 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 421119071) ^ 24191 = 334642271 := by
        calc
          (7 : ZMod 421119071) ^ 24191 = (7 : ZMod 421119071) ^ (12095 + 12095 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 12095 * (7 : ZMod 421119071) ^ 12095) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 334642271 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 421119071) ^ 48382 = 264231290 := by
        calc
          (7 : ZMod 421119071) ^ 48382 = (7 : ZMod 421119071) ^ (24191 + 24191) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 24191 * (7 : ZMod 421119071) ^ 24191 := by rw [pow_add]
          _ = 264231290 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 421119071) ^ 96764 = 332474887 := by
        calc
          (7 : ZMod 421119071) ^ 96764 = (7 : ZMod 421119071) ^ (48382 + 48382) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 48382 * (7 : ZMod 421119071) ^ 48382 := by rw [pow_add]
          _ = 332474887 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 421119071) ^ 193528 = 64324846 := by
        calc
          (7 : ZMod 421119071) ^ 193528 = (7 : ZMod 421119071) ^ (96764 + 96764) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 96764 * (7 : ZMod 421119071) ^ 96764 := by rw [pow_add]
          _ = 64324846 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 421119071) ^ 387057 = 371628729 := by
        calc
          (7 : ZMod 421119071) ^ 387057 = (7 : ZMod 421119071) ^ (193528 + 193528 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 193528 * (7 : ZMod 421119071) ^ 193528) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 371628729 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 421119071) ^ 774115 = 283956571 := by
        calc
          (7 : ZMod 421119071) ^ 774115 = (7 : ZMod 421119071) ^ (387057 + 387057 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 387057 * (7 : ZMod 421119071) ^ 387057) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 283956571 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 421119071) ^ 1548231 = 407752905 := by
        calc
          (7 : ZMod 421119071) ^ 1548231 = (7 : ZMod 421119071) ^ (774115 + 774115 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 774115 * (7 : ZMod 421119071) ^ 774115) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 407752905 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 421119071) ^ 3096463 = 294391032 := by
        calc
          (7 : ZMod 421119071) ^ 3096463 = (7 : ZMod 421119071) ^ (1548231 + 1548231 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 1548231 * (7 : ZMod 421119071) ^ 1548231) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 294391032 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 421119071) ^ 6192927 = 199138850 := by
        calc
          (7 : ZMod 421119071) ^ 6192927 = (7 : ZMod 421119071) ^ (3096463 + 3096463 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 3096463 * (7 : ZMod 421119071) ^ 3096463) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 199138850 := by rw [factor_2_21]; decide
      have factor_2_23 : (7 : ZMod 421119071) ^ 12385855 = 249105214 := by
        calc
          (7 : ZMod 421119071) ^ 12385855 = (7 : ZMod 421119071) ^ (6192927 + 6192927 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 6192927 * (7 : ZMod 421119071) ^ 6192927) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 249105214 := by rw [factor_2_22]; decide
      have factor_2_24 : (7 : ZMod 421119071) ^ 24771710 = 291551835 := by
        calc
          (7 : ZMod 421119071) ^ 24771710 = (7 : ZMod 421119071) ^ (12385855 + 12385855) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 12385855 * (7 : ZMod 421119071) ^ 12385855 := by rw [pow_add]
          _ = 291551835 := by rw [factor_2_23]; decide
      change (7 : ZMod 421119071) ^ 24771710 ≠ 1
      rw [factor_2_24]
      decide
    ·
      have factor_3_0 : (7 : ZMod 421119071) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 421119071) ^ 2 = 49 := by
        calc
          (7 : ZMod 421119071) ^ 2 = (7 : ZMod 421119071) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 1 * (7 : ZMod 421119071) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 421119071) ^ 5 = 16807 := by
        calc
          (7 : ZMod 421119071) ^ 5 = (7 : ZMod 421119071) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 2 * (7 : ZMod 421119071) ^ 2) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 421119071) ^ 10 = 282475249 := by
        calc
          (7 : ZMod 421119071) ^ 10 = (7 : ZMod 421119071) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 5 * (7 : ZMod 421119071) ^ 5 := by rw [pow_add]
          _ = 282475249 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 421119071) ^ 21 = 274806138 := by
        calc
          (7 : ZMod 421119071) ^ 21 = (7 : ZMod 421119071) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 10 * (7 : ZMod 421119071) ^ 10) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 274806138 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 421119071) ^ 42 = 90926659 := by
        calc
          (7 : ZMod 421119071) ^ 42 = (7 : ZMod 421119071) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 21 * (7 : ZMod 421119071) ^ 21 := by rw [pow_add]
          _ = 90926659 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 421119071) ^ 85 = 257996660 := by
        calc
          (7 : ZMod 421119071) ^ 85 = (7 : ZMod 421119071) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = ((7 : ZMod 421119071) ^ 42 * (7 : ZMod 421119071) ^ 42) * (7 : ZMod 421119071) := by rw [pow_succ, pow_add]
          _ = 257996660 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 421119071) ^ 170 = 388527585 := by
        calc
          (7 : ZMod 421119071) ^ 170 = (7 : ZMod 421119071) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (7 : ZMod 421119071) ^ n) (by norm_num)
          _ = (7 : ZMod 421119071) ^ 85 * (7 : ZMod 421119071) ^ 85 := by rw [pow_add]
          _ = 388527585 := by rw [factor_3_6]; decide
      change (7 : ZMod 421119071) ^ 170 ≠ 1
      rw [factor_3_7]
      decide

#print axioms prime_lucas_421119071

end TotientTailPeriodKiller
end Erdos249257
