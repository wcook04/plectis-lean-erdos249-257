import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_491213659 : Nat.Prime 491213659 := by
  apply lucas_primality 491213659 (2 : ZMod 491213659)
  ·
      have fermat_0 : (2 : ZMod 491213659) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 491213659) ^ 3 = 8 := by
        calc
          (2 : ZMod 491213659) ^ 3 = (2 : ZMod 491213659) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 1 * (2 : ZMod 491213659) ^ 1) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 491213659) ^ 7 = 128 := by
        calc
          (2 : ZMod 491213659) ^ 7 = (2 : ZMod 491213659) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 3 * (2 : ZMod 491213659) ^ 3) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 491213659) ^ 14 = 16384 := by
        calc
          (2 : ZMod 491213659) ^ 14 = (2 : ZMod 491213659) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 7 * (2 : ZMod 491213659) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 491213659) ^ 29 = 45657253 := by
        calc
          (2 : ZMod 491213659) ^ 29 = (2 : ZMod 491213659) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 14 * (2 : ZMod 491213659) ^ 14) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 45657253 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 491213659) ^ 58 = 224620372 := by
        calc
          (2 : ZMod 491213659) ^ 58 = (2 : ZMod 491213659) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 29 * (2 : ZMod 491213659) ^ 29 := by rw [pow_add]
          _ = 224620372 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 491213659) ^ 117 = 42967600 := by
        calc
          (2 : ZMod 491213659) ^ 117 = (2 : ZMod 491213659) ^ (58 + 58 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 58 * (2 : ZMod 491213659) ^ 58) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 42967600 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 491213659) ^ 234 = 392749975 := by
        calc
          (2 : ZMod 491213659) ^ 234 = (2 : ZMod 491213659) ^ (117 + 117) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 117 * (2 : ZMod 491213659) ^ 117 := by rw [pow_add]
          _ = 392749975 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 491213659) ^ 468 = 307613722 := by
        calc
          (2 : ZMod 491213659) ^ 468 = (2 : ZMod 491213659) ^ (234 + 234) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 234 * (2 : ZMod 491213659) ^ 234 := by rw [pow_add]
          _ = 307613722 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 491213659) ^ 936 = 271833926 := by
        calc
          (2 : ZMod 491213659) ^ 936 = (2 : ZMod 491213659) ^ (468 + 468) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 468 * (2 : ZMod 491213659) ^ 468 := by rw [pow_add]
          _ = 271833926 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 491213659) ^ 1873 = 454673491 := by
        calc
          (2 : ZMod 491213659) ^ 1873 = (2 : ZMod 491213659) ^ (936 + 936 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 936 * (2 : ZMod 491213659) ^ 936) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 454673491 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 491213659) ^ 3747 = 132992813 := by
        calc
          (2 : ZMod 491213659) ^ 3747 = (2 : ZMod 491213659) ^ (1873 + 1873 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 1873 * (2 : ZMod 491213659) ^ 1873) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 132992813 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 491213659) ^ 7495 = 177615627 := by
        calc
          (2 : ZMod 491213659) ^ 7495 = (2 : ZMod 491213659) ^ (3747 + 3747 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 3747 * (2 : ZMod 491213659) ^ 3747) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 177615627 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 491213659) ^ 14990 = 345982624 := by
        calc
          (2 : ZMod 491213659) ^ 14990 = (2 : ZMod 491213659) ^ (7495 + 7495) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 7495 * (2 : ZMod 491213659) ^ 7495 := by rw [pow_add]
          _ = 345982624 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 491213659) ^ 29981 = 366592478 := by
        calc
          (2 : ZMod 491213659) ^ 29981 = (2 : ZMod 491213659) ^ (14990 + 14990 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 14990 * (2 : ZMod 491213659) ^ 14990) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 366592478 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 491213659) ^ 59962 = 278966644 := by
        calc
          (2 : ZMod 491213659) ^ 59962 = (2 : ZMod 491213659) ^ (29981 + 29981) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 29981 * (2 : ZMod 491213659) ^ 29981 := by rw [pow_add]
          _ = 278966644 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 491213659) ^ 119925 = 272210003 := by
        calc
          (2 : ZMod 491213659) ^ 119925 = (2 : ZMod 491213659) ^ (59962 + 59962 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 59962 * (2 : ZMod 491213659) ^ 59962) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 272210003 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 491213659) ^ 239850 = 112315133 := by
        calc
          (2 : ZMod 491213659) ^ 239850 = (2 : ZMod 491213659) ^ (119925 + 119925) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 119925 * (2 : ZMod 491213659) ^ 119925 := by rw [pow_add]
          _ = 112315133 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 491213659) ^ 479700 = 101527385 := by
        calc
          (2 : ZMod 491213659) ^ 479700 = (2 : ZMod 491213659) ^ (239850 + 239850) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 239850 * (2 : ZMod 491213659) ^ 239850 := by rw [pow_add]
          _ = 101527385 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 491213659) ^ 959401 = 488429472 := by
        calc
          (2 : ZMod 491213659) ^ 959401 = (2 : ZMod 491213659) ^ (479700 + 479700 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 479700 * (2 : ZMod 491213659) ^ 479700) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 488429472 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 491213659) ^ 1918803 = 200210239 := by
        calc
          (2 : ZMod 491213659) ^ 1918803 = (2 : ZMod 491213659) ^ (959401 + 959401 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 959401 * (2 : ZMod 491213659) ^ 959401) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 200210239 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 491213659) ^ 3837606 = 486518030 := by
        calc
          (2 : ZMod 491213659) ^ 3837606 = (2 : ZMod 491213659) ^ (1918803 + 1918803) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 1918803 * (2 : ZMod 491213659) ^ 1918803 := by rw [pow_add]
          _ = 486518030 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 491213659) ^ 7675213 = 139601875 := by
        calc
          (2 : ZMod 491213659) ^ 7675213 = (2 : ZMod 491213659) ^ (3837606 + 3837606 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 3837606 * (2 : ZMod 491213659) ^ 3837606) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 139601875 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 491213659) ^ 15350426 = 172768880 := by
        calc
          (2 : ZMod 491213659) ^ 15350426 = (2 : ZMod 491213659) ^ (7675213 + 7675213) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 7675213 * (2 : ZMod 491213659) ^ 7675213 := by rw [pow_add]
          _ = 172768880 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 491213659) ^ 30700853 = 264312026 := by
        calc
          (2 : ZMod 491213659) ^ 30700853 = (2 : ZMod 491213659) ^ (15350426 + 15350426 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 15350426 * (2 : ZMod 491213659) ^ 15350426) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 264312026 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 491213659) ^ 61401707 = 264398765 := by
        calc
          (2 : ZMod 491213659) ^ 61401707 = (2 : ZMod 491213659) ^ (30700853 + 30700853 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 30700853 * (2 : ZMod 491213659) ^ 30700853) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 264398765 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 491213659) ^ 122803414 = 24688862 := by
        calc
          (2 : ZMod 491213659) ^ 122803414 = (2 : ZMod 491213659) ^ (61401707 + 61401707) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 61401707 * (2 : ZMod 491213659) ^ 61401707 := by rw [pow_add]
          _ = 24688862 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 491213659) ^ 245606829 = 491213658 := by
        calc
          (2 : ZMod 491213659) ^ 245606829 = (2 : ZMod 491213659) ^ (122803414 + 122803414 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 122803414 * (2 : ZMod 491213659) ^ 122803414) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 491213658 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 491213659) ^ 491213658 = 1 := by
        calc
          (2 : ZMod 491213659) ^ 491213658 = (2 : ZMod 491213659) ^ (245606829 + 245606829) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 245606829 * (2 : ZMod 491213659) ^ 245606829 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (29, 1), (397, 1), (547, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (29, 1), (397, 1), (547, 1)] : List FactorBlock).map factorBlockValue).prod = 491213659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 491213659) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 491213659) ^ 3 = 8 := by
        calc
          (2 : ZMod 491213659) ^ 3 = (2 : ZMod 491213659) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 1 * (2 : ZMod 491213659) ^ 1) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 491213659) ^ 7 = 128 := by
        calc
          (2 : ZMod 491213659) ^ 7 = (2 : ZMod 491213659) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 3 * (2 : ZMod 491213659) ^ 3) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 491213659) ^ 14 = 16384 := by
        calc
          (2 : ZMod 491213659) ^ 14 = (2 : ZMod 491213659) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 7 * (2 : ZMod 491213659) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 491213659) ^ 29 = 45657253 := by
        calc
          (2 : ZMod 491213659) ^ 29 = (2 : ZMod 491213659) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 14 * (2 : ZMod 491213659) ^ 14) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 45657253 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 491213659) ^ 58 = 224620372 := by
        calc
          (2 : ZMod 491213659) ^ 58 = (2 : ZMod 491213659) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 29 * (2 : ZMod 491213659) ^ 29 := by rw [pow_add]
          _ = 224620372 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 491213659) ^ 117 = 42967600 := by
        calc
          (2 : ZMod 491213659) ^ 117 = (2 : ZMod 491213659) ^ (58 + 58 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 58 * (2 : ZMod 491213659) ^ 58) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 42967600 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 491213659) ^ 234 = 392749975 := by
        calc
          (2 : ZMod 491213659) ^ 234 = (2 : ZMod 491213659) ^ (117 + 117) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 117 * (2 : ZMod 491213659) ^ 117 := by rw [pow_add]
          _ = 392749975 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 491213659) ^ 468 = 307613722 := by
        calc
          (2 : ZMod 491213659) ^ 468 = (2 : ZMod 491213659) ^ (234 + 234) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 234 * (2 : ZMod 491213659) ^ 234 := by rw [pow_add]
          _ = 307613722 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 491213659) ^ 936 = 271833926 := by
        calc
          (2 : ZMod 491213659) ^ 936 = (2 : ZMod 491213659) ^ (468 + 468) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 468 * (2 : ZMod 491213659) ^ 468 := by rw [pow_add]
          _ = 271833926 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 491213659) ^ 1873 = 454673491 := by
        calc
          (2 : ZMod 491213659) ^ 1873 = (2 : ZMod 491213659) ^ (936 + 936 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 936 * (2 : ZMod 491213659) ^ 936) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 454673491 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 491213659) ^ 3747 = 132992813 := by
        calc
          (2 : ZMod 491213659) ^ 3747 = (2 : ZMod 491213659) ^ (1873 + 1873 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 1873 * (2 : ZMod 491213659) ^ 1873) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 132992813 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 491213659) ^ 7495 = 177615627 := by
        calc
          (2 : ZMod 491213659) ^ 7495 = (2 : ZMod 491213659) ^ (3747 + 3747 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 3747 * (2 : ZMod 491213659) ^ 3747) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 177615627 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 491213659) ^ 14990 = 345982624 := by
        calc
          (2 : ZMod 491213659) ^ 14990 = (2 : ZMod 491213659) ^ (7495 + 7495) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 7495 * (2 : ZMod 491213659) ^ 7495 := by rw [pow_add]
          _ = 345982624 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 491213659) ^ 29981 = 366592478 := by
        calc
          (2 : ZMod 491213659) ^ 29981 = (2 : ZMod 491213659) ^ (14990 + 14990 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 14990 * (2 : ZMod 491213659) ^ 14990) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 366592478 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 491213659) ^ 59962 = 278966644 := by
        calc
          (2 : ZMod 491213659) ^ 59962 = (2 : ZMod 491213659) ^ (29981 + 29981) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 29981 * (2 : ZMod 491213659) ^ 29981 := by rw [pow_add]
          _ = 278966644 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 491213659) ^ 119925 = 272210003 := by
        calc
          (2 : ZMod 491213659) ^ 119925 = (2 : ZMod 491213659) ^ (59962 + 59962 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 59962 * (2 : ZMod 491213659) ^ 59962) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 272210003 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 491213659) ^ 239850 = 112315133 := by
        calc
          (2 : ZMod 491213659) ^ 239850 = (2 : ZMod 491213659) ^ (119925 + 119925) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 119925 * (2 : ZMod 491213659) ^ 119925 := by rw [pow_add]
          _ = 112315133 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 491213659) ^ 479700 = 101527385 := by
        calc
          (2 : ZMod 491213659) ^ 479700 = (2 : ZMod 491213659) ^ (239850 + 239850) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 239850 * (2 : ZMod 491213659) ^ 239850 := by rw [pow_add]
          _ = 101527385 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 491213659) ^ 959401 = 488429472 := by
        calc
          (2 : ZMod 491213659) ^ 959401 = (2 : ZMod 491213659) ^ (479700 + 479700 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 479700 * (2 : ZMod 491213659) ^ 479700) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 488429472 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 491213659) ^ 1918803 = 200210239 := by
        calc
          (2 : ZMod 491213659) ^ 1918803 = (2 : ZMod 491213659) ^ (959401 + 959401 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 959401 * (2 : ZMod 491213659) ^ 959401) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 200210239 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 491213659) ^ 3837606 = 486518030 := by
        calc
          (2 : ZMod 491213659) ^ 3837606 = (2 : ZMod 491213659) ^ (1918803 + 1918803) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 1918803 * (2 : ZMod 491213659) ^ 1918803 := by rw [pow_add]
          _ = 486518030 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 491213659) ^ 7675213 = 139601875 := by
        calc
          (2 : ZMod 491213659) ^ 7675213 = (2 : ZMod 491213659) ^ (3837606 + 3837606 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 3837606 * (2 : ZMod 491213659) ^ 3837606) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 139601875 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 491213659) ^ 15350426 = 172768880 := by
        calc
          (2 : ZMod 491213659) ^ 15350426 = (2 : ZMod 491213659) ^ (7675213 + 7675213) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 7675213 * (2 : ZMod 491213659) ^ 7675213 := by rw [pow_add]
          _ = 172768880 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 491213659) ^ 30700853 = 264312026 := by
        calc
          (2 : ZMod 491213659) ^ 30700853 = (2 : ZMod 491213659) ^ (15350426 + 15350426 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 15350426 * (2 : ZMod 491213659) ^ 15350426) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 264312026 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 491213659) ^ 61401707 = 264398765 := by
        calc
          (2 : ZMod 491213659) ^ 61401707 = (2 : ZMod 491213659) ^ (30700853 + 30700853 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 30700853 * (2 : ZMod 491213659) ^ 30700853) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 264398765 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 491213659) ^ 122803414 = 24688862 := by
        calc
          (2 : ZMod 491213659) ^ 122803414 = (2 : ZMod 491213659) ^ (61401707 + 61401707) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 61401707 * (2 : ZMod 491213659) ^ 61401707 := by rw [pow_add]
          _ = 24688862 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 491213659) ^ 245606829 = 491213658 := by
        calc
          (2 : ZMod 491213659) ^ 245606829 = (2 : ZMod 491213659) ^ (122803414 + 122803414 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 122803414 * (2 : ZMod 491213659) ^ 122803414) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 491213658 := by rw [factor_0_26]; decide
      change (2 : ZMod 491213659) ^ 245606829 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (2 : ZMod 491213659) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 491213659) ^ 2 = 4 := by
        calc
          (2 : ZMod 491213659) ^ 2 = (2 : ZMod 491213659) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 1 * (2 : ZMod 491213659) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 491213659) ^ 4 = 16 := by
        calc
          (2 : ZMod 491213659) ^ 4 = (2 : ZMod 491213659) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 2 * (2 : ZMod 491213659) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 491213659) ^ 9 = 512 := by
        calc
          (2 : ZMod 491213659) ^ 9 = (2 : ZMod 491213659) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 4 * (2 : ZMod 491213659) ^ 4) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 491213659) ^ 19 = 524288 := by
        calc
          (2 : ZMod 491213659) ^ 19 = (2 : ZMod 491213659) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 9 * (2 : ZMod 491213659) ^ 9) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 491213659) ^ 39 = 87729467 := by
        calc
          (2 : ZMod 491213659) ^ 39 = (2 : ZMod 491213659) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 19 * (2 : ZMod 491213659) ^ 19) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 87729467 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 491213659) ^ 78 = 476263680 := by
        calc
          (2 : ZMod 491213659) ^ 78 = (2 : ZMod 491213659) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 39 * (2 : ZMod 491213659) ^ 39 := by rw [pow_add]
          _ = 476263680 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 491213659) ^ 156 = 148469100 := by
        calc
          (2 : ZMod 491213659) ^ 156 = (2 : ZMod 491213659) ^ (78 + 78) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 78 * (2 : ZMod 491213659) ^ 78 := by rw [pow_add]
          _ = 148469100 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 491213659) ^ 312 = 211864156 := by
        calc
          (2 : ZMod 491213659) ^ 312 = (2 : ZMod 491213659) ^ (156 + 156) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 156 * (2 : ZMod 491213659) ^ 156 := by rw [pow_add]
          _ = 211864156 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 491213659) ^ 624 = 207585664 := by
        calc
          (2 : ZMod 491213659) ^ 624 = (2 : ZMod 491213659) ^ (312 + 312) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 312 * (2 : ZMod 491213659) ^ 312 := by rw [pow_add]
          _ = 207585664 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 491213659) ^ 1249 = 32106257 := by
        calc
          (2 : ZMod 491213659) ^ 1249 = (2 : ZMod 491213659) ^ (624 + 624 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 624 * (2 : ZMod 491213659) ^ 624) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 32106257 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 491213659) ^ 2498 = 366352208 := by
        calc
          (2 : ZMod 491213659) ^ 2498 = (2 : ZMod 491213659) ^ (1249 + 1249) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 1249 * (2 : ZMod 491213659) ^ 1249 := by rw [pow_add]
          _ = 366352208 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 491213659) ^ 4996 = 176935855 := by
        calc
          (2 : ZMod 491213659) ^ 4996 = (2 : ZMod 491213659) ^ (2498 + 2498) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 2498 * (2 : ZMod 491213659) ^ 2498 := by rw [pow_add]
          _ = 176935855 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 491213659) ^ 9993 = 315497740 := by
        calc
          (2 : ZMod 491213659) ^ 9993 = (2 : ZMod 491213659) ^ (4996 + 4996 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 4996 * (2 : ZMod 491213659) ^ 4996) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 315497740 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 491213659) ^ 19987 = 199092641 := by
        calc
          (2 : ZMod 491213659) ^ 19987 = (2 : ZMod 491213659) ^ (9993 + 9993 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 9993 * (2 : ZMod 491213659) ^ 9993) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 199092641 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 491213659) ^ 39975 = 272437492 := by
        calc
          (2 : ZMod 491213659) ^ 39975 = (2 : ZMod 491213659) ^ (19987 + 19987 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 19987 * (2 : ZMod 491213659) ^ 19987) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 272437492 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 491213659) ^ 79950 = 149027323 := by
        calc
          (2 : ZMod 491213659) ^ 79950 = (2 : ZMod 491213659) ^ (39975 + 39975) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 39975 * (2 : ZMod 491213659) ^ 39975 := by rw [pow_add]
          _ = 149027323 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 491213659) ^ 159900 = 43765765 := by
        calc
          (2 : ZMod 491213659) ^ 159900 = (2 : ZMod 491213659) ^ (79950 + 79950) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 79950 * (2 : ZMod 491213659) ^ 79950 := by rw [pow_add]
          _ = 43765765 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 491213659) ^ 319800 = 205635012 := by
        calc
          (2 : ZMod 491213659) ^ 319800 = (2 : ZMod 491213659) ^ (159900 + 159900) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 159900 * (2 : ZMod 491213659) ^ 159900 := by rw [pow_add]
          _ = 205635012 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 491213659) ^ 639601 = 418220742 := by
        calc
          (2 : ZMod 491213659) ^ 639601 = (2 : ZMod 491213659) ^ (319800 + 319800 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 319800 * (2 : ZMod 491213659) ^ 319800) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 418220742 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 491213659) ^ 1279202 = 278560983 := by
        calc
          (2 : ZMod 491213659) ^ 1279202 = (2 : ZMod 491213659) ^ (639601 + 639601) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 639601 * (2 : ZMod 491213659) ^ 639601 := by rw [pow_add]
          _ = 278560983 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 491213659) ^ 2558404 = 215960459 := by
        calc
          (2 : ZMod 491213659) ^ 2558404 = (2 : ZMod 491213659) ^ (1279202 + 1279202) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 1279202 * (2 : ZMod 491213659) ^ 1279202 := by rw [pow_add]
          _ = 215960459 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 491213659) ^ 5116808 = 419978981 := by
        calc
          (2 : ZMod 491213659) ^ 5116808 = (2 : ZMod 491213659) ^ (2558404 + 2558404) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 2558404 * (2 : ZMod 491213659) ^ 2558404 := by rw [pow_add]
          _ = 419978981 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 491213659) ^ 10233617 = 91878807 := by
        calc
          (2 : ZMod 491213659) ^ 10233617 = (2 : ZMod 491213659) ^ (5116808 + 5116808 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 5116808 * (2 : ZMod 491213659) ^ 5116808) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 91878807 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 491213659) ^ 20467235 = 342473666 := by
        calc
          (2 : ZMod 491213659) ^ 20467235 = (2 : ZMod 491213659) ^ (10233617 + 10233617 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 10233617 * (2 : ZMod 491213659) ^ 10233617) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 342473666 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 491213659) ^ 40934471 = 382258938 := by
        calc
          (2 : ZMod 491213659) ^ 40934471 = (2 : ZMod 491213659) ^ (20467235 + 20467235 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 20467235 * (2 : ZMod 491213659) ^ 20467235) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 382258938 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 491213659) ^ 81868943 = 407908762 := by
        calc
          (2 : ZMod 491213659) ^ 81868943 = (2 : ZMod 491213659) ^ (40934471 + 40934471 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 40934471 * (2 : ZMod 491213659) ^ 40934471) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 407908762 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 491213659) ^ 163737886 = 407908761 := by
        calc
          (2 : ZMod 491213659) ^ 163737886 = (2 : ZMod 491213659) ^ (81868943 + 81868943) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 81868943 * (2 : ZMod 491213659) ^ 81868943 := by rw [pow_add]
          _ = 407908761 := by rw [factor_1_26]; decide
      change (2 : ZMod 491213659) ^ 163737886 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (2 : ZMod 491213659) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 491213659) ^ 2 = 4 := by
        calc
          (2 : ZMod 491213659) ^ 2 = (2 : ZMod 491213659) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 1 * (2 : ZMod 491213659) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 491213659) ^ 4 = 16 := by
        calc
          (2 : ZMod 491213659) ^ 4 = (2 : ZMod 491213659) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 2 * (2 : ZMod 491213659) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 491213659) ^ 9 = 512 := by
        calc
          (2 : ZMod 491213659) ^ 9 = (2 : ZMod 491213659) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 4 * (2 : ZMod 491213659) ^ 4) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 491213659) ^ 18 = 262144 := by
        calc
          (2 : ZMod 491213659) ^ 18 = (2 : ZMod 491213659) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 9 * (2 : ZMod 491213659) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 491213659) ^ 36 = 440778135 := by
        calc
          (2 : ZMod 491213659) ^ 36 = (2 : ZMod 491213659) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 18 * (2 : ZMod 491213659) ^ 18 := by rw [pow_add]
          _ = 440778135 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 491213659) ^ 72 = 7441620 := by
        calc
          (2 : ZMod 491213659) ^ 72 = (2 : ZMod 491213659) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 36 * (2 : ZMod 491213659) ^ 36 := by rw [pow_add]
          _ = 7441620 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 491213659) ^ 144 = 245163376 := by
        calc
          (2 : ZMod 491213659) ^ 144 = (2 : ZMod 491213659) ^ (72 + 72) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 72 * (2 : ZMod 491213659) ^ 72 := by rw [pow_add]
          _ = 245163376 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 491213659) ^ 288 = 288346477 := by
        calc
          (2 : ZMod 491213659) ^ 288 = (2 : ZMod 491213659) ^ (144 + 144) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 144 * (2 : ZMod 491213659) ^ 144 := by rw [pow_add]
          _ = 288346477 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 491213659) ^ 576 = 375077053 := by
        calc
          (2 : ZMod 491213659) ^ 576 = (2 : ZMod 491213659) ^ (288 + 288) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 288 * (2 : ZMod 491213659) ^ 288 := by rw [pow_add]
          _ = 375077053 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 491213659) ^ 1153 = 13812096 := by
        calc
          (2 : ZMod 491213659) ^ 1153 = (2 : ZMod 491213659) ^ (576 + 576 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 576 * (2 : ZMod 491213659) ^ 576) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 13812096 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 491213659) ^ 2306 = 364740068 := by
        calc
          (2 : ZMod 491213659) ^ 2306 = (2 : ZMod 491213659) ^ (1153 + 1153) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 1153 * (2 : ZMod 491213659) ^ 1153 := by rw [pow_add]
          _ = 364740068 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 491213659) ^ 4612 = 40646405 := by
        calc
          (2 : ZMod 491213659) ^ 4612 = (2 : ZMod 491213659) ^ (2306 + 2306) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 2306 * (2 : ZMod 491213659) ^ 2306 := by rw [pow_add]
          _ = 40646405 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 491213659) ^ 9225 = 296083957 := by
        calc
          (2 : ZMod 491213659) ^ 9225 = (2 : ZMod 491213659) ^ (4612 + 4612 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 4612 * (2 : ZMod 491213659) ^ 4612) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 296083957 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 491213659) ^ 18450 = 46598242 := by
        calc
          (2 : ZMod 491213659) ^ 18450 = (2 : ZMod 491213659) ^ (9225 + 9225) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 9225 * (2 : ZMod 491213659) ^ 9225 := by rw [pow_add]
          _ = 46598242 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 491213659) ^ 36900 = 423077175 := by
        calc
          (2 : ZMod 491213659) ^ 36900 = (2 : ZMod 491213659) ^ (18450 + 18450) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 18450 * (2 : ZMod 491213659) ^ 18450 := by rw [pow_add]
          _ = 423077175 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 491213659) ^ 73800 = 304540460 := by
        calc
          (2 : ZMod 491213659) ^ 73800 = (2 : ZMod 491213659) ^ (36900 + 36900) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 36900 * (2 : ZMod 491213659) ^ 36900 := by rw [pow_add]
          _ = 304540460 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 491213659) ^ 147600 = 85456840 := by
        calc
          (2 : ZMod 491213659) ^ 147600 = (2 : ZMod 491213659) ^ (73800 + 73800) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 73800 * (2 : ZMod 491213659) ^ 73800 := by rw [pow_add]
          _ = 85456840 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 491213659) ^ 295200 = 490500895 := by
        calc
          (2 : ZMod 491213659) ^ 295200 = (2 : ZMod 491213659) ^ (147600 + 147600) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 147600 * (2 : ZMod 491213659) ^ 147600 := by rw [pow_add]
          _ = 490500895 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 491213659) ^ 590401 = 235192580 := by
        calc
          (2 : ZMod 491213659) ^ 590401 = (2 : ZMod 491213659) ^ (295200 + 295200 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 295200 * (2 : ZMod 491213659) ^ 295200) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 235192580 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 491213659) ^ 1180802 = 178040078 := by
        calc
          (2 : ZMod 491213659) ^ 1180802 = (2 : ZMod 491213659) ^ (590401 + 590401) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 590401 * (2 : ZMod 491213659) ^ 590401 := by rw [pow_add]
          _ = 178040078 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 491213659) ^ 2361604 = 457582676 := by
        calc
          (2 : ZMod 491213659) ^ 2361604 = (2 : ZMod 491213659) ^ (1180802 + 1180802) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 1180802 * (2 : ZMod 491213659) ^ 1180802 := by rw [pow_add]
          _ = 457582676 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 491213659) ^ 4723208 = 480656816 := by
        calc
          (2 : ZMod 491213659) ^ 4723208 = (2 : ZMod 491213659) ^ (2361604 + 2361604) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 2361604 * (2 : ZMod 491213659) ^ 2361604 := by rw [pow_add]
          _ = 480656816 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 491213659) ^ 9446416 = 379172729 := by
        calc
          (2 : ZMod 491213659) ^ 9446416 = (2 : ZMod 491213659) ^ (4723208 + 4723208) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 4723208 * (2 : ZMod 491213659) ^ 4723208 := by rw [pow_add]
          _ = 379172729 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 491213659) ^ 18892833 = 206848194 := by
        calc
          (2 : ZMod 491213659) ^ 18892833 = (2 : ZMod 491213659) ^ (9446416 + 9446416 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 9446416 * (2 : ZMod 491213659) ^ 9446416) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 206848194 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 491213659) ^ 37785666 = 371816839 := by
        calc
          (2 : ZMod 491213659) ^ 37785666 = (2 : ZMod 491213659) ^ (18892833 + 18892833) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 18892833 * (2 : ZMod 491213659) ^ 18892833 := by rw [pow_add]
          _ = 371816839 := by rw [factor_2_24]; decide
      change (2 : ZMod 491213659) ^ 37785666 ≠ 1
      rw [factor_2_25]
      decide
    ·
      have factor_3_0 : (2 : ZMod 491213659) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 491213659) ^ 2 = 4 := by
        calc
          (2 : ZMod 491213659) ^ 2 = (2 : ZMod 491213659) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 1 * (2 : ZMod 491213659) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 491213659) ^ 4 = 16 := by
        calc
          (2 : ZMod 491213659) ^ 4 = (2 : ZMod 491213659) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 2 * (2 : ZMod 491213659) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 491213659) ^ 8 = 256 := by
        calc
          (2 : ZMod 491213659) ^ 8 = (2 : ZMod 491213659) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 4 * (2 : ZMod 491213659) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 491213659) ^ 16 = 65536 := by
        calc
          (2 : ZMod 491213659) ^ 16 = (2 : ZMod 491213659) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 8 * (2 : ZMod 491213659) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 491213659) ^ 32 = 365258024 := by
        calc
          (2 : ZMod 491213659) ^ 32 = (2 : ZMod 491213659) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 16 * (2 : ZMod 491213659) ^ 16 := by rw [pow_add]
          _ = 365258024 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 491213659) ^ 64 = 130507697 := by
        calc
          (2 : ZMod 491213659) ^ 64 = (2 : ZMod 491213659) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 32 * (2 : ZMod 491213659) ^ 32 := by rw [pow_add]
          _ = 130507697 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 491213659) ^ 129 = 140799678 := by
        calc
          (2 : ZMod 491213659) ^ 129 = (2 : ZMod 491213659) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 64 * (2 : ZMod 491213659) ^ 64) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 140799678 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 491213659) ^ 258 = 128456666 := by
        calc
          (2 : ZMod 491213659) ^ 258 = (2 : ZMod 491213659) ^ (129 + 129) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 129 * (2 : ZMod 491213659) ^ 129 := by rw [pow_add]
          _ = 128456666 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 491213659) ^ 516 = 60118037 := by
        calc
          (2 : ZMod 491213659) ^ 516 = (2 : ZMod 491213659) ^ (258 + 258) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 258 * (2 : ZMod 491213659) ^ 258 := by rw [pow_add]
          _ = 60118037 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 491213659) ^ 1033 = 389184038 := by
        calc
          (2 : ZMod 491213659) ^ 1033 = (2 : ZMod 491213659) ^ (516 + 516 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 516 * (2 : ZMod 491213659) ^ 516) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 389184038 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 491213659) ^ 2067 = 115801554 := by
        calc
          (2 : ZMod 491213659) ^ 2067 = (2 : ZMod 491213659) ^ (1033 + 1033 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 1033 * (2 : ZMod 491213659) ^ 1033) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 115801554 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 491213659) ^ 4135 = 274033010 := by
        calc
          (2 : ZMod 491213659) ^ 4135 = (2 : ZMod 491213659) ^ (2067 + 2067 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 2067 * (2 : ZMod 491213659) ^ 2067) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 274033010 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 491213659) ^ 8270 = 409139677 := by
        calc
          (2 : ZMod 491213659) ^ 8270 = (2 : ZMod 491213659) ^ (4135 + 4135) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 4135 * (2 : ZMod 491213659) ^ 4135 := by rw [pow_add]
          _ = 409139677 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 491213659) ^ 16541 = 220758899 := by
        calc
          (2 : ZMod 491213659) ^ 16541 = (2 : ZMod 491213659) ^ (8270 + 8270 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 8270 * (2 : ZMod 491213659) ^ 8270) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 220758899 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 491213659) ^ 33082 = 62170352 := by
        calc
          (2 : ZMod 491213659) ^ 33082 = (2 : ZMod 491213659) ^ (16541 + 16541) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 16541 * (2 : ZMod 491213659) ^ 16541 := by rw [pow_add]
          _ = 62170352 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 491213659) ^ 66165 = 337021322 := by
        calc
          (2 : ZMod 491213659) ^ 66165 = (2 : ZMod 491213659) ^ (33082 + 33082 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 33082 * (2 : ZMod 491213659) ^ 33082) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 337021322 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 491213659) ^ 132331 = 50852859 := by
        calc
          (2 : ZMod 491213659) ^ 132331 = (2 : ZMod 491213659) ^ (66165 + 66165 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 66165 * (2 : ZMod 491213659) ^ 66165) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 50852859 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 491213659) ^ 264662 = 294549339 := by
        calc
          (2 : ZMod 491213659) ^ 264662 = (2 : ZMod 491213659) ^ (132331 + 132331) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 132331 * (2 : ZMod 491213659) ^ 132331 := by rw [pow_add]
          _ = 294549339 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 491213659) ^ 529325 = 180393611 := by
        calc
          (2 : ZMod 491213659) ^ 529325 = (2 : ZMod 491213659) ^ (264662 + 264662 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 264662 * (2 : ZMod 491213659) ^ 264662) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 180393611 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 491213659) ^ 1058650 = 195672263 := by
        calc
          (2 : ZMod 491213659) ^ 1058650 = (2 : ZMod 491213659) ^ (529325 + 529325) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 529325 * (2 : ZMod 491213659) ^ 529325 := by rw [pow_add]
          _ = 195672263 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 491213659) ^ 2117300 = 101982280 := by
        calc
          (2 : ZMod 491213659) ^ 2117300 = (2 : ZMod 491213659) ^ (1058650 + 1058650) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 1058650 * (2 : ZMod 491213659) ^ 1058650 := by rw [pow_add]
          _ = 101982280 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 491213659) ^ 4234600 = 173458794 := by
        calc
          (2 : ZMod 491213659) ^ 4234600 = (2 : ZMod 491213659) ^ (2117300 + 2117300) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 2117300 * (2 : ZMod 491213659) ^ 2117300 := by rw [pow_add]
          _ = 173458794 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 491213659) ^ 8469201 = 147075058 := by
        calc
          (2 : ZMod 491213659) ^ 8469201 = (2 : ZMod 491213659) ^ (4234600 + 4234600 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 4234600 * (2 : ZMod 491213659) ^ 4234600) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 147075058 := by rw [factor_3_22]; decide
      have factor_3_24 : (2 : ZMod 491213659) ^ 16938402 = 278320839 := by
        calc
          (2 : ZMod 491213659) ^ 16938402 = (2 : ZMod 491213659) ^ (8469201 + 8469201) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 8469201 * (2 : ZMod 491213659) ^ 8469201 := by rw [pow_add]
          _ = 278320839 := by rw [factor_3_23]; decide
      change (2 : ZMod 491213659) ^ 16938402 ≠ 1
      rw [factor_3_24]
      decide
    ·
      have factor_4_0 : (2 : ZMod 491213659) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 491213659) ^ 2 = 4 := by
        calc
          (2 : ZMod 491213659) ^ 2 = (2 : ZMod 491213659) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 1 * (2 : ZMod 491213659) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 491213659) ^ 4 = 16 := by
        calc
          (2 : ZMod 491213659) ^ 4 = (2 : ZMod 491213659) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 2 * (2 : ZMod 491213659) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 491213659) ^ 9 = 512 := by
        calc
          (2 : ZMod 491213659) ^ 9 = (2 : ZMod 491213659) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 4 * (2 : ZMod 491213659) ^ 4) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 491213659) ^ 18 = 262144 := by
        calc
          (2 : ZMod 491213659) ^ 18 = (2 : ZMod 491213659) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 9 * (2 : ZMod 491213659) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 491213659) ^ 37 = 390342611 := by
        calc
          (2 : ZMod 491213659) ^ 37 = (2 : ZMod 491213659) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 18 * (2 : ZMod 491213659) ^ 18) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 390342611 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 491213659) ^ 75 = 59532960 := by
        calc
          (2 : ZMod 491213659) ^ 75 = (2 : ZMod 491213659) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 37 * (2 : ZMod 491213659) ^ 37) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 59532960 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 491213659) ^ 151 = 434451611 := by
        calc
          (2 : ZMod 491213659) ^ 151 = (2 : ZMod 491213659) ^ (75 + 75 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 75 * (2 : ZMod 491213659) ^ 75) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 434451611 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 491213659) ^ 302 = 266920565 := by
        calc
          (2 : ZMod 491213659) ^ 302 = (2 : ZMod 491213659) ^ (151 + 151) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 151 * (2 : ZMod 491213659) ^ 151 := by rw [pow_add]
          _ = 266920565 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 491213659) ^ 604 = 69496857 := by
        calc
          (2 : ZMod 491213659) ^ 604 = (2 : ZMod 491213659) ^ (302 + 302) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 302 * (2 : ZMod 491213659) ^ 302 := by rw [pow_add]
          _ = 69496857 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 491213659) ^ 1208 = 22417577 := by
        calc
          (2 : ZMod 491213659) ^ 1208 = (2 : ZMod 491213659) ^ (604 + 604) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 604 * (2 : ZMod 491213659) ^ 604 := by rw [pow_add]
          _ = 22417577 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 491213659) ^ 2416 = 326796822 := by
        calc
          (2 : ZMod 491213659) ^ 2416 = (2 : ZMod 491213659) ^ (1208 + 1208) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 1208 * (2 : ZMod 491213659) ^ 1208 := by rw [pow_add]
          _ = 326796822 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 491213659) ^ 4833 = 158294773 := by
        calc
          (2 : ZMod 491213659) ^ 4833 = (2 : ZMod 491213659) ^ (2416 + 2416 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 2416 * (2 : ZMod 491213659) ^ 2416) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 158294773 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 491213659) ^ 9666 = 40075517 := by
        calc
          (2 : ZMod 491213659) ^ 9666 = (2 : ZMod 491213659) ^ (4833 + 4833) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 4833 * (2 : ZMod 491213659) ^ 4833 := by rw [pow_add]
          _ = 40075517 := by rw [factor_4_12]; decide
      have factor_4_14 : (2 : ZMod 491213659) ^ 19333 = 361708655 := by
        calc
          (2 : ZMod 491213659) ^ 19333 = (2 : ZMod 491213659) ^ (9666 + 9666 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 9666 * (2 : ZMod 491213659) ^ 9666) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 361708655 := by rw [factor_4_13]; decide
      have factor_4_15 : (2 : ZMod 491213659) ^ 38666 = 278351273 := by
        calc
          (2 : ZMod 491213659) ^ 38666 = (2 : ZMod 491213659) ^ (19333 + 19333) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 19333 * (2 : ZMod 491213659) ^ 19333 := by rw [pow_add]
          _ = 278351273 := by rw [factor_4_14]; decide
      have factor_4_16 : (2 : ZMod 491213659) ^ 77332 = 123891221 := by
        calc
          (2 : ZMod 491213659) ^ 77332 = (2 : ZMod 491213659) ^ (38666 + 38666) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 38666 * (2 : ZMod 491213659) ^ 38666 := by rw [pow_add]
          _ = 123891221 := by rw [factor_4_15]; decide
      have factor_4_17 : (2 : ZMod 491213659) ^ 154664 = 387844106 := by
        calc
          (2 : ZMod 491213659) ^ 154664 = (2 : ZMod 491213659) ^ (77332 + 77332) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 77332 * (2 : ZMod 491213659) ^ 77332 := by rw [pow_add]
          _ = 387844106 := by rw [factor_4_16]; decide
      have factor_4_18 : (2 : ZMod 491213659) ^ 309328 = 356556812 := by
        calc
          (2 : ZMod 491213659) ^ 309328 = (2 : ZMod 491213659) ^ (154664 + 154664) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 154664 * (2 : ZMod 491213659) ^ 154664 := by rw [pow_add]
          _ = 356556812 := by rw [factor_4_17]; decide
      have factor_4_19 : (2 : ZMod 491213659) ^ 618657 = 403742405 := by
        calc
          (2 : ZMod 491213659) ^ 618657 = (2 : ZMod 491213659) ^ (309328 + 309328 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 309328 * (2 : ZMod 491213659) ^ 309328) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 403742405 := by rw [factor_4_18]; decide
      have factor_4_20 : (2 : ZMod 491213659) ^ 1237314 = 185631371 := by
        calc
          (2 : ZMod 491213659) ^ 1237314 = (2 : ZMod 491213659) ^ (618657 + 618657) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 618657 * (2 : ZMod 491213659) ^ 618657 := by rw [pow_add]
          _ = 185631371 := by rw [factor_4_19]; decide
      change (2 : ZMod 491213659) ^ 1237314 ≠ 1
      rw [factor_4_20]
      decide
    ·
      have factor_5_0 : (2 : ZMod 491213659) ^ 1 = 2 := by norm_num
      have factor_5_1 : (2 : ZMod 491213659) ^ 3 = 8 := by
        calc
          (2 : ZMod 491213659) ^ 3 = (2 : ZMod 491213659) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 1 * (2 : ZMod 491213659) ^ 1) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_5_0]; decide
      have factor_5_2 : (2 : ZMod 491213659) ^ 6 = 64 := by
        calc
          (2 : ZMod 491213659) ^ 6 = (2 : ZMod 491213659) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 3 * (2 : ZMod 491213659) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_5_1]; decide
      have factor_5_3 : (2 : ZMod 491213659) ^ 13 = 8192 := by
        calc
          (2 : ZMod 491213659) ^ 13 = (2 : ZMod 491213659) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 6 * (2 : ZMod 491213659) ^ 6) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_5_2]; decide
      have factor_5_4 : (2 : ZMod 491213659) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 491213659) ^ 27 = (2 : ZMod 491213659) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 13 * (2 : ZMod 491213659) ^ 13) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [factor_5_3]; decide
      have factor_5_5 : (2 : ZMod 491213659) ^ 54 = 136842188 := by
        calc
          (2 : ZMod 491213659) ^ 54 = (2 : ZMod 491213659) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 27 * (2 : ZMod 491213659) ^ 27 := by rw [pow_add]
          _ = 136842188 := by rw [factor_5_4]; decide
      have factor_5_6 : (2 : ZMod 491213659) ^ 109 = 215073818 := by
        calc
          (2 : ZMod 491213659) ^ 109 = (2 : ZMod 491213659) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 54 * (2 : ZMod 491213659) ^ 54) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 215073818 := by rw [factor_5_5]; decide
      have factor_5_7 : (2 : ZMod 491213659) ^ 219 = 178625595 := by
        calc
          (2 : ZMod 491213659) ^ 219 = (2 : ZMod 491213659) ^ (109 + 109 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 109 * (2 : ZMod 491213659) ^ 109) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 178625595 := by rw [factor_5_6]; decide
      have factor_5_8 : (2 : ZMod 491213659) ^ 438 = 188667016 := by
        calc
          (2 : ZMod 491213659) ^ 438 = (2 : ZMod 491213659) ^ (219 + 219) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 219 * (2 : ZMod 491213659) ^ 219 := by rw [pow_add]
          _ = 188667016 := by rw [factor_5_7]; decide
      have factor_5_9 : (2 : ZMod 491213659) ^ 876 = 198343926 := by
        calc
          (2 : ZMod 491213659) ^ 876 = (2 : ZMod 491213659) ^ (438 + 438) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 438 * (2 : ZMod 491213659) ^ 438 := by rw [pow_add]
          _ = 198343926 := by rw [factor_5_8]; decide
      have factor_5_10 : (2 : ZMod 491213659) ^ 1753 = 180971745 := by
        calc
          (2 : ZMod 491213659) ^ 1753 = (2 : ZMod 491213659) ^ (876 + 876 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 876 * (2 : ZMod 491213659) ^ 876) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 180971745 := by rw [factor_5_9]; decide
      have factor_5_11 : (2 : ZMod 491213659) ^ 3507 = 408604672 := by
        calc
          (2 : ZMod 491213659) ^ 3507 = (2 : ZMod 491213659) ^ (1753 + 1753 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 1753 * (2 : ZMod 491213659) ^ 1753) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 408604672 := by rw [factor_5_10]; decide
      have factor_5_12 : (2 : ZMod 491213659) ^ 7015 = 59739178 := by
        calc
          (2 : ZMod 491213659) ^ 7015 = (2 : ZMod 491213659) ^ (3507 + 3507 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 3507 * (2 : ZMod 491213659) ^ 3507) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 59739178 := by rw [factor_5_11]; decide
      have factor_5_13 : (2 : ZMod 491213659) ^ 14031 = 457292883 := by
        calc
          (2 : ZMod 491213659) ^ 14031 = (2 : ZMod 491213659) ^ (7015 + 7015 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 7015 * (2 : ZMod 491213659) ^ 7015) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 457292883 := by rw [factor_5_12]; decide
      have factor_5_14 : (2 : ZMod 491213659) ^ 28062 = 169600576 := by
        calc
          (2 : ZMod 491213659) ^ 28062 = (2 : ZMod 491213659) ^ (14031 + 14031) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 14031 * (2 : ZMod 491213659) ^ 14031 := by rw [pow_add]
          _ = 169600576 := by rw [factor_5_13]; decide
      have factor_5_15 : (2 : ZMod 491213659) ^ 56125 = 74277366 := by
        calc
          (2 : ZMod 491213659) ^ 56125 = (2 : ZMod 491213659) ^ (28062 + 28062 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 28062 * (2 : ZMod 491213659) ^ 28062) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 74277366 := by rw [factor_5_14]; decide
      have factor_5_16 : (2 : ZMod 491213659) ^ 112251 = 447905139 := by
        calc
          (2 : ZMod 491213659) ^ 112251 = (2 : ZMod 491213659) ^ (56125 + 56125 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 56125 * (2 : ZMod 491213659) ^ 56125) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 447905139 := by rw [factor_5_15]; decide
      have factor_5_17 : (2 : ZMod 491213659) ^ 224503 = 38572569 := by
        calc
          (2 : ZMod 491213659) ^ 224503 = (2 : ZMod 491213659) ^ (112251 + 112251 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 112251 * (2 : ZMod 491213659) ^ 112251) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 38572569 := by rw [factor_5_16]; decide
      have factor_5_18 : (2 : ZMod 491213659) ^ 449007 = 265901506 := by
        calc
          (2 : ZMod 491213659) ^ 449007 = (2 : ZMod 491213659) ^ (224503 + 224503 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = ((2 : ZMod 491213659) ^ 224503 * (2 : ZMod 491213659) ^ 224503) * (2 : ZMod 491213659) := by rw [pow_succ, pow_add]
          _ = 265901506 := by rw [factor_5_17]; decide
      have factor_5_19 : (2 : ZMod 491213659) ^ 898014 = 205817429 := by
        calc
          (2 : ZMod 491213659) ^ 898014 = (2 : ZMod 491213659) ^ (449007 + 449007) :=
            congrArg (fun n : ℕ => (2 : ZMod 491213659) ^ n) (by norm_num)
          _ = (2 : ZMod 491213659) ^ 449007 * (2 : ZMod 491213659) ^ 449007 := by rw [pow_add]
          _ = 205817429 := by rw [factor_5_18]; decide
      change (2 : ZMod 491213659) ^ 898014 ≠ 1
      rw [factor_5_19]
      decide

#print axioms prime_lucas_491213659

end TotientTailPeriodKiller
end Erdos249257
