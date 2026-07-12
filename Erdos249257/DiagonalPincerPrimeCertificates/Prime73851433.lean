import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=23 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_73851433 : Nat.Prime 73851433 := by
  apply lucas_primality 73851433 (5 : ZMod 73851433)
  ·
      have fermat_0 : (5 : ZMod 73851433) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 73851433) ^ 2 = 25 := by
        calc
          (5 : ZMod 73851433) ^ 2 = (5 : ZMod 73851433) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 1 * (5 : ZMod 73851433) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 73851433) ^ 4 = 625 := by
        calc
          (5 : ZMod 73851433) ^ 4 = (5 : ZMod 73851433) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 2 * (5 : ZMod 73851433) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 73851433) ^ 8 = 390625 := by
        calc
          (5 : ZMod 73851433) ^ 8 = (5 : ZMod 73851433) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 4 * (5 : ZMod 73851433) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 73851433) ^ 17 = 54150235 := by
        calc
          (5 : ZMod 73851433) ^ 17 = (5 : ZMod 73851433) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 8 * (5 : ZMod 73851433) ^ 8) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 54150235 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 73851433) ^ 35 = 37052368 := by
        calc
          (5 : ZMod 73851433) ^ 35 = (5 : ZMod 73851433) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 17 * (5 : ZMod 73851433) ^ 17) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 37052368 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 73851433) ^ 70 = 70230066 := by
        calc
          (5 : ZMod 73851433) ^ 70 = (5 : ZMod 73851433) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 35 * (5 : ZMod 73851433) ^ 35 := by rw [pow_add]
          _ = 70230066 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 73851433) ^ 140 = 56882281 := by
        calc
          (5 : ZMod 73851433) ^ 140 = (5 : ZMod 73851433) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 70 * (5 : ZMod 73851433) ^ 70 := by rw [pow_add]
          _ = 56882281 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 73851433) ^ 281 = 29738908 := by
        calc
          (5 : ZMod 73851433) ^ 281 = (5 : ZMod 73851433) ^ (140 + 140 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 140 * (5 : ZMod 73851433) ^ 140) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 29738908 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 73851433) ^ 563 = 61409236 := by
        calc
          (5 : ZMod 73851433) ^ 563 = (5 : ZMod 73851433) ^ (281 + 281 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 281 * (5 : ZMod 73851433) ^ 281) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 61409236 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 73851433) ^ 1126 = 6115013 := by
        calc
          (5 : ZMod 73851433) ^ 1126 = (5 : ZMod 73851433) ^ (563 + 563) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 563 * (5 : ZMod 73851433) ^ 563 := by rw [pow_add]
          _ = 6115013 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 73851433) ^ 2253 = 53379199 := by
        calc
          (5 : ZMod 73851433) ^ 2253 = (5 : ZMod 73851433) ^ (1126 + 1126 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 1126 * (5 : ZMod 73851433) ^ 1126) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 53379199 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 73851433) ^ 4507 = 14497137 := by
        calc
          (5 : ZMod 73851433) ^ 4507 = (5 : ZMod 73851433) ^ (2253 + 2253 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 2253 * (5 : ZMod 73851433) ^ 2253) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 14497137 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 73851433) ^ 9015 = 59472391 := by
        calc
          (5 : ZMod 73851433) ^ 9015 = (5 : ZMod 73851433) ^ (4507 + 4507 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 4507 * (5 : ZMod 73851433) ^ 4507) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 59472391 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 73851433) ^ 18030 = 13765108 := by
        calc
          (5 : ZMod 73851433) ^ 18030 = (5 : ZMod 73851433) ^ (9015 + 9015) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 9015 * (5 : ZMod 73851433) ^ 9015 := by rw [pow_add]
          _ = 13765108 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 73851433) ^ 36060 = 13700853 := by
        calc
          (5 : ZMod 73851433) ^ 36060 = (5 : ZMod 73851433) ^ (18030 + 18030) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 18030 * (5 : ZMod 73851433) ^ 18030 := by rw [pow_add]
          _ = 13700853 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 73851433) ^ 72120 = 16071199 := by
        calc
          (5 : ZMod 73851433) ^ 72120 = (5 : ZMod 73851433) ^ (36060 + 36060) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 36060 * (5 : ZMod 73851433) ^ 36060 := by rw [pow_add]
          _ = 16071199 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 73851433) ^ 144241 = 71561235 := by
        calc
          (5 : ZMod 73851433) ^ 144241 = (5 : ZMod 73851433) ^ (72120 + 72120 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 72120 * (5 : ZMod 73851433) ^ 72120) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 71561235 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 73851433) ^ 288482 = 4256111 := by
        calc
          (5 : ZMod 73851433) ^ 288482 = (5 : ZMod 73851433) ^ (144241 + 144241) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 144241 * (5 : ZMod 73851433) ^ 144241 := by rw [pow_add]
          _ = 4256111 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 73851433) ^ 576964 = 53655215 := by
        calc
          (5 : ZMod 73851433) ^ 576964 = (5 : ZMod 73851433) ^ (288482 + 288482) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 288482 * (5 : ZMod 73851433) ^ 288482 := by rw [pow_add]
          _ = 53655215 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 73851433) ^ 1153928 = 70484183 := by
        calc
          (5 : ZMod 73851433) ^ 1153928 = (5 : ZMod 73851433) ^ (576964 + 576964) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 576964 * (5 : ZMod 73851433) ^ 576964 := by rw [pow_add]
          _ = 70484183 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 73851433) ^ 2307857 = 31824349 := by
        calc
          (5 : ZMod 73851433) ^ 2307857 = (5 : ZMod 73851433) ^ (1153928 + 1153928 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 1153928 * (5 : ZMod 73851433) ^ 1153928) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 31824349 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 73851433) ^ 4615714 = 16243792 := by
        calc
          (5 : ZMod 73851433) ^ 4615714 = (5 : ZMod 73851433) ^ (2307857 + 2307857) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 2307857 * (5 : ZMod 73851433) ^ 2307857 := by rw [pow_add]
          _ = 16243792 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 73851433) ^ 9231429 = 33560152 := by
        calc
          (5 : ZMod 73851433) ^ 9231429 = (5 : ZMod 73851433) ^ (4615714 + 4615714 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 4615714 * (5 : ZMod 73851433) ^ 4615714) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 33560152 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 73851433) ^ 18462858 = 42404427 := by
        calc
          (5 : ZMod 73851433) ^ 18462858 = (5 : ZMod 73851433) ^ (9231429 + 9231429) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 9231429 * (5 : ZMod 73851433) ^ 9231429 := by rw [pow_add]
          _ = 42404427 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 73851433) ^ 36925716 = 73851432 := by
        calc
          (5 : ZMod 73851433) ^ 36925716 = (5 : ZMod 73851433) ^ (18462858 + 18462858) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 18462858 * (5 : ZMod 73851433) ^ 18462858 := by rw [pow_add]
          _ = 73851432 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 73851433) ^ 73851432 = 1 := by
        calc
          (5 : ZMod 73851433) ^ 73851432 = (5 : ZMod 73851433) ^ (36925716 + 36925716) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 36925716 * (5 : ZMod 73851433) ^ 36925716 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (3077143, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (3077143, 1)] : List FactorBlock).map factorBlockValue).prod = 73851433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 73851433) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 73851433) ^ 2 = 25 := by
        calc
          (5 : ZMod 73851433) ^ 2 = (5 : ZMod 73851433) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 1 * (5 : ZMod 73851433) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 73851433) ^ 4 = 625 := by
        calc
          (5 : ZMod 73851433) ^ 4 = (5 : ZMod 73851433) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 2 * (5 : ZMod 73851433) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 73851433) ^ 8 = 390625 := by
        calc
          (5 : ZMod 73851433) ^ 8 = (5 : ZMod 73851433) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 4 * (5 : ZMod 73851433) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 73851433) ^ 17 = 54150235 := by
        calc
          (5 : ZMod 73851433) ^ 17 = (5 : ZMod 73851433) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 8 * (5 : ZMod 73851433) ^ 8) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 54150235 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 73851433) ^ 35 = 37052368 := by
        calc
          (5 : ZMod 73851433) ^ 35 = (5 : ZMod 73851433) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 17 * (5 : ZMod 73851433) ^ 17) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 37052368 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 73851433) ^ 70 = 70230066 := by
        calc
          (5 : ZMod 73851433) ^ 70 = (5 : ZMod 73851433) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 35 * (5 : ZMod 73851433) ^ 35 := by rw [pow_add]
          _ = 70230066 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 73851433) ^ 140 = 56882281 := by
        calc
          (5 : ZMod 73851433) ^ 140 = (5 : ZMod 73851433) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 70 * (5 : ZMod 73851433) ^ 70 := by rw [pow_add]
          _ = 56882281 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 73851433) ^ 281 = 29738908 := by
        calc
          (5 : ZMod 73851433) ^ 281 = (5 : ZMod 73851433) ^ (140 + 140 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 140 * (5 : ZMod 73851433) ^ 140) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 29738908 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 73851433) ^ 563 = 61409236 := by
        calc
          (5 : ZMod 73851433) ^ 563 = (5 : ZMod 73851433) ^ (281 + 281 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 281 * (5 : ZMod 73851433) ^ 281) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 61409236 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 73851433) ^ 1126 = 6115013 := by
        calc
          (5 : ZMod 73851433) ^ 1126 = (5 : ZMod 73851433) ^ (563 + 563) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 563 * (5 : ZMod 73851433) ^ 563 := by rw [pow_add]
          _ = 6115013 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 73851433) ^ 2253 = 53379199 := by
        calc
          (5 : ZMod 73851433) ^ 2253 = (5 : ZMod 73851433) ^ (1126 + 1126 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 1126 * (5 : ZMod 73851433) ^ 1126) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 53379199 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 73851433) ^ 4507 = 14497137 := by
        calc
          (5 : ZMod 73851433) ^ 4507 = (5 : ZMod 73851433) ^ (2253 + 2253 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 2253 * (5 : ZMod 73851433) ^ 2253) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 14497137 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 73851433) ^ 9015 = 59472391 := by
        calc
          (5 : ZMod 73851433) ^ 9015 = (5 : ZMod 73851433) ^ (4507 + 4507 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 4507 * (5 : ZMod 73851433) ^ 4507) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 59472391 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 73851433) ^ 18030 = 13765108 := by
        calc
          (5 : ZMod 73851433) ^ 18030 = (5 : ZMod 73851433) ^ (9015 + 9015) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 9015 * (5 : ZMod 73851433) ^ 9015 := by rw [pow_add]
          _ = 13765108 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 73851433) ^ 36060 = 13700853 := by
        calc
          (5 : ZMod 73851433) ^ 36060 = (5 : ZMod 73851433) ^ (18030 + 18030) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 18030 * (5 : ZMod 73851433) ^ 18030 := by rw [pow_add]
          _ = 13700853 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 73851433) ^ 72120 = 16071199 := by
        calc
          (5 : ZMod 73851433) ^ 72120 = (5 : ZMod 73851433) ^ (36060 + 36060) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 36060 * (5 : ZMod 73851433) ^ 36060 := by rw [pow_add]
          _ = 16071199 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 73851433) ^ 144241 = 71561235 := by
        calc
          (5 : ZMod 73851433) ^ 144241 = (5 : ZMod 73851433) ^ (72120 + 72120 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 72120 * (5 : ZMod 73851433) ^ 72120) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 71561235 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 73851433) ^ 288482 = 4256111 := by
        calc
          (5 : ZMod 73851433) ^ 288482 = (5 : ZMod 73851433) ^ (144241 + 144241) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 144241 * (5 : ZMod 73851433) ^ 144241 := by rw [pow_add]
          _ = 4256111 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 73851433) ^ 576964 = 53655215 := by
        calc
          (5 : ZMod 73851433) ^ 576964 = (5 : ZMod 73851433) ^ (288482 + 288482) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 288482 * (5 : ZMod 73851433) ^ 288482 := by rw [pow_add]
          _ = 53655215 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 73851433) ^ 1153928 = 70484183 := by
        calc
          (5 : ZMod 73851433) ^ 1153928 = (5 : ZMod 73851433) ^ (576964 + 576964) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 576964 * (5 : ZMod 73851433) ^ 576964 := by rw [pow_add]
          _ = 70484183 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 73851433) ^ 2307857 = 31824349 := by
        calc
          (5 : ZMod 73851433) ^ 2307857 = (5 : ZMod 73851433) ^ (1153928 + 1153928 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 1153928 * (5 : ZMod 73851433) ^ 1153928) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 31824349 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 73851433) ^ 4615714 = 16243792 := by
        calc
          (5 : ZMod 73851433) ^ 4615714 = (5 : ZMod 73851433) ^ (2307857 + 2307857) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 2307857 * (5 : ZMod 73851433) ^ 2307857 := by rw [pow_add]
          _ = 16243792 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 73851433) ^ 9231429 = 33560152 := by
        calc
          (5 : ZMod 73851433) ^ 9231429 = (5 : ZMod 73851433) ^ (4615714 + 4615714 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 4615714 * (5 : ZMod 73851433) ^ 4615714) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 33560152 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 73851433) ^ 18462858 = 42404427 := by
        calc
          (5 : ZMod 73851433) ^ 18462858 = (5 : ZMod 73851433) ^ (9231429 + 9231429) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 9231429 * (5 : ZMod 73851433) ^ 9231429 := by rw [pow_add]
          _ = 42404427 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 73851433) ^ 36925716 = 73851432 := by
        calc
          (5 : ZMod 73851433) ^ 36925716 = (5 : ZMod 73851433) ^ (18462858 + 18462858) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 18462858 * (5 : ZMod 73851433) ^ 18462858 := by rw [pow_add]
          _ = 73851432 := by rw [factor_0_24]; decide
      change (5 : ZMod 73851433) ^ 36925716 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (5 : ZMod 73851433) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 73851433) ^ 2 = 25 := by
        calc
          (5 : ZMod 73851433) ^ 2 = (5 : ZMod 73851433) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 1 * (5 : ZMod 73851433) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 73851433) ^ 5 = 3125 := by
        calc
          (5 : ZMod 73851433) ^ 5 = (5 : ZMod 73851433) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 2 * (5 : ZMod 73851433) ^ 2) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 73851433) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 73851433) ^ 11 = (5 : ZMod 73851433) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 5 * (5 : ZMod 73851433) ^ 5) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 73851433) ^ 23 = 55405427 := by
        calc
          (5 : ZMod 73851433) ^ 23 = (5 : ZMod 73851433) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 11 * (5 : ZMod 73851433) ^ 11) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 55405427 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 73851433) ^ 46 = 20902600 := by
        calc
          (5 : ZMod 73851433) ^ 46 = (5 : ZMod 73851433) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 23 * (5 : ZMod 73851433) ^ 23 := by rw [pow_add]
          _ = 20902600 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 73851433) ^ 93 = 28490207 := by
        calc
          (5 : ZMod 73851433) ^ 93 = (5 : ZMod 73851433) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 46 * (5 : ZMod 73851433) ^ 46) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 28490207 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 73851433) ^ 187 = 57293437 := by
        calc
          (5 : ZMod 73851433) ^ 187 = (5 : ZMod 73851433) ^ (93 + 93 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 93 * (5 : ZMod 73851433) ^ 93) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 57293437 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 73851433) ^ 375 = 24070873 := by
        calc
          (5 : ZMod 73851433) ^ 375 = (5 : ZMod 73851433) ^ (187 + 187 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 187 * (5 : ZMod 73851433) ^ 187) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 24070873 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 73851433) ^ 751 = 318636 := by
        calc
          (5 : ZMod 73851433) ^ 751 = (5 : ZMod 73851433) ^ (375 + 375 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 375 * (5 : ZMod 73851433) ^ 375) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 318636 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 73851433) ^ 1502 = 57031554 := by
        calc
          (5 : ZMod 73851433) ^ 1502 = (5 : ZMod 73851433) ^ (751 + 751) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 751 * (5 : ZMod 73851433) ^ 751 := by rw [pow_add]
          _ = 57031554 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 73851433) ^ 3005 = 14660299 := by
        calc
          (5 : ZMod 73851433) ^ 3005 = (5 : ZMod 73851433) ^ (1502 + 1502 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 1502 * (5 : ZMod 73851433) ^ 1502) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 14660299 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 73851433) ^ 6010 = 6315543 := by
        calc
          (5 : ZMod 73851433) ^ 6010 = (5 : ZMod 73851433) ^ (3005 + 3005) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 3005 * (5 : ZMod 73851433) ^ 3005 := by rw [pow_add]
          _ = 6315543 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 73851433) ^ 12020 = 32193044 := by
        calc
          (5 : ZMod 73851433) ^ 12020 = (5 : ZMod 73851433) ^ (6010 + 6010) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 6010 * (5 : ZMod 73851433) ^ 6010 := by rw [pow_add]
          _ = 32193044 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 73851433) ^ 24040 = 64820560 := by
        calc
          (5 : ZMod 73851433) ^ 24040 = (5 : ZMod 73851433) ^ (12020 + 12020) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 12020 * (5 : ZMod 73851433) ^ 12020 := by rw [pow_add]
          _ = 64820560 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 73851433) ^ 48080 = 18731507 := by
        calc
          (5 : ZMod 73851433) ^ 48080 = (5 : ZMod 73851433) ^ (24040 + 24040) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 24040 * (5 : ZMod 73851433) ^ 24040 := by rw [pow_add]
          _ = 18731507 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 73851433) ^ 96160 = 14685121 := by
        calc
          (5 : ZMod 73851433) ^ 96160 = (5 : ZMod 73851433) ^ (48080 + 48080) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 48080 * (5 : ZMod 73851433) ^ 48080 := by rw [pow_add]
          _ = 14685121 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 73851433) ^ 192321 = 34384087 := by
        calc
          (5 : ZMod 73851433) ^ 192321 = (5 : ZMod 73851433) ^ (96160 + 96160 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 96160 * (5 : ZMod 73851433) ^ 96160) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 34384087 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 73851433) ^ 384642 = 3356469 := by
        calc
          (5 : ZMod 73851433) ^ 384642 = (5 : ZMod 73851433) ^ (192321 + 192321) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 192321 * (5 : ZMod 73851433) ^ 192321 := by rw [pow_add]
          _ = 3356469 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 73851433) ^ 769285 = 52584818 := by
        calc
          (5 : ZMod 73851433) ^ 769285 = (5 : ZMod 73851433) ^ (384642 + 384642 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 384642 * (5 : ZMod 73851433) ^ 384642) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 52584818 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 73851433) ^ 1538571 = 26816020 := by
        calc
          (5 : ZMod 73851433) ^ 1538571 = (5 : ZMod 73851433) ^ (769285 + 769285 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 769285 * (5 : ZMod 73851433) ^ 769285) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 26816020 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 73851433) ^ 3077143 = 37217603 := by
        calc
          (5 : ZMod 73851433) ^ 3077143 = (5 : ZMod 73851433) ^ (1538571 + 1538571 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 1538571 * (5 : ZMod 73851433) ^ 1538571) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 37217603 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 73851433) ^ 6154286 = 28563775 := by
        calc
          (5 : ZMod 73851433) ^ 6154286 = (5 : ZMod 73851433) ^ (3077143 + 3077143) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 3077143 * (5 : ZMod 73851433) ^ 3077143 := by rw [pow_add]
          _ = 28563775 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 73851433) ^ 12308572 = 27382195 := by
        calc
          (5 : ZMod 73851433) ^ 12308572 = (5 : ZMod 73851433) ^ (6154286 + 6154286) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 6154286 * (5 : ZMod 73851433) ^ 6154286 := by rw [pow_add]
          _ = 27382195 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 73851433) ^ 24617144 = 27382194 := by
        calc
          (5 : ZMod 73851433) ^ 24617144 = (5 : ZMod 73851433) ^ (12308572 + 12308572) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 12308572 * (5 : ZMod 73851433) ^ 12308572 := by rw [pow_add]
          _ = 27382194 := by rw [factor_1_23]; decide
      change (5 : ZMod 73851433) ^ 24617144 ≠ 1
      rw [factor_1_24]
      decide
    ·
      have factor_2_0 : (5 : ZMod 73851433) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 73851433) ^ 3 = 125 := by
        calc
          (5 : ZMod 73851433) ^ 3 = (5 : ZMod 73851433) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = ((5 : ZMod 73851433) ^ 1 * (5 : ZMod 73851433) ^ 1) * (5 : ZMod 73851433) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 73851433) ^ 6 = 15625 := by
        calc
          (5 : ZMod 73851433) ^ 6 = (5 : ZMod 73851433) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 3 * (5 : ZMod 73851433) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 73851433) ^ 12 = 22586326 := by
        calc
          (5 : ZMod 73851433) ^ 12 = (5 : ZMod 73851433) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 6 * (5 : ZMod 73851433) ^ 6 := by rw [pow_add]
          _ = 22586326 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 73851433) ^ 24 = 55472836 := by
        calc
          (5 : ZMod 73851433) ^ 24 = (5 : ZMod 73851433) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 73851433) ^ n) (by norm_num)
          _ = (5 : ZMod 73851433) ^ 12 * (5 : ZMod 73851433) ^ 12 := by rw [pow_add]
          _ = 55472836 := by rw [factor_2_3]; decide
      change (5 : ZMod 73851433) ^ 24 ≠ 1
      rw [factor_2_4]
      decide

#print axioms prime_lucas_73851433

end TotientTailPeriodKiller
end Erdos249257
