import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_246258553 : Nat.Prime 246258553 := by
  apply lucas_primality 246258553 (5 : ZMod 246258553)
  ·
      have fermat_0 : (5 : ZMod 246258553) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 246258553) ^ 3 = 125 := by
        calc
          (5 : ZMod 246258553) ^ 3 = (5 : ZMod 246258553) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 1 * (5 : ZMod 246258553) ^ 1) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 246258553) ^ 7 = 78125 := by
        calc
          (5 : ZMod 246258553) ^ 7 = (5 : ZMod 246258553) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 3 * (5 : ZMod 246258553) ^ 3) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 246258553) ^ 14 = 193310353 := by
        calc
          (5 : ZMod 246258553) ^ 14 = (5 : ZMod 246258553) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 7 * (5 : ZMod 246258553) ^ 7 := by rw [pow_add]
          _ = 193310353 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 246258553) ^ 29 = 18790534 := by
        calc
          (5 : ZMod 246258553) ^ 29 = (5 : ZMod 246258553) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 14 * (5 : ZMod 246258553) ^ 14) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 18790534 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 246258553) ^ 58 = 132265074 := by
        calc
          (5 : ZMod 246258553) ^ 58 = (5 : ZMod 246258553) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 29 * (5 : ZMod 246258553) ^ 29 := by rw [pow_add]
          _ = 132265074 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 246258553) ^ 117 = 234189745 := by
        calc
          (5 : ZMod 246258553) ^ 117 = (5 : ZMod 246258553) ^ (58 + 58 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 58 * (5 : ZMod 246258553) ^ 58) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 234189745 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 246258553) ^ 234 = 102646636 := by
        calc
          (5 : ZMod 246258553) ^ 234 = (5 : ZMod 246258553) ^ (117 + 117) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 117 * (5 : ZMod 246258553) ^ 117 := by rw [pow_add]
          _ = 102646636 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 246258553) ^ 469 = 89828654 := by
        calc
          (5 : ZMod 246258553) ^ 469 = (5 : ZMod 246258553) ^ (234 + 234 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 234 * (5 : ZMod 246258553) ^ 234) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 89828654 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 246258553) ^ 939 = 127014517 := by
        calc
          (5 : ZMod 246258553) ^ 939 = (5 : ZMod 246258553) ^ (469 + 469 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 469 * (5 : ZMod 246258553) ^ 469) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 127014517 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 246258553) ^ 1878 = 121654961 := by
        calc
          (5 : ZMod 246258553) ^ 1878 = (5 : ZMod 246258553) ^ (939 + 939) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 939 * (5 : ZMod 246258553) ^ 939 := by rw [pow_add]
          _ = 121654961 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 246258553) ^ 3757 = 86942067 := by
        calc
          (5 : ZMod 246258553) ^ 3757 = (5 : ZMod 246258553) ^ (1878 + 1878 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 1878 * (5 : ZMod 246258553) ^ 1878) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 86942067 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 246258553) ^ 7515 = 167837978 := by
        calc
          (5 : ZMod 246258553) ^ 7515 = (5 : ZMod 246258553) ^ (3757 + 3757 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 3757 * (5 : ZMod 246258553) ^ 3757) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 167837978 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 246258553) ^ 15030 = 58995220 := by
        calc
          (5 : ZMod 246258553) ^ 15030 = (5 : ZMod 246258553) ^ (7515 + 7515) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 7515 * (5 : ZMod 246258553) ^ 7515 := by rw [pow_add]
          _ = 58995220 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 246258553) ^ 30060 = 72334173 := by
        calc
          (5 : ZMod 246258553) ^ 30060 = (5 : ZMod 246258553) ^ (15030 + 15030) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 15030 * (5 : ZMod 246258553) ^ 15030 := by rw [pow_add]
          _ = 72334173 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 246258553) ^ 60121 = 50241790 := by
        calc
          (5 : ZMod 246258553) ^ 60121 = (5 : ZMod 246258553) ^ (30060 + 30060 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 30060 * (5 : ZMod 246258553) ^ 30060) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 50241790 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 246258553) ^ 120243 = 100614584 := by
        calc
          (5 : ZMod 246258553) ^ 120243 = (5 : ZMod 246258553) ^ (60121 + 60121 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 60121 * (5 : ZMod 246258553) ^ 60121) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 100614584 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 246258553) ^ 240486 = 152123515 := by
        calc
          (5 : ZMod 246258553) ^ 240486 = (5 : ZMod 246258553) ^ (120243 + 120243) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 120243 * (5 : ZMod 246258553) ^ 120243 := by rw [pow_add]
          _ = 152123515 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 246258553) ^ 480973 = 145271281 := by
        calc
          (5 : ZMod 246258553) ^ 480973 = (5 : ZMod 246258553) ^ (240486 + 240486 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 240486 * (5 : ZMod 246258553) ^ 240486) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 145271281 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 246258553) ^ 961947 = 144096890 := by
        calc
          (5 : ZMod 246258553) ^ 961947 = (5 : ZMod 246258553) ^ (480973 + 480973 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 480973 * (5 : ZMod 246258553) ^ 480973) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 144096890 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 246258553) ^ 1923894 = 38562351 := by
        calc
          (5 : ZMod 246258553) ^ 1923894 = (5 : ZMod 246258553) ^ (961947 + 961947) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 961947 * (5 : ZMod 246258553) ^ 961947 := by rw [pow_add]
          _ = 38562351 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 246258553) ^ 3847789 = 179107678 := by
        calc
          (5 : ZMod 246258553) ^ 3847789 = (5 : ZMod 246258553) ^ (1923894 + 1923894 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 1923894 * (5 : ZMod 246258553) ^ 1923894) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 179107678 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 246258553) ^ 7695579 = 216481549 := by
        calc
          (5 : ZMod 246258553) ^ 7695579 = (5 : ZMod 246258553) ^ (3847789 + 3847789 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 3847789 * (5 : ZMod 246258553) ^ 3847789) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 216481549 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 246258553) ^ 15391159 = 201667855 := by
        calc
          (5 : ZMod 246258553) ^ 15391159 = (5 : ZMod 246258553) ^ (7695579 + 7695579 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 7695579 * (5 : ZMod 246258553) ^ 7695579) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 201667855 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 246258553) ^ 30782319 = 150544809 := by
        calc
          (5 : ZMod 246258553) ^ 30782319 = (5 : ZMod 246258553) ^ (15391159 + 15391159 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 15391159 * (5 : ZMod 246258553) ^ 15391159) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 150544809 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 246258553) ^ 61564638 = 213394452 := by
        calc
          (5 : ZMod 246258553) ^ 61564638 = (5 : ZMod 246258553) ^ (30782319 + 30782319) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 30782319 * (5 : ZMod 246258553) ^ 30782319 := by rw [pow_add]
          _ = 213394452 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 246258553) ^ 123129276 = 246258552 := by
        calc
          (5 : ZMod 246258553) ^ 123129276 = (5 : ZMod 246258553) ^ (61564638 + 61564638) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 61564638 * (5 : ZMod 246258553) ^ 61564638 := by rw [pow_add]
          _ = 246258552 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 246258553) ^ 246258552 = 1 := by
        calc
          (5 : ZMod 246258553) ^ 246258552 = (5 : ZMod 246258553) ^ (123129276 + 123129276) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 123129276 * (5 : ZMod 246258553) ^ 123129276 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (647, 1), (15859, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (647, 1), (15859, 1)] : List FactorBlock).map factorBlockValue).prod = 246258553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 246258553) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 246258553) ^ 3 = 125 := by
        calc
          (5 : ZMod 246258553) ^ 3 = (5 : ZMod 246258553) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 1 * (5 : ZMod 246258553) ^ 1) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 246258553) ^ 7 = 78125 := by
        calc
          (5 : ZMod 246258553) ^ 7 = (5 : ZMod 246258553) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 3 * (5 : ZMod 246258553) ^ 3) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 246258553) ^ 14 = 193310353 := by
        calc
          (5 : ZMod 246258553) ^ 14 = (5 : ZMod 246258553) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 7 * (5 : ZMod 246258553) ^ 7 := by rw [pow_add]
          _ = 193310353 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 246258553) ^ 29 = 18790534 := by
        calc
          (5 : ZMod 246258553) ^ 29 = (5 : ZMod 246258553) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 14 * (5 : ZMod 246258553) ^ 14) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 18790534 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 246258553) ^ 58 = 132265074 := by
        calc
          (5 : ZMod 246258553) ^ 58 = (5 : ZMod 246258553) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 29 * (5 : ZMod 246258553) ^ 29 := by rw [pow_add]
          _ = 132265074 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 246258553) ^ 117 = 234189745 := by
        calc
          (5 : ZMod 246258553) ^ 117 = (5 : ZMod 246258553) ^ (58 + 58 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 58 * (5 : ZMod 246258553) ^ 58) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 234189745 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 246258553) ^ 234 = 102646636 := by
        calc
          (5 : ZMod 246258553) ^ 234 = (5 : ZMod 246258553) ^ (117 + 117) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 117 * (5 : ZMod 246258553) ^ 117 := by rw [pow_add]
          _ = 102646636 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 246258553) ^ 469 = 89828654 := by
        calc
          (5 : ZMod 246258553) ^ 469 = (5 : ZMod 246258553) ^ (234 + 234 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 234 * (5 : ZMod 246258553) ^ 234) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 89828654 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 246258553) ^ 939 = 127014517 := by
        calc
          (5 : ZMod 246258553) ^ 939 = (5 : ZMod 246258553) ^ (469 + 469 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 469 * (5 : ZMod 246258553) ^ 469) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 127014517 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 246258553) ^ 1878 = 121654961 := by
        calc
          (5 : ZMod 246258553) ^ 1878 = (5 : ZMod 246258553) ^ (939 + 939) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 939 * (5 : ZMod 246258553) ^ 939 := by rw [pow_add]
          _ = 121654961 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 246258553) ^ 3757 = 86942067 := by
        calc
          (5 : ZMod 246258553) ^ 3757 = (5 : ZMod 246258553) ^ (1878 + 1878 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 1878 * (5 : ZMod 246258553) ^ 1878) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 86942067 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 246258553) ^ 7515 = 167837978 := by
        calc
          (5 : ZMod 246258553) ^ 7515 = (5 : ZMod 246258553) ^ (3757 + 3757 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 3757 * (5 : ZMod 246258553) ^ 3757) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 167837978 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 246258553) ^ 15030 = 58995220 := by
        calc
          (5 : ZMod 246258553) ^ 15030 = (5 : ZMod 246258553) ^ (7515 + 7515) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 7515 * (5 : ZMod 246258553) ^ 7515 := by rw [pow_add]
          _ = 58995220 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 246258553) ^ 30060 = 72334173 := by
        calc
          (5 : ZMod 246258553) ^ 30060 = (5 : ZMod 246258553) ^ (15030 + 15030) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 15030 * (5 : ZMod 246258553) ^ 15030 := by rw [pow_add]
          _ = 72334173 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 246258553) ^ 60121 = 50241790 := by
        calc
          (5 : ZMod 246258553) ^ 60121 = (5 : ZMod 246258553) ^ (30060 + 30060 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 30060 * (5 : ZMod 246258553) ^ 30060) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 50241790 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 246258553) ^ 120243 = 100614584 := by
        calc
          (5 : ZMod 246258553) ^ 120243 = (5 : ZMod 246258553) ^ (60121 + 60121 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 60121 * (5 : ZMod 246258553) ^ 60121) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 100614584 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 246258553) ^ 240486 = 152123515 := by
        calc
          (5 : ZMod 246258553) ^ 240486 = (5 : ZMod 246258553) ^ (120243 + 120243) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 120243 * (5 : ZMod 246258553) ^ 120243 := by rw [pow_add]
          _ = 152123515 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 246258553) ^ 480973 = 145271281 := by
        calc
          (5 : ZMod 246258553) ^ 480973 = (5 : ZMod 246258553) ^ (240486 + 240486 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 240486 * (5 : ZMod 246258553) ^ 240486) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 145271281 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 246258553) ^ 961947 = 144096890 := by
        calc
          (5 : ZMod 246258553) ^ 961947 = (5 : ZMod 246258553) ^ (480973 + 480973 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 480973 * (5 : ZMod 246258553) ^ 480973) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 144096890 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 246258553) ^ 1923894 = 38562351 := by
        calc
          (5 : ZMod 246258553) ^ 1923894 = (5 : ZMod 246258553) ^ (961947 + 961947) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 961947 * (5 : ZMod 246258553) ^ 961947 := by rw [pow_add]
          _ = 38562351 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 246258553) ^ 3847789 = 179107678 := by
        calc
          (5 : ZMod 246258553) ^ 3847789 = (5 : ZMod 246258553) ^ (1923894 + 1923894 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 1923894 * (5 : ZMod 246258553) ^ 1923894) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 179107678 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 246258553) ^ 7695579 = 216481549 := by
        calc
          (5 : ZMod 246258553) ^ 7695579 = (5 : ZMod 246258553) ^ (3847789 + 3847789 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 3847789 * (5 : ZMod 246258553) ^ 3847789) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 216481549 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 246258553) ^ 15391159 = 201667855 := by
        calc
          (5 : ZMod 246258553) ^ 15391159 = (5 : ZMod 246258553) ^ (7695579 + 7695579 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 7695579 * (5 : ZMod 246258553) ^ 7695579) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 201667855 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 246258553) ^ 30782319 = 150544809 := by
        calc
          (5 : ZMod 246258553) ^ 30782319 = (5 : ZMod 246258553) ^ (15391159 + 15391159 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 15391159 * (5 : ZMod 246258553) ^ 15391159) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 150544809 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 246258553) ^ 61564638 = 213394452 := by
        calc
          (5 : ZMod 246258553) ^ 61564638 = (5 : ZMod 246258553) ^ (30782319 + 30782319) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 30782319 * (5 : ZMod 246258553) ^ 30782319 := by rw [pow_add]
          _ = 213394452 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 246258553) ^ 123129276 = 246258552 := by
        calc
          (5 : ZMod 246258553) ^ 123129276 = (5 : ZMod 246258553) ^ (61564638 + 61564638) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 61564638 * (5 : ZMod 246258553) ^ 61564638 := by rw [pow_add]
          _ = 246258552 := by rw [factor_0_25]; decide
      change (5 : ZMod 246258553) ^ 123129276 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (5 : ZMod 246258553) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 246258553) ^ 2 = 25 := by
        calc
          (5 : ZMod 246258553) ^ 2 = (5 : ZMod 246258553) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 1 * (5 : ZMod 246258553) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 246258553) ^ 4 = 625 := by
        calc
          (5 : ZMod 246258553) ^ 4 = (5 : ZMod 246258553) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 2 * (5 : ZMod 246258553) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 246258553) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 246258553) ^ 9 = (5 : ZMod 246258553) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 4 * (5 : ZMod 246258553) ^ 4) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 246258553) ^ 19 = 22622616 := by
        calc
          (5 : ZMod 246258553) ^ 19 = (5 : ZMod 246258553) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 9 * (5 : ZMod 246258553) ^ 9) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 22622616 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 246258553) ^ 39 = 24015929 := by
        calc
          (5 : ZMod 246258553) ^ 39 = (5 : ZMod 246258553) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 19 * (5 : ZMod 246258553) ^ 19) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 24015929 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 246258553) ^ 78 = 226166211 := by
        calc
          (5 : ZMod 246258553) ^ 78 = (5 : ZMod 246258553) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 39 * (5 : ZMod 246258553) ^ 39 := by rw [pow_add]
          _ = 226166211 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 246258553) ^ 156 = 218252838 := by
        calc
          (5 : ZMod 246258553) ^ 156 = (5 : ZMod 246258553) ^ (78 + 78) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 78 * (5 : ZMod 246258553) ^ 78 := by rw [pow_add]
          _ = 218252838 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 246258553) ^ 313 = 135366094 := by
        calc
          (5 : ZMod 246258553) ^ 313 = (5 : ZMod 246258553) ^ (156 + 156 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 156 * (5 : ZMod 246258553) ^ 156) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 135366094 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 246258553) ^ 626 = 157743594 := by
        calc
          (5 : ZMod 246258553) ^ 626 = (5 : ZMod 246258553) ^ (313 + 313) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 313 * (5 : ZMod 246258553) ^ 313 := by rw [pow_add]
          _ = 157743594 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 246258553) ^ 1252 = 118006014 := by
        calc
          (5 : ZMod 246258553) ^ 1252 = (5 : ZMod 246258553) ^ (626 + 626) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 626 * (5 : ZMod 246258553) ^ 626 := by rw [pow_add]
          _ = 118006014 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 246258553) ^ 2505 = 214746050 := by
        calc
          (5 : ZMod 246258553) ^ 2505 = (5 : ZMod 246258553) ^ (1252 + 1252 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 1252 * (5 : ZMod 246258553) ^ 1252) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 214746050 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 246258553) ^ 5010 = 230352509 := by
        calc
          (5 : ZMod 246258553) ^ 5010 = (5 : ZMod 246258553) ^ (2505 + 2505) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 2505 * (5 : ZMod 246258553) ^ 2505 := by rw [pow_add]
          _ = 230352509 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 246258553) ^ 10020 = 138514584 := by
        calc
          (5 : ZMod 246258553) ^ 10020 = (5 : ZMod 246258553) ^ (5010 + 5010) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 5010 * (5 : ZMod 246258553) ^ 5010 := by rw [pow_add]
          _ = 138514584 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 246258553) ^ 20040 = 210283023 := by
        calc
          (5 : ZMod 246258553) ^ 20040 = (5 : ZMod 246258553) ^ (10020 + 10020) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 10020 * (5 : ZMod 246258553) ^ 10020 := by rw [pow_add]
          _ = 210283023 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 246258553) ^ 40081 = 210277062 := by
        calc
          (5 : ZMod 246258553) ^ 40081 = (5 : ZMod 246258553) ^ (20040 + 20040 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 20040 * (5 : ZMod 246258553) ^ 20040) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 210277062 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 246258553) ^ 80162 = 44709978 := by
        calc
          (5 : ZMod 246258553) ^ 80162 = (5 : ZMod 246258553) ^ (40081 + 40081) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 40081 * (5 : ZMod 246258553) ^ 40081 := by rw [pow_add]
          _ = 44709978 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 246258553) ^ 160324 = 245794201 := by
        calc
          (5 : ZMod 246258553) ^ 160324 = (5 : ZMod 246258553) ^ (80162 + 80162) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 80162 * (5 : ZMod 246258553) ^ 80162 := by rw [pow_add]
          _ = 245794201 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 246258553) ^ 320649 = 240213039 := by
        calc
          (5 : ZMod 246258553) ^ 320649 = (5 : ZMod 246258553) ^ (160324 + 160324 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 160324 * (5 : ZMod 246258553) ^ 160324) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 240213039 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 246258553) ^ 641298 = 22639254 := by
        calc
          (5 : ZMod 246258553) ^ 641298 = (5 : ZMod 246258553) ^ (320649 + 320649) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 320649 * (5 : ZMod 246258553) ^ 320649 := by rw [pow_add]
          _ = 22639254 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 246258553) ^ 1282596 = 111644593 := by
        calc
          (5 : ZMod 246258553) ^ 1282596 = (5 : ZMod 246258553) ^ (641298 + 641298) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 641298 * (5 : ZMod 246258553) ^ 641298 := by rw [pow_add]
          _ = 111644593 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 246258553) ^ 2565193 = 197410762 := by
        calc
          (5 : ZMod 246258553) ^ 2565193 = (5 : ZMod 246258553) ^ (1282596 + 1282596 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 1282596 * (5 : ZMod 246258553) ^ 1282596) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 197410762 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 246258553) ^ 5130386 = 196833573 := by
        calc
          (5 : ZMod 246258553) ^ 5130386 = (5 : ZMod 246258553) ^ (2565193 + 2565193) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 2565193 * (5 : ZMod 246258553) ^ 2565193 := by rw [pow_add]
          _ = 196833573 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 246258553) ^ 10260773 = 238469526 := by
        calc
          (5 : ZMod 246258553) ^ 10260773 = (5 : ZMod 246258553) ^ (5130386 + 5130386 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 5130386 * (5 : ZMod 246258553) ^ 5130386) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 238469526 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 246258553) ^ 20521546 = 191972543 := by
        calc
          (5 : ZMod 246258553) ^ 20521546 = (5 : ZMod 246258553) ^ (10260773 + 10260773) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 10260773 * (5 : ZMod 246258553) ^ 10260773 := by rw [pow_add]
          _ = 191972543 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 246258553) ^ 41043092 = 195657266 := by
        calc
          (5 : ZMod 246258553) ^ 41043092 = (5 : ZMod 246258553) ^ (20521546 + 20521546) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 20521546 * (5 : ZMod 246258553) ^ 20521546 := by rw [pow_add]
          _ = 195657266 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 246258553) ^ 82086184 = 195657265 := by
        calc
          (5 : ZMod 246258553) ^ 82086184 = (5 : ZMod 246258553) ^ (41043092 + 41043092) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 41043092 * (5 : ZMod 246258553) ^ 41043092 := by rw [pow_add]
          _ = 195657265 := by rw [factor_1_25]; decide
      change (5 : ZMod 246258553) ^ 82086184 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (5 : ZMod 246258553) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 246258553) ^ 2 = 25 := by
        calc
          (5 : ZMod 246258553) ^ 2 = (5 : ZMod 246258553) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 1 * (5 : ZMod 246258553) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 246258553) ^ 5 = 3125 := by
        calc
          (5 : ZMod 246258553) ^ 5 = (5 : ZMod 246258553) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 2 * (5 : ZMod 246258553) ^ 2) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 246258553) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 246258553) ^ 11 = (5 : ZMod 246258553) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 5 * (5 : ZMod 246258553) ^ 5) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 246258553) ^ 23 = 102397479 := by
        calc
          (5 : ZMod 246258553) ^ 23 = (5 : ZMod 246258553) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 11 * (5 : ZMod 246258553) ^ 11) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 102397479 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 246258553) ^ 46 = 537818 := by
        calc
          (5 : ZMod 246258553) ^ 46 = (5 : ZMod 246258553) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 23 * (5 : ZMod 246258553) ^ 23 := by rw [pow_add]
          _ = 537818 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 246258553) ^ 92 = 140659902 := by
        calc
          (5 : ZMod 246258553) ^ 92 = (5 : ZMod 246258553) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 46 * (5 : ZMod 246258553) ^ 46 := by rw [pow_add]
          _ = 140659902 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 246258553) ^ 185 = 121190093 := by
        calc
          (5 : ZMod 246258553) ^ 185 = (5 : ZMod 246258553) ^ (92 + 92 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 92 * (5 : ZMod 246258553) ^ 92) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 121190093 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 246258553) ^ 371 = 14888620 := by
        calc
          (5 : ZMod 246258553) ^ 371 = (5 : ZMod 246258553) ^ (185 + 185 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 185 * (5 : ZMod 246258553) ^ 185) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 14888620 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 246258553) ^ 743 = 196126319 := by
        calc
          (5 : ZMod 246258553) ^ 743 = (5 : ZMod 246258553) ^ (371 + 371 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 371 * (5 : ZMod 246258553) ^ 371) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 196126319 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 246258553) ^ 1486 = 217737209 := by
        calc
          (5 : ZMod 246258553) ^ 1486 = (5 : ZMod 246258553) ^ (743 + 743) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 743 * (5 : ZMod 246258553) ^ 743 := by rw [pow_add]
          _ = 217737209 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 246258553) ^ 2973 = 17001908 := by
        calc
          (5 : ZMod 246258553) ^ 2973 = (5 : ZMod 246258553) ^ (1486 + 1486 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 1486 * (5 : ZMod 246258553) ^ 1486) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 17001908 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 246258553) ^ 5947 = 178257771 := by
        calc
          (5 : ZMod 246258553) ^ 5947 = (5 : ZMod 246258553) ^ (2973 + 2973 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 2973 * (5 : ZMod 246258553) ^ 2973) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 178257771 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 246258553) ^ 11894 = 164132992 := by
        calc
          (5 : ZMod 246258553) ^ 11894 = (5 : ZMod 246258553) ^ (5947 + 5947) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 5947 * (5 : ZMod 246258553) ^ 5947 := by rw [pow_add]
          _ = 164132992 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 246258553) ^ 23788 = 209780867 := by
        calc
          (5 : ZMod 246258553) ^ 23788 = (5 : ZMod 246258553) ^ (11894 + 11894) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 11894 * (5 : ZMod 246258553) ^ 11894 := by rw [pow_add]
          _ = 209780867 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 246258553) ^ 47577 = 147741806 := by
        calc
          (5 : ZMod 246258553) ^ 47577 = (5 : ZMod 246258553) ^ (23788 + 23788 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 23788 * (5 : ZMod 246258553) ^ 23788) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 147741806 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 246258553) ^ 95154 = 207127972 := by
        calc
          (5 : ZMod 246258553) ^ 95154 = (5 : ZMod 246258553) ^ (47577 + 47577) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 47577 * (5 : ZMod 246258553) ^ 47577 := by rw [pow_add]
          _ = 207127972 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 246258553) ^ 190308 = 178006769 := by
        calc
          (5 : ZMod 246258553) ^ 190308 = (5 : ZMod 246258553) ^ (95154 + 95154) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 95154 * (5 : ZMod 246258553) ^ 95154 := by rw [pow_add]
          _ = 178006769 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 246258553) ^ 380616 = 181639143 := by
        calc
          (5 : ZMod 246258553) ^ 380616 = (5 : ZMod 246258553) ^ (190308 + 190308) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 190308 * (5 : ZMod 246258553) ^ 190308 := by rw [pow_add]
          _ = 181639143 := by rw [factor_2_17]; decide
      change (5 : ZMod 246258553) ^ 380616 ≠ 1
      rw [factor_2_18]
      decide
    ·
      have factor_3_0 : (5 : ZMod 246258553) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 246258553) ^ 3 = 125 := by
        calc
          (5 : ZMod 246258553) ^ 3 = (5 : ZMod 246258553) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 1 * (5 : ZMod 246258553) ^ 1) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 246258553) ^ 7 = 78125 := by
        calc
          (5 : ZMod 246258553) ^ 7 = (5 : ZMod 246258553) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 3 * (5 : ZMod 246258553) ^ 3) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 246258553) ^ 15 = 227776106 := by
        calc
          (5 : ZMod 246258553) ^ 15 = (5 : ZMod 246258553) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 7 * (5 : ZMod 246258553) ^ 7) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 227776106 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 246258553) ^ 30 = 93952670 := by
        calc
          (5 : ZMod 246258553) ^ 30 = (5 : ZMod 246258553) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 15 * (5 : ZMod 246258553) ^ 15 := by rw [pow_add]
          _ = 93952670 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 246258553) ^ 60 = 105265661 := by
        calc
          (5 : ZMod 246258553) ^ 60 = (5 : ZMod 246258553) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 30 * (5 : ZMod 246258553) ^ 30 := by rw [pow_add]
          _ = 105265661 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 246258553) ^ 121 = 91010143 := by
        calc
          (5 : ZMod 246258553) ^ 121 = (5 : ZMod 246258553) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 60 * (5 : ZMod 246258553) ^ 60) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 91010143 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 246258553) ^ 242 = 32070934 := by
        calc
          (5 : ZMod 246258553) ^ 242 = (5 : ZMod 246258553) ^ (121 + 121) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 121 * (5 : ZMod 246258553) ^ 121 := by rw [pow_add]
          _ = 32070934 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 246258553) ^ 485 = 45909331 := by
        calc
          (5 : ZMod 246258553) ^ 485 = (5 : ZMod 246258553) ^ (242 + 242 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 242 * (5 : ZMod 246258553) ^ 242) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 45909331 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 246258553) ^ 970 = 51086046 := by
        calc
          (5 : ZMod 246258553) ^ 970 = (5 : ZMod 246258553) ^ (485 + 485) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 485 * (5 : ZMod 246258553) ^ 485 := by rw [pow_add]
          _ = 51086046 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 246258553) ^ 1941 = 138478033 := by
        calc
          (5 : ZMod 246258553) ^ 1941 = (5 : ZMod 246258553) ^ (970 + 970 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = ((5 : ZMod 246258553) ^ 970 * (5 : ZMod 246258553) ^ 970) * (5 : ZMod 246258553) := by rw [pow_succ, pow_add]
          _ = 138478033 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 246258553) ^ 3882 = 34769992 := by
        calc
          (5 : ZMod 246258553) ^ 3882 = (5 : ZMod 246258553) ^ (1941 + 1941) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 1941 * (5 : ZMod 246258553) ^ 1941 := by rw [pow_add]
          _ = 34769992 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 246258553) ^ 7764 = 154608224 := by
        calc
          (5 : ZMod 246258553) ^ 7764 = (5 : ZMod 246258553) ^ (3882 + 3882) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 3882 * (5 : ZMod 246258553) ^ 3882 := by rw [pow_add]
          _ = 154608224 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 246258553) ^ 15528 = 96331017 := by
        calc
          (5 : ZMod 246258553) ^ 15528 = (5 : ZMod 246258553) ^ (7764 + 7764) :=
            congrArg (fun n : ℕ => (5 : ZMod 246258553) ^ n) (by norm_num)
          _ = (5 : ZMod 246258553) ^ 7764 * (5 : ZMod 246258553) ^ 7764 := by rw [pow_add]
          _ = 96331017 := by rw [factor_3_12]; decide
      change (5 : ZMod 246258553) ^ 15528 ≠ 1
      rw [factor_3_13]
      decide

#print axioms prime_lucas_246258553

end TotientTailPeriodKiller
end Erdos249257
