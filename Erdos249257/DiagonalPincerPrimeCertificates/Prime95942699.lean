import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_95942699 : Nat.Prime 95942699 := by
  apply lucas_primality 95942699 (2 : ZMod 95942699)
  ·
      have fermat_0 : (2 : ZMod 95942699) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 95942699) ^ 2 = 4 := by
        calc
          (2 : ZMod 95942699) ^ 2 = (2 : ZMod 95942699) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 1 * (2 : ZMod 95942699) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 95942699) ^ 5 = 32 := by
        calc
          (2 : ZMod 95942699) ^ 5 = (2 : ZMod 95942699) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 2 * (2 : ZMod 95942699) ^ 2) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 95942699) ^ 11 = 2048 := by
        calc
          (2 : ZMod 95942699) ^ 11 = (2 : ZMod 95942699) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 5 * (2 : ZMod 95942699) ^ 5) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 95942699) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 95942699) ^ 22 = (2 : ZMod 95942699) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 11 * (2 : ZMod 95942699) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 95942699) ^ 45 = 73626154 := by
        calc
          (2 : ZMod 95942699) ^ 45 = (2 : ZMod 95942699) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 22 * (2 : ZMod 95942699) ^ 22) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 73626154 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 95942699) ^ 91 = 80021733 := by
        calc
          (2 : ZMod 95942699) ^ 91 = (2 : ZMod 95942699) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 45 * (2 : ZMod 95942699) ^ 45) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 80021733 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 95942699) ^ 182 = 1552320 := by
        calc
          (2 : ZMod 95942699) ^ 182 = (2 : ZMod 95942699) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 91 * (2 : ZMod 95942699) ^ 91 := by rw [pow_add]
          _ = 1552320 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 95942699) ^ 365 = 1108632 := by
        calc
          (2 : ZMod 95942699) ^ 365 = (2 : ZMod 95942699) ^ (182 + 182 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 182 * (2 : ZMod 95942699) ^ 182) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 1108632 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 95942699) ^ 731 = 77874468 := by
        calc
          (2 : ZMod 95942699) ^ 731 = (2 : ZMod 95942699) ^ (365 + 365 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 365 * (2 : ZMod 95942699) ^ 365) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 77874468 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 95942699) ^ 1463 = 23267654 := by
        calc
          (2 : ZMod 95942699) ^ 1463 = (2 : ZMod 95942699) ^ (731 + 731 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 731 * (2 : ZMod 95942699) ^ 731) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 23267654 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 95942699) ^ 2927 = 71372895 := by
        calc
          (2 : ZMod 95942699) ^ 2927 = (2 : ZMod 95942699) ^ (1463 + 1463 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 1463 * (2 : ZMod 95942699) ^ 1463) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 71372895 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 95942699) ^ 5855 = 33507611 := by
        calc
          (2 : ZMod 95942699) ^ 5855 = (2 : ZMod 95942699) ^ (2927 + 2927 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 2927 * (2 : ZMod 95942699) ^ 2927) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 33507611 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 95942699) ^ 11711 = 20471345 := by
        calc
          (2 : ZMod 95942699) ^ 11711 = (2 : ZMod 95942699) ^ (5855 + 5855 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 5855 * (2 : ZMod 95942699) ^ 5855) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 20471345 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 95942699) ^ 23423 = 63633913 := by
        calc
          (2 : ZMod 95942699) ^ 23423 = (2 : ZMod 95942699) ^ (11711 + 11711 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 11711 * (2 : ZMod 95942699) ^ 11711) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 63633913 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 95942699) ^ 46847 = 64608214 := by
        calc
          (2 : ZMod 95942699) ^ 46847 = (2 : ZMod 95942699) ^ (23423 + 23423 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 23423 * (2 : ZMod 95942699) ^ 23423) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 64608214 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 95942699) ^ 93694 = 146537 := by
        calc
          (2 : ZMod 95942699) ^ 93694 = (2 : ZMod 95942699) ^ (46847 + 46847) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 46847 * (2 : ZMod 95942699) ^ 46847 := by rw [pow_add]
          _ = 146537 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 95942699) ^ 187388 = 77870492 := by
        calc
          (2 : ZMod 95942699) ^ 187388 = (2 : ZMod 95942699) ^ (93694 + 93694) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 93694 * (2 : ZMod 95942699) ^ 93694 := by rw [pow_add]
          _ = 77870492 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 95942699) ^ 374776 = 79794912 := by
        calc
          (2 : ZMod 95942699) ^ 374776 = (2 : ZMod 95942699) ^ (187388 + 187388) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 187388 * (2 : ZMod 95942699) ^ 187388 := by rw [pow_add]
          _ = 79794912 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 95942699) ^ 749552 = 68394547 := by
        calc
          (2 : ZMod 95942699) ^ 749552 = (2 : ZMod 95942699) ^ (374776 + 374776) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 374776 * (2 : ZMod 95942699) ^ 374776 := by rw [pow_add]
          _ = 68394547 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 95942699) ^ 1499104 = 69857840 := by
        calc
          (2 : ZMod 95942699) ^ 1499104 = (2 : ZMod 95942699) ^ (749552 + 749552) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 749552 * (2 : ZMod 95942699) ^ 749552 := by rw [pow_add]
          _ = 69857840 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 95942699) ^ 2998209 = 8607642 := by
        calc
          (2 : ZMod 95942699) ^ 2998209 = (2 : ZMod 95942699) ^ (1499104 + 1499104 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 1499104 * (2 : ZMod 95942699) ^ 1499104) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 8607642 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 95942699) ^ 5996418 = 39325511 := by
        calc
          (2 : ZMod 95942699) ^ 5996418 = (2 : ZMod 95942699) ^ (2998209 + 2998209) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 2998209 * (2 : ZMod 95942699) ^ 2998209 := by rw [pow_add]
          _ = 39325511 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 95942699) ^ 11992837 = 15016647 := by
        calc
          (2 : ZMod 95942699) ^ 11992837 = (2 : ZMod 95942699) ^ (5996418 + 5996418 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 5996418 * (2 : ZMod 95942699) ^ 5996418) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 15016647 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 95942699) ^ 23985674 = 92929066 := by
        calc
          (2 : ZMod 95942699) ^ 23985674 = (2 : ZMod 95942699) ^ (11992837 + 11992837) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 11992837 * (2 : ZMod 95942699) ^ 11992837 := by rw [pow_add]
          _ = 92929066 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 95942699) ^ 47971349 = 95942698 := by
        calc
          (2 : ZMod 95942699) ^ 47971349 = (2 : ZMod 95942699) ^ (23985674 + 23985674 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 23985674 * (2 : ZMod 95942699) ^ 23985674) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 95942698 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 95942699) ^ 95942698 = 1 := by
        calc
          (2 : ZMod 95942699) ^ 95942698 = (2 : ZMod 95942699) ^ (47971349 + 47971349) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 47971349 * (2 : ZMod 95942699) ^ 47971349 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (47, 1), (1020667, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (47, 1), (1020667, 1)] : List FactorBlock).map factorBlockValue).prod = 95942699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 95942699) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 95942699) ^ 2 = 4 := by
        calc
          (2 : ZMod 95942699) ^ 2 = (2 : ZMod 95942699) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 1 * (2 : ZMod 95942699) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 95942699) ^ 5 = 32 := by
        calc
          (2 : ZMod 95942699) ^ 5 = (2 : ZMod 95942699) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 2 * (2 : ZMod 95942699) ^ 2) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 95942699) ^ 11 = 2048 := by
        calc
          (2 : ZMod 95942699) ^ 11 = (2 : ZMod 95942699) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 5 * (2 : ZMod 95942699) ^ 5) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 95942699) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 95942699) ^ 22 = (2 : ZMod 95942699) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 11 * (2 : ZMod 95942699) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 95942699) ^ 45 = 73626154 := by
        calc
          (2 : ZMod 95942699) ^ 45 = (2 : ZMod 95942699) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 22 * (2 : ZMod 95942699) ^ 22) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 73626154 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 95942699) ^ 91 = 80021733 := by
        calc
          (2 : ZMod 95942699) ^ 91 = (2 : ZMod 95942699) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 45 * (2 : ZMod 95942699) ^ 45) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 80021733 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 95942699) ^ 182 = 1552320 := by
        calc
          (2 : ZMod 95942699) ^ 182 = (2 : ZMod 95942699) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 91 * (2 : ZMod 95942699) ^ 91 := by rw [pow_add]
          _ = 1552320 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 95942699) ^ 365 = 1108632 := by
        calc
          (2 : ZMod 95942699) ^ 365 = (2 : ZMod 95942699) ^ (182 + 182 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 182 * (2 : ZMod 95942699) ^ 182) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 1108632 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 95942699) ^ 731 = 77874468 := by
        calc
          (2 : ZMod 95942699) ^ 731 = (2 : ZMod 95942699) ^ (365 + 365 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 365 * (2 : ZMod 95942699) ^ 365) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 77874468 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 95942699) ^ 1463 = 23267654 := by
        calc
          (2 : ZMod 95942699) ^ 1463 = (2 : ZMod 95942699) ^ (731 + 731 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 731 * (2 : ZMod 95942699) ^ 731) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 23267654 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 95942699) ^ 2927 = 71372895 := by
        calc
          (2 : ZMod 95942699) ^ 2927 = (2 : ZMod 95942699) ^ (1463 + 1463 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 1463 * (2 : ZMod 95942699) ^ 1463) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 71372895 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 95942699) ^ 5855 = 33507611 := by
        calc
          (2 : ZMod 95942699) ^ 5855 = (2 : ZMod 95942699) ^ (2927 + 2927 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 2927 * (2 : ZMod 95942699) ^ 2927) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 33507611 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 95942699) ^ 11711 = 20471345 := by
        calc
          (2 : ZMod 95942699) ^ 11711 = (2 : ZMod 95942699) ^ (5855 + 5855 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 5855 * (2 : ZMod 95942699) ^ 5855) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 20471345 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 95942699) ^ 23423 = 63633913 := by
        calc
          (2 : ZMod 95942699) ^ 23423 = (2 : ZMod 95942699) ^ (11711 + 11711 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 11711 * (2 : ZMod 95942699) ^ 11711) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 63633913 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 95942699) ^ 46847 = 64608214 := by
        calc
          (2 : ZMod 95942699) ^ 46847 = (2 : ZMod 95942699) ^ (23423 + 23423 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 23423 * (2 : ZMod 95942699) ^ 23423) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 64608214 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 95942699) ^ 93694 = 146537 := by
        calc
          (2 : ZMod 95942699) ^ 93694 = (2 : ZMod 95942699) ^ (46847 + 46847) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 46847 * (2 : ZMod 95942699) ^ 46847 := by rw [pow_add]
          _ = 146537 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 95942699) ^ 187388 = 77870492 := by
        calc
          (2 : ZMod 95942699) ^ 187388 = (2 : ZMod 95942699) ^ (93694 + 93694) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 93694 * (2 : ZMod 95942699) ^ 93694 := by rw [pow_add]
          _ = 77870492 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 95942699) ^ 374776 = 79794912 := by
        calc
          (2 : ZMod 95942699) ^ 374776 = (2 : ZMod 95942699) ^ (187388 + 187388) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 187388 * (2 : ZMod 95942699) ^ 187388 := by rw [pow_add]
          _ = 79794912 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 95942699) ^ 749552 = 68394547 := by
        calc
          (2 : ZMod 95942699) ^ 749552 = (2 : ZMod 95942699) ^ (374776 + 374776) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 374776 * (2 : ZMod 95942699) ^ 374776 := by rw [pow_add]
          _ = 68394547 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 95942699) ^ 1499104 = 69857840 := by
        calc
          (2 : ZMod 95942699) ^ 1499104 = (2 : ZMod 95942699) ^ (749552 + 749552) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 749552 * (2 : ZMod 95942699) ^ 749552 := by rw [pow_add]
          _ = 69857840 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 95942699) ^ 2998209 = 8607642 := by
        calc
          (2 : ZMod 95942699) ^ 2998209 = (2 : ZMod 95942699) ^ (1499104 + 1499104 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 1499104 * (2 : ZMod 95942699) ^ 1499104) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 8607642 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 95942699) ^ 5996418 = 39325511 := by
        calc
          (2 : ZMod 95942699) ^ 5996418 = (2 : ZMod 95942699) ^ (2998209 + 2998209) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 2998209 * (2 : ZMod 95942699) ^ 2998209 := by rw [pow_add]
          _ = 39325511 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 95942699) ^ 11992837 = 15016647 := by
        calc
          (2 : ZMod 95942699) ^ 11992837 = (2 : ZMod 95942699) ^ (5996418 + 5996418 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 5996418 * (2 : ZMod 95942699) ^ 5996418) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 15016647 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 95942699) ^ 23985674 = 92929066 := by
        calc
          (2 : ZMod 95942699) ^ 23985674 = (2 : ZMod 95942699) ^ (11992837 + 11992837) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 11992837 * (2 : ZMod 95942699) ^ 11992837 := by rw [pow_add]
          _ = 92929066 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 95942699) ^ 47971349 = 95942698 := by
        calc
          (2 : ZMod 95942699) ^ 47971349 = (2 : ZMod 95942699) ^ (23985674 + 23985674 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 23985674 * (2 : ZMod 95942699) ^ 23985674) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 95942698 := by rw [factor_0_24]; decide
      change (2 : ZMod 95942699) ^ 47971349 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (2 : ZMod 95942699) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 95942699) ^ 3 = 8 := by
        calc
          (2 : ZMod 95942699) ^ 3 = (2 : ZMod 95942699) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 1 * (2 : ZMod 95942699) ^ 1) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 95942699) ^ 7 = 128 := by
        calc
          (2 : ZMod 95942699) ^ 7 = (2 : ZMod 95942699) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 3 * (2 : ZMod 95942699) ^ 3) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 95942699) ^ 15 = 32768 := by
        calc
          (2 : ZMod 95942699) ^ 15 = (2 : ZMod 95942699) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 7 * (2 : ZMod 95942699) ^ 7) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 95942699) ^ 31 = 36744270 := by
        calc
          (2 : ZMod 95942699) ^ 31 = (2 : ZMod 95942699) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 15 * (2 : ZMod 95942699) ^ 15) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 36744270 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 95942699) ^ 62 = 26820872 := by
        calc
          (2 : ZMod 95942699) ^ 62 = (2 : ZMod 95942699) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 31 * (2 : ZMod 95942699) ^ 31 := by rw [pow_add]
          _ = 26820872 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 95942699) ^ 124 = 6278184 := by
        calc
          (2 : ZMod 95942699) ^ 124 = (2 : ZMod 95942699) ^ (62 + 62) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 62 * (2 : ZMod 95942699) ^ 62 := by rw [pow_add]
          _ = 6278184 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 95942699) ^ 249 = 61927760 := by
        calc
          (2 : ZMod 95942699) ^ 249 = (2 : ZMod 95942699) ^ (124 + 124 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 124 * (2 : ZMod 95942699) ^ 124) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 61927760 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 95942699) ^ 498 = 85603569 := by
        calc
          (2 : ZMod 95942699) ^ 498 = (2 : ZMod 95942699) ^ (249 + 249) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 249 * (2 : ZMod 95942699) ^ 249 := by rw [pow_add]
          _ = 85603569 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 95942699) ^ 996 = 76842381 := by
        calc
          (2 : ZMod 95942699) ^ 996 = (2 : ZMod 95942699) ^ (498 + 498) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 498 * (2 : ZMod 95942699) ^ 498 := by rw [pow_add]
          _ = 76842381 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 95942699) ^ 1993 = 69507248 := by
        calc
          (2 : ZMod 95942699) ^ 1993 = (2 : ZMod 95942699) ^ (996 + 996 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 996 * (2 : ZMod 95942699) ^ 996) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 69507248 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 95942699) ^ 3986 = 73920659 := by
        calc
          (2 : ZMod 95942699) ^ 3986 = (2 : ZMod 95942699) ^ (1993 + 1993) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 1993 * (2 : ZMod 95942699) ^ 1993 := by rw [pow_add]
          _ = 73920659 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 95942699) ^ 7973 = 4624081 := by
        calc
          (2 : ZMod 95942699) ^ 7973 = (2 : ZMod 95942699) ^ (3986 + 3986 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 3986 * (2 : ZMod 95942699) ^ 3986) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 4624081 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 95942699) ^ 15947 = 94734648 := by
        calc
          (2 : ZMod 95942699) ^ 15947 = (2 : ZMod 95942699) ^ (7973 + 7973 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 7973 * (2 : ZMod 95942699) ^ 7973) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 94734648 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 95942699) ^ 31895 = 5648224 := by
        calc
          (2 : ZMod 95942699) ^ 31895 = (2 : ZMod 95942699) ^ (15947 + 15947 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 15947 * (2 : ZMod 95942699) ^ 15947) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 5648224 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 95942699) ^ 63791 = 95592382 := by
        calc
          (2 : ZMod 95942699) ^ 63791 = (2 : ZMod 95942699) ^ (31895 + 31895 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 31895 * (2 : ZMod 95942699) ^ 31895) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 95592382 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 95942699) ^ 127583 = 22576936 := by
        calc
          (2 : ZMod 95942699) ^ 127583 = (2 : ZMod 95942699) ^ (63791 + 63791 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 63791 * (2 : ZMod 95942699) ^ 63791) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 22576936 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 95942699) ^ 255166 = 119030 := by
        calc
          (2 : ZMod 95942699) ^ 255166 = (2 : ZMod 95942699) ^ (127583 + 127583) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 127583 * (2 : ZMod 95942699) ^ 127583 := by rw [pow_add]
          _ = 119030 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 95942699) ^ 510333 = 33185595 := by
        calc
          (2 : ZMod 95942699) ^ 510333 = (2 : ZMod 95942699) ^ (255166 + 255166 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 255166 * (2 : ZMod 95942699) ^ 255166) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 33185595 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 95942699) ^ 1020667 = 48540063 := by
        calc
          (2 : ZMod 95942699) ^ 1020667 = (2 : ZMod 95942699) ^ (510333 + 510333 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 510333 * (2 : ZMod 95942699) ^ 510333) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 48540063 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 95942699) ^ 2041334 = 36192428 := by
        calc
          (2 : ZMod 95942699) ^ 2041334 = (2 : ZMod 95942699) ^ (1020667 + 1020667) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 1020667 * (2 : ZMod 95942699) ^ 1020667 := by rw [pow_add]
          _ = 36192428 := by rw [factor_1_19]; decide
      change (2 : ZMod 95942699) ^ 2041334 ≠ 1
      rw [factor_1_20]
      decide
    ·
      have factor_2_0 : (2 : ZMod 95942699) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 95942699) ^ 2 = 4 := by
        calc
          (2 : ZMod 95942699) ^ 2 = (2 : ZMod 95942699) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 1 * (2 : ZMod 95942699) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 95942699) ^ 5 = 32 := by
        calc
          (2 : ZMod 95942699) ^ 5 = (2 : ZMod 95942699) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 2 * (2 : ZMod 95942699) ^ 2) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 95942699) ^ 11 = 2048 := by
        calc
          (2 : ZMod 95942699) ^ 11 = (2 : ZMod 95942699) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 5 * (2 : ZMod 95942699) ^ 5) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 95942699) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 95942699) ^ 23 = (2 : ZMod 95942699) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 11 * (2 : ZMod 95942699) ^ 11) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 95942699) ^ 47 = 6676519 := by
        calc
          (2 : ZMod 95942699) ^ 47 = (2 : ZMod 95942699) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = ((2 : ZMod 95942699) ^ 23 * (2 : ZMod 95942699) ^ 23) * (2 : ZMod 95942699) := by rw [pow_succ, pow_add]
          _ = 6676519 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 95942699) ^ 94 = 64517670 := by
        calc
          (2 : ZMod 95942699) ^ 94 = (2 : ZMod 95942699) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (2 : ZMod 95942699) ^ n) (by norm_num)
          _ = (2 : ZMod 95942699) ^ 47 * (2 : ZMod 95942699) ^ 47 := by rw [pow_add]
          _ = 64517670 := by rw [factor_2_5]; decide
      change (2 : ZMod 95942699) ^ 94 ≠ 1
      rw [factor_2_6]
      decide

#print axioms prime_lucas_95942699

end TotientTailPeriodKiller
end Erdos249257
