import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_306555929 : Nat.Prime 306555929 := by
  apply lucas_primality 306555929 (3 : ZMod 306555929)
  ·
      have fermat_0 : (3 : ZMod 306555929) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 306555929) ^ 2 = 9 := by
        calc
          (3 : ZMod 306555929) ^ 2 = (3 : ZMod 306555929) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 1 * (3 : ZMod 306555929) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 306555929) ^ 4 = 81 := by
        calc
          (3 : ZMod 306555929) ^ 4 = (3 : ZMod 306555929) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 2 * (3 : ZMod 306555929) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 306555929) ^ 9 = 19683 := by
        calc
          (3 : ZMod 306555929) ^ 9 = (3 : ZMod 306555929) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 4 * (3 : ZMod 306555929) ^ 4) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 306555929) ^ 18 = 80864560 := by
        calc
          (3 : ZMod 306555929) ^ 18 = (3 : ZMod 306555929) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 9 * (3 : ZMod 306555929) ^ 9 := by rw [pow_add]
          _ = 80864560 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 306555929) ^ 36 = 291354909 := by
        calc
          (3 : ZMod 306555929) ^ 36 = (3 : ZMod 306555929) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 18 * (3 : ZMod 306555929) ^ 18 := by rw [pow_add]
          _ = 291354909 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 306555929) ^ 73 = 250765003 := by
        calc
          (3 : ZMod 306555929) ^ 73 = (3 : ZMod 306555929) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 36 * (3 : ZMod 306555929) ^ 36) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 250765003 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 306555929) ^ 146 = 149710674 := by
        calc
          (3 : ZMod 306555929) ^ 146 = (3 : ZMod 306555929) ^ (73 + 73) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 73 * (3 : ZMod 306555929) ^ 73 := by rw [pow_add]
          _ = 149710674 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 306555929) ^ 292 = 41703689 := by
        calc
          (3 : ZMod 306555929) ^ 292 = (3 : ZMod 306555929) ^ (146 + 146) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 146 * (3 : ZMod 306555929) ^ 146 := by rw [pow_add]
          _ = 41703689 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 306555929) ^ 584 = 129196216 := by
        calc
          (3 : ZMod 306555929) ^ 584 = (3 : ZMod 306555929) ^ (292 + 292) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 292 * (3 : ZMod 306555929) ^ 292 := by rw [pow_add]
          _ = 129196216 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 306555929) ^ 1169 = 256687832 := by
        calc
          (3 : ZMod 306555929) ^ 1169 = (3 : ZMod 306555929) ^ (584 + 584 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 584 * (3 : ZMod 306555929) ^ 584) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 256687832 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 306555929) ^ 2338 = 32075917 := by
        calc
          (3 : ZMod 306555929) ^ 2338 = (3 : ZMod 306555929) ^ (1169 + 1169) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 1169 * (3 : ZMod 306555929) ^ 1169 := by rw [pow_add]
          _ = 32075917 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 306555929) ^ 4677 = 35660261 := by
        calc
          (3 : ZMod 306555929) ^ 4677 = (3 : ZMod 306555929) ^ (2338 + 2338 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 2338 * (3 : ZMod 306555929) ^ 2338) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 35660261 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 306555929) ^ 9355 = 101846182 := by
        calc
          (3 : ZMod 306555929) ^ 9355 = (3 : ZMod 306555929) ^ (4677 + 4677 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 4677 * (3 : ZMod 306555929) ^ 4677) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 101846182 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 306555929) ^ 18710 = 287533313 := by
        calc
          (3 : ZMod 306555929) ^ 18710 = (3 : ZMod 306555929) ^ (9355 + 9355) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 9355 * (3 : ZMod 306555929) ^ 9355 := by rw [pow_add]
          _ = 287533313 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 306555929) ^ 37421 = 224004420 := by
        calc
          (3 : ZMod 306555929) ^ 37421 = (3 : ZMod 306555929) ^ (18710 + 18710 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 18710 * (3 : ZMod 306555929) ^ 18710) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 224004420 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 306555929) ^ 74842 = 154602134 := by
        calc
          (3 : ZMod 306555929) ^ 74842 = (3 : ZMod 306555929) ^ (37421 + 37421) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 37421 * (3 : ZMod 306555929) ^ 37421 := by rw [pow_add]
          _ = 154602134 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 306555929) ^ 149685 = 158047462 := by
        calc
          (3 : ZMod 306555929) ^ 149685 = (3 : ZMod 306555929) ^ (74842 + 74842 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 74842 * (3 : ZMod 306555929) ^ 74842) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 158047462 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 306555929) ^ 299371 = 141156237 := by
        calc
          (3 : ZMod 306555929) ^ 299371 = (3 : ZMod 306555929) ^ (149685 + 149685 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 149685 * (3 : ZMod 306555929) ^ 149685) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 141156237 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 306555929) ^ 598742 = 265504426 := by
        calc
          (3 : ZMod 306555929) ^ 598742 = (3 : ZMod 306555929) ^ (299371 + 299371) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 299371 * (3 : ZMod 306555929) ^ 299371 := by rw [pow_add]
          _ = 265504426 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 306555929) ^ 1197484 = 281850315 := by
        calc
          (3 : ZMod 306555929) ^ 1197484 = (3 : ZMod 306555929) ^ (598742 + 598742) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 598742 * (3 : ZMod 306555929) ^ 598742 := by rw [pow_add]
          _ = 281850315 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 306555929) ^ 2394968 = 100349333 := by
        calc
          (3 : ZMod 306555929) ^ 2394968 = (3 : ZMod 306555929) ^ (1197484 + 1197484) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 1197484 * (3 : ZMod 306555929) ^ 1197484 := by rw [pow_add]
          _ = 100349333 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 306555929) ^ 4789936 = 57572340 := by
        calc
          (3 : ZMod 306555929) ^ 4789936 = (3 : ZMod 306555929) ^ (2394968 + 2394968) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 2394968 * (3 : ZMod 306555929) ^ 2394968 := by rw [pow_add]
          _ = 57572340 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 306555929) ^ 9579872 = 275060758 := by
        calc
          (3 : ZMod 306555929) ^ 9579872 = (3 : ZMod 306555929) ^ (4789936 + 4789936) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 4789936 * (3 : ZMod 306555929) ^ 4789936 := by rw [pow_add]
          _ = 275060758 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 306555929) ^ 19159745 = 275145585 := by
        calc
          (3 : ZMod 306555929) ^ 19159745 = (3 : ZMod 306555929) ^ (9579872 + 9579872 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 9579872 * (3 : ZMod 306555929) ^ 9579872) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 275145585 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 306555929) ^ 38319491 = 60839321 := by
        calc
          (3 : ZMod 306555929) ^ 38319491 = (3 : ZMod 306555929) ^ (19159745 + 19159745 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 19159745 * (3 : ZMod 306555929) ^ 19159745) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 60839321 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 306555929) ^ 76638982 = 170358448 := by
        calc
          (3 : ZMod 306555929) ^ 76638982 = (3 : ZMod 306555929) ^ (38319491 + 38319491) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 38319491 * (3 : ZMod 306555929) ^ 38319491 := by rw [pow_add]
          _ = 170358448 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 306555929) ^ 153277964 = 306555928 := by
        calc
          (3 : ZMod 306555929) ^ 153277964 = (3 : ZMod 306555929) ^ (76638982 + 76638982) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 76638982 * (3 : ZMod 306555929) ^ 76638982 := by rw [pow_add]
          _ = 306555928 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 306555929) ^ 306555928 = 1 := by
        calc
          (3 : ZMod 306555929) ^ 306555928 = (3 : ZMod 306555929) ^ (153277964 + 153277964) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 153277964 * (3 : ZMod 306555929) ^ 153277964 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (5474213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (5474213, 1)] : List FactorBlock).map factorBlockValue).prod = 306555929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 306555929) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 306555929) ^ 2 = 9 := by
        calc
          (3 : ZMod 306555929) ^ 2 = (3 : ZMod 306555929) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 1 * (3 : ZMod 306555929) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 306555929) ^ 4 = 81 := by
        calc
          (3 : ZMod 306555929) ^ 4 = (3 : ZMod 306555929) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 2 * (3 : ZMod 306555929) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 306555929) ^ 9 = 19683 := by
        calc
          (3 : ZMod 306555929) ^ 9 = (3 : ZMod 306555929) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 4 * (3 : ZMod 306555929) ^ 4) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 306555929) ^ 18 = 80864560 := by
        calc
          (3 : ZMod 306555929) ^ 18 = (3 : ZMod 306555929) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 9 * (3 : ZMod 306555929) ^ 9 := by rw [pow_add]
          _ = 80864560 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 306555929) ^ 36 = 291354909 := by
        calc
          (3 : ZMod 306555929) ^ 36 = (3 : ZMod 306555929) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 18 * (3 : ZMod 306555929) ^ 18 := by rw [pow_add]
          _ = 291354909 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 306555929) ^ 73 = 250765003 := by
        calc
          (3 : ZMod 306555929) ^ 73 = (3 : ZMod 306555929) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 36 * (3 : ZMod 306555929) ^ 36) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 250765003 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 306555929) ^ 146 = 149710674 := by
        calc
          (3 : ZMod 306555929) ^ 146 = (3 : ZMod 306555929) ^ (73 + 73) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 73 * (3 : ZMod 306555929) ^ 73 := by rw [pow_add]
          _ = 149710674 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 306555929) ^ 292 = 41703689 := by
        calc
          (3 : ZMod 306555929) ^ 292 = (3 : ZMod 306555929) ^ (146 + 146) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 146 * (3 : ZMod 306555929) ^ 146 := by rw [pow_add]
          _ = 41703689 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 306555929) ^ 584 = 129196216 := by
        calc
          (3 : ZMod 306555929) ^ 584 = (3 : ZMod 306555929) ^ (292 + 292) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 292 * (3 : ZMod 306555929) ^ 292 := by rw [pow_add]
          _ = 129196216 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 306555929) ^ 1169 = 256687832 := by
        calc
          (3 : ZMod 306555929) ^ 1169 = (3 : ZMod 306555929) ^ (584 + 584 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 584 * (3 : ZMod 306555929) ^ 584) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 256687832 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 306555929) ^ 2338 = 32075917 := by
        calc
          (3 : ZMod 306555929) ^ 2338 = (3 : ZMod 306555929) ^ (1169 + 1169) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 1169 * (3 : ZMod 306555929) ^ 1169 := by rw [pow_add]
          _ = 32075917 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 306555929) ^ 4677 = 35660261 := by
        calc
          (3 : ZMod 306555929) ^ 4677 = (3 : ZMod 306555929) ^ (2338 + 2338 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 2338 * (3 : ZMod 306555929) ^ 2338) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 35660261 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 306555929) ^ 9355 = 101846182 := by
        calc
          (3 : ZMod 306555929) ^ 9355 = (3 : ZMod 306555929) ^ (4677 + 4677 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 4677 * (3 : ZMod 306555929) ^ 4677) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 101846182 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 306555929) ^ 18710 = 287533313 := by
        calc
          (3 : ZMod 306555929) ^ 18710 = (3 : ZMod 306555929) ^ (9355 + 9355) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 9355 * (3 : ZMod 306555929) ^ 9355 := by rw [pow_add]
          _ = 287533313 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 306555929) ^ 37421 = 224004420 := by
        calc
          (3 : ZMod 306555929) ^ 37421 = (3 : ZMod 306555929) ^ (18710 + 18710 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 18710 * (3 : ZMod 306555929) ^ 18710) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 224004420 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 306555929) ^ 74842 = 154602134 := by
        calc
          (3 : ZMod 306555929) ^ 74842 = (3 : ZMod 306555929) ^ (37421 + 37421) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 37421 * (3 : ZMod 306555929) ^ 37421 := by rw [pow_add]
          _ = 154602134 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 306555929) ^ 149685 = 158047462 := by
        calc
          (3 : ZMod 306555929) ^ 149685 = (3 : ZMod 306555929) ^ (74842 + 74842 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 74842 * (3 : ZMod 306555929) ^ 74842) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 158047462 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 306555929) ^ 299371 = 141156237 := by
        calc
          (3 : ZMod 306555929) ^ 299371 = (3 : ZMod 306555929) ^ (149685 + 149685 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 149685 * (3 : ZMod 306555929) ^ 149685) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 141156237 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 306555929) ^ 598742 = 265504426 := by
        calc
          (3 : ZMod 306555929) ^ 598742 = (3 : ZMod 306555929) ^ (299371 + 299371) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 299371 * (3 : ZMod 306555929) ^ 299371 := by rw [pow_add]
          _ = 265504426 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 306555929) ^ 1197484 = 281850315 := by
        calc
          (3 : ZMod 306555929) ^ 1197484 = (3 : ZMod 306555929) ^ (598742 + 598742) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 598742 * (3 : ZMod 306555929) ^ 598742 := by rw [pow_add]
          _ = 281850315 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 306555929) ^ 2394968 = 100349333 := by
        calc
          (3 : ZMod 306555929) ^ 2394968 = (3 : ZMod 306555929) ^ (1197484 + 1197484) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 1197484 * (3 : ZMod 306555929) ^ 1197484 := by rw [pow_add]
          _ = 100349333 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 306555929) ^ 4789936 = 57572340 := by
        calc
          (3 : ZMod 306555929) ^ 4789936 = (3 : ZMod 306555929) ^ (2394968 + 2394968) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 2394968 * (3 : ZMod 306555929) ^ 2394968 := by rw [pow_add]
          _ = 57572340 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 306555929) ^ 9579872 = 275060758 := by
        calc
          (3 : ZMod 306555929) ^ 9579872 = (3 : ZMod 306555929) ^ (4789936 + 4789936) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 4789936 * (3 : ZMod 306555929) ^ 4789936 := by rw [pow_add]
          _ = 275060758 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 306555929) ^ 19159745 = 275145585 := by
        calc
          (3 : ZMod 306555929) ^ 19159745 = (3 : ZMod 306555929) ^ (9579872 + 9579872 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 9579872 * (3 : ZMod 306555929) ^ 9579872) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 275145585 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 306555929) ^ 38319491 = 60839321 := by
        calc
          (3 : ZMod 306555929) ^ 38319491 = (3 : ZMod 306555929) ^ (19159745 + 19159745 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 19159745 * (3 : ZMod 306555929) ^ 19159745) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 60839321 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 306555929) ^ 76638982 = 170358448 := by
        calc
          (3 : ZMod 306555929) ^ 76638982 = (3 : ZMod 306555929) ^ (38319491 + 38319491) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 38319491 * (3 : ZMod 306555929) ^ 38319491 := by rw [pow_add]
          _ = 170358448 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 306555929) ^ 153277964 = 306555928 := by
        calc
          (3 : ZMod 306555929) ^ 153277964 = (3 : ZMod 306555929) ^ (76638982 + 76638982) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 76638982 * (3 : ZMod 306555929) ^ 76638982 := by rw [pow_add]
          _ = 306555928 := by rw [factor_0_26]; decide
      change (3 : ZMod 306555929) ^ 153277964 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (3 : ZMod 306555929) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 306555929) ^ 2 = 9 := by
        calc
          (3 : ZMod 306555929) ^ 2 = (3 : ZMod 306555929) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 1 * (3 : ZMod 306555929) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 306555929) ^ 5 = 243 := by
        calc
          (3 : ZMod 306555929) ^ 5 = (3 : ZMod 306555929) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 2 * (3 : ZMod 306555929) ^ 2) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 306555929) ^ 10 = 59049 := by
        calc
          (3 : ZMod 306555929) ^ 10 = (3 : ZMod 306555929) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 5 * (3 : ZMod 306555929) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 306555929) ^ 20 = 114669182 := by
        calc
          (3 : ZMod 306555929) ^ 20 = (3 : ZMod 306555929) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 10 * (3 : ZMod 306555929) ^ 10 := by rw [pow_add]
          _ = 114669182 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 306555929) ^ 41 = 291379217 := by
        calc
          (3 : ZMod 306555929) ^ 41 = (3 : ZMod 306555929) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 20 * (3 : ZMod 306555929) ^ 20) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 291379217 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 306555929) ^ 83 = 158179589 := by
        calc
          (3 : ZMod 306555929) ^ 83 = (3 : ZMod 306555929) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 41 * (3 : ZMod 306555929) ^ 41) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 158179589 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 306555929) ^ 167 = 108273574 := by
        calc
          (3 : ZMod 306555929) ^ 167 = (3 : ZMod 306555929) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 83 * (3 : ZMod 306555929) ^ 83) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 108273574 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 306555929) ^ 334 = 297425822 := by
        calc
          (3 : ZMod 306555929) ^ 334 = (3 : ZMod 306555929) ^ (167 + 167) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 167 * (3 : ZMod 306555929) ^ 167 := by rw [pow_add]
          _ = 297425822 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 306555929) ^ 668 = 165617769 := by
        calc
          (3 : ZMod 306555929) ^ 668 = (3 : ZMod 306555929) ^ (334 + 334) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 334 * (3 : ZMod 306555929) ^ 334 := by rw [pow_add]
          _ = 165617769 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 306555929) ^ 1336 = 76741932 := by
        calc
          (3 : ZMod 306555929) ^ 1336 = (3 : ZMod 306555929) ^ (668 + 668) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 668 * (3 : ZMod 306555929) ^ 668 := by rw [pow_add]
          _ = 76741932 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 306555929) ^ 2672 = 3311729 := by
        calc
          (3 : ZMod 306555929) ^ 2672 = (3 : ZMod 306555929) ^ (1336 + 1336) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 1336 * (3 : ZMod 306555929) ^ 1336 := by rw [pow_add]
          _ = 3311729 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 306555929) ^ 5345 = 305604682 := by
        calc
          (3 : ZMod 306555929) ^ 5345 = (3 : ZMod 306555929) ^ (2672 + 2672 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 2672 * (3 : ZMod 306555929) ^ 2672) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 305604682 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 306555929) ^ 10691 = 59813732 := by
        calc
          (3 : ZMod 306555929) ^ 10691 = (3 : ZMod 306555929) ^ (5345 + 5345 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 5345 * (3 : ZMod 306555929) ^ 5345) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 59813732 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 306555929) ^ 21383 = 15818953 := by
        calc
          (3 : ZMod 306555929) ^ 21383 = (3 : ZMod 306555929) ^ (10691 + 10691 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 10691 * (3 : ZMod 306555929) ^ 10691) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 15818953 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 306555929) ^ 42767 = 58306894 := by
        calc
          (3 : ZMod 306555929) ^ 42767 = (3 : ZMod 306555929) ^ (21383 + 21383 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 21383 * (3 : ZMod 306555929) ^ 21383) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 58306894 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 306555929) ^ 85534 = 284442538 := by
        calc
          (3 : ZMod 306555929) ^ 85534 = (3 : ZMod 306555929) ^ (42767 + 42767) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 42767 * (3 : ZMod 306555929) ^ 42767 := by rw [pow_add]
          _ = 284442538 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 306555929) ^ 171069 = 260015096 := by
        calc
          (3 : ZMod 306555929) ^ 171069 = (3 : ZMod 306555929) ^ (85534 + 85534 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 85534 * (3 : ZMod 306555929) ^ 85534) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 260015096 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 306555929) ^ 342138 = 48222494 := by
        calc
          (3 : ZMod 306555929) ^ 342138 = (3 : ZMod 306555929) ^ (171069 + 171069) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 171069 * (3 : ZMod 306555929) ^ 171069 := by rw [pow_add]
          _ = 48222494 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 306555929) ^ 684276 = 111893210 := by
        calc
          (3 : ZMod 306555929) ^ 684276 = (3 : ZMod 306555929) ^ (342138 + 342138) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 342138 * (3 : ZMod 306555929) ^ 342138 := by rw [pow_add]
          _ = 111893210 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 306555929) ^ 1368553 = 299744848 := by
        calc
          (3 : ZMod 306555929) ^ 1368553 = (3 : ZMod 306555929) ^ (684276 + 684276 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 684276 * (3 : ZMod 306555929) ^ 684276) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 299744848 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 306555929) ^ 2737106 = 22208920 := by
        calc
          (3 : ZMod 306555929) ^ 2737106 = (3 : ZMod 306555929) ^ (1368553 + 1368553) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 1368553 * (3 : ZMod 306555929) ^ 1368553 := by rw [pow_add]
          _ = 22208920 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 306555929) ^ 5474213 = 6683609 := by
        calc
          (3 : ZMod 306555929) ^ 5474213 = (3 : ZMod 306555929) ^ (2737106 + 2737106 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 2737106 * (3 : ZMod 306555929) ^ 2737106) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 6683609 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 306555929) ^ 10948426 = 218958788 := by
        calc
          (3 : ZMod 306555929) ^ 10948426 = (3 : ZMod 306555929) ^ (5474213 + 5474213) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 5474213 * (3 : ZMod 306555929) ^ 5474213 := by rw [pow_add]
          _ = 218958788 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 306555929) ^ 21896852 = 201081866 := by
        calc
          (3 : ZMod 306555929) ^ 21896852 = (3 : ZMod 306555929) ^ (10948426 + 10948426) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 10948426 * (3 : ZMod 306555929) ^ 10948426 := by rw [pow_add]
          _ = 201081866 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 306555929) ^ 43793704 = 26262303 := by
        calc
          (3 : ZMod 306555929) ^ 43793704 = (3 : ZMod 306555929) ^ (21896852 + 21896852) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 21896852 * (3 : ZMod 306555929) ^ 21896852 := by rw [pow_add]
          _ = 26262303 := by rw [factor_1_24]; decide
      change (3 : ZMod 306555929) ^ 43793704 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (3 : ZMod 306555929) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 306555929) ^ 3 = 27 := by
        calc
          (3 : ZMod 306555929) ^ 3 = (3 : ZMod 306555929) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 1 * (3 : ZMod 306555929) ^ 1) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 306555929) ^ 7 = 2187 := by
        calc
          (3 : ZMod 306555929) ^ 7 = (3 : ZMod 306555929) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = ((3 : ZMod 306555929) ^ 3 * (3 : ZMod 306555929) ^ 3) * (3 : ZMod 306555929) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 306555929) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 306555929) ^ 14 = (3 : ZMod 306555929) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 7 * (3 : ZMod 306555929) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 306555929) ^ 28 = 56253336 := by
        calc
          (3 : ZMod 306555929) ^ 28 = (3 : ZMod 306555929) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 14 * (3 : ZMod 306555929) ^ 14 := by rw [pow_add]
          _ = 56253336 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 306555929) ^ 56 = 132453662 := by
        calc
          (3 : ZMod 306555929) ^ 56 = (3 : ZMod 306555929) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (3 : ZMod 306555929) ^ n) (by norm_num)
          _ = (3 : ZMod 306555929) ^ 28 * (3 : ZMod 306555929) ^ 28 := by rw [pow_add]
          _ = 132453662 := by rw [factor_2_4]; decide
      change (3 : ZMod 306555929) ^ 56 ≠ 1
      rw [factor_2_5]
      decide

#print axioms prime_lucas_306555929

end TotientTailPeriodKiller
end Erdos249257
