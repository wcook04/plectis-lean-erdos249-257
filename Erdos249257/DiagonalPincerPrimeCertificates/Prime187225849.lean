import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_187225849 : Nat.Prime 187225849 := by
  apply lucas_primality 187225849 (11 : ZMod 187225849)
  ·
      have fermat_0 : (11 : ZMod 187225849) ^ 1 = 11 := by norm_num
      have fermat_1 : (11 : ZMod 187225849) ^ 2 = 121 := by
        calc
          (11 : ZMod 187225849) ^ 2 = (11 : ZMod 187225849) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 1 * (11 : ZMod 187225849) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [fermat_0]; decide
      have fermat_2 : (11 : ZMod 187225849) ^ 5 = 161051 := by
        calc
          (11 : ZMod 187225849) ^ 5 = (11 : ZMod 187225849) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 2 * (11 : ZMod 187225849) ^ 2) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 161051 := by rw [fermat_1]; decide
      have fermat_3 : (11 : ZMod 187225849) ^ 11 = 166702584 := by
        calc
          (11 : ZMod 187225849) ^ 11 = (11 : ZMod 187225849) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 5 * (11 : ZMod 187225849) ^ 5) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 166702584 := by rw [fermat_2]; decide
      have fermat_4 : (11 : ZMod 187225849) ^ 22 = 167054737 := by
        calc
          (11 : ZMod 187225849) ^ 22 = (11 : ZMod 187225849) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 11 * (11 : ZMod 187225849) ^ 11 := by rw [pow_add]
          _ = 167054737 := by rw [fermat_3]; decide
      have fermat_5 : (11 : ZMod 187225849) ^ 44 = 161045214 := by
        calc
          (11 : ZMod 187225849) ^ 44 = (11 : ZMod 187225849) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 22 * (11 : ZMod 187225849) ^ 22 := by rw [pow_add]
          _ = 161045214 := by rw [fermat_4]; decide
      have fermat_6 : (11 : ZMod 187225849) ^ 89 = 29589844 := by
        calc
          (11 : ZMod 187225849) ^ 89 = (11 : ZMod 187225849) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 44 * (11 : ZMod 187225849) ^ 44) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 29589844 := by rw [fermat_5]; decide
      have fermat_7 : (11 : ZMod 187225849) ^ 178 = 180709420 := by
        calc
          (11 : ZMod 187225849) ^ 178 = (11 : ZMod 187225849) ^ (89 + 89) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 89 * (11 : ZMod 187225849) ^ 89 := by rw [pow_add]
          _ = 180709420 := by rw [fermat_6]; decide
      have fermat_8 : (11 : ZMod 187225849) ^ 357 = 34396311 := by
        calc
          (11 : ZMod 187225849) ^ 357 = (11 : ZMod 187225849) ^ (178 + 178 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 178 * (11 : ZMod 187225849) ^ 178) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 34396311 := by rw [fermat_7]; decide
      have fermat_9 : (11 : ZMod 187225849) ^ 714 = 46184710 := by
        calc
          (11 : ZMod 187225849) ^ 714 = (11 : ZMod 187225849) ^ (357 + 357) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 357 * (11 : ZMod 187225849) ^ 357 := by rw [pow_add]
          _ = 46184710 := by rw [fermat_8]; decide
      have fermat_10 : (11 : ZMod 187225849) ^ 1428 = 36393504 := by
        calc
          (11 : ZMod 187225849) ^ 1428 = (11 : ZMod 187225849) ^ (714 + 714) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 714 * (11 : ZMod 187225849) ^ 714 := by rw [pow_add]
          _ = 36393504 := by rw [fermat_9]; decide
      have fermat_11 : (11 : ZMod 187225849) ^ 2856 = 177689390 := by
        calc
          (11 : ZMod 187225849) ^ 2856 = (11 : ZMod 187225849) ^ (1428 + 1428) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 1428 * (11 : ZMod 187225849) ^ 1428 := by rw [pow_add]
          _ = 177689390 := by rw [fermat_10]; decide
      have fermat_12 : (11 : ZMod 187225849) ^ 5713 = 145372087 := by
        calc
          (11 : ZMod 187225849) ^ 5713 = (11 : ZMod 187225849) ^ (2856 + 2856 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 2856 * (11 : ZMod 187225849) ^ 2856) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 145372087 := by rw [fermat_11]; decide
      have fermat_13 : (11 : ZMod 187225849) ^ 11427 = 133909409 := by
        calc
          (11 : ZMod 187225849) ^ 11427 = (11 : ZMod 187225849) ^ (5713 + 5713 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 5713 * (11 : ZMod 187225849) ^ 5713) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 133909409 := by rw [fermat_12]; decide
      have fermat_14 : (11 : ZMod 187225849) ^ 22854 = 10714711 := by
        calc
          (11 : ZMod 187225849) ^ 22854 = (11 : ZMod 187225849) ^ (11427 + 11427) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 11427 * (11 : ZMod 187225849) ^ 11427 := by rw [pow_add]
          _ = 10714711 := by rw [fermat_13]; decide
      have fermat_15 : (11 : ZMod 187225849) ^ 45709 = 148117321 := by
        calc
          (11 : ZMod 187225849) ^ 45709 = (11 : ZMod 187225849) ^ (22854 + 22854 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 22854 * (11 : ZMod 187225849) ^ 22854) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 148117321 := by rw [fermat_14]; decide
      have fermat_16 : (11 : ZMod 187225849) ^ 91418 = 169065038 := by
        calc
          (11 : ZMod 187225849) ^ 91418 = (11 : ZMod 187225849) ^ (45709 + 45709) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 45709 * (11 : ZMod 187225849) ^ 45709 := by rw [pow_add]
          _ = 169065038 := by rw [fermat_15]; decide
      have fermat_17 : (11 : ZMod 187225849) ^ 182837 = 99022713 := by
        calc
          (11 : ZMod 187225849) ^ 182837 = (11 : ZMod 187225849) ^ (91418 + 91418 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 91418 * (11 : ZMod 187225849) ^ 91418) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 99022713 := by rw [fermat_16]; decide
      have fermat_18 : (11 : ZMod 187225849) ^ 365675 = 173538108 := by
        calc
          (11 : ZMod 187225849) ^ 365675 = (11 : ZMod 187225849) ^ (182837 + 182837 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 182837 * (11 : ZMod 187225849) ^ 182837) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 173538108 := by rw [fermat_17]; decide
      have fermat_19 : (11 : ZMod 187225849) ^ 731350 = 154976516 := by
        calc
          (11 : ZMod 187225849) ^ 731350 = (11 : ZMod 187225849) ^ (365675 + 365675) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 365675 * (11 : ZMod 187225849) ^ 365675 := by rw [pow_add]
          _ = 154976516 := by rw [fermat_18]; decide
      have fermat_20 : (11 : ZMod 187225849) ^ 1462701 = 66202297 := by
        calc
          (11 : ZMod 187225849) ^ 1462701 = (11 : ZMod 187225849) ^ (731350 + 731350 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 731350 * (11 : ZMod 187225849) ^ 731350) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 66202297 := by rw [fermat_19]; decide
      have fermat_21 : (11 : ZMod 187225849) ^ 2925403 = 164348534 := by
        calc
          (11 : ZMod 187225849) ^ 2925403 = (11 : ZMod 187225849) ^ (1462701 + 1462701 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 1462701 * (11 : ZMod 187225849) ^ 1462701) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 164348534 := by rw [fermat_20]; decide
      have fermat_22 : (11 : ZMod 187225849) ^ 5850807 = 130266348 := by
        calc
          (11 : ZMod 187225849) ^ 5850807 = (11 : ZMod 187225849) ^ (2925403 + 2925403 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 2925403 * (11 : ZMod 187225849) ^ 2925403) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 130266348 := by rw [fermat_21]; decide
      have fermat_23 : (11 : ZMod 187225849) ^ 11701615 = 160296706 := by
        calc
          (11 : ZMod 187225849) ^ 11701615 = (11 : ZMod 187225849) ^ (5850807 + 5850807 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 5850807 * (11 : ZMod 187225849) ^ 5850807) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 160296706 := by rw [fermat_22]; decide
      have fermat_24 : (11 : ZMod 187225849) ^ 23403231 = 116392304 := by
        calc
          (11 : ZMod 187225849) ^ 23403231 = (11 : ZMod 187225849) ^ (11701615 + 11701615 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 11701615 * (11 : ZMod 187225849) ^ 11701615) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 116392304 := by rw [fermat_23]; decide
      have fermat_25 : (11 : ZMod 187225849) ^ 46806462 = 85803927 := by
        calc
          (11 : ZMod 187225849) ^ 46806462 = (11 : ZMod 187225849) ^ (23403231 + 23403231) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 23403231 * (11 : ZMod 187225849) ^ 23403231 := by rw [pow_add]
          _ = 85803927 := by rw [fermat_24]; decide
      have fermat_26 : (11 : ZMod 187225849) ^ 93612924 = 187225848 := by
        calc
          (11 : ZMod 187225849) ^ 93612924 = (11 : ZMod 187225849) ^ (46806462 + 46806462) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 46806462 * (11 : ZMod 187225849) ^ 46806462 := by rw [pow_add]
          _ = 187225848 := by rw [fermat_25]; decide
      have fermat_27 : (11 : ZMod 187225849) ^ 187225848 = 1 := by
        calc
          (11 : ZMod 187225849) ^ 187225848 = (11 : ZMod 187225849) ^ (93612924 + 93612924) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 93612924 * (11 : ZMod 187225849) ^ 93612924 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (19, 1), (136861, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (19, 1), (136861, 1)] : List FactorBlock).map factorBlockValue).prod = 187225849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (11 : ZMod 187225849) ^ 1 = 11 := by norm_num
      have factor_0_1 : (11 : ZMod 187225849) ^ 2 = 121 := by
        calc
          (11 : ZMod 187225849) ^ 2 = (11 : ZMod 187225849) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 1 * (11 : ZMod 187225849) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_0_0]; decide
      have factor_0_2 : (11 : ZMod 187225849) ^ 5 = 161051 := by
        calc
          (11 : ZMod 187225849) ^ 5 = (11 : ZMod 187225849) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 2 * (11 : ZMod 187225849) ^ 2) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 161051 := by rw [factor_0_1]; decide
      have factor_0_3 : (11 : ZMod 187225849) ^ 11 = 166702584 := by
        calc
          (11 : ZMod 187225849) ^ 11 = (11 : ZMod 187225849) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 5 * (11 : ZMod 187225849) ^ 5) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 166702584 := by rw [factor_0_2]; decide
      have factor_0_4 : (11 : ZMod 187225849) ^ 22 = 167054737 := by
        calc
          (11 : ZMod 187225849) ^ 22 = (11 : ZMod 187225849) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 11 * (11 : ZMod 187225849) ^ 11 := by rw [pow_add]
          _ = 167054737 := by rw [factor_0_3]; decide
      have factor_0_5 : (11 : ZMod 187225849) ^ 44 = 161045214 := by
        calc
          (11 : ZMod 187225849) ^ 44 = (11 : ZMod 187225849) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 22 * (11 : ZMod 187225849) ^ 22 := by rw [pow_add]
          _ = 161045214 := by rw [factor_0_4]; decide
      have factor_0_6 : (11 : ZMod 187225849) ^ 89 = 29589844 := by
        calc
          (11 : ZMod 187225849) ^ 89 = (11 : ZMod 187225849) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 44 * (11 : ZMod 187225849) ^ 44) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 29589844 := by rw [factor_0_5]; decide
      have factor_0_7 : (11 : ZMod 187225849) ^ 178 = 180709420 := by
        calc
          (11 : ZMod 187225849) ^ 178 = (11 : ZMod 187225849) ^ (89 + 89) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 89 * (11 : ZMod 187225849) ^ 89 := by rw [pow_add]
          _ = 180709420 := by rw [factor_0_6]; decide
      have factor_0_8 : (11 : ZMod 187225849) ^ 357 = 34396311 := by
        calc
          (11 : ZMod 187225849) ^ 357 = (11 : ZMod 187225849) ^ (178 + 178 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 178 * (11 : ZMod 187225849) ^ 178) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 34396311 := by rw [factor_0_7]; decide
      have factor_0_9 : (11 : ZMod 187225849) ^ 714 = 46184710 := by
        calc
          (11 : ZMod 187225849) ^ 714 = (11 : ZMod 187225849) ^ (357 + 357) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 357 * (11 : ZMod 187225849) ^ 357 := by rw [pow_add]
          _ = 46184710 := by rw [factor_0_8]; decide
      have factor_0_10 : (11 : ZMod 187225849) ^ 1428 = 36393504 := by
        calc
          (11 : ZMod 187225849) ^ 1428 = (11 : ZMod 187225849) ^ (714 + 714) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 714 * (11 : ZMod 187225849) ^ 714 := by rw [pow_add]
          _ = 36393504 := by rw [factor_0_9]; decide
      have factor_0_11 : (11 : ZMod 187225849) ^ 2856 = 177689390 := by
        calc
          (11 : ZMod 187225849) ^ 2856 = (11 : ZMod 187225849) ^ (1428 + 1428) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 1428 * (11 : ZMod 187225849) ^ 1428 := by rw [pow_add]
          _ = 177689390 := by rw [factor_0_10]; decide
      have factor_0_12 : (11 : ZMod 187225849) ^ 5713 = 145372087 := by
        calc
          (11 : ZMod 187225849) ^ 5713 = (11 : ZMod 187225849) ^ (2856 + 2856 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 2856 * (11 : ZMod 187225849) ^ 2856) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 145372087 := by rw [factor_0_11]; decide
      have factor_0_13 : (11 : ZMod 187225849) ^ 11427 = 133909409 := by
        calc
          (11 : ZMod 187225849) ^ 11427 = (11 : ZMod 187225849) ^ (5713 + 5713 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 5713 * (11 : ZMod 187225849) ^ 5713) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 133909409 := by rw [factor_0_12]; decide
      have factor_0_14 : (11 : ZMod 187225849) ^ 22854 = 10714711 := by
        calc
          (11 : ZMod 187225849) ^ 22854 = (11 : ZMod 187225849) ^ (11427 + 11427) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 11427 * (11 : ZMod 187225849) ^ 11427 := by rw [pow_add]
          _ = 10714711 := by rw [factor_0_13]; decide
      have factor_0_15 : (11 : ZMod 187225849) ^ 45709 = 148117321 := by
        calc
          (11 : ZMod 187225849) ^ 45709 = (11 : ZMod 187225849) ^ (22854 + 22854 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 22854 * (11 : ZMod 187225849) ^ 22854) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 148117321 := by rw [factor_0_14]; decide
      have factor_0_16 : (11 : ZMod 187225849) ^ 91418 = 169065038 := by
        calc
          (11 : ZMod 187225849) ^ 91418 = (11 : ZMod 187225849) ^ (45709 + 45709) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 45709 * (11 : ZMod 187225849) ^ 45709 := by rw [pow_add]
          _ = 169065038 := by rw [factor_0_15]; decide
      have factor_0_17 : (11 : ZMod 187225849) ^ 182837 = 99022713 := by
        calc
          (11 : ZMod 187225849) ^ 182837 = (11 : ZMod 187225849) ^ (91418 + 91418 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 91418 * (11 : ZMod 187225849) ^ 91418) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 99022713 := by rw [factor_0_16]; decide
      have factor_0_18 : (11 : ZMod 187225849) ^ 365675 = 173538108 := by
        calc
          (11 : ZMod 187225849) ^ 365675 = (11 : ZMod 187225849) ^ (182837 + 182837 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 182837 * (11 : ZMod 187225849) ^ 182837) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 173538108 := by rw [factor_0_17]; decide
      have factor_0_19 : (11 : ZMod 187225849) ^ 731350 = 154976516 := by
        calc
          (11 : ZMod 187225849) ^ 731350 = (11 : ZMod 187225849) ^ (365675 + 365675) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 365675 * (11 : ZMod 187225849) ^ 365675 := by rw [pow_add]
          _ = 154976516 := by rw [factor_0_18]; decide
      have factor_0_20 : (11 : ZMod 187225849) ^ 1462701 = 66202297 := by
        calc
          (11 : ZMod 187225849) ^ 1462701 = (11 : ZMod 187225849) ^ (731350 + 731350 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 731350 * (11 : ZMod 187225849) ^ 731350) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 66202297 := by rw [factor_0_19]; decide
      have factor_0_21 : (11 : ZMod 187225849) ^ 2925403 = 164348534 := by
        calc
          (11 : ZMod 187225849) ^ 2925403 = (11 : ZMod 187225849) ^ (1462701 + 1462701 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 1462701 * (11 : ZMod 187225849) ^ 1462701) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 164348534 := by rw [factor_0_20]; decide
      have factor_0_22 : (11 : ZMod 187225849) ^ 5850807 = 130266348 := by
        calc
          (11 : ZMod 187225849) ^ 5850807 = (11 : ZMod 187225849) ^ (2925403 + 2925403 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 2925403 * (11 : ZMod 187225849) ^ 2925403) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 130266348 := by rw [factor_0_21]; decide
      have factor_0_23 : (11 : ZMod 187225849) ^ 11701615 = 160296706 := by
        calc
          (11 : ZMod 187225849) ^ 11701615 = (11 : ZMod 187225849) ^ (5850807 + 5850807 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 5850807 * (11 : ZMod 187225849) ^ 5850807) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 160296706 := by rw [factor_0_22]; decide
      have factor_0_24 : (11 : ZMod 187225849) ^ 23403231 = 116392304 := by
        calc
          (11 : ZMod 187225849) ^ 23403231 = (11 : ZMod 187225849) ^ (11701615 + 11701615 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 11701615 * (11 : ZMod 187225849) ^ 11701615) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 116392304 := by rw [factor_0_23]; decide
      have factor_0_25 : (11 : ZMod 187225849) ^ 46806462 = 85803927 := by
        calc
          (11 : ZMod 187225849) ^ 46806462 = (11 : ZMod 187225849) ^ (23403231 + 23403231) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 23403231 * (11 : ZMod 187225849) ^ 23403231 := by rw [pow_add]
          _ = 85803927 := by rw [factor_0_24]; decide
      have factor_0_26 : (11 : ZMod 187225849) ^ 93612924 = 187225848 := by
        calc
          (11 : ZMod 187225849) ^ 93612924 = (11 : ZMod 187225849) ^ (46806462 + 46806462) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 46806462 * (11 : ZMod 187225849) ^ 46806462 := by rw [pow_add]
          _ = 187225848 := by rw [factor_0_25]; decide
      change (11 : ZMod 187225849) ^ 93612924 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (11 : ZMod 187225849) ^ 1 = 11 := by norm_num
      have factor_1_1 : (11 : ZMod 187225849) ^ 3 = 1331 := by
        calc
          (11 : ZMod 187225849) ^ 3 = (11 : ZMod 187225849) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 1 * (11 : ZMod 187225849) ^ 1) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 1331 := by rw [factor_1_0]; decide
      have factor_1_2 : (11 : ZMod 187225849) ^ 7 = 19487171 := by
        calc
          (11 : ZMod 187225849) ^ 7 = (11 : ZMod 187225849) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 3 * (11 : ZMod 187225849) ^ 3) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 19487171 := by rw [factor_1_1]; decide
      have factor_1_3 : (11 : ZMod 187225849) ^ 14 = 18508239 := by
        calc
          (11 : ZMod 187225849) ^ 14 = (11 : ZMod 187225849) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 7 * (11 : ZMod 187225849) ^ 7 := by rw [pow_add]
          _ = 18508239 := by rw [factor_1_2]; decide
      have factor_1_4 : (11 : ZMod 187225849) ^ 29 = 140009462 := by
        calc
          (11 : ZMod 187225849) ^ 29 = (11 : ZMod 187225849) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 14 * (11 : ZMod 187225849) ^ 14) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 140009462 := by rw [factor_1_3]; decide
      have factor_1_5 : (11 : ZMod 187225849) ^ 59 = 186234038 := by
        calc
          (11 : ZMod 187225849) ^ 59 = (11 : ZMod 187225849) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 29 * (11 : ZMod 187225849) ^ 29) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 186234038 := by rw [factor_1_4]; decide
      have factor_1_6 : (11 : ZMod 187225849) ^ 119 = 48939825 := by
        calc
          (11 : ZMod 187225849) ^ 119 = (11 : ZMod 187225849) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 59 * (11 : ZMod 187225849) ^ 59) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 48939825 := by rw [factor_1_5]; decide
      have factor_1_7 : (11 : ZMod 187225849) ^ 238 = 138983980 := by
        calc
          (11 : ZMod 187225849) ^ 238 = (11 : ZMod 187225849) ^ (119 + 119) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 119 * (11 : ZMod 187225849) ^ 119 := by rw [pow_add]
          _ = 138983980 := by rw [factor_1_6]; decide
      have factor_1_8 : (11 : ZMod 187225849) ^ 476 = 147593934 := by
        calc
          (11 : ZMod 187225849) ^ 476 = (11 : ZMod 187225849) ^ (238 + 238) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 238 * (11 : ZMod 187225849) ^ 238 := by rw [pow_add]
          _ = 147593934 := by rw [factor_1_7]; decide
      have factor_1_9 : (11 : ZMod 187225849) ^ 952 = 113875297 := by
        calc
          (11 : ZMod 187225849) ^ 952 = (11 : ZMod 187225849) ^ (476 + 476) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 476 * (11 : ZMod 187225849) ^ 476 := by rw [pow_add]
          _ = 113875297 := by rw [factor_1_8]; decide
      have factor_1_10 : (11 : ZMod 187225849) ^ 1904 = 59993023 := by
        calc
          (11 : ZMod 187225849) ^ 1904 = (11 : ZMod 187225849) ^ (952 + 952) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 952 * (11 : ZMod 187225849) ^ 952 := by rw [pow_add]
          _ = 59993023 := by rw [factor_1_9]; decide
      have factor_1_11 : (11 : ZMod 187225849) ^ 3809 = 134566087 := by
        calc
          (11 : ZMod 187225849) ^ 3809 = (11 : ZMod 187225849) ^ (1904 + 1904 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 1904 * (11 : ZMod 187225849) ^ 1904) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 134566087 := by rw [factor_1_10]; decide
      have factor_1_12 : (11 : ZMod 187225849) ^ 7618 = 180088602 := by
        calc
          (11 : ZMod 187225849) ^ 7618 = (11 : ZMod 187225849) ^ (3809 + 3809) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 3809 * (11 : ZMod 187225849) ^ 3809 := by rw [pow_add]
          _ = 180088602 := by rw [factor_1_11]; decide
      have factor_1_13 : (11 : ZMod 187225849) ^ 15236 = 72968938 := by
        calc
          (11 : ZMod 187225849) ^ 15236 = (11 : ZMod 187225849) ^ (7618 + 7618) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 7618 * (11 : ZMod 187225849) ^ 7618 := by rw [pow_add]
          _ = 72968938 := by rw [factor_1_12]; decide
      have factor_1_14 : (11 : ZMod 187225849) ^ 30472 = 169664376 := by
        calc
          (11 : ZMod 187225849) ^ 30472 = (11 : ZMod 187225849) ^ (15236 + 15236) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 15236 * (11 : ZMod 187225849) ^ 15236 := by rw [pow_add]
          _ = 169664376 := by rw [factor_1_13]; decide
      have factor_1_15 : (11 : ZMod 187225849) ^ 60945 = 56331525 := by
        calc
          (11 : ZMod 187225849) ^ 60945 = (11 : ZMod 187225849) ^ (30472 + 30472 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 30472 * (11 : ZMod 187225849) ^ 30472) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 56331525 := by rw [factor_1_14]; decide
      have factor_1_16 : (11 : ZMod 187225849) ^ 121891 = 51625425 := by
        calc
          (11 : ZMod 187225849) ^ 121891 = (11 : ZMod 187225849) ^ (60945 + 60945 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 60945 * (11 : ZMod 187225849) ^ 60945) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 51625425 := by rw [factor_1_15]; decide
      have factor_1_17 : (11 : ZMod 187225849) ^ 243783 = 25397617 := by
        calc
          (11 : ZMod 187225849) ^ 243783 = (11 : ZMod 187225849) ^ (121891 + 121891 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 121891 * (11 : ZMod 187225849) ^ 121891) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 25397617 := by rw [factor_1_16]; decide
      have factor_1_18 : (11 : ZMod 187225849) ^ 487567 = 133321675 := by
        calc
          (11 : ZMod 187225849) ^ 487567 = (11 : ZMod 187225849) ^ (243783 + 243783 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 243783 * (11 : ZMod 187225849) ^ 243783) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 133321675 := by rw [factor_1_17]; decide
      have factor_1_19 : (11 : ZMod 187225849) ^ 975134 = 173129420 := by
        calc
          (11 : ZMod 187225849) ^ 975134 = (11 : ZMod 187225849) ^ (487567 + 487567) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 487567 * (11 : ZMod 187225849) ^ 487567 := by rw [pow_add]
          _ = 173129420 := by rw [factor_1_18]; decide
      have factor_1_20 : (11 : ZMod 187225849) ^ 1950269 = 166817433 := by
        calc
          (11 : ZMod 187225849) ^ 1950269 = (11 : ZMod 187225849) ^ (975134 + 975134 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 975134 * (11 : ZMod 187225849) ^ 975134) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 166817433 := by rw [factor_1_19]; decide
      have factor_1_21 : (11 : ZMod 187225849) ^ 3900538 = 71040260 := by
        calc
          (11 : ZMod 187225849) ^ 3900538 = (11 : ZMod 187225849) ^ (1950269 + 1950269) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 1950269 * (11 : ZMod 187225849) ^ 1950269 := by rw [pow_add]
          _ = 71040260 := by rw [factor_1_20]; decide
      have factor_1_22 : (11 : ZMod 187225849) ^ 7801077 = 141490639 := by
        calc
          (11 : ZMod 187225849) ^ 7801077 = (11 : ZMod 187225849) ^ (3900538 + 3900538 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 3900538 * (11 : ZMod 187225849) ^ 3900538) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 141490639 := by rw [factor_1_21]; decide
      have factor_1_23 : (11 : ZMod 187225849) ^ 15602154 = 156065918 := by
        calc
          (11 : ZMod 187225849) ^ 15602154 = (11 : ZMod 187225849) ^ (7801077 + 7801077) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 7801077 * (11 : ZMod 187225849) ^ 7801077 := by rw [pow_add]
          _ = 156065918 := by rw [factor_1_22]; decide
      have factor_1_24 : (11 : ZMod 187225849) ^ 31204308 = 29465097 := by
        calc
          (11 : ZMod 187225849) ^ 31204308 = (11 : ZMod 187225849) ^ (15602154 + 15602154) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 15602154 * (11 : ZMod 187225849) ^ 15602154 := by rw [pow_add]
          _ = 29465097 := by rw [factor_1_23]; decide
      have factor_1_25 : (11 : ZMod 187225849) ^ 62408616 = 29465096 := by
        calc
          (11 : ZMod 187225849) ^ 62408616 = (11 : ZMod 187225849) ^ (31204308 + 31204308) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 31204308 * (11 : ZMod 187225849) ^ 31204308 := by rw [pow_add]
          _ = 29465096 := by rw [factor_1_24]; decide
      change (11 : ZMod 187225849) ^ 62408616 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (11 : ZMod 187225849) ^ 1 = 11 := by norm_num
      have factor_2_1 : (11 : ZMod 187225849) ^ 2 = 121 := by
        calc
          (11 : ZMod 187225849) ^ 2 = (11 : ZMod 187225849) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 1 * (11 : ZMod 187225849) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_2_0]; decide
      have factor_2_2 : (11 : ZMod 187225849) ^ 4 = 14641 := by
        calc
          (11 : ZMod 187225849) ^ 4 = (11 : ZMod 187225849) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 2 * (11 : ZMod 187225849) ^ 2 := by rw [pow_add]
          _ = 14641 := by rw [factor_2_1]; decide
      have factor_2_3 : (11 : ZMod 187225849) ^ 9 = 111237503 := by
        calc
          (11 : ZMod 187225849) ^ 9 = (11 : ZMod 187225849) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 4 * (11 : ZMod 187225849) ^ 4) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 111237503 := by rw [factor_2_2]; decide
      have factor_2_4 : (11 : ZMod 187225849) ^ 18 = 63323696 := by
        calc
          (11 : ZMod 187225849) ^ 18 = (11 : ZMod 187225849) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 9 * (11 : ZMod 187225849) ^ 9 := by rw [pow_add]
          _ = 63323696 := by rw [factor_2_3]; decide
      have factor_2_5 : (11 : ZMod 187225849) ^ 37 = 24652201 := by
        calc
          (11 : ZMod 187225849) ^ 37 = (11 : ZMod 187225849) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 18 * (11 : ZMod 187225849) ^ 18) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 24652201 := by rw [factor_2_4]; decide
      have factor_2_6 : (11 : ZMod 187225849) ^ 75 = 112624020 := by
        calc
          (11 : ZMod 187225849) ^ 75 = (11 : ZMod 187225849) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 37 * (11 : ZMod 187225849) ^ 37) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 112624020 := by rw [factor_2_5]; decide
      have factor_2_7 : (11 : ZMod 187225849) ^ 150 = 177490662 := by
        calc
          (11 : ZMod 187225849) ^ 150 = (11 : ZMod 187225849) ^ (75 + 75) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 75 * (11 : ZMod 187225849) ^ 75 := by rw [pow_add]
          _ = 177490662 := by rw [factor_2_6]; decide
      have factor_2_8 : (11 : ZMod 187225849) ^ 300 = 141161169 := by
        calc
          (11 : ZMod 187225849) ^ 300 = (11 : ZMod 187225849) ^ (150 + 150) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 150 * (11 : ZMod 187225849) ^ 150 := by rw [pow_add]
          _ = 141161169 := by rw [factor_2_7]; decide
      have factor_2_9 : (11 : ZMod 187225849) ^ 601 = 164845096 := by
        calc
          (11 : ZMod 187225849) ^ 601 = (11 : ZMod 187225849) ^ (300 + 300 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 300 * (11 : ZMod 187225849) ^ 300) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 164845096 := by rw [factor_2_8]; decide
      have factor_2_10 : (11 : ZMod 187225849) ^ 1202 = 59659577 := by
        calc
          (11 : ZMod 187225849) ^ 1202 = (11 : ZMod 187225849) ^ (601 + 601) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 601 * (11 : ZMod 187225849) ^ 601 := by rw [pow_add]
          _ = 59659577 := by rw [factor_2_9]; decide
      have factor_2_11 : (11 : ZMod 187225849) ^ 2405 = 72718746 := by
        calc
          (11 : ZMod 187225849) ^ 2405 = (11 : ZMod 187225849) ^ (1202 + 1202 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 1202 * (11 : ZMod 187225849) ^ 1202) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 72718746 := by rw [factor_2_10]; decide
      have factor_2_12 : (11 : ZMod 187225849) ^ 4811 = 6940763 := by
        calc
          (11 : ZMod 187225849) ^ 4811 = (11 : ZMod 187225849) ^ (2405 + 2405 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 2405 * (11 : ZMod 187225849) ^ 2405) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 6940763 := by rw [factor_2_11]; decide
      have factor_2_13 : (11 : ZMod 187225849) ^ 9623 = 108945766 := by
        calc
          (11 : ZMod 187225849) ^ 9623 = (11 : ZMod 187225849) ^ (4811 + 4811 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 4811 * (11 : ZMod 187225849) ^ 4811) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 108945766 := by rw [factor_2_12]; decide
      have factor_2_14 : (11 : ZMod 187225849) ^ 19246 = 40359491 := by
        calc
          (11 : ZMod 187225849) ^ 19246 = (11 : ZMod 187225849) ^ (9623 + 9623) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 9623 * (11 : ZMod 187225849) ^ 9623 := by rw [pow_add]
          _ = 40359491 := by rw [factor_2_13]; decide
      have factor_2_15 : (11 : ZMod 187225849) ^ 38492 = 37022107 := by
        calc
          (11 : ZMod 187225849) ^ 38492 = (11 : ZMod 187225849) ^ (19246 + 19246) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 19246 * (11 : ZMod 187225849) ^ 19246 := by rw [pow_add]
          _ = 37022107 := by rw [factor_2_14]; decide
      have factor_2_16 : (11 : ZMod 187225849) ^ 76984 = 151490813 := by
        calc
          (11 : ZMod 187225849) ^ 76984 = (11 : ZMod 187225849) ^ (38492 + 38492) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 38492 * (11 : ZMod 187225849) ^ 38492 := by rw [pow_add]
          _ = 151490813 := by rw [factor_2_15]; decide
      have factor_2_17 : (11 : ZMod 187225849) ^ 153968 = 172231896 := by
        calc
          (11 : ZMod 187225849) ^ 153968 = (11 : ZMod 187225849) ^ (76984 + 76984) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 76984 * (11 : ZMod 187225849) ^ 76984 := by rw [pow_add]
          _ = 172231896 := by rw [factor_2_16]; decide
      have factor_2_18 : (11 : ZMod 187225849) ^ 307937 = 62865771 := by
        calc
          (11 : ZMod 187225849) ^ 307937 = (11 : ZMod 187225849) ^ (153968 + 153968 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 153968 * (11 : ZMod 187225849) ^ 153968) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 62865771 := by rw [factor_2_17]; decide
      have factor_2_19 : (11 : ZMod 187225849) ^ 615874 = 25538899 := by
        calc
          (11 : ZMod 187225849) ^ 615874 = (11 : ZMod 187225849) ^ (307937 + 307937) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 307937 * (11 : ZMod 187225849) ^ 307937 := by rw [pow_add]
          _ = 25538899 := by rw [factor_2_18]; decide
      have factor_2_20 : (11 : ZMod 187225849) ^ 1231749 = 87946315 := by
        calc
          (11 : ZMod 187225849) ^ 1231749 = (11 : ZMod 187225849) ^ (615874 + 615874 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 615874 * (11 : ZMod 187225849) ^ 615874) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 87946315 := by rw [factor_2_19]; decide
      have factor_2_21 : (11 : ZMod 187225849) ^ 2463498 = 59960434 := by
        calc
          (11 : ZMod 187225849) ^ 2463498 = (11 : ZMod 187225849) ^ (1231749 + 1231749) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 1231749 * (11 : ZMod 187225849) ^ 1231749 := by rw [pow_add]
          _ = 59960434 := by rw [factor_2_20]; decide
      have factor_2_22 : (11 : ZMod 187225849) ^ 4926996 = 39647569 := by
        calc
          (11 : ZMod 187225849) ^ 4926996 = (11 : ZMod 187225849) ^ (2463498 + 2463498) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 2463498 * (11 : ZMod 187225849) ^ 2463498 := by rw [pow_add]
          _ = 39647569 := by rw [factor_2_21]; decide
      have factor_2_23 : (11 : ZMod 187225849) ^ 9853992 = 34764812 := by
        calc
          (11 : ZMod 187225849) ^ 9853992 = (11 : ZMod 187225849) ^ (4926996 + 4926996) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 4926996 * (11 : ZMod 187225849) ^ 4926996 := by rw [pow_add]
          _ = 34764812 := by rw [factor_2_22]; decide
      change (11 : ZMod 187225849) ^ 9853992 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (11 : ZMod 187225849) ^ 1 = 11 := by norm_num
      have factor_3_1 : (11 : ZMod 187225849) ^ 2 = 121 := by
        calc
          (11 : ZMod 187225849) ^ 2 = (11 : ZMod 187225849) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 1 * (11 : ZMod 187225849) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_3_0]; decide
      have factor_3_2 : (11 : ZMod 187225849) ^ 5 = 161051 := by
        calc
          (11 : ZMod 187225849) ^ 5 = (11 : ZMod 187225849) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 2 * (11 : ZMod 187225849) ^ 2) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 161051 := by rw [factor_3_1]; decide
      have factor_3_3 : (11 : ZMod 187225849) ^ 10 = 100257439 := by
        calc
          (11 : ZMod 187225849) ^ 10 = (11 : ZMod 187225849) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 5 * (11 : ZMod 187225849) ^ 5 := by rw [pow_add]
          _ = 100257439 := by rw [factor_3_2]; decide
      have factor_3_4 : (11 : ZMod 187225849) ^ 21 = 32207326 := by
        calc
          (11 : ZMod 187225849) ^ 21 = (11 : ZMod 187225849) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 10 * (11 : ZMod 187225849) ^ 10) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 32207326 := by rw [factor_3_3]; decide
      have factor_3_5 : (11 : ZMod 187225849) ^ 42 = 137495206 := by
        calc
          (11 : ZMod 187225849) ^ 42 = (11 : ZMod 187225849) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 21 * (11 : ZMod 187225849) ^ 21 := by rw [pow_add]
          _ = 137495206 := by rw [factor_3_4]; decide
      have factor_3_6 : (11 : ZMod 187225849) ^ 85 = 138455287 := by
        calc
          (11 : ZMod 187225849) ^ 85 = (11 : ZMod 187225849) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 42 * (11 : ZMod 187225849) ^ 42) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 138455287 := by rw [factor_3_5]; decide
      have factor_3_7 : (11 : ZMod 187225849) ^ 171 = 166778452 := by
        calc
          (11 : ZMod 187225849) ^ 171 = (11 : ZMod 187225849) ^ (85 + 85 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = ((11 : ZMod 187225849) ^ 85 * (11 : ZMod 187225849) ^ 85) * (11 : ZMod 187225849) := by rw [pow_succ, pow_add]
          _ = 166778452 := by rw [factor_3_6]; decide
      have factor_3_8 : (11 : ZMod 187225849) ^ 342 = 128415219 := by
        calc
          (11 : ZMod 187225849) ^ 342 = (11 : ZMod 187225849) ^ (171 + 171) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 171 * (11 : ZMod 187225849) ^ 171 := by rw [pow_add]
          _ = 128415219 := by rw [factor_3_7]; decide
      have factor_3_9 : (11 : ZMod 187225849) ^ 684 = 65565958 := by
        calc
          (11 : ZMod 187225849) ^ 684 = (11 : ZMod 187225849) ^ (342 + 342) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 342 * (11 : ZMod 187225849) ^ 342 := by rw [pow_add]
          _ = 65565958 := by rw [factor_3_8]; decide
      have factor_3_10 : (11 : ZMod 187225849) ^ 1368 = 70084425 := by
        calc
          (11 : ZMod 187225849) ^ 1368 = (11 : ZMod 187225849) ^ (684 + 684) :=
            congrArg (fun n : ℕ => (11 : ZMod 187225849) ^ n) (by norm_num)
          _ = (11 : ZMod 187225849) ^ 684 * (11 : ZMod 187225849) ^ 684 := by rw [pow_add]
          _ = 70084425 := by rw [factor_3_9]; decide
      change (11 : ZMod 187225849) ^ 1368 ≠ 1
      rw [factor_3_10]
      decide

#print axioms prime_lucas_187225849

end TotientTailPeriodKiller
end Erdos249257
