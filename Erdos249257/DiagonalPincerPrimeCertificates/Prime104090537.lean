import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_104090537 : Nat.Prime 104090537 := by
  apply lucas_primality 104090537 (3 : ZMod 104090537)
  ·
      have fermat_0 : (3 : ZMod 104090537) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 104090537) ^ 3 = 27 := by
        calc
          (3 : ZMod 104090537) ^ 3 = (3 : ZMod 104090537) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 1 * (3 : ZMod 104090537) ^ 1) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 104090537) ^ 6 = 729 := by
        calc
          (3 : ZMod 104090537) ^ 6 = (3 : ZMod 104090537) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 3 * (3 : ZMod 104090537) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 104090537) ^ 12 = 531441 := by
        calc
          (3 : ZMod 104090537) ^ 12 = (3 : ZMod 104090537) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 6 * (3 : ZMod 104090537) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 104090537) ^ 24 = 31909600 := by
        calc
          (3 : ZMod 104090537) ^ 24 = (3 : ZMod 104090537) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 12 * (3 : ZMod 104090537) ^ 12 := by rw [pow_add]
          _ = 31909600 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 104090537) ^ 49 = 66409991 := by
        calc
          (3 : ZMod 104090537) ^ 49 = (3 : ZMod 104090537) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 24 * (3 : ZMod 104090537) ^ 24) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 66409991 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 104090537) ^ 99 = 95931860 := by
        calc
          (3 : ZMod 104090537) ^ 99 = (3 : ZMod 104090537) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 49 * (3 : ZMod 104090537) ^ 49) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 95931860 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 104090537) ^ 198 = 89699032 := by
        calc
          (3 : ZMod 104090537) ^ 198 = (3 : ZMod 104090537) ^ (99 + 99) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 99 * (3 : ZMod 104090537) ^ 99 := by rw [pow_add]
          _ = 89699032 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 104090537) ^ 397 = 63248493 := by
        calc
          (3 : ZMod 104090537) ^ 397 = (3 : ZMod 104090537) ^ (198 + 198 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 198 * (3 : ZMod 104090537) ^ 198) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 63248493 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 104090537) ^ 794 = 51841240 := by
        calc
          (3 : ZMod 104090537) ^ 794 = (3 : ZMod 104090537) ^ (397 + 397) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 397 * (3 : ZMod 104090537) ^ 397 := by rw [pow_add]
          _ = 51841240 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 104090537) ^ 1588 = 69481915 := by
        calc
          (3 : ZMod 104090537) ^ 1588 = (3 : ZMod 104090537) ^ (794 + 794) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 794 * (3 : ZMod 104090537) ^ 794 := by rw [pow_add]
          _ = 69481915 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 104090537) ^ 3176 = 22887546 := by
        calc
          (3 : ZMod 104090537) ^ 3176 = (3 : ZMod 104090537) ^ (1588 + 1588) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 1588 * (3 : ZMod 104090537) ^ 1588 := by rw [pow_add]
          _ = 22887546 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 104090537) ^ 6353 = 16574945 := by
        calc
          (3 : ZMod 104090537) ^ 6353 = (3 : ZMod 104090537) ^ (3176 + 3176 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 3176 * (3 : ZMod 104090537) ^ 3176) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 16574945 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 104090537) ^ 12706 = 45185500 := by
        calc
          (3 : ZMod 104090537) ^ 12706 = (3 : ZMod 104090537) ^ (6353 + 6353) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 6353 * (3 : ZMod 104090537) ^ 6353 := by rw [pow_add]
          _ = 45185500 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 104090537) ^ 25412 = 84698831 := by
        calc
          (3 : ZMod 104090537) ^ 25412 = (3 : ZMod 104090537) ^ (12706 + 12706) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 12706 * (3 : ZMod 104090537) ^ 12706 := by rw [pow_add]
          _ = 84698831 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 104090537) ^ 50825 = 72880894 := by
        calc
          (3 : ZMod 104090537) ^ 50825 = (3 : ZMod 104090537) ^ (25412 + 25412 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 25412 * (3 : ZMod 104090537) ^ 25412) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 72880894 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 104090537) ^ 101650 = 43534769 := by
        calc
          (3 : ZMod 104090537) ^ 101650 = (3 : ZMod 104090537) ^ (50825 + 50825) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 50825 * (3 : ZMod 104090537) ^ 50825 := by rw [pow_add]
          _ = 43534769 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 104090537) ^ 203301 = 62060282 := by
        calc
          (3 : ZMod 104090537) ^ 203301 = (3 : ZMod 104090537) ^ (101650 + 101650 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 101650 * (3 : ZMod 104090537) ^ 101650) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 62060282 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 104090537) ^ 406603 = 22866302 := by
        calc
          (3 : ZMod 104090537) ^ 406603 = (3 : ZMod 104090537) ^ (203301 + 203301 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 203301 * (3 : ZMod 104090537) ^ 203301) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 22866302 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 104090537) ^ 813207 = 24637727 := by
        calc
          (3 : ZMod 104090537) ^ 813207 = (3 : ZMod 104090537) ^ (406603 + 406603 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 406603 * (3 : ZMod 104090537) ^ 406603) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 24637727 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 104090537) ^ 1626414 = 93441219 := by
        calc
          (3 : ZMod 104090537) ^ 1626414 = (3 : ZMod 104090537) ^ (813207 + 813207) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 813207 * (3 : ZMod 104090537) ^ 813207 := by rw [pow_add]
          _ = 93441219 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 104090537) ^ 3252829 = 45970466 := by
        calc
          (3 : ZMod 104090537) ^ 3252829 = (3 : ZMod 104090537) ^ (1626414 + 1626414 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 1626414 * (3 : ZMod 104090537) ^ 1626414) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 45970466 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 104090537) ^ 6505658 = 85399299 := by
        calc
          (3 : ZMod 104090537) ^ 6505658 = (3 : ZMod 104090537) ^ (3252829 + 3252829) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 3252829 * (3 : ZMod 104090537) ^ 3252829 := by rw [pow_add]
          _ = 85399299 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 104090537) ^ 13011317 = 37317617 := by
        calc
          (3 : ZMod 104090537) ^ 13011317 = (3 : ZMod 104090537) ^ (6505658 + 6505658 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 6505658 * (3 : ZMod 104090537) ^ 6505658) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 37317617 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 104090537) ^ 26022634 = 39863292 := by
        calc
          (3 : ZMod 104090537) ^ 26022634 = (3 : ZMod 104090537) ^ (13011317 + 13011317) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 13011317 * (3 : ZMod 104090537) ^ 13011317 := by rw [pow_add]
          _ = 39863292 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 104090537) ^ 52045268 = 104090536 := by
        calc
          (3 : ZMod 104090537) ^ 52045268 = (3 : ZMod 104090537) ^ (26022634 + 26022634) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 26022634 * (3 : ZMod 104090537) ^ 26022634 := by rw [pow_add]
          _ = 104090536 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 104090537) ^ 104090536 = 1 := by
        calc
          (3 : ZMod 104090537) ^ 104090536 = (3 : ZMod 104090537) ^ (52045268 + 52045268) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 52045268 * (3 : ZMod 104090537) ^ 52045268 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (1182847, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (1182847, 1)] : List FactorBlock).map factorBlockValue).prod = 104090537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 104090537) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 104090537) ^ 3 = 27 := by
        calc
          (3 : ZMod 104090537) ^ 3 = (3 : ZMod 104090537) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 1 * (3 : ZMod 104090537) ^ 1) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 104090537) ^ 6 = 729 := by
        calc
          (3 : ZMod 104090537) ^ 6 = (3 : ZMod 104090537) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 3 * (3 : ZMod 104090537) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 104090537) ^ 12 = 531441 := by
        calc
          (3 : ZMod 104090537) ^ 12 = (3 : ZMod 104090537) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 6 * (3 : ZMod 104090537) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 104090537) ^ 24 = 31909600 := by
        calc
          (3 : ZMod 104090537) ^ 24 = (3 : ZMod 104090537) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 12 * (3 : ZMod 104090537) ^ 12 := by rw [pow_add]
          _ = 31909600 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 104090537) ^ 49 = 66409991 := by
        calc
          (3 : ZMod 104090537) ^ 49 = (3 : ZMod 104090537) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 24 * (3 : ZMod 104090537) ^ 24) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 66409991 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 104090537) ^ 99 = 95931860 := by
        calc
          (3 : ZMod 104090537) ^ 99 = (3 : ZMod 104090537) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 49 * (3 : ZMod 104090537) ^ 49) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 95931860 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 104090537) ^ 198 = 89699032 := by
        calc
          (3 : ZMod 104090537) ^ 198 = (3 : ZMod 104090537) ^ (99 + 99) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 99 * (3 : ZMod 104090537) ^ 99 := by rw [pow_add]
          _ = 89699032 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 104090537) ^ 397 = 63248493 := by
        calc
          (3 : ZMod 104090537) ^ 397 = (3 : ZMod 104090537) ^ (198 + 198 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 198 * (3 : ZMod 104090537) ^ 198) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 63248493 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 104090537) ^ 794 = 51841240 := by
        calc
          (3 : ZMod 104090537) ^ 794 = (3 : ZMod 104090537) ^ (397 + 397) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 397 * (3 : ZMod 104090537) ^ 397 := by rw [pow_add]
          _ = 51841240 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 104090537) ^ 1588 = 69481915 := by
        calc
          (3 : ZMod 104090537) ^ 1588 = (3 : ZMod 104090537) ^ (794 + 794) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 794 * (3 : ZMod 104090537) ^ 794 := by rw [pow_add]
          _ = 69481915 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 104090537) ^ 3176 = 22887546 := by
        calc
          (3 : ZMod 104090537) ^ 3176 = (3 : ZMod 104090537) ^ (1588 + 1588) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 1588 * (3 : ZMod 104090537) ^ 1588 := by rw [pow_add]
          _ = 22887546 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 104090537) ^ 6353 = 16574945 := by
        calc
          (3 : ZMod 104090537) ^ 6353 = (3 : ZMod 104090537) ^ (3176 + 3176 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 3176 * (3 : ZMod 104090537) ^ 3176) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 16574945 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 104090537) ^ 12706 = 45185500 := by
        calc
          (3 : ZMod 104090537) ^ 12706 = (3 : ZMod 104090537) ^ (6353 + 6353) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 6353 * (3 : ZMod 104090537) ^ 6353 := by rw [pow_add]
          _ = 45185500 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 104090537) ^ 25412 = 84698831 := by
        calc
          (3 : ZMod 104090537) ^ 25412 = (3 : ZMod 104090537) ^ (12706 + 12706) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 12706 * (3 : ZMod 104090537) ^ 12706 := by rw [pow_add]
          _ = 84698831 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 104090537) ^ 50825 = 72880894 := by
        calc
          (3 : ZMod 104090537) ^ 50825 = (3 : ZMod 104090537) ^ (25412 + 25412 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 25412 * (3 : ZMod 104090537) ^ 25412) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 72880894 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 104090537) ^ 101650 = 43534769 := by
        calc
          (3 : ZMod 104090537) ^ 101650 = (3 : ZMod 104090537) ^ (50825 + 50825) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 50825 * (3 : ZMod 104090537) ^ 50825 := by rw [pow_add]
          _ = 43534769 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 104090537) ^ 203301 = 62060282 := by
        calc
          (3 : ZMod 104090537) ^ 203301 = (3 : ZMod 104090537) ^ (101650 + 101650 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 101650 * (3 : ZMod 104090537) ^ 101650) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 62060282 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 104090537) ^ 406603 = 22866302 := by
        calc
          (3 : ZMod 104090537) ^ 406603 = (3 : ZMod 104090537) ^ (203301 + 203301 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 203301 * (3 : ZMod 104090537) ^ 203301) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 22866302 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 104090537) ^ 813207 = 24637727 := by
        calc
          (3 : ZMod 104090537) ^ 813207 = (3 : ZMod 104090537) ^ (406603 + 406603 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 406603 * (3 : ZMod 104090537) ^ 406603) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 24637727 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 104090537) ^ 1626414 = 93441219 := by
        calc
          (3 : ZMod 104090537) ^ 1626414 = (3 : ZMod 104090537) ^ (813207 + 813207) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 813207 * (3 : ZMod 104090537) ^ 813207 := by rw [pow_add]
          _ = 93441219 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 104090537) ^ 3252829 = 45970466 := by
        calc
          (3 : ZMod 104090537) ^ 3252829 = (3 : ZMod 104090537) ^ (1626414 + 1626414 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 1626414 * (3 : ZMod 104090537) ^ 1626414) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 45970466 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 104090537) ^ 6505658 = 85399299 := by
        calc
          (3 : ZMod 104090537) ^ 6505658 = (3 : ZMod 104090537) ^ (3252829 + 3252829) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 3252829 * (3 : ZMod 104090537) ^ 3252829 := by rw [pow_add]
          _ = 85399299 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 104090537) ^ 13011317 = 37317617 := by
        calc
          (3 : ZMod 104090537) ^ 13011317 = (3 : ZMod 104090537) ^ (6505658 + 6505658 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 6505658 * (3 : ZMod 104090537) ^ 6505658) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 37317617 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 104090537) ^ 26022634 = 39863292 := by
        calc
          (3 : ZMod 104090537) ^ 26022634 = (3 : ZMod 104090537) ^ (13011317 + 13011317) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 13011317 * (3 : ZMod 104090537) ^ 13011317 := by rw [pow_add]
          _ = 39863292 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 104090537) ^ 52045268 = 104090536 := by
        calc
          (3 : ZMod 104090537) ^ 52045268 = (3 : ZMod 104090537) ^ (26022634 + 26022634) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 26022634 * (3 : ZMod 104090537) ^ 26022634 := by rw [pow_add]
          _ = 104090536 := by rw [factor_0_24]; decide
      change (3 : ZMod 104090537) ^ 52045268 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (3 : ZMod 104090537) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 104090537) ^ 2 = 9 := by
        calc
          (3 : ZMod 104090537) ^ 2 = (3 : ZMod 104090537) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 1 * (3 : ZMod 104090537) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 104090537) ^ 4 = 81 := by
        calc
          (3 : ZMod 104090537) ^ 4 = (3 : ZMod 104090537) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 2 * (3 : ZMod 104090537) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 104090537) ^ 9 = 19683 := by
        calc
          (3 : ZMod 104090537) ^ 9 = (3 : ZMod 104090537) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 4 * (3 : ZMod 104090537) ^ 4) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 104090537) ^ 18 = 75148878 := by
        calc
          (3 : ZMod 104090537) ^ 18 = (3 : ZMod 104090537) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 9 * (3 : ZMod 104090537) ^ 9 := by rw [pow_add]
          _ = 75148878 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 104090537) ^ 36 = 55807708 := by
        calc
          (3 : ZMod 104090537) ^ 36 = (3 : ZMod 104090537) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 18 * (3 : ZMod 104090537) ^ 18 := by rw [pow_add]
          _ = 55807708 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 104090537) ^ 72 = 28298674 := by
        calc
          (3 : ZMod 104090537) ^ 72 = (3 : ZMod 104090537) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 36 * (3 : ZMod 104090537) ^ 36 := by rw [pow_add]
          _ = 28298674 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 104090537) ^ 144 = 24637774 := by
        calc
          (3 : ZMod 104090537) ^ 144 = (3 : ZMod 104090537) ^ (72 + 72) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 72 * (3 : ZMod 104090537) ^ 72 := by rw [pow_add]
          _ = 24637774 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 104090537) ^ 288 = 15307415 := by
        calc
          (3 : ZMod 104090537) ^ 288 = (3 : ZMod 104090537) ^ (144 + 144) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 144 * (3 : ZMod 104090537) ^ 144 := by rw [pow_add]
          _ = 15307415 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 104090537) ^ 577 = 89774444 := by
        calc
          (3 : ZMod 104090537) ^ 577 = (3 : ZMod 104090537) ^ (288 + 288 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 288 * (3 : ZMod 104090537) ^ 288) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 89774444 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 104090537) ^ 1155 = 100163480 := by
        calc
          (3 : ZMod 104090537) ^ 1155 = (3 : ZMod 104090537) ^ (577 + 577 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 577 * (3 : ZMod 104090537) ^ 577) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 100163480 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 104090537) ^ 2310 = 34990940 := by
        calc
          (3 : ZMod 104090537) ^ 2310 = (3 : ZMod 104090537) ^ (1155 + 1155) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 1155 * (3 : ZMod 104090537) ^ 1155 := by rw [pow_add]
          _ = 34990940 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 104090537) ^ 4620 = 3806267 := by
        calc
          (3 : ZMod 104090537) ^ 4620 = (3 : ZMod 104090537) ^ (2310 + 2310) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 2310 * (3 : ZMod 104090537) ^ 2310 := by rw [pow_add]
          _ = 3806267 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 104090537) ^ 9240 = 35264018 := by
        calc
          (3 : ZMod 104090537) ^ 9240 = (3 : ZMod 104090537) ^ (4620 + 4620) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 4620 * (3 : ZMod 104090537) ^ 4620 := by rw [pow_add]
          _ = 35264018 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 104090537) ^ 18481 = 64695415 := by
        calc
          (3 : ZMod 104090537) ^ 18481 = (3 : ZMod 104090537) ^ (9240 + 9240 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 9240 * (3 : ZMod 104090537) ^ 9240) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 64695415 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 104090537) ^ 36963 = 77475896 := by
        calc
          (3 : ZMod 104090537) ^ 36963 = (3 : ZMod 104090537) ^ (18481 + 18481 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 18481 * (3 : ZMod 104090537) ^ 18481) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 77475896 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 104090537) ^ 73927 = 82035461 := by
        calc
          (3 : ZMod 104090537) ^ 73927 = (3 : ZMod 104090537) ^ (36963 + 36963 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 36963 * (3 : ZMod 104090537) ^ 36963) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 82035461 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 104090537) ^ 147855 = 64469803 := by
        calc
          (3 : ZMod 104090537) ^ 147855 = (3 : ZMod 104090537) ^ (73927 + 73927 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 73927 * (3 : ZMod 104090537) ^ 73927) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 64469803 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 104090537) ^ 295711 = 72291745 := by
        calc
          (3 : ZMod 104090537) ^ 295711 = (3 : ZMod 104090537) ^ (147855 + 147855 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 147855 * (3 : ZMod 104090537) ^ 147855) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 72291745 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 104090537) ^ 591423 = 24475266 := by
        calc
          (3 : ZMod 104090537) ^ 591423 = (3 : ZMod 104090537) ^ (295711 + 295711 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 295711 * (3 : ZMod 104090537) ^ 295711) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 24475266 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 104090537) ^ 1182847 = 102344858 := by
        calc
          (3 : ZMod 104090537) ^ 1182847 = (3 : ZMod 104090537) ^ (591423 + 591423 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 591423 * (3 : ZMod 104090537) ^ 591423) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 102344858 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 104090537) ^ 2365694 = 40609829 := by
        calc
          (3 : ZMod 104090537) ^ 2365694 = (3 : ZMod 104090537) ^ (1182847 + 1182847) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 1182847 * (3 : ZMod 104090537) ^ 1182847 := by rw [pow_add]
          _ = 40609829 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 104090537) ^ 4731388 = 100721352 := by
        calc
          (3 : ZMod 104090537) ^ 4731388 = (3 : ZMod 104090537) ^ (2365694 + 2365694) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 2365694 * (3 : ZMod 104090537) ^ 2365694 := by rw [pow_add]
          _ = 100721352 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 104090537) ^ 9462776 = 22232764 := by
        calc
          (3 : ZMod 104090537) ^ 9462776 = (3 : ZMod 104090537) ^ (4731388 + 4731388) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 4731388 * (3 : ZMod 104090537) ^ 4731388 := by rw [pow_add]
          _ = 22232764 := by rw [factor_1_22]; decide
      change (3 : ZMod 104090537) ^ 9462776 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (3 : ZMod 104090537) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 104090537) ^ 2 = 9 := by
        calc
          (3 : ZMod 104090537) ^ 2 = (3 : ZMod 104090537) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 1 * (3 : ZMod 104090537) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 104090537) ^ 5 = 243 := by
        calc
          (3 : ZMod 104090537) ^ 5 = (3 : ZMod 104090537) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 2 * (3 : ZMod 104090537) ^ 2) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 104090537) ^ 11 = 177147 := by
        calc
          (3 : ZMod 104090537) ^ 11 = (3 : ZMod 104090537) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = ((3 : ZMod 104090537) ^ 5 * (3 : ZMod 104090537) ^ 5) * (3 : ZMod 104090537) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 104090537) ^ 22 = 49807972 := by
        calc
          (3 : ZMod 104090537) ^ 22 = (3 : ZMod 104090537) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 11 * (3 : ZMod 104090537) ^ 11 := by rw [pow_add]
          _ = 49807972 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 104090537) ^ 44 = 67953559 := by
        calc
          (3 : ZMod 104090537) ^ 44 = (3 : ZMod 104090537) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 22 * (3 : ZMod 104090537) ^ 22 := by rw [pow_add]
          _ = 67953559 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 104090537) ^ 88 = 23450248 := by
        calc
          (3 : ZMod 104090537) ^ 88 = (3 : ZMod 104090537) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (3 : ZMod 104090537) ^ n) (by norm_num)
          _ = (3 : ZMod 104090537) ^ 44 * (3 : ZMod 104090537) ^ 44 := by rw [pow_add]
          _ = 23450248 := by rw [factor_2_5]; decide
      change (3 : ZMod 104090537) ^ 88 ≠ 1
      rw [factor_2_6]
      decide

#print axioms prime_lucas_104090537

end TotientTailPeriodKiller
end Erdos249257
