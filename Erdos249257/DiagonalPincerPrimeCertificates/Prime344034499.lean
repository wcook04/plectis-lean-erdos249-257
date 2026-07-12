import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime57339083

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_344034499 : Nat.Prime 344034499 := by
  apply lucas_primality 344034499 (2 : ZMod 344034499)
  ·
      have fermat_0 : (2 : ZMod 344034499) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 344034499) ^ 2 = 4 := by
        calc
          (2 : ZMod 344034499) ^ 2 = (2 : ZMod 344034499) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 1 * (2 : ZMod 344034499) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 344034499) ^ 5 = 32 := by
        calc
          (2 : ZMod 344034499) ^ 5 = (2 : ZMod 344034499) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 2 * (2 : ZMod 344034499) ^ 2) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 344034499) ^ 10 = 1024 := by
        calc
          (2 : ZMod 344034499) ^ 10 = (2 : ZMod 344034499) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 5 * (2 : ZMod 344034499) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 344034499) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 344034499) ^ 20 = (2 : ZMod 344034499) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 10 * (2 : ZMod 344034499) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 344034499) ^ 41 = 298772443 := by
        calc
          (2 : ZMod 344034499) ^ 41 = (2 : ZMod 344034499) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 20 * (2 : ZMod 344034499) ^ 20) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 298772443 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 344034499) ^ 82 = 175012427 := by
        calc
          (2 : ZMod 344034499) ^ 82 = (2 : ZMod 344034499) ^ (41 + 41) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 41 * (2 : ZMod 344034499) ^ 41 := by rw [pow_add]
          _ = 175012427 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 344034499) ^ 164 = 130669207 := by
        calc
          (2 : ZMod 344034499) ^ 164 = (2 : ZMod 344034499) ^ (82 + 82) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 82 * (2 : ZMod 344034499) ^ 82 := by rw [pow_add]
          _ = 130669207 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 344034499) ^ 328 = 183707376 := by
        calc
          (2 : ZMod 344034499) ^ 328 = (2 : ZMod 344034499) ^ (164 + 164) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 164 * (2 : ZMod 344034499) ^ 164 := by rw [pow_add]
          _ = 183707376 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 344034499) ^ 656 = 39729352 := by
        calc
          (2 : ZMod 344034499) ^ 656 = (2 : ZMod 344034499) ^ (328 + 328) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 328 * (2 : ZMod 344034499) ^ 328 := by rw [pow_add]
          _ = 39729352 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 344034499) ^ 1312 = 73824878 := by
        calc
          (2 : ZMod 344034499) ^ 1312 = (2 : ZMod 344034499) ^ (656 + 656) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 656 * (2 : ZMod 344034499) ^ 656 := by rw [pow_add]
          _ = 73824878 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 344034499) ^ 2624 = 302802145 := by
        calc
          (2 : ZMod 344034499) ^ 2624 = (2 : ZMod 344034499) ^ (1312 + 1312) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 1312 * (2 : ZMod 344034499) ^ 1312 := by rw [pow_add]
          _ = 302802145 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 344034499) ^ 5249 = 323036483 := by
        calc
          (2 : ZMod 344034499) ^ 5249 = (2 : ZMod 344034499) ^ (2624 + 2624 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 2624 * (2 : ZMod 344034499) ^ 2624) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 323036483 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 344034499) ^ 10499 = 339656223 := by
        calc
          (2 : ZMod 344034499) ^ 10499 = (2 : ZMod 344034499) ^ (5249 + 5249 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 5249 * (2 : ZMod 344034499) ^ 5249) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 339656223 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 344034499) ^ 20998 = 42482395 := by
        calc
          (2 : ZMod 344034499) ^ 20998 = (2 : ZMod 344034499) ^ (10499 + 10499) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 10499 * (2 : ZMod 344034499) ^ 10499 := by rw [pow_add]
          _ = 42482395 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 344034499) ^ 41996 = 164322376 := by
        calc
          (2 : ZMod 344034499) ^ 41996 = (2 : ZMod 344034499) ^ (20998 + 20998) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 20998 * (2 : ZMod 344034499) ^ 20998 := by rw [pow_add]
          _ = 164322376 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 344034499) ^ 83992 = 74635735 := by
        calc
          (2 : ZMod 344034499) ^ 83992 = (2 : ZMod 344034499) ^ (41996 + 41996) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 41996 * (2 : ZMod 344034499) ^ 41996 := by rw [pow_add]
          _ = 74635735 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 344034499) ^ 167985 = 69168289 := by
        calc
          (2 : ZMod 344034499) ^ 167985 = (2 : ZMod 344034499) ^ (83992 + 83992 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 83992 * (2 : ZMod 344034499) ^ 83992) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 69168289 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 344034499) ^ 335971 = 178452672 := by
        calc
          (2 : ZMod 344034499) ^ 335971 = (2 : ZMod 344034499) ^ (167985 + 167985 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 167985 * (2 : ZMod 344034499) ^ 167985) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 178452672 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 344034499) ^ 671942 = 219807010 := by
        calc
          (2 : ZMod 344034499) ^ 671942 = (2 : ZMod 344034499) ^ (335971 + 335971) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 335971 * (2 : ZMod 344034499) ^ 335971 := by rw [pow_add]
          _ = 219807010 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 344034499) ^ 1343884 = 314251950 := by
        calc
          (2 : ZMod 344034499) ^ 1343884 = (2 : ZMod 344034499) ^ (671942 + 671942) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 671942 * (2 : ZMod 344034499) ^ 671942 := by rw [pow_add]
          _ = 314251950 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 344034499) ^ 2687769 = 317161262 := by
        calc
          (2 : ZMod 344034499) ^ 2687769 = (2 : ZMod 344034499) ^ (1343884 + 1343884 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 1343884 * (2 : ZMod 344034499) ^ 1343884) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 317161262 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 344034499) ^ 5375539 = 274427584 := by
        calc
          (2 : ZMod 344034499) ^ 5375539 = (2 : ZMod 344034499) ^ (2687769 + 2687769 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 2687769 * (2 : ZMod 344034499) ^ 2687769) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 274427584 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 344034499) ^ 10751078 = 133913471 := by
        calc
          (2 : ZMod 344034499) ^ 10751078 = (2 : ZMod 344034499) ^ (5375539 + 5375539) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 5375539 * (2 : ZMod 344034499) ^ 5375539 := by rw [pow_add]
          _ = 133913471 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 344034499) ^ 21502156 = 188960897 := by
        calc
          (2 : ZMod 344034499) ^ 21502156 = (2 : ZMod 344034499) ^ (10751078 + 10751078) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 10751078 * (2 : ZMod 344034499) ^ 10751078 := by rw [pow_add]
          _ = 188960897 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 344034499) ^ 43004312 = 120163353 := by
        calc
          (2 : ZMod 344034499) ^ 43004312 = (2 : ZMod 344034499) ^ (21502156 + 21502156) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 21502156 * (2 : ZMod 344034499) ^ 21502156 := by rw [pow_add]
          _ = 120163353 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 344034499) ^ 86008624 = 270822909 := by
        calc
          (2 : ZMod 344034499) ^ 86008624 = (2 : ZMod 344034499) ^ (43004312 + 43004312) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 43004312 * (2 : ZMod 344034499) ^ 43004312 := by rw [pow_add]
          _ = 270822909 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 344034499) ^ 172017249 = 344034498 := by
        calc
          (2 : ZMod 344034499) ^ 172017249 = (2 : ZMod 344034499) ^ (86008624 + 86008624 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 86008624 * (2 : ZMod 344034499) ^ 86008624) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 344034498 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 344034499) ^ 344034498 = 1 := by
        calc
          (2 : ZMod 344034499) ^ 344034498 = (2 : ZMod 344034499) ^ (172017249 + 172017249) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 172017249 * (2 : ZMod 344034499) ^ 172017249 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (57339083, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (57339083, 1)] : List FactorBlock).map factorBlockValue).prod = 344034499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_57339083) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 344034499) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 344034499) ^ 2 = 4 := by
        calc
          (2 : ZMod 344034499) ^ 2 = (2 : ZMod 344034499) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 1 * (2 : ZMod 344034499) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 344034499) ^ 5 = 32 := by
        calc
          (2 : ZMod 344034499) ^ 5 = (2 : ZMod 344034499) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 2 * (2 : ZMod 344034499) ^ 2) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 344034499) ^ 10 = 1024 := by
        calc
          (2 : ZMod 344034499) ^ 10 = (2 : ZMod 344034499) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 5 * (2 : ZMod 344034499) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 344034499) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 344034499) ^ 20 = (2 : ZMod 344034499) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 10 * (2 : ZMod 344034499) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 344034499) ^ 41 = 298772443 := by
        calc
          (2 : ZMod 344034499) ^ 41 = (2 : ZMod 344034499) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 20 * (2 : ZMod 344034499) ^ 20) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 298772443 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 344034499) ^ 82 = 175012427 := by
        calc
          (2 : ZMod 344034499) ^ 82 = (2 : ZMod 344034499) ^ (41 + 41) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 41 * (2 : ZMod 344034499) ^ 41 := by rw [pow_add]
          _ = 175012427 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 344034499) ^ 164 = 130669207 := by
        calc
          (2 : ZMod 344034499) ^ 164 = (2 : ZMod 344034499) ^ (82 + 82) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 82 * (2 : ZMod 344034499) ^ 82 := by rw [pow_add]
          _ = 130669207 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 344034499) ^ 328 = 183707376 := by
        calc
          (2 : ZMod 344034499) ^ 328 = (2 : ZMod 344034499) ^ (164 + 164) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 164 * (2 : ZMod 344034499) ^ 164 := by rw [pow_add]
          _ = 183707376 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 344034499) ^ 656 = 39729352 := by
        calc
          (2 : ZMod 344034499) ^ 656 = (2 : ZMod 344034499) ^ (328 + 328) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 328 * (2 : ZMod 344034499) ^ 328 := by rw [pow_add]
          _ = 39729352 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 344034499) ^ 1312 = 73824878 := by
        calc
          (2 : ZMod 344034499) ^ 1312 = (2 : ZMod 344034499) ^ (656 + 656) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 656 * (2 : ZMod 344034499) ^ 656 := by rw [pow_add]
          _ = 73824878 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 344034499) ^ 2624 = 302802145 := by
        calc
          (2 : ZMod 344034499) ^ 2624 = (2 : ZMod 344034499) ^ (1312 + 1312) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 1312 * (2 : ZMod 344034499) ^ 1312 := by rw [pow_add]
          _ = 302802145 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 344034499) ^ 5249 = 323036483 := by
        calc
          (2 : ZMod 344034499) ^ 5249 = (2 : ZMod 344034499) ^ (2624 + 2624 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 2624 * (2 : ZMod 344034499) ^ 2624) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 323036483 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 344034499) ^ 10499 = 339656223 := by
        calc
          (2 : ZMod 344034499) ^ 10499 = (2 : ZMod 344034499) ^ (5249 + 5249 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 5249 * (2 : ZMod 344034499) ^ 5249) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 339656223 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 344034499) ^ 20998 = 42482395 := by
        calc
          (2 : ZMod 344034499) ^ 20998 = (2 : ZMod 344034499) ^ (10499 + 10499) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 10499 * (2 : ZMod 344034499) ^ 10499 := by rw [pow_add]
          _ = 42482395 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 344034499) ^ 41996 = 164322376 := by
        calc
          (2 : ZMod 344034499) ^ 41996 = (2 : ZMod 344034499) ^ (20998 + 20998) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 20998 * (2 : ZMod 344034499) ^ 20998 := by rw [pow_add]
          _ = 164322376 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 344034499) ^ 83992 = 74635735 := by
        calc
          (2 : ZMod 344034499) ^ 83992 = (2 : ZMod 344034499) ^ (41996 + 41996) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 41996 * (2 : ZMod 344034499) ^ 41996 := by rw [pow_add]
          _ = 74635735 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 344034499) ^ 167985 = 69168289 := by
        calc
          (2 : ZMod 344034499) ^ 167985 = (2 : ZMod 344034499) ^ (83992 + 83992 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 83992 * (2 : ZMod 344034499) ^ 83992) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 69168289 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 344034499) ^ 335971 = 178452672 := by
        calc
          (2 : ZMod 344034499) ^ 335971 = (2 : ZMod 344034499) ^ (167985 + 167985 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 167985 * (2 : ZMod 344034499) ^ 167985) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 178452672 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 344034499) ^ 671942 = 219807010 := by
        calc
          (2 : ZMod 344034499) ^ 671942 = (2 : ZMod 344034499) ^ (335971 + 335971) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 335971 * (2 : ZMod 344034499) ^ 335971 := by rw [pow_add]
          _ = 219807010 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 344034499) ^ 1343884 = 314251950 := by
        calc
          (2 : ZMod 344034499) ^ 1343884 = (2 : ZMod 344034499) ^ (671942 + 671942) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 671942 * (2 : ZMod 344034499) ^ 671942 := by rw [pow_add]
          _ = 314251950 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 344034499) ^ 2687769 = 317161262 := by
        calc
          (2 : ZMod 344034499) ^ 2687769 = (2 : ZMod 344034499) ^ (1343884 + 1343884 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 1343884 * (2 : ZMod 344034499) ^ 1343884) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 317161262 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 344034499) ^ 5375539 = 274427584 := by
        calc
          (2 : ZMod 344034499) ^ 5375539 = (2 : ZMod 344034499) ^ (2687769 + 2687769 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 2687769 * (2 : ZMod 344034499) ^ 2687769) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 274427584 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 344034499) ^ 10751078 = 133913471 := by
        calc
          (2 : ZMod 344034499) ^ 10751078 = (2 : ZMod 344034499) ^ (5375539 + 5375539) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 5375539 * (2 : ZMod 344034499) ^ 5375539 := by rw [pow_add]
          _ = 133913471 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 344034499) ^ 21502156 = 188960897 := by
        calc
          (2 : ZMod 344034499) ^ 21502156 = (2 : ZMod 344034499) ^ (10751078 + 10751078) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 10751078 * (2 : ZMod 344034499) ^ 10751078 := by rw [pow_add]
          _ = 188960897 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 344034499) ^ 43004312 = 120163353 := by
        calc
          (2 : ZMod 344034499) ^ 43004312 = (2 : ZMod 344034499) ^ (21502156 + 21502156) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 21502156 * (2 : ZMod 344034499) ^ 21502156 := by rw [pow_add]
          _ = 120163353 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 344034499) ^ 86008624 = 270822909 := by
        calc
          (2 : ZMod 344034499) ^ 86008624 = (2 : ZMod 344034499) ^ (43004312 + 43004312) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 43004312 * (2 : ZMod 344034499) ^ 43004312 := by rw [pow_add]
          _ = 270822909 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 344034499) ^ 172017249 = 344034498 := by
        calc
          (2 : ZMod 344034499) ^ 172017249 = (2 : ZMod 344034499) ^ (86008624 + 86008624 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 86008624 * (2 : ZMod 344034499) ^ 86008624) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 344034498 := by rw [factor_0_26]; decide
      change (2 : ZMod 344034499) ^ 172017249 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (2 : ZMod 344034499) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 344034499) ^ 3 = 8 := by
        calc
          (2 : ZMod 344034499) ^ 3 = (2 : ZMod 344034499) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 1 * (2 : ZMod 344034499) ^ 1) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 344034499) ^ 6 = 64 := by
        calc
          (2 : ZMod 344034499) ^ 6 = (2 : ZMod 344034499) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 3 * (2 : ZMod 344034499) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 344034499) ^ 13 = 8192 := by
        calc
          (2 : ZMod 344034499) ^ 13 = (2 : ZMod 344034499) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 6 * (2 : ZMod 344034499) ^ 6) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 344034499) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 344034499) ^ 27 = (2 : ZMod 344034499) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 13 * (2 : ZMod 344034499) ^ 13) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 344034499) ^ 54 = 82427170 := by
        calc
          (2 : ZMod 344034499) ^ 54 = (2 : ZMod 344034499) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 27 * (2 : ZMod 344034499) ^ 27 := by rw [pow_add]
          _ = 82427170 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 344034499) ^ 109 = 230787224 := by
        calc
          (2 : ZMod 344034499) ^ 109 = (2 : ZMod 344034499) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 54 * (2 : ZMod 344034499) ^ 54) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 230787224 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 344034499) ^ 218 = 62478204 := by
        calc
          (2 : ZMod 344034499) ^ 218 = (2 : ZMod 344034499) ^ (109 + 109) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 109 * (2 : ZMod 344034499) ^ 109 := by rw [pow_add]
          _ = 62478204 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 344034499) ^ 437 = 228674874 := by
        calc
          (2 : ZMod 344034499) ^ 437 = (2 : ZMod 344034499) ^ (218 + 218 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 218 * (2 : ZMod 344034499) ^ 218) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 228674874 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 344034499) ^ 874 = 15792836 := by
        calc
          (2 : ZMod 344034499) ^ 874 = (2 : ZMod 344034499) ^ (437 + 437) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 437 * (2 : ZMod 344034499) ^ 437 := by rw [pow_add]
          _ = 15792836 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 344034499) ^ 1749 = 20572726 := by
        calc
          (2 : ZMod 344034499) ^ 1749 = (2 : ZMod 344034499) ^ (874 + 874 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 874 * (2 : ZMod 344034499) ^ 874) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 20572726 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 344034499) ^ 3499 = 275664085 := by
        calc
          (2 : ZMod 344034499) ^ 3499 = (2 : ZMod 344034499) ^ (1749 + 1749 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 1749 * (2 : ZMod 344034499) ^ 1749) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 275664085 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 344034499) ^ 6999 = 289846470 := by
        calc
          (2 : ZMod 344034499) ^ 6999 = (2 : ZMod 344034499) ^ (3499 + 3499 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 3499 * (2 : ZMod 344034499) ^ 3499) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 289846470 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 344034499) ^ 13998 = 125146364 := by
        calc
          (2 : ZMod 344034499) ^ 13998 = (2 : ZMod 344034499) ^ (6999 + 6999) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 6999 * (2 : ZMod 344034499) ^ 6999 := by rw [pow_add]
          _ = 125146364 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 344034499) ^ 27997 = 102840247 := by
        calc
          (2 : ZMod 344034499) ^ 27997 = (2 : ZMod 344034499) ^ (13998 + 13998 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 13998 * (2 : ZMod 344034499) ^ 13998) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 102840247 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 344034499) ^ 55995 = 300095900 := by
        calc
          (2 : ZMod 344034499) ^ 55995 = (2 : ZMod 344034499) ^ (27997 + 27997 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 27997 * (2 : ZMod 344034499) ^ 27997) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 300095900 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 344034499) ^ 111990 = 317872948 := by
        calc
          (2 : ZMod 344034499) ^ 111990 = (2 : ZMod 344034499) ^ (55995 + 55995) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 55995 * (2 : ZMod 344034499) ^ 55995 := by rw [pow_add]
          _ = 317872948 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 344034499) ^ 223980 = 45966514 := by
        calc
          (2 : ZMod 344034499) ^ 223980 = (2 : ZMod 344034499) ^ (111990 + 111990) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 111990 * (2 : ZMod 344034499) ^ 111990 := by rw [pow_add]
          _ = 45966514 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 344034499) ^ 447961 = 44887081 := by
        calc
          (2 : ZMod 344034499) ^ 447961 = (2 : ZMod 344034499) ^ (223980 + 223980 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 223980 * (2 : ZMod 344034499) ^ 223980) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 44887081 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 344034499) ^ 895923 = 256233691 := by
        calc
          (2 : ZMod 344034499) ^ 895923 = (2 : ZMod 344034499) ^ (447961 + 447961 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 447961 * (2 : ZMod 344034499) ^ 447961) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 256233691 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 344034499) ^ 1791846 = 294246947 := by
        calc
          (2 : ZMod 344034499) ^ 1791846 = (2 : ZMod 344034499) ^ (895923 + 895923) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 895923 * (2 : ZMod 344034499) ^ 895923 := by rw [pow_add]
          _ = 294246947 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 344034499) ^ 3583692 = 117683796 := by
        calc
          (2 : ZMod 344034499) ^ 3583692 = (2 : ZMod 344034499) ^ (1791846 + 1791846) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 1791846 * (2 : ZMod 344034499) ^ 1791846 := by rw [pow_add]
          _ = 117683796 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 344034499) ^ 7167385 = 341862865 := by
        calc
          (2 : ZMod 344034499) ^ 7167385 = (2 : ZMod 344034499) ^ (3583692 + 3583692 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 3583692 * (2 : ZMod 344034499) ^ 3583692) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 341862865 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 344034499) ^ 14334770 = 313352163 := by
        calc
          (2 : ZMod 344034499) ^ 14334770 = (2 : ZMod 344034499) ^ (7167385 + 7167385) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 7167385 * (2 : ZMod 344034499) ^ 7167385 := by rw [pow_add]
          _ = 313352163 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 344034499) ^ 28669541 = 120776532 := by
        calc
          (2 : ZMod 344034499) ^ 28669541 = (2 : ZMod 344034499) ^ (14334770 + 14334770 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 14334770 * (2 : ZMod 344034499) ^ 14334770) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 120776532 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 344034499) ^ 57339083 = 251185512 := by
        calc
          (2 : ZMod 344034499) ^ 57339083 = (2 : ZMod 344034499) ^ (28669541 + 28669541 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 28669541 * (2 : ZMod 344034499) ^ 28669541) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 251185512 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 344034499) ^ 114678166 = 251185511 := by
        calc
          (2 : ZMod 344034499) ^ 114678166 = (2 : ZMod 344034499) ^ (57339083 + 57339083) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 57339083 * (2 : ZMod 344034499) ^ 57339083 := by rw [pow_add]
          _ = 251185511 := by rw [factor_1_25]; decide
      change (2 : ZMod 344034499) ^ 114678166 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (2 : ZMod 344034499) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 344034499) ^ 3 = 8 := by
        calc
          (2 : ZMod 344034499) ^ 3 = (2 : ZMod 344034499) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = ((2 : ZMod 344034499) ^ 1 * (2 : ZMod 344034499) ^ 1) * (2 : ZMod 344034499) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 344034499) ^ 6 = 64 := by
        calc
          (2 : ZMod 344034499) ^ 6 = (2 : ZMod 344034499) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 344034499) ^ n) (by norm_num)
          _ = (2 : ZMod 344034499) ^ 3 * (2 : ZMod 344034499) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      change (2 : ZMod 344034499) ^ 6 ≠ 1
      rw [factor_2_2]
      decide

#print axioms prime_lucas_344034499

end TotientTailPeriodKiller
end Erdos249257
