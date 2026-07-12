import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_73011517 : Nat.Prime 73011517 := by
  apply lucas_primality 73011517 (6 : ZMod 73011517)
  ·
      have fermat_0 : (6 : ZMod 73011517) ^ 1 = 6 := by norm_num
      have fermat_1 : (6 : ZMod 73011517) ^ 2 = 36 := by
        calc
          (6 : ZMod 73011517) ^ 2 = (6 : ZMod 73011517) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 1 * (6 : ZMod 73011517) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [fermat_0]; decide
      have fermat_2 : (6 : ZMod 73011517) ^ 4 = 1296 := by
        calc
          (6 : ZMod 73011517) ^ 4 = (6 : ZMod 73011517) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 2 * (6 : ZMod 73011517) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [fermat_1]; decide
      have fermat_3 : (6 : ZMod 73011517) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 73011517) ^ 8 = (6 : ZMod 73011517) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 4 * (6 : ZMod 73011517) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [fermat_2]; decide
      have fermat_4 : (6 : ZMod 73011517) ^ 17 = 34401041 := by
        calc
          (6 : ZMod 73011517) ^ 17 = (6 : ZMod 73011517) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 8 * (6 : ZMod 73011517) ^ 8) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 34401041 := by rw [fermat_3]; decide
      have fermat_5 : (6 : ZMod 73011517) ^ 34 = 62742503 := by
        calc
          (6 : ZMod 73011517) ^ 34 = (6 : ZMod 73011517) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 17 * (6 : ZMod 73011517) ^ 17 := by rw [pow_add]
          _ = 62742503 := by rw [fermat_4]; decide
      have fermat_6 : (6 : ZMod 73011517) ^ 69 = 56182135 := by
        calc
          (6 : ZMod 73011517) ^ 69 = (6 : ZMod 73011517) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 34 * (6 : ZMod 73011517) ^ 34) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 56182135 := by rw [fermat_5]; decide
      have fermat_7 : (6 : ZMod 73011517) ^ 139 = 51817111 := by
        calc
          (6 : ZMod 73011517) ^ 139 = (6 : ZMod 73011517) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 69 * (6 : ZMod 73011517) ^ 69) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 51817111 := by rw [fermat_6]; decide
      have fermat_8 : (6 : ZMod 73011517) ^ 278 = 71442472 := by
        calc
          (6 : ZMod 73011517) ^ 278 = (6 : ZMod 73011517) ^ (139 + 139) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 139 * (6 : ZMod 73011517) ^ 139 := by rw [pow_add]
          _ = 71442472 := by rw [fermat_7]; decide
      have fermat_9 : (6 : ZMod 73011517) ^ 557 = 15198778 := by
        calc
          (6 : ZMod 73011517) ^ 557 = (6 : ZMod 73011517) ^ (278 + 278 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 278 * (6 : ZMod 73011517) ^ 278) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 15198778 := by rw [fermat_8]; decide
      have fermat_10 : (6 : ZMod 73011517) ^ 1114 = 34792093 := by
        calc
          (6 : ZMod 73011517) ^ 1114 = (6 : ZMod 73011517) ^ (557 + 557) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 557 * (6 : ZMod 73011517) ^ 557 := by rw [pow_add]
          _ = 34792093 := by rw [fermat_9]; decide
      have fermat_11 : (6 : ZMod 73011517) ^ 2228 = 34967754 := by
        calc
          (6 : ZMod 73011517) ^ 2228 = (6 : ZMod 73011517) ^ (1114 + 1114) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 1114 * (6 : ZMod 73011517) ^ 1114 := by rw [pow_add]
          _ = 34967754 := by rw [fermat_10]; decide
      have fermat_12 : (6 : ZMod 73011517) ^ 4456 = 12461375 := by
        calc
          (6 : ZMod 73011517) ^ 4456 = (6 : ZMod 73011517) ^ (2228 + 2228) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 2228 * (6 : ZMod 73011517) ^ 2228 := by rw [pow_add]
          _ = 12461375 := by rw [fermat_11]; decide
      have fermat_13 : (6 : ZMod 73011517) ^ 8912 = 7751869 := by
        calc
          (6 : ZMod 73011517) ^ 8912 = (6 : ZMod 73011517) ^ (4456 + 4456) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 4456 * (6 : ZMod 73011517) ^ 4456 := by rw [pow_add]
          _ = 7751869 := by rw [fermat_12]; decide
      have fermat_14 : (6 : ZMod 73011517) ^ 17825 = 6179784 := by
        calc
          (6 : ZMod 73011517) ^ 17825 = (6 : ZMod 73011517) ^ (8912 + 8912 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 8912 * (6 : ZMod 73011517) ^ 8912) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 6179784 := by rw [fermat_13]; decide
      have fermat_15 : (6 : ZMod 73011517) ^ 35650 = 34158568 := by
        calc
          (6 : ZMod 73011517) ^ 35650 = (6 : ZMod 73011517) ^ (17825 + 17825) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 17825 * (6 : ZMod 73011517) ^ 17825 := by rw [pow_add]
          _ = 34158568 := by rw [fermat_14]; decide
      have fermat_16 : (6 : ZMod 73011517) ^ 71300 = 54952142 := by
        calc
          (6 : ZMod 73011517) ^ 71300 = (6 : ZMod 73011517) ^ (35650 + 35650) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 35650 * (6 : ZMod 73011517) ^ 35650 := by rw [pow_add]
          _ = 54952142 := by rw [fermat_15]; decide
      have fermat_17 : (6 : ZMod 73011517) ^ 142600 = 39181965 := by
        calc
          (6 : ZMod 73011517) ^ 142600 = (6 : ZMod 73011517) ^ (71300 + 71300) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 71300 * (6 : ZMod 73011517) ^ 71300 := by rw [pow_add]
          _ = 39181965 := by rw [fermat_16]; decide
      have fermat_18 : (6 : ZMod 73011517) ^ 285201 = 62317405 := by
        calc
          (6 : ZMod 73011517) ^ 285201 = (6 : ZMod 73011517) ^ (142600 + 142600 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 142600 * (6 : ZMod 73011517) ^ 142600) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 62317405 := by rw [fermat_17]; decide
      have fermat_19 : (6 : ZMod 73011517) ^ 570402 = 32435533 := by
        calc
          (6 : ZMod 73011517) ^ 570402 = (6 : ZMod 73011517) ^ (285201 + 285201) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 285201 * (6 : ZMod 73011517) ^ 285201 := by rw [pow_add]
          _ = 32435533 := by rw [fermat_18]; decide
      have fermat_20 : (6 : ZMod 73011517) ^ 1140804 = 39103086 := by
        calc
          (6 : ZMod 73011517) ^ 1140804 = (6 : ZMod 73011517) ^ (570402 + 570402) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 570402 * (6 : ZMod 73011517) ^ 570402 := by rw [pow_add]
          _ = 39103086 := by rw [fermat_19]; decide
      have fermat_21 : (6 : ZMod 73011517) ^ 2281609 = 61484217 := by
        calc
          (6 : ZMod 73011517) ^ 2281609 = (6 : ZMod 73011517) ^ (1140804 + 1140804 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 1140804 * (6 : ZMod 73011517) ^ 1140804) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 61484217 := by rw [fermat_20]; decide
      have fermat_22 : (6 : ZMod 73011517) ^ 4563219 = 51299747 := by
        calc
          (6 : ZMod 73011517) ^ 4563219 = (6 : ZMod 73011517) ^ (2281609 + 2281609 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 2281609 * (6 : ZMod 73011517) ^ 2281609) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 51299747 := by rw [fermat_21]; decide
      have fermat_23 : (6 : ZMod 73011517) ^ 9126439 = 24153476 := by
        calc
          (6 : ZMod 73011517) ^ 9126439 = (6 : ZMod 73011517) ^ (4563219 + 4563219 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 4563219 * (6 : ZMod 73011517) ^ 4563219) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 24153476 := by rw [fermat_22]; decide
      have fermat_24 : (6 : ZMod 73011517) ^ 18252879 = 29457812 := by
        calc
          (6 : ZMod 73011517) ^ 18252879 = (6 : ZMod 73011517) ^ (9126439 + 9126439 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 9126439 * (6 : ZMod 73011517) ^ 9126439) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 29457812 := by rw [fermat_23]; decide
      have fermat_25 : (6 : ZMod 73011517) ^ 36505758 = 73011516 := by
        calc
          (6 : ZMod 73011517) ^ 36505758 = (6 : ZMod 73011517) ^ (18252879 + 18252879) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 18252879 * (6 : ZMod 73011517) ^ 18252879 := by rw [pow_add]
          _ = 73011516 := by rw [fermat_24]; decide
      have fermat_26 : (6 : ZMod 73011517) ^ 73011516 = 1 := by
        calc
          (6 : ZMod 73011517) ^ 73011516 = (6 : ZMod 73011517) ^ (36505758 + 36505758) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 36505758 * (6 : ZMod 73011517) ^ 36505758 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (6084293, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (6084293, 1)] : List FactorBlock).map factorBlockValue).prod = 73011517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (6 : ZMod 73011517) ^ 1 = 6 := by norm_num
      have factor_0_1 : (6 : ZMod 73011517) ^ 2 = 36 := by
        calc
          (6 : ZMod 73011517) ^ 2 = (6 : ZMod 73011517) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 1 * (6 : ZMod 73011517) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_0_0]; decide
      have factor_0_2 : (6 : ZMod 73011517) ^ 4 = 1296 := by
        calc
          (6 : ZMod 73011517) ^ 4 = (6 : ZMod 73011517) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 2 * (6 : ZMod 73011517) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_0_1]; decide
      have factor_0_3 : (6 : ZMod 73011517) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 73011517) ^ 8 = (6 : ZMod 73011517) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 4 * (6 : ZMod 73011517) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_0_2]; decide
      have factor_0_4 : (6 : ZMod 73011517) ^ 17 = 34401041 := by
        calc
          (6 : ZMod 73011517) ^ 17 = (6 : ZMod 73011517) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 8 * (6 : ZMod 73011517) ^ 8) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 34401041 := by rw [factor_0_3]; decide
      have factor_0_5 : (6 : ZMod 73011517) ^ 34 = 62742503 := by
        calc
          (6 : ZMod 73011517) ^ 34 = (6 : ZMod 73011517) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 17 * (6 : ZMod 73011517) ^ 17 := by rw [pow_add]
          _ = 62742503 := by rw [factor_0_4]; decide
      have factor_0_6 : (6 : ZMod 73011517) ^ 69 = 56182135 := by
        calc
          (6 : ZMod 73011517) ^ 69 = (6 : ZMod 73011517) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 34 * (6 : ZMod 73011517) ^ 34) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 56182135 := by rw [factor_0_5]; decide
      have factor_0_7 : (6 : ZMod 73011517) ^ 139 = 51817111 := by
        calc
          (6 : ZMod 73011517) ^ 139 = (6 : ZMod 73011517) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 69 * (6 : ZMod 73011517) ^ 69) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 51817111 := by rw [factor_0_6]; decide
      have factor_0_8 : (6 : ZMod 73011517) ^ 278 = 71442472 := by
        calc
          (6 : ZMod 73011517) ^ 278 = (6 : ZMod 73011517) ^ (139 + 139) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 139 * (6 : ZMod 73011517) ^ 139 := by rw [pow_add]
          _ = 71442472 := by rw [factor_0_7]; decide
      have factor_0_9 : (6 : ZMod 73011517) ^ 557 = 15198778 := by
        calc
          (6 : ZMod 73011517) ^ 557 = (6 : ZMod 73011517) ^ (278 + 278 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 278 * (6 : ZMod 73011517) ^ 278) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 15198778 := by rw [factor_0_8]; decide
      have factor_0_10 : (6 : ZMod 73011517) ^ 1114 = 34792093 := by
        calc
          (6 : ZMod 73011517) ^ 1114 = (6 : ZMod 73011517) ^ (557 + 557) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 557 * (6 : ZMod 73011517) ^ 557 := by rw [pow_add]
          _ = 34792093 := by rw [factor_0_9]; decide
      have factor_0_11 : (6 : ZMod 73011517) ^ 2228 = 34967754 := by
        calc
          (6 : ZMod 73011517) ^ 2228 = (6 : ZMod 73011517) ^ (1114 + 1114) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 1114 * (6 : ZMod 73011517) ^ 1114 := by rw [pow_add]
          _ = 34967754 := by rw [factor_0_10]; decide
      have factor_0_12 : (6 : ZMod 73011517) ^ 4456 = 12461375 := by
        calc
          (6 : ZMod 73011517) ^ 4456 = (6 : ZMod 73011517) ^ (2228 + 2228) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 2228 * (6 : ZMod 73011517) ^ 2228 := by rw [pow_add]
          _ = 12461375 := by rw [factor_0_11]; decide
      have factor_0_13 : (6 : ZMod 73011517) ^ 8912 = 7751869 := by
        calc
          (6 : ZMod 73011517) ^ 8912 = (6 : ZMod 73011517) ^ (4456 + 4456) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 4456 * (6 : ZMod 73011517) ^ 4456 := by rw [pow_add]
          _ = 7751869 := by rw [factor_0_12]; decide
      have factor_0_14 : (6 : ZMod 73011517) ^ 17825 = 6179784 := by
        calc
          (6 : ZMod 73011517) ^ 17825 = (6 : ZMod 73011517) ^ (8912 + 8912 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 8912 * (6 : ZMod 73011517) ^ 8912) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 6179784 := by rw [factor_0_13]; decide
      have factor_0_15 : (6 : ZMod 73011517) ^ 35650 = 34158568 := by
        calc
          (6 : ZMod 73011517) ^ 35650 = (6 : ZMod 73011517) ^ (17825 + 17825) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 17825 * (6 : ZMod 73011517) ^ 17825 := by rw [pow_add]
          _ = 34158568 := by rw [factor_0_14]; decide
      have factor_0_16 : (6 : ZMod 73011517) ^ 71300 = 54952142 := by
        calc
          (6 : ZMod 73011517) ^ 71300 = (6 : ZMod 73011517) ^ (35650 + 35650) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 35650 * (6 : ZMod 73011517) ^ 35650 := by rw [pow_add]
          _ = 54952142 := by rw [factor_0_15]; decide
      have factor_0_17 : (6 : ZMod 73011517) ^ 142600 = 39181965 := by
        calc
          (6 : ZMod 73011517) ^ 142600 = (6 : ZMod 73011517) ^ (71300 + 71300) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 71300 * (6 : ZMod 73011517) ^ 71300 := by rw [pow_add]
          _ = 39181965 := by rw [factor_0_16]; decide
      have factor_0_18 : (6 : ZMod 73011517) ^ 285201 = 62317405 := by
        calc
          (6 : ZMod 73011517) ^ 285201 = (6 : ZMod 73011517) ^ (142600 + 142600 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 142600 * (6 : ZMod 73011517) ^ 142600) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 62317405 := by rw [factor_0_17]; decide
      have factor_0_19 : (6 : ZMod 73011517) ^ 570402 = 32435533 := by
        calc
          (6 : ZMod 73011517) ^ 570402 = (6 : ZMod 73011517) ^ (285201 + 285201) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 285201 * (6 : ZMod 73011517) ^ 285201 := by rw [pow_add]
          _ = 32435533 := by rw [factor_0_18]; decide
      have factor_0_20 : (6 : ZMod 73011517) ^ 1140804 = 39103086 := by
        calc
          (6 : ZMod 73011517) ^ 1140804 = (6 : ZMod 73011517) ^ (570402 + 570402) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 570402 * (6 : ZMod 73011517) ^ 570402 := by rw [pow_add]
          _ = 39103086 := by rw [factor_0_19]; decide
      have factor_0_21 : (6 : ZMod 73011517) ^ 2281609 = 61484217 := by
        calc
          (6 : ZMod 73011517) ^ 2281609 = (6 : ZMod 73011517) ^ (1140804 + 1140804 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 1140804 * (6 : ZMod 73011517) ^ 1140804) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 61484217 := by rw [factor_0_20]; decide
      have factor_0_22 : (6 : ZMod 73011517) ^ 4563219 = 51299747 := by
        calc
          (6 : ZMod 73011517) ^ 4563219 = (6 : ZMod 73011517) ^ (2281609 + 2281609 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 2281609 * (6 : ZMod 73011517) ^ 2281609) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 51299747 := by rw [factor_0_21]; decide
      have factor_0_23 : (6 : ZMod 73011517) ^ 9126439 = 24153476 := by
        calc
          (6 : ZMod 73011517) ^ 9126439 = (6 : ZMod 73011517) ^ (4563219 + 4563219 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 4563219 * (6 : ZMod 73011517) ^ 4563219) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 24153476 := by rw [factor_0_22]; decide
      have factor_0_24 : (6 : ZMod 73011517) ^ 18252879 = 29457812 := by
        calc
          (6 : ZMod 73011517) ^ 18252879 = (6 : ZMod 73011517) ^ (9126439 + 9126439 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 9126439 * (6 : ZMod 73011517) ^ 9126439) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 29457812 := by rw [factor_0_23]; decide
      have factor_0_25 : (6 : ZMod 73011517) ^ 36505758 = 73011516 := by
        calc
          (6 : ZMod 73011517) ^ 36505758 = (6 : ZMod 73011517) ^ (18252879 + 18252879) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 18252879 * (6 : ZMod 73011517) ^ 18252879 := by rw [pow_add]
          _ = 73011516 := by rw [factor_0_24]; decide
      change (6 : ZMod 73011517) ^ 36505758 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (6 : ZMod 73011517) ^ 1 = 6 := by norm_num
      have factor_1_1 : (6 : ZMod 73011517) ^ 2 = 36 := by
        calc
          (6 : ZMod 73011517) ^ 2 = (6 : ZMod 73011517) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 1 * (6 : ZMod 73011517) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_1_0]; decide
      have factor_1_2 : (6 : ZMod 73011517) ^ 5 = 7776 := by
        calc
          (6 : ZMod 73011517) ^ 5 = (6 : ZMod 73011517) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 2 * (6 : ZMod 73011517) ^ 2) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_1_1]; decide
      have factor_1_3 : (6 : ZMod 73011517) ^ 11 = 70750988 := by
        calc
          (6 : ZMod 73011517) ^ 11 = (6 : ZMod 73011517) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 5 * (6 : ZMod 73011517) ^ 5) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 70750988 := by rw [factor_1_2]; decide
      have factor_1_4 : (6 : ZMod 73011517) ^ 23 = 2790685 := by
        calc
          (6 : ZMod 73011517) ^ 23 = (6 : ZMod 73011517) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 11 * (6 : ZMod 73011517) ^ 11) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 2790685 := by rw [factor_1_3]; decide
      have factor_1_5 : (6 : ZMod 73011517) ^ 46 = 3285386 := by
        calc
          (6 : ZMod 73011517) ^ 46 = (6 : ZMod 73011517) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 23 * (6 : ZMod 73011517) ^ 23 := by rw [pow_add]
          _ = 3285386 := by rw [factor_1_4]; decide
      have factor_1_6 : (6 : ZMod 73011517) ^ 92 = 30541784 := by
        calc
          (6 : ZMod 73011517) ^ 92 = (6 : ZMod 73011517) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 46 * (6 : ZMod 73011517) ^ 46 := by rw [pow_add]
          _ = 30541784 := by rw [factor_1_5]; decide
      have factor_1_7 : (6 : ZMod 73011517) ^ 185 = 9127354 := by
        calc
          (6 : ZMod 73011517) ^ 185 = (6 : ZMod 73011517) ^ (92 + 92 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 92 * (6 : ZMod 73011517) ^ 92) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 9127354 := by rw [factor_1_6]; decide
      have factor_1_8 : (6 : ZMod 73011517) ^ 371 = 25550979 := by
        calc
          (6 : ZMod 73011517) ^ 371 = (6 : ZMod 73011517) ^ (185 + 185 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 185 * (6 : ZMod 73011517) ^ 185) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 25550979 := by rw [factor_1_7]; decide
      have factor_1_9 : (6 : ZMod 73011517) ^ 742 = 43447283 := by
        calc
          (6 : ZMod 73011517) ^ 742 = (6 : ZMod 73011517) ^ (371 + 371) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 371 * (6 : ZMod 73011517) ^ 371 := by rw [pow_add]
          _ = 43447283 := by rw [factor_1_8]; decide
      have factor_1_10 : (6 : ZMod 73011517) ^ 1485 = 15173821 := by
        calc
          (6 : ZMod 73011517) ^ 1485 = (6 : ZMod 73011517) ^ (742 + 742 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 742 * (6 : ZMod 73011517) ^ 742) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 15173821 := by rw [factor_1_9]; decide
      have factor_1_11 : (6 : ZMod 73011517) ^ 2970 = 31408344 := by
        calc
          (6 : ZMod 73011517) ^ 2970 = (6 : ZMod 73011517) ^ (1485 + 1485) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 1485 * (6 : ZMod 73011517) ^ 1485 := by rw [pow_add]
          _ = 31408344 := by rw [factor_1_10]; decide
      have factor_1_12 : (6 : ZMod 73011517) ^ 5941 = 59718452 := by
        calc
          (6 : ZMod 73011517) ^ 5941 = (6 : ZMod 73011517) ^ (2970 + 2970 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 2970 * (6 : ZMod 73011517) ^ 2970) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 59718452 := by rw [factor_1_11]; decide
      have factor_1_13 : (6 : ZMod 73011517) ^ 11883 = 3968115 := by
        calc
          (6 : ZMod 73011517) ^ 11883 = (6 : ZMod 73011517) ^ (5941 + 5941 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 5941 * (6 : ZMod 73011517) ^ 5941) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 3968115 := by rw [factor_1_12]; decide
      have factor_1_14 : (6 : ZMod 73011517) ^ 23766 = 53862454 := by
        calc
          (6 : ZMod 73011517) ^ 23766 = (6 : ZMod 73011517) ^ (11883 + 11883) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 11883 * (6 : ZMod 73011517) ^ 11883 := by rw [pow_add]
          _ = 53862454 := by rw [factor_1_13]; decide
      have factor_1_15 : (6 : ZMod 73011517) ^ 47533 = 47875507 := by
        calc
          (6 : ZMod 73011517) ^ 47533 = (6 : ZMod 73011517) ^ (23766 + 23766 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 23766 * (6 : ZMod 73011517) ^ 23766) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 47875507 := by rw [factor_1_14]; decide
      have factor_1_16 : (6 : ZMod 73011517) ^ 95067 = 4068771 := by
        calc
          (6 : ZMod 73011517) ^ 95067 = (6 : ZMod 73011517) ^ (47533 + 47533 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 47533 * (6 : ZMod 73011517) ^ 47533) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 4068771 := by rw [factor_1_15]; decide
      have factor_1_17 : (6 : ZMod 73011517) ^ 190134 = 47051310 := by
        calc
          (6 : ZMod 73011517) ^ 190134 = (6 : ZMod 73011517) ^ (95067 + 95067) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 95067 * (6 : ZMod 73011517) ^ 95067 := by rw [pow_add]
          _ = 47051310 := by rw [factor_1_16]; decide
      have factor_1_18 : (6 : ZMod 73011517) ^ 380268 = 50894968 := by
        calc
          (6 : ZMod 73011517) ^ 380268 = (6 : ZMod 73011517) ^ (190134 + 190134) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 190134 * (6 : ZMod 73011517) ^ 190134 := by rw [pow_add]
          _ = 50894968 := by rw [factor_1_17]; decide
      have factor_1_19 : (6 : ZMod 73011517) ^ 760536 = 59366663 := by
        calc
          (6 : ZMod 73011517) ^ 760536 = (6 : ZMod 73011517) ^ (380268 + 380268) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 380268 * (6 : ZMod 73011517) ^ 380268 := by rw [pow_add]
          _ = 59366663 := by rw [factor_1_18]; decide
      have factor_1_20 : (6 : ZMod 73011517) ^ 1521073 = 44465673 := by
        calc
          (6 : ZMod 73011517) ^ 1521073 = (6 : ZMod 73011517) ^ (760536 + 760536 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 760536 * (6 : ZMod 73011517) ^ 760536) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 44465673 := by rw [factor_1_19]; decide
      have factor_1_21 : (6 : ZMod 73011517) ^ 3042146 = 23015144 := by
        calc
          (6 : ZMod 73011517) ^ 3042146 = (6 : ZMod 73011517) ^ (1521073 + 1521073) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 1521073 * (6 : ZMod 73011517) ^ 1521073 := by rw [pow_add]
          _ = 23015144 := by rw [factor_1_20]; decide
      have factor_1_22 : (6 : ZMod 73011517) ^ 6084293 = 6646796 := by
        calc
          (6 : ZMod 73011517) ^ 6084293 = (6 : ZMod 73011517) ^ (3042146 + 3042146 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 3042146 * (6 : ZMod 73011517) ^ 3042146) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 6646796 := by rw [factor_1_21]; decide
      have factor_1_23 : (6 : ZMod 73011517) ^ 12168586 = 44036780 := by
        calc
          (6 : ZMod 73011517) ^ 12168586 = (6 : ZMod 73011517) ^ (6084293 + 6084293) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 6084293 * (6 : ZMod 73011517) ^ 6084293 := by rw [pow_add]
          _ = 44036780 := by rw [factor_1_22]; decide
      have factor_1_24 : (6 : ZMod 73011517) ^ 24337172 = 44036779 := by
        calc
          (6 : ZMod 73011517) ^ 24337172 = (6 : ZMod 73011517) ^ (12168586 + 12168586) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 12168586 * (6 : ZMod 73011517) ^ 12168586 := by rw [pow_add]
          _ = 44036779 := by rw [factor_1_23]; decide
      change (6 : ZMod 73011517) ^ 24337172 ≠ 1
      rw [factor_1_24]
      decide
    ·
      have factor_2_0 : (6 : ZMod 73011517) ^ 1 = 6 := by norm_num
      have factor_2_1 : (6 : ZMod 73011517) ^ 3 = 216 := by
        calc
          (6 : ZMod 73011517) ^ 3 = (6 : ZMod 73011517) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = ((6 : ZMod 73011517) ^ 1 * (6 : ZMod 73011517) ^ 1) * (6 : ZMod 73011517) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_2_0]; decide
      have factor_2_2 : (6 : ZMod 73011517) ^ 6 = 46656 := by
        calc
          (6 : ZMod 73011517) ^ 6 = (6 : ZMod 73011517) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 3 * (6 : ZMod 73011517) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [factor_2_1]; decide
      have factor_2_3 : (6 : ZMod 73011517) ^ 12 = 59448343 := by
        calc
          (6 : ZMod 73011517) ^ 12 = (6 : ZMod 73011517) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (6 : ZMod 73011517) ^ n) (by norm_num)
          _ = (6 : ZMod 73011517) ^ 6 * (6 : ZMod 73011517) ^ 6 := by rw [pow_add]
          _ = 59448343 := by rw [factor_2_2]; decide
      change (6 : ZMod 73011517) ^ 12 ≠ 1
      rw [factor_2_3]
      decide

#print axioms prime_lucas_73011517

end TotientTailPeriodKiller
end Erdos249257
