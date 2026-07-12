import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1029659401 : Nat.Prime 1029659401 := by
  apply lucas_primality 1029659401 (37 : ZMod 1029659401)
  ·
      have fermat_0 : (37 : ZMod 1029659401) ^ 1 = 37 := by norm_num
      have fermat_1 : (37 : ZMod 1029659401) ^ 3 = 50653 := by
        calc
          (37 : ZMod 1029659401) ^ 3 = (37 : ZMod 1029659401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 1 * (37 : ZMod 1029659401) ^ 1) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [fermat_0]; decide
      have fermat_2 : (37 : ZMod 1029659401) ^ 7 = 203212241 := by
        calc
          (37 : ZMod 1029659401) ^ 7 = (37 : ZMod 1029659401) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 3 * (37 : ZMod 1029659401) ^ 3) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 203212241 := by rw [fermat_1]; decide
      have fermat_3 : (37 : ZMod 1029659401) ^ 15 = 488588759 := by
        calc
          (37 : ZMod 1029659401) ^ 15 = (37 : ZMod 1029659401) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 7 * (37 : ZMod 1029659401) ^ 7) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 488588759 := by rw [fermat_2]; decide
      have fermat_4 : (37 : ZMod 1029659401) ^ 30 = 999313421 := by
        calc
          (37 : ZMod 1029659401) ^ 30 = (37 : ZMod 1029659401) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 15 * (37 : ZMod 1029659401) ^ 15 := by rw [pow_add]
          _ = 999313421 := by rw [fermat_3]; decide
      have fermat_5 : (37 : ZMod 1029659401) ^ 61 = 36430156 := by
        calc
          (37 : ZMod 1029659401) ^ 61 = (37 : ZMod 1029659401) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 30 * (37 : ZMod 1029659401) ^ 30) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 36430156 := by rw [fermat_4]; decide
      have fermat_6 : (37 : ZMod 1029659401) ^ 122 = 463431609 := by
        calc
          (37 : ZMod 1029659401) ^ 122 = (37 : ZMod 1029659401) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 61 * (37 : ZMod 1029659401) ^ 61 := by rw [pow_add]
          _ = 463431609 := by rw [fermat_5]; decide
      have fermat_7 : (37 : ZMod 1029659401) ^ 245 = 608324421 := by
        calc
          (37 : ZMod 1029659401) ^ 245 = (37 : ZMod 1029659401) ^ (122 + 122 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 122 * (37 : ZMod 1029659401) ^ 122) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 608324421 := by rw [fermat_6]; decide
      have fermat_8 : (37 : ZMod 1029659401) ^ 490 = 938610201 := by
        calc
          (37 : ZMod 1029659401) ^ 490 = (37 : ZMod 1029659401) ^ (245 + 245) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 245 * (37 : ZMod 1029659401) ^ 245 := by rw [pow_add]
          _ = 938610201 := by rw [fermat_7]; decide
      have fermat_9 : (37 : ZMod 1029659401) ^ 981 = 286110128 := by
        calc
          (37 : ZMod 1029659401) ^ 981 = (37 : ZMod 1029659401) ^ (490 + 490 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 490 * (37 : ZMod 1029659401) ^ 490) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 286110128 := by rw [fermat_8]; decide
      have fermat_10 : (37 : ZMod 1029659401) ^ 1963 = 497436293 := by
        calc
          (37 : ZMod 1029659401) ^ 1963 = (37 : ZMod 1029659401) ^ (981 + 981 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 981 * (37 : ZMod 1029659401) ^ 981) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 497436293 := by rw [fermat_9]; decide
      have fermat_11 : (37 : ZMod 1029659401) ^ 3927 = 597152432 := by
        calc
          (37 : ZMod 1029659401) ^ 3927 = (37 : ZMod 1029659401) ^ (1963 + 1963 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 1963 * (37 : ZMod 1029659401) ^ 1963) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 597152432 := by rw [fermat_10]; decide
      have fermat_12 : (37 : ZMod 1029659401) ^ 7855 = 1011846050 := by
        calc
          (37 : ZMod 1029659401) ^ 7855 = (37 : ZMod 1029659401) ^ (3927 + 3927 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 3927 * (37 : ZMod 1029659401) ^ 3927) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 1011846050 := by rw [fermat_11]; decide
      have fermat_13 : (37 : ZMod 1029659401) ^ 15711 = 776046556 := by
        calc
          (37 : ZMod 1029659401) ^ 15711 = (37 : ZMod 1029659401) ^ (7855 + 7855 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 7855 * (37 : ZMod 1029659401) ^ 7855) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 776046556 := by rw [fermat_12]; decide
      have fermat_14 : (37 : ZMod 1029659401) ^ 31422 = 820896077 := by
        calc
          (37 : ZMod 1029659401) ^ 31422 = (37 : ZMod 1029659401) ^ (15711 + 15711) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 15711 * (37 : ZMod 1029659401) ^ 15711 := by rw [pow_add]
          _ = 820896077 := by rw [fermat_13]; decide
      have fermat_15 : (37 : ZMod 1029659401) ^ 62845 = 991223544 := by
        calc
          (37 : ZMod 1029659401) ^ 62845 = (37 : ZMod 1029659401) ^ (31422 + 31422 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 31422 * (37 : ZMod 1029659401) ^ 31422) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 991223544 := by rw [fermat_14]; decide
      have fermat_16 : (37 : ZMod 1029659401) ^ 125690 = 981145689 := by
        calc
          (37 : ZMod 1029659401) ^ 125690 = (37 : ZMod 1029659401) ^ (62845 + 62845) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 62845 * (37 : ZMod 1029659401) ^ 62845 := by rw [pow_add]
          _ = 981145689 := by rw [fermat_15]; decide
      have fermat_17 : (37 : ZMod 1029659401) ^ 251381 = 572578675 := by
        calc
          (37 : ZMod 1029659401) ^ 251381 = (37 : ZMod 1029659401) ^ (125690 + 125690 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 125690 * (37 : ZMod 1029659401) ^ 125690) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 572578675 := by rw [fermat_16]; decide
      have fermat_18 : (37 : ZMod 1029659401) ^ 502763 = 40821020 := by
        calc
          (37 : ZMod 1029659401) ^ 502763 = (37 : ZMod 1029659401) ^ (251381 + 251381 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 251381 * (37 : ZMod 1029659401) ^ 251381) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 40821020 := by rw [fermat_17]; decide
      have fermat_19 : (37 : ZMod 1029659401) ^ 1005526 = 204275644 := by
        calc
          (37 : ZMod 1029659401) ^ 1005526 = (37 : ZMod 1029659401) ^ (502763 + 502763) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 502763 * (37 : ZMod 1029659401) ^ 502763 := by rw [pow_add]
          _ = 204275644 := by rw [fermat_18]; decide
      have fermat_20 : (37 : ZMod 1029659401) ^ 2011053 = 533836443 := by
        calc
          (37 : ZMod 1029659401) ^ 2011053 = (37 : ZMod 1029659401) ^ (1005526 + 1005526 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 1005526 * (37 : ZMod 1029659401) ^ 1005526) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 533836443 := by rw [fermat_19]; decide
      have fermat_21 : (37 : ZMod 1029659401) ^ 4022107 = 81607422 := by
        calc
          (37 : ZMod 1029659401) ^ 4022107 = (37 : ZMod 1029659401) ^ (2011053 + 2011053 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 2011053 * (37 : ZMod 1029659401) ^ 2011053) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 81607422 := by rw [fermat_20]; decide
      have fermat_22 : (37 : ZMod 1029659401) ^ 8044214 = 218019748 := by
        calc
          (37 : ZMod 1029659401) ^ 8044214 = (37 : ZMod 1029659401) ^ (4022107 + 4022107) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 4022107 * (37 : ZMod 1029659401) ^ 4022107 := by rw [pow_add]
          _ = 218019748 := by rw [fermat_21]; decide
      have fermat_23 : (37 : ZMod 1029659401) ^ 16088428 = 836078074 := by
        calc
          (37 : ZMod 1029659401) ^ 16088428 = (37 : ZMod 1029659401) ^ (8044214 + 8044214) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 8044214 * (37 : ZMod 1029659401) ^ 8044214 := by rw [pow_add]
          _ = 836078074 := by rw [fermat_22]; decide
      have fermat_24 : (37 : ZMod 1029659401) ^ 32176856 = 114244832 := by
        calc
          (37 : ZMod 1029659401) ^ 32176856 = (37 : ZMod 1029659401) ^ (16088428 + 16088428) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 16088428 * (37 : ZMod 1029659401) ^ 16088428 := by rw [pow_add]
          _ = 114244832 := by rw [fermat_23]; decide
      have fermat_25 : (37 : ZMod 1029659401) ^ 64353712 = 414724903 := by
        calc
          (37 : ZMod 1029659401) ^ 64353712 = (37 : ZMod 1029659401) ^ (32176856 + 32176856) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 32176856 * (37 : ZMod 1029659401) ^ 32176856 := by rw [pow_add]
          _ = 414724903 := by rw [fermat_24]; decide
      have fermat_26 : (37 : ZMod 1029659401) ^ 128707425 = 275892696 := by
        calc
          (37 : ZMod 1029659401) ^ 128707425 = (37 : ZMod 1029659401) ^ (64353712 + 64353712 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 64353712 * (37 : ZMod 1029659401) ^ 64353712) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 275892696 := by rw [fermat_25]; decide
      have fermat_27 : (37 : ZMod 1029659401) ^ 257414850 = 295302785 := by
        calc
          (37 : ZMod 1029659401) ^ 257414850 = (37 : ZMod 1029659401) ^ (128707425 + 128707425) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 128707425 * (37 : ZMod 1029659401) ^ 128707425 := by rw [pow_add]
          _ = 295302785 := by rw [fermat_26]; decide
      have fermat_28 : (37 : ZMod 1029659401) ^ 514829700 = 1029659400 := by
        calc
          (37 : ZMod 1029659401) ^ 514829700 = (37 : ZMod 1029659401) ^ (257414850 + 257414850) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 257414850 * (37 : ZMod 1029659401) ^ 257414850 := by rw [pow_add]
          _ = 1029659400 := by rw [fermat_27]; decide
      have fermat_29 : (37 : ZMod 1029659401) ^ 1029659400 = 1 := by
        calc
          (37 : ZMod 1029659401) ^ 1029659400 = (37 : ZMod 1029659401) ^ (514829700 + 514829700) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 514829700 * (37 : ZMod 1029659401) ^ 514829700 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (5, 2), (7, 1), (11, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (5, 2), (7, 1), (11, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 1029659401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (37 : ZMod 1029659401) ^ 1 = 37 := by norm_num
      have factor_0_1 : (37 : ZMod 1029659401) ^ 3 = 50653 := by
        calc
          (37 : ZMod 1029659401) ^ 3 = (37 : ZMod 1029659401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 1 * (37 : ZMod 1029659401) ^ 1) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [factor_0_0]; decide
      have factor_0_2 : (37 : ZMod 1029659401) ^ 7 = 203212241 := by
        calc
          (37 : ZMod 1029659401) ^ 7 = (37 : ZMod 1029659401) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 3 * (37 : ZMod 1029659401) ^ 3) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 203212241 := by rw [factor_0_1]; decide
      have factor_0_3 : (37 : ZMod 1029659401) ^ 15 = 488588759 := by
        calc
          (37 : ZMod 1029659401) ^ 15 = (37 : ZMod 1029659401) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 7 * (37 : ZMod 1029659401) ^ 7) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 488588759 := by rw [factor_0_2]; decide
      have factor_0_4 : (37 : ZMod 1029659401) ^ 30 = 999313421 := by
        calc
          (37 : ZMod 1029659401) ^ 30 = (37 : ZMod 1029659401) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 15 * (37 : ZMod 1029659401) ^ 15 := by rw [pow_add]
          _ = 999313421 := by rw [factor_0_3]; decide
      have factor_0_5 : (37 : ZMod 1029659401) ^ 61 = 36430156 := by
        calc
          (37 : ZMod 1029659401) ^ 61 = (37 : ZMod 1029659401) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 30 * (37 : ZMod 1029659401) ^ 30) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 36430156 := by rw [factor_0_4]; decide
      have factor_0_6 : (37 : ZMod 1029659401) ^ 122 = 463431609 := by
        calc
          (37 : ZMod 1029659401) ^ 122 = (37 : ZMod 1029659401) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 61 * (37 : ZMod 1029659401) ^ 61 := by rw [pow_add]
          _ = 463431609 := by rw [factor_0_5]; decide
      have factor_0_7 : (37 : ZMod 1029659401) ^ 245 = 608324421 := by
        calc
          (37 : ZMod 1029659401) ^ 245 = (37 : ZMod 1029659401) ^ (122 + 122 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 122 * (37 : ZMod 1029659401) ^ 122) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 608324421 := by rw [factor_0_6]; decide
      have factor_0_8 : (37 : ZMod 1029659401) ^ 490 = 938610201 := by
        calc
          (37 : ZMod 1029659401) ^ 490 = (37 : ZMod 1029659401) ^ (245 + 245) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 245 * (37 : ZMod 1029659401) ^ 245 := by rw [pow_add]
          _ = 938610201 := by rw [factor_0_7]; decide
      have factor_0_9 : (37 : ZMod 1029659401) ^ 981 = 286110128 := by
        calc
          (37 : ZMod 1029659401) ^ 981 = (37 : ZMod 1029659401) ^ (490 + 490 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 490 * (37 : ZMod 1029659401) ^ 490) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 286110128 := by rw [factor_0_8]; decide
      have factor_0_10 : (37 : ZMod 1029659401) ^ 1963 = 497436293 := by
        calc
          (37 : ZMod 1029659401) ^ 1963 = (37 : ZMod 1029659401) ^ (981 + 981 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 981 * (37 : ZMod 1029659401) ^ 981) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 497436293 := by rw [factor_0_9]; decide
      have factor_0_11 : (37 : ZMod 1029659401) ^ 3927 = 597152432 := by
        calc
          (37 : ZMod 1029659401) ^ 3927 = (37 : ZMod 1029659401) ^ (1963 + 1963 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 1963 * (37 : ZMod 1029659401) ^ 1963) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 597152432 := by rw [factor_0_10]; decide
      have factor_0_12 : (37 : ZMod 1029659401) ^ 7855 = 1011846050 := by
        calc
          (37 : ZMod 1029659401) ^ 7855 = (37 : ZMod 1029659401) ^ (3927 + 3927 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 3927 * (37 : ZMod 1029659401) ^ 3927) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 1011846050 := by rw [factor_0_11]; decide
      have factor_0_13 : (37 : ZMod 1029659401) ^ 15711 = 776046556 := by
        calc
          (37 : ZMod 1029659401) ^ 15711 = (37 : ZMod 1029659401) ^ (7855 + 7855 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 7855 * (37 : ZMod 1029659401) ^ 7855) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 776046556 := by rw [factor_0_12]; decide
      have factor_0_14 : (37 : ZMod 1029659401) ^ 31422 = 820896077 := by
        calc
          (37 : ZMod 1029659401) ^ 31422 = (37 : ZMod 1029659401) ^ (15711 + 15711) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 15711 * (37 : ZMod 1029659401) ^ 15711 := by rw [pow_add]
          _ = 820896077 := by rw [factor_0_13]; decide
      have factor_0_15 : (37 : ZMod 1029659401) ^ 62845 = 991223544 := by
        calc
          (37 : ZMod 1029659401) ^ 62845 = (37 : ZMod 1029659401) ^ (31422 + 31422 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 31422 * (37 : ZMod 1029659401) ^ 31422) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 991223544 := by rw [factor_0_14]; decide
      have factor_0_16 : (37 : ZMod 1029659401) ^ 125690 = 981145689 := by
        calc
          (37 : ZMod 1029659401) ^ 125690 = (37 : ZMod 1029659401) ^ (62845 + 62845) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 62845 * (37 : ZMod 1029659401) ^ 62845 := by rw [pow_add]
          _ = 981145689 := by rw [factor_0_15]; decide
      have factor_0_17 : (37 : ZMod 1029659401) ^ 251381 = 572578675 := by
        calc
          (37 : ZMod 1029659401) ^ 251381 = (37 : ZMod 1029659401) ^ (125690 + 125690 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 125690 * (37 : ZMod 1029659401) ^ 125690) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 572578675 := by rw [factor_0_16]; decide
      have factor_0_18 : (37 : ZMod 1029659401) ^ 502763 = 40821020 := by
        calc
          (37 : ZMod 1029659401) ^ 502763 = (37 : ZMod 1029659401) ^ (251381 + 251381 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 251381 * (37 : ZMod 1029659401) ^ 251381) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 40821020 := by rw [factor_0_17]; decide
      have factor_0_19 : (37 : ZMod 1029659401) ^ 1005526 = 204275644 := by
        calc
          (37 : ZMod 1029659401) ^ 1005526 = (37 : ZMod 1029659401) ^ (502763 + 502763) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 502763 * (37 : ZMod 1029659401) ^ 502763 := by rw [pow_add]
          _ = 204275644 := by rw [factor_0_18]; decide
      have factor_0_20 : (37 : ZMod 1029659401) ^ 2011053 = 533836443 := by
        calc
          (37 : ZMod 1029659401) ^ 2011053 = (37 : ZMod 1029659401) ^ (1005526 + 1005526 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 1005526 * (37 : ZMod 1029659401) ^ 1005526) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 533836443 := by rw [factor_0_19]; decide
      have factor_0_21 : (37 : ZMod 1029659401) ^ 4022107 = 81607422 := by
        calc
          (37 : ZMod 1029659401) ^ 4022107 = (37 : ZMod 1029659401) ^ (2011053 + 2011053 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 2011053 * (37 : ZMod 1029659401) ^ 2011053) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 81607422 := by rw [factor_0_20]; decide
      have factor_0_22 : (37 : ZMod 1029659401) ^ 8044214 = 218019748 := by
        calc
          (37 : ZMod 1029659401) ^ 8044214 = (37 : ZMod 1029659401) ^ (4022107 + 4022107) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 4022107 * (37 : ZMod 1029659401) ^ 4022107 := by rw [pow_add]
          _ = 218019748 := by rw [factor_0_21]; decide
      have factor_0_23 : (37 : ZMod 1029659401) ^ 16088428 = 836078074 := by
        calc
          (37 : ZMod 1029659401) ^ 16088428 = (37 : ZMod 1029659401) ^ (8044214 + 8044214) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 8044214 * (37 : ZMod 1029659401) ^ 8044214 := by rw [pow_add]
          _ = 836078074 := by rw [factor_0_22]; decide
      have factor_0_24 : (37 : ZMod 1029659401) ^ 32176856 = 114244832 := by
        calc
          (37 : ZMod 1029659401) ^ 32176856 = (37 : ZMod 1029659401) ^ (16088428 + 16088428) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 16088428 * (37 : ZMod 1029659401) ^ 16088428 := by rw [pow_add]
          _ = 114244832 := by rw [factor_0_23]; decide
      have factor_0_25 : (37 : ZMod 1029659401) ^ 64353712 = 414724903 := by
        calc
          (37 : ZMod 1029659401) ^ 64353712 = (37 : ZMod 1029659401) ^ (32176856 + 32176856) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 32176856 * (37 : ZMod 1029659401) ^ 32176856 := by rw [pow_add]
          _ = 414724903 := by rw [factor_0_24]; decide
      have factor_0_26 : (37 : ZMod 1029659401) ^ 128707425 = 275892696 := by
        calc
          (37 : ZMod 1029659401) ^ 128707425 = (37 : ZMod 1029659401) ^ (64353712 + 64353712 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 64353712 * (37 : ZMod 1029659401) ^ 64353712) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 275892696 := by rw [factor_0_25]; decide
      have factor_0_27 : (37 : ZMod 1029659401) ^ 257414850 = 295302785 := by
        calc
          (37 : ZMod 1029659401) ^ 257414850 = (37 : ZMod 1029659401) ^ (128707425 + 128707425) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 128707425 * (37 : ZMod 1029659401) ^ 128707425 := by rw [pow_add]
          _ = 295302785 := by rw [factor_0_26]; decide
      have factor_0_28 : (37 : ZMod 1029659401) ^ 514829700 = 1029659400 := by
        calc
          (37 : ZMod 1029659401) ^ 514829700 = (37 : ZMod 1029659401) ^ (257414850 + 257414850) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 257414850 * (37 : ZMod 1029659401) ^ 257414850 := by rw [pow_add]
          _ = 1029659400 := by rw [factor_0_27]; decide
      change (37 : ZMod 1029659401) ^ 514829700 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (37 : ZMod 1029659401) ^ 1 = 37 := by norm_num
      have factor_1_1 : (37 : ZMod 1029659401) ^ 2 = 1369 := by
        calc
          (37 : ZMod 1029659401) ^ 2 = (37 : ZMod 1029659401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 1 * (37 : ZMod 1029659401) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_1_0]; decide
      have factor_1_2 : (37 : ZMod 1029659401) ^ 5 = 69343957 := by
        calc
          (37 : ZMod 1029659401) ^ 5 = (37 : ZMod 1029659401) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 2 * (37 : ZMod 1029659401) ^ 2) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 69343957 := by rw [factor_1_1]; decide
      have factor_1_3 : (37 : ZMod 1029659401) ^ 10 = 834270977 := by
        calc
          (37 : ZMod 1029659401) ^ 10 = (37 : ZMod 1029659401) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 5 * (37 : ZMod 1029659401) ^ 5 := by rw [pow_add]
          _ = 834270977 := by rw [factor_1_2]; decide
      have factor_1_4 : (37 : ZMod 1029659401) ^ 20 = 956999821 := by
        calc
          (37 : ZMod 1029659401) ^ 20 = (37 : ZMod 1029659401) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 10 * (37 : ZMod 1029659401) ^ 10 := by rw [pow_add]
          _ = 956999821 := by rw [factor_1_3]; decide
      have factor_1_5 : (37 : ZMod 1029659401) ^ 40 = 732653060 := by
        calc
          (37 : ZMod 1029659401) ^ 40 = (37 : ZMod 1029659401) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 20 * (37 : ZMod 1029659401) ^ 20 := by rw [pow_add]
          _ = 732653060 := by rw [factor_1_4]; decide
      have factor_1_6 : (37 : ZMod 1029659401) ^ 81 = 159804473 := by
        calc
          (37 : ZMod 1029659401) ^ 81 = (37 : ZMod 1029659401) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 40 * (37 : ZMod 1029659401) ^ 40) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 159804473 := by rw [factor_1_5]; decide
      have factor_1_7 : (37 : ZMod 1029659401) ^ 163 = 1007636108 := by
        calc
          (37 : ZMod 1029659401) ^ 163 = (37 : ZMod 1029659401) ^ (81 + 81 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 81 * (37 : ZMod 1029659401) ^ 81) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 1007636108 := by rw [factor_1_6]; decide
      have factor_1_8 : (37 : ZMod 1029659401) ^ 327 = 171217606 := by
        calc
          (37 : ZMod 1029659401) ^ 327 = (37 : ZMod 1029659401) ^ (163 + 163 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 163 * (37 : ZMod 1029659401) ^ 163) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 171217606 := by rw [factor_1_7]; decide
      have factor_1_9 : (37 : ZMod 1029659401) ^ 654 = 790080602 := by
        calc
          (37 : ZMod 1029659401) ^ 654 = (37 : ZMod 1029659401) ^ (327 + 327) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 327 * (37 : ZMod 1029659401) ^ 327 := by rw [pow_add]
          _ = 790080602 := by rw [factor_1_8]; decide
      have factor_1_10 : (37 : ZMod 1029659401) ^ 1309 = 221603659 := by
        calc
          (37 : ZMod 1029659401) ^ 1309 = (37 : ZMod 1029659401) ^ (654 + 654 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 654 * (37 : ZMod 1029659401) ^ 654) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 221603659 := by rw [factor_1_9]; decide
      have factor_1_11 : (37 : ZMod 1029659401) ^ 2618 = 570444864 := by
        calc
          (37 : ZMod 1029659401) ^ 2618 = (37 : ZMod 1029659401) ^ (1309 + 1309) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 1309 * (37 : ZMod 1029659401) ^ 1309 := by rw [pow_add]
          _ = 570444864 := by rw [factor_1_10]; decide
      have factor_1_12 : (37 : ZMod 1029659401) ^ 5237 = 624605256 := by
        calc
          (37 : ZMod 1029659401) ^ 5237 = (37 : ZMod 1029659401) ^ (2618 + 2618 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 2618 * (37 : ZMod 1029659401) ^ 2618) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 624605256 := by rw [factor_1_11]; decide
      have factor_1_13 : (37 : ZMod 1029659401) ^ 10474 = 1015685779 := by
        calc
          (37 : ZMod 1029659401) ^ 10474 = (37 : ZMod 1029659401) ^ (5237 + 5237) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 5237 * (37 : ZMod 1029659401) ^ 5237 := by rw [pow_add]
          _ = 1015685779 := by rw [factor_1_12]; decide
      have factor_1_14 : (37 : ZMod 1029659401) ^ 20948 = 591971447 := by
        calc
          (37 : ZMod 1029659401) ^ 20948 = (37 : ZMod 1029659401) ^ (10474 + 10474) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 10474 * (37 : ZMod 1029659401) ^ 10474 := by rw [pow_add]
          _ = 591971447 := by rw [factor_1_13]; decide
      have factor_1_15 : (37 : ZMod 1029659401) ^ 41896 = 245096378 := by
        calc
          (37 : ZMod 1029659401) ^ 41896 = (37 : ZMod 1029659401) ^ (20948 + 20948) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 20948 * (37 : ZMod 1029659401) ^ 20948 := by rw [pow_add]
          _ = 245096378 := by rw [factor_1_14]; decide
      have factor_1_16 : (37 : ZMod 1029659401) ^ 83793 = 648063852 := by
        calc
          (37 : ZMod 1029659401) ^ 83793 = (37 : ZMod 1029659401) ^ (41896 + 41896 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 41896 * (37 : ZMod 1029659401) ^ 41896) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 648063852 := by rw [factor_1_15]; decide
      have factor_1_17 : (37 : ZMod 1029659401) ^ 167587 = 946805587 := by
        calc
          (37 : ZMod 1029659401) ^ 167587 = (37 : ZMod 1029659401) ^ (83793 + 83793 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 83793 * (37 : ZMod 1029659401) ^ 83793) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 946805587 := by rw [factor_1_16]; decide
      have factor_1_18 : (37 : ZMod 1029659401) ^ 335175 = 658193304 := by
        calc
          (37 : ZMod 1029659401) ^ 335175 = (37 : ZMod 1029659401) ^ (167587 + 167587 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 167587 * (37 : ZMod 1029659401) ^ 167587) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 658193304 := by rw [factor_1_17]; decide
      have factor_1_19 : (37 : ZMod 1029659401) ^ 670351 = 942469916 := by
        calc
          (37 : ZMod 1029659401) ^ 670351 = (37 : ZMod 1029659401) ^ (335175 + 335175 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 335175 * (37 : ZMod 1029659401) ^ 335175) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 942469916 := by rw [factor_1_18]; decide
      have factor_1_20 : (37 : ZMod 1029659401) ^ 1340702 = 47200195 := by
        calc
          (37 : ZMod 1029659401) ^ 1340702 = (37 : ZMod 1029659401) ^ (670351 + 670351) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 670351 * (37 : ZMod 1029659401) ^ 670351 := by rw [pow_add]
          _ = 47200195 := by rw [factor_1_19]; decide
      have factor_1_21 : (37 : ZMod 1029659401) ^ 2681404 = 836644741 := by
        calc
          (37 : ZMod 1029659401) ^ 2681404 = (37 : ZMod 1029659401) ^ (1340702 + 1340702) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 1340702 * (37 : ZMod 1029659401) ^ 1340702 := by rw [pow_add]
          _ = 836644741 := by rw [factor_1_20]; decide
      have factor_1_22 : (37 : ZMod 1029659401) ^ 5362809 = 429545558 := by
        calc
          (37 : ZMod 1029659401) ^ 5362809 = (37 : ZMod 1029659401) ^ (2681404 + 2681404 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 2681404 * (37 : ZMod 1029659401) ^ 2681404) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 429545558 := by rw [factor_1_21]; decide
      have factor_1_23 : (37 : ZMod 1029659401) ^ 10725618 = 432965982 := by
        calc
          (37 : ZMod 1029659401) ^ 10725618 = (37 : ZMod 1029659401) ^ (5362809 + 5362809) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 5362809 * (37 : ZMod 1029659401) ^ 5362809 := by rw [pow_add]
          _ = 432965982 := by rw [factor_1_22]; decide
      have factor_1_24 : (37 : ZMod 1029659401) ^ 21451237 = 219740735 := by
        calc
          (37 : ZMod 1029659401) ^ 21451237 = (37 : ZMod 1029659401) ^ (10725618 + 10725618 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 10725618 * (37 : ZMod 1029659401) ^ 10725618) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 219740735 := by rw [factor_1_23]; decide
      have factor_1_25 : (37 : ZMod 1029659401) ^ 42902475 = 895305265 := by
        calc
          (37 : ZMod 1029659401) ^ 42902475 = (37 : ZMod 1029659401) ^ (21451237 + 21451237 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 21451237 * (37 : ZMod 1029659401) ^ 21451237) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 895305265 := by rw [factor_1_24]; decide
      have factor_1_26 : (37 : ZMod 1029659401) ^ 85804950 = 765898624 := by
        calc
          (37 : ZMod 1029659401) ^ 85804950 = (37 : ZMod 1029659401) ^ (42902475 + 42902475) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 42902475 * (37 : ZMod 1029659401) ^ 42902475 := by rw [pow_add]
          _ = 765898624 := by rw [factor_1_25]; decide
      have factor_1_27 : (37 : ZMod 1029659401) ^ 171609900 = 742789543 := by
        calc
          (37 : ZMod 1029659401) ^ 171609900 = (37 : ZMod 1029659401) ^ (85804950 + 85804950) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 85804950 * (37 : ZMod 1029659401) ^ 85804950 := by rw [pow_add]
          _ = 742789543 := by rw [factor_1_26]; decide
      have factor_1_28 : (37 : ZMod 1029659401) ^ 343219800 = 742789542 := by
        calc
          (37 : ZMod 1029659401) ^ 343219800 = (37 : ZMod 1029659401) ^ (171609900 + 171609900) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 171609900 * (37 : ZMod 1029659401) ^ 171609900 := by rw [pow_add]
          _ = 742789542 := by rw [factor_1_27]; decide
      change (37 : ZMod 1029659401) ^ 343219800 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (37 : ZMod 1029659401) ^ 1 = 37 := by norm_num
      have factor_2_1 : (37 : ZMod 1029659401) ^ 3 = 50653 := by
        calc
          (37 : ZMod 1029659401) ^ 3 = (37 : ZMod 1029659401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 1 * (37 : ZMod 1029659401) ^ 1) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [factor_2_0]; decide
      have factor_2_2 : (37 : ZMod 1029659401) ^ 6 = 506407607 := by
        calc
          (37 : ZMod 1029659401) ^ 6 = (37 : ZMod 1029659401) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 3 * (37 : ZMod 1029659401) ^ 3 := by rw [pow_add]
          _ = 506407607 := by rw [factor_2_1]; decide
      have factor_2_3 : (37 : ZMod 1029659401) ^ 12 = 224691804 := by
        calc
          (37 : ZMod 1029659401) ^ 12 = (37 : ZMod 1029659401) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 6 * (37 : ZMod 1029659401) ^ 6 := by rw [pow_add]
          _ = 224691804 := by rw [factor_2_2]; decide
      have factor_2_4 : (37 : ZMod 1029659401) ^ 24 = 823307474 := by
        calc
          (37 : ZMod 1029659401) ^ 24 = (37 : ZMod 1029659401) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 12 * (37 : ZMod 1029659401) ^ 12 := by rw [pow_add]
          _ = 823307474 := by rw [factor_2_3]; decide
      have factor_2_5 : (37 : ZMod 1029659401) ^ 49 = 337581827 := by
        calc
          (37 : ZMod 1029659401) ^ 49 = (37 : ZMod 1029659401) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 24 * (37 : ZMod 1029659401) ^ 24) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 337581827 := by rw [factor_2_4]; decide
      have factor_2_6 : (37 : ZMod 1029659401) ^ 98 = 356752307 := by
        calc
          (37 : ZMod 1029659401) ^ 98 = (37 : ZMod 1029659401) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 49 * (37 : ZMod 1029659401) ^ 49 := by rw [pow_add]
          _ = 356752307 := by rw [factor_2_5]; decide
      have factor_2_7 : (37 : ZMod 1029659401) ^ 196 = 952050525 := by
        calc
          (37 : ZMod 1029659401) ^ 196 = (37 : ZMod 1029659401) ^ (98 + 98) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 98 * (37 : ZMod 1029659401) ^ 98 := by rw [pow_add]
          _ = 952050525 := by rw [factor_2_6]; decide
      have factor_2_8 : (37 : ZMod 1029659401) ^ 392 = 815517736 := by
        calc
          (37 : ZMod 1029659401) ^ 392 = (37 : ZMod 1029659401) ^ (196 + 196) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 196 * (37 : ZMod 1029659401) ^ 196 := by rw [pow_add]
          _ = 815517736 := by rw [factor_2_7]; decide
      have factor_2_9 : (37 : ZMod 1029659401) ^ 785 = 840538011 := by
        calc
          (37 : ZMod 1029659401) ^ 785 = (37 : ZMod 1029659401) ^ (392 + 392 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 392 * (37 : ZMod 1029659401) ^ 392) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 840538011 := by rw [factor_2_8]; decide
      have factor_2_10 : (37 : ZMod 1029659401) ^ 1571 = 458672300 := by
        calc
          (37 : ZMod 1029659401) ^ 1571 = (37 : ZMod 1029659401) ^ (785 + 785 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 785 * (37 : ZMod 1029659401) ^ 785) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 458672300 := by rw [factor_2_9]; decide
      have factor_2_11 : (37 : ZMod 1029659401) ^ 3142 = 204206938 := by
        calc
          (37 : ZMod 1029659401) ^ 3142 = (37 : ZMod 1029659401) ^ (1571 + 1571) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 1571 * (37 : ZMod 1029659401) ^ 1571 := by rw [pow_add]
          _ = 204206938 := by rw [factor_2_10]; decide
      have factor_2_12 : (37 : ZMod 1029659401) ^ 6284 = 904329356 := by
        calc
          (37 : ZMod 1029659401) ^ 6284 = (37 : ZMod 1029659401) ^ (3142 + 3142) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 3142 * (37 : ZMod 1029659401) ^ 3142 := by rw [pow_add]
          _ = 904329356 := by rw [factor_2_11]; decide
      have factor_2_13 : (37 : ZMod 1029659401) ^ 12569 = 727212960 := by
        calc
          (37 : ZMod 1029659401) ^ 12569 = (37 : ZMod 1029659401) ^ (6284 + 6284 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 6284 * (37 : ZMod 1029659401) ^ 6284) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 727212960 := by rw [factor_2_12]; decide
      have factor_2_14 : (37 : ZMod 1029659401) ^ 25138 = 957350942 := by
        calc
          (37 : ZMod 1029659401) ^ 25138 = (37 : ZMod 1029659401) ^ (12569 + 12569) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 12569 * (37 : ZMod 1029659401) ^ 12569 := by rw [pow_add]
          _ = 957350942 := by rw [factor_2_13]; decide
      have factor_2_15 : (37 : ZMod 1029659401) ^ 50276 = 622319776 := by
        calc
          (37 : ZMod 1029659401) ^ 50276 = (37 : ZMod 1029659401) ^ (25138 + 25138) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 25138 * (37 : ZMod 1029659401) ^ 25138 := by rw [pow_add]
          _ = 622319776 := by rw [factor_2_14]; decide
      have factor_2_16 : (37 : ZMod 1029659401) ^ 100552 = 66798951 := by
        calc
          (37 : ZMod 1029659401) ^ 100552 = (37 : ZMod 1029659401) ^ (50276 + 50276) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 50276 * (37 : ZMod 1029659401) ^ 50276 := by rw [pow_add]
          _ = 66798951 := by rw [factor_2_15]; decide
      have factor_2_17 : (37 : ZMod 1029659401) ^ 201105 = 614099792 := by
        calc
          (37 : ZMod 1029659401) ^ 201105 = (37 : ZMod 1029659401) ^ (100552 + 100552 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 100552 * (37 : ZMod 1029659401) ^ 100552) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 614099792 := by rw [factor_2_16]; decide
      have factor_2_18 : (37 : ZMod 1029659401) ^ 402210 = 906106233 := by
        calc
          (37 : ZMod 1029659401) ^ 402210 = (37 : ZMod 1029659401) ^ (201105 + 201105) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 201105 * (37 : ZMod 1029659401) ^ 201105 := by rw [pow_add]
          _ = 906106233 := by rw [factor_2_17]; decide
      have factor_2_19 : (37 : ZMod 1029659401) ^ 804421 = 271513084 := by
        calc
          (37 : ZMod 1029659401) ^ 804421 = (37 : ZMod 1029659401) ^ (402210 + 402210 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 402210 * (37 : ZMod 1029659401) ^ 402210) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 271513084 := by rw [factor_2_18]; decide
      have factor_2_20 : (37 : ZMod 1029659401) ^ 1608842 = 342873592 := by
        calc
          (37 : ZMod 1029659401) ^ 1608842 = (37 : ZMod 1029659401) ^ (804421 + 804421) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 804421 * (37 : ZMod 1029659401) ^ 804421 := by rw [pow_add]
          _ = 342873592 := by rw [factor_2_19]; decide
      have factor_2_21 : (37 : ZMod 1029659401) ^ 3217685 = 656765463 := by
        calc
          (37 : ZMod 1029659401) ^ 3217685 = (37 : ZMod 1029659401) ^ (1608842 + 1608842 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 1608842 * (37 : ZMod 1029659401) ^ 1608842) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 656765463 := by rw [factor_2_20]; decide
      have factor_2_22 : (37 : ZMod 1029659401) ^ 6435371 = 397780131 := by
        calc
          (37 : ZMod 1029659401) ^ 6435371 = (37 : ZMod 1029659401) ^ (3217685 + 3217685 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 3217685 * (37 : ZMod 1029659401) ^ 3217685) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 397780131 := by rw [factor_2_21]; decide
      have factor_2_23 : (37 : ZMod 1029659401) ^ 12870742 = 837346926 := by
        calc
          (37 : ZMod 1029659401) ^ 12870742 = (37 : ZMod 1029659401) ^ (6435371 + 6435371) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 6435371 * (37 : ZMod 1029659401) ^ 6435371 := by rw [pow_add]
          _ = 837346926 := by rw [factor_2_22]; decide
      have factor_2_24 : (37 : ZMod 1029659401) ^ 25741485 = 920526837 := by
        calc
          (37 : ZMod 1029659401) ^ 25741485 = (37 : ZMod 1029659401) ^ (12870742 + 12870742 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 12870742 * (37 : ZMod 1029659401) ^ 12870742) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 920526837 := by rw [factor_2_23]; decide
      have factor_2_25 : (37 : ZMod 1029659401) ^ 51482970 = 682757246 := by
        calc
          (37 : ZMod 1029659401) ^ 51482970 = (37 : ZMod 1029659401) ^ (25741485 + 25741485) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 25741485 * (37 : ZMod 1029659401) ^ 25741485 := by rw [pow_add]
          _ = 682757246 := by rw [factor_2_24]; decide
      have factor_2_26 : (37 : ZMod 1029659401) ^ 102965940 = 380052553 := by
        calc
          (37 : ZMod 1029659401) ^ 102965940 = (37 : ZMod 1029659401) ^ (51482970 + 51482970) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 51482970 * (37 : ZMod 1029659401) ^ 51482970 := by rw [pow_add]
          _ = 380052553 := by rw [factor_2_25]; decide
      have factor_2_27 : (37 : ZMod 1029659401) ^ 205931880 = 815083068 := by
        calc
          (37 : ZMod 1029659401) ^ 205931880 = (37 : ZMod 1029659401) ^ (102965940 + 102965940) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 102965940 * (37 : ZMod 1029659401) ^ 102965940 := by rw [pow_add]
          _ = 815083068 := by rw [factor_2_26]; decide
      change (37 : ZMod 1029659401) ^ 205931880 ≠ 1
      rw [factor_2_27]
      decide
    ·
      have factor_3_0 : (37 : ZMod 1029659401) ^ 1 = 37 := by norm_num
      have factor_3_1 : (37 : ZMod 1029659401) ^ 2 = 1369 := by
        calc
          (37 : ZMod 1029659401) ^ 2 = (37 : ZMod 1029659401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 1 * (37 : ZMod 1029659401) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_3_0]; decide
      have factor_3_2 : (37 : ZMod 1029659401) ^ 4 = 1874161 := by
        calc
          (37 : ZMod 1029659401) ^ 4 = (37 : ZMod 1029659401) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 2 * (37 : ZMod 1029659401) ^ 2 := by rw [pow_add]
          _ = 1874161 := by rw [factor_3_1]; decide
      have factor_3_3 : (37 : ZMod 1029659401) ^ 8 = 311237110 := by
        calc
          (37 : ZMod 1029659401) ^ 8 = (37 : ZMod 1029659401) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 4 * (37 : ZMod 1029659401) ^ 4 := by rw [pow_add]
          _ = 311237110 := by rw [factor_3_2]; decide
      have factor_3_4 : (37 : ZMod 1029659401) ^ 17 = 629059822 := by
        calc
          (37 : ZMod 1029659401) ^ 17 = (37 : ZMod 1029659401) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 8 * (37 : ZMod 1029659401) ^ 8) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 629059822 := by rw [factor_3_3]; decide
      have factor_3_5 : (37 : ZMod 1029659401) ^ 35 = 466943236 := by
        calc
          (37 : ZMod 1029659401) ^ 35 = (37 : ZMod 1029659401) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 17 * (37 : ZMod 1029659401) ^ 17) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 466943236 := by rw [factor_3_4]; decide
      have factor_3_6 : (37 : ZMod 1029659401) ^ 70 = 988963251 := by
        calc
          (37 : ZMod 1029659401) ^ 70 = (37 : ZMod 1029659401) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 35 * (37 : ZMod 1029659401) ^ 35 := by rw [pow_add]
          _ = 988963251 := by rw [factor_3_5]; decide
      have factor_3_7 : (37 : ZMod 1029659401) ^ 140 = 368096030 := by
        calc
          (37 : ZMod 1029659401) ^ 140 = (37 : ZMod 1029659401) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 70 * (37 : ZMod 1029659401) ^ 70 := by rw [pow_add]
          _ = 368096030 := by rw [factor_3_6]; decide
      have factor_3_8 : (37 : ZMod 1029659401) ^ 280 = 701581546 := by
        calc
          (37 : ZMod 1029659401) ^ 280 = (37 : ZMod 1029659401) ^ (140 + 140) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 140 * (37 : ZMod 1029659401) ^ 140 := by rw [pow_add]
          _ = 701581546 := by rw [factor_3_7]; decide
      have factor_3_9 : (37 : ZMod 1029659401) ^ 561 = 614672897 := by
        calc
          (37 : ZMod 1029659401) ^ 561 = (37 : ZMod 1029659401) ^ (280 + 280 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 280 * (37 : ZMod 1029659401) ^ 280) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 614672897 := by rw [factor_3_8]; decide
      have factor_3_10 : (37 : ZMod 1029659401) ^ 1122 = 694250247 := by
        calc
          (37 : ZMod 1029659401) ^ 1122 = (37 : ZMod 1029659401) ^ (561 + 561) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 561 * (37 : ZMod 1029659401) ^ 561 := by rw [pow_add]
          _ = 694250247 := by rw [factor_3_9]; decide
      have factor_3_11 : (37 : ZMod 1029659401) ^ 2244 = 478327565 := by
        calc
          (37 : ZMod 1029659401) ^ 2244 = (37 : ZMod 1029659401) ^ (1122 + 1122) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 1122 * (37 : ZMod 1029659401) ^ 1122 := by rw [pow_add]
          _ = 478327565 := by rw [factor_3_10]; decide
      have factor_3_12 : (37 : ZMod 1029659401) ^ 4488 = 632266485 := by
        calc
          (37 : ZMod 1029659401) ^ 4488 = (37 : ZMod 1029659401) ^ (2244 + 2244) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 2244 * (37 : ZMod 1029659401) ^ 2244 := by rw [pow_add]
          _ = 632266485 := by rw [factor_3_11]; decide
      have factor_3_13 : (37 : ZMod 1029659401) ^ 8977 = 657986597 := by
        calc
          (37 : ZMod 1029659401) ^ 8977 = (37 : ZMod 1029659401) ^ (4488 + 4488 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 4488 * (37 : ZMod 1029659401) ^ 4488) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 657986597 := by rw [factor_3_12]; decide
      have factor_3_14 : (37 : ZMod 1029659401) ^ 17955 = 688019448 := by
        calc
          (37 : ZMod 1029659401) ^ 17955 = (37 : ZMod 1029659401) ^ (8977 + 8977 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 8977 * (37 : ZMod 1029659401) ^ 8977) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 688019448 := by rw [factor_3_13]; decide
      have factor_3_15 : (37 : ZMod 1029659401) ^ 35911 = 401092408 := by
        calc
          (37 : ZMod 1029659401) ^ 35911 = (37 : ZMod 1029659401) ^ (17955 + 17955 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 17955 * (37 : ZMod 1029659401) ^ 17955) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 401092408 := by rw [factor_3_14]; decide
      have factor_3_16 : (37 : ZMod 1029659401) ^ 71823 = 291592185 := by
        calc
          (37 : ZMod 1029659401) ^ 71823 = (37 : ZMod 1029659401) ^ (35911 + 35911 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 35911 * (37 : ZMod 1029659401) ^ 35911) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 291592185 := by rw [factor_3_15]; decide
      have factor_3_17 : (37 : ZMod 1029659401) ^ 143646 = 246411202 := by
        calc
          (37 : ZMod 1029659401) ^ 143646 = (37 : ZMod 1029659401) ^ (71823 + 71823) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 71823 * (37 : ZMod 1029659401) ^ 71823 := by rw [pow_add]
          _ = 246411202 := by rw [factor_3_16]; decide
      have factor_3_18 : (37 : ZMod 1029659401) ^ 287293 = 561384552 := by
        calc
          (37 : ZMod 1029659401) ^ 287293 = (37 : ZMod 1029659401) ^ (143646 + 143646 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 143646 * (37 : ZMod 1029659401) ^ 143646) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 561384552 := by rw [factor_3_17]; decide
      have factor_3_19 : (37 : ZMod 1029659401) ^ 574586 = 185441079 := by
        calc
          (37 : ZMod 1029659401) ^ 574586 = (37 : ZMod 1029659401) ^ (287293 + 287293) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 287293 * (37 : ZMod 1029659401) ^ 287293 := by rw [pow_add]
          _ = 185441079 := by rw [factor_3_18]; decide
      have factor_3_20 : (37 : ZMod 1029659401) ^ 1149173 = 63572458 := by
        calc
          (37 : ZMod 1029659401) ^ 1149173 = (37 : ZMod 1029659401) ^ (574586 + 574586 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 574586 * (37 : ZMod 1029659401) ^ 574586) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 63572458 := by rw [factor_3_19]; decide
      have factor_3_21 : (37 : ZMod 1029659401) ^ 2298346 = 1021541922 := by
        calc
          (37 : ZMod 1029659401) ^ 2298346 = (37 : ZMod 1029659401) ^ (1149173 + 1149173) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 1149173 * (37 : ZMod 1029659401) ^ 1149173 := by rw [pow_add]
          _ = 1021541922 := by rw [factor_3_20]; decide
      have factor_3_22 : (37 : ZMod 1029659401) ^ 4596693 = 826860888 := by
        calc
          (37 : ZMod 1029659401) ^ 4596693 = (37 : ZMod 1029659401) ^ (2298346 + 2298346 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 2298346 * (37 : ZMod 1029659401) ^ 2298346) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 826860888 := by rw [factor_3_21]; decide
      have factor_3_23 : (37 : ZMod 1029659401) ^ 9193387 = 681666373 := by
        calc
          (37 : ZMod 1029659401) ^ 9193387 = (37 : ZMod 1029659401) ^ (4596693 + 4596693 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 4596693 * (37 : ZMod 1029659401) ^ 4596693) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 681666373 := by rw [factor_3_22]; decide
      have factor_3_24 : (37 : ZMod 1029659401) ^ 18386775 = 306002874 := by
        calc
          (37 : ZMod 1029659401) ^ 18386775 = (37 : ZMod 1029659401) ^ (9193387 + 9193387 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 9193387 * (37 : ZMod 1029659401) ^ 9193387) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 306002874 := by rw [factor_3_23]; decide
      have factor_3_25 : (37 : ZMod 1029659401) ^ 36773550 = 635409559 := by
        calc
          (37 : ZMod 1029659401) ^ 36773550 = (37 : ZMod 1029659401) ^ (18386775 + 18386775) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 18386775 * (37 : ZMod 1029659401) ^ 18386775 := by rw [pow_add]
          _ = 635409559 := by rw [factor_3_24]; decide
      have factor_3_26 : (37 : ZMod 1029659401) ^ 73547100 = 811358482 := by
        calc
          (37 : ZMod 1029659401) ^ 73547100 = (37 : ZMod 1029659401) ^ (36773550 + 36773550) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 36773550 * (37 : ZMod 1029659401) ^ 36773550 := by rw [pow_add]
          _ = 811358482 := by rw [factor_3_25]; decide
      have factor_3_27 : (37 : ZMod 1029659401) ^ 147094200 = 725688184 := by
        calc
          (37 : ZMod 1029659401) ^ 147094200 = (37 : ZMod 1029659401) ^ (73547100 + 73547100) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 73547100 * (37 : ZMod 1029659401) ^ 73547100 := by rw [pow_add]
          _ = 725688184 := by rw [factor_3_26]; decide
      change (37 : ZMod 1029659401) ^ 147094200 ≠ 1
      rw [factor_3_27]
      decide
    ·
      have factor_4_0 : (37 : ZMod 1029659401) ^ 1 = 37 := by norm_num
      have factor_4_1 : (37 : ZMod 1029659401) ^ 2 = 1369 := by
        calc
          (37 : ZMod 1029659401) ^ 2 = (37 : ZMod 1029659401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 1 * (37 : ZMod 1029659401) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_4_0]; decide
      have factor_4_2 : (37 : ZMod 1029659401) ^ 5 = 69343957 := by
        calc
          (37 : ZMod 1029659401) ^ 5 = (37 : ZMod 1029659401) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 2 * (37 : ZMod 1029659401) ^ 2) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 69343957 := by rw [factor_4_1]; decide
      have factor_4_3 : (37 : ZMod 1029659401) ^ 11 = 1007903520 := by
        calc
          (37 : ZMod 1029659401) ^ 11 = (37 : ZMod 1029659401) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 5 * (37 : ZMod 1029659401) ^ 5) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 1007903520 := by rw [factor_4_2]; decide
      have factor_4_4 : (37 : ZMod 1029659401) ^ 22 = 405996877 := by
        calc
          (37 : ZMod 1029659401) ^ 22 = (37 : ZMod 1029659401) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 11 * (37 : ZMod 1029659401) ^ 11 := by rw [pow_add]
          _ = 405996877 := by rw [factor_4_3]; decide
      have factor_4_5 : (37 : ZMod 1029659401) ^ 44 = 289763303 := by
        calc
          (37 : ZMod 1029659401) ^ 44 = (37 : ZMod 1029659401) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 22 * (37 : ZMod 1029659401) ^ 22 := by rw [pow_add]
          _ = 289763303 := by rw [factor_4_4]; decide
      have factor_4_6 : (37 : ZMod 1029659401) ^ 89 = 712609828 := by
        calc
          (37 : ZMod 1029659401) ^ 89 = (37 : ZMod 1029659401) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 44 * (37 : ZMod 1029659401) ^ 44) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 712609828 := by rw [factor_4_5]; decide
      have factor_4_7 : (37 : ZMod 1029659401) ^ 178 = 674377795 := by
        calc
          (37 : ZMod 1029659401) ^ 178 = (37 : ZMod 1029659401) ^ (89 + 89) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 89 * (37 : ZMod 1029659401) ^ 89 := by rw [pow_add]
          _ = 674377795 := by rw [factor_4_6]; decide
      have factor_4_8 : (37 : ZMod 1029659401) ^ 357 = 315381022 := by
        calc
          (37 : ZMod 1029659401) ^ 357 = (37 : ZMod 1029659401) ^ (178 + 178 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 178 * (37 : ZMod 1029659401) ^ 178) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 315381022 := by rw [factor_4_7]; decide
      have factor_4_9 : (37 : ZMod 1029659401) ^ 714 = 291137196 := by
        calc
          (37 : ZMod 1029659401) ^ 714 = (37 : ZMod 1029659401) ^ (357 + 357) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 357 * (37 : ZMod 1029659401) ^ 357 := by rw [pow_add]
          _ = 291137196 := by rw [factor_4_8]; decide
      have factor_4_10 : (37 : ZMod 1029659401) ^ 1428 = 24518091 := by
        calc
          (37 : ZMod 1029659401) ^ 1428 = (37 : ZMod 1029659401) ^ (714 + 714) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 714 * (37 : ZMod 1029659401) ^ 714 := by rw [pow_add]
          _ = 24518091 := by rw [factor_4_9]; decide
      have factor_4_11 : (37 : ZMod 1029659401) ^ 2856 = 5133060 := by
        calc
          (37 : ZMod 1029659401) ^ 2856 = (37 : ZMod 1029659401) ^ (1428 + 1428) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 1428 * (37 : ZMod 1029659401) ^ 1428 := by rw [pow_add]
          _ = 5133060 := by rw [factor_4_10]; decide
      have factor_4_12 : (37 : ZMod 1029659401) ^ 5713 = 614489395 := by
        calc
          (37 : ZMod 1029659401) ^ 5713 = (37 : ZMod 1029659401) ^ (2856 + 2856 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 2856 * (37 : ZMod 1029659401) ^ 2856) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 614489395 := by rw [factor_4_11]; decide
      have factor_4_13 : (37 : ZMod 1029659401) ^ 11426 = 25089119 := by
        calc
          (37 : ZMod 1029659401) ^ 11426 = (37 : ZMod 1029659401) ^ (5713 + 5713) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 5713 * (37 : ZMod 1029659401) ^ 5713 := by rw [pow_add]
          _ = 25089119 := by rw [factor_4_12]; decide
      have factor_4_14 : (37 : ZMod 1029659401) ^ 22852 = 151264029 := by
        calc
          (37 : ZMod 1029659401) ^ 22852 = (37 : ZMod 1029659401) ^ (11426 + 11426) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 11426 * (37 : ZMod 1029659401) ^ 11426 := by rw [pow_add]
          _ = 151264029 := by rw [factor_4_13]; decide
      have factor_4_15 : (37 : ZMod 1029659401) ^ 45705 = 105752149 := by
        calc
          (37 : ZMod 1029659401) ^ 45705 = (37 : ZMod 1029659401) ^ (22852 + 22852 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 22852 * (37 : ZMod 1029659401) ^ 22852) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 105752149 := by rw [factor_4_14]; decide
      have factor_4_16 : (37 : ZMod 1029659401) ^ 91411 = 90230557 := by
        calc
          (37 : ZMod 1029659401) ^ 91411 = (37 : ZMod 1029659401) ^ (45705 + 45705 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 45705 * (37 : ZMod 1029659401) ^ 45705) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 90230557 := by rw [factor_4_15]; decide
      have factor_4_17 : (37 : ZMod 1029659401) ^ 182823 = 801326101 := by
        calc
          (37 : ZMod 1029659401) ^ 182823 = (37 : ZMod 1029659401) ^ (91411 + 91411 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 91411 * (37 : ZMod 1029659401) ^ 91411) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 801326101 := by rw [factor_4_16]; decide
      have factor_4_18 : (37 : ZMod 1029659401) ^ 365646 = 524922888 := by
        calc
          (37 : ZMod 1029659401) ^ 365646 = (37 : ZMod 1029659401) ^ (182823 + 182823) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 182823 * (37 : ZMod 1029659401) ^ 182823 := by rw [pow_add]
          _ = 524922888 := by rw [factor_4_17]; decide
      have factor_4_19 : (37 : ZMod 1029659401) ^ 731292 = 764338569 := by
        calc
          (37 : ZMod 1029659401) ^ 731292 = (37 : ZMod 1029659401) ^ (365646 + 365646) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 365646 * (37 : ZMod 1029659401) ^ 365646 := by rw [pow_add]
          _ = 764338569 := by rw [factor_4_18]; decide
      have factor_4_20 : (37 : ZMod 1029659401) ^ 1462584 = 553629017 := by
        calc
          (37 : ZMod 1029659401) ^ 1462584 = (37 : ZMod 1029659401) ^ (731292 + 731292) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 731292 * (37 : ZMod 1029659401) ^ 731292 := by rw [pow_add]
          _ = 553629017 := by rw [factor_4_19]; decide
      have factor_4_21 : (37 : ZMod 1029659401) ^ 2925168 = 977024099 := by
        calc
          (37 : ZMod 1029659401) ^ 2925168 = (37 : ZMod 1029659401) ^ (1462584 + 1462584) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 1462584 * (37 : ZMod 1029659401) ^ 1462584 := by rw [pow_add]
          _ = 977024099 := by rw [factor_4_20]; decide
      have factor_4_22 : (37 : ZMod 1029659401) ^ 5850337 = 753622510 := by
        calc
          (37 : ZMod 1029659401) ^ 5850337 = (37 : ZMod 1029659401) ^ (2925168 + 2925168 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 2925168 * (37 : ZMod 1029659401) ^ 2925168) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 753622510 := by rw [factor_4_21]; decide
      have factor_4_23 : (37 : ZMod 1029659401) ^ 11700675 = 440440598 := by
        calc
          (37 : ZMod 1029659401) ^ 11700675 = (37 : ZMod 1029659401) ^ (5850337 + 5850337 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 5850337 * (37 : ZMod 1029659401) ^ 5850337) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 440440598 := by rw [factor_4_22]; decide
      have factor_4_24 : (37 : ZMod 1029659401) ^ 23401350 = 667489118 := by
        calc
          (37 : ZMod 1029659401) ^ 23401350 = (37 : ZMod 1029659401) ^ (11700675 + 11700675) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 11700675 * (37 : ZMod 1029659401) ^ 11700675 := by rw [pow_add]
          _ = 667489118 := by rw [factor_4_23]; decide
      have factor_4_25 : (37 : ZMod 1029659401) ^ 46802700 = 534869658 := by
        calc
          (37 : ZMod 1029659401) ^ 46802700 = (37 : ZMod 1029659401) ^ (23401350 + 23401350) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 23401350 * (37 : ZMod 1029659401) ^ 23401350 := by rw [pow_add]
          _ = 534869658 := by rw [factor_4_24]; decide
      have factor_4_26 : (37 : ZMod 1029659401) ^ 93605400 = 553355525 := by
        calc
          (37 : ZMod 1029659401) ^ 93605400 = (37 : ZMod 1029659401) ^ (46802700 + 46802700) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 46802700 * (37 : ZMod 1029659401) ^ 46802700 := by rw [pow_add]
          _ = 553355525 := by rw [factor_4_25]; decide
      change (37 : ZMod 1029659401) ^ 93605400 ≠ 1
      rw [factor_4_26]
      decide
    ·
      have factor_5_0 : (37 : ZMod 1029659401) ^ 1 = 37 := by norm_num
      have factor_5_1 : (37 : ZMod 1029659401) ^ 3 = 50653 := by
        calc
          (37 : ZMod 1029659401) ^ 3 = (37 : ZMod 1029659401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 1 * (37 : ZMod 1029659401) ^ 1) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [factor_5_0]; decide
      have factor_5_2 : (37 : ZMod 1029659401) ^ 7 = 203212241 := by
        calc
          (37 : ZMod 1029659401) ^ 7 = (37 : ZMod 1029659401) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 3 * (37 : ZMod 1029659401) ^ 3) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 203212241 := by rw [factor_5_1]; decide
      have factor_5_3 : (37 : ZMod 1029659401) ^ 14 = 764578178 := by
        calc
          (37 : ZMod 1029659401) ^ 14 = (37 : ZMod 1029659401) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 7 * (37 : ZMod 1029659401) ^ 7 := by rw [pow_add]
          _ = 764578178 := by rw [factor_5_2]; decide
      have factor_5_4 : (37 : ZMod 1029659401) ^ 28 = 248179150 := by
        calc
          (37 : ZMod 1029659401) ^ 28 = (37 : ZMod 1029659401) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 14 * (37 : ZMod 1029659401) ^ 14 := by rw [pow_add]
          _ = 248179150 := by rw [factor_5_3]; decide
      have factor_5_5 : (37 : ZMod 1029659401) ^ 57 = 397539668 := by
        calc
          (37 : ZMod 1029659401) ^ 57 = (37 : ZMod 1029659401) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 28 * (37 : ZMod 1029659401) ^ 28) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 397539668 := by rw [factor_5_4]; decide
      have factor_5_6 : (37 : ZMod 1029659401) ^ 115 = 116067001 := by
        calc
          (37 : ZMod 1029659401) ^ 115 = (37 : ZMod 1029659401) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 57 * (37 : ZMod 1029659401) ^ 57) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 116067001 := by rw [factor_5_5]; decide
      have factor_5_7 : (37 : ZMod 1029659401) ^ 231 = 140887339 := by
        calc
          (37 : ZMod 1029659401) ^ 231 = (37 : ZMod 1029659401) ^ (115 + 115 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 115 * (37 : ZMod 1029659401) ^ 115) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 140887339 := by rw [factor_5_6]; decide
      have factor_5_8 : (37 : ZMod 1029659401) ^ 462 = 691933238 := by
        calc
          (37 : ZMod 1029659401) ^ 462 = (37 : ZMod 1029659401) ^ (231 + 231) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 231 * (37 : ZMod 1029659401) ^ 231 := by rw [pow_add]
          _ = 691933238 := by rw [factor_5_7]; decide
      have factor_5_9 : (37 : ZMod 1029659401) ^ 924 = 962920084 := by
        calc
          (37 : ZMod 1029659401) ^ 924 = (37 : ZMod 1029659401) ^ (462 + 462) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 462 * (37 : ZMod 1029659401) ^ 462 := by rw [pow_add]
          _ = 962920084 := by rw [factor_5_8]; decide
      have factor_5_10 : (37 : ZMod 1029659401) ^ 1848 = 788361055 := by
        calc
          (37 : ZMod 1029659401) ^ 1848 = (37 : ZMod 1029659401) ^ (924 + 924) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 924 * (37 : ZMod 1029659401) ^ 924 := by rw [pow_add]
          _ = 788361055 := by rw [factor_5_9]; decide
      have factor_5_11 : (37 : ZMod 1029659401) ^ 3696 = 279219996 := by
        calc
          (37 : ZMod 1029659401) ^ 3696 = (37 : ZMod 1029659401) ^ (1848 + 1848) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 1848 * (37 : ZMod 1029659401) ^ 1848 := by rw [pow_add]
          _ = 279219996 := by rw [factor_5_10]; decide
      have factor_5_12 : (37 : ZMod 1029659401) ^ 7393 = 439771993 := by
        calc
          (37 : ZMod 1029659401) ^ 7393 = (37 : ZMod 1029659401) ^ (3696 + 3696 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 3696 * (37 : ZMod 1029659401) ^ 3696) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 439771993 := by rw [factor_5_11]; decide
      have factor_5_13 : (37 : ZMod 1029659401) ^ 14787 = 315349814 := by
        calc
          (37 : ZMod 1029659401) ^ 14787 = (37 : ZMod 1029659401) ^ (7393 + 7393 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 7393 * (37 : ZMod 1029659401) ^ 7393) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 315349814 := by rw [factor_5_12]; decide
      have factor_5_14 : (37 : ZMod 1029659401) ^ 29574 = 441976225 := by
        calc
          (37 : ZMod 1029659401) ^ 29574 = (37 : ZMod 1029659401) ^ (14787 + 14787) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 14787 * (37 : ZMod 1029659401) ^ 14787 := by rw [pow_add]
          _ = 441976225 := by rw [factor_5_13]; decide
      have factor_5_15 : (37 : ZMod 1029659401) ^ 59148 = 74984708 := by
        calc
          (37 : ZMod 1029659401) ^ 59148 = (37 : ZMod 1029659401) ^ (29574 + 29574) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 29574 * (37 : ZMod 1029659401) ^ 29574 := by rw [pow_add]
          _ = 74984708 := by rw [factor_5_14]; decide
      have factor_5_16 : (37 : ZMod 1029659401) ^ 118297 = 368604639 := by
        calc
          (37 : ZMod 1029659401) ^ 118297 = (37 : ZMod 1029659401) ^ (59148 + 59148 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 59148 * (37 : ZMod 1029659401) ^ 59148) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 368604639 := by rw [factor_5_15]; decide
      have factor_5_17 : (37 : ZMod 1029659401) ^ 236594 = 236117067 := by
        calc
          (37 : ZMod 1029659401) ^ 236594 = (37 : ZMod 1029659401) ^ (118297 + 118297) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 118297 * (37 : ZMod 1029659401) ^ 118297 := by rw [pow_add]
          _ = 236117067 := by rw [factor_5_16]; decide
      have factor_5_18 : (37 : ZMod 1029659401) ^ 473189 = 475818519 := by
        calc
          (37 : ZMod 1029659401) ^ 473189 = (37 : ZMod 1029659401) ^ (236594 + 236594 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 236594 * (37 : ZMod 1029659401) ^ 236594) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 475818519 := by rw [factor_5_17]; decide
      have factor_5_19 : (37 : ZMod 1029659401) ^ 946378 = 421513458 := by
        calc
          (37 : ZMod 1029659401) ^ 946378 = (37 : ZMod 1029659401) ^ (473189 + 473189) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 473189 * (37 : ZMod 1029659401) ^ 473189 := by rw [pow_add]
          _ = 421513458 := by rw [factor_5_18]; decide
      have factor_5_20 : (37 : ZMod 1029659401) ^ 1892756 = 692619668 := by
        calc
          (37 : ZMod 1029659401) ^ 1892756 = (37 : ZMod 1029659401) ^ (946378 + 946378) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 946378 * (37 : ZMod 1029659401) ^ 946378 := by rw [pow_add]
          _ = 692619668 := by rw [factor_5_19]; decide
      have factor_5_21 : (37 : ZMod 1029659401) ^ 3785512 = 304896441 := by
        calc
          (37 : ZMod 1029659401) ^ 3785512 = (37 : ZMod 1029659401) ^ (1892756 + 1892756) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 1892756 * (37 : ZMod 1029659401) ^ 1892756 := by rw [pow_add]
          _ = 304896441 := by rw [factor_5_20]; decide
      have factor_5_22 : (37 : ZMod 1029659401) ^ 7571025 = 880586069 := by
        calc
          (37 : ZMod 1029659401) ^ 7571025 = (37 : ZMod 1029659401) ^ (3785512 + 3785512 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 3785512 * (37 : ZMod 1029659401) ^ 3785512) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 880586069 := by rw [factor_5_21]; decide
      have factor_5_23 : (37 : ZMod 1029659401) ^ 15142050 = 558815697 := by
        calc
          (37 : ZMod 1029659401) ^ 15142050 = (37 : ZMod 1029659401) ^ (7571025 + 7571025) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 7571025 * (37 : ZMod 1029659401) ^ 7571025 := by rw [pow_add]
          _ = 558815697 := by rw [factor_5_22]; decide
      have factor_5_24 : (37 : ZMod 1029659401) ^ 30284100 = 548465726 := by
        calc
          (37 : ZMod 1029659401) ^ 30284100 = (37 : ZMod 1029659401) ^ (15142050 + 15142050) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 15142050 * (37 : ZMod 1029659401) ^ 15142050 := by rw [pow_add]
          _ = 548465726 := by rw [factor_5_23]; decide
      have factor_5_25 : (37 : ZMod 1029659401) ^ 60568200 = 441478208 := by
        calc
          (37 : ZMod 1029659401) ^ 60568200 = (37 : ZMod 1029659401) ^ (30284100 + 30284100) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 30284100 * (37 : ZMod 1029659401) ^ 30284100 := by rw [pow_add]
          _ = 441478208 := by rw [factor_5_24]; decide
      change (37 : ZMod 1029659401) ^ 60568200 ≠ 1
      rw [factor_5_25]
      decide
    ·
      have factor_6_0 : (37 : ZMod 1029659401) ^ 1 = 37 := by norm_num
      have factor_6_1 : (37 : ZMod 1029659401) ^ 3 = 50653 := by
        calc
          (37 : ZMod 1029659401) ^ 3 = (37 : ZMod 1029659401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 1 * (37 : ZMod 1029659401) ^ 1) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [factor_6_0]; decide
      have factor_6_2 : (37 : ZMod 1029659401) ^ 6 = 506407607 := by
        calc
          (37 : ZMod 1029659401) ^ 6 = (37 : ZMod 1029659401) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 3 * (37 : ZMod 1029659401) ^ 3 := by rw [pow_add]
          _ = 506407607 := by rw [factor_6_1]; decide
      have factor_6_3 : (37 : ZMod 1029659401) ^ 12 = 224691804 := by
        calc
          (37 : ZMod 1029659401) ^ 12 = (37 : ZMod 1029659401) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 6 * (37 : ZMod 1029659401) ^ 6 := by rw [pow_add]
          _ = 224691804 := by rw [factor_6_2]; decide
      have factor_6_4 : (37 : ZMod 1029659401) ^ 25 = 602253909 := by
        calc
          (37 : ZMod 1029659401) ^ 25 = (37 : ZMod 1029659401) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 12 * (37 : ZMod 1029659401) ^ 12) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 602253909 := by rw [factor_6_3]; decide
      have factor_6_5 : (37 : ZMod 1029659401) ^ 51 = 862109515 := by
        calc
          (37 : ZMod 1029659401) ^ 51 = (37 : ZMod 1029659401) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 25 * (37 : ZMod 1029659401) ^ 25) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 862109515 := by rw [factor_6_4]; decide
      have factor_6_6 : (37 : ZMod 1029659401) ^ 103 = 304304180 := by
        calc
          (37 : ZMod 1029659401) ^ 103 = (37 : ZMod 1029659401) ^ (51 + 51 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 51 * (37 : ZMod 1029659401) ^ 51) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 304304180 := by rw [factor_6_5]; decide
      have factor_6_7 : (37 : ZMod 1029659401) ^ 206 = 628431745 := by
        calc
          (37 : ZMod 1029659401) ^ 206 = (37 : ZMod 1029659401) ^ (103 + 103) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 103 * (37 : ZMod 1029659401) ^ 103 := by rw [pow_add]
          _ = 628431745 := by rw [factor_6_6]; decide
      have factor_6_8 : (37 : ZMod 1029659401) ^ 413 = 197860149 := by
        calc
          (37 : ZMod 1029659401) ^ 413 = (37 : ZMod 1029659401) ^ (206 + 206 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 206 * (37 : ZMod 1029659401) ^ 206) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 197860149 := by rw [factor_6_7]; decide
      have factor_6_9 : (37 : ZMod 1029659401) ^ 826 = 692916642 := by
        calc
          (37 : ZMod 1029659401) ^ 826 = (37 : ZMod 1029659401) ^ (413 + 413) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 413 * (37 : ZMod 1029659401) ^ 413 := by rw [pow_add]
          _ = 692916642 := by rw [factor_6_8]; decide
      have factor_6_10 : (37 : ZMod 1029659401) ^ 1653 = 993841099 := by
        calc
          (37 : ZMod 1029659401) ^ 1653 = (37 : ZMod 1029659401) ^ (826 + 826 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 826 * (37 : ZMod 1029659401) ^ 826) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 993841099 := by rw [factor_6_9]; decide
      have factor_6_11 : (37 : ZMod 1029659401) ^ 3307 = 537531723 := by
        calc
          (37 : ZMod 1029659401) ^ 3307 = (37 : ZMod 1029659401) ^ (1653 + 1653 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 1653 * (37 : ZMod 1029659401) ^ 1653) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 537531723 := by rw [factor_6_10]; decide
      have factor_6_12 : (37 : ZMod 1029659401) ^ 6615 = 958077442 := by
        calc
          (37 : ZMod 1029659401) ^ 6615 = (37 : ZMod 1029659401) ^ (3307 + 3307 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 3307 * (37 : ZMod 1029659401) ^ 3307) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 958077442 := by rw [factor_6_11]; decide
      have factor_6_13 : (37 : ZMod 1029659401) ^ 13230 = 404329301 := by
        calc
          (37 : ZMod 1029659401) ^ 13230 = (37 : ZMod 1029659401) ^ (6615 + 6615) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 6615 * (37 : ZMod 1029659401) ^ 6615 := by rw [pow_add]
          _ = 404329301 := by rw [factor_6_12]; decide
      have factor_6_14 : (37 : ZMod 1029659401) ^ 26461 = 916177266 := by
        calc
          (37 : ZMod 1029659401) ^ 26461 = (37 : ZMod 1029659401) ^ (13230 + 13230 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 13230 * (37 : ZMod 1029659401) ^ 13230) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 916177266 := by rw [factor_6_13]; decide
      have factor_6_15 : (37 : ZMod 1029659401) ^ 52922 = 806573188 := by
        calc
          (37 : ZMod 1029659401) ^ 52922 = (37 : ZMod 1029659401) ^ (26461 + 26461) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 26461 * (37 : ZMod 1029659401) ^ 26461 := by rw [pow_add]
          _ = 806573188 := by rw [factor_6_14]; decide
      have factor_6_16 : (37 : ZMod 1029659401) ^ 105844 = 819709266 := by
        calc
          (37 : ZMod 1029659401) ^ 105844 = (37 : ZMod 1029659401) ^ (52922 + 52922) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 52922 * (37 : ZMod 1029659401) ^ 52922 := by rw [pow_add]
          _ = 819709266 := by rw [factor_6_15]; decide
      have factor_6_17 : (37 : ZMod 1029659401) ^ 211689 = 693942634 := by
        calc
          (37 : ZMod 1029659401) ^ 211689 = (37 : ZMod 1029659401) ^ (105844 + 105844 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 105844 * (37 : ZMod 1029659401) ^ 105844) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 693942634 := by rw [factor_6_16]; decide
      have factor_6_18 : (37 : ZMod 1029659401) ^ 423379 = 715331977 := by
        calc
          (37 : ZMod 1029659401) ^ 423379 = (37 : ZMod 1029659401) ^ (211689 + 211689 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 211689 * (37 : ZMod 1029659401) ^ 211689) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 715331977 := by rw [factor_6_17]; decide
      have factor_6_19 : (37 : ZMod 1029659401) ^ 846759 = 506122743 := by
        calc
          (37 : ZMod 1029659401) ^ 846759 = (37 : ZMod 1029659401) ^ (423379 + 423379 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 423379 * (37 : ZMod 1029659401) ^ 423379) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 506122743 := by rw [factor_6_18]; decide
      have factor_6_20 : (37 : ZMod 1029659401) ^ 1693518 = 118774529 := by
        calc
          (37 : ZMod 1029659401) ^ 1693518 = (37 : ZMod 1029659401) ^ (846759 + 846759) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 846759 * (37 : ZMod 1029659401) ^ 846759 := by rw [pow_add]
          _ = 118774529 := by rw [factor_6_19]; decide
      have factor_6_21 : (37 : ZMod 1029659401) ^ 3387037 = 653885009 := by
        calc
          (37 : ZMod 1029659401) ^ 3387037 = (37 : ZMod 1029659401) ^ (1693518 + 1693518 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 1693518 * (37 : ZMod 1029659401) ^ 1693518) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 653885009 := by rw [factor_6_20]; decide
      have factor_6_22 : (37 : ZMod 1029659401) ^ 6774075 = 632393973 := by
        calc
          (37 : ZMod 1029659401) ^ 6774075 = (37 : ZMod 1029659401) ^ (3387037 + 3387037 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 3387037 * (37 : ZMod 1029659401) ^ 3387037) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 632393973 := by rw [factor_6_21]; decide
      have factor_6_23 : (37 : ZMod 1029659401) ^ 13548150 = 890435374 := by
        calc
          (37 : ZMod 1029659401) ^ 13548150 = (37 : ZMod 1029659401) ^ (6774075 + 6774075) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 6774075 * (37 : ZMod 1029659401) ^ 6774075 := by rw [pow_add]
          _ = 890435374 := by rw [factor_6_22]; decide
      have factor_6_24 : (37 : ZMod 1029659401) ^ 27096300 = 737206338 := by
        calc
          (37 : ZMod 1029659401) ^ 27096300 = (37 : ZMod 1029659401) ^ (13548150 + 13548150) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 13548150 * (37 : ZMod 1029659401) ^ 13548150 := by rw [pow_add]
          _ = 737206338 := by rw [factor_6_23]; decide
      have factor_6_25 : (37 : ZMod 1029659401) ^ 54192600 = 1028635438 := by
        calc
          (37 : ZMod 1029659401) ^ 54192600 = (37 : ZMod 1029659401) ^ (27096300 + 27096300) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 27096300 * (37 : ZMod 1029659401) ^ 27096300 := by rw [pow_add]
          _ = 1028635438 := by rw [factor_6_24]; decide
      change (37 : ZMod 1029659401) ^ 54192600 ≠ 1
      rw [factor_6_25]
      decide
    ·
      have factor_7_0 : (37 : ZMod 1029659401) ^ 1 = 37 := by norm_num
      have factor_7_1 : (37 : ZMod 1029659401) ^ 2 = 1369 := by
        calc
          (37 : ZMod 1029659401) ^ 2 = (37 : ZMod 1029659401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 1 * (37 : ZMod 1029659401) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_7_0]; decide
      have factor_7_2 : (37 : ZMod 1029659401) ^ 5 = 69343957 := by
        calc
          (37 : ZMod 1029659401) ^ 5 = (37 : ZMod 1029659401) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 2 * (37 : ZMod 1029659401) ^ 2) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 69343957 := by rw [factor_7_1]; decide
      have factor_7_3 : (37 : ZMod 1029659401) ^ 10 = 834270977 := by
        calc
          (37 : ZMod 1029659401) ^ 10 = (37 : ZMod 1029659401) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 5 * (37 : ZMod 1029659401) ^ 5 := by rw [pow_add]
          _ = 834270977 := by rw [factor_7_2]; decide
      have factor_7_4 : (37 : ZMod 1029659401) ^ 21 = 400573743 := by
        calc
          (37 : ZMod 1029659401) ^ 21 = (37 : ZMod 1029659401) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 10 * (37 : ZMod 1029659401) ^ 10) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 400573743 := by rw [factor_7_3]; decide
      have factor_7_5 : (37 : ZMod 1029659401) ^ 42 = 113782566 := by
        calc
          (37 : ZMod 1029659401) ^ 42 = (37 : ZMod 1029659401) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 21 * (37 : ZMod 1029659401) ^ 21 := by rw [pow_add]
          _ = 113782566 := by rw [factor_7_4]; decide
      have factor_7_6 : (37 : ZMod 1029659401) ^ 85 = 221634481 := by
        calc
          (37 : ZMod 1029659401) ^ 85 = (37 : ZMod 1029659401) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 42 * (37 : ZMod 1029659401) ^ 42) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 221634481 := by rw [factor_7_5]; decide
      have factor_7_7 : (37 : ZMod 1029659401) ^ 170 = 535463476 := by
        calc
          (37 : ZMod 1029659401) ^ 170 = (37 : ZMod 1029659401) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 85 * (37 : ZMod 1029659401) ^ 85 := by rw [pow_add]
          _ = 535463476 := by rw [factor_7_6]; decide
      have factor_7_8 : (37 : ZMod 1029659401) ^ 341 = 567541072 := by
        calc
          (37 : ZMod 1029659401) ^ 341 = (37 : ZMod 1029659401) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 170 * (37 : ZMod 1029659401) ^ 170) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 567541072 := by rw [factor_7_7]; decide
      have factor_7_9 : (37 : ZMod 1029659401) ^ 683 = 371651600 := by
        calc
          (37 : ZMod 1029659401) ^ 683 = (37 : ZMod 1029659401) ^ (341 + 341 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 341 * (37 : ZMod 1029659401) ^ 341) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 371651600 := by rw [factor_7_8]; decide
      have factor_7_10 : (37 : ZMod 1029659401) ^ 1366 = 399242785 := by
        calc
          (37 : ZMod 1029659401) ^ 1366 = (37 : ZMod 1029659401) ^ (683 + 683) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 683 * (37 : ZMod 1029659401) ^ 683 := by rw [pow_add]
          _ = 399242785 := by rw [factor_7_9]; decide
      have factor_7_11 : (37 : ZMod 1029659401) ^ 2732 = 545967201 := by
        calc
          (37 : ZMod 1029659401) ^ 2732 = (37 : ZMod 1029659401) ^ (1366 + 1366) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 1366 * (37 : ZMod 1029659401) ^ 1366 := by rw [pow_add]
          _ = 545967201 := by rw [factor_7_10]; decide
      have factor_7_12 : (37 : ZMod 1029659401) ^ 5464 = 943100035 := by
        calc
          (37 : ZMod 1029659401) ^ 5464 = (37 : ZMod 1029659401) ^ (2732 + 2732) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 2732 * (37 : ZMod 1029659401) ^ 2732 := by rw [pow_add]
          _ = 943100035 := by rw [factor_7_11]; decide
      have factor_7_13 : (37 : ZMod 1029659401) ^ 10929 = 990741427 := by
        calc
          (37 : ZMod 1029659401) ^ 10929 = (37 : ZMod 1029659401) ^ (5464 + 5464 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 5464 * (37 : ZMod 1029659401) ^ 5464) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 990741427 := by rw [factor_7_12]; decide
      have factor_7_14 : (37 : ZMod 1029659401) ^ 21859 = 313269341 := by
        calc
          (37 : ZMod 1029659401) ^ 21859 = (37 : ZMod 1029659401) ^ (10929 + 10929 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 10929 * (37 : ZMod 1029659401) ^ 10929) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 313269341 := by rw [factor_7_13]; decide
      have factor_7_15 : (37 : ZMod 1029659401) ^ 43718 = 239874263 := by
        calc
          (37 : ZMod 1029659401) ^ 43718 = (37 : ZMod 1029659401) ^ (21859 + 21859) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 21859 * (37 : ZMod 1029659401) ^ 21859 := by rw [pow_add]
          _ = 239874263 := by rw [factor_7_14]; decide
      have factor_7_16 : (37 : ZMod 1029659401) ^ 87437 = 26240194 := by
        calc
          (37 : ZMod 1029659401) ^ 87437 = (37 : ZMod 1029659401) ^ (43718 + 43718 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 43718 * (37 : ZMod 1029659401) ^ 43718) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 26240194 := by rw [factor_7_15]; decide
      have factor_7_17 : (37 : ZMod 1029659401) ^ 174874 = 124477322 := by
        calc
          (37 : ZMod 1029659401) ^ 174874 = (37 : ZMod 1029659401) ^ (87437 + 87437) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 87437 * (37 : ZMod 1029659401) ^ 87437 := by rw [pow_add]
          _ = 124477322 := by rw [factor_7_16]; decide
      have factor_7_18 : (37 : ZMod 1029659401) ^ 349748 = 721411404 := by
        calc
          (37 : ZMod 1029659401) ^ 349748 = (37 : ZMod 1029659401) ^ (174874 + 174874) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 174874 * (37 : ZMod 1029659401) ^ 174874 := by rw [pow_add]
          _ = 721411404 := by rw [factor_7_17]; decide
      have factor_7_19 : (37 : ZMod 1029659401) ^ 699496 = 223229347 := by
        calc
          (37 : ZMod 1029659401) ^ 699496 = (37 : ZMod 1029659401) ^ (349748 + 349748) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 349748 * (37 : ZMod 1029659401) ^ 349748 := by rw [pow_add]
          _ = 223229347 := by rw [factor_7_18]; decide
      have factor_7_20 : (37 : ZMod 1029659401) ^ 1398993 = 312900910 := by
        calc
          (37 : ZMod 1029659401) ^ 1398993 = (37 : ZMod 1029659401) ^ (699496 + 699496 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 699496 * (37 : ZMod 1029659401) ^ 699496) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 312900910 := by rw [factor_7_19]; decide
      have factor_7_21 : (37 : ZMod 1029659401) ^ 2797987 = 643448668 := by
        calc
          (37 : ZMod 1029659401) ^ 2797987 = (37 : ZMod 1029659401) ^ (1398993 + 1398993 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 1398993 * (37 : ZMod 1029659401) ^ 1398993) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 643448668 := by rw [factor_7_20]; decide
      have factor_7_22 : (37 : ZMod 1029659401) ^ 5595975 = 101068742 := by
        calc
          (37 : ZMod 1029659401) ^ 5595975 = (37 : ZMod 1029659401) ^ (2797987 + 2797987 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = ((37 : ZMod 1029659401) ^ 2797987 * (37 : ZMod 1029659401) ^ 2797987) * (37 : ZMod 1029659401) := by rw [pow_succ, pow_add]
          _ = 101068742 := by rw [factor_7_21]; decide
      have factor_7_23 : (37 : ZMod 1029659401) ^ 11191950 = 72931914 := by
        calc
          (37 : ZMod 1029659401) ^ 11191950 = (37 : ZMod 1029659401) ^ (5595975 + 5595975) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 5595975 * (37 : ZMod 1029659401) ^ 5595975 := by rw [pow_add]
          _ = 72931914 := by rw [factor_7_22]; decide
      have factor_7_24 : (37 : ZMod 1029659401) ^ 22383900 = 122366348 := by
        calc
          (37 : ZMod 1029659401) ^ 22383900 = (37 : ZMod 1029659401) ^ (11191950 + 11191950) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 11191950 * (37 : ZMod 1029659401) ^ 11191950 := by rw [pow_add]
          _ = 122366348 := by rw [factor_7_23]; decide
      have factor_7_25 : (37 : ZMod 1029659401) ^ 44767800 = 914700295 := by
        calc
          (37 : ZMod 1029659401) ^ 44767800 = (37 : ZMod 1029659401) ^ (22383900 + 22383900) :=
            congrArg (fun n : ℕ => (37 : ZMod 1029659401) ^ n) (by norm_num)
          _ = (37 : ZMod 1029659401) ^ 22383900 * (37 : ZMod 1029659401) ^ 22383900 := by rw [pow_add]
          _ = 914700295 := by rw [factor_7_24]; decide
      change (37 : ZMod 1029659401) ^ 44767800 ≠ 1
      rw [factor_7_25]
      decide

#print axioms prime_lucas_1029659401

end TotientTailPeriodKiller
end Erdos249257
