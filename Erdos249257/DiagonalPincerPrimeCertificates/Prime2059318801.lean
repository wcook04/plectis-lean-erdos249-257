import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2059318801 : Nat.Prime 2059318801 := by
  apply lucas_primality 2059318801 (26 : ZMod 2059318801)
  ·
      have fermat_0 : (26 : ZMod 2059318801) ^ 1 = 26 := by norm_num
      have fermat_1 : (26 : ZMod 2059318801) ^ 3 = 17576 := by
        calc
          (26 : ZMod 2059318801) ^ 3 = (26 : ZMod 2059318801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 1 * (26 : ZMod 2059318801) ^ 1) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 17576 := by rw [fermat_0]; decide
      have fermat_2 : (26 : ZMod 2059318801) ^ 7 = 1853853773 := by
        calc
          (26 : ZMod 2059318801) ^ 7 = (26 : ZMod 2059318801) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 3 * (26 : ZMod 2059318801) ^ 3) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1853853773 := by rw [fermat_1]; decide
      have fermat_3 : (26 : ZMod 2059318801) ^ 15 = 177793175 := by
        calc
          (26 : ZMod 2059318801) ^ 15 = (26 : ZMod 2059318801) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 7 * (26 : ZMod 2059318801) ^ 7) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 177793175 := by rw [fermat_2]; decide
      have fermat_4 : (26 : ZMod 2059318801) ^ 30 = 1277633889 := by
        calc
          (26 : ZMod 2059318801) ^ 30 = (26 : ZMod 2059318801) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 15 * (26 : ZMod 2059318801) ^ 15 := by rw [pow_add]
          _ = 1277633889 := by rw [fermat_3]; decide
      have fermat_5 : (26 : ZMod 2059318801) ^ 61 = 1755776734 := by
        calc
          (26 : ZMod 2059318801) ^ 61 = (26 : ZMod 2059318801) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 30 * (26 : ZMod 2059318801) ^ 30) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1755776734 := by rw [fermat_4]; decide
      have fermat_6 : (26 : ZMod 2059318801) ^ 122 = 2059140614 := by
        calc
          (26 : ZMod 2059318801) ^ 122 = (26 : ZMod 2059318801) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 61 * (26 : ZMod 2059318801) ^ 61 := by rw [pow_add]
          _ = 2059140614 := by rw [fermat_5]; decide
      have fermat_7 : (26 : ZMod 2059318801) ^ 245 = 1788260794 := by
        calc
          (26 : ZMod 2059318801) ^ 245 = (26 : ZMod 2059318801) ^ (122 + 122 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 122 * (26 : ZMod 2059318801) ^ 122) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1788260794 := by rw [fermat_6]; decide
      have fermat_8 : (26 : ZMod 2059318801) ^ 490 = 1078532417 := by
        calc
          (26 : ZMod 2059318801) ^ 490 = (26 : ZMod 2059318801) ^ (245 + 245) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 245 * (26 : ZMod 2059318801) ^ 245 := by rw [pow_add]
          _ = 1078532417 := by rw [fermat_7]; decide
      have fermat_9 : (26 : ZMod 2059318801) ^ 981 = 1590856285 := by
        calc
          (26 : ZMod 2059318801) ^ 981 = (26 : ZMod 2059318801) ^ (490 + 490 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 490 * (26 : ZMod 2059318801) ^ 490) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1590856285 := by rw [fermat_8]; decide
      have fermat_10 : (26 : ZMod 2059318801) ^ 1963 = 1182612365 := by
        calc
          (26 : ZMod 2059318801) ^ 1963 = (26 : ZMod 2059318801) ^ (981 + 981 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 981 * (26 : ZMod 2059318801) ^ 981) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1182612365 := by rw [fermat_9]; decide
      have fermat_11 : (26 : ZMod 2059318801) ^ 3927 = 1020293926 := by
        calc
          (26 : ZMod 2059318801) ^ 3927 = (26 : ZMod 2059318801) ^ (1963 + 1963 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 1963 * (26 : ZMod 2059318801) ^ 1963) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1020293926 := by rw [fermat_10]; decide
      have fermat_12 : (26 : ZMod 2059318801) ^ 7855 = 1605470295 := by
        calc
          (26 : ZMod 2059318801) ^ 7855 = (26 : ZMod 2059318801) ^ (3927 + 3927 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 3927 * (26 : ZMod 2059318801) ^ 3927) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1605470295 := by rw [fermat_11]; decide
      have fermat_13 : (26 : ZMod 2059318801) ^ 15711 = 1864135960 := by
        calc
          (26 : ZMod 2059318801) ^ 15711 = (26 : ZMod 2059318801) ^ (7855 + 7855 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 7855 * (26 : ZMod 2059318801) ^ 7855) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1864135960 := by rw [fermat_12]; decide
      have fermat_14 : (26 : ZMod 2059318801) ^ 31422 = 32876194 := by
        calc
          (26 : ZMod 2059318801) ^ 31422 = (26 : ZMod 2059318801) ^ (15711 + 15711) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 15711 * (26 : ZMod 2059318801) ^ 15711 := by rw [pow_add]
          _ = 32876194 := by rw [fermat_13]; decide
      have fermat_15 : (26 : ZMod 2059318801) ^ 62845 = 1191021102 := by
        calc
          (26 : ZMod 2059318801) ^ 62845 = (26 : ZMod 2059318801) ^ (31422 + 31422 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 31422 * (26 : ZMod 2059318801) ^ 31422) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1191021102 := by rw [fermat_14]; decide
      have fermat_16 : (26 : ZMod 2059318801) ^ 125690 = 1673930811 := by
        calc
          (26 : ZMod 2059318801) ^ 125690 = (26 : ZMod 2059318801) ^ (62845 + 62845) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 62845 * (26 : ZMod 2059318801) ^ 62845 := by rw [pow_add]
          _ = 1673930811 := by rw [fermat_15]; decide
      have fermat_17 : (26 : ZMod 2059318801) ^ 251381 = 679630582 := by
        calc
          (26 : ZMod 2059318801) ^ 251381 = (26 : ZMod 2059318801) ^ (125690 + 125690 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 125690 * (26 : ZMod 2059318801) ^ 125690) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 679630582 := by rw [fermat_16]; decide
      have fermat_18 : (26 : ZMod 2059318801) ^ 502763 = 1415067652 := by
        calc
          (26 : ZMod 2059318801) ^ 502763 = (26 : ZMod 2059318801) ^ (251381 + 251381 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 251381 * (26 : ZMod 2059318801) ^ 251381) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1415067652 := by rw [fermat_17]; decide
      have fermat_19 : (26 : ZMod 2059318801) ^ 1005526 = 76025137 := by
        calc
          (26 : ZMod 2059318801) ^ 1005526 = (26 : ZMod 2059318801) ^ (502763 + 502763) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 502763 * (26 : ZMod 2059318801) ^ 502763 := by rw [pow_add]
          _ = 76025137 := by rw [fermat_18]; decide
      have fermat_20 : (26 : ZMod 2059318801) ^ 2011053 = 1234054261 := by
        calc
          (26 : ZMod 2059318801) ^ 2011053 = (26 : ZMod 2059318801) ^ (1005526 + 1005526 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 1005526 * (26 : ZMod 2059318801) ^ 1005526) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1234054261 := by rw [fermat_19]; decide
      have fermat_21 : (26 : ZMod 2059318801) ^ 4022107 = 1588470754 := by
        calc
          (26 : ZMod 2059318801) ^ 4022107 = (26 : ZMod 2059318801) ^ (2011053 + 2011053 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 2011053 * (26 : ZMod 2059318801) ^ 2011053) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1588470754 := by rw [fermat_20]; decide
      have fermat_22 : (26 : ZMod 2059318801) ^ 8044214 = 616255478 := by
        calc
          (26 : ZMod 2059318801) ^ 8044214 = (26 : ZMod 2059318801) ^ (4022107 + 4022107) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 4022107 * (26 : ZMod 2059318801) ^ 4022107 := by rw [pow_add]
          _ = 616255478 := by rw [fermat_21]; decide
      have fermat_23 : (26 : ZMod 2059318801) ^ 16088428 = 1226767938 := by
        calc
          (26 : ZMod 2059318801) ^ 16088428 = (26 : ZMod 2059318801) ^ (8044214 + 8044214) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 8044214 * (26 : ZMod 2059318801) ^ 8044214 := by rw [pow_add]
          _ = 1226767938 := by rw [fermat_22]; decide
      have fermat_24 : (26 : ZMod 2059318801) ^ 32176856 = 1380920483 := by
        calc
          (26 : ZMod 2059318801) ^ 32176856 = (26 : ZMod 2059318801) ^ (16088428 + 16088428) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 16088428 * (26 : ZMod 2059318801) ^ 16088428 := by rw [pow_add]
          _ = 1380920483 := by rw [fermat_23]; decide
      have fermat_25 : (26 : ZMod 2059318801) ^ 64353712 = 68839379 := by
        calc
          (26 : ZMod 2059318801) ^ 64353712 = (26 : ZMod 2059318801) ^ (32176856 + 32176856) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 32176856 * (26 : ZMod 2059318801) ^ 32176856 := by rw [pow_add]
          _ = 68839379 := by rw [fermat_24]; decide
      have fermat_26 : (26 : ZMod 2059318801) ^ 128707425 = 800884026 := by
        calc
          (26 : ZMod 2059318801) ^ 128707425 = (26 : ZMod 2059318801) ^ (64353712 + 64353712 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 64353712 * (26 : ZMod 2059318801) ^ 64353712) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 800884026 := by rw [fermat_25]; decide
      have fermat_27 : (26 : ZMod 2059318801) ^ 257414850 = 1348149867 := by
        calc
          (26 : ZMod 2059318801) ^ 257414850 = (26 : ZMod 2059318801) ^ (128707425 + 128707425) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 128707425 * (26 : ZMod 2059318801) ^ 128707425 := by rw [pow_add]
          _ = 1348149867 := by rw [fermat_26]; decide
      have fermat_28 : (26 : ZMod 2059318801) ^ 514829700 = 1657880772 := by
        calc
          (26 : ZMod 2059318801) ^ 514829700 = (26 : ZMod 2059318801) ^ (257414850 + 257414850) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 257414850 * (26 : ZMod 2059318801) ^ 257414850 := by rw [pow_add]
          _ = 1657880772 := by rw [fermat_27]; decide
      have fermat_29 : (26 : ZMod 2059318801) ^ 1029659400 = 2059318800 := by
        calc
          (26 : ZMod 2059318801) ^ 1029659400 = (26 : ZMod 2059318801) ^ (514829700 + 514829700) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 514829700 * (26 : ZMod 2059318801) ^ 514829700 := by rw [pow_add]
          _ = 2059318800 := by rw [fermat_28]; decide
      have fermat_30 : (26 : ZMod 2059318801) ^ 2059318800 = 1 := by
        calc
          (26 : ZMod 2059318801) ^ 2059318800 = (26 : ZMod 2059318801) ^ (1029659400 + 1029659400) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 1029659400 * (26 : ZMod 2059318801) ^ 1029659400 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5, 2), (7, 1), (11, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5, 2), (7, 1), (11, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 2059318801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (26 : ZMod 2059318801) ^ 1 = 26 := by norm_num
      have factor_0_1 : (26 : ZMod 2059318801) ^ 3 = 17576 := by
        calc
          (26 : ZMod 2059318801) ^ 3 = (26 : ZMod 2059318801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 1 * (26 : ZMod 2059318801) ^ 1) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 17576 := by rw [factor_0_0]; decide
      have factor_0_2 : (26 : ZMod 2059318801) ^ 7 = 1853853773 := by
        calc
          (26 : ZMod 2059318801) ^ 7 = (26 : ZMod 2059318801) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 3 * (26 : ZMod 2059318801) ^ 3) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1853853773 := by rw [factor_0_1]; decide
      have factor_0_3 : (26 : ZMod 2059318801) ^ 15 = 177793175 := by
        calc
          (26 : ZMod 2059318801) ^ 15 = (26 : ZMod 2059318801) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 7 * (26 : ZMod 2059318801) ^ 7) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 177793175 := by rw [factor_0_2]; decide
      have factor_0_4 : (26 : ZMod 2059318801) ^ 30 = 1277633889 := by
        calc
          (26 : ZMod 2059318801) ^ 30 = (26 : ZMod 2059318801) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 15 * (26 : ZMod 2059318801) ^ 15 := by rw [pow_add]
          _ = 1277633889 := by rw [factor_0_3]; decide
      have factor_0_5 : (26 : ZMod 2059318801) ^ 61 = 1755776734 := by
        calc
          (26 : ZMod 2059318801) ^ 61 = (26 : ZMod 2059318801) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 30 * (26 : ZMod 2059318801) ^ 30) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1755776734 := by rw [factor_0_4]; decide
      have factor_0_6 : (26 : ZMod 2059318801) ^ 122 = 2059140614 := by
        calc
          (26 : ZMod 2059318801) ^ 122 = (26 : ZMod 2059318801) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 61 * (26 : ZMod 2059318801) ^ 61 := by rw [pow_add]
          _ = 2059140614 := by rw [factor_0_5]; decide
      have factor_0_7 : (26 : ZMod 2059318801) ^ 245 = 1788260794 := by
        calc
          (26 : ZMod 2059318801) ^ 245 = (26 : ZMod 2059318801) ^ (122 + 122 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 122 * (26 : ZMod 2059318801) ^ 122) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1788260794 := by rw [factor_0_6]; decide
      have factor_0_8 : (26 : ZMod 2059318801) ^ 490 = 1078532417 := by
        calc
          (26 : ZMod 2059318801) ^ 490 = (26 : ZMod 2059318801) ^ (245 + 245) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 245 * (26 : ZMod 2059318801) ^ 245 := by rw [pow_add]
          _ = 1078532417 := by rw [factor_0_7]; decide
      have factor_0_9 : (26 : ZMod 2059318801) ^ 981 = 1590856285 := by
        calc
          (26 : ZMod 2059318801) ^ 981 = (26 : ZMod 2059318801) ^ (490 + 490 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 490 * (26 : ZMod 2059318801) ^ 490) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1590856285 := by rw [factor_0_8]; decide
      have factor_0_10 : (26 : ZMod 2059318801) ^ 1963 = 1182612365 := by
        calc
          (26 : ZMod 2059318801) ^ 1963 = (26 : ZMod 2059318801) ^ (981 + 981 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 981 * (26 : ZMod 2059318801) ^ 981) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1182612365 := by rw [factor_0_9]; decide
      have factor_0_11 : (26 : ZMod 2059318801) ^ 3927 = 1020293926 := by
        calc
          (26 : ZMod 2059318801) ^ 3927 = (26 : ZMod 2059318801) ^ (1963 + 1963 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 1963 * (26 : ZMod 2059318801) ^ 1963) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1020293926 := by rw [factor_0_10]; decide
      have factor_0_12 : (26 : ZMod 2059318801) ^ 7855 = 1605470295 := by
        calc
          (26 : ZMod 2059318801) ^ 7855 = (26 : ZMod 2059318801) ^ (3927 + 3927 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 3927 * (26 : ZMod 2059318801) ^ 3927) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1605470295 := by rw [factor_0_11]; decide
      have factor_0_13 : (26 : ZMod 2059318801) ^ 15711 = 1864135960 := by
        calc
          (26 : ZMod 2059318801) ^ 15711 = (26 : ZMod 2059318801) ^ (7855 + 7855 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 7855 * (26 : ZMod 2059318801) ^ 7855) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1864135960 := by rw [factor_0_12]; decide
      have factor_0_14 : (26 : ZMod 2059318801) ^ 31422 = 32876194 := by
        calc
          (26 : ZMod 2059318801) ^ 31422 = (26 : ZMod 2059318801) ^ (15711 + 15711) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 15711 * (26 : ZMod 2059318801) ^ 15711 := by rw [pow_add]
          _ = 32876194 := by rw [factor_0_13]; decide
      have factor_0_15 : (26 : ZMod 2059318801) ^ 62845 = 1191021102 := by
        calc
          (26 : ZMod 2059318801) ^ 62845 = (26 : ZMod 2059318801) ^ (31422 + 31422 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 31422 * (26 : ZMod 2059318801) ^ 31422) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1191021102 := by rw [factor_0_14]; decide
      have factor_0_16 : (26 : ZMod 2059318801) ^ 125690 = 1673930811 := by
        calc
          (26 : ZMod 2059318801) ^ 125690 = (26 : ZMod 2059318801) ^ (62845 + 62845) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 62845 * (26 : ZMod 2059318801) ^ 62845 := by rw [pow_add]
          _ = 1673930811 := by rw [factor_0_15]; decide
      have factor_0_17 : (26 : ZMod 2059318801) ^ 251381 = 679630582 := by
        calc
          (26 : ZMod 2059318801) ^ 251381 = (26 : ZMod 2059318801) ^ (125690 + 125690 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 125690 * (26 : ZMod 2059318801) ^ 125690) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 679630582 := by rw [factor_0_16]; decide
      have factor_0_18 : (26 : ZMod 2059318801) ^ 502763 = 1415067652 := by
        calc
          (26 : ZMod 2059318801) ^ 502763 = (26 : ZMod 2059318801) ^ (251381 + 251381 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 251381 * (26 : ZMod 2059318801) ^ 251381) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1415067652 := by rw [factor_0_17]; decide
      have factor_0_19 : (26 : ZMod 2059318801) ^ 1005526 = 76025137 := by
        calc
          (26 : ZMod 2059318801) ^ 1005526 = (26 : ZMod 2059318801) ^ (502763 + 502763) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 502763 * (26 : ZMod 2059318801) ^ 502763 := by rw [pow_add]
          _ = 76025137 := by rw [factor_0_18]; decide
      have factor_0_20 : (26 : ZMod 2059318801) ^ 2011053 = 1234054261 := by
        calc
          (26 : ZMod 2059318801) ^ 2011053 = (26 : ZMod 2059318801) ^ (1005526 + 1005526 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 1005526 * (26 : ZMod 2059318801) ^ 1005526) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1234054261 := by rw [factor_0_19]; decide
      have factor_0_21 : (26 : ZMod 2059318801) ^ 4022107 = 1588470754 := by
        calc
          (26 : ZMod 2059318801) ^ 4022107 = (26 : ZMod 2059318801) ^ (2011053 + 2011053 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 2011053 * (26 : ZMod 2059318801) ^ 2011053) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1588470754 := by rw [factor_0_20]; decide
      have factor_0_22 : (26 : ZMod 2059318801) ^ 8044214 = 616255478 := by
        calc
          (26 : ZMod 2059318801) ^ 8044214 = (26 : ZMod 2059318801) ^ (4022107 + 4022107) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 4022107 * (26 : ZMod 2059318801) ^ 4022107 := by rw [pow_add]
          _ = 616255478 := by rw [factor_0_21]; decide
      have factor_0_23 : (26 : ZMod 2059318801) ^ 16088428 = 1226767938 := by
        calc
          (26 : ZMod 2059318801) ^ 16088428 = (26 : ZMod 2059318801) ^ (8044214 + 8044214) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 8044214 * (26 : ZMod 2059318801) ^ 8044214 := by rw [pow_add]
          _ = 1226767938 := by rw [factor_0_22]; decide
      have factor_0_24 : (26 : ZMod 2059318801) ^ 32176856 = 1380920483 := by
        calc
          (26 : ZMod 2059318801) ^ 32176856 = (26 : ZMod 2059318801) ^ (16088428 + 16088428) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 16088428 * (26 : ZMod 2059318801) ^ 16088428 := by rw [pow_add]
          _ = 1380920483 := by rw [factor_0_23]; decide
      have factor_0_25 : (26 : ZMod 2059318801) ^ 64353712 = 68839379 := by
        calc
          (26 : ZMod 2059318801) ^ 64353712 = (26 : ZMod 2059318801) ^ (32176856 + 32176856) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 32176856 * (26 : ZMod 2059318801) ^ 32176856 := by rw [pow_add]
          _ = 68839379 := by rw [factor_0_24]; decide
      have factor_0_26 : (26 : ZMod 2059318801) ^ 128707425 = 800884026 := by
        calc
          (26 : ZMod 2059318801) ^ 128707425 = (26 : ZMod 2059318801) ^ (64353712 + 64353712 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 64353712 * (26 : ZMod 2059318801) ^ 64353712) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 800884026 := by rw [factor_0_25]; decide
      have factor_0_27 : (26 : ZMod 2059318801) ^ 257414850 = 1348149867 := by
        calc
          (26 : ZMod 2059318801) ^ 257414850 = (26 : ZMod 2059318801) ^ (128707425 + 128707425) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 128707425 * (26 : ZMod 2059318801) ^ 128707425 := by rw [pow_add]
          _ = 1348149867 := by rw [factor_0_26]; decide
      have factor_0_28 : (26 : ZMod 2059318801) ^ 514829700 = 1657880772 := by
        calc
          (26 : ZMod 2059318801) ^ 514829700 = (26 : ZMod 2059318801) ^ (257414850 + 257414850) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 257414850 * (26 : ZMod 2059318801) ^ 257414850 := by rw [pow_add]
          _ = 1657880772 := by rw [factor_0_27]; decide
      have factor_0_29 : (26 : ZMod 2059318801) ^ 1029659400 = 2059318800 := by
        calc
          (26 : ZMod 2059318801) ^ 1029659400 = (26 : ZMod 2059318801) ^ (514829700 + 514829700) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 514829700 * (26 : ZMod 2059318801) ^ 514829700 := by rw [pow_add]
          _ = 2059318800 := by rw [factor_0_28]; decide
      change (26 : ZMod 2059318801) ^ 1029659400 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (26 : ZMod 2059318801) ^ 1 = 26 := by norm_num
      have factor_1_1 : (26 : ZMod 2059318801) ^ 2 = 676 := by
        calc
          (26 : ZMod 2059318801) ^ 2 = (26 : ZMod 2059318801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 1 * (26 : ZMod 2059318801) ^ 1 := by rw [pow_add]
          _ = 676 := by rw [factor_1_0]; decide
      have factor_1_2 : (26 : ZMod 2059318801) ^ 5 = 11881376 := by
        calc
          (26 : ZMod 2059318801) ^ 5 = (26 : ZMod 2059318801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 2 * (26 : ZMod 2059318801) ^ 2) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 11881376 := by rw [factor_1_1]; decide
      have factor_1_3 : (26 : ZMod 2059318801) ^ 10 = 791844826 := by
        calc
          (26 : ZMod 2059318801) ^ 10 = (26 : ZMod 2059318801) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 5 * (26 : ZMod 2059318801) ^ 5 := by rw [pow_add]
          _ = 791844826 := by rw [factor_1_2]; decide
      have factor_1_4 : (26 : ZMod 2059318801) ^ 20 = 988849811 := by
        calc
          (26 : ZMod 2059318801) ^ 20 = (26 : ZMod 2059318801) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 10 * (26 : ZMod 2059318801) ^ 10 := by rw [pow_add]
          _ = 988849811 := by rw [factor_1_3]; decide
      have factor_1_5 : (26 : ZMod 2059318801) ^ 40 = 1542308886 := by
        calc
          (26 : ZMod 2059318801) ^ 40 = (26 : ZMod 2059318801) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 20 * (26 : ZMod 2059318801) ^ 20 := by rw [pow_add]
          _ = 1542308886 := by rw [factor_1_4]; decide
      have factor_1_6 : (26 : ZMod 2059318801) ^ 81 = 1618299194 := by
        calc
          (26 : ZMod 2059318801) ^ 81 = (26 : ZMod 2059318801) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 40 * (26 : ZMod 2059318801) ^ 40) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1618299194 := by rw [factor_1_5]; decide
      have factor_1_7 : (26 : ZMod 2059318801) ^ 163 = 705007610 := by
        calc
          (26 : ZMod 2059318801) ^ 163 = (26 : ZMod 2059318801) ^ (81 + 81 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 81 * (26 : ZMod 2059318801) ^ 81) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 705007610 := by rw [factor_1_6]; decide
      have factor_1_8 : (26 : ZMod 2059318801) ^ 327 = 1282598179 := by
        calc
          (26 : ZMod 2059318801) ^ 327 = (26 : ZMod 2059318801) ^ (163 + 163 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 163 * (26 : ZMod 2059318801) ^ 163) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1282598179 := by rw [factor_1_7]; decide
      have factor_1_9 : (26 : ZMod 2059318801) ^ 654 = 329815195 := by
        calc
          (26 : ZMod 2059318801) ^ 654 = (26 : ZMod 2059318801) ^ (327 + 327) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 327 * (26 : ZMod 2059318801) ^ 327 := by rw [pow_add]
          _ = 329815195 := by rw [factor_1_8]; decide
      have factor_1_10 : (26 : ZMod 2059318801) ^ 1309 = 744493495 := by
        calc
          (26 : ZMod 2059318801) ^ 1309 = (26 : ZMod 2059318801) ^ (654 + 654 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 654 * (26 : ZMod 2059318801) ^ 654) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 744493495 := by rw [factor_1_9]; decide
      have factor_1_11 : (26 : ZMod 2059318801) ^ 2618 = 1451462242 := by
        calc
          (26 : ZMod 2059318801) ^ 2618 = (26 : ZMod 2059318801) ^ (1309 + 1309) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 1309 * (26 : ZMod 2059318801) ^ 1309 := by rw [pow_add]
          _ = 1451462242 := by rw [factor_1_10]; decide
      have factor_1_12 : (26 : ZMod 2059318801) ^ 5237 = 1470820563 := by
        calc
          (26 : ZMod 2059318801) ^ 5237 = (26 : ZMod 2059318801) ^ (2618 + 2618 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 2618 * (26 : ZMod 2059318801) ^ 2618) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1470820563 := by rw [factor_1_11]; decide
      have factor_1_13 : (26 : ZMod 2059318801) ^ 10474 = 752155987 := by
        calc
          (26 : ZMod 2059318801) ^ 10474 = (26 : ZMod 2059318801) ^ (5237 + 5237) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 5237 * (26 : ZMod 2059318801) ^ 5237 := by rw [pow_add]
          _ = 752155987 := by rw [factor_1_12]; decide
      have factor_1_14 : (26 : ZMod 2059318801) ^ 20948 = 1857998123 := by
        calc
          (26 : ZMod 2059318801) ^ 20948 = (26 : ZMod 2059318801) ^ (10474 + 10474) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 10474 * (26 : ZMod 2059318801) ^ 10474 := by rw [pow_add]
          _ = 1857998123 := by rw [factor_1_13]; decide
      have factor_1_15 : (26 : ZMod 2059318801) ^ 41896 = 1933184812 := by
        calc
          (26 : ZMod 2059318801) ^ 41896 = (26 : ZMod 2059318801) ^ (20948 + 20948) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 20948 * (26 : ZMod 2059318801) ^ 20948 := by rw [pow_add]
          _ = 1933184812 := by rw [factor_1_14]; decide
      have factor_1_16 : (26 : ZMod 2059318801) ^ 83793 = 98060034 := by
        calc
          (26 : ZMod 2059318801) ^ 83793 = (26 : ZMod 2059318801) ^ (41896 + 41896 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 41896 * (26 : ZMod 2059318801) ^ 41896) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 98060034 := by rw [factor_1_15]; decide
      have factor_1_17 : (26 : ZMod 2059318801) ^ 167587 = 1254269020 := by
        calc
          (26 : ZMod 2059318801) ^ 167587 = (26 : ZMod 2059318801) ^ (83793 + 83793 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 83793 * (26 : ZMod 2059318801) ^ 83793) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1254269020 := by rw [factor_1_16]; decide
      have factor_1_18 : (26 : ZMod 2059318801) ^ 335175 = 1267673236 := by
        calc
          (26 : ZMod 2059318801) ^ 335175 = (26 : ZMod 2059318801) ^ (167587 + 167587 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 167587 * (26 : ZMod 2059318801) ^ 167587) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1267673236 := by rw [factor_1_17]; decide
      have factor_1_19 : (26 : ZMod 2059318801) ^ 670351 = 931536256 := by
        calc
          (26 : ZMod 2059318801) ^ 670351 = (26 : ZMod 2059318801) ^ (335175 + 335175 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 335175 * (26 : ZMod 2059318801) ^ 335175) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 931536256 := by rw [factor_1_18]; decide
      have factor_1_20 : (26 : ZMod 2059318801) ^ 1340702 = 1552948775 := by
        calc
          (26 : ZMod 2059318801) ^ 1340702 = (26 : ZMod 2059318801) ^ (670351 + 670351) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 670351 * (26 : ZMod 2059318801) ^ 670351 := by rw [pow_add]
          _ = 1552948775 := by rw [factor_1_19]; decide
      have factor_1_21 : (26 : ZMod 2059318801) ^ 2681404 = 512736336 := by
        calc
          (26 : ZMod 2059318801) ^ 2681404 = (26 : ZMod 2059318801) ^ (1340702 + 1340702) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 1340702 * (26 : ZMod 2059318801) ^ 1340702 := by rw [pow_add]
          _ = 512736336 := by rw [factor_1_20]; decide
      have factor_1_22 : (26 : ZMod 2059318801) ^ 5362809 = 1361904253 := by
        calc
          (26 : ZMod 2059318801) ^ 5362809 = (26 : ZMod 2059318801) ^ (2681404 + 2681404 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 2681404 * (26 : ZMod 2059318801) ^ 2681404) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1361904253 := by rw [factor_1_21]; decide
      have factor_1_23 : (26 : ZMod 2059318801) ^ 10725618 = 1750121183 := by
        calc
          (26 : ZMod 2059318801) ^ 10725618 = (26 : ZMod 2059318801) ^ (5362809 + 5362809) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 5362809 * (26 : ZMod 2059318801) ^ 5362809 := by rw [pow_add]
          _ = 1750121183 := by rw [factor_1_22]; decide
      have factor_1_24 : (26 : ZMod 2059318801) ^ 21451237 = 1199028168 := by
        calc
          (26 : ZMod 2059318801) ^ 21451237 = (26 : ZMod 2059318801) ^ (10725618 + 10725618 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 10725618 * (26 : ZMod 2059318801) ^ 10725618) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1199028168 := by rw [factor_1_23]; decide
      have factor_1_25 : (26 : ZMod 2059318801) ^ 42902475 = 228829573 := by
        calc
          (26 : ZMod 2059318801) ^ 42902475 = (26 : ZMod 2059318801) ^ (21451237 + 21451237 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 21451237 * (26 : ZMod 2059318801) ^ 21451237) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 228829573 := by rw [factor_1_24]; decide
      have factor_1_26 : (26 : ZMod 2059318801) ^ 85804950 = 929087402 := by
        calc
          (26 : ZMod 2059318801) ^ 85804950 = (26 : ZMod 2059318801) ^ (42902475 + 42902475) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 42902475 * (26 : ZMod 2059318801) ^ 42902475 := by rw [pow_add]
          _ = 929087402 := by rw [factor_1_25]; decide
      have factor_1_27 : (26 : ZMod 2059318801) ^ 171609900 = 1102364617 := by
        calc
          (26 : ZMod 2059318801) ^ 171609900 = (26 : ZMod 2059318801) ^ (85804950 + 85804950) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 85804950 * (26 : ZMod 2059318801) ^ 85804950 := by rw [pow_add]
          _ = 1102364617 := by rw [factor_1_26]; decide
      have factor_1_28 : (26 : ZMod 2059318801) ^ 343219800 = 1095064481 := by
        calc
          (26 : ZMod 2059318801) ^ 343219800 = (26 : ZMod 2059318801) ^ (171609900 + 171609900) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 171609900 * (26 : ZMod 2059318801) ^ 171609900 := by rw [pow_add]
          _ = 1095064481 := by rw [factor_1_27]; decide
      have factor_1_29 : (26 : ZMod 2059318801) ^ 686439600 = 1095064480 := by
        calc
          (26 : ZMod 2059318801) ^ 686439600 = (26 : ZMod 2059318801) ^ (343219800 + 343219800) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 343219800 * (26 : ZMod 2059318801) ^ 343219800 := by rw [pow_add]
          _ = 1095064480 := by rw [factor_1_28]; decide
      change (26 : ZMod 2059318801) ^ 686439600 ≠ 1
      rw [factor_1_29]
      decide
    ·
      have factor_2_0 : (26 : ZMod 2059318801) ^ 1 = 26 := by norm_num
      have factor_2_1 : (26 : ZMod 2059318801) ^ 3 = 17576 := by
        calc
          (26 : ZMod 2059318801) ^ 3 = (26 : ZMod 2059318801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 1 * (26 : ZMod 2059318801) ^ 1) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 17576 := by rw [factor_2_0]; decide
      have factor_2_2 : (26 : ZMod 2059318801) ^ 6 = 308915776 := by
        calc
          (26 : ZMod 2059318801) ^ 6 = (26 : ZMod 2059318801) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 3 * (26 : ZMod 2059318801) ^ 3 := by rw [pow_add]
          _ = 308915776 := by rw [factor_2_1]; decide
      have factor_2_3 : (26 : ZMod 2059318801) ^ 12 = 1923532917 := by
        calc
          (26 : ZMod 2059318801) ^ 12 = (26 : ZMod 2059318801) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 6 * (26 : ZMod 2059318801) ^ 6 := by rw [pow_add]
          _ = 1923532917 := by rw [factor_2_2]; decide
      have factor_2_4 : (26 : ZMod 2059318801) ^ 24 = 188090504 := by
        calc
          (26 : ZMod 2059318801) ^ 24 = (26 : ZMod 2059318801) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 12 * (26 : ZMod 2059318801) ^ 12 := by rw [pow_add]
          _ = 188090504 := by rw [factor_2_3]; decide
      have factor_2_5 : (26 : ZMod 2059318801) ^ 49 = 1427607791 := by
        calc
          (26 : ZMod 2059318801) ^ 49 = (26 : ZMod 2059318801) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 24 * (26 : ZMod 2059318801) ^ 24) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1427607791 := by rw [factor_2_4]; decide
      have factor_2_6 : (26 : ZMod 2059318801) ^ 98 = 1641009757 := by
        calc
          (26 : ZMod 2059318801) ^ 98 = (26 : ZMod 2059318801) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 49 * (26 : ZMod 2059318801) ^ 49 := by rw [pow_add]
          _ = 1641009757 := by rw [factor_2_5]; decide
      have factor_2_7 : (26 : ZMod 2059318801) ^ 196 = 198308498 := by
        calc
          (26 : ZMod 2059318801) ^ 196 = (26 : ZMod 2059318801) ^ (98 + 98) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 98 * (26 : ZMod 2059318801) ^ 98 := by rw [pow_add]
          _ = 198308498 := by rw [factor_2_6]; decide
      have factor_2_8 : (26 : ZMod 2059318801) ^ 392 = 1133757672 := by
        calc
          (26 : ZMod 2059318801) ^ 392 = (26 : ZMod 2059318801) ^ (196 + 196) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 196 * (26 : ZMod 2059318801) ^ 196 := by rw [pow_add]
          _ = 1133757672 := by rw [factor_2_7]; decide
      have factor_2_9 : (26 : ZMod 2059318801) ^ 785 = 974450347 := by
        calc
          (26 : ZMod 2059318801) ^ 785 = (26 : ZMod 2059318801) ^ (392 + 392 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 392 * (26 : ZMod 2059318801) ^ 392) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 974450347 := by rw [factor_2_8]; decide
      have factor_2_10 : (26 : ZMod 2059318801) ^ 1571 = 1315482291 := by
        calc
          (26 : ZMod 2059318801) ^ 1571 = (26 : ZMod 2059318801) ^ (785 + 785 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 785 * (26 : ZMod 2059318801) ^ 785) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1315482291 := by rw [factor_2_9]; decide
      have factor_2_11 : (26 : ZMod 2059318801) ^ 3142 = 834855739 := by
        calc
          (26 : ZMod 2059318801) ^ 3142 = (26 : ZMod 2059318801) ^ (1571 + 1571) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 1571 * (26 : ZMod 2059318801) ^ 1571 := by rw [pow_add]
          _ = 834855739 := by rw [factor_2_10]; decide
      have factor_2_12 : (26 : ZMod 2059318801) ^ 6284 = 195484003 := by
        calc
          (26 : ZMod 2059318801) ^ 6284 = (26 : ZMod 2059318801) ^ (3142 + 3142) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 3142 * (26 : ZMod 2059318801) ^ 3142 := by rw [pow_add]
          _ = 195484003 := by rw [factor_2_11]; decide
      have factor_2_13 : (26 : ZMod 2059318801) ^ 12569 = 248320527 := by
        calc
          (26 : ZMod 2059318801) ^ 12569 = (26 : ZMod 2059318801) ^ (6284 + 6284 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 6284 * (26 : ZMod 2059318801) ^ 6284) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 248320527 := by rw [factor_2_12]; decide
      have factor_2_14 : (26 : ZMod 2059318801) ^ 25138 = 1348898692 := by
        calc
          (26 : ZMod 2059318801) ^ 25138 = (26 : ZMod 2059318801) ^ (12569 + 12569) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 12569 * (26 : ZMod 2059318801) ^ 12569 := by rw [pow_add]
          _ = 1348898692 := by rw [factor_2_13]; decide
      have factor_2_15 : (26 : ZMod 2059318801) ^ 50276 = 1851238426 := by
        calc
          (26 : ZMod 2059318801) ^ 50276 = (26 : ZMod 2059318801) ^ (25138 + 25138) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 25138 * (26 : ZMod 2059318801) ^ 25138 := by rw [pow_add]
          _ = 1851238426 := by rw [factor_2_14]; decide
      have factor_2_16 : (26 : ZMod 2059318801) ^ 100552 = 1076309097 := by
        calc
          (26 : ZMod 2059318801) ^ 100552 = (26 : ZMod 2059318801) ^ (50276 + 50276) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 50276 * (26 : ZMod 2059318801) ^ 50276 := by rw [pow_add]
          _ = 1076309097 := by rw [factor_2_15]; decide
      have factor_2_17 : (26 : ZMod 2059318801) ^ 201105 = 1322535505 := by
        calc
          (26 : ZMod 2059318801) ^ 201105 = (26 : ZMod 2059318801) ^ (100552 + 100552 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 100552 * (26 : ZMod 2059318801) ^ 100552) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1322535505 := by rw [factor_2_16]; decide
      have factor_2_18 : (26 : ZMod 2059318801) ^ 402210 = 1443422012 := by
        calc
          (26 : ZMod 2059318801) ^ 402210 = (26 : ZMod 2059318801) ^ (201105 + 201105) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 201105 * (26 : ZMod 2059318801) ^ 201105 := by rw [pow_add]
          _ = 1443422012 := by rw [factor_2_17]; decide
      have factor_2_19 : (26 : ZMod 2059318801) ^ 804421 = 296528509 := by
        calc
          (26 : ZMod 2059318801) ^ 804421 = (26 : ZMod 2059318801) ^ (402210 + 402210 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 402210 * (26 : ZMod 2059318801) ^ 402210) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 296528509 := by rw [factor_2_18]; decide
      have factor_2_20 : (26 : ZMod 2059318801) ^ 1608842 = 44556105 := by
        calc
          (26 : ZMod 2059318801) ^ 1608842 = (26 : ZMod 2059318801) ^ (804421 + 804421) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 804421 * (26 : ZMod 2059318801) ^ 804421 := by rw [pow_add]
          _ = 44556105 := by rw [factor_2_19]; decide
      have factor_2_21 : (26 : ZMod 2059318801) ^ 3217685 = 1106698253 := by
        calc
          (26 : ZMod 2059318801) ^ 3217685 = (26 : ZMod 2059318801) ^ (1608842 + 1608842 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 1608842 * (26 : ZMod 2059318801) ^ 1608842) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1106698253 := by rw [factor_2_20]; decide
      have factor_2_22 : (26 : ZMod 2059318801) ^ 6435371 = 291707509 := by
        calc
          (26 : ZMod 2059318801) ^ 6435371 = (26 : ZMod 2059318801) ^ (3217685 + 3217685 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 3217685 * (26 : ZMod 2059318801) ^ 3217685) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 291707509 := by rw [factor_2_21]; decide
      have factor_2_23 : (26 : ZMod 2059318801) ^ 12870742 = 63316404 := by
        calc
          (26 : ZMod 2059318801) ^ 12870742 = (26 : ZMod 2059318801) ^ (6435371 + 6435371) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 6435371 * (26 : ZMod 2059318801) ^ 6435371 := by rw [pow_add]
          _ = 63316404 := by rw [factor_2_22]; decide
      have factor_2_24 : (26 : ZMod 2059318801) ^ 25741485 = 528576266 := by
        calc
          (26 : ZMod 2059318801) ^ 25741485 = (26 : ZMod 2059318801) ^ (12870742 + 12870742 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 12870742 * (26 : ZMod 2059318801) ^ 12870742) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 528576266 := by rw [factor_2_23]; decide
      have factor_2_25 : (26 : ZMod 2059318801) ^ 51482970 = 729394286 := by
        calc
          (26 : ZMod 2059318801) ^ 51482970 = (26 : ZMod 2059318801) ^ (25741485 + 25741485) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 25741485 * (26 : ZMod 2059318801) ^ 25741485 := by rw [pow_add]
          _ = 729394286 := by rw [factor_2_24]; decide
      have factor_2_26 : (26 : ZMod 2059318801) ^ 102965940 = 1137666161 := by
        calc
          (26 : ZMod 2059318801) ^ 102965940 = (26 : ZMod 2059318801) ^ (51482970 + 51482970) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 51482970 * (26 : ZMod 2059318801) ^ 51482970 := by rw [pow_add]
          _ = 1137666161 := by rw [factor_2_25]; decide
      have factor_2_27 : (26 : ZMod 2059318801) ^ 205931880 = 1578430343 := by
        calc
          (26 : ZMod 2059318801) ^ 205931880 = (26 : ZMod 2059318801) ^ (102965940 + 102965940) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 102965940 * (26 : ZMod 2059318801) ^ 102965940 := by rw [pow_add]
          _ = 1578430343 := by rw [factor_2_26]; decide
      have factor_2_28 : (26 : ZMod 2059318801) ^ 411863760 = 147660748 := by
        calc
          (26 : ZMod 2059318801) ^ 411863760 = (26 : ZMod 2059318801) ^ (205931880 + 205931880) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 205931880 * (26 : ZMod 2059318801) ^ 205931880 := by rw [pow_add]
          _ = 147660748 := by rw [factor_2_27]; decide
      change (26 : ZMod 2059318801) ^ 411863760 ≠ 1
      rw [factor_2_28]
      decide
    ·
      have factor_3_0 : (26 : ZMod 2059318801) ^ 1 = 26 := by norm_num
      have factor_3_1 : (26 : ZMod 2059318801) ^ 2 = 676 := by
        calc
          (26 : ZMod 2059318801) ^ 2 = (26 : ZMod 2059318801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 1 * (26 : ZMod 2059318801) ^ 1 := by rw [pow_add]
          _ = 676 := by rw [factor_3_0]; decide
      have factor_3_2 : (26 : ZMod 2059318801) ^ 4 = 456976 := by
        calc
          (26 : ZMod 2059318801) ^ 4 = (26 : ZMod 2059318801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 2 * (26 : ZMod 2059318801) ^ 2 := by rw [pow_add]
          _ = 456976 := by rw [factor_3_1]; decide
      have factor_3_3 : (26 : ZMod 2059318801) ^ 8 = 835865675 := by
        calc
          (26 : ZMod 2059318801) ^ 8 = (26 : ZMod 2059318801) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 4 * (26 : ZMod 2059318801) ^ 4 := by rw [pow_add]
          _ = 835865675 := by rw [factor_3_2]; decide
      have factor_3_4 : (26 : ZMod 2059318801) ^ 17 = 747695842 := by
        calc
          (26 : ZMod 2059318801) ^ 17 = (26 : ZMod 2059318801) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 8 * (26 : ZMod 2059318801) ^ 8) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 747695842 := by rw [factor_3_3]; decide
      have factor_3_5 : (26 : ZMod 2059318801) ^ 35 = 431091471 := by
        calc
          (26 : ZMod 2059318801) ^ 35 = (26 : ZMod 2059318801) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 17 * (26 : ZMod 2059318801) ^ 17) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 431091471 := by rw [factor_3_4]; decide
      have factor_3_6 : (26 : ZMod 2059318801) ^ 70 = 218257277 := by
        calc
          (26 : ZMod 2059318801) ^ 70 = (26 : ZMod 2059318801) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 35 * (26 : ZMod 2059318801) ^ 35 := by rw [pow_add]
          _ = 218257277 := by rw [factor_3_5]; decide
      have factor_3_7 : (26 : ZMod 2059318801) ^ 140 = 263927092 := by
        calc
          (26 : ZMod 2059318801) ^ 140 = (26 : ZMod 2059318801) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 70 * (26 : ZMod 2059318801) ^ 70 := by rw [pow_add]
          _ = 263927092 := by rw [factor_3_6]; decide
      have factor_3_8 : (26 : ZMod 2059318801) ^ 280 = 1195162954 := by
        calc
          (26 : ZMod 2059318801) ^ 280 = (26 : ZMod 2059318801) ^ (140 + 140) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 140 * (26 : ZMod 2059318801) ^ 140 := by rw [pow_add]
          _ = 1195162954 := by rw [factor_3_7]; decide
      have factor_3_9 : (26 : ZMod 2059318801) ^ 561 = 1435326230 := by
        calc
          (26 : ZMod 2059318801) ^ 561 = (26 : ZMod 2059318801) ^ (280 + 280 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 280 * (26 : ZMod 2059318801) ^ 280) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1435326230 := by rw [factor_3_8]; decide
      have factor_3_10 : (26 : ZMod 2059318801) ^ 1122 = 823352143 := by
        calc
          (26 : ZMod 2059318801) ^ 1122 = (26 : ZMod 2059318801) ^ (561 + 561) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 561 * (26 : ZMod 2059318801) ^ 561 := by rw [pow_add]
          _ = 823352143 := by rw [factor_3_9]; decide
      have factor_3_11 : (26 : ZMod 2059318801) ^ 2244 = 1368750475 := by
        calc
          (26 : ZMod 2059318801) ^ 2244 = (26 : ZMod 2059318801) ^ (1122 + 1122) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 1122 * (26 : ZMod 2059318801) ^ 1122 := by rw [pow_add]
          _ = 1368750475 := by rw [factor_3_10]; decide
      have factor_3_12 : (26 : ZMod 2059318801) ^ 4488 = 1165101515 := by
        calc
          (26 : ZMod 2059318801) ^ 4488 = (26 : ZMod 2059318801) ^ (2244 + 2244) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 2244 * (26 : ZMod 2059318801) ^ 2244 := by rw [pow_add]
          _ = 1165101515 := by rw [factor_3_11]; decide
      have factor_3_13 : (26 : ZMod 2059318801) ^ 8977 = 322679516 := by
        calc
          (26 : ZMod 2059318801) ^ 8977 = (26 : ZMod 2059318801) ^ (4488 + 4488 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 4488 * (26 : ZMod 2059318801) ^ 4488) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 322679516 := by rw [factor_3_12]; decide
      have factor_3_14 : (26 : ZMod 2059318801) ^ 17955 = 1712803498 := by
        calc
          (26 : ZMod 2059318801) ^ 17955 = (26 : ZMod 2059318801) ^ (8977 + 8977 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 8977 * (26 : ZMod 2059318801) ^ 8977) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1712803498 := by rw [factor_3_13]; decide
      have factor_3_15 : (26 : ZMod 2059318801) ^ 35911 = 1768033492 := by
        calc
          (26 : ZMod 2059318801) ^ 35911 = (26 : ZMod 2059318801) ^ (17955 + 17955 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 17955 * (26 : ZMod 2059318801) ^ 17955) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1768033492 := by rw [factor_3_14]; decide
      have factor_3_16 : (26 : ZMod 2059318801) ^ 71823 = 541172947 := by
        calc
          (26 : ZMod 2059318801) ^ 71823 = (26 : ZMod 2059318801) ^ (35911 + 35911 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 35911 * (26 : ZMod 2059318801) ^ 35911) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 541172947 := by rw [factor_3_15]; decide
      have factor_3_17 : (26 : ZMod 2059318801) ^ 143646 = 1826171973 := by
        calc
          (26 : ZMod 2059318801) ^ 143646 = (26 : ZMod 2059318801) ^ (71823 + 71823) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 71823 * (26 : ZMod 2059318801) ^ 71823 := by rw [pow_add]
          _ = 1826171973 := by rw [factor_3_16]; decide
      have factor_3_18 : (26 : ZMod 2059318801) ^ 287293 = 109983822 := by
        calc
          (26 : ZMod 2059318801) ^ 287293 = (26 : ZMod 2059318801) ^ (143646 + 143646 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 143646 * (26 : ZMod 2059318801) ^ 143646) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 109983822 := by rw [factor_3_17]; decide
      have factor_3_19 : (26 : ZMod 2059318801) ^ 574586 = 405334883 := by
        calc
          (26 : ZMod 2059318801) ^ 574586 = (26 : ZMod 2059318801) ^ (287293 + 287293) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 287293 * (26 : ZMod 2059318801) ^ 287293 := by rw [pow_add]
          _ = 405334883 := by rw [factor_3_18]; decide
      have factor_3_20 : (26 : ZMod 2059318801) ^ 1149173 = 371297305 := by
        calc
          (26 : ZMod 2059318801) ^ 1149173 = (26 : ZMod 2059318801) ^ (574586 + 574586 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 574586 * (26 : ZMod 2059318801) ^ 574586) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 371297305 := by rw [factor_3_19]; decide
      have factor_3_21 : (26 : ZMod 2059318801) ^ 2298346 = 542822138 := by
        calc
          (26 : ZMod 2059318801) ^ 2298346 = (26 : ZMod 2059318801) ^ (1149173 + 1149173) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 1149173 * (26 : ZMod 2059318801) ^ 1149173 := by rw [pow_add]
          _ = 542822138 := by rw [factor_3_20]; decide
      have factor_3_22 : (26 : ZMod 2059318801) ^ 4596693 = 394557329 := by
        calc
          (26 : ZMod 2059318801) ^ 4596693 = (26 : ZMod 2059318801) ^ (2298346 + 2298346 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 2298346 * (26 : ZMod 2059318801) ^ 2298346) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 394557329 := by rw [factor_3_21]; decide
      have factor_3_23 : (26 : ZMod 2059318801) ^ 9193387 = 1334212892 := by
        calc
          (26 : ZMod 2059318801) ^ 9193387 = (26 : ZMod 2059318801) ^ (4596693 + 4596693 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 4596693 * (26 : ZMod 2059318801) ^ 4596693) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1334212892 := by rw [factor_3_22]; decide
      have factor_3_24 : (26 : ZMod 2059318801) ^ 18386775 = 1522203060 := by
        calc
          (26 : ZMod 2059318801) ^ 18386775 = (26 : ZMod 2059318801) ^ (9193387 + 9193387 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 9193387 * (26 : ZMod 2059318801) ^ 9193387) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1522203060 := by rw [factor_3_23]; decide
      have factor_3_25 : (26 : ZMod 2059318801) ^ 36773550 = 2004837456 := by
        calc
          (26 : ZMod 2059318801) ^ 36773550 = (26 : ZMod 2059318801) ^ (18386775 + 18386775) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 18386775 * (26 : ZMod 2059318801) ^ 18386775 := by rw [pow_add]
          _ = 2004837456 := by rw [factor_3_24]; decide
      have factor_3_26 : (26 : ZMod 2059318801) ^ 73547100 = 1324637267 := by
        calc
          (26 : ZMod 2059318801) ^ 73547100 = (26 : ZMod 2059318801) ^ (36773550 + 36773550) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 36773550 * (26 : ZMod 2059318801) ^ 36773550 := by rw [pow_add]
          _ = 1324637267 := by rw [factor_3_25]; decide
      have factor_3_27 : (26 : ZMod 2059318801) ^ 147094200 = 1080182944 := by
        calc
          (26 : ZMod 2059318801) ^ 147094200 = (26 : ZMod 2059318801) ^ (73547100 + 73547100) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 73547100 * (26 : ZMod 2059318801) ^ 73547100 := by rw [pow_add]
          _ = 1080182944 := by rw [factor_3_26]; decide
      have factor_3_28 : (26 : ZMod 2059318801) ^ 294188400 = 1372505943 := by
        calc
          (26 : ZMod 2059318801) ^ 294188400 = (26 : ZMod 2059318801) ^ (147094200 + 147094200) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 147094200 * (26 : ZMod 2059318801) ^ 147094200 := by rw [pow_add]
          _ = 1372505943 := by rw [factor_3_27]; decide
      change (26 : ZMod 2059318801) ^ 294188400 ≠ 1
      rw [factor_3_28]
      decide
    ·
      have factor_4_0 : (26 : ZMod 2059318801) ^ 1 = 26 := by norm_num
      have factor_4_1 : (26 : ZMod 2059318801) ^ 2 = 676 := by
        calc
          (26 : ZMod 2059318801) ^ 2 = (26 : ZMod 2059318801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 1 * (26 : ZMod 2059318801) ^ 1 := by rw [pow_add]
          _ = 676 := by rw [factor_4_0]; decide
      have factor_4_2 : (26 : ZMod 2059318801) ^ 5 = 11881376 := by
        calc
          (26 : ZMod 2059318801) ^ 5 = (26 : ZMod 2059318801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 2 * (26 : ZMod 2059318801) ^ 2) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 11881376 := by rw [factor_4_1]; decide
      have factor_4_3 : (26 : ZMod 2059318801) ^ 11 = 2054096267 := by
        calc
          (26 : ZMod 2059318801) ^ 11 = (26 : ZMod 2059318801) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 5 * (26 : ZMod 2059318801) ^ 5) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 2054096267 := by rw [factor_4_2]; decide
      have factor_4_4 : (26 : ZMod 2059318801) ^ 22 = 1243180712 := by
        calc
          (26 : ZMod 2059318801) ^ 22 = (26 : ZMod 2059318801) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 11 * (26 : ZMod 2059318801) ^ 11 := by rw [pow_add]
          _ = 1243180712 := by rw [factor_4_3]; decide
      have factor_4_5 : (26 : ZMod 2059318801) ^ 44 = 404484088 := by
        calc
          (26 : ZMod 2059318801) ^ 44 = (26 : ZMod 2059318801) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 22 * (26 : ZMod 2059318801) ^ 22 := by rw [pow_add]
          _ = 404484088 := by rw [factor_4_4]; decide
      have factor_4_6 : (26 : ZMod 2059318801) ^ 89 = 455246401 := by
        calc
          (26 : ZMod 2059318801) ^ 89 = (26 : ZMod 2059318801) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 44 * (26 : ZMod 2059318801) ^ 44) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 455246401 := by rw [factor_4_5]; decide
      have factor_4_7 : (26 : ZMod 2059318801) ^ 178 = 1625526673 := by
        calc
          (26 : ZMod 2059318801) ^ 178 = (26 : ZMod 2059318801) ^ (89 + 89) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 89 * (26 : ZMod 2059318801) ^ 89 := by rw [pow_add]
          _ = 1625526673 := by rw [factor_4_6]; decide
      have factor_4_8 : (26 : ZMod 2059318801) ^ 357 = 282729976 := by
        calc
          (26 : ZMod 2059318801) ^ 357 = (26 : ZMod 2059318801) ^ (178 + 178 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 178 * (26 : ZMod 2059318801) ^ 178) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 282729976 := by rw [factor_4_7]; decide
      have factor_4_9 : (26 : ZMod 2059318801) ^ 714 = 1218145741 := by
        calc
          (26 : ZMod 2059318801) ^ 714 = (26 : ZMod 2059318801) ^ (357 + 357) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 357 * (26 : ZMod 2059318801) ^ 357 := by rw [pow_add]
          _ = 1218145741 := by rw [factor_4_8]; decide
      have factor_4_10 : (26 : ZMod 2059318801) ^ 1428 = 1856163171 := by
        calc
          (26 : ZMod 2059318801) ^ 1428 = (26 : ZMod 2059318801) ^ (714 + 714) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 714 * (26 : ZMod 2059318801) ^ 714 := by rw [pow_add]
          _ = 1856163171 := by rw [factor_4_9]; decide
      have factor_4_11 : (26 : ZMod 2059318801) ^ 2856 = 1573071220 := by
        calc
          (26 : ZMod 2059318801) ^ 2856 = (26 : ZMod 2059318801) ^ (1428 + 1428) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 1428 * (26 : ZMod 2059318801) ^ 1428 := by rw [pow_add]
          _ = 1573071220 := by rw [factor_4_10]; decide
      have factor_4_12 : (26 : ZMod 2059318801) ^ 5713 = 526049612 := by
        calc
          (26 : ZMod 2059318801) ^ 5713 = (26 : ZMod 2059318801) ^ (2856 + 2856 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 2856 * (26 : ZMod 2059318801) ^ 2856) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 526049612 := by rw [factor_4_11]; decide
      have factor_4_13 : (26 : ZMod 2059318801) ^ 11426 = 132665233 := by
        calc
          (26 : ZMod 2059318801) ^ 11426 = (26 : ZMod 2059318801) ^ (5713 + 5713) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 5713 * (26 : ZMod 2059318801) ^ 5713 := by rw [pow_add]
          _ = 132665233 := by rw [factor_4_12]; decide
      have factor_4_14 : (26 : ZMod 2059318801) ^ 22852 = 1185532943 := by
        calc
          (26 : ZMod 2059318801) ^ 22852 = (26 : ZMod 2059318801) ^ (11426 + 11426) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 11426 * (26 : ZMod 2059318801) ^ 11426 := by rw [pow_add]
          _ = 1185532943 := by rw [factor_4_13]; decide
      have factor_4_15 : (26 : ZMod 2059318801) ^ 45705 = 215243497 := by
        calc
          (26 : ZMod 2059318801) ^ 45705 = (26 : ZMod 2059318801) ^ (22852 + 22852 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 22852 * (26 : ZMod 2059318801) ^ 22852) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 215243497 := by rw [factor_4_14]; decide
      have factor_4_16 : (26 : ZMod 2059318801) ^ 91411 = 726625826 := by
        calc
          (26 : ZMod 2059318801) ^ 91411 = (26 : ZMod 2059318801) ^ (45705 + 45705 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 45705 * (26 : ZMod 2059318801) ^ 45705) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 726625826 := by rw [factor_4_15]; decide
      have factor_4_17 : (26 : ZMod 2059318801) ^ 182823 = 559728540 := by
        calc
          (26 : ZMod 2059318801) ^ 182823 = (26 : ZMod 2059318801) ^ (91411 + 91411 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 91411 * (26 : ZMod 2059318801) ^ 91411) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 559728540 := by rw [factor_4_16]; decide
      have factor_4_18 : (26 : ZMod 2059318801) ^ 365646 = 1440151437 := by
        calc
          (26 : ZMod 2059318801) ^ 365646 = (26 : ZMod 2059318801) ^ (182823 + 182823) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 182823 * (26 : ZMod 2059318801) ^ 182823 := by rw [pow_add]
          _ = 1440151437 := by rw [factor_4_17]; decide
      have factor_4_19 : (26 : ZMod 2059318801) ^ 731292 = 46913856 := by
        calc
          (26 : ZMod 2059318801) ^ 731292 = (26 : ZMod 2059318801) ^ (365646 + 365646) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 365646 * (26 : ZMod 2059318801) ^ 365646 := by rw [pow_add]
          _ = 46913856 := by rw [factor_4_18]; decide
      have factor_4_20 : (26 : ZMod 2059318801) ^ 1462584 = 560307180 := by
        calc
          (26 : ZMod 2059318801) ^ 1462584 = (26 : ZMod 2059318801) ^ (731292 + 731292) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 731292 * (26 : ZMod 2059318801) ^ 731292 := by rw [pow_add]
          _ = 560307180 := by rw [factor_4_19]; decide
      have factor_4_21 : (26 : ZMod 2059318801) ^ 2925168 = 392715522 := by
        calc
          (26 : ZMod 2059318801) ^ 2925168 = (26 : ZMod 2059318801) ^ (1462584 + 1462584) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 1462584 * (26 : ZMod 2059318801) ^ 1462584 := by rw [pow_add]
          _ = 392715522 := by rw [factor_4_20]; decide
      have factor_4_22 : (26 : ZMod 2059318801) ^ 5850337 = 702654693 := by
        calc
          (26 : ZMod 2059318801) ^ 5850337 = (26 : ZMod 2059318801) ^ (2925168 + 2925168 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 2925168 * (26 : ZMod 2059318801) ^ 2925168) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 702654693 := by rw [factor_4_21]; decide
      have factor_4_23 : (26 : ZMod 2059318801) ^ 11700675 = 216903243 := by
        calc
          (26 : ZMod 2059318801) ^ 11700675 = (26 : ZMod 2059318801) ^ (5850337 + 5850337 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 5850337 * (26 : ZMod 2059318801) ^ 5850337) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 216903243 := by rw [factor_4_22]; decide
      have factor_4_24 : (26 : ZMod 2059318801) ^ 23401350 = 716325537 := by
        calc
          (26 : ZMod 2059318801) ^ 23401350 = (26 : ZMod 2059318801) ^ (11700675 + 11700675) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 11700675 * (26 : ZMod 2059318801) ^ 11700675 := by rw [pow_add]
          _ = 716325537 := by rw [factor_4_23]; decide
      have factor_4_25 : (26 : ZMod 2059318801) ^ 46802700 = 1231261091 := by
        calc
          (26 : ZMod 2059318801) ^ 46802700 = (26 : ZMod 2059318801) ^ (23401350 + 23401350) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 23401350 * (26 : ZMod 2059318801) ^ 23401350 := by rw [pow_add]
          _ = 1231261091 := by rw [factor_4_24]; decide
      have factor_4_26 : (26 : ZMod 2059318801) ^ 93605400 = 114797835 := by
        calc
          (26 : ZMod 2059318801) ^ 93605400 = (26 : ZMod 2059318801) ^ (46802700 + 46802700) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 46802700 * (26 : ZMod 2059318801) ^ 46802700 := by rw [pow_add]
          _ = 114797835 := by rw [factor_4_25]; decide
      have factor_4_27 : (26 : ZMod 2059318801) ^ 187210800 = 211208158 := by
        calc
          (26 : ZMod 2059318801) ^ 187210800 = (26 : ZMod 2059318801) ^ (93605400 + 93605400) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 93605400 * (26 : ZMod 2059318801) ^ 93605400 := by rw [pow_add]
          _ = 211208158 := by rw [factor_4_26]; decide
      change (26 : ZMod 2059318801) ^ 187210800 ≠ 1
      rw [factor_4_27]
      decide
    ·
      have factor_5_0 : (26 : ZMod 2059318801) ^ 1 = 26 := by norm_num
      have factor_5_1 : (26 : ZMod 2059318801) ^ 3 = 17576 := by
        calc
          (26 : ZMod 2059318801) ^ 3 = (26 : ZMod 2059318801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 1 * (26 : ZMod 2059318801) ^ 1) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 17576 := by rw [factor_5_0]; decide
      have factor_5_2 : (26 : ZMod 2059318801) ^ 7 = 1853853773 := by
        calc
          (26 : ZMod 2059318801) ^ 7 = (26 : ZMod 2059318801) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 3 * (26 : ZMod 2059318801) ^ 3) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1853853773 := by rw [factor_5_1]; decide
      have factor_5_3 : (26 : ZMod 2059318801) ^ 14 = 878088461 := by
        calc
          (26 : ZMod 2059318801) ^ 14 = (26 : ZMod 2059318801) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 7 * (26 : ZMod 2059318801) ^ 7 := by rw [pow_add]
          _ = 878088461 := by rw [factor_5_2]; decide
      have factor_5_4 : (26 : ZMod 2059318801) ^ 28 = 998039766 := by
        calc
          (26 : ZMod 2059318801) ^ 28 = (26 : ZMod 2059318801) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 14 * (26 : ZMod 2059318801) ^ 14 := by rw [pow_add]
          _ = 998039766 := by rw [factor_5_3]; decide
      have factor_5_5 : (26 : ZMod 2059318801) ^ 57 = 1755419722 := by
        calc
          (26 : ZMod 2059318801) ^ 57 = (26 : ZMod 2059318801) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 28 * (26 : ZMod 2059318801) ^ 28) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1755419722 := by rw [factor_5_4]; decide
      have factor_5_6 : (26 : ZMod 2059318801) ^ 115 = 111343869 := by
        calc
          (26 : ZMod 2059318801) ^ 115 = (26 : ZMod 2059318801) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 57 * (26 : ZMod 2059318801) ^ 57) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 111343869 := by rw [factor_5_5]; decide
      have factor_5_7 : (26 : ZMod 2059318801) ^ 231 = 1466936467 := by
        calc
          (26 : ZMod 2059318801) ^ 231 = (26 : ZMod 2059318801) ^ (115 + 115 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 115 * (26 : ZMod 2059318801) ^ 115) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1466936467 := by rw [factor_5_6]; decide
      have factor_5_8 : (26 : ZMod 2059318801) ^ 462 = 1450392032 := by
        calc
          (26 : ZMod 2059318801) ^ 462 = (26 : ZMod 2059318801) ^ (231 + 231) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 231 * (26 : ZMod 2059318801) ^ 231 := by rw [pow_add]
          _ = 1450392032 := by rw [factor_5_7]; decide
      have factor_5_9 : (26 : ZMod 2059318801) ^ 924 = 1834920597 := by
        calc
          (26 : ZMod 2059318801) ^ 924 = (26 : ZMod 2059318801) ^ (462 + 462) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 462 * (26 : ZMod 2059318801) ^ 462 := by rw [pow_add]
          _ = 1834920597 := by rw [factor_5_8]; decide
      have factor_5_10 : (26 : ZMod 2059318801) ^ 1848 = 26346372 := by
        calc
          (26 : ZMod 2059318801) ^ 1848 = (26 : ZMod 2059318801) ^ (924 + 924) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 924 * (26 : ZMod 2059318801) ^ 924 := by rw [pow_add]
          _ = 26346372 := by rw [factor_5_9]; decide
      have factor_5_11 : (26 : ZMod 2059318801) ^ 3696 = 847946916 := by
        calc
          (26 : ZMod 2059318801) ^ 3696 = (26 : ZMod 2059318801) ^ (1848 + 1848) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 1848 * (26 : ZMod 2059318801) ^ 1848 := by rw [pow_add]
          _ = 847946916 := by rw [factor_5_10]; decide
      have factor_5_12 : (26 : ZMod 2059318801) ^ 7393 = 896569941 := by
        calc
          (26 : ZMod 2059318801) ^ 7393 = (26 : ZMod 2059318801) ^ (3696 + 3696 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 3696 * (26 : ZMod 2059318801) ^ 3696) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 896569941 := by rw [factor_5_11]; decide
      have factor_5_13 : (26 : ZMod 2059318801) ^ 14787 = 1045300631 := by
        calc
          (26 : ZMod 2059318801) ^ 14787 = (26 : ZMod 2059318801) ^ (7393 + 7393 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 7393 * (26 : ZMod 2059318801) ^ 7393) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1045300631 := by rw [factor_5_12]; decide
      have factor_5_14 : (26 : ZMod 2059318801) ^ 29574 = 503165630 := by
        calc
          (26 : ZMod 2059318801) ^ 29574 = (26 : ZMod 2059318801) ^ (14787 + 14787) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 14787 * (26 : ZMod 2059318801) ^ 14787 := by rw [pow_add]
          _ = 503165630 := by rw [factor_5_13]; decide
      have factor_5_15 : (26 : ZMod 2059318801) ^ 59148 = 1509501445 := by
        calc
          (26 : ZMod 2059318801) ^ 59148 = (26 : ZMod 2059318801) ^ (29574 + 29574) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 29574 * (26 : ZMod 2059318801) ^ 29574 := by rw [pow_add]
          _ = 1509501445 := by rw [factor_5_14]; decide
      have factor_5_16 : (26 : ZMod 2059318801) ^ 118297 = 63088788 := by
        calc
          (26 : ZMod 2059318801) ^ 118297 = (26 : ZMod 2059318801) ^ (59148 + 59148 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 59148 * (26 : ZMod 2059318801) ^ 59148) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 63088788 := by rw [factor_5_15]; decide
      have factor_5_17 : (26 : ZMod 2059318801) ^ 236594 = 1453662572 := by
        calc
          (26 : ZMod 2059318801) ^ 236594 = (26 : ZMod 2059318801) ^ (118297 + 118297) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 118297 * (26 : ZMod 2059318801) ^ 118297 := by rw [pow_add]
          _ = 1453662572 := by rw [factor_5_16]; decide
      have factor_5_18 : (26 : ZMod 2059318801) ^ 473189 = 1613051323 := by
        calc
          (26 : ZMod 2059318801) ^ 473189 = (26 : ZMod 2059318801) ^ (236594 + 236594 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 236594 * (26 : ZMod 2059318801) ^ 236594) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1613051323 := by rw [factor_5_17]; decide
      have factor_5_19 : (26 : ZMod 2059318801) ^ 946378 = 2053890285 := by
        calc
          (26 : ZMod 2059318801) ^ 946378 = (26 : ZMod 2059318801) ^ (473189 + 473189) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 473189 * (26 : ZMod 2059318801) ^ 473189 := by rw [pow_add]
          _ = 2053890285 := by rw [factor_5_18]; decide
      have factor_5_20 : (26 : ZMod 2059318801) ^ 1892756 = 1993238747 := by
        calc
          (26 : ZMod 2059318801) ^ 1892756 = (26 : ZMod 2059318801) ^ (946378 + 946378) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 946378 * (26 : ZMod 2059318801) ^ 946378 := by rw [pow_add]
          _ = 1993238747 := by rw [factor_5_19]; decide
      have factor_5_21 : (26 : ZMod 2059318801) ^ 3785512 = 128958919 := by
        calc
          (26 : ZMod 2059318801) ^ 3785512 = (26 : ZMod 2059318801) ^ (1892756 + 1892756) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 1892756 * (26 : ZMod 2059318801) ^ 1892756 := by rw [pow_add]
          _ = 128958919 := by rw [factor_5_20]; decide
      have factor_5_22 : (26 : ZMod 2059318801) ^ 7571025 = 1191077667 := by
        calc
          (26 : ZMod 2059318801) ^ 7571025 = (26 : ZMod 2059318801) ^ (3785512 + 3785512 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 3785512 * (26 : ZMod 2059318801) ^ 3785512) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1191077667 := by rw [factor_5_21]; decide
      have factor_5_23 : (26 : ZMod 2059318801) ^ 15142050 = 1802331065 := by
        calc
          (26 : ZMod 2059318801) ^ 15142050 = (26 : ZMod 2059318801) ^ (7571025 + 7571025) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 7571025 * (26 : ZMod 2059318801) ^ 7571025 := by rw [pow_add]
          _ = 1802331065 := by rw [factor_5_22]; decide
      have factor_5_24 : (26 : ZMod 2059318801) ^ 30284100 = 659414730 := by
        calc
          (26 : ZMod 2059318801) ^ 30284100 = (26 : ZMod 2059318801) ^ (15142050 + 15142050) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 15142050 * (26 : ZMod 2059318801) ^ 15142050 := by rw [pow_add]
          _ = 659414730 := by rw [factor_5_23]; decide
      have factor_5_25 : (26 : ZMod 2059318801) ^ 60568200 = 1856308028 := by
        calc
          (26 : ZMod 2059318801) ^ 60568200 = (26 : ZMod 2059318801) ^ (30284100 + 30284100) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 30284100 * (26 : ZMod 2059318801) ^ 30284100 := by rw [pow_add]
          _ = 1856308028 := by rw [factor_5_24]; decide
      have factor_5_26 : (26 : ZMod 2059318801) ^ 121136400 = 264576419 := by
        calc
          (26 : ZMod 2059318801) ^ 121136400 = (26 : ZMod 2059318801) ^ (60568200 + 60568200) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 60568200 * (26 : ZMod 2059318801) ^ 60568200 := by rw [pow_add]
          _ = 264576419 := by rw [factor_5_25]; decide
      change (26 : ZMod 2059318801) ^ 121136400 ≠ 1
      rw [factor_5_26]
      decide
    ·
      have factor_6_0 : (26 : ZMod 2059318801) ^ 1 = 26 := by norm_num
      have factor_6_1 : (26 : ZMod 2059318801) ^ 3 = 17576 := by
        calc
          (26 : ZMod 2059318801) ^ 3 = (26 : ZMod 2059318801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 1 * (26 : ZMod 2059318801) ^ 1) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 17576 := by rw [factor_6_0]; decide
      have factor_6_2 : (26 : ZMod 2059318801) ^ 6 = 308915776 := by
        calc
          (26 : ZMod 2059318801) ^ 6 = (26 : ZMod 2059318801) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 3 * (26 : ZMod 2059318801) ^ 3 := by rw [pow_add]
          _ = 308915776 := by rw [factor_6_1]; decide
      have factor_6_3 : (26 : ZMod 2059318801) ^ 12 = 1923532917 := by
        calc
          (26 : ZMod 2059318801) ^ 12 = (26 : ZMod 2059318801) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 6 * (26 : ZMod 2059318801) ^ 6 := by rw [pow_add]
          _ = 1923532917 := by rw [factor_6_2]; decide
      have factor_6_4 : (26 : ZMod 2059318801) ^ 25 = 771715502 := by
        calc
          (26 : ZMod 2059318801) ^ 25 = (26 : ZMod 2059318801) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 12 * (26 : ZMod 2059318801) ^ 12) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 771715502 := by rw [factor_6_3]; decide
      have factor_6_5 : (26 : ZMod 2059318801) ^ 51 = 1301667848 := by
        calc
          (26 : ZMod 2059318801) ^ 51 = (26 : ZMod 2059318801) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 25 * (26 : ZMod 2059318801) ^ 25) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1301667848 := by rw [factor_6_4]; decide
      have factor_6_6 : (26 : ZMod 2059318801) ^ 103 = 636134518 := by
        calc
          (26 : ZMod 2059318801) ^ 103 = (26 : ZMod 2059318801) ^ (51 + 51 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 51 * (26 : ZMod 2059318801) ^ 51) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 636134518 := by rw [factor_6_5]; decide
      have factor_6_7 : (26 : ZMod 2059318801) ^ 206 = 306745392 := by
        calc
          (26 : ZMod 2059318801) ^ 206 = (26 : ZMod 2059318801) ^ (103 + 103) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 103 * (26 : ZMod 2059318801) ^ 103 := by rw [pow_add]
          _ = 306745392 := by rw [factor_6_6]; decide
      have factor_6_8 : (26 : ZMod 2059318801) ^ 413 = 916726612 := by
        calc
          (26 : ZMod 2059318801) ^ 413 = (26 : ZMod 2059318801) ^ (206 + 206 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 206 * (26 : ZMod 2059318801) ^ 206) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 916726612 := by rw [factor_6_7]; decide
      have factor_6_9 : (26 : ZMod 2059318801) ^ 826 = 1878145613 := by
        calc
          (26 : ZMod 2059318801) ^ 826 = (26 : ZMod 2059318801) ^ (413 + 413) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 413 * (26 : ZMod 2059318801) ^ 413 := by rw [pow_add]
          _ = 1878145613 := by rw [factor_6_8]; decide
      have factor_6_10 : (26 : ZMod 2059318801) ^ 1653 = 722891093 := by
        calc
          (26 : ZMod 2059318801) ^ 1653 = (26 : ZMod 2059318801) ^ (826 + 826 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 826 * (26 : ZMod 2059318801) ^ 826) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 722891093 := by rw [factor_6_9]; decide
      have factor_6_11 : (26 : ZMod 2059318801) ^ 3307 = 2043274109 := by
        calc
          (26 : ZMod 2059318801) ^ 3307 = (26 : ZMod 2059318801) ^ (1653 + 1653 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 1653 * (26 : ZMod 2059318801) ^ 1653) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 2043274109 := by rw [factor_6_10]; decide
      have factor_6_12 : (26 : ZMod 2059318801) ^ 6615 = 640997846 := by
        calc
          (26 : ZMod 2059318801) ^ 6615 = (26 : ZMod 2059318801) ^ (3307 + 3307 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 3307 * (26 : ZMod 2059318801) ^ 3307) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 640997846 := by rw [factor_6_11]; decide
      have factor_6_13 : (26 : ZMod 2059318801) ^ 13230 = 397277883 := by
        calc
          (26 : ZMod 2059318801) ^ 13230 = (26 : ZMod 2059318801) ^ (6615 + 6615) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 6615 * (26 : ZMod 2059318801) ^ 6615 := by rw [pow_add]
          _ = 397277883 := by rw [factor_6_12]; decide
      have factor_6_14 : (26 : ZMod 2059318801) ^ 26461 = 1982820230 := by
        calc
          (26 : ZMod 2059318801) ^ 26461 = (26 : ZMod 2059318801) ^ (13230 + 13230 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 13230 * (26 : ZMod 2059318801) ^ 13230) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1982820230 := by rw [factor_6_13]; decide
      have factor_6_15 : (26 : ZMod 2059318801) ^ 52922 = 1289357510 := by
        calc
          (26 : ZMod 2059318801) ^ 52922 = (26 : ZMod 2059318801) ^ (26461 + 26461) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 26461 * (26 : ZMod 2059318801) ^ 26461 := by rw [pow_add]
          _ = 1289357510 := by rw [factor_6_14]; decide
      have factor_6_16 : (26 : ZMod 2059318801) ^ 105844 = 847896488 := by
        calc
          (26 : ZMod 2059318801) ^ 105844 = (26 : ZMod 2059318801) ^ (52922 + 52922) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 52922 * (26 : ZMod 2059318801) ^ 52922 := by rw [pow_add]
          _ = 847896488 := by rw [factor_6_15]; decide
      have factor_6_17 : (26 : ZMod 2059318801) ^ 211689 = 228597939 := by
        calc
          (26 : ZMod 2059318801) ^ 211689 = (26 : ZMod 2059318801) ^ (105844 + 105844 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 105844 * (26 : ZMod 2059318801) ^ 105844) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 228597939 := by rw [factor_6_16]; decide
      have factor_6_18 : (26 : ZMod 2059318801) ^ 423379 = 1238985981 := by
        calc
          (26 : ZMod 2059318801) ^ 423379 = (26 : ZMod 2059318801) ^ (211689 + 211689 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 211689 * (26 : ZMod 2059318801) ^ 211689) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1238985981 := by rw [factor_6_17]; decide
      have factor_6_19 : (26 : ZMod 2059318801) ^ 846759 = 783188460 := by
        calc
          (26 : ZMod 2059318801) ^ 846759 = (26 : ZMod 2059318801) ^ (423379 + 423379 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 423379 * (26 : ZMod 2059318801) ^ 423379) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 783188460 := by rw [factor_6_18]; decide
      have factor_6_20 : (26 : ZMod 2059318801) ^ 1693518 = 431311402 := by
        calc
          (26 : ZMod 2059318801) ^ 1693518 = (26 : ZMod 2059318801) ^ (846759 + 846759) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 846759 * (26 : ZMod 2059318801) ^ 846759 := by rw [pow_add]
          _ = 431311402 := by rw [factor_6_19]; decide
      have factor_6_21 : (26 : ZMod 2059318801) ^ 3387037 = 1648391564 := by
        calc
          (26 : ZMod 2059318801) ^ 3387037 = (26 : ZMod 2059318801) ^ (1693518 + 1693518 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 1693518 * (26 : ZMod 2059318801) ^ 1693518) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1648391564 := by rw [factor_6_20]; decide
      have factor_6_22 : (26 : ZMod 2059318801) ^ 6774075 = 636987609 := by
        calc
          (26 : ZMod 2059318801) ^ 6774075 = (26 : ZMod 2059318801) ^ (3387037 + 3387037 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 3387037 * (26 : ZMod 2059318801) ^ 3387037) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 636987609 := by rw [factor_6_21]; decide
      have factor_6_23 : (26 : ZMod 2059318801) ^ 13548150 = 480904947 := by
        calc
          (26 : ZMod 2059318801) ^ 13548150 = (26 : ZMod 2059318801) ^ (6774075 + 6774075) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 6774075 * (26 : ZMod 2059318801) ^ 6774075 := by rw [pow_add]
          _ = 480904947 := by rw [factor_6_22]; decide
      have factor_6_24 : (26 : ZMod 2059318801) ^ 27096300 = 345029292 := by
        calc
          (26 : ZMod 2059318801) ^ 27096300 = (26 : ZMod 2059318801) ^ (13548150 + 13548150) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 13548150 * (26 : ZMod 2059318801) ^ 13548150 := by rw [pow_add]
          _ = 345029292 := by rw [factor_6_23]; decide
      have factor_6_25 : (26 : ZMod 2059318801) ^ 54192600 = 1945916811 := by
        calc
          (26 : ZMod 2059318801) ^ 54192600 = (26 : ZMod 2059318801) ^ (27096300 + 27096300) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 27096300 * (26 : ZMod 2059318801) ^ 27096300 := by rw [pow_add]
          _ = 1945916811 := by rw [factor_6_24]; decide
      have factor_6_26 : (26 : ZMod 2059318801) ^ 108385200 = 1999300912 := by
        calc
          (26 : ZMod 2059318801) ^ 108385200 = (26 : ZMod 2059318801) ^ (54192600 + 54192600) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 54192600 * (26 : ZMod 2059318801) ^ 54192600 := by rw [pow_add]
          _ = 1999300912 := by rw [factor_6_25]; decide
      change (26 : ZMod 2059318801) ^ 108385200 ≠ 1
      rw [factor_6_26]
      decide
    ·
      have factor_7_0 : (26 : ZMod 2059318801) ^ 1 = 26 := by norm_num
      have factor_7_1 : (26 : ZMod 2059318801) ^ 2 = 676 := by
        calc
          (26 : ZMod 2059318801) ^ 2 = (26 : ZMod 2059318801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 1 * (26 : ZMod 2059318801) ^ 1 := by rw [pow_add]
          _ = 676 := by rw [factor_7_0]; decide
      have factor_7_2 : (26 : ZMod 2059318801) ^ 5 = 11881376 := by
        calc
          (26 : ZMod 2059318801) ^ 5 = (26 : ZMod 2059318801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 2 * (26 : ZMod 2059318801) ^ 2) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 11881376 := by rw [factor_7_1]; decide
      have factor_7_3 : (26 : ZMod 2059318801) ^ 10 = 791844826 := by
        calc
          (26 : ZMod 2059318801) ^ 10 = (26 : ZMod 2059318801) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 5 * (26 : ZMod 2059318801) ^ 5 := by rw [pow_add]
          _ = 791844826 := by rw [factor_7_2]; decide
      have factor_7_4 : (26 : ZMod 2059318801) ^ 21 = 998269474 := by
        calc
          (26 : ZMod 2059318801) ^ 21 = (26 : ZMod 2059318801) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 10 * (26 : ZMod 2059318801) ^ 10) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 998269474 := by rw [factor_7_3]; decide
      have factor_7_5 : (26 : ZMod 2059318801) ^ 42 = 585493630 := by
        calc
          (26 : ZMod 2059318801) ^ 42 = (26 : ZMod 2059318801) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 21 * (26 : ZMod 2059318801) ^ 21 := by rw [pow_add]
          _ = 585493630 := by rw [factor_7_4]; decide
      have factor_7_6 : (26 : ZMod 2059318801) ^ 85 = 1917850234 := by
        calc
          (26 : ZMod 2059318801) ^ 85 = (26 : ZMod 2059318801) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 42 * (26 : ZMod 2059318801) ^ 42) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1917850234 := by rw [factor_7_5]; decide
      have factor_7_7 : (26 : ZMod 2059318801) ^ 170 = 1596555855 := by
        calc
          (26 : ZMod 2059318801) ^ 170 = (26 : ZMod 2059318801) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 85 * (26 : ZMod 2059318801) ^ 85 := by rw [pow_add]
          _ = 1596555855 := by rw [factor_7_6]; decide
      have factor_7_8 : (26 : ZMod 2059318801) ^ 341 = 446018217 := by
        calc
          (26 : ZMod 2059318801) ^ 341 = (26 : ZMod 2059318801) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 170 * (26 : ZMod 2059318801) ^ 170) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 446018217 := by rw [factor_7_7]; decide
      have factor_7_9 : (26 : ZMod 2059318801) ^ 683 = 623545185 := by
        calc
          (26 : ZMod 2059318801) ^ 683 = (26 : ZMod 2059318801) ^ (341 + 341 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 341 * (26 : ZMod 2059318801) ^ 341) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 623545185 := by rw [factor_7_8]; decide
      have factor_7_10 : (26 : ZMod 2059318801) ^ 1366 = 893524954 := by
        calc
          (26 : ZMod 2059318801) ^ 1366 = (26 : ZMod 2059318801) ^ (683 + 683) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 683 * (26 : ZMod 2059318801) ^ 683 := by rw [pow_add]
          _ = 893524954 := by rw [factor_7_9]; decide
      have factor_7_11 : (26 : ZMod 2059318801) ^ 2732 = 755644685 := by
        calc
          (26 : ZMod 2059318801) ^ 2732 = (26 : ZMod 2059318801) ^ (1366 + 1366) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 1366 * (26 : ZMod 2059318801) ^ 1366 := by rw [pow_add]
          _ = 755644685 := by rw [factor_7_10]; decide
      have factor_7_12 : (26 : ZMod 2059318801) ^ 5464 = 881092809 := by
        calc
          (26 : ZMod 2059318801) ^ 5464 = (26 : ZMod 2059318801) ^ (2732 + 2732) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 2732 * (26 : ZMod 2059318801) ^ 2732 := by rw [pow_add]
          _ = 881092809 := by rw [factor_7_11]; decide
      have factor_7_13 : (26 : ZMod 2059318801) ^ 10929 = 608509282 := by
        calc
          (26 : ZMod 2059318801) ^ 10929 = (26 : ZMod 2059318801) ^ (5464 + 5464 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 5464 * (26 : ZMod 2059318801) ^ 5464) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 608509282 := by rw [factor_7_12]; decide
      have factor_7_14 : (26 : ZMod 2059318801) ^ 21859 = 240599238 := by
        calc
          (26 : ZMod 2059318801) ^ 21859 = (26 : ZMod 2059318801) ^ (10929 + 10929 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 10929 * (26 : ZMod 2059318801) ^ 10929) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 240599238 := by rw [factor_7_13]; decide
      have factor_7_15 : (26 : ZMod 2059318801) ^ 43718 = 229225981 := by
        calc
          (26 : ZMod 2059318801) ^ 43718 = (26 : ZMod 2059318801) ^ (21859 + 21859) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 21859 * (26 : ZMod 2059318801) ^ 21859 := by rw [pow_add]
          _ = 229225981 := by rw [factor_7_14]; decide
      have factor_7_16 : (26 : ZMod 2059318801) ^ 87437 = 1893179968 := by
        calc
          (26 : ZMod 2059318801) ^ 87437 = (26 : ZMod 2059318801) ^ (43718 + 43718 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 43718 * (26 : ZMod 2059318801) ^ 43718) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1893179968 := by rw [factor_7_15]; decide
      have factor_7_17 : (26 : ZMod 2059318801) ^ 174874 = 1391616374 := by
        calc
          (26 : ZMod 2059318801) ^ 174874 = (26 : ZMod 2059318801) ^ (87437 + 87437) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 87437 * (26 : ZMod 2059318801) ^ 87437 := by rw [pow_add]
          _ = 1391616374 := by rw [factor_7_16]; decide
      have factor_7_18 : (26 : ZMod 2059318801) ^ 349748 = 1215680094 := by
        calc
          (26 : ZMod 2059318801) ^ 349748 = (26 : ZMod 2059318801) ^ (174874 + 174874) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 174874 * (26 : ZMod 2059318801) ^ 174874 := by rw [pow_add]
          _ = 1215680094 := by rw [factor_7_17]; decide
      have factor_7_19 : (26 : ZMod 2059318801) ^ 699496 = 320989374 := by
        calc
          (26 : ZMod 2059318801) ^ 699496 = (26 : ZMod 2059318801) ^ (349748 + 349748) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 349748 * (26 : ZMod 2059318801) ^ 349748 := by rw [pow_add]
          _ = 320989374 := by rw [factor_7_18]; decide
      have factor_7_20 : (26 : ZMod 2059318801) ^ 1398993 = 745938833 := by
        calc
          (26 : ZMod 2059318801) ^ 1398993 = (26 : ZMod 2059318801) ^ (699496 + 699496 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 699496 * (26 : ZMod 2059318801) ^ 699496) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 745938833 := by rw [factor_7_19]; decide
      have factor_7_21 : (26 : ZMod 2059318801) ^ 2797987 = 927245484 := by
        calc
          (26 : ZMod 2059318801) ^ 2797987 = (26 : ZMod 2059318801) ^ (1398993 + 1398993 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 1398993 * (26 : ZMod 2059318801) ^ 1398993) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 927245484 := by rw [factor_7_20]; decide
      have factor_7_22 : (26 : ZMod 2059318801) ^ 5595975 = 1470437971 := by
        calc
          (26 : ZMod 2059318801) ^ 5595975 = (26 : ZMod 2059318801) ^ (2797987 + 2797987 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = ((26 : ZMod 2059318801) ^ 2797987 * (26 : ZMod 2059318801) ^ 2797987) * (26 : ZMod 2059318801) := by rw [pow_succ, pow_add]
          _ = 1470437971 := by rw [factor_7_21]; decide
      have factor_7_23 : (26 : ZMod 2059318801) ^ 11191950 = 1170009503 := by
        calc
          (26 : ZMod 2059318801) ^ 11191950 = (26 : ZMod 2059318801) ^ (5595975 + 5595975) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 5595975 * (26 : ZMod 2059318801) ^ 5595975 := by rw [pow_add]
          _ = 1170009503 := by rw [factor_7_22]; decide
      have factor_7_24 : (26 : ZMod 2059318801) ^ 22383900 = 358771834 := by
        calc
          (26 : ZMod 2059318801) ^ 22383900 = (26 : ZMod 2059318801) ^ (11191950 + 11191950) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 11191950 * (26 : ZMod 2059318801) ^ 11191950 := by rw [pow_add]
          _ = 358771834 := by rw [factor_7_23]; decide
      have factor_7_25 : (26 : ZMod 2059318801) ^ 44767800 = 1451730796 := by
        calc
          (26 : ZMod 2059318801) ^ 44767800 = (26 : ZMod 2059318801) ^ (22383900 + 22383900) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 22383900 * (26 : ZMod 2059318801) ^ 22383900 := by rw [pow_add]
          _ = 1451730796 := by rw [factor_7_24]; decide
      have factor_7_26 : (26 : ZMod 2059318801) ^ 89535600 = 279704917 := by
        calc
          (26 : ZMod 2059318801) ^ 89535600 = (26 : ZMod 2059318801) ^ (44767800 + 44767800) :=
            congrArg (fun n : ℕ => (26 : ZMod 2059318801) ^ n) (by norm_num)
          _ = (26 : ZMod 2059318801) ^ 44767800 * (26 : ZMod 2059318801) ^ 44767800 := by rw [pow_add]
          _ = 279704917 := by rw [factor_7_25]; decide
      change (26 : ZMod 2059318801) ^ 89535600 ≠ 1
      rw [factor_7_26]
      decide

#print axioms prime_lucas_2059318801

end TotientTailPeriodKiller
end Erdos249257
