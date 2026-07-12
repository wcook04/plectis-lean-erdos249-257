import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1632785537 : Nat.Prime 1632785537 := by
  apply lucas_primality 1632785537 (3 : ZMod 1632785537)
  ·
      have fermat_0 : (3 : ZMod 1632785537) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 1632785537) ^ 3 = 27 := by
        calc
          (3 : ZMod 1632785537) ^ 3 = (3 : ZMod 1632785537) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 1 * (3 : ZMod 1632785537) ^ 1) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 1632785537) ^ 6 = 729 := by
        calc
          (3 : ZMod 1632785537) ^ 6 = (3 : ZMod 1632785537) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 3 * (3 : ZMod 1632785537) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 1632785537) ^ 12 = 531441 := by
        calc
          (3 : ZMod 1632785537) ^ 12 = (3 : ZMod 1632785537) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 6 * (3 : ZMod 1632785537) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 1632785537) ^ 24 = 1590424117 := by
        calc
          (3 : ZMod 1632785537) ^ 24 = (3 : ZMod 1632785537) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 12 * (3 : ZMod 1632785537) ^ 12 := by rw [pow_add]
          _ = 1590424117 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 1632785537) ^ 48 = 1451759605 := by
        calc
          (3 : ZMod 1632785537) ^ 48 = (3 : ZMod 1632785537) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 24 * (3 : ZMod 1632785537) ^ 24 := by rw [pow_add]
          _ = 1451759605 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 1632785537) ^ 97 = 771188898 := by
        calc
          (3 : ZMod 1632785537) ^ 97 = (3 : ZMod 1632785537) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 48 * (3 : ZMod 1632785537) ^ 48) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 771188898 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 1632785537) ^ 194 = 852852848 := by
        calc
          (3 : ZMod 1632785537) ^ 194 = (3 : ZMod 1632785537) ^ (97 + 97) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 97 * (3 : ZMod 1632785537) ^ 97 := by rw [pow_add]
          _ = 852852848 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 1632785537) ^ 389 = 869719862 := by
        calc
          (3 : ZMod 1632785537) ^ 389 = (3 : ZMod 1632785537) ^ (194 + 194 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 194 * (3 : ZMod 1632785537) ^ 194) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 869719862 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 1632785537) ^ 778 = 8377957 := by
        calc
          (3 : ZMod 1632785537) ^ 778 = (3 : ZMod 1632785537) ^ (389 + 389) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 389 * (3 : ZMod 1632785537) ^ 389 := by rw [pow_add]
          _ = 8377957 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 1632785537) ^ 1557 = 1569273416 := by
        calc
          (3 : ZMod 1632785537) ^ 1557 = (3 : ZMod 1632785537) ^ (778 + 778 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 778 * (3 : ZMod 1632785537) ^ 778) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 1569273416 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 1632785537) ^ 3114 = 1008687826 := by
        calc
          (3 : ZMod 1632785537) ^ 3114 = (3 : ZMod 1632785537) ^ (1557 + 1557) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 1557 * (3 : ZMod 1632785537) ^ 1557 := by rw [pow_add]
          _ = 1008687826 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 1632785537) ^ 6228 = 5188341 := by
        calc
          (3 : ZMod 1632785537) ^ 6228 = (3 : ZMod 1632785537) ^ (3114 + 3114) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 3114 * (3 : ZMod 1632785537) ^ 3114 := by rw [pow_add]
          _ = 5188341 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 1632785537) ^ 12457 = 707122360 := by
        calc
          (3 : ZMod 1632785537) ^ 12457 = (3 : ZMod 1632785537) ^ (6228 + 6228 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 6228 * (3 : ZMod 1632785537) ^ 6228) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 707122360 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 1632785537) ^ 24914 = 1585492235 := by
        calc
          (3 : ZMod 1632785537) ^ 24914 = (3 : ZMod 1632785537) ^ (12457 + 12457) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 12457 * (3 : ZMod 1632785537) ^ 12457 := by rw [pow_add]
          _ = 1585492235 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 1632785537) ^ 49828 = 1474059124 := by
        calc
          (3 : ZMod 1632785537) ^ 49828 = (3 : ZMod 1632785537) ^ (24914 + 24914) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 24914 * (3 : ZMod 1632785537) ^ 24914 := by rw [pow_add]
          _ = 1474059124 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 1632785537) ^ 99657 = 404944072 := by
        calc
          (3 : ZMod 1632785537) ^ 99657 = (3 : ZMod 1632785537) ^ (49828 + 49828 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 49828 * (3 : ZMod 1632785537) ^ 49828) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 404944072 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 1632785537) ^ 199314 = 248213718 := by
        calc
          (3 : ZMod 1632785537) ^ 199314 = (3 : ZMod 1632785537) ^ (99657 + 99657) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 99657 * (3 : ZMod 1632785537) ^ 99657 := by rw [pow_add]
          _ = 248213718 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 1632785537) ^ 398629 = 594551675 := by
        calc
          (3 : ZMod 1632785537) ^ 398629 = (3 : ZMod 1632785537) ^ (199314 + 199314 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 199314 * (3 : ZMod 1632785537) ^ 199314) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 594551675 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 1632785537) ^ 797258 = 1512327610 := by
        calc
          (3 : ZMod 1632785537) ^ 797258 = (3 : ZMod 1632785537) ^ (398629 + 398629) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 398629 * (3 : ZMod 1632785537) ^ 398629 := by rw [pow_add]
          _ = 1512327610 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 1632785537) ^ 1594517 = 1439807308 := by
        calc
          (3 : ZMod 1632785537) ^ 1594517 = (3 : ZMod 1632785537) ^ (797258 + 797258 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 797258 * (3 : ZMod 1632785537) ^ 797258) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 1439807308 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 1632785537) ^ 3189034 = 1481082923 := by
        calc
          (3 : ZMod 1632785537) ^ 3189034 = (3 : ZMod 1632785537) ^ (1594517 + 1594517) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 1594517 * (3 : ZMod 1632785537) ^ 1594517 := by rw [pow_add]
          _ = 1481082923 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 1632785537) ^ 6378068 = 373014227 := by
        calc
          (3 : ZMod 1632785537) ^ 6378068 = (3 : ZMod 1632785537) ^ (3189034 + 3189034) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 3189034 * (3 : ZMod 1632785537) ^ 3189034 := by rw [pow_add]
          _ = 373014227 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 1632785537) ^ 12756137 = 365727635 := by
        calc
          (3 : ZMod 1632785537) ^ 12756137 = (3 : ZMod 1632785537) ^ (6378068 + 6378068 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 6378068 * (3 : ZMod 1632785537) ^ 6378068) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 365727635 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 1632785537) ^ 25512274 = 879606404 := by
        calc
          (3 : ZMod 1632785537) ^ 25512274 = (3 : ZMod 1632785537) ^ (12756137 + 12756137) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 12756137 * (3 : ZMod 1632785537) ^ 12756137 := by rw [pow_add]
          _ = 879606404 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 1632785537) ^ 51024548 = 1542235340 := by
        calc
          (3 : ZMod 1632785537) ^ 51024548 = (3 : ZMod 1632785537) ^ (25512274 + 25512274) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 25512274 * (3 : ZMod 1632785537) ^ 25512274 := by rw [pow_add]
          _ = 1542235340 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 1632785537) ^ 102049096 = 271797890 := by
        calc
          (3 : ZMod 1632785537) ^ 102049096 = (3 : ZMod 1632785537) ^ (51024548 + 51024548) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 51024548 * (3 : ZMod 1632785537) ^ 51024548 := by rw [pow_add]
          _ = 271797890 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 1632785537) ^ 204098192 = 1287461330 := by
        calc
          (3 : ZMod 1632785537) ^ 204098192 = (3 : ZMod 1632785537) ^ (102049096 + 102049096) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 102049096 * (3 : ZMod 1632785537) ^ 102049096 := by rw [pow_add]
          _ = 1287461330 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 1632785537) ^ 408196384 = 1280058033 := by
        calc
          (3 : ZMod 1632785537) ^ 408196384 = (3 : ZMod 1632785537) ^ (204098192 + 204098192) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 204098192 * (3 : ZMod 1632785537) ^ 204098192 := by rw [pow_add]
          _ = 1280058033 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 1632785537) ^ 816392768 = 1632785536 := by
        calc
          (3 : ZMod 1632785537) ^ 816392768 = (3 : ZMod 1632785537) ^ (408196384 + 408196384) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 408196384 * (3 : ZMod 1632785537) ^ 408196384 := by rw [pow_add]
          _ = 1632785536 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 1632785537) ^ 1632785536 = 1 := by
        calc
          (3 : ZMod 1632785537) ^ 1632785536 = (3 : ZMod 1632785537) ^ (816392768 + 816392768) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 816392768 * (3 : ZMod 1632785537) ^ 816392768 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (17, 1), (61, 1), (12301, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (17, 1), (61, 1), (12301, 1)] : List FactorBlock).map factorBlockValue).prod = 1632785537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 1632785537) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 1632785537) ^ 3 = 27 := by
        calc
          (3 : ZMod 1632785537) ^ 3 = (3 : ZMod 1632785537) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 1 * (3 : ZMod 1632785537) ^ 1) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 1632785537) ^ 6 = 729 := by
        calc
          (3 : ZMod 1632785537) ^ 6 = (3 : ZMod 1632785537) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 3 * (3 : ZMod 1632785537) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 1632785537) ^ 12 = 531441 := by
        calc
          (3 : ZMod 1632785537) ^ 12 = (3 : ZMod 1632785537) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 6 * (3 : ZMod 1632785537) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 1632785537) ^ 24 = 1590424117 := by
        calc
          (3 : ZMod 1632785537) ^ 24 = (3 : ZMod 1632785537) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 12 * (3 : ZMod 1632785537) ^ 12 := by rw [pow_add]
          _ = 1590424117 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 1632785537) ^ 48 = 1451759605 := by
        calc
          (3 : ZMod 1632785537) ^ 48 = (3 : ZMod 1632785537) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 24 * (3 : ZMod 1632785537) ^ 24 := by rw [pow_add]
          _ = 1451759605 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 1632785537) ^ 97 = 771188898 := by
        calc
          (3 : ZMod 1632785537) ^ 97 = (3 : ZMod 1632785537) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 48 * (3 : ZMod 1632785537) ^ 48) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 771188898 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 1632785537) ^ 194 = 852852848 := by
        calc
          (3 : ZMod 1632785537) ^ 194 = (3 : ZMod 1632785537) ^ (97 + 97) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 97 * (3 : ZMod 1632785537) ^ 97 := by rw [pow_add]
          _ = 852852848 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 1632785537) ^ 389 = 869719862 := by
        calc
          (3 : ZMod 1632785537) ^ 389 = (3 : ZMod 1632785537) ^ (194 + 194 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 194 * (3 : ZMod 1632785537) ^ 194) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 869719862 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 1632785537) ^ 778 = 8377957 := by
        calc
          (3 : ZMod 1632785537) ^ 778 = (3 : ZMod 1632785537) ^ (389 + 389) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 389 * (3 : ZMod 1632785537) ^ 389 := by rw [pow_add]
          _ = 8377957 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 1632785537) ^ 1557 = 1569273416 := by
        calc
          (3 : ZMod 1632785537) ^ 1557 = (3 : ZMod 1632785537) ^ (778 + 778 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 778 * (3 : ZMod 1632785537) ^ 778) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 1569273416 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 1632785537) ^ 3114 = 1008687826 := by
        calc
          (3 : ZMod 1632785537) ^ 3114 = (3 : ZMod 1632785537) ^ (1557 + 1557) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 1557 * (3 : ZMod 1632785537) ^ 1557 := by rw [pow_add]
          _ = 1008687826 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 1632785537) ^ 6228 = 5188341 := by
        calc
          (3 : ZMod 1632785537) ^ 6228 = (3 : ZMod 1632785537) ^ (3114 + 3114) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 3114 * (3 : ZMod 1632785537) ^ 3114 := by rw [pow_add]
          _ = 5188341 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 1632785537) ^ 12457 = 707122360 := by
        calc
          (3 : ZMod 1632785537) ^ 12457 = (3 : ZMod 1632785537) ^ (6228 + 6228 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 6228 * (3 : ZMod 1632785537) ^ 6228) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 707122360 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 1632785537) ^ 24914 = 1585492235 := by
        calc
          (3 : ZMod 1632785537) ^ 24914 = (3 : ZMod 1632785537) ^ (12457 + 12457) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 12457 * (3 : ZMod 1632785537) ^ 12457 := by rw [pow_add]
          _ = 1585492235 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 1632785537) ^ 49828 = 1474059124 := by
        calc
          (3 : ZMod 1632785537) ^ 49828 = (3 : ZMod 1632785537) ^ (24914 + 24914) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 24914 * (3 : ZMod 1632785537) ^ 24914 := by rw [pow_add]
          _ = 1474059124 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 1632785537) ^ 99657 = 404944072 := by
        calc
          (3 : ZMod 1632785537) ^ 99657 = (3 : ZMod 1632785537) ^ (49828 + 49828 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 49828 * (3 : ZMod 1632785537) ^ 49828) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 404944072 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 1632785537) ^ 199314 = 248213718 := by
        calc
          (3 : ZMod 1632785537) ^ 199314 = (3 : ZMod 1632785537) ^ (99657 + 99657) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 99657 * (3 : ZMod 1632785537) ^ 99657 := by rw [pow_add]
          _ = 248213718 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 1632785537) ^ 398629 = 594551675 := by
        calc
          (3 : ZMod 1632785537) ^ 398629 = (3 : ZMod 1632785537) ^ (199314 + 199314 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 199314 * (3 : ZMod 1632785537) ^ 199314) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 594551675 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 1632785537) ^ 797258 = 1512327610 := by
        calc
          (3 : ZMod 1632785537) ^ 797258 = (3 : ZMod 1632785537) ^ (398629 + 398629) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 398629 * (3 : ZMod 1632785537) ^ 398629 := by rw [pow_add]
          _ = 1512327610 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 1632785537) ^ 1594517 = 1439807308 := by
        calc
          (3 : ZMod 1632785537) ^ 1594517 = (3 : ZMod 1632785537) ^ (797258 + 797258 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 797258 * (3 : ZMod 1632785537) ^ 797258) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 1439807308 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 1632785537) ^ 3189034 = 1481082923 := by
        calc
          (3 : ZMod 1632785537) ^ 3189034 = (3 : ZMod 1632785537) ^ (1594517 + 1594517) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 1594517 * (3 : ZMod 1632785537) ^ 1594517 := by rw [pow_add]
          _ = 1481082923 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 1632785537) ^ 6378068 = 373014227 := by
        calc
          (3 : ZMod 1632785537) ^ 6378068 = (3 : ZMod 1632785537) ^ (3189034 + 3189034) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 3189034 * (3 : ZMod 1632785537) ^ 3189034 := by rw [pow_add]
          _ = 373014227 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 1632785537) ^ 12756137 = 365727635 := by
        calc
          (3 : ZMod 1632785537) ^ 12756137 = (3 : ZMod 1632785537) ^ (6378068 + 6378068 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 6378068 * (3 : ZMod 1632785537) ^ 6378068) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 365727635 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 1632785537) ^ 25512274 = 879606404 := by
        calc
          (3 : ZMod 1632785537) ^ 25512274 = (3 : ZMod 1632785537) ^ (12756137 + 12756137) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 12756137 * (3 : ZMod 1632785537) ^ 12756137 := by rw [pow_add]
          _ = 879606404 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 1632785537) ^ 51024548 = 1542235340 := by
        calc
          (3 : ZMod 1632785537) ^ 51024548 = (3 : ZMod 1632785537) ^ (25512274 + 25512274) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 25512274 * (3 : ZMod 1632785537) ^ 25512274 := by rw [pow_add]
          _ = 1542235340 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 1632785537) ^ 102049096 = 271797890 := by
        calc
          (3 : ZMod 1632785537) ^ 102049096 = (3 : ZMod 1632785537) ^ (51024548 + 51024548) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 51024548 * (3 : ZMod 1632785537) ^ 51024548 := by rw [pow_add]
          _ = 271797890 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 1632785537) ^ 204098192 = 1287461330 := by
        calc
          (3 : ZMod 1632785537) ^ 204098192 = (3 : ZMod 1632785537) ^ (102049096 + 102049096) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 102049096 * (3 : ZMod 1632785537) ^ 102049096 := by rw [pow_add]
          _ = 1287461330 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 1632785537) ^ 408196384 = 1280058033 := by
        calc
          (3 : ZMod 1632785537) ^ 408196384 = (3 : ZMod 1632785537) ^ (204098192 + 204098192) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 204098192 * (3 : ZMod 1632785537) ^ 204098192 := by rw [pow_add]
          _ = 1280058033 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 1632785537) ^ 816392768 = 1632785536 := by
        calc
          (3 : ZMod 1632785537) ^ 816392768 = (3 : ZMod 1632785537) ^ (408196384 + 408196384) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 408196384 * (3 : ZMod 1632785537) ^ 408196384 := by rw [pow_add]
          _ = 1632785536 := by rw [factor_0_28]; decide
      change (3 : ZMod 1632785537) ^ 816392768 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (3 : ZMod 1632785537) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 1632785537) ^ 2 = 9 := by
        calc
          (3 : ZMod 1632785537) ^ 2 = (3 : ZMod 1632785537) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 1 * (3 : ZMod 1632785537) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 1632785537) ^ 5 = 243 := by
        calc
          (3 : ZMod 1632785537) ^ 5 = (3 : ZMod 1632785537) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 2 * (3 : ZMod 1632785537) ^ 2) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 1632785537) ^ 11 = 177147 := by
        calc
          (3 : ZMod 1632785537) ^ 11 = (3 : ZMod 1632785537) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 5 * (3 : ZMod 1632785537) ^ 5) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 1632785537) ^ 22 = 358134406 := by
        calc
          (3 : ZMod 1632785537) ^ 22 = (3 : ZMod 1632785537) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 11 * (3 : ZMod 1632785537) ^ 11 := by rw [pow_add]
          _ = 358134406 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 1632785537) ^ 45 = 1202766104 := by
        calc
          (3 : ZMod 1632785537) ^ 45 = (3 : ZMod 1632785537) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 22 * (3 : ZMod 1632785537) ^ 22) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 1202766104 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 1632785537) ^ 91 = 552039000 := by
        calc
          (3 : ZMod 1632785537) ^ 91 = (3 : ZMod 1632785537) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 45 * (3 : ZMod 1632785537) ^ 45) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 552039000 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 1632785537) ^ 183 = 1476108492 := by
        calc
          (3 : ZMod 1632785537) ^ 183 = (3 : ZMod 1632785537) ^ (91 + 91 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 91 * (3 : ZMod 1632785537) ^ 91) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 1476108492 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 1632785537) ^ 366 = 267002997 := by
        calc
          (3 : ZMod 1632785537) ^ 366 = (3 : ZMod 1632785537) ^ (183 + 183) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 183 * (3 : ZMod 1632785537) ^ 183 := by rw [pow_add]
          _ = 267002997 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 1632785537) ^ 732 = 1562550396 := by
        calc
          (3 : ZMod 1632785537) ^ 732 = (3 : ZMod 1632785537) ^ (366 + 366) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 366 * (3 : ZMod 1632785537) ^ 366 := by rw [pow_add]
          _ = 1562550396 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 1632785537) ^ 1465 = 304003221 := by
        calc
          (3 : ZMod 1632785537) ^ 1465 = (3 : ZMod 1632785537) ^ (732 + 732 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 732 * (3 : ZMod 1632785537) ^ 732) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 304003221 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 1632785537) ^ 2931 = 597558383 := by
        calc
          (3 : ZMod 1632785537) ^ 2931 = (3 : ZMod 1632785537) ^ (1465 + 1465 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 1465 * (3 : ZMod 1632785537) ^ 1465) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 597558383 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 1632785537) ^ 5862 = 1628492460 := by
        calc
          (3 : ZMod 1632785537) ^ 5862 = (3 : ZMod 1632785537) ^ (2931 + 2931) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 2931 * (3 : ZMod 1632785537) ^ 2931 := by rw [pow_add]
          _ = 1628492460 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 1632785537) ^ 11724 = 1259771810 := by
        calc
          (3 : ZMod 1632785537) ^ 11724 = (3 : ZMod 1632785537) ^ (5862 + 5862) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 5862 * (3 : ZMod 1632785537) ^ 5862 := by rw [pow_add]
          _ = 1259771810 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 1632785537) ^ 23448 = 471558339 := by
        calc
          (3 : ZMod 1632785537) ^ 23448 = (3 : ZMod 1632785537) ^ (11724 + 11724) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 11724 * (3 : ZMod 1632785537) ^ 11724 := by rw [pow_add]
          _ = 471558339 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 1632785537) ^ 46897 = 948713326 := by
        calc
          (3 : ZMod 1632785537) ^ 46897 = (3 : ZMod 1632785537) ^ (23448 + 23448 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 23448 * (3 : ZMod 1632785537) ^ 23448) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 948713326 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 1632785537) ^ 93795 = 352825106 := by
        calc
          (3 : ZMod 1632785537) ^ 93795 = (3 : ZMod 1632785537) ^ (46897 + 46897 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 46897 * (3 : ZMod 1632785537) ^ 46897) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 352825106 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 1632785537) ^ 187590 = 615818244 := by
        calc
          (3 : ZMod 1632785537) ^ 187590 = (3 : ZMod 1632785537) ^ (93795 + 93795) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 93795 * (3 : ZMod 1632785537) ^ 93795 := by rw [pow_add]
          _ = 615818244 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 1632785537) ^ 375180 = 302697659 := by
        calc
          (3 : ZMod 1632785537) ^ 375180 = (3 : ZMod 1632785537) ^ (187590 + 187590) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 187590 * (3 : ZMod 1632785537) ^ 187590 := by rw [pow_add]
          _ = 302697659 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 1632785537) ^ 750361 = 225306746 := by
        calc
          (3 : ZMod 1632785537) ^ 750361 = (3 : ZMod 1632785537) ^ (375180 + 375180 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 375180 * (3 : ZMod 1632785537) ^ 375180) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 225306746 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 1632785537) ^ 1500722 = 523045438 := by
        calc
          (3 : ZMod 1632785537) ^ 1500722 = (3 : ZMod 1632785537) ^ (750361 + 750361) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 750361 * (3 : ZMod 1632785537) ^ 750361 := by rw [pow_add]
          _ = 523045438 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 1632785537) ^ 3001444 = 566407271 := by
        calc
          (3 : ZMod 1632785537) ^ 3001444 = (3 : ZMod 1632785537) ^ (1500722 + 1500722) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 1500722 * (3 : ZMod 1632785537) ^ 1500722 := by rw [pow_add]
          _ = 566407271 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 1632785537) ^ 6002888 = 1479078148 := by
        calc
          (3 : ZMod 1632785537) ^ 6002888 = (3 : ZMod 1632785537) ^ (3001444 + 3001444) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 3001444 * (3 : ZMod 1632785537) ^ 3001444 := by rw [pow_add]
          _ = 1479078148 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 1632785537) ^ 12005776 = 463258922 := by
        calc
          (3 : ZMod 1632785537) ^ 12005776 = (3 : ZMod 1632785537) ^ (6002888 + 6002888) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 6002888 * (3 : ZMod 1632785537) ^ 6002888 := by rw [pow_add]
          _ = 463258922 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 1632785537) ^ 24011552 = 1051833130 := by
        calc
          (3 : ZMod 1632785537) ^ 24011552 = (3 : ZMod 1632785537) ^ (12005776 + 12005776) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 12005776 * (3 : ZMod 1632785537) ^ 12005776 := by rw [pow_add]
          _ = 1051833130 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 1632785537) ^ 48023104 = 629877333 := by
        calc
          (3 : ZMod 1632785537) ^ 48023104 = (3 : ZMod 1632785537) ^ (24011552 + 24011552) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 24011552 * (3 : ZMod 1632785537) ^ 24011552 := by rw [pow_add]
          _ = 629877333 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 1632785537) ^ 96046208 = 1079151551 := by
        calc
          (3 : ZMod 1632785537) ^ 96046208 = (3 : ZMod 1632785537) ^ (48023104 + 48023104) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 48023104 * (3 : ZMod 1632785537) ^ 48023104 := by rw [pow_add]
          _ = 1079151551 := by rw [factor_1_25]; decide
      change (3 : ZMod 1632785537) ^ 96046208 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (3 : ZMod 1632785537) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 1632785537) ^ 3 = 27 := by
        calc
          (3 : ZMod 1632785537) ^ 3 = (3 : ZMod 1632785537) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 1 * (3 : ZMod 1632785537) ^ 1) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 1632785537) ^ 6 = 729 := by
        calc
          (3 : ZMod 1632785537) ^ 6 = (3 : ZMod 1632785537) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 3 * (3 : ZMod 1632785537) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 1632785537) ^ 12 = 531441 := by
        calc
          (3 : ZMod 1632785537) ^ 12 = (3 : ZMod 1632785537) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 6 * (3 : ZMod 1632785537) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 1632785537) ^ 25 = 1505701277 := by
        calc
          (3 : ZMod 1632785537) ^ 25 = (3 : ZMod 1632785537) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 12 * (3 : ZMod 1632785537) ^ 12) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 1505701277 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 1632785537) ^ 51 = 10656447 := by
        calc
          (3 : ZMod 1632785537) ^ 51 = (3 : ZMod 1632785537) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 25 * (3 : ZMod 1632785537) ^ 25) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 10656447 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 1632785537) ^ 102 = 1261350996 := by
        calc
          (3 : ZMod 1632785537) ^ 102 = (3 : ZMod 1632785537) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 51 * (3 : ZMod 1632785537) ^ 51 := by rw [pow_add]
          _ = 1261350996 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 1632785537) ^ 204 = 103503861 := by
        calc
          (3 : ZMod 1632785537) ^ 204 = (3 : ZMod 1632785537) ^ (102 + 102) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 102 * (3 : ZMod 1632785537) ^ 102 := by rw [pow_add]
          _ = 103503861 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 1632785537) ^ 408 = 448687551 := by
        calc
          (3 : ZMod 1632785537) ^ 408 = (3 : ZMod 1632785537) ^ (204 + 204) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 204 * (3 : ZMod 1632785537) ^ 204 := by rw [pow_add]
          _ = 448687551 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 1632785537) ^ 816 = 1459495557 := by
        calc
          (3 : ZMod 1632785537) ^ 816 = (3 : ZMod 1632785537) ^ (408 + 408) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 408 * (3 : ZMod 1632785537) ^ 408 := by rw [pow_add]
          _ = 1459495557 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 1632785537) ^ 1633 = 169508351 := by
        calc
          (3 : ZMod 1632785537) ^ 1633 = (3 : ZMod 1632785537) ^ (816 + 816 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 816 * (3 : ZMod 1632785537) ^ 816) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 169508351 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 1632785537) ^ 3267 = 1252189779 := by
        calc
          (3 : ZMod 1632785537) ^ 3267 = (3 : ZMod 1632785537) ^ (1633 + 1633 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 1633 * (3 : ZMod 1632785537) ^ 1633) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 1252189779 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 1632785537) ^ 6534 = 414414836 := by
        calc
          (3 : ZMod 1632785537) ^ 6534 = (3 : ZMod 1632785537) ^ (3267 + 3267) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 3267 * (3 : ZMod 1632785537) ^ 3267 := by rw [pow_add]
          _ = 414414836 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 1632785537) ^ 13069 = 973521170 := by
        calc
          (3 : ZMod 1632785537) ^ 13069 = (3 : ZMod 1632785537) ^ (6534 + 6534 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 6534 * (3 : ZMod 1632785537) ^ 6534) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 973521170 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 1632785537) ^ 26139 = 1117881564 := by
        calc
          (3 : ZMod 1632785537) ^ 26139 = (3 : ZMod 1632785537) ^ (13069 + 13069 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 13069 * (3 : ZMod 1632785537) ^ 13069) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 1117881564 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 1632785537) ^ 52279 = 1554973879 := by
        calc
          (3 : ZMod 1632785537) ^ 52279 = (3 : ZMod 1632785537) ^ (26139 + 26139 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 26139 * (3 : ZMod 1632785537) ^ 26139) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 1554973879 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 1632785537) ^ 104558 = 1244829526 := by
        calc
          (3 : ZMod 1632785537) ^ 104558 = (3 : ZMod 1632785537) ^ (52279 + 52279) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 52279 * (3 : ZMod 1632785537) ^ 52279 := by rw [pow_add]
          _ = 1244829526 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 1632785537) ^ 209117 = 1371017083 := by
        calc
          (3 : ZMod 1632785537) ^ 209117 = (3 : ZMod 1632785537) ^ (104558 + 104558 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 104558 * (3 : ZMod 1632785537) ^ 104558) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 1371017083 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 1632785537) ^ 418234 = 1481228922 := by
        calc
          (3 : ZMod 1632785537) ^ 418234 = (3 : ZMod 1632785537) ^ (209117 + 209117) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 209117 * (3 : ZMod 1632785537) ^ 209117 := by rw [pow_add]
          _ = 1481228922 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 1632785537) ^ 836468 = 1074246285 := by
        calc
          (3 : ZMod 1632785537) ^ 836468 = (3 : ZMod 1632785537) ^ (418234 + 418234) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 418234 * (3 : ZMod 1632785537) ^ 418234 := by rw [pow_add]
          _ = 1074246285 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 1632785537) ^ 1672936 = 1035446494 := by
        calc
          (3 : ZMod 1632785537) ^ 1672936 = (3 : ZMod 1632785537) ^ (836468 + 836468) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 836468 * (3 : ZMod 1632785537) ^ 836468 := by rw [pow_add]
          _ = 1035446494 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 1632785537) ^ 3345872 = 1030330712 := by
        calc
          (3 : ZMod 1632785537) ^ 3345872 = (3 : ZMod 1632785537) ^ (1672936 + 1672936) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 1672936 * (3 : ZMod 1632785537) ^ 1672936 := by rw [pow_add]
          _ = 1030330712 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 1632785537) ^ 6691744 = 785327475 := by
        calc
          (3 : ZMod 1632785537) ^ 6691744 = (3 : ZMod 1632785537) ^ (3345872 + 3345872) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 3345872 * (3 : ZMod 1632785537) ^ 3345872 := by rw [pow_add]
          _ = 785327475 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 1632785537) ^ 13383488 = 691543056 := by
        calc
          (3 : ZMod 1632785537) ^ 13383488 = (3 : ZMod 1632785537) ^ (6691744 + 6691744) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 6691744 * (3 : ZMod 1632785537) ^ 6691744 := by rw [pow_add]
          _ = 691543056 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 1632785537) ^ 26766976 = 1128315366 := by
        calc
          (3 : ZMod 1632785537) ^ 26766976 = (3 : ZMod 1632785537) ^ (13383488 + 13383488) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 13383488 * (3 : ZMod 1632785537) ^ 13383488 := by rw [pow_add]
          _ = 1128315366 := by rw [factor_2_23]; decide
      change (3 : ZMod 1632785537) ^ 26766976 ≠ 1
      rw [factor_2_24]
      decide
    ·
      have factor_3_0 : (3 : ZMod 1632785537) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 1632785537) ^ 2 = 9 := by
        calc
          (3 : ZMod 1632785537) ^ 2 = (3 : ZMod 1632785537) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 1 * (3 : ZMod 1632785537) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 1632785537) ^ 4 = 81 := by
        calc
          (3 : ZMod 1632785537) ^ 4 = (3 : ZMod 1632785537) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 2 * (3 : ZMod 1632785537) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 1632785537) ^ 8 = 6561 := by
        calc
          (3 : ZMod 1632785537) ^ 8 = (3 : ZMod 1632785537) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 4 * (3 : ZMod 1632785537) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 1632785537) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 1632785537) ^ 16 = (3 : ZMod 1632785537) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 8 * (3 : ZMod 1632785537) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 1632785537) ^ 32 = 1273050207 := by
        calc
          (3 : ZMod 1632785537) ^ 32 = (3 : ZMod 1632785537) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 16 * (3 : ZMod 1632785537) ^ 16 := by rw [pow_add]
          _ = 1273050207 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 1632785537) ^ 64 = 685037896 := by
        calc
          (3 : ZMod 1632785537) ^ 64 = (3 : ZMod 1632785537) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 32 * (3 : ZMod 1632785537) ^ 32 := by rw [pow_add]
          _ = 685037896 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 1632785537) ^ 129 = 515596536 := by
        calc
          (3 : ZMod 1632785537) ^ 129 = (3 : ZMod 1632785537) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 64 * (3 : ZMod 1632785537) ^ 64) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 515596536 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 1632785537) ^ 259 = 881848239 := by
        calc
          (3 : ZMod 1632785537) ^ 259 = (3 : ZMod 1632785537) ^ (129 + 129 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 129 * (3 : ZMod 1632785537) ^ 129) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 881848239 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 1632785537) ^ 518 = 390590745 := by
        calc
          (3 : ZMod 1632785537) ^ 518 = (3 : ZMod 1632785537) ^ (259 + 259) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 259 * (3 : ZMod 1632785537) ^ 259 := by rw [pow_add]
          _ = 390590745 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 1632785537) ^ 1037 = 1481556328 := by
        calc
          (3 : ZMod 1632785537) ^ 1037 = (3 : ZMod 1632785537) ^ (518 + 518 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = ((3 : ZMod 1632785537) ^ 518 * (3 : ZMod 1632785537) ^ 518) * (3 : ZMod 1632785537) := by rw [pow_succ, pow_add]
          _ = 1481556328 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 1632785537) ^ 2074 = 119847159 := by
        calc
          (3 : ZMod 1632785537) ^ 2074 = (3 : ZMod 1632785537) ^ (1037 + 1037) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 1037 * (3 : ZMod 1632785537) ^ 1037 := by rw [pow_add]
          _ = 119847159 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 1632785537) ^ 4148 = 1459352497 := by
        calc
          (3 : ZMod 1632785537) ^ 4148 = (3 : ZMod 1632785537) ^ (2074 + 2074) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 2074 * (3 : ZMod 1632785537) ^ 2074 := by rw [pow_add]
          _ = 1459352497 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 1632785537) ^ 8296 = 948439152 := by
        calc
          (3 : ZMod 1632785537) ^ 8296 = (3 : ZMod 1632785537) ^ (4148 + 4148) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 4148 * (3 : ZMod 1632785537) ^ 4148 := by rw [pow_add]
          _ = 948439152 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 1632785537) ^ 16592 = 1280008830 := by
        calc
          (3 : ZMod 1632785537) ^ 16592 = (3 : ZMod 1632785537) ^ (8296 + 8296) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 8296 * (3 : ZMod 1632785537) ^ 8296 := by rw [pow_add]
          _ = 1280008830 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 1632785537) ^ 33184 = 1535962749 := by
        calc
          (3 : ZMod 1632785537) ^ 33184 = (3 : ZMod 1632785537) ^ (16592 + 16592) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 16592 * (3 : ZMod 1632785537) ^ 16592 := by rw [pow_add]
          _ = 1535962749 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 1632785537) ^ 66368 = 1053123148 := by
        calc
          (3 : ZMod 1632785537) ^ 66368 = (3 : ZMod 1632785537) ^ (33184 + 33184) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 33184 * (3 : ZMod 1632785537) ^ 33184 := by rw [pow_add]
          _ = 1053123148 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 1632785537) ^ 132736 = 373048358 := by
        calc
          (3 : ZMod 1632785537) ^ 132736 = (3 : ZMod 1632785537) ^ (66368 + 66368) :=
            congrArg (fun n : ℕ => (3 : ZMod 1632785537) ^ n) (by norm_num)
          _ = (3 : ZMod 1632785537) ^ 66368 * (3 : ZMod 1632785537) ^ 66368 := by rw [pow_add]
          _ = 373048358 := by rw [factor_3_16]; decide
      change (3 : ZMod 1632785537) ^ 132736 ≠ 1
      rw [factor_3_17]
      decide

#print axioms prime_lucas_1632785537

end TotientTailPeriodKiller
end Erdos249257
