import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime187225849

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1872258491 : Nat.Prime 1872258491 := by
  apply lucas_primality 1872258491 (6 : ZMod 1872258491)
  ·
      have fermat_0 : (6 : ZMod 1872258491) ^ 1 = 6 := by norm_num
      have fermat_1 : (6 : ZMod 1872258491) ^ 3 = 216 := by
        calc
          (6 : ZMod 1872258491) ^ 3 = (6 : ZMod 1872258491) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 1 * (6 : ZMod 1872258491) ^ 1) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [fermat_0]; decide
      have fermat_2 : (6 : ZMod 1872258491) ^ 6 = 46656 := by
        calc
          (6 : ZMod 1872258491) ^ 6 = (6 : ZMod 1872258491) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 3 * (6 : ZMod 1872258491) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [fermat_1]; decide
      have fermat_3 : (6 : ZMod 1872258491) ^ 13 = 1827143070 := by
        calc
          (6 : ZMod 1872258491) ^ 13 = (6 : ZMod 1872258491) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 6 * (6 : ZMod 1872258491) ^ 6) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1827143070 := by rw [fermat_2]; decide
      have fermat_4 : (6 : ZMod 1872258491) ^ 27 = 269520335 := by
        calc
          (6 : ZMod 1872258491) ^ 27 = (6 : ZMod 1872258491) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 13 * (6 : ZMod 1872258491) ^ 13) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 269520335 := by rw [fermat_3]; decide
      have fermat_5 : (6 : ZMod 1872258491) ^ 55 = 1041837091 := by
        calc
          (6 : ZMod 1872258491) ^ 55 = (6 : ZMod 1872258491) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 27 * (6 : ZMod 1872258491) ^ 27) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1041837091 := by rw [fermat_4]; decide
      have fermat_6 : (6 : ZMod 1872258491) ^ 111 = 1221538173 := by
        calc
          (6 : ZMod 1872258491) ^ 111 = (6 : ZMod 1872258491) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 55 * (6 : ZMod 1872258491) ^ 55) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1221538173 := by rw [fermat_5]; decide
      have fermat_7 : (6 : ZMod 1872258491) ^ 223 = 1426104246 := by
        calc
          (6 : ZMod 1872258491) ^ 223 = (6 : ZMod 1872258491) ^ (111 + 111 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 111 * (6 : ZMod 1872258491) ^ 111) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1426104246 := by rw [fermat_6]; decide
      have fermat_8 : (6 : ZMod 1872258491) ^ 446 = 374680409 := by
        calc
          (6 : ZMod 1872258491) ^ 446 = (6 : ZMod 1872258491) ^ (223 + 223) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 223 * (6 : ZMod 1872258491) ^ 223 := by rw [pow_add]
          _ = 374680409 := by rw [fermat_7]; decide
      have fermat_9 : (6 : ZMod 1872258491) ^ 892 = 1682760440 := by
        calc
          (6 : ZMod 1872258491) ^ 892 = (6 : ZMod 1872258491) ^ (446 + 446) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 446 * (6 : ZMod 1872258491) ^ 446 := by rw [pow_add]
          _ = 1682760440 := by rw [fermat_8]; decide
      have fermat_10 : (6 : ZMod 1872258491) ^ 1785 = 405325379 := by
        calc
          (6 : ZMod 1872258491) ^ 1785 = (6 : ZMod 1872258491) ^ (892 + 892 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 892 * (6 : ZMod 1872258491) ^ 892) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 405325379 := by rw [fermat_9]; decide
      have fermat_11 : (6 : ZMod 1872258491) ^ 3571 = 786674089 := by
        calc
          (6 : ZMod 1872258491) ^ 3571 = (6 : ZMod 1872258491) ^ (1785 + 1785 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 1785 * (6 : ZMod 1872258491) ^ 1785) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 786674089 := by rw [fermat_10]; decide
      have fermat_12 : (6 : ZMod 1872258491) ^ 7142 = 1020498458 := by
        calc
          (6 : ZMod 1872258491) ^ 7142 = (6 : ZMod 1872258491) ^ (3571 + 3571) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 3571 * (6 : ZMod 1872258491) ^ 3571 := by rw [pow_add]
          _ = 1020498458 := by rw [fermat_11]; decide
      have fermat_13 : (6 : ZMod 1872258491) ^ 14284 = 589641496 := by
        calc
          (6 : ZMod 1872258491) ^ 14284 = (6 : ZMod 1872258491) ^ (7142 + 7142) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 7142 * (6 : ZMod 1872258491) ^ 7142 := by rw [pow_add]
          _ = 589641496 := by rw [fermat_12]; decide
      have fermat_14 : (6 : ZMod 1872258491) ^ 28568 = 735103225 := by
        calc
          (6 : ZMod 1872258491) ^ 28568 = (6 : ZMod 1872258491) ^ (14284 + 14284) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 14284 * (6 : ZMod 1872258491) ^ 14284 := by rw [pow_add]
          _ = 735103225 := by rw [fermat_13]; decide
      have fermat_15 : (6 : ZMod 1872258491) ^ 57136 = 1293017085 := by
        calc
          (6 : ZMod 1872258491) ^ 57136 = (6 : ZMod 1872258491) ^ (28568 + 28568) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 28568 * (6 : ZMod 1872258491) ^ 28568 := by rw [pow_add]
          _ = 1293017085 := by rw [fermat_14]; decide
      have fermat_16 : (6 : ZMod 1872258491) ^ 114273 = 316794299 := by
        calc
          (6 : ZMod 1872258491) ^ 114273 = (6 : ZMod 1872258491) ^ (57136 + 57136 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 57136 * (6 : ZMod 1872258491) ^ 57136) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 316794299 := by rw [fermat_15]; decide
      have fermat_17 : (6 : ZMod 1872258491) ^ 228547 = 1775676128 := by
        calc
          (6 : ZMod 1872258491) ^ 228547 = (6 : ZMod 1872258491) ^ (114273 + 114273 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 114273 * (6 : ZMod 1872258491) ^ 114273) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1775676128 := by rw [fermat_16]; decide
      have fermat_18 : (6 : ZMod 1872258491) ^ 457094 = 1235212960 := by
        calc
          (6 : ZMod 1872258491) ^ 457094 = (6 : ZMod 1872258491) ^ (228547 + 228547) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 228547 * (6 : ZMod 1872258491) ^ 228547 := by rw [pow_add]
          _ = 1235212960 := by rw [fermat_17]; decide
      have fermat_19 : (6 : ZMod 1872258491) ^ 914188 = 702635470 := by
        calc
          (6 : ZMod 1872258491) ^ 914188 = (6 : ZMod 1872258491) ^ (457094 + 457094) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 457094 * (6 : ZMod 1872258491) ^ 457094 := by rw [pow_add]
          _ = 702635470 := by rw [fermat_18]; decide
      have fermat_20 : (6 : ZMod 1872258491) ^ 1828377 = 1206750378 := by
        calc
          (6 : ZMod 1872258491) ^ 1828377 = (6 : ZMod 1872258491) ^ (914188 + 914188 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 914188 * (6 : ZMod 1872258491) ^ 914188) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1206750378 := by rw [fermat_19]; decide
      have fermat_21 : (6 : ZMod 1872258491) ^ 3656754 = 1096021244 := by
        calc
          (6 : ZMod 1872258491) ^ 3656754 = (6 : ZMod 1872258491) ^ (1828377 + 1828377) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 1828377 * (6 : ZMod 1872258491) ^ 1828377 := by rw [pow_add]
          _ = 1096021244 := by rw [fermat_20]; decide
      have fermat_22 : (6 : ZMod 1872258491) ^ 7313509 = 279930383 := by
        calc
          (6 : ZMod 1872258491) ^ 7313509 = (6 : ZMod 1872258491) ^ (3656754 + 3656754 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 3656754 * (6 : ZMod 1872258491) ^ 3656754) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 279930383 := by rw [fermat_21]; decide
      have fermat_23 : (6 : ZMod 1872258491) ^ 14627019 = 1005297567 := by
        calc
          (6 : ZMod 1872258491) ^ 14627019 = (6 : ZMod 1872258491) ^ (7313509 + 7313509 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 7313509 * (6 : ZMod 1872258491) ^ 7313509) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1005297567 := by rw [fermat_22]; decide
      have fermat_24 : (6 : ZMod 1872258491) ^ 29254038 = 154800045 := by
        calc
          (6 : ZMod 1872258491) ^ 29254038 = (6 : ZMod 1872258491) ^ (14627019 + 14627019) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 14627019 * (6 : ZMod 1872258491) ^ 14627019 := by rw [pow_add]
          _ = 154800045 := by rw [fermat_23]; decide
      have fermat_25 : (6 : ZMod 1872258491) ^ 58508077 = 187682654 := by
        calc
          (6 : ZMod 1872258491) ^ 58508077 = (6 : ZMod 1872258491) ^ (29254038 + 29254038 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 29254038 * (6 : ZMod 1872258491) ^ 29254038) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 187682654 := by rw [fermat_24]; decide
      have fermat_26 : (6 : ZMod 1872258491) ^ 117016155 = 119937392 := by
        calc
          (6 : ZMod 1872258491) ^ 117016155 = (6 : ZMod 1872258491) ^ (58508077 + 58508077 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 58508077 * (6 : ZMod 1872258491) ^ 58508077) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 119937392 := by rw [fermat_25]; decide
      have fermat_27 : (6 : ZMod 1872258491) ^ 234032311 = 359883481 := by
        calc
          (6 : ZMod 1872258491) ^ 234032311 = (6 : ZMod 1872258491) ^ (117016155 + 117016155 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 117016155 * (6 : ZMod 1872258491) ^ 117016155) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 359883481 := by rw [fermat_26]; decide
      have fermat_28 : (6 : ZMod 1872258491) ^ 468064622 = 769538542 := by
        calc
          (6 : ZMod 1872258491) ^ 468064622 = (6 : ZMod 1872258491) ^ (234032311 + 234032311) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 234032311 * (6 : ZMod 1872258491) ^ 234032311 := by rw [pow_add]
          _ = 769538542 := by rw [fermat_27]; decide
      have fermat_29 : (6 : ZMod 1872258491) ^ 936129245 = 1872258490 := by
        calc
          (6 : ZMod 1872258491) ^ 936129245 = (6 : ZMod 1872258491) ^ (468064622 + 468064622 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 468064622 * (6 : ZMod 1872258491) ^ 468064622) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1872258490 := by rw [fermat_28]; decide
      have fermat_30 : (6 : ZMod 1872258491) ^ 1872258490 = 1 := by
        calc
          (6 : ZMod 1872258491) ^ 1872258490 = (6 : ZMod 1872258491) ^ (936129245 + 936129245) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 936129245 * (6 : ZMod 1872258491) ^ 936129245 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (187225849, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (187225849, 1)] : List FactorBlock).map factorBlockValue).prod = 1872258491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_187225849) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (6 : ZMod 1872258491) ^ 1 = 6 := by norm_num
      have factor_0_1 : (6 : ZMod 1872258491) ^ 3 = 216 := by
        calc
          (6 : ZMod 1872258491) ^ 3 = (6 : ZMod 1872258491) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 1 * (6 : ZMod 1872258491) ^ 1) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_0_0]; decide
      have factor_0_2 : (6 : ZMod 1872258491) ^ 6 = 46656 := by
        calc
          (6 : ZMod 1872258491) ^ 6 = (6 : ZMod 1872258491) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 3 * (6 : ZMod 1872258491) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [factor_0_1]; decide
      have factor_0_3 : (6 : ZMod 1872258491) ^ 13 = 1827143070 := by
        calc
          (6 : ZMod 1872258491) ^ 13 = (6 : ZMod 1872258491) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 6 * (6 : ZMod 1872258491) ^ 6) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1827143070 := by rw [factor_0_2]; decide
      have factor_0_4 : (6 : ZMod 1872258491) ^ 27 = 269520335 := by
        calc
          (6 : ZMod 1872258491) ^ 27 = (6 : ZMod 1872258491) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 13 * (6 : ZMod 1872258491) ^ 13) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 269520335 := by rw [factor_0_3]; decide
      have factor_0_5 : (6 : ZMod 1872258491) ^ 55 = 1041837091 := by
        calc
          (6 : ZMod 1872258491) ^ 55 = (6 : ZMod 1872258491) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 27 * (6 : ZMod 1872258491) ^ 27) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1041837091 := by rw [factor_0_4]; decide
      have factor_0_6 : (6 : ZMod 1872258491) ^ 111 = 1221538173 := by
        calc
          (6 : ZMod 1872258491) ^ 111 = (6 : ZMod 1872258491) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 55 * (6 : ZMod 1872258491) ^ 55) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1221538173 := by rw [factor_0_5]; decide
      have factor_0_7 : (6 : ZMod 1872258491) ^ 223 = 1426104246 := by
        calc
          (6 : ZMod 1872258491) ^ 223 = (6 : ZMod 1872258491) ^ (111 + 111 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 111 * (6 : ZMod 1872258491) ^ 111) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1426104246 := by rw [factor_0_6]; decide
      have factor_0_8 : (6 : ZMod 1872258491) ^ 446 = 374680409 := by
        calc
          (6 : ZMod 1872258491) ^ 446 = (6 : ZMod 1872258491) ^ (223 + 223) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 223 * (6 : ZMod 1872258491) ^ 223 := by rw [pow_add]
          _ = 374680409 := by rw [factor_0_7]; decide
      have factor_0_9 : (6 : ZMod 1872258491) ^ 892 = 1682760440 := by
        calc
          (6 : ZMod 1872258491) ^ 892 = (6 : ZMod 1872258491) ^ (446 + 446) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 446 * (6 : ZMod 1872258491) ^ 446 := by rw [pow_add]
          _ = 1682760440 := by rw [factor_0_8]; decide
      have factor_0_10 : (6 : ZMod 1872258491) ^ 1785 = 405325379 := by
        calc
          (6 : ZMod 1872258491) ^ 1785 = (6 : ZMod 1872258491) ^ (892 + 892 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 892 * (6 : ZMod 1872258491) ^ 892) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 405325379 := by rw [factor_0_9]; decide
      have factor_0_11 : (6 : ZMod 1872258491) ^ 3571 = 786674089 := by
        calc
          (6 : ZMod 1872258491) ^ 3571 = (6 : ZMod 1872258491) ^ (1785 + 1785 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 1785 * (6 : ZMod 1872258491) ^ 1785) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 786674089 := by rw [factor_0_10]; decide
      have factor_0_12 : (6 : ZMod 1872258491) ^ 7142 = 1020498458 := by
        calc
          (6 : ZMod 1872258491) ^ 7142 = (6 : ZMod 1872258491) ^ (3571 + 3571) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 3571 * (6 : ZMod 1872258491) ^ 3571 := by rw [pow_add]
          _ = 1020498458 := by rw [factor_0_11]; decide
      have factor_0_13 : (6 : ZMod 1872258491) ^ 14284 = 589641496 := by
        calc
          (6 : ZMod 1872258491) ^ 14284 = (6 : ZMod 1872258491) ^ (7142 + 7142) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 7142 * (6 : ZMod 1872258491) ^ 7142 := by rw [pow_add]
          _ = 589641496 := by rw [factor_0_12]; decide
      have factor_0_14 : (6 : ZMod 1872258491) ^ 28568 = 735103225 := by
        calc
          (6 : ZMod 1872258491) ^ 28568 = (6 : ZMod 1872258491) ^ (14284 + 14284) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 14284 * (6 : ZMod 1872258491) ^ 14284 := by rw [pow_add]
          _ = 735103225 := by rw [factor_0_13]; decide
      have factor_0_15 : (6 : ZMod 1872258491) ^ 57136 = 1293017085 := by
        calc
          (6 : ZMod 1872258491) ^ 57136 = (6 : ZMod 1872258491) ^ (28568 + 28568) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 28568 * (6 : ZMod 1872258491) ^ 28568 := by rw [pow_add]
          _ = 1293017085 := by rw [factor_0_14]; decide
      have factor_0_16 : (6 : ZMod 1872258491) ^ 114273 = 316794299 := by
        calc
          (6 : ZMod 1872258491) ^ 114273 = (6 : ZMod 1872258491) ^ (57136 + 57136 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 57136 * (6 : ZMod 1872258491) ^ 57136) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 316794299 := by rw [factor_0_15]; decide
      have factor_0_17 : (6 : ZMod 1872258491) ^ 228547 = 1775676128 := by
        calc
          (6 : ZMod 1872258491) ^ 228547 = (6 : ZMod 1872258491) ^ (114273 + 114273 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 114273 * (6 : ZMod 1872258491) ^ 114273) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1775676128 := by rw [factor_0_16]; decide
      have factor_0_18 : (6 : ZMod 1872258491) ^ 457094 = 1235212960 := by
        calc
          (6 : ZMod 1872258491) ^ 457094 = (6 : ZMod 1872258491) ^ (228547 + 228547) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 228547 * (6 : ZMod 1872258491) ^ 228547 := by rw [pow_add]
          _ = 1235212960 := by rw [factor_0_17]; decide
      have factor_0_19 : (6 : ZMod 1872258491) ^ 914188 = 702635470 := by
        calc
          (6 : ZMod 1872258491) ^ 914188 = (6 : ZMod 1872258491) ^ (457094 + 457094) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 457094 * (6 : ZMod 1872258491) ^ 457094 := by rw [pow_add]
          _ = 702635470 := by rw [factor_0_18]; decide
      have factor_0_20 : (6 : ZMod 1872258491) ^ 1828377 = 1206750378 := by
        calc
          (6 : ZMod 1872258491) ^ 1828377 = (6 : ZMod 1872258491) ^ (914188 + 914188 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 914188 * (6 : ZMod 1872258491) ^ 914188) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1206750378 := by rw [factor_0_19]; decide
      have factor_0_21 : (6 : ZMod 1872258491) ^ 3656754 = 1096021244 := by
        calc
          (6 : ZMod 1872258491) ^ 3656754 = (6 : ZMod 1872258491) ^ (1828377 + 1828377) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 1828377 * (6 : ZMod 1872258491) ^ 1828377 := by rw [pow_add]
          _ = 1096021244 := by rw [factor_0_20]; decide
      have factor_0_22 : (6 : ZMod 1872258491) ^ 7313509 = 279930383 := by
        calc
          (6 : ZMod 1872258491) ^ 7313509 = (6 : ZMod 1872258491) ^ (3656754 + 3656754 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 3656754 * (6 : ZMod 1872258491) ^ 3656754) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 279930383 := by rw [factor_0_21]; decide
      have factor_0_23 : (6 : ZMod 1872258491) ^ 14627019 = 1005297567 := by
        calc
          (6 : ZMod 1872258491) ^ 14627019 = (6 : ZMod 1872258491) ^ (7313509 + 7313509 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 7313509 * (6 : ZMod 1872258491) ^ 7313509) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1005297567 := by rw [factor_0_22]; decide
      have factor_0_24 : (6 : ZMod 1872258491) ^ 29254038 = 154800045 := by
        calc
          (6 : ZMod 1872258491) ^ 29254038 = (6 : ZMod 1872258491) ^ (14627019 + 14627019) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 14627019 * (6 : ZMod 1872258491) ^ 14627019 := by rw [pow_add]
          _ = 154800045 := by rw [factor_0_23]; decide
      have factor_0_25 : (6 : ZMod 1872258491) ^ 58508077 = 187682654 := by
        calc
          (6 : ZMod 1872258491) ^ 58508077 = (6 : ZMod 1872258491) ^ (29254038 + 29254038 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 29254038 * (6 : ZMod 1872258491) ^ 29254038) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 187682654 := by rw [factor_0_24]; decide
      have factor_0_26 : (6 : ZMod 1872258491) ^ 117016155 = 119937392 := by
        calc
          (6 : ZMod 1872258491) ^ 117016155 = (6 : ZMod 1872258491) ^ (58508077 + 58508077 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 58508077 * (6 : ZMod 1872258491) ^ 58508077) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 119937392 := by rw [factor_0_25]; decide
      have factor_0_27 : (6 : ZMod 1872258491) ^ 234032311 = 359883481 := by
        calc
          (6 : ZMod 1872258491) ^ 234032311 = (6 : ZMod 1872258491) ^ (117016155 + 117016155 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 117016155 * (6 : ZMod 1872258491) ^ 117016155) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 359883481 := by rw [factor_0_26]; decide
      have factor_0_28 : (6 : ZMod 1872258491) ^ 468064622 = 769538542 := by
        calc
          (6 : ZMod 1872258491) ^ 468064622 = (6 : ZMod 1872258491) ^ (234032311 + 234032311) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 234032311 * (6 : ZMod 1872258491) ^ 234032311 := by rw [pow_add]
          _ = 769538542 := by rw [factor_0_27]; decide
      have factor_0_29 : (6 : ZMod 1872258491) ^ 936129245 = 1872258490 := by
        calc
          (6 : ZMod 1872258491) ^ 936129245 = (6 : ZMod 1872258491) ^ (468064622 + 468064622 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 468064622 * (6 : ZMod 1872258491) ^ 468064622) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1872258490 := by rw [factor_0_28]; decide
      change (6 : ZMod 1872258491) ^ 936129245 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (6 : ZMod 1872258491) ^ 1 = 6 := by norm_num
      have factor_1_1 : (6 : ZMod 1872258491) ^ 2 = 36 := by
        calc
          (6 : ZMod 1872258491) ^ 2 = (6 : ZMod 1872258491) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 1 * (6 : ZMod 1872258491) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_1_0]; decide
      have factor_1_2 : (6 : ZMod 1872258491) ^ 5 = 7776 := by
        calc
          (6 : ZMod 1872258491) ^ 5 = (6 : ZMod 1872258491) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 2 * (6 : ZMod 1872258491) ^ 2) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_1_1]; decide
      have factor_1_3 : (6 : ZMod 1872258491) ^ 11 = 362797056 := by
        calc
          (6 : ZMod 1872258491) ^ 11 = (6 : ZMod 1872258491) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 5 * (6 : ZMod 1872258491) ^ 5) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 362797056 := by rw [factor_1_2]; decide
      have factor_1_4 : (6 : ZMod 1872258491) ^ 22 = 1626462915 := by
        calc
          (6 : ZMod 1872258491) ^ 22 = (6 : ZMod 1872258491) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 11 * (6 : ZMod 1872258491) ^ 11 := by rw [pow_add]
          _ = 1626462915 := by rw [factor_1_3]; decide
      have factor_1_5 : (6 : ZMod 1872258491) ^ 44 = 1532613634 := by
        calc
          (6 : ZMod 1872258491) ^ 44 = (6 : ZMod 1872258491) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 22 * (6 : ZMod 1872258491) ^ 22 := by rw [pow_add]
          _ = 1532613634 := by rw [factor_1_4]; decide
      have factor_1_6 : (6 : ZMod 1872258491) ^ 89 = 1076496517 := by
        calc
          (6 : ZMod 1872258491) ^ 89 = (6 : ZMod 1872258491) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 44 * (6 : ZMod 1872258491) ^ 44) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1076496517 := by rw [factor_1_5]; decide
      have factor_1_7 : (6 : ZMod 1872258491) ^ 178 = 774709077 := by
        calc
          (6 : ZMod 1872258491) ^ 178 = (6 : ZMod 1872258491) ^ (89 + 89) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 89 * (6 : ZMod 1872258491) ^ 89 := by rw [pow_add]
          _ = 774709077 := by rw [factor_1_6]; decide
      have factor_1_8 : (6 : ZMod 1872258491) ^ 357 = 1277523290 := by
        calc
          (6 : ZMod 1872258491) ^ 357 = (6 : ZMod 1872258491) ^ (178 + 178 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 178 * (6 : ZMod 1872258491) ^ 178) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1277523290 := by rw [factor_1_7]; decide
      have factor_1_9 : (6 : ZMod 1872258491) ^ 714 = 38455770 := by
        calc
          (6 : ZMod 1872258491) ^ 714 = (6 : ZMod 1872258491) ^ (357 + 357) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 357 * (6 : ZMod 1872258491) ^ 357 := by rw [pow_add]
          _ = 38455770 := by rw [factor_1_8]; decide
      have factor_1_10 : (6 : ZMod 1872258491) ^ 1428 = 1687489748 := by
        calc
          (6 : ZMod 1872258491) ^ 1428 = (6 : ZMod 1872258491) ^ (714 + 714) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 714 * (6 : ZMod 1872258491) ^ 714 := by rw [pow_add]
          _ = 1687489748 := by rw [factor_1_9]; decide
      have factor_1_11 : (6 : ZMod 1872258491) ^ 2856 = 628611541 := by
        calc
          (6 : ZMod 1872258491) ^ 2856 = (6 : ZMod 1872258491) ^ (1428 + 1428) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 1428 * (6 : ZMod 1872258491) ^ 1428 := by rw [pow_add]
          _ = 628611541 := by rw [factor_1_10]; decide
      have factor_1_12 : (6 : ZMod 1872258491) ^ 5713 = 1035720771 := by
        calc
          (6 : ZMod 1872258491) ^ 5713 = (6 : ZMod 1872258491) ^ (2856 + 2856 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 2856 * (6 : ZMod 1872258491) ^ 2856) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1035720771 := by rw [factor_1_11]; decide
      have factor_1_13 : (6 : ZMod 1872258491) ^ 11427 = 1236979912 := by
        calc
          (6 : ZMod 1872258491) ^ 11427 = (6 : ZMod 1872258491) ^ (5713 + 5713 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 5713 * (6 : ZMod 1872258491) ^ 5713) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1236979912 := by rw [factor_1_12]; decide
      have factor_1_14 : (6 : ZMod 1872258491) ^ 22854 = 49734401 := by
        calc
          (6 : ZMod 1872258491) ^ 22854 = (6 : ZMod 1872258491) ^ (11427 + 11427) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 11427 * (6 : ZMod 1872258491) ^ 11427 := by rw [pow_add]
          _ = 49734401 := by rw [factor_1_13]; decide
      have factor_1_15 : (6 : ZMod 1872258491) ^ 45709 = 316310222 := by
        calc
          (6 : ZMod 1872258491) ^ 45709 = (6 : ZMod 1872258491) ^ (22854 + 22854 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 22854 * (6 : ZMod 1872258491) ^ 22854) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 316310222 := by rw [factor_1_14]; decide
      have factor_1_16 : (6 : ZMod 1872258491) ^ 91418 = 1447470349 := by
        calc
          (6 : ZMod 1872258491) ^ 91418 = (6 : ZMod 1872258491) ^ (45709 + 45709) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 45709 * (6 : ZMod 1872258491) ^ 45709 := by rw [pow_add]
          _ = 1447470349 := by rw [factor_1_15]; decide
      have factor_1_17 : (6 : ZMod 1872258491) ^ 182837 = 1139656075 := by
        calc
          (6 : ZMod 1872258491) ^ 182837 = (6 : ZMod 1872258491) ^ (91418 + 91418 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 91418 * (6 : ZMod 1872258491) ^ 91418) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1139656075 := by rw [factor_1_16]; decide
      have factor_1_18 : (6 : ZMod 1872258491) ^ 365675 = 1516497336 := by
        calc
          (6 : ZMod 1872258491) ^ 365675 = (6 : ZMod 1872258491) ^ (182837 + 182837 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 182837 * (6 : ZMod 1872258491) ^ 182837) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1516497336 := by rw [factor_1_17]; decide
      have factor_1_19 : (6 : ZMod 1872258491) ^ 731350 = 1728580888 := by
        calc
          (6 : ZMod 1872258491) ^ 731350 = (6 : ZMod 1872258491) ^ (365675 + 365675) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 365675 * (6 : ZMod 1872258491) ^ 365675 := by rw [pow_add]
          _ = 1728580888 := by rw [factor_1_18]; decide
      have factor_1_20 : (6 : ZMod 1872258491) ^ 1462701 = 906918405 := by
        calc
          (6 : ZMod 1872258491) ^ 1462701 = (6 : ZMod 1872258491) ^ (731350 + 731350 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 731350 * (6 : ZMod 1872258491) ^ 731350) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 906918405 := by rw [factor_1_19]; decide
      have factor_1_21 : (6 : ZMod 1872258491) ^ 2925403 = 1732026135 := by
        calc
          (6 : ZMod 1872258491) ^ 2925403 = (6 : ZMod 1872258491) ^ (1462701 + 1462701 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 1462701 * (6 : ZMod 1872258491) ^ 1462701) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1732026135 := by rw [factor_1_20]; decide
      have factor_1_22 : (6 : ZMod 1872258491) ^ 5850807 = 805730988 := by
        calc
          (6 : ZMod 1872258491) ^ 5850807 = (6 : ZMod 1872258491) ^ (2925403 + 2925403 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 2925403 * (6 : ZMod 1872258491) ^ 2925403) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 805730988 := by rw [factor_1_21]; decide
      have factor_1_23 : (6 : ZMod 1872258491) ^ 11701615 = 815748871 := by
        calc
          (6 : ZMod 1872258491) ^ 11701615 = (6 : ZMod 1872258491) ^ (5850807 + 5850807 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 5850807 * (6 : ZMod 1872258491) ^ 5850807) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 815748871 := by rw [factor_1_22]; decide
      have factor_1_24 : (6 : ZMod 1872258491) ^ 23403231 = 979214684 := by
        calc
          (6 : ZMod 1872258491) ^ 23403231 = (6 : ZMod 1872258491) ^ (11701615 + 11701615 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 11701615 * (6 : ZMod 1872258491) ^ 11701615) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 979214684 := by rw [factor_1_23]; decide
      have factor_1_25 : (6 : ZMod 1872258491) ^ 46806462 = 1823682950 := by
        calc
          (6 : ZMod 1872258491) ^ 46806462 = (6 : ZMod 1872258491) ^ (23403231 + 23403231) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 23403231 * (6 : ZMod 1872258491) ^ 23403231 := by rw [pow_add]
          _ = 1823682950 := by rw [factor_1_24]; decide
      have factor_1_26 : (6 : ZMod 1872258491) ^ 93612924 = 146595764 := by
        calc
          (6 : ZMod 1872258491) ^ 93612924 = (6 : ZMod 1872258491) ^ (46806462 + 46806462) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 46806462 * (6 : ZMod 1872258491) ^ 46806462 := by rw [pow_add]
          _ = 146595764 := by rw [factor_1_25]; decide
      have factor_1_27 : (6 : ZMod 1872258491) ^ 187225849 = 1327220602 := by
        calc
          (6 : ZMod 1872258491) ^ 187225849 = (6 : ZMod 1872258491) ^ (93612924 + 93612924 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 93612924 * (6 : ZMod 1872258491) ^ 93612924) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 1327220602 := by rw [factor_1_26]; decide
      have factor_1_28 : (6 : ZMod 1872258491) ^ 374451698 = 1546831998 := by
        calc
          (6 : ZMod 1872258491) ^ 374451698 = (6 : ZMod 1872258491) ^ (187225849 + 187225849) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 187225849 * (6 : ZMod 1872258491) ^ 187225849 := by rw [pow_add]
          _ = 1546831998 := by rw [factor_1_27]; decide
      change (6 : ZMod 1872258491) ^ 374451698 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (6 : ZMod 1872258491) ^ 1 = 6 := by norm_num
      have factor_2_1 : (6 : ZMod 1872258491) ^ 2 = 36 := by
        calc
          (6 : ZMod 1872258491) ^ 2 = (6 : ZMod 1872258491) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 1 * (6 : ZMod 1872258491) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_2_0]; decide
      have factor_2_2 : (6 : ZMod 1872258491) ^ 5 = 7776 := by
        calc
          (6 : ZMod 1872258491) ^ 5 = (6 : ZMod 1872258491) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = ((6 : ZMod 1872258491) ^ 2 * (6 : ZMod 1872258491) ^ 2) * (6 : ZMod 1872258491) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_2_1]; decide
      have factor_2_3 : (6 : ZMod 1872258491) ^ 10 = 60466176 := by
        calc
          (6 : ZMod 1872258491) ^ 10 = (6 : ZMod 1872258491) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (6 : ZMod 1872258491) ^ n) (by norm_num)
          _ = (6 : ZMod 1872258491) ^ 5 * (6 : ZMod 1872258491) ^ 5 := by rw [pow_add]
          _ = 60466176 := by rw [factor_2_2]; decide
      change (6 : ZMod 1872258491) ^ 10 ≠ 1
      rw [factor_2_3]
      decide

#print axioms prime_lucas_1872258491

end TotientTailPeriodKiller
end Erdos249257
