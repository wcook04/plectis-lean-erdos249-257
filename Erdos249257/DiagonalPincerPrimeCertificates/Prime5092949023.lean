import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime121260691

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_5092949023 : Nat.Prime 5092949023 := by
  apply lucas_primality 5092949023 (3 : ZMod 5092949023)
  ·
      have fermat_0 : (3 : ZMod 5092949023) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 5092949023) ^ 2 = 9 := by
        calc
          (3 : ZMod 5092949023) ^ 2 = (3 : ZMod 5092949023) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 1 * (3 : ZMod 5092949023) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 5092949023) ^ 4 = 81 := by
        calc
          (3 : ZMod 5092949023) ^ 4 = (3 : ZMod 5092949023) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 2 * (3 : ZMod 5092949023) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 5092949023) ^ 9 = 19683 := by
        calc
          (3 : ZMod 5092949023) ^ 9 = (3 : ZMod 5092949023) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 4 * (3 : ZMod 5092949023) ^ 4) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 5092949023) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 5092949023) ^ 18 = (3 : ZMod 5092949023) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 9 * (3 : ZMod 5092949023) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 5092949023) ^ 37 = 609540832 := by
        calc
          (3 : ZMod 5092949023) ^ 37 = (3 : ZMod 5092949023) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 18 * (3 : ZMod 5092949023) ^ 18) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 609540832 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 5092949023) ^ 75 = 4655262413 := by
        calc
          (3 : ZMod 5092949023) ^ 75 = (3 : ZMod 5092949023) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 37 * (3 : ZMod 5092949023) ^ 37) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 4655262413 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 5092949023) ^ 151 = 1819107461 := by
        calc
          (3 : ZMod 5092949023) ^ 151 = (3 : ZMod 5092949023) ^ (75 + 75 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 75 * (3 : ZMod 5092949023) ^ 75) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 1819107461 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 5092949023) ^ 303 = 5092840771 := by
        calc
          (3 : ZMod 5092949023) ^ 303 = (3 : ZMod 5092949023) ^ (151 + 151 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 151 * (3 : ZMod 5092949023) ^ 151) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 5092840771 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 5092949023) ^ 607 = 4597792374 := by
        calc
          (3 : ZMod 5092949023) ^ 607 = (3 : ZMod 5092949023) ^ (303 + 303 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 303 * (3 : ZMod 5092949023) ^ 303) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 4597792374 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 5092949023) ^ 1214 = 5046101200 := by
        calc
          (3 : ZMod 5092949023) ^ 1214 = (3 : ZMod 5092949023) ^ (607 + 607) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 607 * (3 : ZMod 5092949023) ^ 607 := by rw [pow_add]
          _ = 5046101200 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 5092949023) ^ 2428 = 3811459893 := by
        calc
          (3 : ZMod 5092949023) ^ 2428 = (3 : ZMod 5092949023) ^ (1214 + 1214) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 1214 * (3 : ZMod 5092949023) ^ 1214 := by rw [pow_add]
          _ = 3811459893 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 5092949023) ^ 4857 = 3055528851 := by
        calc
          (3 : ZMod 5092949023) ^ 4857 = (3 : ZMod 5092949023) ^ (2428 + 2428 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 2428 * (3 : ZMod 5092949023) ^ 2428) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 3055528851 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 5092949023) ^ 9714 = 1440585569 := by
        calc
          (3 : ZMod 5092949023) ^ 9714 = (3 : ZMod 5092949023) ^ (4857 + 4857) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 4857 * (3 : ZMod 5092949023) ^ 4857 := by rw [pow_add]
          _ = 1440585569 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 5092949023) ^ 19428 = 1311248964 := by
        calc
          (3 : ZMod 5092949023) ^ 19428 = (3 : ZMod 5092949023) ^ (9714 + 9714) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 9714 * (3 : ZMod 5092949023) ^ 9714 := by rw [pow_add]
          _ = 1311248964 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 5092949023) ^ 38856 = 272771240 := by
        calc
          (3 : ZMod 5092949023) ^ 38856 = (3 : ZMod 5092949023) ^ (19428 + 19428) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 19428 * (3 : ZMod 5092949023) ^ 19428 := by rw [pow_add]
          _ = 272771240 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 5092949023) ^ 77712 = 4228670942 := by
        calc
          (3 : ZMod 5092949023) ^ 77712 = (3 : ZMod 5092949023) ^ (38856 + 38856) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 38856 * (3 : ZMod 5092949023) ^ 38856 := by rw [pow_add]
          _ = 4228670942 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 5092949023) ^ 155424 = 1863236713 := by
        calc
          (3 : ZMod 5092949023) ^ 155424 = (3 : ZMod 5092949023) ^ (77712 + 77712) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 77712 * (3 : ZMod 5092949023) ^ 77712 := by rw [pow_add]
          _ = 1863236713 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 5092949023) ^ 310848 = 4364917147 := by
        calc
          (3 : ZMod 5092949023) ^ 310848 = (3 : ZMod 5092949023) ^ (155424 + 155424) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 155424 * (3 : ZMod 5092949023) ^ 155424 := by rw [pow_add]
          _ = 4364917147 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 5092949023) ^ 621697 = 3376805493 := by
        calc
          (3 : ZMod 5092949023) ^ 621697 = (3 : ZMod 5092949023) ^ (310848 + 310848 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 310848 * (3 : ZMod 5092949023) ^ 310848) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 3376805493 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 5092949023) ^ 1243395 = 140843058 := by
        calc
          (3 : ZMod 5092949023) ^ 1243395 = (3 : ZMod 5092949023) ^ (621697 + 621697 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 621697 * (3 : ZMod 5092949023) ^ 621697) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 140843058 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 5092949023) ^ 2486791 = 1405513749 := by
        calc
          (3 : ZMod 5092949023) ^ 2486791 = (3 : ZMod 5092949023) ^ (1243395 + 1243395 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 1243395 * (3 : ZMod 5092949023) ^ 1243395) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 1405513749 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 5092949023) ^ 4973583 = 3010745528 := by
        calc
          (3 : ZMod 5092949023) ^ 4973583 = (3 : ZMod 5092949023) ^ (2486791 + 2486791 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 2486791 * (3 : ZMod 5092949023) ^ 2486791) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 3010745528 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 5092949023) ^ 9947166 = 329701416 := by
        calc
          (3 : ZMod 5092949023) ^ 9947166 = (3 : ZMod 5092949023) ^ (4973583 + 4973583) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 4973583 * (3 : ZMod 5092949023) ^ 4973583 := by rw [pow_add]
          _ = 329701416 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 5092949023) ^ 19894332 = 845674035 := by
        calc
          (3 : ZMod 5092949023) ^ 19894332 = (3 : ZMod 5092949023) ^ (9947166 + 9947166) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 9947166 * (3 : ZMod 5092949023) ^ 9947166 := by rw [pow_add]
          _ = 845674035 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 5092949023) ^ 39788664 = 406352001 := by
        calc
          (3 : ZMod 5092949023) ^ 39788664 = (3 : ZMod 5092949023) ^ (19894332 + 19894332) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 19894332 * (3 : ZMod 5092949023) ^ 19894332 := by rw [pow_add]
          _ = 406352001 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 5092949023) ^ 79577328 = 515532430 := by
        calc
          (3 : ZMod 5092949023) ^ 79577328 = (3 : ZMod 5092949023) ^ (39788664 + 39788664) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 39788664 * (3 : ZMod 5092949023) ^ 39788664 := by rw [pow_add]
          _ = 515532430 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 5092949023) ^ 159154656 = 542843295 := by
        calc
          (3 : ZMod 5092949023) ^ 159154656 = (3 : ZMod 5092949023) ^ (79577328 + 79577328) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 79577328 * (3 : ZMod 5092949023) ^ 79577328 := by rw [pow_add]
          _ = 542843295 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 5092949023) ^ 318309313 = 2937398081 := by
        calc
          (3 : ZMod 5092949023) ^ 318309313 = (3 : ZMod 5092949023) ^ (159154656 + 159154656 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 159154656 * (3 : ZMod 5092949023) ^ 159154656) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 2937398081 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 5092949023) ^ 636618627 = 4312482835 := by
        calc
          (3 : ZMod 5092949023) ^ 636618627 = (3 : ZMod 5092949023) ^ (318309313 + 318309313 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 318309313 * (3 : ZMod 5092949023) ^ 318309313) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 4312482835 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 5092949023) ^ 1273237255 = 2898650166 := by
        calc
          (3 : ZMod 5092949023) ^ 1273237255 = (3 : ZMod 5092949023) ^ (636618627 + 636618627 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 636618627 * (3 : ZMod 5092949023) ^ 636618627) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 2898650166 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 5092949023) ^ 2546474511 = 5092949022 := by
        calc
          (3 : ZMod 5092949023) ^ 2546474511 = (3 : ZMod 5092949023) ^ (1273237255 + 1273237255 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 1273237255 * (3 : ZMod 5092949023) ^ 1273237255) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 5092949022 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 5092949023) ^ 5092949022 = 1 := by
        calc
          (3 : ZMod 5092949023) ^ 5092949022 = (3 : ZMod 5092949023) ^ (2546474511 + 2546474511) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 2546474511 * (3 : ZMod 5092949023) ^ 2546474511 := by rw [pow_add]
          _ = 1 := by rw [fermat_31]; decide
      simpa using fermat_32
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (121260691, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (121260691, 1)] : List FactorBlock).map factorBlockValue).prod = 5092949023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_121260691) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 5092949023) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 5092949023) ^ 2 = 9 := by
        calc
          (3 : ZMod 5092949023) ^ 2 = (3 : ZMod 5092949023) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 1 * (3 : ZMod 5092949023) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 5092949023) ^ 4 = 81 := by
        calc
          (3 : ZMod 5092949023) ^ 4 = (3 : ZMod 5092949023) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 2 * (3 : ZMod 5092949023) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 5092949023) ^ 9 = 19683 := by
        calc
          (3 : ZMod 5092949023) ^ 9 = (3 : ZMod 5092949023) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 4 * (3 : ZMod 5092949023) ^ 4) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 5092949023) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 5092949023) ^ 18 = (3 : ZMod 5092949023) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 9 * (3 : ZMod 5092949023) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 5092949023) ^ 37 = 609540832 := by
        calc
          (3 : ZMod 5092949023) ^ 37 = (3 : ZMod 5092949023) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 18 * (3 : ZMod 5092949023) ^ 18) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 609540832 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 5092949023) ^ 75 = 4655262413 := by
        calc
          (3 : ZMod 5092949023) ^ 75 = (3 : ZMod 5092949023) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 37 * (3 : ZMod 5092949023) ^ 37) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 4655262413 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 5092949023) ^ 151 = 1819107461 := by
        calc
          (3 : ZMod 5092949023) ^ 151 = (3 : ZMod 5092949023) ^ (75 + 75 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 75 * (3 : ZMod 5092949023) ^ 75) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 1819107461 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 5092949023) ^ 303 = 5092840771 := by
        calc
          (3 : ZMod 5092949023) ^ 303 = (3 : ZMod 5092949023) ^ (151 + 151 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 151 * (3 : ZMod 5092949023) ^ 151) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 5092840771 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 5092949023) ^ 607 = 4597792374 := by
        calc
          (3 : ZMod 5092949023) ^ 607 = (3 : ZMod 5092949023) ^ (303 + 303 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 303 * (3 : ZMod 5092949023) ^ 303) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 4597792374 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 5092949023) ^ 1214 = 5046101200 := by
        calc
          (3 : ZMod 5092949023) ^ 1214 = (3 : ZMod 5092949023) ^ (607 + 607) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 607 * (3 : ZMod 5092949023) ^ 607 := by rw [pow_add]
          _ = 5046101200 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 5092949023) ^ 2428 = 3811459893 := by
        calc
          (3 : ZMod 5092949023) ^ 2428 = (3 : ZMod 5092949023) ^ (1214 + 1214) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 1214 * (3 : ZMod 5092949023) ^ 1214 := by rw [pow_add]
          _ = 3811459893 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 5092949023) ^ 4857 = 3055528851 := by
        calc
          (3 : ZMod 5092949023) ^ 4857 = (3 : ZMod 5092949023) ^ (2428 + 2428 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 2428 * (3 : ZMod 5092949023) ^ 2428) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 3055528851 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 5092949023) ^ 9714 = 1440585569 := by
        calc
          (3 : ZMod 5092949023) ^ 9714 = (3 : ZMod 5092949023) ^ (4857 + 4857) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 4857 * (3 : ZMod 5092949023) ^ 4857 := by rw [pow_add]
          _ = 1440585569 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 5092949023) ^ 19428 = 1311248964 := by
        calc
          (3 : ZMod 5092949023) ^ 19428 = (3 : ZMod 5092949023) ^ (9714 + 9714) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 9714 * (3 : ZMod 5092949023) ^ 9714 := by rw [pow_add]
          _ = 1311248964 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 5092949023) ^ 38856 = 272771240 := by
        calc
          (3 : ZMod 5092949023) ^ 38856 = (3 : ZMod 5092949023) ^ (19428 + 19428) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 19428 * (3 : ZMod 5092949023) ^ 19428 := by rw [pow_add]
          _ = 272771240 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 5092949023) ^ 77712 = 4228670942 := by
        calc
          (3 : ZMod 5092949023) ^ 77712 = (3 : ZMod 5092949023) ^ (38856 + 38856) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 38856 * (3 : ZMod 5092949023) ^ 38856 := by rw [pow_add]
          _ = 4228670942 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 5092949023) ^ 155424 = 1863236713 := by
        calc
          (3 : ZMod 5092949023) ^ 155424 = (3 : ZMod 5092949023) ^ (77712 + 77712) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 77712 * (3 : ZMod 5092949023) ^ 77712 := by rw [pow_add]
          _ = 1863236713 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 5092949023) ^ 310848 = 4364917147 := by
        calc
          (3 : ZMod 5092949023) ^ 310848 = (3 : ZMod 5092949023) ^ (155424 + 155424) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 155424 * (3 : ZMod 5092949023) ^ 155424 := by rw [pow_add]
          _ = 4364917147 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 5092949023) ^ 621697 = 3376805493 := by
        calc
          (3 : ZMod 5092949023) ^ 621697 = (3 : ZMod 5092949023) ^ (310848 + 310848 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 310848 * (3 : ZMod 5092949023) ^ 310848) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 3376805493 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 5092949023) ^ 1243395 = 140843058 := by
        calc
          (3 : ZMod 5092949023) ^ 1243395 = (3 : ZMod 5092949023) ^ (621697 + 621697 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 621697 * (3 : ZMod 5092949023) ^ 621697) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 140843058 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 5092949023) ^ 2486791 = 1405513749 := by
        calc
          (3 : ZMod 5092949023) ^ 2486791 = (3 : ZMod 5092949023) ^ (1243395 + 1243395 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 1243395 * (3 : ZMod 5092949023) ^ 1243395) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 1405513749 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 5092949023) ^ 4973583 = 3010745528 := by
        calc
          (3 : ZMod 5092949023) ^ 4973583 = (3 : ZMod 5092949023) ^ (2486791 + 2486791 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 2486791 * (3 : ZMod 5092949023) ^ 2486791) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 3010745528 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 5092949023) ^ 9947166 = 329701416 := by
        calc
          (3 : ZMod 5092949023) ^ 9947166 = (3 : ZMod 5092949023) ^ (4973583 + 4973583) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 4973583 * (3 : ZMod 5092949023) ^ 4973583 := by rw [pow_add]
          _ = 329701416 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 5092949023) ^ 19894332 = 845674035 := by
        calc
          (3 : ZMod 5092949023) ^ 19894332 = (3 : ZMod 5092949023) ^ (9947166 + 9947166) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 9947166 * (3 : ZMod 5092949023) ^ 9947166 := by rw [pow_add]
          _ = 845674035 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 5092949023) ^ 39788664 = 406352001 := by
        calc
          (3 : ZMod 5092949023) ^ 39788664 = (3 : ZMod 5092949023) ^ (19894332 + 19894332) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 19894332 * (3 : ZMod 5092949023) ^ 19894332 := by rw [pow_add]
          _ = 406352001 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 5092949023) ^ 79577328 = 515532430 := by
        calc
          (3 : ZMod 5092949023) ^ 79577328 = (3 : ZMod 5092949023) ^ (39788664 + 39788664) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 39788664 * (3 : ZMod 5092949023) ^ 39788664 := by rw [pow_add]
          _ = 515532430 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 5092949023) ^ 159154656 = 542843295 := by
        calc
          (3 : ZMod 5092949023) ^ 159154656 = (3 : ZMod 5092949023) ^ (79577328 + 79577328) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 79577328 * (3 : ZMod 5092949023) ^ 79577328 := by rw [pow_add]
          _ = 542843295 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 5092949023) ^ 318309313 = 2937398081 := by
        calc
          (3 : ZMod 5092949023) ^ 318309313 = (3 : ZMod 5092949023) ^ (159154656 + 159154656 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 159154656 * (3 : ZMod 5092949023) ^ 159154656) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 2937398081 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 5092949023) ^ 636618627 = 4312482835 := by
        calc
          (3 : ZMod 5092949023) ^ 636618627 = (3 : ZMod 5092949023) ^ (318309313 + 318309313 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 318309313 * (3 : ZMod 5092949023) ^ 318309313) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 4312482835 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 5092949023) ^ 1273237255 = 2898650166 := by
        calc
          (3 : ZMod 5092949023) ^ 1273237255 = (3 : ZMod 5092949023) ^ (636618627 + 636618627 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 636618627 * (3 : ZMod 5092949023) ^ 636618627) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 2898650166 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 5092949023) ^ 2546474511 = 5092949022 := by
        calc
          (3 : ZMod 5092949023) ^ 2546474511 = (3 : ZMod 5092949023) ^ (1273237255 + 1273237255 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 1273237255 * (3 : ZMod 5092949023) ^ 1273237255) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 5092949022 := by rw [factor_0_30]; decide
      change (3 : ZMod 5092949023) ^ 2546474511 ≠ 1
      rw [factor_0_31]
      decide
    ·
      have factor_1_0 : (3 : ZMod 5092949023) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 5092949023) ^ 3 = 27 := by
        calc
          (3 : ZMod 5092949023) ^ 3 = (3 : ZMod 5092949023) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 1 * (3 : ZMod 5092949023) ^ 1) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 5092949023) ^ 6 = 729 := by
        calc
          (3 : ZMod 5092949023) ^ 6 = (3 : ZMod 5092949023) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 3 * (3 : ZMod 5092949023) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 5092949023) ^ 12 = 531441 := by
        calc
          (3 : ZMod 5092949023) ^ 12 = (3 : ZMod 5092949023) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 6 * (3 : ZMod 5092949023) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 5092949023) ^ 25 = 1859071625 := by
        calc
          (3 : ZMod 5092949023) ^ 25 = (3 : ZMod 5092949023) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 12 * (3 : ZMod 5092949023) ^ 12) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 1859071625 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 5092949023) ^ 50 = 4085971037 := by
        calc
          (3 : ZMod 5092949023) ^ 50 = (3 : ZMod 5092949023) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 25 * (3 : ZMod 5092949023) ^ 25 := by rw [pow_add]
          _ = 4085971037 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 5092949023) ^ 101 = 2851292736 := by
        calc
          (3 : ZMod 5092949023) ^ 101 = (3 : ZMod 5092949023) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 50 * (3 : ZMod 5092949023) ^ 50) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 2851292736 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 5092949023) ^ 202 = 3749797947 := by
        calc
          (3 : ZMod 5092949023) ^ 202 = (3 : ZMod 5092949023) ^ (101 + 101) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 101 * (3 : ZMod 5092949023) ^ 101 := by rw [pow_add]
          _ = 3749797947 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 5092949023) ^ 404 = 34281443 := by
        calc
          (3 : ZMod 5092949023) ^ 404 = (3 : ZMod 5092949023) ^ (202 + 202) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 202 * (3 : ZMod 5092949023) ^ 202 := by rw [pow_add]
          _ = 34281443 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 5092949023) ^ 809 = 2018875744 := by
        calc
          (3 : ZMod 5092949023) ^ 809 = (3 : ZMod 5092949023) ^ (404 + 404 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 404 * (3 : ZMod 5092949023) ^ 404) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 2018875744 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 5092949023) ^ 1619 = 3806141716 := by
        calc
          (3 : ZMod 5092949023) ^ 1619 = (3 : ZMod 5092949023) ^ (809 + 809 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 809 * (3 : ZMod 5092949023) ^ 809) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 3806141716 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 5092949023) ^ 3238 = 3397886841 := by
        calc
          (3 : ZMod 5092949023) ^ 3238 = (3 : ZMod 5092949023) ^ (1619 + 1619) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 1619 * (3 : ZMod 5092949023) ^ 1619 := by rw [pow_add]
          _ = 3397886841 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 5092949023) ^ 6476 = 2415675612 := by
        calc
          (3 : ZMod 5092949023) ^ 6476 = (3 : ZMod 5092949023) ^ (3238 + 3238) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 3238 * (3 : ZMod 5092949023) ^ 3238 := by rw [pow_add]
          _ = 2415675612 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 5092949023) ^ 12952 = 1887759227 := by
        calc
          (3 : ZMod 5092949023) ^ 12952 = (3 : ZMod 5092949023) ^ (6476 + 6476) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 6476 * (3 : ZMod 5092949023) ^ 6476 := by rw [pow_add]
          _ = 1887759227 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 5092949023) ^ 25904 = 654126847 := by
        calc
          (3 : ZMod 5092949023) ^ 25904 = (3 : ZMod 5092949023) ^ (12952 + 12952) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 12952 * (3 : ZMod 5092949023) ^ 12952 := by rw [pow_add]
          _ = 654126847 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 5092949023) ^ 51808 = 4673947276 := by
        calc
          (3 : ZMod 5092949023) ^ 51808 = (3 : ZMod 5092949023) ^ (25904 + 25904) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 25904 * (3 : ZMod 5092949023) ^ 25904 := by rw [pow_add]
          _ = 4673947276 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 5092949023) ^ 103616 = 848424576 := by
        calc
          (3 : ZMod 5092949023) ^ 103616 = (3 : ZMod 5092949023) ^ (51808 + 51808) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 51808 * (3 : ZMod 5092949023) ^ 51808 := by rw [pow_add]
          _ = 848424576 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 5092949023) ^ 207232 = 1337286185 := by
        calc
          (3 : ZMod 5092949023) ^ 207232 = (3 : ZMod 5092949023) ^ (103616 + 103616) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 103616 * (3 : ZMod 5092949023) ^ 103616 := by rw [pow_add]
          _ = 1337286185 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 5092949023) ^ 414465 = 3964376896 := by
        calc
          (3 : ZMod 5092949023) ^ 414465 = (3 : ZMod 5092949023) ^ (207232 + 207232 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 207232 * (3 : ZMod 5092949023) ^ 207232) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 3964376896 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 5092949023) ^ 828930 = 193287049 := by
        calc
          (3 : ZMod 5092949023) ^ 828930 = (3 : ZMod 5092949023) ^ (414465 + 414465) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 414465 * (3 : ZMod 5092949023) ^ 414465 := by rw [pow_add]
          _ = 193287049 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 5092949023) ^ 1657861 = 1864405182 := by
        calc
          (3 : ZMod 5092949023) ^ 1657861 = (3 : ZMod 5092949023) ^ (828930 + 828930 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 828930 * (3 : ZMod 5092949023) ^ 828930) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 1864405182 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 5092949023) ^ 3315722 = 662334635 := by
        calc
          (3 : ZMod 5092949023) ^ 3315722 = (3 : ZMod 5092949023) ^ (1657861 + 1657861) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 1657861 * (3 : ZMod 5092949023) ^ 1657861 := by rw [pow_add]
          _ = 662334635 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 5092949023) ^ 6631444 = 37580108 := by
        calc
          (3 : ZMod 5092949023) ^ 6631444 = (3 : ZMod 5092949023) ^ (3315722 + 3315722) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 3315722 * (3 : ZMod 5092949023) ^ 3315722 := by rw [pow_add]
          _ = 37580108 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 5092949023) ^ 13262888 = 5032060833 := by
        calc
          (3 : ZMod 5092949023) ^ 13262888 = (3 : ZMod 5092949023) ^ (6631444 + 6631444) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 6631444 * (3 : ZMod 5092949023) ^ 6631444 := by rw [pow_add]
          _ = 5032060833 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 5092949023) ^ 26525776 = 183775434 := by
        calc
          (3 : ZMod 5092949023) ^ 26525776 = (3 : ZMod 5092949023) ^ (13262888 + 13262888) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 13262888 * (3 : ZMod 5092949023) ^ 13262888 := by rw [pow_add]
          _ = 183775434 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 5092949023) ^ 53051552 = 2526021041 := by
        calc
          (3 : ZMod 5092949023) ^ 53051552 = (3 : ZMod 5092949023) ^ (26525776 + 26525776) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 26525776 * (3 : ZMod 5092949023) ^ 26525776 := by rw [pow_add]
          _ = 2526021041 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 5092949023) ^ 106103104 = 710084360 := by
        calc
          (3 : ZMod 5092949023) ^ 106103104 = (3 : ZMod 5092949023) ^ (53051552 + 53051552) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 53051552 * (3 : ZMod 5092949023) ^ 53051552 := by rw [pow_add]
          _ = 710084360 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 5092949023) ^ 212206209 = 3131648047 := by
        calc
          (3 : ZMod 5092949023) ^ 212206209 = (3 : ZMod 5092949023) ^ (106103104 + 106103104 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 106103104 * (3 : ZMod 5092949023) ^ 106103104) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 3131648047 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 5092949023) ^ 424412418 = 3995799594 := by
        calc
          (3 : ZMod 5092949023) ^ 424412418 = (3 : ZMod 5092949023) ^ (212206209 + 212206209) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 212206209 * (3 : ZMod 5092949023) ^ 212206209 := by rw [pow_add]
          _ = 3995799594 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 5092949023) ^ 848824837 = 3291448286 := by
        calc
          (3 : ZMod 5092949023) ^ 848824837 = (3 : ZMod 5092949023) ^ (424412418 + 424412418 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 424412418 * (3 : ZMod 5092949023) ^ 424412418) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 3291448286 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 5092949023) ^ 1697649674 = 3291448285 := by
        calc
          (3 : ZMod 5092949023) ^ 1697649674 = (3 : ZMod 5092949023) ^ (848824837 + 848824837) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 848824837 * (3 : ZMod 5092949023) ^ 848824837 := by rw [pow_add]
          _ = 3291448285 := by rw [factor_1_29]; decide
      change (3 : ZMod 5092949023) ^ 1697649674 ≠ 1
      rw [factor_1_30]
      decide
    ·
      have factor_2_0 : (3 : ZMod 5092949023) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 5092949023) ^ 2 = 9 := by
        calc
          (3 : ZMod 5092949023) ^ 2 = (3 : ZMod 5092949023) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 1 * (3 : ZMod 5092949023) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 5092949023) ^ 5 = 243 := by
        calc
          (3 : ZMod 5092949023) ^ 5 = (3 : ZMod 5092949023) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 2 * (3 : ZMod 5092949023) ^ 2) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 5092949023) ^ 10 = 59049 := by
        calc
          (3 : ZMod 5092949023) ^ 10 = (3 : ZMod 5092949023) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 5 * (3 : ZMod 5092949023) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 5092949023) ^ 21 = 274455157 := by
        calc
          (3 : ZMod 5092949023) ^ 21 = (3 : ZMod 5092949023) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 10 * (3 : ZMod 5092949023) ^ 10) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 274455157 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 5092949023) ^ 43 = 1268701527 := by
        calc
          (3 : ZMod 5092949023) ^ 43 = (3 : ZMod 5092949023) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 21 * (3 : ZMod 5092949023) ^ 21) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 1268701527 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 5092949023) ^ 86 = 186024482 := by
        calc
          (3 : ZMod 5092949023) ^ 86 = (3 : ZMod 5092949023) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 43 * (3 : ZMod 5092949023) ^ 43 := by rw [pow_add]
          _ = 186024482 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 5092949023) ^ 173 = 4020747051 := by
        calc
          (3 : ZMod 5092949023) ^ 173 = (3 : ZMod 5092949023) ^ (86 + 86 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 86 * (3 : ZMod 5092949023) ^ 86) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 4020747051 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 5092949023) ^ 346 = 2078602437 := by
        calc
          (3 : ZMod 5092949023) ^ 346 = (3 : ZMod 5092949023) ^ (173 + 173) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 173 * (3 : ZMod 5092949023) ^ 173 := by rw [pow_add]
          _ = 2078602437 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 5092949023) ^ 693 = 237062010 := by
        calc
          (3 : ZMod 5092949023) ^ 693 = (3 : ZMod 5092949023) ^ (346 + 346 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 346 * (3 : ZMod 5092949023) ^ 346) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 237062010 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 5092949023) ^ 1387 = 3109333419 := by
        calc
          (3 : ZMod 5092949023) ^ 1387 = (3 : ZMod 5092949023) ^ (693 + 693 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 693 * (3 : ZMod 5092949023) ^ 693) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 3109333419 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 5092949023) ^ 2775 = 2872621322 := by
        calc
          (3 : ZMod 5092949023) ^ 2775 = (3 : ZMod 5092949023) ^ (1387 + 1387 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 1387 * (3 : ZMod 5092949023) ^ 1387) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 2872621322 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 5092949023) ^ 5550 = 2542260326 := by
        calc
          (3 : ZMod 5092949023) ^ 5550 = (3 : ZMod 5092949023) ^ (2775 + 2775) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 2775 * (3 : ZMod 5092949023) ^ 2775 := by rw [pow_add]
          _ = 2542260326 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 5092949023) ^ 11101 = 4558267395 := by
        calc
          (3 : ZMod 5092949023) ^ 11101 = (3 : ZMod 5092949023) ^ (5550 + 5550 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 5550 * (3 : ZMod 5092949023) ^ 5550) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 4558267395 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 5092949023) ^ 22203 = 1476127932 := by
        calc
          (3 : ZMod 5092949023) ^ 22203 = (3 : ZMod 5092949023) ^ (11101 + 11101 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 11101 * (3 : ZMod 5092949023) ^ 11101) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 1476127932 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 5092949023) ^ 44406 = 547760218 := by
        calc
          (3 : ZMod 5092949023) ^ 44406 = (3 : ZMod 5092949023) ^ (22203 + 22203) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 22203 * (3 : ZMod 5092949023) ^ 22203 := by rw [pow_add]
          _ = 547760218 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 5092949023) ^ 88813 = 2746726834 := by
        calc
          (3 : ZMod 5092949023) ^ 88813 = (3 : ZMod 5092949023) ^ (44406 + 44406 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 44406 * (3 : ZMod 5092949023) ^ 44406) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 2746726834 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 5092949023) ^ 177627 = 3610676815 := by
        calc
          (3 : ZMod 5092949023) ^ 177627 = (3 : ZMod 5092949023) ^ (88813 + 88813 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 88813 * (3 : ZMod 5092949023) ^ 88813) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 3610676815 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 5092949023) ^ 355255 = 434598904 := by
        calc
          (3 : ZMod 5092949023) ^ 355255 = (3 : ZMod 5092949023) ^ (177627 + 177627 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 177627 * (3 : ZMod 5092949023) ^ 177627) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 434598904 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 5092949023) ^ 710511 = 4029000861 := by
        calc
          (3 : ZMod 5092949023) ^ 710511 = (3 : ZMod 5092949023) ^ (355255 + 355255 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 355255 * (3 : ZMod 5092949023) ^ 355255) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 4029000861 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 5092949023) ^ 1421023 = 96592079 := by
        calc
          (3 : ZMod 5092949023) ^ 1421023 = (3 : ZMod 5092949023) ^ (710511 + 710511 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 710511 * (3 : ZMod 5092949023) ^ 710511) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 96592079 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 5092949023) ^ 2842047 = 195623150 := by
        calc
          (3 : ZMod 5092949023) ^ 2842047 = (3 : ZMod 5092949023) ^ (1421023 + 1421023 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 1421023 * (3 : ZMod 5092949023) ^ 1421023) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 195623150 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 5092949023) ^ 5684094 = 2950049523 := by
        calc
          (3 : ZMod 5092949023) ^ 5684094 = (3 : ZMod 5092949023) ^ (2842047 + 2842047) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 2842047 * (3 : ZMod 5092949023) ^ 2842047 := by rw [pow_add]
          _ = 2950049523 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 5092949023) ^ 11368189 = 3938178369 := by
        calc
          (3 : ZMod 5092949023) ^ 11368189 = (3 : ZMod 5092949023) ^ (5684094 + 5684094 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 5684094 * (3 : ZMod 5092949023) ^ 5684094) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 3938178369 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 5092949023) ^ 22736379 = 915339068 := by
        calc
          (3 : ZMod 5092949023) ^ 22736379 = (3 : ZMod 5092949023) ^ (11368189 + 11368189 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 11368189 * (3 : ZMod 5092949023) ^ 11368189) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 915339068 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 5092949023) ^ 45472759 = 1960213025 := by
        calc
          (3 : ZMod 5092949023) ^ 45472759 = (3 : ZMod 5092949023) ^ (22736379 + 22736379 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 22736379 * (3 : ZMod 5092949023) ^ 22736379) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 1960213025 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 5092949023) ^ 90945518 = 3242954973 := by
        calc
          (3 : ZMod 5092949023) ^ 90945518 = (3 : ZMod 5092949023) ^ (45472759 + 45472759) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 45472759 * (3 : ZMod 5092949023) ^ 45472759 := by rw [pow_add]
          _ = 3242954973 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 5092949023) ^ 181891036 = 164968153 := by
        calc
          (3 : ZMod 5092949023) ^ 181891036 = (3 : ZMod 5092949023) ^ (90945518 + 90945518) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 90945518 * (3 : ZMod 5092949023) ^ 90945518 := by rw [pow_add]
          _ = 164968153 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 5092949023) ^ 363782073 = 2818025426 := by
        calc
          (3 : ZMod 5092949023) ^ 363782073 = (3 : ZMod 5092949023) ^ (181891036 + 181891036 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 181891036 * (3 : ZMod 5092949023) ^ 181891036) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 2818025426 := by rw [factor_2_27]; decide
      have factor_2_29 : (3 : ZMod 5092949023) ^ 727564146 = 3172881683 := by
        calc
          (3 : ZMod 5092949023) ^ 727564146 = (3 : ZMod 5092949023) ^ (363782073 + 363782073) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 363782073 * (3 : ZMod 5092949023) ^ 363782073 := by rw [pow_add]
          _ = 3172881683 := by rw [factor_2_28]; decide
      change (3 : ZMod 5092949023) ^ 727564146 ≠ 1
      rw [factor_2_29]
      decide
    ·
      have factor_3_0 : (3 : ZMod 5092949023) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 5092949023) ^ 2 = 9 := by
        calc
          (3 : ZMod 5092949023) ^ 2 = (3 : ZMod 5092949023) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 1 * (3 : ZMod 5092949023) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 5092949023) ^ 5 = 243 := by
        calc
          (3 : ZMod 5092949023) ^ 5 = (3 : ZMod 5092949023) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 2 * (3 : ZMod 5092949023) ^ 2) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 5092949023) ^ 10 = 59049 := by
        calc
          (3 : ZMod 5092949023) ^ 10 = (3 : ZMod 5092949023) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 5 * (3 : ZMod 5092949023) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 5092949023) ^ 21 = 274455157 := by
        calc
          (3 : ZMod 5092949023) ^ 21 = (3 : ZMod 5092949023) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = ((3 : ZMod 5092949023) ^ 10 * (3 : ZMod 5092949023) ^ 10) * (3 : ZMod 5092949023) := by rw [pow_succ, pow_add]
          _ = 274455157 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 5092949023) ^ 42 = 422900509 := by
        calc
          (3 : ZMod 5092949023) ^ 42 = (3 : ZMod 5092949023) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (3 : ZMod 5092949023) ^ n) (by norm_num)
          _ = (3 : ZMod 5092949023) ^ 21 * (3 : ZMod 5092949023) ^ 21 := by rw [pow_add]
          _ = 422900509 := by rw [factor_3_4]; decide
      change (3 : ZMod 5092949023) ^ 42 ≠ 1
      rw [factor_3_5]
      decide

#print axioms prime_lucas_5092949023

end TotientTailPeriodKiller
end Erdos249257
