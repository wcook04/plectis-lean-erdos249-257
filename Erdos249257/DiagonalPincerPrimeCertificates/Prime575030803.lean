import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime95838467

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_575030803 : Nat.Prime 575030803 := by
  apply lucas_primality 575030803 (7 : ZMod 575030803)
  ·
      have fermat_0 : (7 : ZMod 575030803) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 575030803) ^ 2 = 49 := by
        calc
          (7 : ZMod 575030803) ^ 2 = (7 : ZMod 575030803) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 1 * (7 : ZMod 575030803) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 575030803) ^ 4 = 2401 := by
        calc
          (7 : ZMod 575030803) ^ 4 = (7 : ZMod 575030803) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 2 * (7 : ZMod 575030803) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 575030803) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 575030803) ^ 8 = (7 : ZMod 575030803) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 4 * (7 : ZMod 575030803) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 575030803) ^ 17 = 77541148 := by
        calc
          (7 : ZMod 575030803) ^ 17 = (7 : ZMod 575030803) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 8 * (7 : ZMod 575030803) ^ 8) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 77541148 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 575030803) ^ 34 = 26229743 := by
        calc
          (7 : ZMod 575030803) ^ 34 = (7 : ZMod 575030803) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 17 * (7 : ZMod 575030803) ^ 17 := by rw [pow_add]
          _ = 26229743 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 575030803) ^ 68 = 363411881 := by
        calc
          (7 : ZMod 575030803) ^ 68 = (7 : ZMod 575030803) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 34 * (7 : ZMod 575030803) ^ 34 := by rw [pow_add]
          _ = 363411881 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 575030803) ^ 137 = 337156130 := by
        calc
          (7 : ZMod 575030803) ^ 137 = (7 : ZMod 575030803) ^ (68 + 68 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 68 * (7 : ZMod 575030803) ^ 68) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 337156130 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 575030803) ^ 274 = 143471196 := by
        calc
          (7 : ZMod 575030803) ^ 274 = (7 : ZMod 575030803) ^ (137 + 137) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 137 * (7 : ZMod 575030803) ^ 137 := by rw [pow_add]
          _ = 143471196 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 575030803) ^ 548 = 322779471 := by
        calc
          (7 : ZMod 575030803) ^ 548 = (7 : ZMod 575030803) ^ (274 + 274) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 274 * (7 : ZMod 575030803) ^ 274 := by rw [pow_add]
          _ = 322779471 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 575030803) ^ 1096 = 27260367 := by
        calc
          (7 : ZMod 575030803) ^ 1096 = (7 : ZMod 575030803) ^ (548 + 548) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 548 * (7 : ZMod 575030803) ^ 548 := by rw [pow_add]
          _ = 27260367 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 575030803) ^ 2193 = 160075165 := by
        calc
          (7 : ZMod 575030803) ^ 2193 = (7 : ZMod 575030803) ^ (1096 + 1096 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 1096 * (7 : ZMod 575030803) ^ 1096) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 160075165 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 575030803) ^ 4387 = 144506328 := by
        calc
          (7 : ZMod 575030803) ^ 4387 = (7 : ZMod 575030803) ^ (2193 + 2193 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 2193 * (7 : ZMod 575030803) ^ 2193) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 144506328 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 575030803) ^ 8774 = 254939045 := by
        calc
          (7 : ZMod 575030803) ^ 8774 = (7 : ZMod 575030803) ^ (4387 + 4387) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 4387 * (7 : ZMod 575030803) ^ 4387 := by rw [pow_add]
          _ = 254939045 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 575030803) ^ 17548 = 374667096 := by
        calc
          (7 : ZMod 575030803) ^ 17548 = (7 : ZMod 575030803) ^ (8774 + 8774) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 8774 * (7 : ZMod 575030803) ^ 8774 := by rw [pow_add]
          _ = 374667096 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 575030803) ^ 35097 = 34516202 := by
        calc
          (7 : ZMod 575030803) ^ 35097 = (7 : ZMod 575030803) ^ (17548 + 17548 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 17548 * (7 : ZMod 575030803) ^ 17548) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 34516202 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 575030803) ^ 70194 = 406832905 := by
        calc
          (7 : ZMod 575030803) ^ 70194 = (7 : ZMod 575030803) ^ (35097 + 35097) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 35097 * (7 : ZMod 575030803) ^ 35097 := by rw [pow_add]
          _ = 406832905 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 575030803) ^ 140388 = 111660731 := by
        calc
          (7 : ZMod 575030803) ^ 140388 = (7 : ZMod 575030803) ^ (70194 + 70194) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 70194 * (7 : ZMod 575030803) ^ 70194 := by rw [pow_add]
          _ = 111660731 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 575030803) ^ 280776 = 235698392 := by
        calc
          (7 : ZMod 575030803) ^ 280776 = (7 : ZMod 575030803) ^ (140388 + 140388) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 140388 * (7 : ZMod 575030803) ^ 140388 := by rw [pow_add]
          _ = 235698392 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 575030803) ^ 561553 = 242610226 := by
        calc
          (7 : ZMod 575030803) ^ 561553 = (7 : ZMod 575030803) ^ (280776 + 280776 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 280776 * (7 : ZMod 575030803) ^ 280776) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 242610226 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 575030803) ^ 1123107 = 264553282 := by
        calc
          (7 : ZMod 575030803) ^ 1123107 = (7 : ZMod 575030803) ^ (561553 + 561553 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 561553 * (7 : ZMod 575030803) ^ 561553) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 264553282 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 575030803) ^ 2246214 = 106710812 := by
        calc
          (7 : ZMod 575030803) ^ 2246214 = (7 : ZMod 575030803) ^ (1123107 + 1123107) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 1123107 * (7 : ZMod 575030803) ^ 1123107 := by rw [pow_add]
          _ = 106710812 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 575030803) ^ 4492428 = 413283064 := by
        calc
          (7 : ZMod 575030803) ^ 4492428 = (7 : ZMod 575030803) ^ (2246214 + 2246214) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 2246214 * (7 : ZMod 575030803) ^ 2246214 := by rw [pow_add]
          _ = 413283064 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 575030803) ^ 8984856 = 519265917 := by
        calc
          (7 : ZMod 575030803) ^ 8984856 = (7 : ZMod 575030803) ^ (4492428 + 4492428) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 4492428 * (7 : ZMod 575030803) ^ 4492428 := by rw [pow_add]
          _ = 519265917 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 575030803) ^ 17969712 = 205340827 := by
        calc
          (7 : ZMod 575030803) ^ 17969712 = (7 : ZMod 575030803) ^ (8984856 + 8984856) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 8984856 * (7 : ZMod 575030803) ^ 8984856 := by rw [pow_add]
          _ = 205340827 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 575030803) ^ 35939425 = 150908951 := by
        calc
          (7 : ZMod 575030803) ^ 35939425 = (7 : ZMod 575030803) ^ (17969712 + 17969712 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 17969712 * (7 : ZMod 575030803) ^ 17969712) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 150908951 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 575030803) ^ 71878850 = 195370446 := by
        calc
          (7 : ZMod 575030803) ^ 71878850 = (7 : ZMod 575030803) ^ (35939425 + 35939425) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 35939425 * (7 : ZMod 575030803) ^ 35939425 := by rw [pow_add]
          _ = 195370446 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 575030803) ^ 143757700 = 317122988 := by
        calc
          (7 : ZMod 575030803) ^ 143757700 = (7 : ZMod 575030803) ^ (71878850 + 71878850) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 71878850 * (7 : ZMod 575030803) ^ 71878850 := by rw [pow_add]
          _ = 317122988 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 575030803) ^ 287515401 = 575030802 := by
        calc
          (7 : ZMod 575030803) ^ 287515401 = (7 : ZMod 575030803) ^ (143757700 + 143757700 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 143757700 * (7 : ZMod 575030803) ^ 143757700) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 575030802 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 575030803) ^ 575030802 = 1 := by
        calc
          (7 : ZMod 575030803) ^ 575030802 = (7 : ZMod 575030803) ^ (287515401 + 287515401) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 287515401 * (7 : ZMod 575030803) ^ 287515401 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (95838467, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (95838467, 1)] : List FactorBlock).map factorBlockValue).prod = 575030803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_95838467) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 575030803) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 575030803) ^ 2 = 49 := by
        calc
          (7 : ZMod 575030803) ^ 2 = (7 : ZMod 575030803) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 1 * (7 : ZMod 575030803) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 575030803) ^ 4 = 2401 := by
        calc
          (7 : ZMod 575030803) ^ 4 = (7 : ZMod 575030803) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 2 * (7 : ZMod 575030803) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 575030803) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 575030803) ^ 8 = (7 : ZMod 575030803) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 4 * (7 : ZMod 575030803) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 575030803) ^ 17 = 77541148 := by
        calc
          (7 : ZMod 575030803) ^ 17 = (7 : ZMod 575030803) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 8 * (7 : ZMod 575030803) ^ 8) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 77541148 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 575030803) ^ 34 = 26229743 := by
        calc
          (7 : ZMod 575030803) ^ 34 = (7 : ZMod 575030803) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 17 * (7 : ZMod 575030803) ^ 17 := by rw [pow_add]
          _ = 26229743 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 575030803) ^ 68 = 363411881 := by
        calc
          (7 : ZMod 575030803) ^ 68 = (7 : ZMod 575030803) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 34 * (7 : ZMod 575030803) ^ 34 := by rw [pow_add]
          _ = 363411881 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 575030803) ^ 137 = 337156130 := by
        calc
          (7 : ZMod 575030803) ^ 137 = (7 : ZMod 575030803) ^ (68 + 68 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 68 * (7 : ZMod 575030803) ^ 68) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 337156130 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 575030803) ^ 274 = 143471196 := by
        calc
          (7 : ZMod 575030803) ^ 274 = (7 : ZMod 575030803) ^ (137 + 137) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 137 * (7 : ZMod 575030803) ^ 137 := by rw [pow_add]
          _ = 143471196 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 575030803) ^ 548 = 322779471 := by
        calc
          (7 : ZMod 575030803) ^ 548 = (7 : ZMod 575030803) ^ (274 + 274) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 274 * (7 : ZMod 575030803) ^ 274 := by rw [pow_add]
          _ = 322779471 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 575030803) ^ 1096 = 27260367 := by
        calc
          (7 : ZMod 575030803) ^ 1096 = (7 : ZMod 575030803) ^ (548 + 548) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 548 * (7 : ZMod 575030803) ^ 548 := by rw [pow_add]
          _ = 27260367 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 575030803) ^ 2193 = 160075165 := by
        calc
          (7 : ZMod 575030803) ^ 2193 = (7 : ZMod 575030803) ^ (1096 + 1096 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 1096 * (7 : ZMod 575030803) ^ 1096) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 160075165 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 575030803) ^ 4387 = 144506328 := by
        calc
          (7 : ZMod 575030803) ^ 4387 = (7 : ZMod 575030803) ^ (2193 + 2193 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 2193 * (7 : ZMod 575030803) ^ 2193) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 144506328 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 575030803) ^ 8774 = 254939045 := by
        calc
          (7 : ZMod 575030803) ^ 8774 = (7 : ZMod 575030803) ^ (4387 + 4387) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 4387 * (7 : ZMod 575030803) ^ 4387 := by rw [pow_add]
          _ = 254939045 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 575030803) ^ 17548 = 374667096 := by
        calc
          (7 : ZMod 575030803) ^ 17548 = (7 : ZMod 575030803) ^ (8774 + 8774) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 8774 * (7 : ZMod 575030803) ^ 8774 := by rw [pow_add]
          _ = 374667096 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 575030803) ^ 35097 = 34516202 := by
        calc
          (7 : ZMod 575030803) ^ 35097 = (7 : ZMod 575030803) ^ (17548 + 17548 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 17548 * (7 : ZMod 575030803) ^ 17548) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 34516202 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 575030803) ^ 70194 = 406832905 := by
        calc
          (7 : ZMod 575030803) ^ 70194 = (7 : ZMod 575030803) ^ (35097 + 35097) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 35097 * (7 : ZMod 575030803) ^ 35097 := by rw [pow_add]
          _ = 406832905 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 575030803) ^ 140388 = 111660731 := by
        calc
          (7 : ZMod 575030803) ^ 140388 = (7 : ZMod 575030803) ^ (70194 + 70194) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 70194 * (7 : ZMod 575030803) ^ 70194 := by rw [pow_add]
          _ = 111660731 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 575030803) ^ 280776 = 235698392 := by
        calc
          (7 : ZMod 575030803) ^ 280776 = (7 : ZMod 575030803) ^ (140388 + 140388) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 140388 * (7 : ZMod 575030803) ^ 140388 := by rw [pow_add]
          _ = 235698392 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 575030803) ^ 561553 = 242610226 := by
        calc
          (7 : ZMod 575030803) ^ 561553 = (7 : ZMod 575030803) ^ (280776 + 280776 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 280776 * (7 : ZMod 575030803) ^ 280776) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 242610226 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 575030803) ^ 1123107 = 264553282 := by
        calc
          (7 : ZMod 575030803) ^ 1123107 = (7 : ZMod 575030803) ^ (561553 + 561553 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 561553 * (7 : ZMod 575030803) ^ 561553) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 264553282 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 575030803) ^ 2246214 = 106710812 := by
        calc
          (7 : ZMod 575030803) ^ 2246214 = (7 : ZMod 575030803) ^ (1123107 + 1123107) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 1123107 * (7 : ZMod 575030803) ^ 1123107 := by rw [pow_add]
          _ = 106710812 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 575030803) ^ 4492428 = 413283064 := by
        calc
          (7 : ZMod 575030803) ^ 4492428 = (7 : ZMod 575030803) ^ (2246214 + 2246214) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 2246214 * (7 : ZMod 575030803) ^ 2246214 := by rw [pow_add]
          _ = 413283064 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 575030803) ^ 8984856 = 519265917 := by
        calc
          (7 : ZMod 575030803) ^ 8984856 = (7 : ZMod 575030803) ^ (4492428 + 4492428) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 4492428 * (7 : ZMod 575030803) ^ 4492428 := by rw [pow_add]
          _ = 519265917 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 575030803) ^ 17969712 = 205340827 := by
        calc
          (7 : ZMod 575030803) ^ 17969712 = (7 : ZMod 575030803) ^ (8984856 + 8984856) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 8984856 * (7 : ZMod 575030803) ^ 8984856 := by rw [pow_add]
          _ = 205340827 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 575030803) ^ 35939425 = 150908951 := by
        calc
          (7 : ZMod 575030803) ^ 35939425 = (7 : ZMod 575030803) ^ (17969712 + 17969712 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 17969712 * (7 : ZMod 575030803) ^ 17969712) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 150908951 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 575030803) ^ 71878850 = 195370446 := by
        calc
          (7 : ZMod 575030803) ^ 71878850 = (7 : ZMod 575030803) ^ (35939425 + 35939425) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 35939425 * (7 : ZMod 575030803) ^ 35939425 := by rw [pow_add]
          _ = 195370446 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 575030803) ^ 143757700 = 317122988 := by
        calc
          (7 : ZMod 575030803) ^ 143757700 = (7 : ZMod 575030803) ^ (71878850 + 71878850) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 71878850 * (7 : ZMod 575030803) ^ 71878850 := by rw [pow_add]
          _ = 317122988 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 575030803) ^ 287515401 = 575030802 := by
        calc
          (7 : ZMod 575030803) ^ 287515401 = (7 : ZMod 575030803) ^ (143757700 + 143757700 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 143757700 * (7 : ZMod 575030803) ^ 143757700) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 575030802 := by rw [factor_0_27]; decide
      change (7 : ZMod 575030803) ^ 287515401 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (7 : ZMod 575030803) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 575030803) ^ 2 = 49 := by
        calc
          (7 : ZMod 575030803) ^ 2 = (7 : ZMod 575030803) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 1 * (7 : ZMod 575030803) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 575030803) ^ 5 = 16807 := by
        calc
          (7 : ZMod 575030803) ^ 5 = (7 : ZMod 575030803) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 2 * (7 : ZMod 575030803) ^ 2) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 575030803) ^ 11 = 252234334 := by
        calc
          (7 : ZMod 575030803) ^ 11 = (7 : ZMod 575030803) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 5 * (7 : ZMod 575030803) ^ 5) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 252234334 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 575030803) ^ 22 = 214274838 := by
        calc
          (7 : ZMod 575030803) ^ 22 = (7 : ZMod 575030803) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 11 * (7 : ZMod 575030803) ^ 11 := by rw [pow_add]
          _ = 214274838 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 575030803) ^ 45 = 126355133 := by
        calc
          (7 : ZMod 575030803) ^ 45 = (7 : ZMod 575030803) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 22 * (7 : ZMod 575030803) ^ 22) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 126355133 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 575030803) ^ 91 = 297560464 := by
        calc
          (7 : ZMod 575030803) ^ 91 = (7 : ZMod 575030803) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 45 * (7 : ZMod 575030803) ^ 45) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 297560464 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 575030803) ^ 182 = 469260985 := by
        calc
          (7 : ZMod 575030803) ^ 182 = (7 : ZMod 575030803) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 91 * (7 : ZMod 575030803) ^ 91 := by rw [pow_add]
          _ = 469260985 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 575030803) ^ 365 = 430442970 := by
        calc
          (7 : ZMod 575030803) ^ 365 = (7 : ZMod 575030803) ^ (182 + 182 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 182 * (7 : ZMod 575030803) ^ 182) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 430442970 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 575030803) ^ 731 = 11279339 := by
        calc
          (7 : ZMod 575030803) ^ 731 = (7 : ZMod 575030803) ^ (365 + 365 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 365 * (7 : ZMod 575030803) ^ 365) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 11279339 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 575030803) ^ 1462 = 223236383 := by
        calc
          (7 : ZMod 575030803) ^ 1462 = (7 : ZMod 575030803) ^ (731 + 731) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 731 * (7 : ZMod 575030803) ^ 731 := by rw [pow_add]
          _ = 223236383 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 575030803) ^ 2924 = 533053023 := by
        calc
          (7 : ZMod 575030803) ^ 2924 = (7 : ZMod 575030803) ^ (1462 + 1462) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 1462 * (7 : ZMod 575030803) ^ 1462 := by rw [pow_add]
          _ = 533053023 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 575030803) ^ 5849 = 68502449 := by
        calc
          (7 : ZMod 575030803) ^ 5849 = (7 : ZMod 575030803) ^ (2924 + 2924 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 2924 * (7 : ZMod 575030803) ^ 2924) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 68502449 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 575030803) ^ 11699 = 515347406 := by
        calc
          (7 : ZMod 575030803) ^ 11699 = (7 : ZMod 575030803) ^ (5849 + 5849 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 5849 * (7 : ZMod 575030803) ^ 5849) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 515347406 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 575030803) ^ 23398 = 214025295 := by
        calc
          (7 : ZMod 575030803) ^ 23398 = (7 : ZMod 575030803) ^ (11699 + 11699) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 11699 * (7 : ZMod 575030803) ^ 11699 := by rw [pow_add]
          _ = 214025295 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 575030803) ^ 46796 = 214664488 := by
        calc
          (7 : ZMod 575030803) ^ 46796 = (7 : ZMod 575030803) ^ (23398 + 23398) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 23398 * (7 : ZMod 575030803) ^ 23398 := by rw [pow_add]
          _ = 214664488 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 575030803) ^ 93592 = 319791638 := by
        calc
          (7 : ZMod 575030803) ^ 93592 = (7 : ZMod 575030803) ^ (46796 + 46796) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 46796 * (7 : ZMod 575030803) ^ 46796 := by rw [pow_add]
          _ = 319791638 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 575030803) ^ 187184 = 457075880 := by
        calc
          (7 : ZMod 575030803) ^ 187184 = (7 : ZMod 575030803) ^ (93592 + 93592) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 93592 * (7 : ZMod 575030803) ^ 93592 := by rw [pow_add]
          _ = 457075880 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 575030803) ^ 374369 = 284392079 := by
        calc
          (7 : ZMod 575030803) ^ 374369 = (7 : ZMod 575030803) ^ (187184 + 187184 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 187184 * (7 : ZMod 575030803) ^ 187184) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 284392079 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 575030803) ^ 748738 = 464654615 := by
        calc
          (7 : ZMod 575030803) ^ 748738 = (7 : ZMod 575030803) ^ (374369 + 374369) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 374369 * (7 : ZMod 575030803) ^ 374369 := by rw [pow_add]
          _ = 464654615 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 575030803) ^ 1497476 = 118974178 := by
        calc
          (7 : ZMod 575030803) ^ 1497476 = (7 : ZMod 575030803) ^ (748738 + 748738) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 748738 * (7 : ZMod 575030803) ^ 748738 := by rw [pow_add]
          _ = 118974178 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 575030803) ^ 2994952 = 289672224 := by
        calc
          (7 : ZMod 575030803) ^ 2994952 = (7 : ZMod 575030803) ^ (1497476 + 1497476) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 1497476 * (7 : ZMod 575030803) ^ 1497476 := by rw [pow_add]
          _ = 289672224 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 575030803) ^ 5989904 = 27857937 := by
        calc
          (7 : ZMod 575030803) ^ 5989904 = (7 : ZMod 575030803) ^ (2994952 + 2994952) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 2994952 * (7 : ZMod 575030803) ^ 2994952 := by rw [pow_add]
          _ = 27857937 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 575030803) ^ 11979808 = 207013154 := by
        calc
          (7 : ZMod 575030803) ^ 11979808 = (7 : ZMod 575030803) ^ (5989904 + 5989904) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 5989904 * (7 : ZMod 575030803) ^ 5989904 := by rw [pow_add]
          _ = 207013154 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 575030803) ^ 23959616 = 470728882 := by
        calc
          (7 : ZMod 575030803) ^ 23959616 = (7 : ZMod 575030803) ^ (11979808 + 11979808) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 11979808 * (7 : ZMod 575030803) ^ 11979808 := by rw [pow_add]
          _ = 470728882 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 575030803) ^ 47919233 = 155226962 := by
        calc
          (7 : ZMod 575030803) ^ 47919233 = (7 : ZMod 575030803) ^ (23959616 + 23959616 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 23959616 * (7 : ZMod 575030803) ^ 23959616) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 155226962 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 575030803) ^ 95838467 = 320249781 := by
        calc
          (7 : ZMod 575030803) ^ 95838467 = (7 : ZMod 575030803) ^ (47919233 + 47919233 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 47919233 * (7 : ZMod 575030803) ^ 47919233) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 320249781 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 575030803) ^ 191676934 = 320249780 := by
        calc
          (7 : ZMod 575030803) ^ 191676934 = (7 : ZMod 575030803) ^ (95838467 + 95838467) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 95838467 * (7 : ZMod 575030803) ^ 95838467 := by rw [pow_add]
          _ = 320249780 := by rw [factor_1_26]; decide
      change (7 : ZMod 575030803) ^ 191676934 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (7 : ZMod 575030803) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 575030803) ^ 3 = 343 := by
        calc
          (7 : ZMod 575030803) ^ 3 = (7 : ZMod 575030803) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = ((7 : ZMod 575030803) ^ 1 * (7 : ZMod 575030803) ^ 1) * (7 : ZMod 575030803) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 575030803) ^ 6 = 117649 := by
        calc
          (7 : ZMod 575030803) ^ 6 = (7 : ZMod 575030803) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 575030803) ^ n) (by norm_num)
          _ = (7 : ZMod 575030803) ^ 3 * (7 : ZMod 575030803) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_2_1]; decide
      change (7 : ZMod 575030803) ^ 6 ≠ 1
      rw [factor_2_2]
      decide

#print axioms prime_lucas_575030803

end TotientTailPeriodKiller
end Erdos249257
