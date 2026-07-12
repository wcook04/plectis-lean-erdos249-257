import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_68502634201 : Nat.Prime 68502634201 := by
  apply lucas_primality 68502634201 (17 : ZMod 68502634201)
  ·
      have fermat_0 : (17 : ZMod 68502634201) ^ 1 = 17 := by norm_num
      have fermat_1 : (17 : ZMod 68502634201) ^ 3 = 4913 := by
        calc
          (17 : ZMod 68502634201) ^ 3 = (17 : ZMod 68502634201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 1 * (17 : ZMod 68502634201) ^ 1) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 4913 := by rw [fermat_0]; decide
      have fermat_2 : (17 : ZMod 68502634201) ^ 7 = 410338673 := by
        calc
          (17 : ZMod 68502634201) ^ 7 = (17 : ZMod 68502634201) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 3 * (17 : ZMod 68502634201) ^ 3) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 410338673 := by rw [fermat_1]; decide
      have fermat_3 : (17 : ZMod 68502634201) ^ 15 = 64866852203 := by
        calc
          (17 : ZMod 68502634201) ^ 15 = (17 : ZMod 68502634201) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 7 * (17 : ZMod 68502634201) ^ 7) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 64866852203 := by rw [fermat_2]; decide
      have fermat_4 : (17 : ZMod 68502634201) ^ 31 = 62977204437 := by
        calc
          (17 : ZMod 68502634201) ^ 31 = (17 : ZMod 68502634201) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 15 * (17 : ZMod 68502634201) ^ 15) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 62977204437 := by rw [fermat_3]; decide
      have fermat_5 : (17 : ZMod 68502634201) ^ 63 = 20833413836 := by
        calc
          (17 : ZMod 68502634201) ^ 63 = (17 : ZMod 68502634201) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 31 * (17 : ZMod 68502634201) ^ 31) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 20833413836 := by rw [fermat_4]; decide
      have fermat_6 : (17 : ZMod 68502634201) ^ 127 = 33652154133 := by
        calc
          (17 : ZMod 68502634201) ^ 127 = (17 : ZMod 68502634201) ^ (63 + 63 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 63 * (17 : ZMod 68502634201) ^ 63) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 33652154133 := by rw [fermat_5]; decide
      have fermat_7 : (17 : ZMod 68502634201) ^ 255 = 32093222670 := by
        calc
          (17 : ZMod 68502634201) ^ 255 = (17 : ZMod 68502634201) ^ (127 + 127 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 127 * (17 : ZMod 68502634201) ^ 127) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 32093222670 := by rw [fermat_6]; decide
      have fermat_8 : (17 : ZMod 68502634201) ^ 510 = 5716056369 := by
        calc
          (17 : ZMod 68502634201) ^ 510 = (17 : ZMod 68502634201) ^ (255 + 255) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 255 * (17 : ZMod 68502634201) ^ 255 := by rw [pow_add]
          _ = 5716056369 := by rw [fermat_7]; decide
      have fermat_9 : (17 : ZMod 68502634201) ^ 1020 = 61657741016 := by
        calc
          (17 : ZMod 68502634201) ^ 1020 = (17 : ZMod 68502634201) ^ (510 + 510) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 510 * (17 : ZMod 68502634201) ^ 510 := by rw [pow_add]
          _ = 61657741016 := by rw [fermat_8]; decide
      have fermat_10 : (17 : ZMod 68502634201) ^ 2041 = 53729707454 := by
        calc
          (17 : ZMod 68502634201) ^ 2041 = (17 : ZMod 68502634201) ^ (1020 + 1020 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 1020 * (17 : ZMod 68502634201) ^ 1020) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 53729707454 := by rw [fermat_9]; decide
      have fermat_11 : (17 : ZMod 68502634201) ^ 4083 = 50231324532 := by
        calc
          (17 : ZMod 68502634201) ^ 4083 = (17 : ZMod 68502634201) ^ (2041 + 2041 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 2041 * (17 : ZMod 68502634201) ^ 2041) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 50231324532 := by rw [fermat_10]; decide
      have fermat_12 : (17 : ZMod 68502634201) ^ 8166 = 50591376477 := by
        calc
          (17 : ZMod 68502634201) ^ 8166 = (17 : ZMod 68502634201) ^ (4083 + 4083) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 4083 * (17 : ZMod 68502634201) ^ 4083 := by rw [pow_add]
          _ = 50591376477 := by rw [fermat_11]; decide
      have fermat_13 : (17 : ZMod 68502634201) ^ 16332 = 34756682375 := by
        calc
          (17 : ZMod 68502634201) ^ 16332 = (17 : ZMod 68502634201) ^ (8166 + 8166) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 8166 * (17 : ZMod 68502634201) ^ 8166 := by rw [pow_add]
          _ = 34756682375 := by rw [fermat_12]; decide
      have fermat_14 : (17 : ZMod 68502634201) ^ 32664 = 56621802364 := by
        calc
          (17 : ZMod 68502634201) ^ 32664 = (17 : ZMod 68502634201) ^ (16332 + 16332) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 16332 * (17 : ZMod 68502634201) ^ 16332 := by rw [pow_add]
          _ = 56621802364 := by rw [fermat_13]; decide
      have fermat_15 : (17 : ZMod 68502634201) ^ 65329 = 36036432063 := by
        calc
          (17 : ZMod 68502634201) ^ 65329 = (17 : ZMod 68502634201) ^ (32664 + 32664 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 32664 * (17 : ZMod 68502634201) ^ 32664) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 36036432063 := by rw [fermat_14]; decide
      have fermat_16 : (17 : ZMod 68502634201) ^ 130658 = 7305088220 := by
        calc
          (17 : ZMod 68502634201) ^ 130658 = (17 : ZMod 68502634201) ^ (65329 + 65329) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 65329 * (17 : ZMod 68502634201) ^ 65329 := by rw [pow_add]
          _ = 7305088220 := by rw [fermat_15]; decide
      have fermat_17 : (17 : ZMod 68502634201) ^ 261316 = 41608819079 := by
        calc
          (17 : ZMod 68502634201) ^ 261316 = (17 : ZMod 68502634201) ^ (130658 + 130658) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 130658 * (17 : ZMod 68502634201) ^ 130658 := by rw [pow_add]
          _ = 41608819079 := by rw [fermat_16]; decide
      have fermat_18 : (17 : ZMod 68502634201) ^ 522633 = 55279616422 := by
        calc
          (17 : ZMod 68502634201) ^ 522633 = (17 : ZMod 68502634201) ^ (261316 + 261316 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 261316 * (17 : ZMod 68502634201) ^ 261316) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 55279616422 := by rw [fermat_17]; decide
      have fermat_19 : (17 : ZMod 68502634201) ^ 1045267 = 54113306393 := by
        calc
          (17 : ZMod 68502634201) ^ 1045267 = (17 : ZMod 68502634201) ^ (522633 + 522633 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 522633 * (17 : ZMod 68502634201) ^ 522633) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 54113306393 := by rw [fermat_18]; decide
      have fermat_20 : (17 : ZMod 68502634201) ^ 2090534 = 5821343345 := by
        calc
          (17 : ZMod 68502634201) ^ 2090534 = (17 : ZMod 68502634201) ^ (1045267 + 1045267) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1045267 * (17 : ZMod 68502634201) ^ 1045267 := by rw [pow_add]
          _ = 5821343345 := by rw [fermat_19]; decide
      have fermat_21 : (17 : ZMod 68502634201) ^ 4181068 = 25401943361 := by
        calc
          (17 : ZMod 68502634201) ^ 4181068 = (17 : ZMod 68502634201) ^ (2090534 + 2090534) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 2090534 * (17 : ZMod 68502634201) ^ 2090534 := by rw [pow_add]
          _ = 25401943361 := by rw [fermat_20]; decide
      have fermat_22 : (17 : ZMod 68502634201) ^ 8362137 = 20202274574 := by
        calc
          (17 : ZMod 68502634201) ^ 8362137 = (17 : ZMod 68502634201) ^ (4181068 + 4181068 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 4181068 * (17 : ZMod 68502634201) ^ 4181068) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 20202274574 := by rw [fermat_21]; decide
      have fermat_23 : (17 : ZMod 68502634201) ^ 16724275 = 58958298777 := by
        calc
          (17 : ZMod 68502634201) ^ 16724275 = (17 : ZMod 68502634201) ^ (8362137 + 8362137 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 8362137 * (17 : ZMod 68502634201) ^ 8362137) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 58958298777 := by rw [fermat_22]; decide
      have fermat_24 : (17 : ZMod 68502634201) ^ 33448551 = 67142187010 := by
        calc
          (17 : ZMod 68502634201) ^ 33448551 = (17 : ZMod 68502634201) ^ (16724275 + 16724275 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 16724275 * (17 : ZMod 68502634201) ^ 16724275) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 67142187010 := by rw [fermat_23]; decide
      have fermat_25 : (17 : ZMod 68502634201) ^ 66897103 = 30074398303 := by
        calc
          (17 : ZMod 68502634201) ^ 66897103 = (17 : ZMod 68502634201) ^ (33448551 + 33448551 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 33448551 * (17 : ZMod 68502634201) ^ 33448551) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 30074398303 := by rw [fermat_24]; decide
      have fermat_26 : (17 : ZMod 68502634201) ^ 133794207 = 6211984949 := by
        calc
          (17 : ZMod 68502634201) ^ 133794207 = (17 : ZMod 68502634201) ^ (66897103 + 66897103 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 66897103 * (17 : ZMod 68502634201) ^ 66897103) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 6211984949 := by rw [fermat_25]; decide
      have fermat_27 : (17 : ZMod 68502634201) ^ 267588414 = 46645573746 := by
        calc
          (17 : ZMod 68502634201) ^ 267588414 = (17 : ZMod 68502634201) ^ (133794207 + 133794207) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 133794207 * (17 : ZMod 68502634201) ^ 133794207 := by rw [pow_add]
          _ = 46645573746 := by rw [fermat_26]; decide
      have fermat_28 : (17 : ZMod 68502634201) ^ 535176829 = 15581185303 := by
        calc
          (17 : ZMod 68502634201) ^ 535176829 = (17 : ZMod 68502634201) ^ (267588414 + 267588414 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 267588414 * (17 : ZMod 68502634201) ^ 267588414) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 15581185303 := by rw [fermat_27]; decide
      have fermat_29 : (17 : ZMod 68502634201) ^ 1070353659 = 55954432994 := by
        calc
          (17 : ZMod 68502634201) ^ 1070353659 = (17 : ZMod 68502634201) ^ (535176829 + 535176829 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 535176829 * (17 : ZMod 68502634201) ^ 535176829) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 55954432994 := by rw [fermat_28]; decide
      have fermat_30 : (17 : ZMod 68502634201) ^ 2140707318 = 40665940945 := by
        calc
          (17 : ZMod 68502634201) ^ 2140707318 = (17 : ZMod 68502634201) ^ (1070353659 + 1070353659) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1070353659 * (17 : ZMod 68502634201) ^ 1070353659 := by rw [pow_add]
          _ = 40665940945 := by rw [fermat_29]; decide
      have fermat_31 : (17 : ZMod 68502634201) ^ 4281414637 = 31535384326 := by
        calc
          (17 : ZMod 68502634201) ^ 4281414637 = (17 : ZMod 68502634201) ^ (2140707318 + 2140707318 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 2140707318 * (17 : ZMod 68502634201) ^ 2140707318) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 31535384326 := by rw [fermat_30]; decide
      have fermat_32 : (17 : ZMod 68502634201) ^ 8562829275 = 36249981175 := by
        calc
          (17 : ZMod 68502634201) ^ 8562829275 = (17 : ZMod 68502634201) ^ (4281414637 + 4281414637 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 4281414637 * (17 : ZMod 68502634201) ^ 4281414637) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 36249981175 := by rw [fermat_31]; decide
      have fermat_33 : (17 : ZMod 68502634201) ^ 17125658550 = 44450660467 := by
        calc
          (17 : ZMod 68502634201) ^ 17125658550 = (17 : ZMod 68502634201) ^ (8562829275 + 8562829275) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 8562829275 * (17 : ZMod 68502634201) ^ 8562829275 := by rw [pow_add]
          _ = 44450660467 := by rw [fermat_32]; decide
      have fermat_34 : (17 : ZMod 68502634201) ^ 34251317100 = 68502634200 := by
        calc
          (17 : ZMod 68502634201) ^ 34251317100 = (17 : ZMod 68502634201) ^ (17125658550 + 17125658550) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 17125658550 * (17 : ZMod 68502634201) ^ 17125658550 := by rw [pow_add]
          _ = 68502634200 := by rw [fermat_33]; decide
      have fermat_35 : (17 : ZMod 68502634201) ^ 68502634200 = 1 := by
        calc
          (17 : ZMod 68502634201) ^ 68502634200 = (17 : ZMod 68502634201) ^ (34251317100 + 34251317100) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 34251317100 * (17 : ZMod 68502634201) ^ 34251317100 := by rw [pow_add]
          _ = 1 := by rw [fermat_34]; decide
      simpa using fermat_35
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod = 68502634201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (17 : ZMod 68502634201) ^ 1 = 17 := by norm_num
      have factor_0_1 : (17 : ZMod 68502634201) ^ 3 = 4913 := by
        calc
          (17 : ZMod 68502634201) ^ 3 = (17 : ZMod 68502634201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 1 * (17 : ZMod 68502634201) ^ 1) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 4913 := by rw [factor_0_0]; decide
      have factor_0_2 : (17 : ZMod 68502634201) ^ 7 = 410338673 := by
        calc
          (17 : ZMod 68502634201) ^ 7 = (17 : ZMod 68502634201) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 3 * (17 : ZMod 68502634201) ^ 3) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 410338673 := by rw [factor_0_1]; decide
      have factor_0_3 : (17 : ZMod 68502634201) ^ 15 = 64866852203 := by
        calc
          (17 : ZMod 68502634201) ^ 15 = (17 : ZMod 68502634201) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 7 * (17 : ZMod 68502634201) ^ 7) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 64866852203 := by rw [factor_0_2]; decide
      have factor_0_4 : (17 : ZMod 68502634201) ^ 31 = 62977204437 := by
        calc
          (17 : ZMod 68502634201) ^ 31 = (17 : ZMod 68502634201) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 15 * (17 : ZMod 68502634201) ^ 15) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 62977204437 := by rw [factor_0_3]; decide
      have factor_0_5 : (17 : ZMod 68502634201) ^ 63 = 20833413836 := by
        calc
          (17 : ZMod 68502634201) ^ 63 = (17 : ZMod 68502634201) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 31 * (17 : ZMod 68502634201) ^ 31) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 20833413836 := by rw [factor_0_4]; decide
      have factor_0_6 : (17 : ZMod 68502634201) ^ 127 = 33652154133 := by
        calc
          (17 : ZMod 68502634201) ^ 127 = (17 : ZMod 68502634201) ^ (63 + 63 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 63 * (17 : ZMod 68502634201) ^ 63) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 33652154133 := by rw [factor_0_5]; decide
      have factor_0_7 : (17 : ZMod 68502634201) ^ 255 = 32093222670 := by
        calc
          (17 : ZMod 68502634201) ^ 255 = (17 : ZMod 68502634201) ^ (127 + 127 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 127 * (17 : ZMod 68502634201) ^ 127) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 32093222670 := by rw [factor_0_6]; decide
      have factor_0_8 : (17 : ZMod 68502634201) ^ 510 = 5716056369 := by
        calc
          (17 : ZMod 68502634201) ^ 510 = (17 : ZMod 68502634201) ^ (255 + 255) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 255 * (17 : ZMod 68502634201) ^ 255 := by rw [pow_add]
          _ = 5716056369 := by rw [factor_0_7]; decide
      have factor_0_9 : (17 : ZMod 68502634201) ^ 1020 = 61657741016 := by
        calc
          (17 : ZMod 68502634201) ^ 1020 = (17 : ZMod 68502634201) ^ (510 + 510) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 510 * (17 : ZMod 68502634201) ^ 510 := by rw [pow_add]
          _ = 61657741016 := by rw [factor_0_8]; decide
      have factor_0_10 : (17 : ZMod 68502634201) ^ 2041 = 53729707454 := by
        calc
          (17 : ZMod 68502634201) ^ 2041 = (17 : ZMod 68502634201) ^ (1020 + 1020 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 1020 * (17 : ZMod 68502634201) ^ 1020) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 53729707454 := by rw [factor_0_9]; decide
      have factor_0_11 : (17 : ZMod 68502634201) ^ 4083 = 50231324532 := by
        calc
          (17 : ZMod 68502634201) ^ 4083 = (17 : ZMod 68502634201) ^ (2041 + 2041 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 2041 * (17 : ZMod 68502634201) ^ 2041) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 50231324532 := by rw [factor_0_10]; decide
      have factor_0_12 : (17 : ZMod 68502634201) ^ 8166 = 50591376477 := by
        calc
          (17 : ZMod 68502634201) ^ 8166 = (17 : ZMod 68502634201) ^ (4083 + 4083) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 4083 * (17 : ZMod 68502634201) ^ 4083 := by rw [pow_add]
          _ = 50591376477 := by rw [factor_0_11]; decide
      have factor_0_13 : (17 : ZMod 68502634201) ^ 16332 = 34756682375 := by
        calc
          (17 : ZMod 68502634201) ^ 16332 = (17 : ZMod 68502634201) ^ (8166 + 8166) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 8166 * (17 : ZMod 68502634201) ^ 8166 := by rw [pow_add]
          _ = 34756682375 := by rw [factor_0_12]; decide
      have factor_0_14 : (17 : ZMod 68502634201) ^ 32664 = 56621802364 := by
        calc
          (17 : ZMod 68502634201) ^ 32664 = (17 : ZMod 68502634201) ^ (16332 + 16332) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 16332 * (17 : ZMod 68502634201) ^ 16332 := by rw [pow_add]
          _ = 56621802364 := by rw [factor_0_13]; decide
      have factor_0_15 : (17 : ZMod 68502634201) ^ 65329 = 36036432063 := by
        calc
          (17 : ZMod 68502634201) ^ 65329 = (17 : ZMod 68502634201) ^ (32664 + 32664 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 32664 * (17 : ZMod 68502634201) ^ 32664) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 36036432063 := by rw [factor_0_14]; decide
      have factor_0_16 : (17 : ZMod 68502634201) ^ 130658 = 7305088220 := by
        calc
          (17 : ZMod 68502634201) ^ 130658 = (17 : ZMod 68502634201) ^ (65329 + 65329) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 65329 * (17 : ZMod 68502634201) ^ 65329 := by rw [pow_add]
          _ = 7305088220 := by rw [factor_0_15]; decide
      have factor_0_17 : (17 : ZMod 68502634201) ^ 261316 = 41608819079 := by
        calc
          (17 : ZMod 68502634201) ^ 261316 = (17 : ZMod 68502634201) ^ (130658 + 130658) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 130658 * (17 : ZMod 68502634201) ^ 130658 := by rw [pow_add]
          _ = 41608819079 := by rw [factor_0_16]; decide
      have factor_0_18 : (17 : ZMod 68502634201) ^ 522633 = 55279616422 := by
        calc
          (17 : ZMod 68502634201) ^ 522633 = (17 : ZMod 68502634201) ^ (261316 + 261316 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 261316 * (17 : ZMod 68502634201) ^ 261316) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 55279616422 := by rw [factor_0_17]; decide
      have factor_0_19 : (17 : ZMod 68502634201) ^ 1045267 = 54113306393 := by
        calc
          (17 : ZMod 68502634201) ^ 1045267 = (17 : ZMod 68502634201) ^ (522633 + 522633 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 522633 * (17 : ZMod 68502634201) ^ 522633) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 54113306393 := by rw [factor_0_18]; decide
      have factor_0_20 : (17 : ZMod 68502634201) ^ 2090534 = 5821343345 := by
        calc
          (17 : ZMod 68502634201) ^ 2090534 = (17 : ZMod 68502634201) ^ (1045267 + 1045267) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1045267 * (17 : ZMod 68502634201) ^ 1045267 := by rw [pow_add]
          _ = 5821343345 := by rw [factor_0_19]; decide
      have factor_0_21 : (17 : ZMod 68502634201) ^ 4181068 = 25401943361 := by
        calc
          (17 : ZMod 68502634201) ^ 4181068 = (17 : ZMod 68502634201) ^ (2090534 + 2090534) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 2090534 * (17 : ZMod 68502634201) ^ 2090534 := by rw [pow_add]
          _ = 25401943361 := by rw [factor_0_20]; decide
      have factor_0_22 : (17 : ZMod 68502634201) ^ 8362137 = 20202274574 := by
        calc
          (17 : ZMod 68502634201) ^ 8362137 = (17 : ZMod 68502634201) ^ (4181068 + 4181068 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 4181068 * (17 : ZMod 68502634201) ^ 4181068) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 20202274574 := by rw [factor_0_21]; decide
      have factor_0_23 : (17 : ZMod 68502634201) ^ 16724275 = 58958298777 := by
        calc
          (17 : ZMod 68502634201) ^ 16724275 = (17 : ZMod 68502634201) ^ (8362137 + 8362137 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 8362137 * (17 : ZMod 68502634201) ^ 8362137) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 58958298777 := by rw [factor_0_22]; decide
      have factor_0_24 : (17 : ZMod 68502634201) ^ 33448551 = 67142187010 := by
        calc
          (17 : ZMod 68502634201) ^ 33448551 = (17 : ZMod 68502634201) ^ (16724275 + 16724275 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 16724275 * (17 : ZMod 68502634201) ^ 16724275) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 67142187010 := by rw [factor_0_23]; decide
      have factor_0_25 : (17 : ZMod 68502634201) ^ 66897103 = 30074398303 := by
        calc
          (17 : ZMod 68502634201) ^ 66897103 = (17 : ZMod 68502634201) ^ (33448551 + 33448551 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 33448551 * (17 : ZMod 68502634201) ^ 33448551) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 30074398303 := by rw [factor_0_24]; decide
      have factor_0_26 : (17 : ZMod 68502634201) ^ 133794207 = 6211984949 := by
        calc
          (17 : ZMod 68502634201) ^ 133794207 = (17 : ZMod 68502634201) ^ (66897103 + 66897103 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 66897103 * (17 : ZMod 68502634201) ^ 66897103) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 6211984949 := by rw [factor_0_25]; decide
      have factor_0_27 : (17 : ZMod 68502634201) ^ 267588414 = 46645573746 := by
        calc
          (17 : ZMod 68502634201) ^ 267588414 = (17 : ZMod 68502634201) ^ (133794207 + 133794207) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 133794207 * (17 : ZMod 68502634201) ^ 133794207 := by rw [pow_add]
          _ = 46645573746 := by rw [factor_0_26]; decide
      have factor_0_28 : (17 : ZMod 68502634201) ^ 535176829 = 15581185303 := by
        calc
          (17 : ZMod 68502634201) ^ 535176829 = (17 : ZMod 68502634201) ^ (267588414 + 267588414 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 267588414 * (17 : ZMod 68502634201) ^ 267588414) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 15581185303 := by rw [factor_0_27]; decide
      have factor_0_29 : (17 : ZMod 68502634201) ^ 1070353659 = 55954432994 := by
        calc
          (17 : ZMod 68502634201) ^ 1070353659 = (17 : ZMod 68502634201) ^ (535176829 + 535176829 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 535176829 * (17 : ZMod 68502634201) ^ 535176829) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 55954432994 := by rw [factor_0_28]; decide
      have factor_0_30 : (17 : ZMod 68502634201) ^ 2140707318 = 40665940945 := by
        calc
          (17 : ZMod 68502634201) ^ 2140707318 = (17 : ZMod 68502634201) ^ (1070353659 + 1070353659) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1070353659 * (17 : ZMod 68502634201) ^ 1070353659 := by rw [pow_add]
          _ = 40665940945 := by rw [factor_0_29]; decide
      have factor_0_31 : (17 : ZMod 68502634201) ^ 4281414637 = 31535384326 := by
        calc
          (17 : ZMod 68502634201) ^ 4281414637 = (17 : ZMod 68502634201) ^ (2140707318 + 2140707318 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 2140707318 * (17 : ZMod 68502634201) ^ 2140707318) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 31535384326 := by rw [factor_0_30]; decide
      have factor_0_32 : (17 : ZMod 68502634201) ^ 8562829275 = 36249981175 := by
        calc
          (17 : ZMod 68502634201) ^ 8562829275 = (17 : ZMod 68502634201) ^ (4281414637 + 4281414637 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 4281414637 * (17 : ZMod 68502634201) ^ 4281414637) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 36249981175 := by rw [factor_0_31]; decide
      have factor_0_33 : (17 : ZMod 68502634201) ^ 17125658550 = 44450660467 := by
        calc
          (17 : ZMod 68502634201) ^ 17125658550 = (17 : ZMod 68502634201) ^ (8562829275 + 8562829275) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 8562829275 * (17 : ZMod 68502634201) ^ 8562829275 := by rw [pow_add]
          _ = 44450660467 := by rw [factor_0_32]; decide
      have factor_0_34 : (17 : ZMod 68502634201) ^ 34251317100 = 68502634200 := by
        calc
          (17 : ZMod 68502634201) ^ 34251317100 = (17 : ZMod 68502634201) ^ (17125658550 + 17125658550) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 17125658550 * (17 : ZMod 68502634201) ^ 17125658550 := by rw [pow_add]
          _ = 68502634200 := by rw [factor_0_33]; decide
      change (17 : ZMod 68502634201) ^ 34251317100 ≠ 1
      rw [factor_0_34]
      decide
    ·
      have factor_1_0 : (17 : ZMod 68502634201) ^ 1 = 17 := by norm_num
      have factor_1_1 : (17 : ZMod 68502634201) ^ 2 = 289 := by
        calc
          (17 : ZMod 68502634201) ^ 2 = (17 : ZMod 68502634201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1 * (17 : ZMod 68502634201) ^ 1 := by rw [pow_add]
          _ = 289 := by rw [factor_1_0]; decide
      have factor_1_2 : (17 : ZMod 68502634201) ^ 5 = 1419857 := by
        calc
          (17 : ZMod 68502634201) ^ 5 = (17 : ZMod 68502634201) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 2 * (17 : ZMod 68502634201) ^ 2) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 1419857 := by rw [factor_1_1]; decide
      have factor_1_3 : (17 : ZMod 68502634201) ^ 10 = 29417508620 := by
        calc
          (17 : ZMod 68502634201) ^ 10 = (17 : ZMod 68502634201) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 5 * (17 : ZMod 68502634201) ^ 5 := by rw [pow_add]
          _ = 29417508620 := by rw [factor_1_2]; decide
      have factor_1_4 : (17 : ZMod 68502634201) ^ 21 = 59839755042 := by
        calc
          (17 : ZMod 68502634201) ^ 21 = (17 : ZMod 68502634201) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 10 * (17 : ZMod 68502634201) ^ 10) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 59839755042 := by rw [factor_1_3]; decide
      have factor_1_5 : (17 : ZMod 68502634201) ^ 42 = 56458914026 := by
        calc
          (17 : ZMod 68502634201) ^ 42 = (17 : ZMod 68502634201) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 21 * (17 : ZMod 68502634201) ^ 21 := by rw [pow_add]
          _ = 56458914026 := by rw [factor_1_4]; decide
      have factor_1_6 : (17 : ZMod 68502634201) ^ 85 = 67059410347 := by
        calc
          (17 : ZMod 68502634201) ^ 85 = (17 : ZMod 68502634201) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 42 * (17 : ZMod 68502634201) ^ 42) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 67059410347 := by rw [factor_1_5]; decide
      have factor_1_7 : (17 : ZMod 68502634201) ^ 170 = 24086223658 := by
        calc
          (17 : ZMod 68502634201) ^ 170 = (17 : ZMod 68502634201) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 85 * (17 : ZMod 68502634201) ^ 85 := by rw [pow_add]
          _ = 24086223658 := by rw [factor_1_6]; decide
      have factor_1_8 : (17 : ZMod 68502634201) ^ 340 = 50409860288 := by
        calc
          (17 : ZMod 68502634201) ^ 340 = (17 : ZMod 68502634201) ^ (170 + 170) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 170 * (17 : ZMod 68502634201) ^ 170 := by rw [pow_add]
          _ = 50409860288 := by rw [factor_1_7]; decide
      have factor_1_9 : (17 : ZMod 68502634201) ^ 680 = 33085018584 := by
        calc
          (17 : ZMod 68502634201) ^ 680 = (17 : ZMod 68502634201) ^ (340 + 340) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 340 * (17 : ZMod 68502634201) ^ 340 := by rw [pow_add]
          _ = 33085018584 := by rw [factor_1_8]; decide
      have factor_1_10 : (17 : ZMod 68502634201) ^ 1361 = 48803772115 := by
        calc
          (17 : ZMod 68502634201) ^ 1361 = (17 : ZMod 68502634201) ^ (680 + 680 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 680 * (17 : ZMod 68502634201) ^ 680) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 48803772115 := by rw [factor_1_9]; decide
      have factor_1_11 : (17 : ZMod 68502634201) ^ 2722 = 7387760678 := by
        calc
          (17 : ZMod 68502634201) ^ 2722 = (17 : ZMod 68502634201) ^ (1361 + 1361) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1361 * (17 : ZMod 68502634201) ^ 1361 := by rw [pow_add]
          _ = 7387760678 := by rw [factor_1_10]; decide
      have factor_1_12 : (17 : ZMod 68502634201) ^ 5444 = 59176739087 := by
        calc
          (17 : ZMod 68502634201) ^ 5444 = (17 : ZMod 68502634201) ^ (2722 + 2722) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 2722 * (17 : ZMod 68502634201) ^ 2722 := by rw [pow_add]
          _ = 59176739087 := by rw [factor_1_11]; decide
      have factor_1_13 : (17 : ZMod 68502634201) ^ 10888 = 36855253720 := by
        calc
          (17 : ZMod 68502634201) ^ 10888 = (17 : ZMod 68502634201) ^ (5444 + 5444) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 5444 * (17 : ZMod 68502634201) ^ 5444 := by rw [pow_add]
          _ = 36855253720 := by rw [factor_1_12]; decide
      have factor_1_14 : (17 : ZMod 68502634201) ^ 21776 = 17873544041 := by
        calc
          (17 : ZMod 68502634201) ^ 21776 = (17 : ZMod 68502634201) ^ (10888 + 10888) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 10888 * (17 : ZMod 68502634201) ^ 10888 := by rw [pow_add]
          _ = 17873544041 := by rw [factor_1_13]; decide
      have factor_1_15 : (17 : ZMod 68502634201) ^ 43552 = 63409879372 := by
        calc
          (17 : ZMod 68502634201) ^ 43552 = (17 : ZMod 68502634201) ^ (21776 + 21776) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 21776 * (17 : ZMod 68502634201) ^ 21776 := by rw [pow_add]
          _ = 63409879372 := by rw [factor_1_14]; decide
      have factor_1_16 : (17 : ZMod 68502634201) ^ 87105 = 49867180422 := by
        calc
          (17 : ZMod 68502634201) ^ 87105 = (17 : ZMod 68502634201) ^ (43552 + 43552 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 43552 * (17 : ZMod 68502634201) ^ 43552) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 49867180422 := by rw [factor_1_15]; decide
      have factor_1_17 : (17 : ZMod 68502634201) ^ 174211 = 18003451198 := by
        calc
          (17 : ZMod 68502634201) ^ 174211 = (17 : ZMod 68502634201) ^ (87105 + 87105 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 87105 * (17 : ZMod 68502634201) ^ 87105) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 18003451198 := by rw [factor_1_16]; decide
      have factor_1_18 : (17 : ZMod 68502634201) ^ 348422 = 3831447209 := by
        calc
          (17 : ZMod 68502634201) ^ 348422 = (17 : ZMod 68502634201) ^ (174211 + 174211) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 174211 * (17 : ZMod 68502634201) ^ 174211 := by rw [pow_add]
          _ = 3831447209 := by rw [factor_1_17]; decide
      have factor_1_19 : (17 : ZMod 68502634201) ^ 696844 = 4455495732 := by
        calc
          (17 : ZMod 68502634201) ^ 696844 = (17 : ZMod 68502634201) ^ (348422 + 348422) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 348422 * (17 : ZMod 68502634201) ^ 348422 := by rw [pow_add]
          _ = 4455495732 := by rw [factor_1_18]; decide
      have factor_1_20 : (17 : ZMod 68502634201) ^ 1393689 = 4219689962 := by
        calc
          (17 : ZMod 68502634201) ^ 1393689 = (17 : ZMod 68502634201) ^ (696844 + 696844 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 696844 * (17 : ZMod 68502634201) ^ 696844) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 4219689962 := by rw [factor_1_19]; decide
      have factor_1_21 : (17 : ZMod 68502634201) ^ 2787379 = 64153664737 := by
        calc
          (17 : ZMod 68502634201) ^ 2787379 = (17 : ZMod 68502634201) ^ (1393689 + 1393689 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 1393689 * (17 : ZMod 68502634201) ^ 1393689) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 64153664737 := by rw [factor_1_20]; decide
      have factor_1_22 : (17 : ZMod 68502634201) ^ 5574758 = 19520478308 := by
        calc
          (17 : ZMod 68502634201) ^ 5574758 = (17 : ZMod 68502634201) ^ (2787379 + 2787379) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 2787379 * (17 : ZMod 68502634201) ^ 2787379 := by rw [pow_add]
          _ = 19520478308 := by rw [factor_1_21]; decide
      have factor_1_23 : (17 : ZMod 68502634201) ^ 11149517 = 29415379647 := by
        calc
          (17 : ZMod 68502634201) ^ 11149517 = (17 : ZMod 68502634201) ^ (5574758 + 5574758 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 5574758 * (17 : ZMod 68502634201) ^ 5574758) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 29415379647 := by rw [factor_1_22]; decide
      have factor_1_24 : (17 : ZMod 68502634201) ^ 22299034 = 10362777532 := by
        calc
          (17 : ZMod 68502634201) ^ 22299034 = (17 : ZMod 68502634201) ^ (11149517 + 11149517) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 11149517 * (17 : ZMod 68502634201) ^ 11149517 := by rw [pow_add]
          _ = 10362777532 := by rw [factor_1_23]; decide
      have factor_1_25 : (17 : ZMod 68502634201) ^ 44598069 = 51767505663 := by
        calc
          (17 : ZMod 68502634201) ^ 44598069 = (17 : ZMod 68502634201) ^ (22299034 + 22299034 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 22299034 * (17 : ZMod 68502634201) ^ 22299034) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 51767505663 := by rw [factor_1_24]; decide
      have factor_1_26 : (17 : ZMod 68502634201) ^ 89196138 = 3673854821 := by
        calc
          (17 : ZMod 68502634201) ^ 89196138 = (17 : ZMod 68502634201) ^ (44598069 + 44598069) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 44598069 * (17 : ZMod 68502634201) ^ 44598069 := by rw [pow_add]
          _ = 3673854821 := by rw [factor_1_25]; decide
      have factor_1_27 : (17 : ZMod 68502634201) ^ 178392276 = 4961999267 := by
        calc
          (17 : ZMod 68502634201) ^ 178392276 = (17 : ZMod 68502634201) ^ (89196138 + 89196138) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 89196138 * (17 : ZMod 68502634201) ^ 89196138 := by rw [pow_add]
          _ = 4961999267 := by rw [factor_1_26]; decide
      have factor_1_28 : (17 : ZMod 68502634201) ^ 356784553 = 57869669132 := by
        calc
          (17 : ZMod 68502634201) ^ 356784553 = (17 : ZMod 68502634201) ^ (178392276 + 178392276 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 178392276 * (17 : ZMod 68502634201) ^ 178392276) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 57869669132 := by rw [factor_1_27]; decide
      have factor_1_29 : (17 : ZMod 68502634201) ^ 713569106 = 11242393267 := by
        calc
          (17 : ZMod 68502634201) ^ 713569106 = (17 : ZMod 68502634201) ^ (356784553 + 356784553) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 356784553 * (17 : ZMod 68502634201) ^ 356784553 := by rw [pow_add]
          _ = 11242393267 := by rw [factor_1_28]; decide
      have factor_1_30 : (17 : ZMod 68502634201) ^ 1427138212 = 23947582822 := by
        calc
          (17 : ZMod 68502634201) ^ 1427138212 = (17 : ZMod 68502634201) ^ (713569106 + 713569106) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 713569106 * (17 : ZMod 68502634201) ^ 713569106 := by rw [pow_add]
          _ = 23947582822 := by rw [factor_1_29]; decide
      have factor_1_31 : (17 : ZMod 68502634201) ^ 2854276425 = 58991617267 := by
        calc
          (17 : ZMod 68502634201) ^ 2854276425 = (17 : ZMod 68502634201) ^ (1427138212 + 1427138212 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 1427138212 * (17 : ZMod 68502634201) ^ 1427138212) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 58991617267 := by rw [factor_1_30]; decide
      have factor_1_32 : (17 : ZMod 68502634201) ^ 5708552850 = 35480209326 := by
        calc
          (17 : ZMod 68502634201) ^ 5708552850 = (17 : ZMod 68502634201) ^ (2854276425 + 2854276425) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 2854276425 * (17 : ZMod 68502634201) ^ 2854276425 := by rw [pow_add]
          _ = 35480209326 := by rw [factor_1_31]; decide
      have factor_1_33 : (17 : ZMod 68502634201) ^ 11417105700 = 29443123182 := by
        calc
          (17 : ZMod 68502634201) ^ 11417105700 = (17 : ZMod 68502634201) ^ (5708552850 + 5708552850) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 5708552850 * (17 : ZMod 68502634201) ^ 5708552850 := by rw [pow_add]
          _ = 29443123182 := by rw [factor_1_32]; decide
      have factor_1_34 : (17 : ZMod 68502634201) ^ 22834211400 = 29443123181 := by
        calc
          (17 : ZMod 68502634201) ^ 22834211400 = (17 : ZMod 68502634201) ^ (11417105700 + 11417105700) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 11417105700 * (17 : ZMod 68502634201) ^ 11417105700 := by rw [pow_add]
          _ = 29443123181 := by rw [factor_1_33]; decide
      change (17 : ZMod 68502634201) ^ 22834211400 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (17 : ZMod 68502634201) ^ 1 = 17 := by norm_num
      have factor_2_1 : (17 : ZMod 68502634201) ^ 3 = 4913 := by
        calc
          (17 : ZMod 68502634201) ^ 3 = (17 : ZMod 68502634201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 1 * (17 : ZMod 68502634201) ^ 1) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 4913 := by rw [factor_2_0]; decide
      have factor_2_2 : (17 : ZMod 68502634201) ^ 6 = 24137569 := by
        calc
          (17 : ZMod 68502634201) ^ 6 = (17 : ZMod 68502634201) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 3 * (17 : ZMod 68502634201) ^ 3 := by rw [pow_add]
          _ = 24137569 := by rw [factor_2_1]; decide
      have factor_2_3 : (17 : ZMod 68502634201) ^ 12 = 7333350256 := by
        calc
          (17 : ZMod 68502634201) ^ 12 = (17 : ZMod 68502634201) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 6 * (17 : ZMod 68502634201) ^ 6 := by rw [pow_add]
          _ = 7333350256 := by rw [factor_2_2]; decide
      have factor_2_4 : (17 : ZMod 68502634201) ^ 25 = 60994826324 := by
        calc
          (17 : ZMod 68502634201) ^ 25 = (17 : ZMod 68502634201) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 12 * (17 : ZMod 68502634201) ^ 12) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 60994826324 := by rw [factor_2_3]; decide
      have factor_2_5 : (17 : ZMod 68502634201) ^ 51 = 63585109761 := by
        calc
          (17 : ZMod 68502634201) ^ 51 = (17 : ZMod 68502634201) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 25 * (17 : ZMod 68502634201) ^ 25) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 63585109761 := by rw [factor_2_4]; decide
      have factor_2_6 : (17 : ZMod 68502634201) ^ 102 = 15828601997 := by
        calc
          (17 : ZMod 68502634201) ^ 102 = (17 : ZMod 68502634201) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 51 * (17 : ZMod 68502634201) ^ 51 := by rw [pow_add]
          _ = 15828601997 := by rw [factor_2_5]; decide
      have factor_2_7 : (17 : ZMod 68502634201) ^ 204 = 52726070056 := by
        calc
          (17 : ZMod 68502634201) ^ 204 = (17 : ZMod 68502634201) ^ (102 + 102) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 102 * (17 : ZMod 68502634201) ^ 102 := by rw [pow_add]
          _ = 52726070056 := by rw [factor_2_6]; decide
      have factor_2_8 : (17 : ZMod 68502634201) ^ 408 = 42556084656 := by
        calc
          (17 : ZMod 68502634201) ^ 408 = (17 : ZMod 68502634201) ^ (204 + 204) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 204 * (17 : ZMod 68502634201) ^ 204 := by rw [pow_add]
          _ = 42556084656 := by rw [factor_2_7]; decide
      have factor_2_9 : (17 : ZMod 68502634201) ^ 816 = 3813101836 := by
        calc
          (17 : ZMod 68502634201) ^ 816 = (17 : ZMod 68502634201) ^ (408 + 408) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 408 * (17 : ZMod 68502634201) ^ 408 := by rw [pow_add]
          _ = 3813101836 := by rw [factor_2_8]; decide
      have factor_2_10 : (17 : ZMod 68502634201) ^ 1633 = 56050279570 := by
        calc
          (17 : ZMod 68502634201) ^ 1633 = (17 : ZMod 68502634201) ^ (816 + 816 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 816 * (17 : ZMod 68502634201) ^ 816) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 56050279570 := by rw [factor_2_9]; decide
      have factor_2_11 : (17 : ZMod 68502634201) ^ 3266 = 57176587192 := by
        calc
          (17 : ZMod 68502634201) ^ 3266 = (17 : ZMod 68502634201) ^ (1633 + 1633) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1633 * (17 : ZMod 68502634201) ^ 1633 := by rw [pow_add]
          _ = 57176587192 := by rw [factor_2_10]; decide
      have factor_2_12 : (17 : ZMod 68502634201) ^ 6532 = 55987812187 := by
        calc
          (17 : ZMod 68502634201) ^ 6532 = (17 : ZMod 68502634201) ^ (3266 + 3266) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 3266 * (17 : ZMod 68502634201) ^ 3266 := by rw [pow_add]
          _ = 55987812187 := by rw [factor_2_11]; decide
      have factor_2_13 : (17 : ZMod 68502634201) ^ 13065 = 53255047631 := by
        calc
          (17 : ZMod 68502634201) ^ 13065 = (17 : ZMod 68502634201) ^ (6532 + 6532 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 6532 * (17 : ZMod 68502634201) ^ 6532) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 53255047631 := by rw [factor_2_12]; decide
      have factor_2_14 : (17 : ZMod 68502634201) ^ 26131 = 21559761177 := by
        calc
          (17 : ZMod 68502634201) ^ 26131 = (17 : ZMod 68502634201) ^ (13065 + 13065 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 13065 * (17 : ZMod 68502634201) ^ 13065) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 21559761177 := by rw [factor_2_13]; decide
      have factor_2_15 : (17 : ZMod 68502634201) ^ 52263 = 19598301758 := by
        calc
          (17 : ZMod 68502634201) ^ 52263 = (17 : ZMod 68502634201) ^ (26131 + 26131 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 26131 * (17 : ZMod 68502634201) ^ 26131) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 19598301758 := by rw [factor_2_14]; decide
      have factor_2_16 : (17 : ZMod 68502634201) ^ 104526 = 30850974000 := by
        calc
          (17 : ZMod 68502634201) ^ 104526 = (17 : ZMod 68502634201) ^ (52263 + 52263) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 52263 * (17 : ZMod 68502634201) ^ 52263 := by rw [pow_add]
          _ = 30850974000 := by rw [factor_2_15]; decide
      have factor_2_17 : (17 : ZMod 68502634201) ^ 209053 = 46525136746 := by
        calc
          (17 : ZMod 68502634201) ^ 209053 = (17 : ZMod 68502634201) ^ (104526 + 104526 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 104526 * (17 : ZMod 68502634201) ^ 104526) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 46525136746 := by rw [factor_2_16]; decide
      have factor_2_18 : (17 : ZMod 68502634201) ^ 418106 = 43860548741 := by
        calc
          (17 : ZMod 68502634201) ^ 418106 = (17 : ZMod 68502634201) ^ (209053 + 209053) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 209053 * (17 : ZMod 68502634201) ^ 209053 := by rw [pow_add]
          _ = 43860548741 := by rw [factor_2_17]; decide
      have factor_2_19 : (17 : ZMod 68502634201) ^ 836213 = 60131117143 := by
        calc
          (17 : ZMod 68502634201) ^ 836213 = (17 : ZMod 68502634201) ^ (418106 + 418106 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 418106 * (17 : ZMod 68502634201) ^ 418106) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 60131117143 := by rw [factor_2_18]; decide
      have factor_2_20 : (17 : ZMod 68502634201) ^ 1672427 = 47207389149 := by
        calc
          (17 : ZMod 68502634201) ^ 1672427 = (17 : ZMod 68502634201) ^ (836213 + 836213 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 836213 * (17 : ZMod 68502634201) ^ 836213) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 47207389149 := by rw [factor_2_19]; decide
      have factor_2_21 : (17 : ZMod 68502634201) ^ 3344855 = 39573498158 := by
        calc
          (17 : ZMod 68502634201) ^ 3344855 = (17 : ZMod 68502634201) ^ (1672427 + 1672427 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 1672427 * (17 : ZMod 68502634201) ^ 1672427) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 39573498158 := by rw [factor_2_20]; decide
      have factor_2_22 : (17 : ZMod 68502634201) ^ 6689710 = 63344549086 := by
        calc
          (17 : ZMod 68502634201) ^ 6689710 = (17 : ZMod 68502634201) ^ (3344855 + 3344855) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 3344855 * (17 : ZMod 68502634201) ^ 3344855 := by rw [pow_add]
          _ = 63344549086 := by rw [factor_2_21]; decide
      have factor_2_23 : (17 : ZMod 68502634201) ^ 13379420 = 37762090308 := by
        calc
          (17 : ZMod 68502634201) ^ 13379420 = (17 : ZMod 68502634201) ^ (6689710 + 6689710) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 6689710 * (17 : ZMod 68502634201) ^ 6689710 := by rw [pow_add]
          _ = 37762090308 := by rw [factor_2_22]; decide
      have factor_2_24 : (17 : ZMod 68502634201) ^ 26758841 = 28869209545 := by
        calc
          (17 : ZMod 68502634201) ^ 26758841 = (17 : ZMod 68502634201) ^ (13379420 + 13379420 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 13379420 * (17 : ZMod 68502634201) ^ 13379420) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 28869209545 := by rw [factor_2_23]; decide
      have factor_2_25 : (17 : ZMod 68502634201) ^ 53517682 = 7386401386 := by
        calc
          (17 : ZMod 68502634201) ^ 53517682 = (17 : ZMod 68502634201) ^ (26758841 + 26758841) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 26758841 * (17 : ZMod 68502634201) ^ 26758841 := by rw [pow_add]
          _ = 7386401386 := by rw [factor_2_24]; decide
      have factor_2_26 : (17 : ZMod 68502634201) ^ 107035365 = 67093452131 := by
        calc
          (17 : ZMod 68502634201) ^ 107035365 = (17 : ZMod 68502634201) ^ (53517682 + 53517682 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 53517682 * (17 : ZMod 68502634201) ^ 53517682) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 67093452131 := by rw [factor_2_25]; decide
      have factor_2_27 : (17 : ZMod 68502634201) ^ 214070731 = 43764122837 := by
        calc
          (17 : ZMod 68502634201) ^ 214070731 = (17 : ZMod 68502634201) ^ (107035365 + 107035365 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 107035365 * (17 : ZMod 68502634201) ^ 107035365) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 43764122837 := by rw [factor_2_26]; decide
      have factor_2_28 : (17 : ZMod 68502634201) ^ 428141463 = 61472045238 := by
        calc
          (17 : ZMod 68502634201) ^ 428141463 = (17 : ZMod 68502634201) ^ (214070731 + 214070731 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 214070731 * (17 : ZMod 68502634201) ^ 214070731) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 61472045238 := by rw [factor_2_27]; decide
      have factor_2_29 : (17 : ZMod 68502634201) ^ 856282927 = 63083545737 := by
        calc
          (17 : ZMod 68502634201) ^ 856282927 = (17 : ZMod 68502634201) ^ (428141463 + 428141463 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 428141463 * (17 : ZMod 68502634201) ^ 428141463) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 63083545737 := by rw [factor_2_28]; decide
      have factor_2_30 : (17 : ZMod 68502634201) ^ 1712565855 = 68474856882 := by
        calc
          (17 : ZMod 68502634201) ^ 1712565855 = (17 : ZMod 68502634201) ^ (856282927 + 856282927 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 856282927 * (17 : ZMod 68502634201) ^ 856282927) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 68474856882 := by rw [factor_2_29]; decide
      have factor_2_31 : (17 : ZMod 68502634201) ^ 3425131710 = 34281821898 := by
        calc
          (17 : ZMod 68502634201) ^ 3425131710 = (17 : ZMod 68502634201) ^ (1712565855 + 1712565855) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1712565855 * (17 : ZMod 68502634201) ^ 1712565855 := by rw [pow_add]
          _ = 34281821898 := by rw [factor_2_30]; decide
      have factor_2_32 : (17 : ZMod 68502634201) ^ 6850263420 = 54264505273 := by
        calc
          (17 : ZMod 68502634201) ^ 6850263420 = (17 : ZMod 68502634201) ^ (3425131710 + 3425131710) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 3425131710 * (17 : ZMod 68502634201) ^ 3425131710 := by rw [pow_add]
          _ = 54264505273 := by rw [factor_2_31]; decide
      have factor_2_33 : (17 : ZMod 68502634201) ^ 13700526840 = 45444245532 := by
        calc
          (17 : ZMod 68502634201) ^ 13700526840 = (17 : ZMod 68502634201) ^ (6850263420 + 6850263420) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 6850263420 * (17 : ZMod 68502634201) ^ 6850263420 := by rw [pow_add]
          _ = 45444245532 := by rw [factor_2_32]; decide
      change (17 : ZMod 68502634201) ^ 13700526840 ≠ 1
      rw [factor_2_33]
      decide
    ·
      have factor_3_0 : (17 : ZMod 68502634201) ^ 1 = 17 := by norm_num
      have factor_3_1 : (17 : ZMod 68502634201) ^ 2 = 289 := by
        calc
          (17 : ZMod 68502634201) ^ 2 = (17 : ZMod 68502634201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1 * (17 : ZMod 68502634201) ^ 1 := by rw [pow_add]
          _ = 289 := by rw [factor_3_0]; decide
      have factor_3_2 : (17 : ZMod 68502634201) ^ 4 = 83521 := by
        calc
          (17 : ZMod 68502634201) ^ 4 = (17 : ZMod 68502634201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 2 * (17 : ZMod 68502634201) ^ 2 := by rw [pow_add]
          _ = 83521 := by rw [factor_3_1]; decide
      have factor_3_3 : (17 : ZMod 68502634201) ^ 9 = 50085242296 := by
        calc
          (17 : ZMod 68502634201) ^ 9 = (17 : ZMod 68502634201) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 4 * (17 : ZMod 68502634201) ^ 4) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 50085242296 := by rw [factor_3_2]; decide
      have factor_3_4 : (17 : ZMod 68502634201) ^ 18 = 16590570287 := by
        calc
          (17 : ZMod 68502634201) ^ 18 = (17 : ZMod 68502634201) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 9 * (17 : ZMod 68502634201) ^ 9 := by rw [pow_add]
          _ = 16590570287 := by rw [factor_3_3]; decide
      have factor_3_5 : (17 : ZMod 68502634201) ^ 36 = 12556079978 := by
        calc
          (17 : ZMod 68502634201) ^ 36 = (17 : ZMod 68502634201) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 18 * (17 : ZMod 68502634201) ^ 18 := by rw [pow_add]
          _ = 12556079978 := by rw [factor_3_4]; decide
      have factor_3_6 : (17 : ZMod 68502634201) ^ 72 = 47889809833 := by
        calc
          (17 : ZMod 68502634201) ^ 72 = (17 : ZMod 68502634201) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 36 * (17 : ZMod 68502634201) ^ 36 := by rw [pow_add]
          _ = 47889809833 := by rw [factor_3_5]; decide
      have factor_3_7 : (17 : ZMod 68502634201) ^ 145 = 44946796184 := by
        calc
          (17 : ZMod 68502634201) ^ 145 = (17 : ZMod 68502634201) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 72 * (17 : ZMod 68502634201) ^ 72) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 44946796184 := by rw [factor_3_6]; decide
      have factor_3_8 : (17 : ZMod 68502634201) ^ 291 = 3814318313 := by
        calc
          (17 : ZMod 68502634201) ^ 291 = (17 : ZMod 68502634201) ^ (145 + 145 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 145 * (17 : ZMod 68502634201) ^ 145) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 3814318313 := by rw [factor_3_7]; decide
      have factor_3_9 : (17 : ZMod 68502634201) ^ 583 = 58043318186 := by
        calc
          (17 : ZMod 68502634201) ^ 583 = (17 : ZMod 68502634201) ^ (291 + 291 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 291 * (17 : ZMod 68502634201) ^ 291) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 58043318186 := by rw [factor_3_8]; decide
      have factor_3_10 : (17 : ZMod 68502634201) ^ 1166 = 15563707086 := by
        calc
          (17 : ZMod 68502634201) ^ 1166 = (17 : ZMod 68502634201) ^ (583 + 583) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 583 * (17 : ZMod 68502634201) ^ 583 := by rw [pow_add]
          _ = 15563707086 := by rw [factor_3_9]; decide
      have factor_3_11 : (17 : ZMod 68502634201) ^ 2333 = 29158502522 := by
        calc
          (17 : ZMod 68502634201) ^ 2333 = (17 : ZMod 68502634201) ^ (1166 + 1166 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 1166 * (17 : ZMod 68502634201) ^ 1166) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 29158502522 := by rw [factor_3_10]; decide
      have factor_3_12 : (17 : ZMod 68502634201) ^ 4666 = 35410010636 := by
        calc
          (17 : ZMod 68502634201) ^ 4666 = (17 : ZMod 68502634201) ^ (2333 + 2333) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 2333 * (17 : ZMod 68502634201) ^ 2333 := by rw [pow_add]
          _ = 35410010636 := by rw [factor_3_11]; decide
      have factor_3_13 : (17 : ZMod 68502634201) ^ 9332 = 31857856792 := by
        calc
          (17 : ZMod 68502634201) ^ 9332 = (17 : ZMod 68502634201) ^ (4666 + 4666) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 4666 * (17 : ZMod 68502634201) ^ 4666 := by rw [pow_add]
          _ = 31857856792 := by rw [factor_3_12]; decide
      have factor_3_14 : (17 : ZMod 68502634201) ^ 18665 = 29987751532 := by
        calc
          (17 : ZMod 68502634201) ^ 18665 = (17 : ZMod 68502634201) ^ (9332 + 9332 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 9332 * (17 : ZMod 68502634201) ^ 9332) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 29987751532 := by rw [factor_3_13]; decide
      have factor_3_15 : (17 : ZMod 68502634201) ^ 37330 = 49609067511 := by
        calc
          (17 : ZMod 68502634201) ^ 37330 = (17 : ZMod 68502634201) ^ (18665 + 18665) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 18665 * (17 : ZMod 68502634201) ^ 18665 := by rw [pow_add]
          _ = 49609067511 := by rw [factor_3_14]; decide
      have factor_3_16 : (17 : ZMod 68502634201) ^ 74661 = 50447618170 := by
        calc
          (17 : ZMod 68502634201) ^ 74661 = (17 : ZMod 68502634201) ^ (37330 + 37330 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 37330 * (17 : ZMod 68502634201) ^ 37330) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 50447618170 := by rw [factor_3_15]; decide
      have factor_3_17 : (17 : ZMod 68502634201) ^ 149323 = 31291763128 := by
        calc
          (17 : ZMod 68502634201) ^ 149323 = (17 : ZMod 68502634201) ^ (74661 + 74661 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 74661 * (17 : ZMod 68502634201) ^ 74661) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 31291763128 := by rw [factor_3_16]; decide
      have factor_3_18 : (17 : ZMod 68502634201) ^ 298647 = 105100270 := by
        calc
          (17 : ZMod 68502634201) ^ 298647 = (17 : ZMod 68502634201) ^ (149323 + 149323 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 149323 * (17 : ZMod 68502634201) ^ 149323) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 105100270 := by rw [factor_3_17]; decide
      have factor_3_19 : (17 : ZMod 68502634201) ^ 597295 = 14805211246 := by
        calc
          (17 : ZMod 68502634201) ^ 597295 = (17 : ZMod 68502634201) ^ (298647 + 298647 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 298647 * (17 : ZMod 68502634201) ^ 298647) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 14805211246 := by rw [factor_3_18]; decide
      have factor_3_20 : (17 : ZMod 68502634201) ^ 1194591 = 67468321569 := by
        calc
          (17 : ZMod 68502634201) ^ 1194591 = (17 : ZMod 68502634201) ^ (597295 + 597295 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 597295 * (17 : ZMod 68502634201) ^ 597295) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 67468321569 := by rw [factor_3_19]; decide
      have factor_3_21 : (17 : ZMod 68502634201) ^ 2389182 = 65016289469 := by
        calc
          (17 : ZMod 68502634201) ^ 2389182 = (17 : ZMod 68502634201) ^ (1194591 + 1194591) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1194591 * (17 : ZMod 68502634201) ^ 1194591 := by rw [pow_add]
          _ = 65016289469 := by rw [factor_3_20]; decide
      have factor_3_22 : (17 : ZMod 68502634201) ^ 4778364 = 56248678038 := by
        calc
          (17 : ZMod 68502634201) ^ 4778364 = (17 : ZMod 68502634201) ^ (2389182 + 2389182) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 2389182 * (17 : ZMod 68502634201) ^ 2389182 := by rw [pow_add]
          _ = 56248678038 := by rw [factor_3_21]; decide
      have factor_3_23 : (17 : ZMod 68502634201) ^ 9556729 = 19213887863 := by
        calc
          (17 : ZMod 68502634201) ^ 9556729 = (17 : ZMod 68502634201) ^ (4778364 + 4778364 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 4778364 * (17 : ZMod 68502634201) ^ 4778364) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 19213887863 := by rw [factor_3_22]; decide
      have factor_3_24 : (17 : ZMod 68502634201) ^ 19113458 = 16881159245 := by
        calc
          (17 : ZMod 68502634201) ^ 19113458 = (17 : ZMod 68502634201) ^ (9556729 + 9556729) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 9556729 * (17 : ZMod 68502634201) ^ 9556729 := by rw [pow_add]
          _ = 16881159245 := by rw [factor_3_23]; decide
      have factor_3_25 : (17 : ZMod 68502634201) ^ 38226916 = 54711302375 := by
        calc
          (17 : ZMod 68502634201) ^ 38226916 = (17 : ZMod 68502634201) ^ (19113458 + 19113458) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 19113458 * (17 : ZMod 68502634201) ^ 19113458 := by rw [pow_add]
          _ = 54711302375 := by rw [factor_3_24]; decide
      have factor_3_26 : (17 : ZMod 68502634201) ^ 76453832 = 45033580546 := by
        calc
          (17 : ZMod 68502634201) ^ 76453832 = (17 : ZMod 68502634201) ^ (38226916 + 38226916) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 38226916 * (17 : ZMod 68502634201) ^ 38226916 := by rw [pow_add]
          _ = 45033580546 := by rw [factor_3_25]; decide
      have factor_3_27 : (17 : ZMod 68502634201) ^ 152907665 = 32823091658 := by
        calc
          (17 : ZMod 68502634201) ^ 152907665 = (17 : ZMod 68502634201) ^ (76453832 + 76453832 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 76453832 * (17 : ZMod 68502634201) ^ 76453832) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 32823091658 := by rw [factor_3_26]; decide
      have factor_3_28 : (17 : ZMod 68502634201) ^ 305815331 = 64069642559 := by
        calc
          (17 : ZMod 68502634201) ^ 305815331 = (17 : ZMod 68502634201) ^ (152907665 + 152907665 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 152907665 * (17 : ZMod 68502634201) ^ 152907665) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 64069642559 := by rw [factor_3_27]; decide
      have factor_3_29 : (17 : ZMod 68502634201) ^ 611630662 = 37832739827 := by
        calc
          (17 : ZMod 68502634201) ^ 611630662 = (17 : ZMod 68502634201) ^ (305815331 + 305815331) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 305815331 * (17 : ZMod 68502634201) ^ 305815331 := by rw [pow_add]
          _ = 37832739827 := by rw [factor_3_28]; decide
      have factor_3_30 : (17 : ZMod 68502634201) ^ 1223261325 = 68335336895 := by
        calc
          (17 : ZMod 68502634201) ^ 1223261325 = (17 : ZMod 68502634201) ^ (611630662 + 611630662 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 611630662 * (17 : ZMod 68502634201) ^ 611630662) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 68335336895 := by rw [factor_3_29]; decide
      have factor_3_31 : (17 : ZMod 68502634201) ^ 2446522650 = 61831452463 := by
        calc
          (17 : ZMod 68502634201) ^ 2446522650 = (17 : ZMod 68502634201) ^ (1223261325 + 1223261325) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1223261325 * (17 : ZMod 68502634201) ^ 1223261325 := by rw [pow_add]
          _ = 61831452463 := by rw [factor_3_30]; decide
      have factor_3_32 : (17 : ZMod 68502634201) ^ 4893045300 = 27550145278 := by
        calc
          (17 : ZMod 68502634201) ^ 4893045300 = (17 : ZMod 68502634201) ^ (2446522650 + 2446522650) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 2446522650 * (17 : ZMod 68502634201) ^ 2446522650 := by rw [pow_add]
          _ = 27550145278 := by rw [factor_3_31]; decide
      have factor_3_33 : (17 : ZMod 68502634201) ^ 9786090600 = 38148938446 := by
        calc
          (17 : ZMod 68502634201) ^ 9786090600 = (17 : ZMod 68502634201) ^ (4893045300 + 4893045300) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 4893045300 * (17 : ZMod 68502634201) ^ 4893045300 := by rw [pow_add]
          _ = 38148938446 := by rw [factor_3_32]; decide
      change (17 : ZMod 68502634201) ^ 9786090600 ≠ 1
      rw [factor_3_33]
      decide
    ·
      have factor_4_0 : (17 : ZMod 68502634201) ^ 1 = 17 := by norm_num
      have factor_4_1 : (17 : ZMod 68502634201) ^ 2 = 289 := by
        calc
          (17 : ZMod 68502634201) ^ 2 = (17 : ZMod 68502634201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1 * (17 : ZMod 68502634201) ^ 1 := by rw [pow_add]
          _ = 289 := by rw [factor_4_0]; decide
      have factor_4_2 : (17 : ZMod 68502634201) ^ 5 = 1419857 := by
        calc
          (17 : ZMod 68502634201) ^ 5 = (17 : ZMod 68502634201) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 2 * (17 : ZMod 68502634201) ^ 2) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 1419857 := by rw [factor_4_1]; decide
      have factor_4_3 : (17 : ZMod 68502634201) ^ 11 = 20579207133 := by
        calc
          (17 : ZMod 68502634201) ^ 11 = (17 : ZMod 68502634201) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 5 * (17 : ZMod 68502634201) ^ 5) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 20579207133 := by rw [factor_4_2]; decide
      have factor_4_4 : (17 : ZMod 68502634201) ^ 23 = 31025388486 := by
        calc
          (17 : ZMod 68502634201) ^ 23 = (17 : ZMod 68502634201) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 11 * (17 : ZMod 68502634201) ^ 11) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 31025388486 := by rw [factor_4_3]; decide
      have factor_4_5 : (17 : ZMod 68502634201) ^ 46 = 57630505510 := by
        calc
          (17 : ZMod 68502634201) ^ 46 = (17 : ZMod 68502634201) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 23 * (17 : ZMod 68502634201) ^ 23 := by rw [pow_add]
          _ = 57630505510 := by rw [factor_4_4]; decide
      have factor_4_6 : (17 : ZMod 68502634201) ^ 92 = 54780806936 := by
        calc
          (17 : ZMod 68502634201) ^ 92 = (17 : ZMod 68502634201) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 46 * (17 : ZMod 68502634201) ^ 46 := by rw [pow_add]
          _ = 54780806936 := by rw [factor_4_5]; decide
      have factor_4_7 : (17 : ZMod 68502634201) ^ 185 = 5466209085 := by
        calc
          (17 : ZMod 68502634201) ^ 185 = (17 : ZMod 68502634201) ^ (92 + 92 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 92 * (17 : ZMod 68502634201) ^ 92) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 5466209085 := by rw [factor_4_6]; decide
      have factor_4_8 : (17 : ZMod 68502634201) ^ 371 = 4788821663 := by
        calc
          (17 : ZMod 68502634201) ^ 371 = (17 : ZMod 68502634201) ^ (185 + 185 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 185 * (17 : ZMod 68502634201) ^ 185) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 4788821663 := by rw [factor_4_7]; decide
      have factor_4_9 : (17 : ZMod 68502634201) ^ 742 = 15394825653 := by
        calc
          (17 : ZMod 68502634201) ^ 742 = (17 : ZMod 68502634201) ^ (371 + 371) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 371 * (17 : ZMod 68502634201) ^ 371 := by rw [pow_add]
          _ = 15394825653 := by rw [factor_4_8]; decide
      have factor_4_10 : (17 : ZMod 68502634201) ^ 1484 = 37571262251 := by
        calc
          (17 : ZMod 68502634201) ^ 1484 = (17 : ZMod 68502634201) ^ (742 + 742) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 742 * (17 : ZMod 68502634201) ^ 742 := by rw [pow_add]
          _ = 37571262251 := by rw [factor_4_9]; decide
      have factor_4_11 : (17 : ZMod 68502634201) ^ 2969 = 25832483145 := by
        calc
          (17 : ZMod 68502634201) ^ 2969 = (17 : ZMod 68502634201) ^ (1484 + 1484 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 1484 * (17 : ZMod 68502634201) ^ 1484) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 25832483145 := by rw [factor_4_10]; decide
      have factor_4_12 : (17 : ZMod 68502634201) ^ 5939 = 11567623585 := by
        calc
          (17 : ZMod 68502634201) ^ 5939 = (17 : ZMod 68502634201) ^ (2969 + 2969 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 2969 * (17 : ZMod 68502634201) ^ 2969) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 11567623585 := by rw [factor_4_11]; decide
      have factor_4_13 : (17 : ZMod 68502634201) ^ 11878 = 52387301121 := by
        calc
          (17 : ZMod 68502634201) ^ 11878 = (17 : ZMod 68502634201) ^ (5939 + 5939) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 5939 * (17 : ZMod 68502634201) ^ 5939 := by rw [pow_add]
          _ = 52387301121 := by rw [factor_4_12]; decide
      have factor_4_14 : (17 : ZMod 68502634201) ^ 23756 = 39084587701 := by
        calc
          (17 : ZMod 68502634201) ^ 23756 = (17 : ZMod 68502634201) ^ (11878 + 11878) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 11878 * (17 : ZMod 68502634201) ^ 11878 := by rw [pow_add]
          _ = 39084587701 := by rw [factor_4_13]; decide
      have factor_4_15 : (17 : ZMod 68502634201) ^ 47512 = 31945991699 := by
        calc
          (17 : ZMod 68502634201) ^ 47512 = (17 : ZMod 68502634201) ^ (23756 + 23756) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 23756 * (17 : ZMod 68502634201) ^ 23756 := by rw [pow_add]
          _ = 31945991699 := by rw [factor_4_14]; decide
      have factor_4_16 : (17 : ZMod 68502634201) ^ 95024 = 62371581327 := by
        calc
          (17 : ZMod 68502634201) ^ 95024 = (17 : ZMod 68502634201) ^ (47512 + 47512) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 47512 * (17 : ZMod 68502634201) ^ 47512 := by rw [pow_add]
          _ = 62371581327 := by rw [factor_4_15]; decide
      have factor_4_17 : (17 : ZMod 68502634201) ^ 190048 = 61870985038 := by
        calc
          (17 : ZMod 68502634201) ^ 190048 = (17 : ZMod 68502634201) ^ (95024 + 95024) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 95024 * (17 : ZMod 68502634201) ^ 95024 := by rw [pow_add]
          _ = 61870985038 := by rw [factor_4_16]; decide
      have factor_4_18 : (17 : ZMod 68502634201) ^ 380097 = 17355765953 := by
        calc
          (17 : ZMod 68502634201) ^ 380097 = (17 : ZMod 68502634201) ^ (190048 + 190048 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 190048 * (17 : ZMod 68502634201) ^ 190048) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 17355765953 := by rw [factor_4_17]; decide
      have factor_4_19 : (17 : ZMod 68502634201) ^ 760194 = 27402736316 := by
        calc
          (17 : ZMod 68502634201) ^ 760194 = (17 : ZMod 68502634201) ^ (380097 + 380097) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 380097 * (17 : ZMod 68502634201) ^ 380097 := by rw [pow_add]
          _ = 27402736316 := by rw [factor_4_18]; decide
      have factor_4_20 : (17 : ZMod 68502634201) ^ 1520388 = 66496246035 := by
        calc
          (17 : ZMod 68502634201) ^ 1520388 = (17 : ZMod 68502634201) ^ (760194 + 760194) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 760194 * (17 : ZMod 68502634201) ^ 760194 := by rw [pow_add]
          _ = 66496246035 := by rw [factor_4_19]; decide
      have factor_4_21 : (17 : ZMod 68502634201) ^ 3040777 = 7185113075 := by
        calc
          (17 : ZMod 68502634201) ^ 3040777 = (17 : ZMod 68502634201) ^ (1520388 + 1520388 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 1520388 * (17 : ZMod 68502634201) ^ 1520388) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 7185113075 := by rw [factor_4_20]; decide
      have factor_4_22 : (17 : ZMod 68502634201) ^ 6081554 = 1073036364 := by
        calc
          (17 : ZMod 68502634201) ^ 6081554 = (17 : ZMod 68502634201) ^ (3040777 + 3040777) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 3040777 * (17 : ZMod 68502634201) ^ 3040777 := by rw [pow_add]
          _ = 1073036364 := by rw [factor_4_21]; decide
      have factor_4_23 : (17 : ZMod 68502634201) ^ 12163109 = 42721774169 := by
        calc
          (17 : ZMod 68502634201) ^ 12163109 = (17 : ZMod 68502634201) ^ (6081554 + 6081554 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 6081554 * (17 : ZMod 68502634201) ^ 6081554) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 42721774169 := by rw [factor_4_22]; decide
      have factor_4_24 : (17 : ZMod 68502634201) ^ 24326219 = 31589269383 := by
        calc
          (17 : ZMod 68502634201) ^ 24326219 = (17 : ZMod 68502634201) ^ (12163109 + 12163109 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 12163109 * (17 : ZMod 68502634201) ^ 12163109) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 31589269383 := by rw [factor_4_23]; decide
      have factor_4_25 : (17 : ZMod 68502634201) ^ 48652439 = 50003991439 := by
        calc
          (17 : ZMod 68502634201) ^ 48652439 = (17 : ZMod 68502634201) ^ (24326219 + 24326219 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 24326219 * (17 : ZMod 68502634201) ^ 24326219) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 50003991439 := by rw [factor_4_24]; decide
      have factor_4_26 : (17 : ZMod 68502634201) ^ 97304878 = 46582504861 := by
        calc
          (17 : ZMod 68502634201) ^ 97304878 = (17 : ZMod 68502634201) ^ (48652439 + 48652439) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 48652439 * (17 : ZMod 68502634201) ^ 48652439 := by rw [pow_add]
          _ = 46582504861 := by rw [factor_4_25]; decide
      have factor_4_27 : (17 : ZMod 68502634201) ^ 194609756 = 58319386158 := by
        calc
          (17 : ZMod 68502634201) ^ 194609756 = (17 : ZMod 68502634201) ^ (97304878 + 97304878) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 97304878 * (17 : ZMod 68502634201) ^ 97304878 := by rw [pow_add]
          _ = 58319386158 := by rw [factor_4_26]; decide
      have factor_4_28 : (17 : ZMod 68502634201) ^ 389219512 = 4512857553 := by
        calc
          (17 : ZMod 68502634201) ^ 389219512 = (17 : ZMod 68502634201) ^ (194609756 + 194609756) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 194609756 * (17 : ZMod 68502634201) ^ 194609756 := by rw [pow_add]
          _ = 4512857553 := by rw [factor_4_27]; decide
      have factor_4_29 : (17 : ZMod 68502634201) ^ 778439025 = 30321415509 := by
        calc
          (17 : ZMod 68502634201) ^ 778439025 = (17 : ZMod 68502634201) ^ (389219512 + 389219512 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 389219512 * (17 : ZMod 68502634201) ^ 389219512) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 30321415509 := by rw [factor_4_28]; decide
      have factor_4_30 : (17 : ZMod 68502634201) ^ 1556878050 = 58151495292 := by
        calc
          (17 : ZMod 68502634201) ^ 1556878050 = (17 : ZMod 68502634201) ^ (778439025 + 778439025) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 778439025 * (17 : ZMod 68502634201) ^ 778439025 := by rw [pow_add]
          _ = 58151495292 := by rw [factor_4_29]; decide
      have factor_4_31 : (17 : ZMod 68502634201) ^ 3113756100 = 36579361528 := by
        calc
          (17 : ZMod 68502634201) ^ 3113756100 = (17 : ZMod 68502634201) ^ (1556878050 + 1556878050) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1556878050 * (17 : ZMod 68502634201) ^ 1556878050 := by rw [pow_add]
          _ = 36579361528 := by rw [factor_4_30]; decide
      have factor_4_32 : (17 : ZMod 68502634201) ^ 6227512200 = 43097134015 := by
        calc
          (17 : ZMod 68502634201) ^ 6227512200 = (17 : ZMod 68502634201) ^ (3113756100 + 3113756100) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 3113756100 * (17 : ZMod 68502634201) ^ 3113756100 := by rw [pow_add]
          _ = 43097134015 := by rw [factor_4_31]; decide
      change (17 : ZMod 68502634201) ^ 6227512200 ≠ 1
      rw [factor_4_32]
      decide
    ·
      have factor_5_0 : (17 : ZMod 68502634201) ^ 1 = 17 := by norm_num
      have factor_5_1 : (17 : ZMod 68502634201) ^ 2 = 289 := by
        calc
          (17 : ZMod 68502634201) ^ 2 = (17 : ZMod 68502634201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1 * (17 : ZMod 68502634201) ^ 1 := by rw [pow_add]
          _ = 289 := by rw [factor_5_0]; decide
      have factor_5_2 : (17 : ZMod 68502634201) ^ 4 = 83521 := by
        calc
          (17 : ZMod 68502634201) ^ 4 = (17 : ZMod 68502634201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 2 * (17 : ZMod 68502634201) ^ 2 := by rw [pow_add]
          _ = 83521 := by rw [factor_5_1]; decide
      have factor_5_3 : (17 : ZMod 68502634201) ^ 9 = 50085242296 := by
        calc
          (17 : ZMod 68502634201) ^ 9 = (17 : ZMod 68502634201) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 4 * (17 : ZMod 68502634201) ^ 4) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 50085242296 := by rw [factor_5_2]; decide
      have factor_5_4 : (17 : ZMod 68502634201) ^ 19 = 8029158075 := by
        calc
          (17 : ZMod 68502634201) ^ 19 = (17 : ZMod 68502634201) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 9 * (17 : ZMod 68502634201) ^ 9) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 8029158075 := by rw [factor_5_3]; decide
      have factor_5_5 : (17 : ZMod 68502634201) ^ 39 = 35650151014 := by
        calc
          (17 : ZMod 68502634201) ^ 39 = (17 : ZMod 68502634201) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 19 * (17 : ZMod 68502634201) ^ 19) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 35650151014 := by rw [factor_5_4]; decide
      have factor_5_6 : (17 : ZMod 68502634201) ^ 78 = 67076827738 := by
        calc
          (17 : ZMod 68502634201) ^ 78 = (17 : ZMod 68502634201) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 39 * (17 : ZMod 68502634201) ^ 39 := by rw [pow_add]
          _ = 67076827738 := by rw [factor_5_5]; decide
      have factor_5_7 : (17 : ZMod 68502634201) ^ 157 = 10941580172 := by
        calc
          (17 : ZMod 68502634201) ^ 157 = (17 : ZMod 68502634201) ^ (78 + 78 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 78 * (17 : ZMod 68502634201) ^ 78) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 10941580172 := by rw [factor_5_6]; decide
      have factor_5_8 : (17 : ZMod 68502634201) ^ 314 = 47808991983 := by
        calc
          (17 : ZMod 68502634201) ^ 314 = (17 : ZMod 68502634201) ^ (157 + 157) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 157 * (17 : ZMod 68502634201) ^ 157 := by rw [pow_add]
          _ = 47808991983 := by rw [factor_5_7]; decide
      have factor_5_9 : (17 : ZMod 68502634201) ^ 628 = 1235017575 := by
        calc
          (17 : ZMod 68502634201) ^ 628 = (17 : ZMod 68502634201) ^ (314 + 314) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 314 * (17 : ZMod 68502634201) ^ 314 := by rw [pow_add]
          _ = 1235017575 := by rw [factor_5_8]; decide
      have factor_5_10 : (17 : ZMod 68502634201) ^ 1256 = 60374057790 := by
        calc
          (17 : ZMod 68502634201) ^ 1256 = (17 : ZMod 68502634201) ^ (628 + 628) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 628 * (17 : ZMod 68502634201) ^ 628 := by rw [pow_add]
          _ = 60374057790 := by rw [factor_5_9]; decide
      have factor_5_11 : (17 : ZMod 68502634201) ^ 2512 = 16132434656 := by
        calc
          (17 : ZMod 68502634201) ^ 2512 = (17 : ZMod 68502634201) ^ (1256 + 1256) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1256 * (17 : ZMod 68502634201) ^ 1256 := by rw [pow_add]
          _ = 16132434656 := by rw [factor_5_10]; decide
      have factor_5_12 : (17 : ZMod 68502634201) ^ 5025 = 2460424534 := by
        calc
          (17 : ZMod 68502634201) ^ 5025 = (17 : ZMod 68502634201) ^ (2512 + 2512 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 2512 * (17 : ZMod 68502634201) ^ 2512) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 2460424534 := by rw [factor_5_11]; decide
      have factor_5_13 : (17 : ZMod 68502634201) ^ 10050 = 60396707335 := by
        calc
          (17 : ZMod 68502634201) ^ 10050 = (17 : ZMod 68502634201) ^ (5025 + 5025) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 5025 * (17 : ZMod 68502634201) ^ 5025 := by rw [pow_add]
          _ = 60396707335 := by rw [factor_5_12]; decide
      have factor_5_14 : (17 : ZMod 68502634201) ^ 20101 = 61678524870 := by
        calc
          (17 : ZMod 68502634201) ^ 20101 = (17 : ZMod 68502634201) ^ (10050 + 10050 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 10050 * (17 : ZMod 68502634201) ^ 10050) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 61678524870 := by rw [factor_5_13]; decide
      have factor_5_15 : (17 : ZMod 68502634201) ^ 40202 = 50589654252 := by
        calc
          (17 : ZMod 68502634201) ^ 40202 = (17 : ZMod 68502634201) ^ (20101 + 20101) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 20101 * (17 : ZMod 68502634201) ^ 20101 := by rw [pow_add]
          _ = 50589654252 := by rw [factor_5_14]; decide
      have factor_5_16 : (17 : ZMod 68502634201) ^ 80405 = 52481166018 := by
        calc
          (17 : ZMod 68502634201) ^ 80405 = (17 : ZMod 68502634201) ^ (40202 + 40202 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 40202 * (17 : ZMod 68502634201) ^ 40202) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 52481166018 := by rw [factor_5_15]; decide
      have factor_5_17 : (17 : ZMod 68502634201) ^ 160810 = 37320075649 := by
        calc
          (17 : ZMod 68502634201) ^ 160810 = (17 : ZMod 68502634201) ^ (80405 + 80405) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 80405 * (17 : ZMod 68502634201) ^ 80405 := by rw [pow_add]
          _ = 37320075649 := by rw [factor_5_16]; decide
      have factor_5_18 : (17 : ZMod 68502634201) ^ 321620 = 8222521263 := by
        calc
          (17 : ZMod 68502634201) ^ 321620 = (17 : ZMod 68502634201) ^ (160810 + 160810) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 160810 * (17 : ZMod 68502634201) ^ 160810 := by rw [pow_add]
          _ = 8222521263 := by rw [factor_5_17]; decide
      have factor_5_19 : (17 : ZMod 68502634201) ^ 643241 = 27170055366 := by
        calc
          (17 : ZMod 68502634201) ^ 643241 = (17 : ZMod 68502634201) ^ (321620 + 321620 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 321620 * (17 : ZMod 68502634201) ^ 321620) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 27170055366 := by rw [factor_5_18]; decide
      have factor_5_20 : (17 : ZMod 68502634201) ^ 1286482 = 1181189784 := by
        calc
          (17 : ZMod 68502634201) ^ 1286482 = (17 : ZMod 68502634201) ^ (643241 + 643241) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 643241 * (17 : ZMod 68502634201) ^ 643241 := by rw [pow_add]
          _ = 1181189784 := by rw [factor_5_19]; decide
      have factor_5_21 : (17 : ZMod 68502634201) ^ 2572965 = 8860882343 := by
        calc
          (17 : ZMod 68502634201) ^ 2572965 = (17 : ZMod 68502634201) ^ (1286482 + 1286482 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 1286482 * (17 : ZMod 68502634201) ^ 1286482) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 8860882343 := by rw [factor_5_20]; decide
      have factor_5_22 : (17 : ZMod 68502634201) ^ 5145931 = 22111194534 := by
        calc
          (17 : ZMod 68502634201) ^ 5145931 = (17 : ZMod 68502634201) ^ (2572965 + 2572965 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 2572965 * (17 : ZMod 68502634201) ^ 2572965) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 22111194534 := by rw [factor_5_21]; decide
      have factor_5_23 : (17 : ZMod 68502634201) ^ 10291862 = 52429181858 := by
        calc
          (17 : ZMod 68502634201) ^ 10291862 = (17 : ZMod 68502634201) ^ (5145931 + 5145931) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 5145931 * (17 : ZMod 68502634201) ^ 5145931 := by rw [pow_add]
          _ = 52429181858 := by rw [factor_5_22]; decide
      have factor_5_24 : (17 : ZMod 68502634201) ^ 20583724 = 36903308340 := by
        calc
          (17 : ZMod 68502634201) ^ 20583724 = (17 : ZMod 68502634201) ^ (10291862 + 10291862) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 10291862 * (17 : ZMod 68502634201) ^ 10291862 := by rw [pow_add]
          _ = 36903308340 := by rw [factor_5_23]; decide
      have factor_5_25 : (17 : ZMod 68502634201) ^ 41167448 = 23993918586 := by
        calc
          (17 : ZMod 68502634201) ^ 41167448 = (17 : ZMod 68502634201) ^ (20583724 + 20583724) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 20583724 * (17 : ZMod 68502634201) ^ 20583724 := by rw [pow_add]
          _ = 23993918586 := by rw [factor_5_24]; decide
      have factor_5_26 : (17 : ZMod 68502634201) ^ 82334896 = 37280622748 := by
        calc
          (17 : ZMod 68502634201) ^ 82334896 = (17 : ZMod 68502634201) ^ (41167448 + 41167448) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 41167448 * (17 : ZMod 68502634201) ^ 41167448 := by rw [pow_add]
          _ = 37280622748 := by rw [factor_5_25]; decide
      have factor_5_27 : (17 : ZMod 68502634201) ^ 164669793 = 28651201996 := by
        calc
          (17 : ZMod 68502634201) ^ 164669793 = (17 : ZMod 68502634201) ^ (82334896 + 82334896 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 82334896 * (17 : ZMod 68502634201) ^ 82334896) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 28651201996 := by rw [factor_5_26]; decide
      have factor_5_28 : (17 : ZMod 68502634201) ^ 329339587 = 41185336920 := by
        calc
          (17 : ZMod 68502634201) ^ 329339587 = (17 : ZMod 68502634201) ^ (164669793 + 164669793 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 164669793 * (17 : ZMod 68502634201) ^ 164669793) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 41185336920 := by rw [factor_5_27]; decide
      have factor_5_29 : (17 : ZMod 68502634201) ^ 658679175 = 13847339427 := by
        calc
          (17 : ZMod 68502634201) ^ 658679175 = (17 : ZMod 68502634201) ^ (329339587 + 329339587 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 329339587 * (17 : ZMod 68502634201) ^ 329339587) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 13847339427 := by rw [factor_5_28]; decide
      have factor_5_30 : (17 : ZMod 68502634201) ^ 1317358350 = 44869370083 := by
        calc
          (17 : ZMod 68502634201) ^ 1317358350 = (17 : ZMod 68502634201) ^ (658679175 + 658679175) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 658679175 * (17 : ZMod 68502634201) ^ 658679175 := by rw [pow_add]
          _ = 44869370083 := by rw [factor_5_29]; decide
      have factor_5_31 : (17 : ZMod 68502634201) ^ 2634716700 = 65183680719 := by
        calc
          (17 : ZMod 68502634201) ^ 2634716700 = (17 : ZMod 68502634201) ^ (1317358350 + 1317358350) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1317358350 * (17 : ZMod 68502634201) ^ 1317358350 := by rw [pow_add]
          _ = 65183680719 := by rw [factor_5_30]; decide
      have factor_5_32 : (17 : ZMod 68502634201) ^ 5269433400 = 42868795587 := by
        calc
          (17 : ZMod 68502634201) ^ 5269433400 = (17 : ZMod 68502634201) ^ (2634716700 + 2634716700) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 2634716700 * (17 : ZMod 68502634201) ^ 2634716700 := by rw [pow_add]
          _ = 42868795587 := by rw [factor_5_31]; decide
      change (17 : ZMod 68502634201) ^ 5269433400 ≠ 1
      rw [factor_5_32]
      decide
    ·
      have factor_6_0 : (17 : ZMod 68502634201) ^ 1 = 17 := by norm_num
      have factor_6_1 : (17 : ZMod 68502634201) ^ 3 = 4913 := by
        calc
          (17 : ZMod 68502634201) ^ 3 = (17 : ZMod 68502634201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 1 * (17 : ZMod 68502634201) ^ 1) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 4913 := by rw [factor_6_0]; decide
      have factor_6_2 : (17 : ZMod 68502634201) ^ 6 = 24137569 := by
        calc
          (17 : ZMod 68502634201) ^ 6 = (17 : ZMod 68502634201) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 3 * (17 : ZMod 68502634201) ^ 3 := by rw [pow_add]
          _ = 24137569 := by rw [factor_6_1]; decide
      have factor_6_3 : (17 : ZMod 68502634201) ^ 13 = 56164320151 := by
        calc
          (17 : ZMod 68502634201) ^ 13 = (17 : ZMod 68502634201) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 6 * (17 : ZMod 68502634201) ^ 6) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 56164320151 := by rw [factor_6_2]; decide
      have factor_6_4 : (17 : ZMod 68502634201) ^ 26 = 9372534493 := by
        calc
          (17 : ZMod 68502634201) ^ 26 = (17 : ZMod 68502634201) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 13 * (17 : ZMod 68502634201) ^ 13 := by rw [pow_add]
          _ = 9372534493 := by rw [factor_6_3]; decide
      have factor_6_5 : (17 : ZMod 68502634201) ^ 53 = 17390755061 := by
        calc
          (17 : ZMod 68502634201) ^ 53 = (17 : ZMod 68502634201) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 26 * (17 : ZMod 68502634201) ^ 26) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 17390755061 := by rw [factor_6_4]; decide
      have factor_6_6 : (17 : ZMod 68502634201) ^ 107 = 7116990349 := by
        calc
          (17 : ZMod 68502634201) ^ 107 = (17 : ZMod 68502634201) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 53 * (17 : ZMod 68502634201) ^ 53) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 7116990349 := by rw [factor_6_5]; decide
      have factor_6_7 : (17 : ZMod 68502634201) ^ 214 = 34973326526 := by
        calc
          (17 : ZMod 68502634201) ^ 214 = (17 : ZMod 68502634201) ^ (107 + 107) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 107 * (17 : ZMod 68502634201) ^ 107 := by rw [pow_add]
          _ = 34973326526 := by rw [factor_6_6]; decide
      have factor_6_8 : (17 : ZMod 68502634201) ^ 429 = 30837987350 := by
        calc
          (17 : ZMod 68502634201) ^ 429 = (17 : ZMod 68502634201) ^ (214 + 214 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 214 * (17 : ZMod 68502634201) ^ 214) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 30837987350 := by rw [factor_6_7]; decide
      have factor_6_9 : (17 : ZMod 68502634201) ^ 859 = 8121846916 := by
        calc
          (17 : ZMod 68502634201) ^ 859 = (17 : ZMod 68502634201) ^ (429 + 429 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 429 * (17 : ZMod 68502634201) ^ 429) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 8121846916 := by rw [factor_6_8]; decide
      have factor_6_10 : (17 : ZMod 68502634201) ^ 1719 = 57036844529 := by
        calc
          (17 : ZMod 68502634201) ^ 1719 = (17 : ZMod 68502634201) ^ (859 + 859 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 859 * (17 : ZMod 68502634201) ^ 859) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 57036844529 := by rw [factor_6_9]; decide
      have factor_6_11 : (17 : ZMod 68502634201) ^ 3438 = 50238320245 := by
        calc
          (17 : ZMod 68502634201) ^ 3438 = (17 : ZMod 68502634201) ^ (1719 + 1719) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1719 * (17 : ZMod 68502634201) ^ 1719 := by rw [pow_add]
          _ = 50238320245 := by rw [factor_6_10]; decide
      have factor_6_12 : (17 : ZMod 68502634201) ^ 6876 = 26499673389 := by
        calc
          (17 : ZMod 68502634201) ^ 6876 = (17 : ZMod 68502634201) ^ (3438 + 3438) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 3438 * (17 : ZMod 68502634201) ^ 3438 := by rw [pow_add]
          _ = 26499673389 := by rw [factor_6_11]; decide
      have factor_6_13 : (17 : ZMod 68502634201) ^ 13753 = 55750172780 := by
        calc
          (17 : ZMod 68502634201) ^ 13753 = (17 : ZMod 68502634201) ^ (6876 + 6876 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 6876 * (17 : ZMod 68502634201) ^ 6876) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 55750172780 := by rw [factor_6_12]; decide
      have factor_6_14 : (17 : ZMod 68502634201) ^ 27507 = 63406074457 := by
        calc
          (17 : ZMod 68502634201) ^ 27507 = (17 : ZMod 68502634201) ^ (13753 + 13753 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 13753 * (17 : ZMod 68502634201) ^ 13753) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 63406074457 := by rw [factor_6_13]; decide
      have factor_6_15 : (17 : ZMod 68502634201) ^ 55014 = 46275262588 := by
        calc
          (17 : ZMod 68502634201) ^ 55014 = (17 : ZMod 68502634201) ^ (27507 + 27507) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 27507 * (17 : ZMod 68502634201) ^ 27507 := by rw [pow_add]
          _ = 46275262588 := by rw [factor_6_14]; decide
      have factor_6_16 : (17 : ZMod 68502634201) ^ 110028 = 45518017456 := by
        calc
          (17 : ZMod 68502634201) ^ 110028 = (17 : ZMod 68502634201) ^ (55014 + 55014) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 55014 * (17 : ZMod 68502634201) ^ 55014 := by rw [pow_add]
          _ = 45518017456 := by rw [factor_6_15]; decide
      have factor_6_17 : (17 : ZMod 68502634201) ^ 220056 = 66698064564 := by
        calc
          (17 : ZMod 68502634201) ^ 220056 = (17 : ZMod 68502634201) ^ (110028 + 110028) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 110028 * (17 : ZMod 68502634201) ^ 110028 := by rw [pow_add]
          _ = 66698064564 := by rw [factor_6_16]; decide
      have factor_6_18 : (17 : ZMod 68502634201) ^ 440112 = 63393325467 := by
        calc
          (17 : ZMod 68502634201) ^ 440112 = (17 : ZMod 68502634201) ^ (220056 + 220056) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 220056 * (17 : ZMod 68502634201) ^ 220056 := by rw [pow_add]
          _ = 63393325467 := by rw [factor_6_17]; decide
      have factor_6_19 : (17 : ZMod 68502634201) ^ 880225 = 20771372173 := by
        calc
          (17 : ZMod 68502634201) ^ 880225 = (17 : ZMod 68502634201) ^ (440112 + 440112 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 440112 * (17 : ZMod 68502634201) ^ 440112) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 20771372173 := by rw [factor_6_18]; decide
      have factor_6_20 : (17 : ZMod 68502634201) ^ 1760450 = 35313803419 := by
        calc
          (17 : ZMod 68502634201) ^ 1760450 = (17 : ZMod 68502634201) ^ (880225 + 880225) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 880225 * (17 : ZMod 68502634201) ^ 880225 := by rw [pow_add]
          _ = 35313803419 := by rw [factor_6_19]; decide
      have factor_6_21 : (17 : ZMod 68502634201) ^ 3520900 = 56022264768 := by
        calc
          (17 : ZMod 68502634201) ^ 3520900 = (17 : ZMod 68502634201) ^ (1760450 + 1760450) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1760450 * (17 : ZMod 68502634201) ^ 1760450 := by rw [pow_add]
          _ = 56022264768 := by rw [factor_6_20]; decide
      have factor_6_22 : (17 : ZMod 68502634201) ^ 7041800 = 56588175246 := by
        calc
          (17 : ZMod 68502634201) ^ 7041800 = (17 : ZMod 68502634201) ^ (3520900 + 3520900) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 3520900 * (17 : ZMod 68502634201) ^ 3520900 := by rw [pow_add]
          _ = 56588175246 := by rw [factor_6_21]; decide
      have factor_6_23 : (17 : ZMod 68502634201) ^ 14083600 = 9030228097 := by
        calc
          (17 : ZMod 68502634201) ^ 14083600 = (17 : ZMod 68502634201) ^ (7041800 + 7041800) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 7041800 * (17 : ZMod 68502634201) ^ 7041800 := by rw [pow_add]
          _ = 9030228097 := by rw [factor_6_22]; decide
      have factor_6_24 : (17 : ZMod 68502634201) ^ 28167201 = 52619770274 := by
        calc
          (17 : ZMod 68502634201) ^ 28167201 = (17 : ZMod 68502634201) ^ (14083600 + 14083600 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 14083600 * (17 : ZMod 68502634201) ^ 14083600) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 52619770274 := by rw [factor_6_23]; decide
      have factor_6_25 : (17 : ZMod 68502634201) ^ 56334403 = 63192851075 := by
        calc
          (17 : ZMod 68502634201) ^ 56334403 = (17 : ZMod 68502634201) ^ (28167201 + 28167201 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 28167201 * (17 : ZMod 68502634201) ^ 28167201) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 63192851075 := by rw [factor_6_24]; decide
      have factor_6_26 : (17 : ZMod 68502634201) ^ 112668806 = 61102872029 := by
        calc
          (17 : ZMod 68502634201) ^ 112668806 = (17 : ZMod 68502634201) ^ (56334403 + 56334403) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 56334403 * (17 : ZMod 68502634201) ^ 56334403 := by rw [pow_add]
          _ = 61102872029 := by rw [factor_6_25]; decide
      have factor_6_27 : (17 : ZMod 68502634201) ^ 225337612 = 48411246649 := by
        calc
          (17 : ZMod 68502634201) ^ 225337612 = (17 : ZMod 68502634201) ^ (112668806 + 112668806) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 112668806 * (17 : ZMod 68502634201) ^ 112668806 := by rw [pow_add]
          _ = 48411246649 := by rw [factor_6_26]; decide
      have factor_6_28 : (17 : ZMod 68502634201) ^ 450675225 = 38008429497 := by
        calc
          (17 : ZMod 68502634201) ^ 450675225 = (17 : ZMod 68502634201) ^ (225337612 + 225337612 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 225337612 * (17 : ZMod 68502634201) ^ 225337612) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 38008429497 := by rw [factor_6_27]; decide
      have factor_6_29 : (17 : ZMod 68502634201) ^ 901350450 = 21093672348 := by
        calc
          (17 : ZMod 68502634201) ^ 901350450 = (17 : ZMod 68502634201) ^ (450675225 + 450675225) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 450675225 * (17 : ZMod 68502634201) ^ 450675225 := by rw [pow_add]
          _ = 21093672348 := by rw [factor_6_28]; decide
      have factor_6_30 : (17 : ZMod 68502634201) ^ 1802700900 = 3077758243 := by
        calc
          (17 : ZMod 68502634201) ^ 1802700900 = (17 : ZMod 68502634201) ^ (901350450 + 901350450) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 901350450 * (17 : ZMod 68502634201) ^ 901350450 := by rw [pow_add]
          _ = 3077758243 := by rw [factor_6_29]; decide
      have factor_6_31 : (17 : ZMod 68502634201) ^ 3605401800 = 31059247897 := by
        calc
          (17 : ZMod 68502634201) ^ 3605401800 = (17 : ZMod 68502634201) ^ (1802700900 + 1802700900) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1802700900 * (17 : ZMod 68502634201) ^ 1802700900 := by rw [pow_add]
          _ = 31059247897 := by rw [factor_6_30]; decide
      change (17 : ZMod 68502634201) ^ 3605401800 ≠ 1
      rw [factor_6_31]
      decide
    ·
      have factor_7_0 : (17 : ZMod 68502634201) ^ 1 = 17 := by norm_num
      have factor_7_1 : (17 : ZMod 68502634201) ^ 2 = 289 := by
        calc
          (17 : ZMod 68502634201) ^ 2 = (17 : ZMod 68502634201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1 * (17 : ZMod 68502634201) ^ 1 := by rw [pow_add]
          _ = 289 := by rw [factor_7_0]; decide
      have factor_7_2 : (17 : ZMod 68502634201) ^ 5 = 1419857 := by
        calc
          (17 : ZMod 68502634201) ^ 5 = (17 : ZMod 68502634201) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 2 * (17 : ZMod 68502634201) ^ 2) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 1419857 := by rw [factor_7_1]; decide
      have factor_7_3 : (17 : ZMod 68502634201) ^ 11 = 20579207133 := by
        calc
          (17 : ZMod 68502634201) ^ 11 = (17 : ZMod 68502634201) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 5 * (17 : ZMod 68502634201) ^ 5) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 20579207133 := by rw [factor_7_2]; decide
      have factor_7_4 : (17 : ZMod 68502634201) ^ 22 = 58238956900 := by
        calc
          (17 : ZMod 68502634201) ^ 22 = (17 : ZMod 68502634201) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 11 * (17 : ZMod 68502634201) ^ 11 := by rw [pow_add]
          _ = 58238956900 := by rw [factor_7_3]; decide
      have factor_7_5 : (17 : ZMod 68502634201) ^ 44 = 12999213676 := by
        calc
          (17 : ZMod 68502634201) ^ 44 = (17 : ZMod 68502634201) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 22 * (17 : ZMod 68502634201) ^ 22 := by rw [pow_add]
          _ = 12999213676 := by rw [factor_7_4]; decide
      have factor_7_6 : (17 : ZMod 68502634201) ^ 88 = 33715162202 := by
        calc
          (17 : ZMod 68502634201) ^ 88 = (17 : ZMod 68502634201) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 44 * (17 : ZMod 68502634201) ^ 44 := by rw [pow_add]
          _ = 33715162202 := by rw [factor_7_5]; decide
      have factor_7_7 : (17 : ZMod 68502634201) ^ 177 = 25347125579 := by
        calc
          (17 : ZMod 68502634201) ^ 177 = (17 : ZMod 68502634201) ^ (88 + 88 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 88 * (17 : ZMod 68502634201) ^ 88) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 25347125579 := by rw [factor_7_6]; decide
      have factor_7_8 : (17 : ZMod 68502634201) ^ 355 = 38343058361 := by
        calc
          (17 : ZMod 68502634201) ^ 355 = (17 : ZMod 68502634201) ^ (177 + 177 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 177 * (17 : ZMod 68502634201) ^ 177) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 38343058361 := by rw [factor_7_7]; decide
      have factor_7_9 : (17 : ZMod 68502634201) ^ 710 = 13887536091 := by
        calc
          (17 : ZMod 68502634201) ^ 710 = (17 : ZMod 68502634201) ^ (355 + 355) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 355 * (17 : ZMod 68502634201) ^ 355 := by rw [pow_add]
          _ = 13887536091 := by rw [factor_7_8]; decide
      have factor_7_10 : (17 : ZMod 68502634201) ^ 1420 = 40214991686 := by
        calc
          (17 : ZMod 68502634201) ^ 1420 = (17 : ZMod 68502634201) ^ (710 + 710) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 710 * (17 : ZMod 68502634201) ^ 710 := by rw [pow_add]
          _ = 40214991686 := by rw [factor_7_9]; decide
      have factor_7_11 : (17 : ZMod 68502634201) ^ 2840 = 40797877894 := by
        calc
          (17 : ZMod 68502634201) ^ 2840 = (17 : ZMod 68502634201) ^ (1420 + 1420) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1420 * (17 : ZMod 68502634201) ^ 1420 := by rw [pow_add]
          _ = 40797877894 := by rw [factor_7_10]; decide
      have factor_7_12 : (17 : ZMod 68502634201) ^ 5680 = 12227595827 := by
        calc
          (17 : ZMod 68502634201) ^ 5680 = (17 : ZMod 68502634201) ^ (2840 + 2840) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 2840 * (17 : ZMod 68502634201) ^ 2840 := by rw [pow_add]
          _ = 12227595827 := by rw [factor_7_11]; decide
      have factor_7_13 : (17 : ZMod 68502634201) ^ 11361 = 13582607477 := by
        calc
          (17 : ZMod 68502634201) ^ 11361 = (17 : ZMod 68502634201) ^ (5680 + 5680 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 5680 * (17 : ZMod 68502634201) ^ 5680) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 13582607477 := by rw [factor_7_12]; decide
      have factor_7_14 : (17 : ZMod 68502634201) ^ 22723 = 15782322869 := by
        calc
          (17 : ZMod 68502634201) ^ 22723 = (17 : ZMod 68502634201) ^ (11361 + 11361 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 11361 * (17 : ZMod 68502634201) ^ 11361) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 15782322869 := by rw [factor_7_13]; decide
      have factor_7_15 : (17 : ZMod 68502634201) ^ 45446 = 35526323571 := by
        calc
          (17 : ZMod 68502634201) ^ 45446 = (17 : ZMod 68502634201) ^ (22723 + 22723) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 22723 * (17 : ZMod 68502634201) ^ 22723 := by rw [pow_add]
          _ = 35526323571 := by rw [factor_7_14]; decide
      have factor_7_16 : (17 : ZMod 68502634201) ^ 90892 = 58759175941 := by
        calc
          (17 : ZMod 68502634201) ^ 90892 = (17 : ZMod 68502634201) ^ (45446 + 45446) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 45446 * (17 : ZMod 68502634201) ^ 45446 := by rw [pow_add]
          _ = 58759175941 := by rw [factor_7_15]; decide
      have factor_7_17 : (17 : ZMod 68502634201) ^ 181785 = 43550090093 := by
        calc
          (17 : ZMod 68502634201) ^ 181785 = (17 : ZMod 68502634201) ^ (90892 + 90892 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 90892 * (17 : ZMod 68502634201) ^ 90892) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 43550090093 := by rw [factor_7_16]; decide
      have factor_7_18 : (17 : ZMod 68502634201) ^ 363571 = 3635066023 := by
        calc
          (17 : ZMod 68502634201) ^ 363571 = (17 : ZMod 68502634201) ^ (181785 + 181785 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 181785 * (17 : ZMod 68502634201) ^ 181785) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 3635066023 := by rw [factor_7_17]; decide
      have factor_7_19 : (17 : ZMod 68502634201) ^ 727142 = 67624010345 := by
        calc
          (17 : ZMod 68502634201) ^ 727142 = (17 : ZMod 68502634201) ^ (363571 + 363571) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 363571 * (17 : ZMod 68502634201) ^ 363571 := by rw [pow_add]
          _ = 67624010345 := by rw [factor_7_18]; decide
      have factor_7_20 : (17 : ZMod 68502634201) ^ 1454284 = 62112440391 := by
        calc
          (17 : ZMod 68502634201) ^ 1454284 = (17 : ZMod 68502634201) ^ (727142 + 727142) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 727142 * (17 : ZMod 68502634201) ^ 727142 := by rw [pow_add]
          _ = 62112440391 := by rw [factor_7_19]; decide
      have factor_7_21 : (17 : ZMod 68502634201) ^ 2908569 = 8560036217 := by
        calc
          (17 : ZMod 68502634201) ^ 2908569 = (17 : ZMod 68502634201) ^ (1454284 + 1454284 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 1454284 * (17 : ZMod 68502634201) ^ 1454284) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 8560036217 := by rw [factor_7_20]; decide
      have factor_7_22 : (17 : ZMod 68502634201) ^ 5817139 = 40596703265 := by
        calc
          (17 : ZMod 68502634201) ^ 5817139 = (17 : ZMod 68502634201) ^ (2908569 + 2908569 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 2908569 * (17 : ZMod 68502634201) ^ 2908569) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 40596703265 := by rw [factor_7_21]; decide
      have factor_7_23 : (17 : ZMod 68502634201) ^ 11634278 = 45096584580 := by
        calc
          (17 : ZMod 68502634201) ^ 11634278 = (17 : ZMod 68502634201) ^ (5817139 + 5817139) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 5817139 * (17 : ZMod 68502634201) ^ 5817139 := by rw [pow_add]
          _ = 45096584580 := by rw [factor_7_22]; decide
      have factor_7_24 : (17 : ZMod 68502634201) ^ 23268557 = 1746077624 := by
        calc
          (17 : ZMod 68502634201) ^ 23268557 = (17 : ZMod 68502634201) ^ (11634278 + 11634278 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 11634278 * (17 : ZMod 68502634201) ^ 11634278) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 1746077624 := by rw [factor_7_23]; decide
      have factor_7_25 : (17 : ZMod 68502634201) ^ 46537115 = 42552715001 := by
        calc
          (17 : ZMod 68502634201) ^ 46537115 = (17 : ZMod 68502634201) ^ (23268557 + 23268557 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 23268557 * (17 : ZMod 68502634201) ^ 23268557) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 42552715001 := by rw [factor_7_24]; decide
      have factor_7_26 : (17 : ZMod 68502634201) ^ 93074231 = 17146644468 := by
        calc
          (17 : ZMod 68502634201) ^ 93074231 = (17 : ZMod 68502634201) ^ (46537115 + 46537115 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 46537115 * (17 : ZMod 68502634201) ^ 46537115) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 17146644468 := by rw [factor_7_25]; decide
      have factor_7_27 : (17 : ZMod 68502634201) ^ 186148462 = 35278433999 := by
        calc
          (17 : ZMod 68502634201) ^ 186148462 = (17 : ZMod 68502634201) ^ (93074231 + 93074231) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 93074231 * (17 : ZMod 68502634201) ^ 93074231 := by rw [pow_add]
          _ = 35278433999 := by rw [factor_7_26]; decide
      have factor_7_28 : (17 : ZMod 68502634201) ^ 372296925 = 33519001302 := by
        calc
          (17 : ZMod 68502634201) ^ 372296925 = (17 : ZMod 68502634201) ^ (186148462 + 186148462 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 186148462 * (17 : ZMod 68502634201) ^ 186148462) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 33519001302 := by rw [factor_7_27]; decide
      have factor_7_29 : (17 : ZMod 68502634201) ^ 744593850 = 44745567955 := by
        calc
          (17 : ZMod 68502634201) ^ 744593850 = (17 : ZMod 68502634201) ^ (372296925 + 372296925) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 372296925 * (17 : ZMod 68502634201) ^ 372296925 := by rw [pow_add]
          _ = 44745567955 := by rw [factor_7_28]; decide
      have factor_7_30 : (17 : ZMod 68502634201) ^ 1489187700 = 3776084822 := by
        calc
          (17 : ZMod 68502634201) ^ 1489187700 = (17 : ZMod 68502634201) ^ (744593850 + 744593850) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 744593850 * (17 : ZMod 68502634201) ^ 744593850 := by rw [pow_add]
          _ = 3776084822 := by rw [factor_7_29]; decide
      have factor_7_31 : (17 : ZMod 68502634201) ^ 2978375400 = 55761407583 := by
        calc
          (17 : ZMod 68502634201) ^ 2978375400 = (17 : ZMod 68502634201) ^ (1489187700 + 1489187700) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1489187700 * (17 : ZMod 68502634201) ^ 1489187700 := by rw [pow_add]
          _ = 55761407583 := by rw [factor_7_30]; decide
      change (17 : ZMod 68502634201) ^ 2978375400 ≠ 1
      rw [factor_7_31]
      decide
    ·
      have factor_8_0 : (17 : ZMod 68502634201) ^ 1 = 17 := by norm_num
      have factor_8_1 : (17 : ZMod 68502634201) ^ 2 = 289 := by
        calc
          (17 : ZMod 68502634201) ^ 2 = (17 : ZMod 68502634201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1 * (17 : ZMod 68502634201) ^ 1 := by rw [pow_add]
          _ = 289 := by rw [factor_8_0]; decide
      have factor_8_2 : (17 : ZMod 68502634201) ^ 4 = 83521 := by
        calc
          (17 : ZMod 68502634201) ^ 4 = (17 : ZMod 68502634201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 2 * (17 : ZMod 68502634201) ^ 2 := by rw [pow_add]
          _ = 83521 := by rw [factor_8_1]; decide
      have factor_8_3 : (17 : ZMod 68502634201) ^ 8 = 6975757441 := by
        calc
          (17 : ZMod 68502634201) ^ 8 = (17 : ZMod 68502634201) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 4 * (17 : ZMod 68502634201) ^ 4 := by rw [pow_add]
          _ = 6975757441 := by rw [factor_8_2]; decide
      have factor_8_4 : (17 : ZMod 68502634201) ^ 17 = 45301149794 := by
        calc
          (17 : ZMod 68502634201) ^ 17 = (17 : ZMod 68502634201) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 8 * (17 : ZMod 68502634201) ^ 8) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 45301149794 := by rw [factor_8_3]; decide
      have factor_8_5 : (17 : ZMod 68502634201) ^ 35 = 12827293093 := by
        calc
          (17 : ZMod 68502634201) ^ 35 = (17 : ZMod 68502634201) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 17 * (17 : ZMod 68502634201) ^ 17) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 12827293093 := by rw [factor_8_4]; decide
      have factor_8_6 : (17 : ZMod 68502634201) ^ 70 = 47098309279 := by
        calc
          (17 : ZMod 68502634201) ^ 70 = (17 : ZMod 68502634201) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 35 * (17 : ZMod 68502634201) ^ 35 := by rw [pow_add]
          _ = 47098309279 := by rw [factor_8_5]; decide
      have factor_8_7 : (17 : ZMod 68502634201) ^ 140 = 21689040269 := by
        calc
          (17 : ZMod 68502634201) ^ 140 = (17 : ZMod 68502634201) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 70 * (17 : ZMod 68502634201) ^ 70 := by rw [pow_add]
          _ = 21689040269 := by rw [factor_8_6]; decide
      have factor_8_8 : (17 : ZMod 68502634201) ^ 281 = 63872374273 := by
        calc
          (17 : ZMod 68502634201) ^ 281 = (17 : ZMod 68502634201) ^ (140 + 140 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 140 * (17 : ZMod 68502634201) ^ 140) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 63872374273 := by rw [factor_8_7]; decide
      have factor_8_9 : (17 : ZMod 68502634201) ^ 563 = 55683828004 := by
        calc
          (17 : ZMod 68502634201) ^ 563 = (17 : ZMod 68502634201) ^ (281 + 281 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 281 * (17 : ZMod 68502634201) ^ 281) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 55683828004 := by rw [factor_8_8]; decide
      have factor_8_10 : (17 : ZMod 68502634201) ^ 1126 = 18354805573 := by
        calc
          (17 : ZMod 68502634201) ^ 1126 = (17 : ZMod 68502634201) ^ (563 + 563) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 563 * (17 : ZMod 68502634201) ^ 563 := by rw [pow_add]
          _ = 18354805573 := by rw [factor_8_9]; decide
      have factor_8_11 : (17 : ZMod 68502634201) ^ 2252 = 24343713519 := by
        calc
          (17 : ZMod 68502634201) ^ 2252 = (17 : ZMod 68502634201) ^ (1126 + 1126) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1126 * (17 : ZMod 68502634201) ^ 1126 := by rw [pow_add]
          _ = 24343713519 := by rw [factor_8_10]; decide
      have factor_8_12 : (17 : ZMod 68502634201) ^ 4505 = 13476535864 := by
        calc
          (17 : ZMod 68502634201) ^ 4505 = (17 : ZMod 68502634201) ^ (2252 + 2252 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 2252 * (17 : ZMod 68502634201) ^ 2252) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 13476535864 := by rw [factor_8_11]; decide
      have factor_8_13 : (17 : ZMod 68502634201) ^ 9010 = 49967983910 := by
        calc
          (17 : ZMod 68502634201) ^ 9010 = (17 : ZMod 68502634201) ^ (4505 + 4505) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 4505 * (17 : ZMod 68502634201) ^ 4505 := by rw [pow_add]
          _ = 49967983910 := by rw [factor_8_12]; decide
      have factor_8_14 : (17 : ZMod 68502634201) ^ 18021 = 18191752790 := by
        calc
          (17 : ZMod 68502634201) ^ 18021 = (17 : ZMod 68502634201) ^ (9010 + 9010 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 9010 * (17 : ZMod 68502634201) ^ 9010) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 18191752790 := by rw [factor_8_13]; decide
      have factor_8_15 : (17 : ZMod 68502634201) ^ 36043 = 62528807048 := by
        calc
          (17 : ZMod 68502634201) ^ 36043 = (17 : ZMod 68502634201) ^ (18021 + 18021 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 18021 * (17 : ZMod 68502634201) ^ 18021) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 62528807048 := by rw [factor_8_14]; decide
      have factor_8_16 : (17 : ZMod 68502634201) ^ 72087 = 47030449162 := by
        calc
          (17 : ZMod 68502634201) ^ 72087 = (17 : ZMod 68502634201) ^ (36043 + 36043 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 36043 * (17 : ZMod 68502634201) ^ 36043) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 47030449162 := by rw [factor_8_15]; decide
      have factor_8_17 : (17 : ZMod 68502634201) ^ 144174 = 6213652954 := by
        calc
          (17 : ZMod 68502634201) ^ 144174 = (17 : ZMod 68502634201) ^ (72087 + 72087) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 72087 * (17 : ZMod 68502634201) ^ 72087 := by rw [pow_add]
          _ = 6213652954 := by rw [factor_8_16]; decide
      have factor_8_18 : (17 : ZMod 68502634201) ^ 288349 = 7021234138 := by
        calc
          (17 : ZMod 68502634201) ^ 288349 = (17 : ZMod 68502634201) ^ (144174 + 144174 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 144174 * (17 : ZMod 68502634201) ^ 144174) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 7021234138 := by rw [factor_8_17]; decide
      have factor_8_19 : (17 : ZMod 68502634201) ^ 576699 = 30676219167 := by
        calc
          (17 : ZMod 68502634201) ^ 576699 = (17 : ZMod 68502634201) ^ (288349 + 288349 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 288349 * (17 : ZMod 68502634201) ^ 288349) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 30676219167 := by rw [factor_8_18]; decide
      have factor_8_20 : (17 : ZMod 68502634201) ^ 1153398 = 14779551558 := by
        calc
          (17 : ZMod 68502634201) ^ 1153398 = (17 : ZMod 68502634201) ^ (576699 + 576699) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 576699 * (17 : ZMod 68502634201) ^ 576699 := by rw [pow_add]
          _ = 14779551558 := by rw [factor_8_19]; decide
      have factor_8_21 : (17 : ZMod 68502634201) ^ 2306796 = 16797429965 := by
        calc
          (17 : ZMod 68502634201) ^ 2306796 = (17 : ZMod 68502634201) ^ (1153398 + 1153398) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1153398 * (17 : ZMod 68502634201) ^ 1153398 := by rw [pow_add]
          _ = 16797429965 := by rw [factor_8_20]; decide
      have factor_8_22 : (17 : ZMod 68502634201) ^ 4613593 = 64523336884 := by
        calc
          (17 : ZMod 68502634201) ^ 4613593 = (17 : ZMod 68502634201) ^ (2306796 + 2306796 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 2306796 * (17 : ZMod 68502634201) ^ 2306796) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 64523336884 := by rw [factor_8_21]; decide
      have factor_8_23 : (17 : ZMod 68502634201) ^ 9227186 = 32248154711 := by
        calc
          (17 : ZMod 68502634201) ^ 9227186 = (17 : ZMod 68502634201) ^ (4613593 + 4613593) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 4613593 * (17 : ZMod 68502634201) ^ 4613593 := by rw [pow_add]
          _ = 32248154711 := by rw [factor_8_22]; decide
      have factor_8_24 : (17 : ZMod 68502634201) ^ 18454373 = 56919255701 := by
        calc
          (17 : ZMod 68502634201) ^ 18454373 = (17 : ZMod 68502634201) ^ (9227186 + 9227186 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 9227186 * (17 : ZMod 68502634201) ^ 9227186) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 56919255701 := by rw [factor_8_23]; decide
      have factor_8_25 : (17 : ZMod 68502634201) ^ 36908746 = 52105976999 := by
        calc
          (17 : ZMod 68502634201) ^ 36908746 = (17 : ZMod 68502634201) ^ (18454373 + 18454373) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 18454373 * (17 : ZMod 68502634201) ^ 18454373 := by rw [pow_add]
          _ = 52105976999 := by rw [factor_8_24]; decide
      have factor_8_26 : (17 : ZMod 68502634201) ^ 73817493 = 48300420207 := by
        calc
          (17 : ZMod 68502634201) ^ 73817493 = (17 : ZMod 68502634201) ^ (36908746 + 36908746 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 36908746 * (17 : ZMod 68502634201) ^ 36908746) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 48300420207 := by rw [factor_8_25]; decide
      have factor_8_27 : (17 : ZMod 68502634201) ^ 147634987 = 58470176933 := by
        calc
          (17 : ZMod 68502634201) ^ 147634987 = (17 : ZMod 68502634201) ^ (73817493 + 73817493 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 73817493 * (17 : ZMod 68502634201) ^ 73817493) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 58470176933 := by rw [factor_8_26]; decide
      have factor_8_28 : (17 : ZMod 68502634201) ^ 295269975 = 23906483284 := by
        calc
          (17 : ZMod 68502634201) ^ 295269975 = (17 : ZMod 68502634201) ^ (147634987 + 147634987 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = ((17 : ZMod 68502634201) ^ 147634987 * (17 : ZMod 68502634201) ^ 147634987) * (17 : ZMod 68502634201) := by rw [pow_succ, pow_add]
          _ = 23906483284 := by rw [factor_8_27]; decide
      have factor_8_29 : (17 : ZMod 68502634201) ^ 590539950 = 48407725460 := by
        calc
          (17 : ZMod 68502634201) ^ 590539950 = (17 : ZMod 68502634201) ^ (295269975 + 295269975) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 295269975 * (17 : ZMod 68502634201) ^ 295269975 := by rw [pow_add]
          _ = 48407725460 := by rw [factor_8_28]; decide
      have factor_8_30 : (17 : ZMod 68502634201) ^ 1181079900 = 44757500247 := by
        calc
          (17 : ZMod 68502634201) ^ 1181079900 = (17 : ZMod 68502634201) ^ (590539950 + 590539950) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 590539950 * (17 : ZMod 68502634201) ^ 590539950 := by rw [pow_add]
          _ = 44757500247 := by rw [factor_8_29]; decide
      have factor_8_31 : (17 : ZMod 68502634201) ^ 2362159800 = 61971779305 := by
        calc
          (17 : ZMod 68502634201) ^ 2362159800 = (17 : ZMod 68502634201) ^ (1181079900 + 1181079900) :=
            congrArg (fun n : ℕ => (17 : ZMod 68502634201) ^ n) (by norm_num)
          _ = (17 : ZMod 68502634201) ^ 1181079900 * (17 : ZMod 68502634201) ^ 1181079900 := by rw [pow_add]
          _ = 61971779305 := by rw [factor_8_30]; decide
      change (17 : ZMod 68502634201) ^ 2362159800 ≠ 1
      rw [factor_8_31]
      decide

#print axioms prime_lucas_68502634201

end TotientTailPeriodKiller
end Erdos249257
