import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_274010536801 : Nat.Prime 274010536801 := by
  apply lucas_primality 274010536801 (79 : ZMod 274010536801)
  ·
      have fermat_0 : (79 : ZMod 274010536801) ^ 1 = 79 := by norm_num
      have fermat_1 : (79 : ZMod 274010536801) ^ 3 = 493039 := by
        calc
          (79 : ZMod 274010536801) ^ 3 = (79 : ZMod 274010536801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 1 * (79 : ZMod 274010536801) ^ 1) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 493039 := by rw [fermat_0]; decide
      have fermat_2 : (79 : ZMod 274010536801) ^ 7 = 23171410089 := by
        calc
          (79 : ZMod 274010536801) ^ 7 = (79 : ZMod 274010536801) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 3 * (79 : ZMod 274010536801) ^ 3) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 23171410089 := by rw [fermat_1]; decide
      have fermat_3 : (79 : ZMod 274010536801) ^ 15 = 89108803463 := by
        calc
          (79 : ZMod 274010536801) ^ 15 = (79 : ZMod 274010536801) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 7 * (79 : ZMod 274010536801) ^ 7) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 89108803463 := by rw [fermat_2]; decide
      have fermat_4 : (79 : ZMod 274010536801) ^ 31 = 94759444146 := by
        calc
          (79 : ZMod 274010536801) ^ 31 = (79 : ZMod 274010536801) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 15 * (79 : ZMod 274010536801) ^ 15) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 94759444146 := by rw [fermat_3]; decide
      have fermat_5 : (79 : ZMod 274010536801) ^ 63 = 93089837203 := by
        calc
          (79 : ZMod 274010536801) ^ 63 = (79 : ZMod 274010536801) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 31 * (79 : ZMod 274010536801) ^ 31) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 93089837203 := by rw [fermat_4]; decide
      have fermat_6 : (79 : ZMod 274010536801) ^ 127 = 216172237311 := by
        calc
          (79 : ZMod 274010536801) ^ 127 = (79 : ZMod 274010536801) ^ (63 + 63 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 63 * (79 : ZMod 274010536801) ^ 63) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 216172237311 := by rw [fermat_5]; decide
      have fermat_7 : (79 : ZMod 274010536801) ^ 255 = 238096754197 := by
        calc
          (79 : ZMod 274010536801) ^ 255 = (79 : ZMod 274010536801) ^ (127 + 127 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 127 * (79 : ZMod 274010536801) ^ 127) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 238096754197 := by rw [fermat_6]; decide
      have fermat_8 : (79 : ZMod 274010536801) ^ 510 = 23455522560 := by
        calc
          (79 : ZMod 274010536801) ^ 510 = (79 : ZMod 274010536801) ^ (255 + 255) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 255 * (79 : ZMod 274010536801) ^ 255 := by rw [pow_add]
          _ = 23455522560 := by rw [fermat_7]; decide
      have fermat_9 : (79 : ZMod 274010536801) ^ 1020 = 141236209985 := by
        calc
          (79 : ZMod 274010536801) ^ 1020 = (79 : ZMod 274010536801) ^ (510 + 510) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 510 * (79 : ZMod 274010536801) ^ 510 := by rw [pow_add]
          _ = 141236209985 := by rw [fermat_8]; decide
      have fermat_10 : (79 : ZMod 274010536801) ^ 2041 = 31807064858 := by
        calc
          (79 : ZMod 274010536801) ^ 2041 = (79 : ZMod 274010536801) ^ (1020 + 1020 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 1020 * (79 : ZMod 274010536801) ^ 1020) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 31807064858 := by rw [fermat_9]; decide
      have fermat_11 : (79 : ZMod 274010536801) ^ 4083 = 121086897959 := by
        calc
          (79 : ZMod 274010536801) ^ 4083 = (79 : ZMod 274010536801) ^ (2041 + 2041 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 2041 * (79 : ZMod 274010536801) ^ 2041) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 121086897959 := by rw [fermat_10]; decide
      have fermat_12 : (79 : ZMod 274010536801) ^ 8166 = 207720895976 := by
        calc
          (79 : ZMod 274010536801) ^ 8166 = (79 : ZMod 274010536801) ^ (4083 + 4083) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 4083 * (79 : ZMod 274010536801) ^ 4083 := by rw [pow_add]
          _ = 207720895976 := by rw [fermat_11]; decide
      have fermat_13 : (79 : ZMod 274010536801) ^ 16332 = 166485032348 := by
        calc
          (79 : ZMod 274010536801) ^ 16332 = (79 : ZMod 274010536801) ^ (8166 + 8166) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 8166 * (79 : ZMod 274010536801) ^ 8166 := by rw [pow_add]
          _ = 166485032348 := by rw [fermat_12]; decide
      have fermat_14 : (79 : ZMod 274010536801) ^ 32664 = 154430195536 := by
        calc
          (79 : ZMod 274010536801) ^ 32664 = (79 : ZMod 274010536801) ^ (16332 + 16332) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 16332 * (79 : ZMod 274010536801) ^ 16332 := by rw [pow_add]
          _ = 154430195536 := by rw [fermat_13]; decide
      have fermat_15 : (79 : ZMod 274010536801) ^ 65329 = 101578638551 := by
        calc
          (79 : ZMod 274010536801) ^ 65329 = (79 : ZMod 274010536801) ^ (32664 + 32664 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 32664 * (79 : ZMod 274010536801) ^ 32664) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 101578638551 := by rw [fermat_14]; decide
      have fermat_16 : (79 : ZMod 274010536801) ^ 130658 = 223001962360 := by
        calc
          (79 : ZMod 274010536801) ^ 130658 = (79 : ZMod 274010536801) ^ (65329 + 65329) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 65329 * (79 : ZMod 274010536801) ^ 65329 := by rw [pow_add]
          _ = 223001962360 := by rw [fermat_15]; decide
      have fermat_17 : (79 : ZMod 274010536801) ^ 261316 = 104346336293 := by
        calc
          (79 : ZMod 274010536801) ^ 261316 = (79 : ZMod 274010536801) ^ (130658 + 130658) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 130658 * (79 : ZMod 274010536801) ^ 130658 := by rw [pow_add]
          _ = 104346336293 := by rw [fermat_16]; decide
      have fermat_18 : (79 : ZMod 274010536801) ^ 522633 = 57584591006 := by
        calc
          (79 : ZMod 274010536801) ^ 522633 = (79 : ZMod 274010536801) ^ (261316 + 261316 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 261316 * (79 : ZMod 274010536801) ^ 261316) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 57584591006 := by rw [fermat_17]; decide
      have fermat_19 : (79 : ZMod 274010536801) ^ 1045267 = 126944109445 := by
        calc
          (79 : ZMod 274010536801) ^ 1045267 = (79 : ZMod 274010536801) ^ (522633 + 522633 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 522633 * (79 : ZMod 274010536801) ^ 522633) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 126944109445 := by rw [fermat_18]; decide
      have fermat_20 : (79 : ZMod 274010536801) ^ 2090534 = 109445825675 := by
        calc
          (79 : ZMod 274010536801) ^ 2090534 = (79 : ZMod 274010536801) ^ (1045267 + 1045267) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1045267 * (79 : ZMod 274010536801) ^ 1045267 := by rw [pow_add]
          _ = 109445825675 := by rw [fermat_19]; decide
      have fermat_21 : (79 : ZMod 274010536801) ^ 4181068 = 11164221818 := by
        calc
          (79 : ZMod 274010536801) ^ 4181068 = (79 : ZMod 274010536801) ^ (2090534 + 2090534) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 2090534 * (79 : ZMod 274010536801) ^ 2090534 := by rw [pow_add]
          _ = 11164221818 := by rw [fermat_20]; decide
      have fermat_22 : (79 : ZMod 274010536801) ^ 8362137 = 142702423120 := by
        calc
          (79 : ZMod 274010536801) ^ 8362137 = (79 : ZMod 274010536801) ^ (4181068 + 4181068 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 4181068 * (79 : ZMod 274010536801) ^ 4181068) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 142702423120 := by rw [fermat_21]; decide
      have fermat_23 : (79 : ZMod 274010536801) ^ 16724275 = 27863082964 := by
        calc
          (79 : ZMod 274010536801) ^ 16724275 = (79 : ZMod 274010536801) ^ (8362137 + 8362137 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 8362137 * (79 : ZMod 274010536801) ^ 8362137) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 27863082964 := by rw [fermat_22]; decide
      have fermat_24 : (79 : ZMod 274010536801) ^ 33448551 = 199196796968 := by
        calc
          (79 : ZMod 274010536801) ^ 33448551 = (79 : ZMod 274010536801) ^ (16724275 + 16724275 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 16724275 * (79 : ZMod 274010536801) ^ 16724275) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 199196796968 := by rw [fermat_23]; decide
      have fermat_25 : (79 : ZMod 274010536801) ^ 66897103 = 149036232708 := by
        calc
          (79 : ZMod 274010536801) ^ 66897103 = (79 : ZMod 274010536801) ^ (33448551 + 33448551 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 33448551 * (79 : ZMod 274010536801) ^ 33448551) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 149036232708 := by rw [fermat_24]; decide
      have fermat_26 : (79 : ZMod 274010536801) ^ 133794207 = 2200925155 := by
        calc
          (79 : ZMod 274010536801) ^ 133794207 = (79 : ZMod 274010536801) ^ (66897103 + 66897103 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 66897103 * (79 : ZMod 274010536801) ^ 66897103) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 2200925155 := by rw [fermat_25]; decide
      have fermat_27 : (79 : ZMod 274010536801) ^ 267588414 = 101991997212 := by
        calc
          (79 : ZMod 274010536801) ^ 267588414 = (79 : ZMod 274010536801) ^ (133794207 + 133794207) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 133794207 * (79 : ZMod 274010536801) ^ 133794207 := by rw [pow_add]
          _ = 101991997212 := by rw [fermat_26]; decide
      have fermat_28 : (79 : ZMod 274010536801) ^ 535176829 = 187473055293 := by
        calc
          (79 : ZMod 274010536801) ^ 535176829 = (79 : ZMod 274010536801) ^ (267588414 + 267588414 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 267588414 * (79 : ZMod 274010536801) ^ 267588414) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 187473055293 := by rw [fermat_27]; decide
      have fermat_29 : (79 : ZMod 274010536801) ^ 1070353659 = 55707028383 := by
        calc
          (79 : ZMod 274010536801) ^ 1070353659 = (79 : ZMod 274010536801) ^ (535176829 + 535176829 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 535176829 * (79 : ZMod 274010536801) ^ 535176829) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 55707028383 := by rw [fermat_28]; decide
      have fermat_30 : (79 : ZMod 274010536801) ^ 2140707318 = 242064611503 := by
        calc
          (79 : ZMod 274010536801) ^ 2140707318 = (79 : ZMod 274010536801) ^ (1070353659 + 1070353659) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1070353659 * (79 : ZMod 274010536801) ^ 1070353659 := by rw [pow_add]
          _ = 242064611503 := by rw [fermat_29]; decide
      have fermat_31 : (79 : ZMod 274010536801) ^ 4281414637 = 241688663786 := by
        calc
          (79 : ZMod 274010536801) ^ 4281414637 = (79 : ZMod 274010536801) ^ (2140707318 + 2140707318 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 2140707318 * (79 : ZMod 274010536801) ^ 2140707318) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 241688663786 := by rw [fermat_30]; decide
      have fermat_32 : (79 : ZMod 274010536801) ^ 8562829275 = 188514087649 := by
        calc
          (79 : ZMod 274010536801) ^ 8562829275 = (79 : ZMod 274010536801) ^ (4281414637 + 4281414637 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 4281414637 * (79 : ZMod 274010536801) ^ 4281414637) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 188514087649 := by rw [fermat_31]; decide
      have fermat_33 : (79 : ZMod 274010536801) ^ 17125658550 = 198480150031 := by
        calc
          (79 : ZMod 274010536801) ^ 17125658550 = (79 : ZMod 274010536801) ^ (8562829275 + 8562829275) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 8562829275 * (79 : ZMod 274010536801) ^ 8562829275 := by rw [pow_add]
          _ = 198480150031 := by rw [fermat_32]; decide
      have fermat_34 : (79 : ZMod 274010536801) ^ 34251317100 = 208163656055 := by
        calc
          (79 : ZMod 274010536801) ^ 34251317100 = (79 : ZMod 274010536801) ^ (17125658550 + 17125658550) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 17125658550 * (79 : ZMod 274010536801) ^ 17125658550 := by rw [pow_add]
          _ = 208163656055 := by rw [fermat_33]; decide
      have fermat_35 : (79 : ZMod 274010536801) ^ 68502634200 = 107567070711 := by
        calc
          (79 : ZMod 274010536801) ^ 68502634200 = (79 : ZMod 274010536801) ^ (34251317100 + 34251317100) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 34251317100 * (79 : ZMod 274010536801) ^ 34251317100 := by rw [pow_add]
          _ = 107567070711 := by rw [fermat_34]; decide
      have fermat_36 : (79 : ZMod 274010536801) ^ 137005268400 = 274010536800 := by
        calc
          (79 : ZMod 274010536801) ^ 137005268400 = (79 : ZMod 274010536801) ^ (68502634200 + 68502634200) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 68502634200 * (79 : ZMod 274010536801) ^ 68502634200 := by rw [pow_add]
          _ = 274010536800 := by rw [fermat_35]; decide
      have fermat_37 : (79 : ZMod 274010536801) ^ 274010536800 = 1 := by
        calc
          (79 : ZMod 274010536801) ^ 274010536800 = (79 : ZMod 274010536801) ^ (137005268400 + 137005268400) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 137005268400 * (79 : ZMod 274010536801) ^ 137005268400 := by rw [pow_add]
          _ = 1 := by rw [fermat_36]; decide
      simpa using fermat_37
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod = 274010536801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (79 : ZMod 274010536801) ^ 1 = 79 := by norm_num
      have factor_0_1 : (79 : ZMod 274010536801) ^ 3 = 493039 := by
        calc
          (79 : ZMod 274010536801) ^ 3 = (79 : ZMod 274010536801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 1 * (79 : ZMod 274010536801) ^ 1) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 493039 := by rw [factor_0_0]; decide
      have factor_0_2 : (79 : ZMod 274010536801) ^ 7 = 23171410089 := by
        calc
          (79 : ZMod 274010536801) ^ 7 = (79 : ZMod 274010536801) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 3 * (79 : ZMod 274010536801) ^ 3) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 23171410089 := by rw [factor_0_1]; decide
      have factor_0_3 : (79 : ZMod 274010536801) ^ 15 = 89108803463 := by
        calc
          (79 : ZMod 274010536801) ^ 15 = (79 : ZMod 274010536801) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 7 * (79 : ZMod 274010536801) ^ 7) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 89108803463 := by rw [factor_0_2]; decide
      have factor_0_4 : (79 : ZMod 274010536801) ^ 31 = 94759444146 := by
        calc
          (79 : ZMod 274010536801) ^ 31 = (79 : ZMod 274010536801) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 15 * (79 : ZMod 274010536801) ^ 15) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 94759444146 := by rw [factor_0_3]; decide
      have factor_0_5 : (79 : ZMod 274010536801) ^ 63 = 93089837203 := by
        calc
          (79 : ZMod 274010536801) ^ 63 = (79 : ZMod 274010536801) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 31 * (79 : ZMod 274010536801) ^ 31) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 93089837203 := by rw [factor_0_4]; decide
      have factor_0_6 : (79 : ZMod 274010536801) ^ 127 = 216172237311 := by
        calc
          (79 : ZMod 274010536801) ^ 127 = (79 : ZMod 274010536801) ^ (63 + 63 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 63 * (79 : ZMod 274010536801) ^ 63) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 216172237311 := by rw [factor_0_5]; decide
      have factor_0_7 : (79 : ZMod 274010536801) ^ 255 = 238096754197 := by
        calc
          (79 : ZMod 274010536801) ^ 255 = (79 : ZMod 274010536801) ^ (127 + 127 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 127 * (79 : ZMod 274010536801) ^ 127) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 238096754197 := by rw [factor_0_6]; decide
      have factor_0_8 : (79 : ZMod 274010536801) ^ 510 = 23455522560 := by
        calc
          (79 : ZMod 274010536801) ^ 510 = (79 : ZMod 274010536801) ^ (255 + 255) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 255 * (79 : ZMod 274010536801) ^ 255 := by rw [pow_add]
          _ = 23455522560 := by rw [factor_0_7]; decide
      have factor_0_9 : (79 : ZMod 274010536801) ^ 1020 = 141236209985 := by
        calc
          (79 : ZMod 274010536801) ^ 1020 = (79 : ZMod 274010536801) ^ (510 + 510) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 510 * (79 : ZMod 274010536801) ^ 510 := by rw [pow_add]
          _ = 141236209985 := by rw [factor_0_8]; decide
      have factor_0_10 : (79 : ZMod 274010536801) ^ 2041 = 31807064858 := by
        calc
          (79 : ZMod 274010536801) ^ 2041 = (79 : ZMod 274010536801) ^ (1020 + 1020 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 1020 * (79 : ZMod 274010536801) ^ 1020) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 31807064858 := by rw [factor_0_9]; decide
      have factor_0_11 : (79 : ZMod 274010536801) ^ 4083 = 121086897959 := by
        calc
          (79 : ZMod 274010536801) ^ 4083 = (79 : ZMod 274010536801) ^ (2041 + 2041 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 2041 * (79 : ZMod 274010536801) ^ 2041) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 121086897959 := by rw [factor_0_10]; decide
      have factor_0_12 : (79 : ZMod 274010536801) ^ 8166 = 207720895976 := by
        calc
          (79 : ZMod 274010536801) ^ 8166 = (79 : ZMod 274010536801) ^ (4083 + 4083) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 4083 * (79 : ZMod 274010536801) ^ 4083 := by rw [pow_add]
          _ = 207720895976 := by rw [factor_0_11]; decide
      have factor_0_13 : (79 : ZMod 274010536801) ^ 16332 = 166485032348 := by
        calc
          (79 : ZMod 274010536801) ^ 16332 = (79 : ZMod 274010536801) ^ (8166 + 8166) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 8166 * (79 : ZMod 274010536801) ^ 8166 := by rw [pow_add]
          _ = 166485032348 := by rw [factor_0_12]; decide
      have factor_0_14 : (79 : ZMod 274010536801) ^ 32664 = 154430195536 := by
        calc
          (79 : ZMod 274010536801) ^ 32664 = (79 : ZMod 274010536801) ^ (16332 + 16332) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 16332 * (79 : ZMod 274010536801) ^ 16332 := by rw [pow_add]
          _ = 154430195536 := by rw [factor_0_13]; decide
      have factor_0_15 : (79 : ZMod 274010536801) ^ 65329 = 101578638551 := by
        calc
          (79 : ZMod 274010536801) ^ 65329 = (79 : ZMod 274010536801) ^ (32664 + 32664 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 32664 * (79 : ZMod 274010536801) ^ 32664) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 101578638551 := by rw [factor_0_14]; decide
      have factor_0_16 : (79 : ZMod 274010536801) ^ 130658 = 223001962360 := by
        calc
          (79 : ZMod 274010536801) ^ 130658 = (79 : ZMod 274010536801) ^ (65329 + 65329) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 65329 * (79 : ZMod 274010536801) ^ 65329 := by rw [pow_add]
          _ = 223001962360 := by rw [factor_0_15]; decide
      have factor_0_17 : (79 : ZMod 274010536801) ^ 261316 = 104346336293 := by
        calc
          (79 : ZMod 274010536801) ^ 261316 = (79 : ZMod 274010536801) ^ (130658 + 130658) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 130658 * (79 : ZMod 274010536801) ^ 130658 := by rw [pow_add]
          _ = 104346336293 := by rw [factor_0_16]; decide
      have factor_0_18 : (79 : ZMod 274010536801) ^ 522633 = 57584591006 := by
        calc
          (79 : ZMod 274010536801) ^ 522633 = (79 : ZMod 274010536801) ^ (261316 + 261316 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 261316 * (79 : ZMod 274010536801) ^ 261316) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 57584591006 := by rw [factor_0_17]; decide
      have factor_0_19 : (79 : ZMod 274010536801) ^ 1045267 = 126944109445 := by
        calc
          (79 : ZMod 274010536801) ^ 1045267 = (79 : ZMod 274010536801) ^ (522633 + 522633 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 522633 * (79 : ZMod 274010536801) ^ 522633) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 126944109445 := by rw [factor_0_18]; decide
      have factor_0_20 : (79 : ZMod 274010536801) ^ 2090534 = 109445825675 := by
        calc
          (79 : ZMod 274010536801) ^ 2090534 = (79 : ZMod 274010536801) ^ (1045267 + 1045267) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1045267 * (79 : ZMod 274010536801) ^ 1045267 := by rw [pow_add]
          _ = 109445825675 := by rw [factor_0_19]; decide
      have factor_0_21 : (79 : ZMod 274010536801) ^ 4181068 = 11164221818 := by
        calc
          (79 : ZMod 274010536801) ^ 4181068 = (79 : ZMod 274010536801) ^ (2090534 + 2090534) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 2090534 * (79 : ZMod 274010536801) ^ 2090534 := by rw [pow_add]
          _ = 11164221818 := by rw [factor_0_20]; decide
      have factor_0_22 : (79 : ZMod 274010536801) ^ 8362137 = 142702423120 := by
        calc
          (79 : ZMod 274010536801) ^ 8362137 = (79 : ZMod 274010536801) ^ (4181068 + 4181068 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 4181068 * (79 : ZMod 274010536801) ^ 4181068) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 142702423120 := by rw [factor_0_21]; decide
      have factor_0_23 : (79 : ZMod 274010536801) ^ 16724275 = 27863082964 := by
        calc
          (79 : ZMod 274010536801) ^ 16724275 = (79 : ZMod 274010536801) ^ (8362137 + 8362137 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 8362137 * (79 : ZMod 274010536801) ^ 8362137) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 27863082964 := by rw [factor_0_22]; decide
      have factor_0_24 : (79 : ZMod 274010536801) ^ 33448551 = 199196796968 := by
        calc
          (79 : ZMod 274010536801) ^ 33448551 = (79 : ZMod 274010536801) ^ (16724275 + 16724275 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 16724275 * (79 : ZMod 274010536801) ^ 16724275) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 199196796968 := by rw [factor_0_23]; decide
      have factor_0_25 : (79 : ZMod 274010536801) ^ 66897103 = 149036232708 := by
        calc
          (79 : ZMod 274010536801) ^ 66897103 = (79 : ZMod 274010536801) ^ (33448551 + 33448551 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 33448551 * (79 : ZMod 274010536801) ^ 33448551) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 149036232708 := by rw [factor_0_24]; decide
      have factor_0_26 : (79 : ZMod 274010536801) ^ 133794207 = 2200925155 := by
        calc
          (79 : ZMod 274010536801) ^ 133794207 = (79 : ZMod 274010536801) ^ (66897103 + 66897103 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 66897103 * (79 : ZMod 274010536801) ^ 66897103) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 2200925155 := by rw [factor_0_25]; decide
      have factor_0_27 : (79 : ZMod 274010536801) ^ 267588414 = 101991997212 := by
        calc
          (79 : ZMod 274010536801) ^ 267588414 = (79 : ZMod 274010536801) ^ (133794207 + 133794207) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 133794207 * (79 : ZMod 274010536801) ^ 133794207 := by rw [pow_add]
          _ = 101991997212 := by rw [factor_0_26]; decide
      have factor_0_28 : (79 : ZMod 274010536801) ^ 535176829 = 187473055293 := by
        calc
          (79 : ZMod 274010536801) ^ 535176829 = (79 : ZMod 274010536801) ^ (267588414 + 267588414 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 267588414 * (79 : ZMod 274010536801) ^ 267588414) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 187473055293 := by rw [factor_0_27]; decide
      have factor_0_29 : (79 : ZMod 274010536801) ^ 1070353659 = 55707028383 := by
        calc
          (79 : ZMod 274010536801) ^ 1070353659 = (79 : ZMod 274010536801) ^ (535176829 + 535176829 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 535176829 * (79 : ZMod 274010536801) ^ 535176829) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 55707028383 := by rw [factor_0_28]; decide
      have factor_0_30 : (79 : ZMod 274010536801) ^ 2140707318 = 242064611503 := by
        calc
          (79 : ZMod 274010536801) ^ 2140707318 = (79 : ZMod 274010536801) ^ (1070353659 + 1070353659) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1070353659 * (79 : ZMod 274010536801) ^ 1070353659 := by rw [pow_add]
          _ = 242064611503 := by rw [factor_0_29]; decide
      have factor_0_31 : (79 : ZMod 274010536801) ^ 4281414637 = 241688663786 := by
        calc
          (79 : ZMod 274010536801) ^ 4281414637 = (79 : ZMod 274010536801) ^ (2140707318 + 2140707318 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 2140707318 * (79 : ZMod 274010536801) ^ 2140707318) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 241688663786 := by rw [factor_0_30]; decide
      have factor_0_32 : (79 : ZMod 274010536801) ^ 8562829275 = 188514087649 := by
        calc
          (79 : ZMod 274010536801) ^ 8562829275 = (79 : ZMod 274010536801) ^ (4281414637 + 4281414637 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 4281414637 * (79 : ZMod 274010536801) ^ 4281414637) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 188514087649 := by rw [factor_0_31]; decide
      have factor_0_33 : (79 : ZMod 274010536801) ^ 17125658550 = 198480150031 := by
        calc
          (79 : ZMod 274010536801) ^ 17125658550 = (79 : ZMod 274010536801) ^ (8562829275 + 8562829275) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 8562829275 * (79 : ZMod 274010536801) ^ 8562829275 := by rw [pow_add]
          _ = 198480150031 := by rw [factor_0_32]; decide
      have factor_0_34 : (79 : ZMod 274010536801) ^ 34251317100 = 208163656055 := by
        calc
          (79 : ZMod 274010536801) ^ 34251317100 = (79 : ZMod 274010536801) ^ (17125658550 + 17125658550) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 17125658550 * (79 : ZMod 274010536801) ^ 17125658550 := by rw [pow_add]
          _ = 208163656055 := by rw [factor_0_33]; decide
      have factor_0_35 : (79 : ZMod 274010536801) ^ 68502634200 = 107567070711 := by
        calc
          (79 : ZMod 274010536801) ^ 68502634200 = (79 : ZMod 274010536801) ^ (34251317100 + 34251317100) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 34251317100 * (79 : ZMod 274010536801) ^ 34251317100 := by rw [pow_add]
          _ = 107567070711 := by rw [factor_0_34]; decide
      have factor_0_36 : (79 : ZMod 274010536801) ^ 137005268400 = 274010536800 := by
        calc
          (79 : ZMod 274010536801) ^ 137005268400 = (79 : ZMod 274010536801) ^ (68502634200 + 68502634200) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 68502634200 * (79 : ZMod 274010536801) ^ 68502634200 := by rw [pow_add]
          _ = 274010536800 := by rw [factor_0_35]; decide
      change (79 : ZMod 274010536801) ^ 137005268400 ≠ 1
      rw [factor_0_36]
      decide
    ·
      have factor_1_0 : (79 : ZMod 274010536801) ^ 1 = 79 := by norm_num
      have factor_1_1 : (79 : ZMod 274010536801) ^ 2 = 6241 := by
        calc
          (79 : ZMod 274010536801) ^ 2 = (79 : ZMod 274010536801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1 * (79 : ZMod 274010536801) ^ 1 := by rw [pow_add]
          _ = 6241 := by rw [factor_1_0]; decide
      have factor_1_2 : (79 : ZMod 274010536801) ^ 5 = 3077056399 := by
        calc
          (79 : ZMod 274010536801) ^ 5 = (79 : ZMod 274010536801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 2 * (79 : ZMod 274010536801) ^ 2) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 3077056399 := by rw [factor_1_1]; decide
      have factor_1_3 : (79 : ZMod 274010536801) ^ 10 = 87548026378 := by
        calc
          (79 : ZMod 274010536801) ^ 10 = (79 : ZMod 274010536801) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 5 * (79 : ZMod 274010536801) ^ 5 := by rw [pow_add]
          _ = 87548026378 := by rw [factor_1_2]; decide
      have factor_1_4 : (79 : ZMod 274010536801) ^ 21 = 5142120097 := by
        calc
          (79 : ZMod 274010536801) ^ 21 = (79 : ZMod 274010536801) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 10 * (79 : ZMod 274010536801) ^ 10) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 5142120097 := by rw [factor_1_3]; decide
      have factor_1_5 : (79 : ZMod 274010536801) ^ 42 = 184435275664 := by
        calc
          (79 : ZMod 274010536801) ^ 42 = (79 : ZMod 274010536801) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 21 * (79 : ZMod 274010536801) ^ 21 := by rw [pow_add]
          _ = 184435275664 := by rw [factor_1_4]; decide
      have factor_1_6 : (79 : ZMod 274010536801) ^ 85 = 61716385253 := by
        calc
          (79 : ZMod 274010536801) ^ 85 = (79 : ZMod 274010536801) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 42 * (79 : ZMod 274010536801) ^ 42) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 61716385253 := by rw [factor_1_5]; decide
      have factor_1_7 : (79 : ZMod 274010536801) ^ 170 = 107178706716 := by
        calc
          (79 : ZMod 274010536801) ^ 170 = (79 : ZMod 274010536801) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 85 * (79 : ZMod 274010536801) ^ 85 := by rw [pow_add]
          _ = 107178706716 := by rw [factor_1_6]; decide
      have factor_1_8 : (79 : ZMod 274010536801) ^ 340 = 4465093269 := by
        calc
          (79 : ZMod 274010536801) ^ 340 = (79 : ZMod 274010536801) ^ (170 + 170) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 170 * (79 : ZMod 274010536801) ^ 170 := by rw [pow_add]
          _ = 4465093269 := by rw [factor_1_7]; decide
      have factor_1_9 : (79 : ZMod 274010536801) ^ 680 = 3257964574 := by
        calc
          (79 : ZMod 274010536801) ^ 680 = (79 : ZMod 274010536801) ^ (340 + 340) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 340 * (79 : ZMod 274010536801) ^ 340 := by rw [pow_add]
          _ = 3257964574 := by rw [factor_1_8]; decide
      have factor_1_10 : (79 : ZMod 274010536801) ^ 1361 = 100406423752 := by
        calc
          (79 : ZMod 274010536801) ^ 1361 = (79 : ZMod 274010536801) ^ (680 + 680 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 680 * (79 : ZMod 274010536801) ^ 680) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 100406423752 := by rw [factor_1_9]; decide
      have factor_1_11 : (79 : ZMod 274010536801) ^ 2722 = 21258276280 := by
        calc
          (79 : ZMod 274010536801) ^ 2722 = (79 : ZMod 274010536801) ^ (1361 + 1361) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1361 * (79 : ZMod 274010536801) ^ 1361 := by rw [pow_add]
          _ = 21258276280 := by rw [factor_1_10]; decide
      have factor_1_12 : (79 : ZMod 274010536801) ^ 5444 = 186226205923 := by
        calc
          (79 : ZMod 274010536801) ^ 5444 = (79 : ZMod 274010536801) ^ (2722 + 2722) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 2722 * (79 : ZMod 274010536801) ^ 2722 := by rw [pow_add]
          _ = 186226205923 := by rw [factor_1_11]; decide
      have factor_1_13 : (79 : ZMod 274010536801) ^ 10888 = 232611752093 := by
        calc
          (79 : ZMod 274010536801) ^ 10888 = (79 : ZMod 274010536801) ^ (5444 + 5444) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 5444 * (79 : ZMod 274010536801) ^ 5444 := by rw [pow_add]
          _ = 232611752093 := by rw [factor_1_12]; decide
      have factor_1_14 : (79 : ZMod 274010536801) ^ 21776 = 122060848569 := by
        calc
          (79 : ZMod 274010536801) ^ 21776 = (79 : ZMod 274010536801) ^ (10888 + 10888) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 10888 * (79 : ZMod 274010536801) ^ 10888 := by rw [pow_add]
          _ = 122060848569 := by rw [factor_1_13]; decide
      have factor_1_15 : (79 : ZMod 274010536801) ^ 43552 = 199390229399 := by
        calc
          (79 : ZMod 274010536801) ^ 43552 = (79 : ZMod 274010536801) ^ (21776 + 21776) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 21776 * (79 : ZMod 274010536801) ^ 21776 := by rw [pow_add]
          _ = 199390229399 := by rw [factor_1_14]; decide
      have factor_1_16 : (79 : ZMod 274010536801) ^ 87105 = 118190990216 := by
        calc
          (79 : ZMod 274010536801) ^ 87105 = (79 : ZMod 274010536801) ^ (43552 + 43552 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 43552 * (79 : ZMod 274010536801) ^ 43552) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 118190990216 := by rw [factor_1_15]; decide
      have factor_1_17 : (79 : ZMod 274010536801) ^ 174211 = 149249631978 := by
        calc
          (79 : ZMod 274010536801) ^ 174211 = (79 : ZMod 274010536801) ^ (87105 + 87105 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 87105 * (79 : ZMod 274010536801) ^ 87105) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 149249631978 := by rw [factor_1_16]; decide
      have factor_1_18 : (79 : ZMod 274010536801) ^ 348422 = 225223539861 := by
        calc
          (79 : ZMod 274010536801) ^ 348422 = (79 : ZMod 274010536801) ^ (174211 + 174211) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 174211 * (79 : ZMod 274010536801) ^ 174211 := by rw [pow_add]
          _ = 225223539861 := by rw [factor_1_17]; decide
      have factor_1_19 : (79 : ZMod 274010536801) ^ 696844 = 266819749910 := by
        calc
          (79 : ZMod 274010536801) ^ 696844 = (79 : ZMod 274010536801) ^ (348422 + 348422) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 348422 * (79 : ZMod 274010536801) ^ 348422 := by rw [pow_add]
          _ = 266819749910 := by rw [factor_1_18]; decide
      have factor_1_20 : (79 : ZMod 274010536801) ^ 1393689 = 47781626483 := by
        calc
          (79 : ZMod 274010536801) ^ 1393689 = (79 : ZMod 274010536801) ^ (696844 + 696844 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 696844 * (79 : ZMod 274010536801) ^ 696844) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 47781626483 := by rw [factor_1_19]; decide
      have factor_1_21 : (79 : ZMod 274010536801) ^ 2787379 = 90761964158 := by
        calc
          (79 : ZMod 274010536801) ^ 2787379 = (79 : ZMod 274010536801) ^ (1393689 + 1393689 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 1393689 * (79 : ZMod 274010536801) ^ 1393689) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 90761964158 := by rw [factor_1_20]; decide
      have factor_1_22 : (79 : ZMod 274010536801) ^ 5574758 = 241026209143 := by
        calc
          (79 : ZMod 274010536801) ^ 5574758 = (79 : ZMod 274010536801) ^ (2787379 + 2787379) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 2787379 * (79 : ZMod 274010536801) ^ 2787379 := by rw [pow_add]
          _ = 241026209143 := by rw [factor_1_21]; decide
      have factor_1_23 : (79 : ZMod 274010536801) ^ 11149517 = 196314784787 := by
        calc
          (79 : ZMod 274010536801) ^ 11149517 = (79 : ZMod 274010536801) ^ (5574758 + 5574758 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 5574758 * (79 : ZMod 274010536801) ^ 5574758) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 196314784787 := by rw [factor_1_22]; decide
      have factor_1_24 : (79 : ZMod 274010536801) ^ 22299034 = 1553121879 := by
        calc
          (79 : ZMod 274010536801) ^ 22299034 = (79 : ZMod 274010536801) ^ (11149517 + 11149517) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 11149517 * (79 : ZMod 274010536801) ^ 11149517 := by rw [pow_add]
          _ = 1553121879 := by rw [factor_1_23]; decide
      have factor_1_25 : (79 : ZMod 274010536801) ^ 44598069 = 126774660246 := by
        calc
          (79 : ZMod 274010536801) ^ 44598069 = (79 : ZMod 274010536801) ^ (22299034 + 22299034 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 22299034 * (79 : ZMod 274010536801) ^ 22299034) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 126774660246 := by rw [factor_1_24]; decide
      have factor_1_26 : (79 : ZMod 274010536801) ^ 89196138 = 105387690856 := by
        calc
          (79 : ZMod 274010536801) ^ 89196138 = (79 : ZMod 274010536801) ^ (44598069 + 44598069) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 44598069 * (79 : ZMod 274010536801) ^ 44598069 := by rw [pow_add]
          _ = 105387690856 := by rw [factor_1_25]; decide
      have factor_1_27 : (79 : ZMod 274010536801) ^ 178392276 = 7934500505 := by
        calc
          (79 : ZMod 274010536801) ^ 178392276 = (79 : ZMod 274010536801) ^ (89196138 + 89196138) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 89196138 * (79 : ZMod 274010536801) ^ 89196138 := by rw [pow_add]
          _ = 7934500505 := by rw [factor_1_26]; decide
      have factor_1_28 : (79 : ZMod 274010536801) ^ 356784553 = 37101093137 := by
        calc
          (79 : ZMod 274010536801) ^ 356784553 = (79 : ZMod 274010536801) ^ (178392276 + 178392276 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 178392276 * (79 : ZMod 274010536801) ^ 178392276) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 37101093137 := by rw [factor_1_27]; decide
      have factor_1_29 : (79 : ZMod 274010536801) ^ 713569106 = 180051109361 := by
        calc
          (79 : ZMod 274010536801) ^ 713569106 = (79 : ZMod 274010536801) ^ (356784553 + 356784553) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 356784553 * (79 : ZMod 274010536801) ^ 356784553 := by rw [pow_add]
          _ = 180051109361 := by rw [factor_1_28]; decide
      have factor_1_30 : (79 : ZMod 274010536801) ^ 1427138212 = 96514631918 := by
        calc
          (79 : ZMod 274010536801) ^ 1427138212 = (79 : ZMod 274010536801) ^ (713569106 + 713569106) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 713569106 * (79 : ZMod 274010536801) ^ 713569106 := by rw [pow_add]
          _ = 96514631918 := by rw [factor_1_29]; decide
      have factor_1_31 : (79 : ZMod 274010536801) ^ 2854276425 = 252625979531 := by
        calc
          (79 : ZMod 274010536801) ^ 2854276425 = (79 : ZMod 274010536801) ^ (1427138212 + 1427138212 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 1427138212 * (79 : ZMod 274010536801) ^ 1427138212) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 252625979531 := by rw [factor_1_30]; decide
      have factor_1_32 : (79 : ZMod 274010536801) ^ 5708552850 = 227338997570 := by
        calc
          (79 : ZMod 274010536801) ^ 5708552850 = (79 : ZMod 274010536801) ^ (2854276425 + 2854276425) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 2854276425 * (79 : ZMod 274010536801) ^ 2854276425 := by rw [pow_add]
          _ = 227338997570 := by rw [factor_1_31]; decide
      have factor_1_33 : (79 : ZMod 274010536801) ^ 11417105700 = 156818127141 := by
        calc
          (79 : ZMod 274010536801) ^ 11417105700 = (79 : ZMod 274010536801) ^ (5708552850 + 5708552850) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 5708552850 * (79 : ZMod 274010536801) ^ 5708552850 := by rw [pow_add]
          _ = 156818127141 := by rw [factor_1_32]; decide
      have factor_1_34 : (79 : ZMod 274010536801) ^ 22834211400 = 231246535693 := by
        calc
          (79 : ZMod 274010536801) ^ 22834211400 = (79 : ZMod 274010536801) ^ (11417105700 + 11417105700) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 11417105700 * (79 : ZMod 274010536801) ^ 11417105700 := by rw [pow_add]
          _ = 231246535693 := by rw [factor_1_33]; decide
      have factor_1_35 : (79 : ZMod 274010536801) ^ 45668422800 = 263256921713 := by
        calc
          (79 : ZMod 274010536801) ^ 45668422800 = (79 : ZMod 274010536801) ^ (22834211400 + 22834211400) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 22834211400 * (79 : ZMod 274010536801) ^ 22834211400 := by rw [pow_add]
          _ = 263256921713 := by rw [factor_1_34]; decide
      have factor_1_36 : (79 : ZMod 274010536801) ^ 91336845600 = 263256921712 := by
        calc
          (79 : ZMod 274010536801) ^ 91336845600 = (79 : ZMod 274010536801) ^ (45668422800 + 45668422800) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 45668422800 * (79 : ZMod 274010536801) ^ 45668422800 := by rw [pow_add]
          _ = 263256921712 := by rw [factor_1_35]; decide
      change (79 : ZMod 274010536801) ^ 91336845600 ≠ 1
      rw [factor_1_36]
      decide
    ·
      have factor_2_0 : (79 : ZMod 274010536801) ^ 1 = 79 := by norm_num
      have factor_2_1 : (79 : ZMod 274010536801) ^ 3 = 493039 := by
        calc
          (79 : ZMod 274010536801) ^ 3 = (79 : ZMod 274010536801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 1 * (79 : ZMod 274010536801) ^ 1) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 493039 := by rw [factor_2_0]; decide
      have factor_2_2 : (79 : ZMod 274010536801) ^ 6 = 243087455521 := by
        calc
          (79 : ZMod 274010536801) ^ 6 = (79 : ZMod 274010536801) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 3 * (79 : ZMod 274010536801) ^ 3 := by rw [pow_add]
          _ = 243087455521 := by rw [factor_2_1]; decide
      have factor_2_3 : (79 : ZMod 274010536801) ^ 12 = 10222243904 := by
        calc
          (79 : ZMod 274010536801) ^ 12 = (79 : ZMod 274010536801) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 6 * (79 : ZMod 274010536801) ^ 6 := by rw [pow_add]
          _ = 10222243904 := by rw [factor_2_2]; decide
      have factor_2_4 : (79 : ZMod 274010536801) ^ 25 = 184499481315 := by
        calc
          (79 : ZMod 274010536801) ^ 25 = (79 : ZMod 274010536801) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 12 * (79 : ZMod 274010536801) ^ 12) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 184499481315 := by rw [factor_2_3]; decide
      have factor_2_5 : (79 : ZMod 274010536801) ^ 51 = 30623482425 := by
        calc
          (79 : ZMod 274010536801) ^ 51 = (79 : ZMod 274010536801) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 25 * (79 : ZMod 274010536801) ^ 25) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 30623482425 := by rw [factor_2_4]; decide
      have factor_2_6 : (79 : ZMod 274010536801) ^ 102 = 129085704184 := by
        calc
          (79 : ZMod 274010536801) ^ 102 = (79 : ZMod 274010536801) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 51 * (79 : ZMod 274010536801) ^ 51 := by rw [pow_add]
          _ = 129085704184 := by rw [factor_2_5]; decide
      have factor_2_7 : (79 : ZMod 274010536801) ^ 204 = 167263160600 := by
        calc
          (79 : ZMod 274010536801) ^ 204 = (79 : ZMod 274010536801) ^ (102 + 102) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 102 * (79 : ZMod 274010536801) ^ 102 := by rw [pow_add]
          _ = 167263160600 := by rw [factor_2_6]; decide
      have factor_2_8 : (79 : ZMod 274010536801) ^ 408 = 179966592682 := by
        calc
          (79 : ZMod 274010536801) ^ 408 = (79 : ZMod 274010536801) ^ (204 + 204) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 204 * (79 : ZMod 274010536801) ^ 204 := by rw [pow_add]
          _ = 179966592682 := by rw [factor_2_7]; decide
      have factor_2_9 : (79 : ZMod 274010536801) ^ 816 = 145716875323 := by
        calc
          (79 : ZMod 274010536801) ^ 816 = (79 : ZMod 274010536801) ^ (408 + 408) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 408 * (79 : ZMod 274010536801) ^ 408 := by rw [pow_add]
          _ = 145716875323 := by rw [factor_2_8]; decide
      have factor_2_10 : (79 : ZMod 274010536801) ^ 1633 = 270747362405 := by
        calc
          (79 : ZMod 274010536801) ^ 1633 = (79 : ZMod 274010536801) ^ (816 + 816 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 816 * (79 : ZMod 274010536801) ^ 816) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 270747362405 := by rw [factor_2_9]; decide
      have factor_2_11 : (79 : ZMod 274010536801) ^ 3266 = 108718511876 := by
        calc
          (79 : ZMod 274010536801) ^ 3266 = (79 : ZMod 274010536801) ^ (1633 + 1633) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1633 * (79 : ZMod 274010536801) ^ 1633 := by rw [pow_add]
          _ = 108718511876 := by rw [factor_2_10]; decide
      have factor_2_12 : (79 : ZMod 274010536801) ^ 6532 = 5947748846 := by
        calc
          (79 : ZMod 274010536801) ^ 6532 = (79 : ZMod 274010536801) ^ (3266 + 3266) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 3266 * (79 : ZMod 274010536801) ^ 3266 := by rw [pow_add]
          _ = 5947748846 := by rw [factor_2_11]; decide
      have factor_2_13 : (79 : ZMod 274010536801) ^ 13065 = 72432698730 := by
        calc
          (79 : ZMod 274010536801) ^ 13065 = (79 : ZMod 274010536801) ^ (6532 + 6532 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 6532 * (79 : ZMod 274010536801) ^ 6532) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 72432698730 := by rw [factor_2_12]; decide
      have factor_2_14 : (79 : ZMod 274010536801) ^ 26131 = 246460250921 := by
        calc
          (79 : ZMod 274010536801) ^ 26131 = (79 : ZMod 274010536801) ^ (13065 + 13065 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 13065 * (79 : ZMod 274010536801) ^ 13065) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 246460250921 := by rw [factor_2_13]; decide
      have factor_2_15 : (79 : ZMod 274010536801) ^ 52263 = 174986661632 := by
        calc
          (79 : ZMod 274010536801) ^ 52263 = (79 : ZMod 274010536801) ^ (26131 + 26131 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 26131 * (79 : ZMod 274010536801) ^ 26131) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 174986661632 := by rw [factor_2_14]; decide
      have factor_2_16 : (79 : ZMod 274010536801) ^ 104526 = 149340837995 := by
        calc
          (79 : ZMod 274010536801) ^ 104526 = (79 : ZMod 274010536801) ^ (52263 + 52263) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 52263 * (79 : ZMod 274010536801) ^ 52263 := by rw [pow_add]
          _ = 149340837995 := by rw [factor_2_15]; decide
      have factor_2_17 : (79 : ZMod 274010536801) ^ 209053 = 258064008913 := by
        calc
          (79 : ZMod 274010536801) ^ 209053 = (79 : ZMod 274010536801) ^ (104526 + 104526 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 104526 * (79 : ZMod 274010536801) ^ 104526) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 258064008913 := by rw [factor_2_16]; decide
      have factor_2_18 : (79 : ZMod 274010536801) ^ 418106 = 95915257746 := by
        calc
          (79 : ZMod 274010536801) ^ 418106 = (79 : ZMod 274010536801) ^ (209053 + 209053) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 209053 * (79 : ZMod 274010536801) ^ 209053 := by rw [pow_add]
          _ = 95915257746 := by rw [factor_2_17]; decide
      have factor_2_19 : (79 : ZMod 274010536801) ^ 836213 = 226421094709 := by
        calc
          (79 : ZMod 274010536801) ^ 836213 = (79 : ZMod 274010536801) ^ (418106 + 418106 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 418106 * (79 : ZMod 274010536801) ^ 418106) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 226421094709 := by rw [factor_2_18]; decide
      have factor_2_20 : (79 : ZMod 274010536801) ^ 1672427 = 12156856852 := by
        calc
          (79 : ZMod 274010536801) ^ 1672427 = (79 : ZMod 274010536801) ^ (836213 + 836213 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 836213 * (79 : ZMod 274010536801) ^ 836213) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 12156856852 := by rw [factor_2_19]; decide
      have factor_2_21 : (79 : ZMod 274010536801) ^ 3344855 = 163080740102 := by
        calc
          (79 : ZMod 274010536801) ^ 3344855 = (79 : ZMod 274010536801) ^ (1672427 + 1672427 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 1672427 * (79 : ZMod 274010536801) ^ 1672427) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 163080740102 := by rw [factor_2_20]; decide
      have factor_2_22 : (79 : ZMod 274010536801) ^ 6689710 = 220836553157 := by
        calc
          (79 : ZMod 274010536801) ^ 6689710 = (79 : ZMod 274010536801) ^ (3344855 + 3344855) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 3344855 * (79 : ZMod 274010536801) ^ 3344855 := by rw [pow_add]
          _ = 220836553157 := by rw [factor_2_21]; decide
      have factor_2_23 : (79 : ZMod 274010536801) ^ 13379420 = 13338210318 := by
        calc
          (79 : ZMod 274010536801) ^ 13379420 = (79 : ZMod 274010536801) ^ (6689710 + 6689710) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 6689710 * (79 : ZMod 274010536801) ^ 6689710 := by rw [pow_add]
          _ = 13338210318 := by rw [factor_2_22]; decide
      have factor_2_24 : (79 : ZMod 274010536801) ^ 26758841 = 224002954498 := by
        calc
          (79 : ZMod 274010536801) ^ 26758841 = (79 : ZMod 274010536801) ^ (13379420 + 13379420 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 13379420 * (79 : ZMod 274010536801) ^ 13379420) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 224002954498 := by rw [factor_2_23]; decide
      have factor_2_25 : (79 : ZMod 274010536801) ^ 53517682 = 233791399709 := by
        calc
          (79 : ZMod 274010536801) ^ 53517682 = (79 : ZMod 274010536801) ^ (26758841 + 26758841) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 26758841 * (79 : ZMod 274010536801) ^ 26758841 := by rw [pow_add]
          _ = 233791399709 := by rw [factor_2_24]; decide
      have factor_2_26 : (79 : ZMod 274010536801) ^ 107035365 = 227831122234 := by
        calc
          (79 : ZMod 274010536801) ^ 107035365 = (79 : ZMod 274010536801) ^ (53517682 + 53517682 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 53517682 * (79 : ZMod 274010536801) ^ 53517682) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 227831122234 := by rw [factor_2_25]; decide
      have factor_2_27 : (79 : ZMod 274010536801) ^ 214070731 = 137639424312 := by
        calc
          (79 : ZMod 274010536801) ^ 214070731 = (79 : ZMod 274010536801) ^ (107035365 + 107035365 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 107035365 * (79 : ZMod 274010536801) ^ 107035365) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 137639424312 := by rw [factor_2_26]; decide
      have factor_2_28 : (79 : ZMod 274010536801) ^ 428141463 = 212557527177 := by
        calc
          (79 : ZMod 274010536801) ^ 428141463 = (79 : ZMod 274010536801) ^ (214070731 + 214070731 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 214070731 * (79 : ZMod 274010536801) ^ 214070731) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 212557527177 := by rw [factor_2_27]; decide
      have factor_2_29 : (79 : ZMod 274010536801) ^ 856282927 = 152686243543 := by
        calc
          (79 : ZMod 274010536801) ^ 856282927 = (79 : ZMod 274010536801) ^ (428141463 + 428141463 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 428141463 * (79 : ZMod 274010536801) ^ 428141463) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 152686243543 := by rw [factor_2_28]; decide
      have factor_2_30 : (79 : ZMod 274010536801) ^ 1712565855 = 246057573258 := by
        calc
          (79 : ZMod 274010536801) ^ 1712565855 = (79 : ZMod 274010536801) ^ (856282927 + 856282927 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 856282927 * (79 : ZMod 274010536801) ^ 856282927) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 246057573258 := by rw [factor_2_29]; decide
      have factor_2_31 : (79 : ZMod 274010536801) ^ 3425131710 = 23166071456 := by
        calc
          (79 : ZMod 274010536801) ^ 3425131710 = (79 : ZMod 274010536801) ^ (1712565855 + 1712565855) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1712565855 * (79 : ZMod 274010536801) ^ 1712565855 := by rw [pow_add]
          _ = 23166071456 := by rw [factor_2_30]; decide
      have factor_2_32 : (79 : ZMod 274010536801) ^ 6850263420 = 49164339454 := by
        calc
          (79 : ZMod 274010536801) ^ 6850263420 = (79 : ZMod 274010536801) ^ (3425131710 + 3425131710) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 3425131710 * (79 : ZMod 274010536801) ^ 3425131710 := by rw [pow_add]
          _ = 49164339454 := by rw [factor_2_31]; decide
      have factor_2_33 : (79 : ZMod 274010536801) ^ 13700526840 = 27286429109 := by
        calc
          (79 : ZMod 274010536801) ^ 13700526840 = (79 : ZMod 274010536801) ^ (6850263420 + 6850263420) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 6850263420 * (79 : ZMod 274010536801) ^ 6850263420 := by rw [pow_add]
          _ = 27286429109 := by rw [factor_2_32]; decide
      have factor_2_34 : (79 : ZMod 274010536801) ^ 27401053680 = 203528575078 := by
        calc
          (79 : ZMod 274010536801) ^ 27401053680 = (79 : ZMod 274010536801) ^ (13700526840 + 13700526840) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 13700526840 * (79 : ZMod 274010536801) ^ 13700526840 := by rw [pow_add]
          _ = 203528575078 := by rw [factor_2_33]; decide
      have factor_2_35 : (79 : ZMod 274010536801) ^ 54802107360 = 121522322256 := by
        calc
          (79 : ZMod 274010536801) ^ 54802107360 = (79 : ZMod 274010536801) ^ (27401053680 + 27401053680) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 27401053680 * (79 : ZMod 274010536801) ^ 27401053680 := by rw [pow_add]
          _ = 121522322256 := by rw [factor_2_34]; decide
      change (79 : ZMod 274010536801) ^ 54802107360 ≠ 1
      rw [factor_2_35]
      decide
    ·
      have factor_3_0 : (79 : ZMod 274010536801) ^ 1 = 79 := by norm_num
      have factor_3_1 : (79 : ZMod 274010536801) ^ 2 = 6241 := by
        calc
          (79 : ZMod 274010536801) ^ 2 = (79 : ZMod 274010536801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1 * (79 : ZMod 274010536801) ^ 1 := by rw [pow_add]
          _ = 6241 := by rw [factor_3_0]; decide
      have factor_3_2 : (79 : ZMod 274010536801) ^ 4 = 38950081 := by
        calc
          (79 : ZMod 274010536801) ^ 4 = (79 : ZMod 274010536801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 2 * (79 : ZMod 274010536801) ^ 2 := by rw [pow_add]
          _ = 38950081 := by rw [factor_3_1]; decide
      have factor_3_3 : (79 : ZMod 274010536801) ^ 9 = 209217471322 := by
        calc
          (79 : ZMod 274010536801) ^ 9 = (79 : ZMod 274010536801) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 4 * (79 : ZMod 274010536801) ^ 4) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 209217471322 := by rw [factor_3_2]; decide
      have factor_3_4 : (79 : ZMod 274010536801) ^ 18 = 87911532120 := by
        calc
          (79 : ZMod 274010536801) ^ 18 = (79 : ZMod 274010536801) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 9 * (79 : ZMod 274010536801) ^ 9 := by rw [pow_add]
          _ = 87911532120 := by rw [factor_3_3]; decide
      have factor_3_5 : (79 : ZMod 274010536801) ^ 36 = 176092026830 := by
        calc
          (79 : ZMod 274010536801) ^ 36 = (79 : ZMod 274010536801) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 18 * (79 : ZMod 274010536801) ^ 18 := by rw [pow_add]
          _ = 176092026830 := by rw [factor_3_4]; decide
      have factor_3_6 : (79 : ZMod 274010536801) ^ 72 = 188893376267 := by
        calc
          (79 : ZMod 274010536801) ^ 72 = (79 : ZMod 274010536801) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 36 * (79 : ZMod 274010536801) ^ 36 := by rw [pow_add]
          _ = 188893376267 := by rw [factor_3_5]; decide
      have factor_3_7 : (79 : ZMod 274010536801) ^ 145 = 129898510852 := by
        calc
          (79 : ZMod 274010536801) ^ 145 = (79 : ZMod 274010536801) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 72 * (79 : ZMod 274010536801) ^ 72) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 129898510852 := by rw [factor_3_6]; decide
      have factor_3_8 : (79 : ZMod 274010536801) ^ 291 = 214073661166 := by
        calc
          (79 : ZMod 274010536801) ^ 291 = (79 : ZMod 274010536801) ^ (145 + 145 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 145 * (79 : ZMod 274010536801) ^ 145) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 214073661166 := by rw [factor_3_7]; decide
      have factor_3_9 : (79 : ZMod 274010536801) ^ 583 = 182261112831 := by
        calc
          (79 : ZMod 274010536801) ^ 583 = (79 : ZMod 274010536801) ^ (291 + 291 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 291 * (79 : ZMod 274010536801) ^ 291) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 182261112831 := by rw [factor_3_8]; decide
      have factor_3_10 : (79 : ZMod 274010536801) ^ 1166 = 237673363434 := by
        calc
          (79 : ZMod 274010536801) ^ 1166 = (79 : ZMod 274010536801) ^ (583 + 583) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 583 * (79 : ZMod 274010536801) ^ 583 := by rw [pow_add]
          _ = 237673363434 := by rw [factor_3_9]; decide
      have factor_3_11 : (79 : ZMod 274010536801) ^ 2333 = 76034457545 := by
        calc
          (79 : ZMod 274010536801) ^ 2333 = (79 : ZMod 274010536801) ^ (1166 + 1166 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 1166 * (79 : ZMod 274010536801) ^ 1166) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 76034457545 := by rw [factor_3_10]; decide
      have factor_3_12 : (79 : ZMod 274010536801) ^ 4666 = 217975346144 := by
        calc
          (79 : ZMod 274010536801) ^ 4666 = (79 : ZMod 274010536801) ^ (2333 + 2333) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 2333 * (79 : ZMod 274010536801) ^ 2333 := by rw [pow_add]
          _ = 217975346144 := by rw [factor_3_11]; decide
      have factor_3_13 : (79 : ZMod 274010536801) ^ 9332 = 17996554222 := by
        calc
          (79 : ZMod 274010536801) ^ 9332 = (79 : ZMod 274010536801) ^ (4666 + 4666) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 4666 * (79 : ZMod 274010536801) ^ 4666 := by rw [pow_add]
          _ = 17996554222 := by rw [factor_3_12]; decide
      have factor_3_14 : (79 : ZMod 274010536801) ^ 18665 = 33661568131 := by
        calc
          (79 : ZMod 274010536801) ^ 18665 = (79 : ZMod 274010536801) ^ (9332 + 9332 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 9332 * (79 : ZMod 274010536801) ^ 9332) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 33661568131 := by rw [factor_3_13]; decide
      have factor_3_15 : (79 : ZMod 274010536801) ^ 37330 = 144359416058 := by
        calc
          (79 : ZMod 274010536801) ^ 37330 = (79 : ZMod 274010536801) ^ (18665 + 18665) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 18665 * (79 : ZMod 274010536801) ^ 18665 := by rw [pow_add]
          _ = 144359416058 := by rw [factor_3_14]; decide
      have factor_3_16 : (79 : ZMod 274010536801) ^ 74661 = 181400613067 := by
        calc
          (79 : ZMod 274010536801) ^ 74661 = (79 : ZMod 274010536801) ^ (37330 + 37330 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 37330 * (79 : ZMod 274010536801) ^ 37330) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 181400613067 := by rw [factor_3_15]; decide
      have factor_3_17 : (79 : ZMod 274010536801) ^ 149323 = 251892514208 := by
        calc
          (79 : ZMod 274010536801) ^ 149323 = (79 : ZMod 274010536801) ^ (74661 + 74661 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 74661 * (79 : ZMod 274010536801) ^ 74661) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 251892514208 := by rw [factor_3_16]; decide
      have factor_3_18 : (79 : ZMod 274010536801) ^ 298647 = 64274175860 := by
        calc
          (79 : ZMod 274010536801) ^ 298647 = (79 : ZMod 274010536801) ^ (149323 + 149323 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 149323 * (79 : ZMod 274010536801) ^ 149323) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 64274175860 := by rw [factor_3_17]; decide
      have factor_3_19 : (79 : ZMod 274010536801) ^ 597295 = 94638589923 := by
        calc
          (79 : ZMod 274010536801) ^ 597295 = (79 : ZMod 274010536801) ^ (298647 + 298647 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 298647 * (79 : ZMod 274010536801) ^ 298647) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 94638589923 := by rw [factor_3_18]; decide
      have factor_3_20 : (79 : ZMod 274010536801) ^ 1194591 = 136624855887 := by
        calc
          (79 : ZMod 274010536801) ^ 1194591 = (79 : ZMod 274010536801) ^ (597295 + 597295 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 597295 * (79 : ZMod 274010536801) ^ 597295) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 136624855887 := by rw [factor_3_19]; decide
      have factor_3_21 : (79 : ZMod 274010536801) ^ 2389182 = 153113504551 := by
        calc
          (79 : ZMod 274010536801) ^ 2389182 = (79 : ZMod 274010536801) ^ (1194591 + 1194591) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1194591 * (79 : ZMod 274010536801) ^ 1194591 := by rw [pow_add]
          _ = 153113504551 := by rw [factor_3_20]; decide
      have factor_3_22 : (79 : ZMod 274010536801) ^ 4778364 = 151848497223 := by
        calc
          (79 : ZMod 274010536801) ^ 4778364 = (79 : ZMod 274010536801) ^ (2389182 + 2389182) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 2389182 * (79 : ZMod 274010536801) ^ 2389182 := by rw [pow_add]
          _ = 151848497223 := by rw [factor_3_21]; decide
      have factor_3_23 : (79 : ZMod 274010536801) ^ 9556729 = 183211881489 := by
        calc
          (79 : ZMod 274010536801) ^ 9556729 = (79 : ZMod 274010536801) ^ (4778364 + 4778364 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 4778364 * (79 : ZMod 274010536801) ^ 4778364) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 183211881489 := by rw [factor_3_22]; decide
      have factor_3_24 : (79 : ZMod 274010536801) ^ 19113458 = 72527085798 := by
        calc
          (79 : ZMod 274010536801) ^ 19113458 = (79 : ZMod 274010536801) ^ (9556729 + 9556729) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 9556729 * (79 : ZMod 274010536801) ^ 9556729 := by rw [pow_add]
          _ = 72527085798 := by rw [factor_3_23]; decide
      have factor_3_25 : (79 : ZMod 274010536801) ^ 38226916 = 220441950071 := by
        calc
          (79 : ZMod 274010536801) ^ 38226916 = (79 : ZMod 274010536801) ^ (19113458 + 19113458) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 19113458 * (79 : ZMod 274010536801) ^ 19113458 := by rw [pow_add]
          _ = 220441950071 := by rw [factor_3_24]; decide
      have factor_3_26 : (79 : ZMod 274010536801) ^ 76453832 = 21597124307 := by
        calc
          (79 : ZMod 274010536801) ^ 76453832 = (79 : ZMod 274010536801) ^ (38226916 + 38226916) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 38226916 * (79 : ZMod 274010536801) ^ 38226916 := by rw [pow_add]
          _ = 21597124307 := by rw [factor_3_25]; decide
      have factor_3_27 : (79 : ZMod 274010536801) ^ 152907665 = 41126028741 := by
        calc
          (79 : ZMod 274010536801) ^ 152907665 = (79 : ZMod 274010536801) ^ (76453832 + 76453832 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 76453832 * (79 : ZMod 274010536801) ^ 76453832) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 41126028741 := by rw [factor_3_26]; decide
      have factor_3_28 : (79 : ZMod 274010536801) ^ 305815331 = 89704577074 := by
        calc
          (79 : ZMod 274010536801) ^ 305815331 = (79 : ZMod 274010536801) ^ (152907665 + 152907665 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 152907665 * (79 : ZMod 274010536801) ^ 152907665) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 89704577074 := by rw [factor_3_27]; decide
      have factor_3_29 : (79 : ZMod 274010536801) ^ 611630662 = 67271927543 := by
        calc
          (79 : ZMod 274010536801) ^ 611630662 = (79 : ZMod 274010536801) ^ (305815331 + 305815331) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 305815331 * (79 : ZMod 274010536801) ^ 305815331 := by rw [pow_add]
          _ = 67271927543 := by rw [factor_3_28]; decide
      have factor_3_30 : (79 : ZMod 274010536801) ^ 1223261325 = 86021612921 := by
        calc
          (79 : ZMod 274010536801) ^ 1223261325 = (79 : ZMod 274010536801) ^ (611630662 + 611630662 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 611630662 * (79 : ZMod 274010536801) ^ 611630662) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 86021612921 := by rw [factor_3_29]; decide
      have factor_3_31 : (79 : ZMod 274010536801) ^ 2446522650 = 203556865071 := by
        calc
          (79 : ZMod 274010536801) ^ 2446522650 = (79 : ZMod 274010536801) ^ (1223261325 + 1223261325) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1223261325 * (79 : ZMod 274010536801) ^ 1223261325 := by rw [pow_add]
          _ = 203556865071 := by rw [factor_3_30]; decide
      have factor_3_32 : (79 : ZMod 274010536801) ^ 4893045300 = 172401788411 := by
        calc
          (79 : ZMod 274010536801) ^ 4893045300 = (79 : ZMod 274010536801) ^ (2446522650 + 2446522650) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 2446522650 * (79 : ZMod 274010536801) ^ 2446522650 := by rw [pow_add]
          _ = 172401788411 := by rw [factor_3_31]; decide
      have factor_3_33 : (79 : ZMod 274010536801) ^ 9786090600 = 159381969071 := by
        calc
          (79 : ZMod 274010536801) ^ 9786090600 = (79 : ZMod 274010536801) ^ (4893045300 + 4893045300) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 4893045300 * (79 : ZMod 274010536801) ^ 4893045300 := by rw [pow_add]
          _ = 159381969071 := by rw [factor_3_32]; decide
      have factor_3_34 : (79 : ZMod 274010536801) ^ 19572181200 = 101745081111 := by
        calc
          (79 : ZMod 274010536801) ^ 19572181200 = (79 : ZMod 274010536801) ^ (9786090600 + 9786090600) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 9786090600 * (79 : ZMod 274010536801) ^ 9786090600 := by rw [pow_add]
          _ = 101745081111 := by rw [factor_3_33]; decide
      have factor_3_35 : (79 : ZMod 274010536801) ^ 39144362400 = 236773984701 := by
        calc
          (79 : ZMod 274010536801) ^ 39144362400 = (79 : ZMod 274010536801) ^ (19572181200 + 19572181200) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 19572181200 * (79 : ZMod 274010536801) ^ 19572181200 := by rw [pow_add]
          _ = 236773984701 := by rw [factor_3_34]; decide
      change (79 : ZMod 274010536801) ^ 39144362400 ≠ 1
      rw [factor_3_35]
      decide
    ·
      have factor_4_0 : (79 : ZMod 274010536801) ^ 1 = 79 := by norm_num
      have factor_4_1 : (79 : ZMod 274010536801) ^ 2 = 6241 := by
        calc
          (79 : ZMod 274010536801) ^ 2 = (79 : ZMod 274010536801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1 * (79 : ZMod 274010536801) ^ 1 := by rw [pow_add]
          _ = 6241 := by rw [factor_4_0]; decide
      have factor_4_2 : (79 : ZMod 274010536801) ^ 5 = 3077056399 := by
        calc
          (79 : ZMod 274010536801) ^ 5 = (79 : ZMod 274010536801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 2 * (79 : ZMod 274010536801) ^ 2) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 3077056399 := by rw [factor_4_1]; decide
      have factor_4_3 : (79 : ZMod 274010536801) ^ 11 = 66030663837 := by
        calc
          (79 : ZMod 274010536801) ^ 11 = (79 : ZMod 274010536801) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 5 * (79 : ZMod 274010536801) ^ 5) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 66030663837 := by rw [factor_4_2]; decide
      have factor_4_4 : (79 : ZMod 274010536801) ^ 23 = 32738719660 := by
        calc
          (79 : ZMod 274010536801) ^ 23 = (79 : ZMod 274010536801) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 11 * (79 : ZMod 274010536801) ^ 11) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 32738719660 := by rw [factor_4_3]; decide
      have factor_4_5 : (79 : ZMod 274010536801) ^ 46 = 157730674858 := by
        calc
          (79 : ZMod 274010536801) ^ 46 = (79 : ZMod 274010536801) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 23 * (79 : ZMod 274010536801) ^ 23 := by rw [pow_add]
          _ = 157730674858 := by rw [factor_4_4]; decide
      have factor_4_6 : (79 : ZMod 274010536801) ^ 92 = 258128008932 := by
        calc
          (79 : ZMod 274010536801) ^ 92 = (79 : ZMod 274010536801) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 46 * (79 : ZMod 274010536801) ^ 46 := by rw [pow_add]
          _ = 258128008932 := by rw [factor_4_5]; decide
      have factor_4_7 : (79 : ZMod 274010536801) ^ 185 = 153948356433 := by
        calc
          (79 : ZMod 274010536801) ^ 185 = (79 : ZMod 274010536801) ^ (92 + 92 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 92 * (79 : ZMod 274010536801) ^ 92) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 153948356433 := by rw [factor_4_6]; decide
      have factor_4_8 : (79 : ZMod 274010536801) ^ 371 = 28202308464 := by
        calc
          (79 : ZMod 274010536801) ^ 371 = (79 : ZMod 274010536801) ^ (185 + 185 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 185 * (79 : ZMod 274010536801) ^ 185) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 28202308464 := by rw [factor_4_7]; decide
      have factor_4_9 : (79 : ZMod 274010536801) ^ 742 = 17360848762 := by
        calc
          (79 : ZMod 274010536801) ^ 742 = (79 : ZMod 274010536801) ^ (371 + 371) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 371 * (79 : ZMod 274010536801) ^ 371 := by rw [pow_add]
          _ = 17360848762 := by rw [factor_4_8]; decide
      have factor_4_10 : (79 : ZMod 274010536801) ^ 1484 = 167416054339 := by
        calc
          (79 : ZMod 274010536801) ^ 1484 = (79 : ZMod 274010536801) ^ (742 + 742) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 742 * (79 : ZMod 274010536801) ^ 742 := by rw [pow_add]
          _ = 167416054339 := by rw [factor_4_9]; decide
      have factor_4_11 : (79 : ZMod 274010536801) ^ 2969 = 232237728559 := by
        calc
          (79 : ZMod 274010536801) ^ 2969 = (79 : ZMod 274010536801) ^ (1484 + 1484 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 1484 * (79 : ZMod 274010536801) ^ 1484) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 232237728559 := by rw [factor_4_10]; decide
      have factor_4_12 : (79 : ZMod 274010536801) ^ 5939 = 40636042 := by
        calc
          (79 : ZMod 274010536801) ^ 5939 = (79 : ZMod 274010536801) ^ (2969 + 2969 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 2969 * (79 : ZMod 274010536801) ^ 2969) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 40636042 := by rw [factor_4_11]; decide
      have factor_4_13 : (79 : ZMod 274010536801) ^ 11878 = 100414662938 := by
        calc
          (79 : ZMod 274010536801) ^ 11878 = (79 : ZMod 274010536801) ^ (5939 + 5939) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 5939 * (79 : ZMod 274010536801) ^ 5939 := by rw [pow_add]
          _ = 100414662938 := by rw [factor_4_12]; decide
      have factor_4_14 : (79 : ZMod 274010536801) ^ 23756 = 93146870558 := by
        calc
          (79 : ZMod 274010536801) ^ 23756 = (79 : ZMod 274010536801) ^ (11878 + 11878) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 11878 * (79 : ZMod 274010536801) ^ 11878 := by rw [pow_add]
          _ = 93146870558 := by rw [factor_4_13]; decide
      have factor_4_15 : (79 : ZMod 274010536801) ^ 47512 = 139649037220 := by
        calc
          (79 : ZMod 274010536801) ^ 47512 = (79 : ZMod 274010536801) ^ (23756 + 23756) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 23756 * (79 : ZMod 274010536801) ^ 23756 := by rw [pow_add]
          _ = 139649037220 := by rw [factor_4_14]; decide
      have factor_4_16 : (79 : ZMod 274010536801) ^ 95024 = 119714815588 := by
        calc
          (79 : ZMod 274010536801) ^ 95024 = (79 : ZMod 274010536801) ^ (47512 + 47512) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 47512 * (79 : ZMod 274010536801) ^ 47512 := by rw [pow_add]
          _ = 119714815588 := by rw [factor_4_15]; decide
      have factor_4_17 : (79 : ZMod 274010536801) ^ 190048 = 220444497105 := by
        calc
          (79 : ZMod 274010536801) ^ 190048 = (79 : ZMod 274010536801) ^ (95024 + 95024) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 95024 * (79 : ZMod 274010536801) ^ 95024 := by rw [pow_add]
          _ = 220444497105 := by rw [factor_4_16]; decide
      have factor_4_18 : (79 : ZMod 274010536801) ^ 380097 = 102748816379 := by
        calc
          (79 : ZMod 274010536801) ^ 380097 = (79 : ZMod 274010536801) ^ (190048 + 190048 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 190048 * (79 : ZMod 274010536801) ^ 190048) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 102748816379 := by rw [factor_4_17]; decide
      have factor_4_19 : (79 : ZMod 274010536801) ^ 760194 = 229381165399 := by
        calc
          (79 : ZMod 274010536801) ^ 760194 = (79 : ZMod 274010536801) ^ (380097 + 380097) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 380097 * (79 : ZMod 274010536801) ^ 380097 := by rw [pow_add]
          _ = 229381165399 := by rw [factor_4_18]; decide
      have factor_4_20 : (79 : ZMod 274010536801) ^ 1520388 = 254423764975 := by
        calc
          (79 : ZMod 274010536801) ^ 1520388 = (79 : ZMod 274010536801) ^ (760194 + 760194) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 760194 * (79 : ZMod 274010536801) ^ 760194 := by rw [pow_add]
          _ = 254423764975 := by rw [factor_4_19]; decide
      have factor_4_21 : (79 : ZMod 274010536801) ^ 3040777 = 241684291906 := by
        calc
          (79 : ZMod 274010536801) ^ 3040777 = (79 : ZMod 274010536801) ^ (1520388 + 1520388 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 1520388 * (79 : ZMod 274010536801) ^ 1520388) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 241684291906 := by rw [factor_4_20]; decide
      have factor_4_22 : (79 : ZMod 274010536801) ^ 6081554 = 150378058566 := by
        calc
          (79 : ZMod 274010536801) ^ 6081554 = (79 : ZMod 274010536801) ^ (3040777 + 3040777) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 3040777 * (79 : ZMod 274010536801) ^ 3040777 := by rw [pow_add]
          _ = 150378058566 := by rw [factor_4_21]; decide
      have factor_4_23 : (79 : ZMod 274010536801) ^ 12163109 = 30233244572 := by
        calc
          (79 : ZMod 274010536801) ^ 12163109 = (79 : ZMod 274010536801) ^ (6081554 + 6081554 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 6081554 * (79 : ZMod 274010536801) ^ 6081554) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 30233244572 := by rw [factor_4_22]; decide
      have factor_4_24 : (79 : ZMod 274010536801) ^ 24326219 = 240625557808 := by
        calc
          (79 : ZMod 274010536801) ^ 24326219 = (79 : ZMod 274010536801) ^ (12163109 + 12163109 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 12163109 * (79 : ZMod 274010536801) ^ 12163109) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 240625557808 := by rw [factor_4_23]; decide
      have factor_4_25 : (79 : ZMod 274010536801) ^ 48652439 = 203865630381 := by
        calc
          (79 : ZMod 274010536801) ^ 48652439 = (79 : ZMod 274010536801) ^ (24326219 + 24326219 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 24326219 * (79 : ZMod 274010536801) ^ 24326219) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 203865630381 := by rw [factor_4_24]; decide
      have factor_4_26 : (79 : ZMod 274010536801) ^ 97304878 = 261979444442 := by
        calc
          (79 : ZMod 274010536801) ^ 97304878 = (79 : ZMod 274010536801) ^ (48652439 + 48652439) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 48652439 * (79 : ZMod 274010536801) ^ 48652439 := by rw [pow_add]
          _ = 261979444442 := by rw [factor_4_25]; decide
      have factor_4_27 : (79 : ZMod 274010536801) ^ 194609756 = 144701397204 := by
        calc
          (79 : ZMod 274010536801) ^ 194609756 = (79 : ZMod 274010536801) ^ (97304878 + 97304878) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 97304878 * (79 : ZMod 274010536801) ^ 97304878 := by rw [pow_add]
          _ = 144701397204 := by rw [factor_4_26]; decide
      have factor_4_28 : (79 : ZMod 274010536801) ^ 389219512 = 269865863188 := by
        calc
          (79 : ZMod 274010536801) ^ 389219512 = (79 : ZMod 274010536801) ^ (194609756 + 194609756) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 194609756 * (79 : ZMod 274010536801) ^ 194609756 := by rw [pow_add]
          _ = 269865863188 := by rw [factor_4_27]; decide
      have factor_4_29 : (79 : ZMod 274010536801) ^ 778439025 = 240175056310 := by
        calc
          (79 : ZMod 274010536801) ^ 778439025 = (79 : ZMod 274010536801) ^ (389219512 + 389219512 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 389219512 * (79 : ZMod 274010536801) ^ 389219512) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 240175056310 := by rw [factor_4_28]; decide
      have factor_4_30 : (79 : ZMod 274010536801) ^ 1556878050 = 46240253725 := by
        calc
          (79 : ZMod 274010536801) ^ 1556878050 = (79 : ZMod 274010536801) ^ (778439025 + 778439025) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 778439025 * (79 : ZMod 274010536801) ^ 778439025 := by rw [pow_add]
          _ = 46240253725 := by rw [factor_4_29]; decide
      have factor_4_31 : (79 : ZMod 274010536801) ^ 3113756100 = 216229713767 := by
        calc
          (79 : ZMod 274010536801) ^ 3113756100 = (79 : ZMod 274010536801) ^ (1556878050 + 1556878050) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1556878050 * (79 : ZMod 274010536801) ^ 1556878050 := by rw [pow_add]
          _ = 216229713767 := by rw [factor_4_30]; decide
      have factor_4_32 : (79 : ZMod 274010536801) ^ 6227512200 = 244181425172 := by
        calc
          (79 : ZMod 274010536801) ^ 6227512200 = (79 : ZMod 274010536801) ^ (3113756100 + 3113756100) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 3113756100 * (79 : ZMod 274010536801) ^ 3113756100 := by rw [pow_add]
          _ = 244181425172 := by rw [factor_4_31]; decide
      have factor_4_33 : (79 : ZMod 274010536801) ^ 12455024400 = 135458987614 := by
        calc
          (79 : ZMod 274010536801) ^ 12455024400 = (79 : ZMod 274010536801) ^ (6227512200 + 6227512200) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 6227512200 * (79 : ZMod 274010536801) ^ 6227512200 := by rw [pow_add]
          _ = 135458987614 := by rw [factor_4_32]; decide
      have factor_4_34 : (79 : ZMod 274010536801) ^ 24910048800 = 43293167298 := by
        calc
          (79 : ZMod 274010536801) ^ 24910048800 = (79 : ZMod 274010536801) ^ (12455024400 + 12455024400) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 12455024400 * (79 : ZMod 274010536801) ^ 12455024400 := by rw [pow_add]
          _ = 43293167298 := by rw [factor_4_33]; decide
      change (79 : ZMod 274010536801) ^ 24910048800 ≠ 1
      rw [factor_4_34]
      decide
    ·
      have factor_5_0 : (79 : ZMod 274010536801) ^ 1 = 79 := by norm_num
      have factor_5_1 : (79 : ZMod 274010536801) ^ 2 = 6241 := by
        calc
          (79 : ZMod 274010536801) ^ 2 = (79 : ZMod 274010536801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1 * (79 : ZMod 274010536801) ^ 1 := by rw [pow_add]
          _ = 6241 := by rw [factor_5_0]; decide
      have factor_5_2 : (79 : ZMod 274010536801) ^ 4 = 38950081 := by
        calc
          (79 : ZMod 274010536801) ^ 4 = (79 : ZMod 274010536801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 2 * (79 : ZMod 274010536801) ^ 2 := by rw [pow_add]
          _ = 38950081 := by rw [factor_5_1]; decide
      have factor_5_3 : (79 : ZMod 274010536801) ^ 9 = 209217471322 := by
        calc
          (79 : ZMod 274010536801) ^ 9 = (79 : ZMod 274010536801) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 4 * (79 : ZMod 274010536801) ^ 4) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 209217471322 := by rw [factor_5_2]; decide
      have factor_5_4 : (79 : ZMod 274010536801) ^ 19 = 94747617455 := by
        calc
          (79 : ZMod 274010536801) ^ 19 = (79 : ZMod 274010536801) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 9 * (79 : ZMod 274010536801) ^ 9) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 94747617455 := by rw [factor_5_3]; decide
      have factor_5_5 : (79 : ZMod 274010536801) ^ 39 = 272241376321 := by
        calc
          (79 : ZMod 274010536801) ^ 39 = (79 : ZMod 274010536801) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 19 * (79 : ZMod 274010536801) ^ 19) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 272241376321 := by rw [factor_5_4]; decide
      have factor_5_6 : (79 : ZMod 274010536801) ^ 78 = 153719593342 := by
        calc
          (79 : ZMod 274010536801) ^ 78 = (79 : ZMod 274010536801) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 39 * (79 : ZMod 274010536801) ^ 39 := by rw [pow_add]
          _ = 153719593342 := by rw [factor_5_5]; decide
      have factor_5_7 : (79 : ZMod 274010536801) ^ 157 = 16677378730 := by
        calc
          (79 : ZMod 274010536801) ^ 157 = (79 : ZMod 274010536801) ^ (78 + 78 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 78 * (79 : ZMod 274010536801) ^ 78) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 16677378730 := by rw [factor_5_6]; decide
      have factor_5_8 : (79 : ZMod 274010536801) ^ 314 = 92242868835 := by
        calc
          (79 : ZMod 274010536801) ^ 314 = (79 : ZMod 274010536801) ^ (157 + 157) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 157 * (79 : ZMod 274010536801) ^ 157 := by rw [pow_add]
          _ = 92242868835 := by rw [factor_5_7]; decide
      have factor_5_9 : (79 : ZMod 274010536801) ^ 628 = 45267166745 := by
        calc
          (79 : ZMod 274010536801) ^ 628 = (79 : ZMod 274010536801) ^ (314 + 314) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 314 * (79 : ZMod 274010536801) ^ 314 := by rw [pow_add]
          _ = 45267166745 := by rw [factor_5_8]; decide
      have factor_5_10 : (79 : ZMod 274010536801) ^ 1256 = 197530229252 := by
        calc
          (79 : ZMod 274010536801) ^ 1256 = (79 : ZMod 274010536801) ^ (628 + 628) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 628 * (79 : ZMod 274010536801) ^ 628 := by rw [pow_add]
          _ = 197530229252 := by rw [factor_5_9]; decide
      have factor_5_11 : (79 : ZMod 274010536801) ^ 2512 = 24890531993 := by
        calc
          (79 : ZMod 274010536801) ^ 2512 = (79 : ZMod 274010536801) ^ (1256 + 1256) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1256 * (79 : ZMod 274010536801) ^ 1256 := by rw [pow_add]
          _ = 24890531993 := by rw [factor_5_10]; decide
      have factor_5_12 : (79 : ZMod 274010536801) ^ 5025 = 111843072190 := by
        calc
          (79 : ZMod 274010536801) ^ 5025 = (79 : ZMod 274010536801) ^ (2512 + 2512 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 2512 * (79 : ZMod 274010536801) ^ 2512) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 111843072190 := by rw [factor_5_11]; decide
      have factor_5_13 : (79 : ZMod 274010536801) ^ 10050 = 29335768807 := by
        calc
          (79 : ZMod 274010536801) ^ 10050 = (79 : ZMod 274010536801) ^ (5025 + 5025) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 5025 * (79 : ZMod 274010536801) ^ 5025 := by rw [pow_add]
          _ = 29335768807 := by rw [factor_5_12]; decide
      have factor_5_14 : (79 : ZMod 274010536801) ^ 20101 = 111391835208 := by
        calc
          (79 : ZMod 274010536801) ^ 20101 = (79 : ZMod 274010536801) ^ (10050 + 10050 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 10050 * (79 : ZMod 274010536801) ^ 10050) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 111391835208 := by rw [factor_5_13]; decide
      have factor_5_15 : (79 : ZMod 274010536801) ^ 40202 = 18347297908 := by
        calc
          (79 : ZMod 274010536801) ^ 40202 = (79 : ZMod 274010536801) ^ (20101 + 20101) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 20101 * (79 : ZMod 274010536801) ^ 20101 := by rw [pow_add]
          _ = 18347297908 := by rw [factor_5_14]; decide
      have factor_5_16 : (79 : ZMod 274010536801) ^ 80405 = 157889574957 := by
        calc
          (79 : ZMod 274010536801) ^ 80405 = (79 : ZMod 274010536801) ^ (40202 + 40202 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 40202 * (79 : ZMod 274010536801) ^ 40202) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 157889574957 := by rw [factor_5_15]; decide
      have factor_5_17 : (79 : ZMod 274010536801) ^ 160810 = 109735696434 := by
        calc
          (79 : ZMod 274010536801) ^ 160810 = (79 : ZMod 274010536801) ^ (80405 + 80405) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 80405 * (79 : ZMod 274010536801) ^ 80405 := by rw [pow_add]
          _ = 109735696434 := by rw [factor_5_16]; decide
      have factor_5_18 : (79 : ZMod 274010536801) ^ 321620 = 127204838807 := by
        calc
          (79 : ZMod 274010536801) ^ 321620 = (79 : ZMod 274010536801) ^ (160810 + 160810) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 160810 * (79 : ZMod 274010536801) ^ 160810 := by rw [pow_add]
          _ = 127204838807 := by rw [factor_5_17]; decide
      have factor_5_19 : (79 : ZMod 274010536801) ^ 643241 = 264318141747 := by
        calc
          (79 : ZMod 274010536801) ^ 643241 = (79 : ZMod 274010536801) ^ (321620 + 321620 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 321620 * (79 : ZMod 274010536801) ^ 321620) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 264318141747 := by rw [factor_5_18]; decide
      have factor_5_20 : (79 : ZMod 274010536801) ^ 1286482 = 27130672181 := by
        calc
          (79 : ZMod 274010536801) ^ 1286482 = (79 : ZMod 274010536801) ^ (643241 + 643241) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 643241 * (79 : ZMod 274010536801) ^ 643241 := by rw [pow_add]
          _ = 27130672181 := by rw [factor_5_19]; decide
      have factor_5_21 : (79 : ZMod 274010536801) ^ 2572965 = 131435560091 := by
        calc
          (79 : ZMod 274010536801) ^ 2572965 = (79 : ZMod 274010536801) ^ (1286482 + 1286482 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 1286482 * (79 : ZMod 274010536801) ^ 1286482) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 131435560091 := by rw [factor_5_20]; decide
      have factor_5_22 : (79 : ZMod 274010536801) ^ 5145931 = 262511291025 := by
        calc
          (79 : ZMod 274010536801) ^ 5145931 = (79 : ZMod 274010536801) ^ (2572965 + 2572965 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 2572965 * (79 : ZMod 274010536801) ^ 2572965) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 262511291025 := by rw [factor_5_21]; decide
      have factor_5_23 : (79 : ZMod 274010536801) ^ 10291862 = 258497191010 := by
        calc
          (79 : ZMod 274010536801) ^ 10291862 = (79 : ZMod 274010536801) ^ (5145931 + 5145931) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 5145931 * (79 : ZMod 274010536801) ^ 5145931 := by rw [pow_add]
          _ = 258497191010 := by rw [factor_5_22]; decide
      have factor_5_24 : (79 : ZMod 274010536801) ^ 20583724 = 83781108464 := by
        calc
          (79 : ZMod 274010536801) ^ 20583724 = (79 : ZMod 274010536801) ^ (10291862 + 10291862) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 10291862 * (79 : ZMod 274010536801) ^ 10291862 := by rw [pow_add]
          _ = 83781108464 := by rw [factor_5_23]; decide
      have factor_5_25 : (79 : ZMod 274010536801) ^ 41167448 = 27594644387 := by
        calc
          (79 : ZMod 274010536801) ^ 41167448 = (79 : ZMod 274010536801) ^ (20583724 + 20583724) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 20583724 * (79 : ZMod 274010536801) ^ 20583724 := by rw [pow_add]
          _ = 27594644387 := by rw [factor_5_24]; decide
      have factor_5_26 : (79 : ZMod 274010536801) ^ 82334896 = 225512267887 := by
        calc
          (79 : ZMod 274010536801) ^ 82334896 = (79 : ZMod 274010536801) ^ (41167448 + 41167448) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 41167448 * (79 : ZMod 274010536801) ^ 41167448 := by rw [pow_add]
          _ = 225512267887 := by rw [factor_5_25]; decide
      have factor_5_27 : (79 : ZMod 274010536801) ^ 164669793 = 208271559589 := by
        calc
          (79 : ZMod 274010536801) ^ 164669793 = (79 : ZMod 274010536801) ^ (82334896 + 82334896 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 82334896 * (79 : ZMod 274010536801) ^ 82334896) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 208271559589 := by rw [factor_5_26]; decide
      have factor_5_28 : (79 : ZMod 274010536801) ^ 329339587 = 72291698237 := by
        calc
          (79 : ZMod 274010536801) ^ 329339587 = (79 : ZMod 274010536801) ^ (164669793 + 164669793 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 164669793 * (79 : ZMod 274010536801) ^ 164669793) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 72291698237 := by rw [factor_5_27]; decide
      have factor_5_29 : (79 : ZMod 274010536801) ^ 658679175 = 100443664806 := by
        calc
          (79 : ZMod 274010536801) ^ 658679175 = (79 : ZMod 274010536801) ^ (329339587 + 329339587 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 329339587 * (79 : ZMod 274010536801) ^ 329339587) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 100443664806 := by rw [factor_5_28]; decide
      have factor_5_30 : (79 : ZMod 274010536801) ^ 1317358350 = 76276333070 := by
        calc
          (79 : ZMod 274010536801) ^ 1317358350 = (79 : ZMod 274010536801) ^ (658679175 + 658679175) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 658679175 * (79 : ZMod 274010536801) ^ 658679175 := by rw [pow_add]
          _ = 76276333070 := by rw [factor_5_29]; decide
      have factor_5_31 : (79 : ZMod 274010536801) ^ 2634716700 = 162098434913 := by
        calc
          (79 : ZMod 274010536801) ^ 2634716700 = (79 : ZMod 274010536801) ^ (1317358350 + 1317358350) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1317358350 * (79 : ZMod 274010536801) ^ 1317358350 := by rw [pow_add]
          _ = 162098434913 := by rw [factor_5_30]; decide
      have factor_5_32 : (79 : ZMod 274010536801) ^ 5269433400 = 110939976061 := by
        calc
          (79 : ZMod 274010536801) ^ 5269433400 = (79 : ZMod 274010536801) ^ (2634716700 + 2634716700) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 2634716700 * (79 : ZMod 274010536801) ^ 2634716700 := by rw [pow_add]
          _ = 110939976061 := by rw [factor_5_31]; decide
      have factor_5_33 : (79 : ZMod 274010536801) ^ 10538866800 = 14532315519 := by
        calc
          (79 : ZMod 274010536801) ^ 10538866800 = (79 : ZMod 274010536801) ^ (5269433400 + 5269433400) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 5269433400 * (79 : ZMod 274010536801) ^ 5269433400 := by rw [pow_add]
          _ = 14532315519 := by rw [factor_5_32]; decide
      have factor_5_34 : (79 : ZMod 274010536801) ^ 21077733600 = 157089369967 := by
        calc
          (79 : ZMod 274010536801) ^ 21077733600 = (79 : ZMod 274010536801) ^ (10538866800 + 10538866800) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 10538866800 * (79 : ZMod 274010536801) ^ 10538866800 := by rw [pow_add]
          _ = 157089369967 := by rw [factor_5_33]; decide
      change (79 : ZMod 274010536801) ^ 21077733600 ≠ 1
      rw [factor_5_34]
      decide
    ·
      have factor_6_0 : (79 : ZMod 274010536801) ^ 1 = 79 := by norm_num
      have factor_6_1 : (79 : ZMod 274010536801) ^ 3 = 493039 := by
        calc
          (79 : ZMod 274010536801) ^ 3 = (79 : ZMod 274010536801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 1 * (79 : ZMod 274010536801) ^ 1) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 493039 := by rw [factor_6_0]; decide
      have factor_6_2 : (79 : ZMod 274010536801) ^ 6 = 243087455521 := by
        calc
          (79 : ZMod 274010536801) ^ 6 = (79 : ZMod 274010536801) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 3 * (79 : ZMod 274010536801) ^ 3 := by rw [pow_add]
          _ = 243087455521 := by rw [factor_6_1]; decide
      have factor_6_3 : (79 : ZMod 274010536801) ^ 13 = 259536194814 := by
        calc
          (79 : ZMod 274010536801) ^ 13 = (79 : ZMod 274010536801) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 6 * (79 : ZMod 274010536801) ^ 6) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 259536194814 := by rw [factor_6_2]; decide
      have factor_6_4 : (79 : ZMod 274010536801) ^ 26 = 52900573432 := by
        calc
          (79 : ZMod 274010536801) ^ 26 = (79 : ZMod 274010536801) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 13 * (79 : ZMod 274010536801) ^ 13 := by rw [pow_add]
          _ = 52900573432 := by rw [factor_6_3]; decide
      have factor_6_5 : (79 : ZMod 274010536801) ^ 53 = 135809664128 := by
        calc
          (79 : ZMod 274010536801) ^ 53 = (79 : ZMod 274010536801) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 26 * (79 : ZMod 274010536801) ^ 26) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 135809664128 := by rw [factor_6_4]; decide
      have factor_6_6 : (79 : ZMod 274010536801) ^ 107 = 82754094755 := by
        calc
          (79 : ZMod 274010536801) ^ 107 = (79 : ZMod 274010536801) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 53 * (79 : ZMod 274010536801) ^ 53) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 82754094755 := by rw [factor_6_5]; decide
      have factor_6_7 : (79 : ZMod 274010536801) ^ 214 = 159475378561 := by
        calc
          (79 : ZMod 274010536801) ^ 214 = (79 : ZMod 274010536801) ^ (107 + 107) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 107 * (79 : ZMod 274010536801) ^ 107 := by rw [pow_add]
          _ = 159475378561 := by rw [factor_6_6]; decide
      have factor_6_8 : (79 : ZMod 274010536801) ^ 429 = 233630568680 := by
        calc
          (79 : ZMod 274010536801) ^ 429 = (79 : ZMod 274010536801) ^ (214 + 214 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 214 * (79 : ZMod 274010536801) ^ 214) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 233630568680 := by rw [factor_6_7]; decide
      have factor_6_9 : (79 : ZMod 274010536801) ^ 859 = 135636036826 := by
        calc
          (79 : ZMod 274010536801) ^ 859 = (79 : ZMod 274010536801) ^ (429 + 429 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 429 * (79 : ZMod 274010536801) ^ 429) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 135636036826 := by rw [factor_6_8]; decide
      have factor_6_10 : (79 : ZMod 274010536801) ^ 1719 = 84308616442 := by
        calc
          (79 : ZMod 274010536801) ^ 1719 = (79 : ZMod 274010536801) ^ (859 + 859 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 859 * (79 : ZMod 274010536801) ^ 859) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 84308616442 := by rw [factor_6_9]; decide
      have factor_6_11 : (79 : ZMod 274010536801) ^ 3438 = 14322289411 := by
        calc
          (79 : ZMod 274010536801) ^ 3438 = (79 : ZMod 274010536801) ^ (1719 + 1719) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1719 * (79 : ZMod 274010536801) ^ 1719 := by rw [pow_add]
          _ = 14322289411 := by rw [factor_6_10]; decide
      have factor_6_12 : (79 : ZMod 274010536801) ^ 6876 = 133473079869 := by
        calc
          (79 : ZMod 274010536801) ^ 6876 = (79 : ZMod 274010536801) ^ (3438 + 3438) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 3438 * (79 : ZMod 274010536801) ^ 3438 := by rw [pow_add]
          _ = 133473079869 := by rw [factor_6_11]; decide
      have factor_6_13 : (79 : ZMod 274010536801) ^ 13753 = 44751163933 := by
        calc
          (79 : ZMod 274010536801) ^ 13753 = (79 : ZMod 274010536801) ^ (6876 + 6876 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 6876 * (79 : ZMod 274010536801) ^ 6876) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 44751163933 := by rw [factor_6_12]; decide
      have factor_6_14 : (79 : ZMod 274010536801) ^ 27507 = 207811033858 := by
        calc
          (79 : ZMod 274010536801) ^ 27507 = (79 : ZMod 274010536801) ^ (13753 + 13753 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 13753 * (79 : ZMod 274010536801) ^ 13753) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 207811033858 := by rw [factor_6_13]; decide
      have factor_6_15 : (79 : ZMod 274010536801) ^ 55014 = 186087529899 := by
        calc
          (79 : ZMod 274010536801) ^ 55014 = (79 : ZMod 274010536801) ^ (27507 + 27507) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 27507 * (79 : ZMod 274010536801) ^ 27507 := by rw [pow_add]
          _ = 186087529899 := by rw [factor_6_14]; decide
      have factor_6_16 : (79 : ZMod 274010536801) ^ 110028 = 18222109783 := by
        calc
          (79 : ZMod 274010536801) ^ 110028 = (79 : ZMod 274010536801) ^ (55014 + 55014) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 55014 * (79 : ZMod 274010536801) ^ 55014 := by rw [pow_add]
          _ = 18222109783 := by rw [factor_6_15]; decide
      have factor_6_17 : (79 : ZMod 274010536801) ^ 220056 = 104541825584 := by
        calc
          (79 : ZMod 274010536801) ^ 220056 = (79 : ZMod 274010536801) ^ (110028 + 110028) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 110028 * (79 : ZMod 274010536801) ^ 110028 := by rw [pow_add]
          _ = 104541825584 := by rw [factor_6_16]; decide
      have factor_6_18 : (79 : ZMod 274010536801) ^ 440112 = 248530302817 := by
        calc
          (79 : ZMod 274010536801) ^ 440112 = (79 : ZMod 274010536801) ^ (220056 + 220056) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 220056 * (79 : ZMod 274010536801) ^ 220056 := by rw [pow_add]
          _ = 248530302817 := by rw [factor_6_17]; decide
      have factor_6_19 : (79 : ZMod 274010536801) ^ 880225 = 68315502180 := by
        calc
          (79 : ZMod 274010536801) ^ 880225 = (79 : ZMod 274010536801) ^ (440112 + 440112 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 440112 * (79 : ZMod 274010536801) ^ 440112) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 68315502180 := by rw [factor_6_18]; decide
      have factor_6_20 : (79 : ZMod 274010536801) ^ 1760450 = 103284556861 := by
        calc
          (79 : ZMod 274010536801) ^ 1760450 = (79 : ZMod 274010536801) ^ (880225 + 880225) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 880225 * (79 : ZMod 274010536801) ^ 880225 := by rw [pow_add]
          _ = 103284556861 := by rw [factor_6_19]; decide
      have factor_6_21 : (79 : ZMod 274010536801) ^ 3520900 = 26510023926 := by
        calc
          (79 : ZMod 274010536801) ^ 3520900 = (79 : ZMod 274010536801) ^ (1760450 + 1760450) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1760450 * (79 : ZMod 274010536801) ^ 1760450 := by rw [pow_add]
          _ = 26510023926 := by rw [factor_6_20]; decide
      have factor_6_22 : (79 : ZMod 274010536801) ^ 7041800 = 52815156601 := by
        calc
          (79 : ZMod 274010536801) ^ 7041800 = (79 : ZMod 274010536801) ^ (3520900 + 3520900) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 3520900 * (79 : ZMod 274010536801) ^ 3520900 := by rw [pow_add]
          _ = 52815156601 := by rw [factor_6_21]; decide
      have factor_6_23 : (79 : ZMod 274010536801) ^ 14083600 = 10762467125 := by
        calc
          (79 : ZMod 274010536801) ^ 14083600 = (79 : ZMod 274010536801) ^ (7041800 + 7041800) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 7041800 * (79 : ZMod 274010536801) ^ 7041800 := by rw [pow_add]
          _ = 10762467125 := by rw [factor_6_22]; decide
      have factor_6_24 : (79 : ZMod 274010536801) ^ 28167201 = 34755666300 := by
        calc
          (79 : ZMod 274010536801) ^ 28167201 = (79 : ZMod 274010536801) ^ (14083600 + 14083600 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 14083600 * (79 : ZMod 274010536801) ^ 14083600) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 34755666300 := by rw [factor_6_23]; decide
      have factor_6_25 : (79 : ZMod 274010536801) ^ 56334403 = 46296749647 := by
        calc
          (79 : ZMod 274010536801) ^ 56334403 = (79 : ZMod 274010536801) ^ (28167201 + 28167201 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 28167201 * (79 : ZMod 274010536801) ^ 28167201) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 46296749647 := by rw [factor_6_24]; decide
      have factor_6_26 : (79 : ZMod 274010536801) ^ 112668806 = 54743543326 := by
        calc
          (79 : ZMod 274010536801) ^ 112668806 = (79 : ZMod 274010536801) ^ (56334403 + 56334403) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 56334403 * (79 : ZMod 274010536801) ^ 56334403 := by rw [pow_add]
          _ = 54743543326 := by rw [factor_6_25]; decide
      have factor_6_27 : (79 : ZMod 274010536801) ^ 225337612 = 54856433901 := by
        calc
          (79 : ZMod 274010536801) ^ 225337612 = (79 : ZMod 274010536801) ^ (112668806 + 112668806) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 112668806 * (79 : ZMod 274010536801) ^ 112668806 := by rw [pow_add]
          _ = 54856433901 := by rw [factor_6_26]; decide
      have factor_6_28 : (79 : ZMod 274010536801) ^ 450675225 = 10472991588 := by
        calc
          (79 : ZMod 274010536801) ^ 450675225 = (79 : ZMod 274010536801) ^ (225337612 + 225337612 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 225337612 * (79 : ZMod 274010536801) ^ 225337612) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 10472991588 := by rw [factor_6_27]; decide
      have factor_6_29 : (79 : ZMod 274010536801) ^ 901350450 = 249061789801 := by
        calc
          (79 : ZMod 274010536801) ^ 901350450 = (79 : ZMod 274010536801) ^ (450675225 + 450675225) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 450675225 * (79 : ZMod 274010536801) ^ 450675225 := by rw [pow_add]
          _ = 249061789801 := by rw [factor_6_28]; decide
      have factor_6_30 : (79 : ZMod 274010536801) ^ 1802700900 = 155558183008 := by
        calc
          (79 : ZMod 274010536801) ^ 1802700900 = (79 : ZMod 274010536801) ^ (901350450 + 901350450) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 901350450 * (79 : ZMod 274010536801) ^ 901350450 := by rw [pow_add]
          _ = 155558183008 := by rw [factor_6_29]; decide
      have factor_6_31 : (79 : ZMod 274010536801) ^ 3605401800 = 118953045951 := by
        calc
          (79 : ZMod 274010536801) ^ 3605401800 = (79 : ZMod 274010536801) ^ (1802700900 + 1802700900) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1802700900 * (79 : ZMod 274010536801) ^ 1802700900 := by rw [pow_add]
          _ = 118953045951 := by rw [factor_6_30]; decide
      have factor_6_32 : (79 : ZMod 274010536801) ^ 7210803600 = 41244220137 := by
        calc
          (79 : ZMod 274010536801) ^ 7210803600 = (79 : ZMod 274010536801) ^ (3605401800 + 3605401800) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 3605401800 * (79 : ZMod 274010536801) ^ 3605401800 := by rw [pow_add]
          _ = 41244220137 := by rw [factor_6_31]; decide
      have factor_6_33 : (79 : ZMod 274010536801) ^ 14421607200 = 251152383554 := by
        calc
          (79 : ZMod 274010536801) ^ 14421607200 = (79 : ZMod 274010536801) ^ (7210803600 + 7210803600) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 7210803600 * (79 : ZMod 274010536801) ^ 7210803600 := by rw [pow_add]
          _ = 251152383554 := by rw [factor_6_32]; decide
      change (79 : ZMod 274010536801) ^ 14421607200 ≠ 1
      rw [factor_6_33]
      decide
    ·
      have factor_7_0 : (79 : ZMod 274010536801) ^ 1 = 79 := by norm_num
      have factor_7_1 : (79 : ZMod 274010536801) ^ 2 = 6241 := by
        calc
          (79 : ZMod 274010536801) ^ 2 = (79 : ZMod 274010536801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1 * (79 : ZMod 274010536801) ^ 1 := by rw [pow_add]
          _ = 6241 := by rw [factor_7_0]; decide
      have factor_7_2 : (79 : ZMod 274010536801) ^ 5 = 3077056399 := by
        calc
          (79 : ZMod 274010536801) ^ 5 = (79 : ZMod 274010536801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 2 * (79 : ZMod 274010536801) ^ 2) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 3077056399 := by rw [factor_7_1]; decide
      have factor_7_3 : (79 : ZMod 274010536801) ^ 11 = 66030663837 := by
        calc
          (79 : ZMod 274010536801) ^ 11 = (79 : ZMod 274010536801) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 5 * (79 : ZMod 274010536801) ^ 5) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 66030663837 := by rw [factor_7_2]; decide
      have factor_7_4 : (79 : ZMod 274010536801) ^ 22 = 132216950862 := by
        calc
          (79 : ZMod 274010536801) ^ 22 = (79 : ZMod 274010536801) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 11 * (79 : ZMod 274010536801) ^ 11 := by rw [pow_add]
          _ = 132216950862 := by rw [factor_7_3]; decide
      have factor_7_5 : (79 : ZMod 274010536801) ^ 44 = 216300854824 := by
        calc
          (79 : ZMod 274010536801) ^ 44 = (79 : ZMod 274010536801) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 22 * (79 : ZMod 274010536801) ^ 22 := by rw [pow_add]
          _ = 216300854824 := by rw [factor_7_4]; decide
      have factor_7_6 : (79 : ZMod 274010536801) ^ 88 = 262778076419 := by
        calc
          (79 : ZMod 274010536801) ^ 88 = (79 : ZMod 274010536801) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 44 * (79 : ZMod 274010536801) ^ 44 := by rw [pow_add]
          _ = 262778076419 := by rw [factor_7_5]; decide
      have factor_7_7 : (79 : ZMod 274010536801) ^ 177 = 194918247398 := by
        calc
          (79 : ZMod 274010536801) ^ 177 = (79 : ZMod 274010536801) ^ (88 + 88 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 88 * (79 : ZMod 274010536801) ^ 88) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 194918247398 := by rw [factor_7_6]; decide
      have factor_7_8 : (79 : ZMod 274010536801) ^ 355 = 213933132016 := by
        calc
          (79 : ZMod 274010536801) ^ 355 = (79 : ZMod 274010536801) ^ (177 + 177 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 177 * (79 : ZMod 274010536801) ^ 177) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 213933132016 := by rw [factor_7_7]; decide
      have factor_7_9 : (79 : ZMod 274010536801) ^ 710 = 153916599661 := by
        calc
          (79 : ZMod 274010536801) ^ 710 = (79 : ZMod 274010536801) ^ (355 + 355) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 355 * (79 : ZMod 274010536801) ^ 355 := by rw [pow_add]
          _ = 153916599661 := by rw [factor_7_8]; decide
      have factor_7_10 : (79 : ZMod 274010536801) ^ 1420 = 220434265469 := by
        calc
          (79 : ZMod 274010536801) ^ 1420 = (79 : ZMod 274010536801) ^ (710 + 710) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 710 * (79 : ZMod 274010536801) ^ 710 := by rw [pow_add]
          _ = 220434265469 := by rw [factor_7_9]; decide
      have factor_7_11 : (79 : ZMod 274010536801) ^ 2840 = 118453938363 := by
        calc
          (79 : ZMod 274010536801) ^ 2840 = (79 : ZMod 274010536801) ^ (1420 + 1420) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1420 * (79 : ZMod 274010536801) ^ 1420 := by rw [pow_add]
          _ = 118453938363 := by rw [factor_7_10]; decide
      have factor_7_12 : (79 : ZMod 274010536801) ^ 5680 = 12886772070 := by
        calc
          (79 : ZMod 274010536801) ^ 5680 = (79 : ZMod 274010536801) ^ (2840 + 2840) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 2840 * (79 : ZMod 274010536801) ^ 2840 := by rw [pow_add]
          _ = 12886772070 := by rw [factor_7_11]; decide
      have factor_7_13 : (79 : ZMod 274010536801) ^ 11361 = 37250006745 := by
        calc
          (79 : ZMod 274010536801) ^ 11361 = (79 : ZMod 274010536801) ^ (5680 + 5680 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 5680 * (79 : ZMod 274010536801) ^ 5680) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 37250006745 := by rw [factor_7_12]; decide
      have factor_7_14 : (79 : ZMod 274010536801) ^ 22723 = 145806393635 := by
        calc
          (79 : ZMod 274010536801) ^ 22723 = (79 : ZMod 274010536801) ^ (11361 + 11361 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 11361 * (79 : ZMod 274010536801) ^ 11361) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 145806393635 := by rw [factor_7_13]; decide
      have factor_7_15 : (79 : ZMod 274010536801) ^ 45446 = 133552710242 := by
        calc
          (79 : ZMod 274010536801) ^ 45446 = (79 : ZMod 274010536801) ^ (22723 + 22723) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 22723 * (79 : ZMod 274010536801) ^ 22723 := by rw [pow_add]
          _ = 133552710242 := by rw [factor_7_14]; decide
      have factor_7_16 : (79 : ZMod 274010536801) ^ 90892 = 143588860770 := by
        calc
          (79 : ZMod 274010536801) ^ 90892 = (79 : ZMod 274010536801) ^ (45446 + 45446) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 45446 * (79 : ZMod 274010536801) ^ 45446 := by rw [pow_add]
          _ = 143588860770 := by rw [factor_7_15]; decide
      have factor_7_17 : (79 : ZMod 274010536801) ^ 181785 = 138561342561 := by
        calc
          (79 : ZMod 274010536801) ^ 181785 = (79 : ZMod 274010536801) ^ (90892 + 90892 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 90892 * (79 : ZMod 274010536801) ^ 90892) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 138561342561 := by rw [factor_7_16]; decide
      have factor_7_18 : (79 : ZMod 274010536801) ^ 363571 = 255869686805 := by
        calc
          (79 : ZMod 274010536801) ^ 363571 = (79 : ZMod 274010536801) ^ (181785 + 181785 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 181785 * (79 : ZMod 274010536801) ^ 181785) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 255869686805 := by rw [factor_7_17]; decide
      have factor_7_19 : (79 : ZMod 274010536801) ^ 727142 = 67869515007 := by
        calc
          (79 : ZMod 274010536801) ^ 727142 = (79 : ZMod 274010536801) ^ (363571 + 363571) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 363571 * (79 : ZMod 274010536801) ^ 363571 := by rw [pow_add]
          _ = 67869515007 := by rw [factor_7_18]; decide
      have factor_7_20 : (79 : ZMod 274010536801) ^ 1454284 = 156844819433 := by
        calc
          (79 : ZMod 274010536801) ^ 1454284 = (79 : ZMod 274010536801) ^ (727142 + 727142) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 727142 * (79 : ZMod 274010536801) ^ 727142 := by rw [pow_add]
          _ = 156844819433 := by rw [factor_7_19]; decide
      have factor_7_21 : (79 : ZMod 274010536801) ^ 2908569 = 17837435105 := by
        calc
          (79 : ZMod 274010536801) ^ 2908569 = (79 : ZMod 274010536801) ^ (1454284 + 1454284 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 1454284 * (79 : ZMod 274010536801) ^ 1454284) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 17837435105 := by rw [factor_7_20]; decide
      have factor_7_22 : (79 : ZMod 274010536801) ^ 5817139 = 209029487861 := by
        calc
          (79 : ZMod 274010536801) ^ 5817139 = (79 : ZMod 274010536801) ^ (2908569 + 2908569 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 2908569 * (79 : ZMod 274010536801) ^ 2908569) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 209029487861 := by rw [factor_7_21]; decide
      have factor_7_23 : (79 : ZMod 274010536801) ^ 11634278 = 100403360643 := by
        calc
          (79 : ZMod 274010536801) ^ 11634278 = (79 : ZMod 274010536801) ^ (5817139 + 5817139) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 5817139 * (79 : ZMod 274010536801) ^ 5817139 := by rw [pow_add]
          _ = 100403360643 := by rw [factor_7_22]; decide
      have factor_7_24 : (79 : ZMod 274010536801) ^ 23268557 = 129945302751 := by
        calc
          (79 : ZMod 274010536801) ^ 23268557 = (79 : ZMod 274010536801) ^ (11634278 + 11634278 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 11634278 * (79 : ZMod 274010536801) ^ 11634278) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 129945302751 := by rw [factor_7_23]; decide
      have factor_7_25 : (79 : ZMod 274010536801) ^ 46537115 = 68288805666 := by
        calc
          (79 : ZMod 274010536801) ^ 46537115 = (79 : ZMod 274010536801) ^ (23268557 + 23268557 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 23268557 * (79 : ZMod 274010536801) ^ 23268557) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 68288805666 := by rw [factor_7_24]; decide
      have factor_7_26 : (79 : ZMod 274010536801) ^ 93074231 = 188575680274 := by
        calc
          (79 : ZMod 274010536801) ^ 93074231 = (79 : ZMod 274010536801) ^ (46537115 + 46537115 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 46537115 * (79 : ZMod 274010536801) ^ 46537115) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 188575680274 := by rw [factor_7_25]; decide
      have factor_7_27 : (79 : ZMod 274010536801) ^ 186148462 = 36877701329 := by
        calc
          (79 : ZMod 274010536801) ^ 186148462 = (79 : ZMod 274010536801) ^ (93074231 + 93074231) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 93074231 * (79 : ZMod 274010536801) ^ 93074231 := by rw [pow_add]
          _ = 36877701329 := by rw [factor_7_26]; decide
      have factor_7_28 : (79 : ZMod 274010536801) ^ 372296925 = 83617936545 := by
        calc
          (79 : ZMod 274010536801) ^ 372296925 = (79 : ZMod 274010536801) ^ (186148462 + 186148462 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 186148462 * (79 : ZMod 274010536801) ^ 186148462) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 83617936545 := by rw [factor_7_27]; decide
      have factor_7_29 : (79 : ZMod 274010536801) ^ 744593850 = 909077819 := by
        calc
          (79 : ZMod 274010536801) ^ 744593850 = (79 : ZMod 274010536801) ^ (372296925 + 372296925) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 372296925 * (79 : ZMod 274010536801) ^ 372296925 := by rw [pow_add]
          _ = 909077819 := by rw [factor_7_28]; decide
      have factor_7_30 : (79 : ZMod 274010536801) ^ 1489187700 = 125753097537 := by
        calc
          (79 : ZMod 274010536801) ^ 1489187700 = (79 : ZMod 274010536801) ^ (744593850 + 744593850) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 744593850 * (79 : ZMod 274010536801) ^ 744593850 := by rw [pow_add]
          _ = 125753097537 := by rw [factor_7_29]; decide
      have factor_7_31 : (79 : ZMod 274010536801) ^ 2978375400 = 156168621186 := by
        calc
          (79 : ZMod 274010536801) ^ 2978375400 = (79 : ZMod 274010536801) ^ (1489187700 + 1489187700) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1489187700 * (79 : ZMod 274010536801) ^ 1489187700 := by rw [pow_add]
          _ = 156168621186 := by rw [factor_7_30]; decide
      have factor_7_32 : (79 : ZMod 274010536801) ^ 5956750800 = 105582634348 := by
        calc
          (79 : ZMod 274010536801) ^ 5956750800 = (79 : ZMod 274010536801) ^ (2978375400 + 2978375400) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 2978375400 * (79 : ZMod 274010536801) ^ 2978375400 := by rw [pow_add]
          _ = 105582634348 := by rw [factor_7_31]; decide
      have factor_7_33 : (79 : ZMod 274010536801) ^ 11913501600 = 160728224640 := by
        calc
          (79 : ZMod 274010536801) ^ 11913501600 = (79 : ZMod 274010536801) ^ (5956750800 + 5956750800) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 5956750800 * (79 : ZMod 274010536801) ^ 5956750800 := by rw [pow_add]
          _ = 160728224640 := by rw [factor_7_32]; decide
      change (79 : ZMod 274010536801) ^ 11913501600 ≠ 1
      rw [factor_7_33]
      decide
    ·
      have factor_8_0 : (79 : ZMod 274010536801) ^ 1 = 79 := by norm_num
      have factor_8_1 : (79 : ZMod 274010536801) ^ 2 = 6241 := by
        calc
          (79 : ZMod 274010536801) ^ 2 = (79 : ZMod 274010536801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1 * (79 : ZMod 274010536801) ^ 1 := by rw [pow_add]
          _ = 6241 := by rw [factor_8_0]; decide
      have factor_8_2 : (79 : ZMod 274010536801) ^ 4 = 38950081 := by
        calc
          (79 : ZMod 274010536801) ^ 4 = (79 : ZMod 274010536801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 2 * (79 : ZMod 274010536801) ^ 2 := by rw [pow_add]
          _ = 38950081 := by rw [factor_8_1]; decide
      have factor_8_3 : (79 : ZMod 274010536801) ^ 8 = 186478176225 := by
        calc
          (79 : ZMod 274010536801) ^ 8 = (79 : ZMod 274010536801) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 4 * (79 : ZMod 274010536801) ^ 4 := by rw [pow_add]
          _ = 186478176225 := by rw [factor_8_2]; decide
      have factor_8_4 : (79 : ZMod 274010536801) ^ 17 = 160663243354 := by
        calc
          (79 : ZMod 274010536801) ^ 17 = (79 : ZMod 274010536801) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 8 * (79 : ZMod 274010536801) ^ 8) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 160663243354 := by rw [factor_8_3]; decide
      have factor_8_5 : (79 : ZMod 274010536801) ^ 35 = 71598769150 := by
        calc
          (79 : ZMod 274010536801) ^ 35 = (79 : ZMod 274010536801) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 17 * (79 : ZMod 274010536801) ^ 17) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 71598769150 := by rw [factor_8_4]; decide
      have factor_8_6 : (79 : ZMod 274010536801) ^ 70 = 131920613031 := by
        calc
          (79 : ZMod 274010536801) ^ 70 = (79 : ZMod 274010536801) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 35 * (79 : ZMod 274010536801) ^ 35 := by rw [pow_add]
          _ = 131920613031 := by rw [factor_8_5]; decide
      have factor_8_7 : (79 : ZMod 274010536801) ^ 140 = 143150279116 := by
        calc
          (79 : ZMod 274010536801) ^ 140 = (79 : ZMod 274010536801) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 70 * (79 : ZMod 274010536801) ^ 70 := by rw [pow_add]
          _ = 143150279116 := by rw [factor_8_6]; decide
      have factor_8_8 : (79 : ZMod 274010536801) ^ 281 = 267629040544 := by
        calc
          (79 : ZMod 274010536801) ^ 281 = (79 : ZMod 274010536801) ^ (140 + 140 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 140 * (79 : ZMod 274010536801) ^ 140) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 267629040544 := by rw [factor_8_7]; decide
      have factor_8_9 : (79 : ZMod 274010536801) ^ 563 = 185165262289 := by
        calc
          (79 : ZMod 274010536801) ^ 563 = (79 : ZMod 274010536801) ^ (281 + 281 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 281 * (79 : ZMod 274010536801) ^ 281) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 185165262289 := by rw [factor_8_8]; decide
      have factor_8_10 : (79 : ZMod 274010536801) ^ 1126 = 182180060942 := by
        calc
          (79 : ZMod 274010536801) ^ 1126 = (79 : ZMod 274010536801) ^ (563 + 563) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 563 * (79 : ZMod 274010536801) ^ 563 := by rw [pow_add]
          _ = 182180060942 := by rw [factor_8_9]; decide
      have factor_8_11 : (79 : ZMod 274010536801) ^ 2252 = 173048841367 := by
        calc
          (79 : ZMod 274010536801) ^ 2252 = (79 : ZMod 274010536801) ^ (1126 + 1126) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1126 * (79 : ZMod 274010536801) ^ 1126 := by rw [pow_add]
          _ = 173048841367 := by rw [factor_8_10]; decide
      have factor_8_12 : (79 : ZMod 274010536801) ^ 4505 = 162377884744 := by
        calc
          (79 : ZMod 274010536801) ^ 4505 = (79 : ZMod 274010536801) ^ (2252 + 2252 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 2252 * (79 : ZMod 274010536801) ^ 2252) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 162377884744 := by rw [factor_8_11]; decide
      have factor_8_13 : (79 : ZMod 274010536801) ^ 9010 = 35862587434 := by
        calc
          (79 : ZMod 274010536801) ^ 9010 = (79 : ZMod 274010536801) ^ (4505 + 4505) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 4505 * (79 : ZMod 274010536801) ^ 4505 := by rw [pow_add]
          _ = 35862587434 := by rw [factor_8_12]; decide
      have factor_8_14 : (79 : ZMod 274010536801) ^ 18021 = 169474655916 := by
        calc
          (79 : ZMod 274010536801) ^ 18021 = (79 : ZMod 274010536801) ^ (9010 + 9010 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 9010 * (79 : ZMod 274010536801) ^ 9010) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 169474655916 := by rw [factor_8_13]; decide
      have factor_8_15 : (79 : ZMod 274010536801) ^ 36043 = 170065924385 := by
        calc
          (79 : ZMod 274010536801) ^ 36043 = (79 : ZMod 274010536801) ^ (18021 + 18021 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 18021 * (79 : ZMod 274010536801) ^ 18021) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 170065924385 := by rw [factor_8_14]; decide
      have factor_8_16 : (79 : ZMod 274010536801) ^ 72087 = 216445832976 := by
        calc
          (79 : ZMod 274010536801) ^ 72087 = (79 : ZMod 274010536801) ^ (36043 + 36043 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 36043 * (79 : ZMod 274010536801) ^ 36043) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 216445832976 := by rw [factor_8_15]; decide
      have factor_8_17 : (79 : ZMod 274010536801) ^ 144174 = 183786550646 := by
        calc
          (79 : ZMod 274010536801) ^ 144174 = (79 : ZMod 274010536801) ^ (72087 + 72087) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 72087 * (79 : ZMod 274010536801) ^ 72087 := by rw [pow_add]
          _ = 183786550646 := by rw [factor_8_16]; decide
      have factor_8_18 : (79 : ZMod 274010536801) ^ 288349 = 214821459230 := by
        calc
          (79 : ZMod 274010536801) ^ 288349 = (79 : ZMod 274010536801) ^ (144174 + 144174 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 144174 * (79 : ZMod 274010536801) ^ 144174) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 214821459230 := by rw [factor_8_17]; decide
      have factor_8_19 : (79 : ZMod 274010536801) ^ 576699 = 13569032827 := by
        calc
          (79 : ZMod 274010536801) ^ 576699 = (79 : ZMod 274010536801) ^ (288349 + 288349 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 288349 * (79 : ZMod 274010536801) ^ 288349) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 13569032827 := by rw [factor_8_18]; decide
      have factor_8_20 : (79 : ZMod 274010536801) ^ 1153398 = 253697126287 := by
        calc
          (79 : ZMod 274010536801) ^ 1153398 = (79 : ZMod 274010536801) ^ (576699 + 576699) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 576699 * (79 : ZMod 274010536801) ^ 576699 := by rw [pow_add]
          _ = 253697126287 := by rw [factor_8_19]; decide
      have factor_8_21 : (79 : ZMod 274010536801) ^ 2306796 = 135860665843 := by
        calc
          (79 : ZMod 274010536801) ^ 2306796 = (79 : ZMod 274010536801) ^ (1153398 + 1153398) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1153398 * (79 : ZMod 274010536801) ^ 1153398 := by rw [pow_add]
          _ = 135860665843 := by rw [factor_8_20]; decide
      have factor_8_22 : (79 : ZMod 274010536801) ^ 4613593 = 260927506529 := by
        calc
          (79 : ZMod 274010536801) ^ 4613593 = (79 : ZMod 274010536801) ^ (2306796 + 2306796 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 2306796 * (79 : ZMod 274010536801) ^ 2306796) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 260927506529 := by rw [factor_8_21]; decide
      have factor_8_23 : (79 : ZMod 274010536801) ^ 9227186 = 237090346540 := by
        calc
          (79 : ZMod 274010536801) ^ 9227186 = (79 : ZMod 274010536801) ^ (4613593 + 4613593) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 4613593 * (79 : ZMod 274010536801) ^ 4613593 := by rw [pow_add]
          _ = 237090346540 := by rw [factor_8_22]; decide
      have factor_8_24 : (79 : ZMod 274010536801) ^ 18454373 = 191966739422 := by
        calc
          (79 : ZMod 274010536801) ^ 18454373 = (79 : ZMod 274010536801) ^ (9227186 + 9227186 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 9227186 * (79 : ZMod 274010536801) ^ 9227186) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 191966739422 := by rw [factor_8_23]; decide
      have factor_8_25 : (79 : ZMod 274010536801) ^ 36908746 = 194882806841 := by
        calc
          (79 : ZMod 274010536801) ^ 36908746 = (79 : ZMod 274010536801) ^ (18454373 + 18454373) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 18454373 * (79 : ZMod 274010536801) ^ 18454373 := by rw [pow_add]
          _ = 194882806841 := by rw [factor_8_24]; decide
      have factor_8_26 : (79 : ZMod 274010536801) ^ 73817493 = 150624741739 := by
        calc
          (79 : ZMod 274010536801) ^ 73817493 = (79 : ZMod 274010536801) ^ (36908746 + 36908746 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 36908746 * (79 : ZMod 274010536801) ^ 36908746) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 150624741739 := by rw [factor_8_25]; decide
      have factor_8_27 : (79 : ZMod 274010536801) ^ 147634987 = 88679038340 := by
        calc
          (79 : ZMod 274010536801) ^ 147634987 = (79 : ZMod 274010536801) ^ (73817493 + 73817493 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 73817493 * (79 : ZMod 274010536801) ^ 73817493) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 88679038340 := by rw [factor_8_26]; decide
      have factor_8_28 : (79 : ZMod 274010536801) ^ 295269975 = 38530597287 := by
        calc
          (79 : ZMod 274010536801) ^ 295269975 = (79 : ZMod 274010536801) ^ (147634987 + 147634987 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = ((79 : ZMod 274010536801) ^ 147634987 * (79 : ZMod 274010536801) ^ 147634987) * (79 : ZMod 274010536801) := by rw [pow_succ, pow_add]
          _ = 38530597287 := by rw [factor_8_27]; decide
      have factor_8_29 : (79 : ZMod 274010536801) ^ 590539950 = 271186941667 := by
        calc
          (79 : ZMod 274010536801) ^ 590539950 = (79 : ZMod 274010536801) ^ (295269975 + 295269975) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 295269975 * (79 : ZMod 274010536801) ^ 295269975 := by rw [pow_add]
          _ = 271186941667 := by rw [factor_8_28]; decide
      have factor_8_30 : (79 : ZMod 274010536801) ^ 1181079900 = 260962520069 := by
        calc
          (79 : ZMod 274010536801) ^ 1181079900 = (79 : ZMod 274010536801) ^ (590539950 + 590539950) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 590539950 * (79 : ZMod 274010536801) ^ 590539950 := by rw [pow_add]
          _ = 260962520069 := by rw [factor_8_29]; decide
      have factor_8_31 : (79 : ZMod 274010536801) ^ 2362159800 = 140690027450 := by
        calc
          (79 : ZMod 274010536801) ^ 2362159800 = (79 : ZMod 274010536801) ^ (1181079900 + 1181079900) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 1181079900 * (79 : ZMod 274010536801) ^ 1181079900 := by rw [pow_add]
          _ = 140690027450 := by rw [factor_8_30]; decide
      have factor_8_32 : (79 : ZMod 274010536801) ^ 4724319600 = 205155488022 := by
        calc
          (79 : ZMod 274010536801) ^ 4724319600 = (79 : ZMod 274010536801) ^ (2362159800 + 2362159800) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 2362159800 * (79 : ZMod 274010536801) ^ 2362159800 := by rw [pow_add]
          _ = 205155488022 := by rw [factor_8_31]; decide
      have factor_8_33 : (79 : ZMod 274010536801) ^ 9448639200 = 57358486149 := by
        calc
          (79 : ZMod 274010536801) ^ 9448639200 = (79 : ZMod 274010536801) ^ (4724319600 + 4724319600) :=
            congrArg (fun n : ℕ => (79 : ZMod 274010536801) ^ n) (by norm_num)
          _ = (79 : ZMod 274010536801) ^ 4724319600 * (79 : ZMod 274010536801) ^ 4724319600 := by rw [pow_add]
          _ = 57358486149 := by rw [factor_8_32]; decide
      change (79 : ZMod 274010536801) ^ 9448639200 ≠ 1
      rw [factor_8_33]
      decide

#print axioms prime_lucas_274010536801

end TotientTailPeriodKiller
end Erdos249257
