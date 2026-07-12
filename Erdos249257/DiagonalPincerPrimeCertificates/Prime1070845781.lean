import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=23 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1070845781 : Nat.Prime 1070845781 := by
  apply lucas_primality 1070845781 (2 : ZMod 1070845781)
  ·
      have fermat_0 : (2 : ZMod 1070845781) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 1070845781) ^ 3 = 8 := by
        calc
          (2 : ZMod 1070845781) ^ 3 = (2 : ZMod 1070845781) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 1 * (2 : ZMod 1070845781) ^ 1) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 1070845781) ^ 7 = 128 := by
        calc
          (2 : ZMod 1070845781) ^ 7 = (2 : ZMod 1070845781) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 3 * (2 : ZMod 1070845781) ^ 3) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 1070845781) ^ 15 = 32768 := by
        calc
          (2 : ZMod 1070845781) ^ 15 = (2 : ZMod 1070845781) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 7 * (2 : ZMod 1070845781) ^ 7) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 1070845781) ^ 31 = 5792086 := by
        calc
          (2 : ZMod 1070845781) ^ 31 = (2 : ZMod 1070845781) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 15 * (2 : ZMod 1070845781) ^ 15) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 5792086 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 1070845781) ^ 63 = 536362675 := by
        calc
          (2 : ZMod 1070845781) ^ 63 = (2 : ZMod 1070845781) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 31 * (2 : ZMod 1070845781) ^ 31) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 536362675 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 1070845781) ^ 127 = 29697121 := by
        calc
          (2 : ZMod 1070845781) ^ 127 = (2 : ZMod 1070845781) ^ (63 + 63 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 63 * (2 : ZMod 1070845781) ^ 63) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 29697121 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 1070845781) ^ 255 = 788277818 := by
        calc
          (2 : ZMod 1070845781) ^ 255 = (2 : ZMod 1070845781) ^ (127 + 127 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 127 * (2 : ZMod 1070845781) ^ 127) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 788277818 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 1070845781) ^ 510 = 13134615 := by
        calc
          (2 : ZMod 1070845781) ^ 510 = (2 : ZMod 1070845781) ^ (255 + 255) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 255 * (2 : ZMod 1070845781) ^ 255 := by rw [pow_add]
          _ = 13134615 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 1070845781) ^ 1021 = 74146221 := by
        calc
          (2 : ZMod 1070845781) ^ 1021 = (2 : ZMod 1070845781) ^ (510 + 510 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 510 * (2 : ZMod 1070845781) ^ 510) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 74146221 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 1070845781) ^ 2042 = 887136358 := by
        calc
          (2 : ZMod 1070845781) ^ 2042 = (2 : ZMod 1070845781) ^ (1021 + 1021) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 1021 * (2 : ZMod 1070845781) ^ 1021 := by rw [pow_add]
          _ = 887136358 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 1070845781) ^ 4084 = 598127798 := by
        calc
          (2 : ZMod 1070845781) ^ 4084 = (2 : ZMod 1070845781) ^ (2042 + 2042) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 2042 * (2 : ZMod 1070845781) ^ 2042 := by rw [pow_add]
          _ = 598127798 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 1070845781) ^ 8169 = 778681672 := by
        calc
          (2 : ZMod 1070845781) ^ 8169 = (2 : ZMod 1070845781) ^ (4084 + 4084 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 4084 * (2 : ZMod 1070845781) ^ 4084) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 778681672 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 1070845781) ^ 16339 = 1046268108 := by
        calc
          (2 : ZMod 1070845781) ^ 16339 = (2 : ZMod 1070845781) ^ (8169 + 8169 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 8169 * (2 : ZMod 1070845781) ^ 8169) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 1046268108 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 1070845781) ^ 32679 = 93448782 := by
        calc
          (2 : ZMod 1070845781) ^ 32679 = (2 : ZMod 1070845781) ^ (16339 + 16339 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 16339 * (2 : ZMod 1070845781) ^ 16339) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 93448782 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 1070845781) ^ 65359 = 661483264 := by
        calc
          (2 : ZMod 1070845781) ^ 65359 = (2 : ZMod 1070845781) ^ (32679 + 32679 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 32679 * (2 : ZMod 1070845781) ^ 32679) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 661483264 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 1070845781) ^ 130718 = 1035776463 := by
        calc
          (2 : ZMod 1070845781) ^ 130718 = (2 : ZMod 1070845781) ^ (65359 + 65359) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 65359 * (2 : ZMod 1070845781) ^ 65359 := by rw [pow_add]
          _ = 1035776463 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 1070845781) ^ 261436 = 323118653 := by
        calc
          (2 : ZMod 1070845781) ^ 261436 = (2 : ZMod 1070845781) ^ (130718 + 130718) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 130718 * (2 : ZMod 1070845781) ^ 130718 := by rw [pow_add]
          _ = 323118653 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 1070845781) ^ 522873 = 721584540 := by
        calc
          (2 : ZMod 1070845781) ^ 522873 = (2 : ZMod 1070845781) ^ (261436 + 261436 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 261436 * (2 : ZMod 1070845781) ^ 261436) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 721584540 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 1070845781) ^ 1045747 = 1057262986 := by
        calc
          (2 : ZMod 1070845781) ^ 1045747 = (2 : ZMod 1070845781) ^ (522873 + 522873 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 522873 * (2 : ZMod 1070845781) ^ 522873) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 1057262986 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 1070845781) ^ 2091495 = 96727537 := by
        calc
          (2 : ZMod 1070845781) ^ 2091495 = (2 : ZMod 1070845781) ^ (1045747 + 1045747 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 1045747 * (2 : ZMod 1070845781) ^ 1045747) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 96727537 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 1070845781) ^ 4182991 = 337143536 := by
        calc
          (2 : ZMod 1070845781) ^ 4182991 = (2 : ZMod 1070845781) ^ (2091495 + 2091495 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 2091495 * (2 : ZMod 1070845781) ^ 2091495) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 337143536 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 1070845781) ^ 8365982 = 1040937554 := by
        calc
          (2 : ZMod 1070845781) ^ 8365982 = (2 : ZMod 1070845781) ^ (4182991 + 4182991) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 4182991 * (2 : ZMod 1070845781) ^ 4182991 := by rw [pow_add]
          _ = 1040937554 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 1070845781) ^ 16731965 = 934768313 := by
        calc
          (2 : ZMod 1070845781) ^ 16731965 = (2 : ZMod 1070845781) ^ (8365982 + 8365982 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 8365982 * (2 : ZMod 1070845781) ^ 8365982) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 934768313 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 1070845781) ^ 33463930 = 272935433 := by
        calc
          (2 : ZMod 1070845781) ^ 33463930 = (2 : ZMod 1070845781) ^ (16731965 + 16731965) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 16731965 * (2 : ZMod 1070845781) ^ 16731965 := by rw [pow_add]
          _ = 272935433 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 1070845781) ^ 66927861 = 558979679 := by
        calc
          (2 : ZMod 1070845781) ^ 66927861 = (2 : ZMod 1070845781) ^ (33463930 + 33463930 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 33463930 * (2 : ZMod 1070845781) ^ 33463930) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 558979679 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 1070845781) ^ 133855722 = 95396058 := by
        calc
          (2 : ZMod 1070845781) ^ 133855722 = (2 : ZMod 1070845781) ^ (66927861 + 66927861) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 66927861 * (2 : ZMod 1070845781) ^ 66927861 := by rw [pow_add]
          _ = 95396058 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 1070845781) ^ 267711445 = 190792115 := by
        calc
          (2 : ZMod 1070845781) ^ 267711445 = (2 : ZMod 1070845781) ^ (133855722 + 133855722 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 133855722 * (2 : ZMod 1070845781) ^ 133855722) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 190792115 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 1070845781) ^ 535422890 = 1070845780 := by
        calc
          (2 : ZMod 1070845781) ^ 535422890 = (2 : ZMod 1070845781) ^ (267711445 + 267711445) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 267711445 * (2 : ZMod 1070845781) ^ 267711445 := by rw [pow_add]
          _ = 1070845780 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 1070845781) ^ 1070845780 = 1 := by
        calc
          (2 : ZMod 1070845781) ^ 1070845780 = (2 : ZMod 1070845781) ^ (535422890 + 535422890) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 535422890 * (2 : ZMod 1070845781) ^ 535422890 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (173, 1), (309493, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (173, 1), (309493, 1)] : List FactorBlock).map factorBlockValue).prod = 1070845781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 1070845781) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 1070845781) ^ 3 = 8 := by
        calc
          (2 : ZMod 1070845781) ^ 3 = (2 : ZMod 1070845781) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 1 * (2 : ZMod 1070845781) ^ 1) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 1070845781) ^ 7 = 128 := by
        calc
          (2 : ZMod 1070845781) ^ 7 = (2 : ZMod 1070845781) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 3 * (2 : ZMod 1070845781) ^ 3) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 1070845781) ^ 15 = 32768 := by
        calc
          (2 : ZMod 1070845781) ^ 15 = (2 : ZMod 1070845781) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 7 * (2 : ZMod 1070845781) ^ 7) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 1070845781) ^ 31 = 5792086 := by
        calc
          (2 : ZMod 1070845781) ^ 31 = (2 : ZMod 1070845781) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 15 * (2 : ZMod 1070845781) ^ 15) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 5792086 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 1070845781) ^ 63 = 536362675 := by
        calc
          (2 : ZMod 1070845781) ^ 63 = (2 : ZMod 1070845781) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 31 * (2 : ZMod 1070845781) ^ 31) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 536362675 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 1070845781) ^ 127 = 29697121 := by
        calc
          (2 : ZMod 1070845781) ^ 127 = (2 : ZMod 1070845781) ^ (63 + 63 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 63 * (2 : ZMod 1070845781) ^ 63) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 29697121 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 1070845781) ^ 255 = 788277818 := by
        calc
          (2 : ZMod 1070845781) ^ 255 = (2 : ZMod 1070845781) ^ (127 + 127 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 127 * (2 : ZMod 1070845781) ^ 127) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 788277818 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 1070845781) ^ 510 = 13134615 := by
        calc
          (2 : ZMod 1070845781) ^ 510 = (2 : ZMod 1070845781) ^ (255 + 255) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 255 * (2 : ZMod 1070845781) ^ 255 := by rw [pow_add]
          _ = 13134615 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 1070845781) ^ 1021 = 74146221 := by
        calc
          (2 : ZMod 1070845781) ^ 1021 = (2 : ZMod 1070845781) ^ (510 + 510 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 510 * (2 : ZMod 1070845781) ^ 510) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 74146221 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 1070845781) ^ 2042 = 887136358 := by
        calc
          (2 : ZMod 1070845781) ^ 2042 = (2 : ZMod 1070845781) ^ (1021 + 1021) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 1021 * (2 : ZMod 1070845781) ^ 1021 := by rw [pow_add]
          _ = 887136358 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 1070845781) ^ 4084 = 598127798 := by
        calc
          (2 : ZMod 1070845781) ^ 4084 = (2 : ZMod 1070845781) ^ (2042 + 2042) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 2042 * (2 : ZMod 1070845781) ^ 2042 := by rw [pow_add]
          _ = 598127798 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 1070845781) ^ 8169 = 778681672 := by
        calc
          (2 : ZMod 1070845781) ^ 8169 = (2 : ZMod 1070845781) ^ (4084 + 4084 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 4084 * (2 : ZMod 1070845781) ^ 4084) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 778681672 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 1070845781) ^ 16339 = 1046268108 := by
        calc
          (2 : ZMod 1070845781) ^ 16339 = (2 : ZMod 1070845781) ^ (8169 + 8169 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 8169 * (2 : ZMod 1070845781) ^ 8169) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 1046268108 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 1070845781) ^ 32679 = 93448782 := by
        calc
          (2 : ZMod 1070845781) ^ 32679 = (2 : ZMod 1070845781) ^ (16339 + 16339 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 16339 * (2 : ZMod 1070845781) ^ 16339) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 93448782 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 1070845781) ^ 65359 = 661483264 := by
        calc
          (2 : ZMod 1070845781) ^ 65359 = (2 : ZMod 1070845781) ^ (32679 + 32679 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 32679 * (2 : ZMod 1070845781) ^ 32679) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 661483264 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 1070845781) ^ 130718 = 1035776463 := by
        calc
          (2 : ZMod 1070845781) ^ 130718 = (2 : ZMod 1070845781) ^ (65359 + 65359) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 65359 * (2 : ZMod 1070845781) ^ 65359 := by rw [pow_add]
          _ = 1035776463 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 1070845781) ^ 261436 = 323118653 := by
        calc
          (2 : ZMod 1070845781) ^ 261436 = (2 : ZMod 1070845781) ^ (130718 + 130718) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 130718 * (2 : ZMod 1070845781) ^ 130718 := by rw [pow_add]
          _ = 323118653 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 1070845781) ^ 522873 = 721584540 := by
        calc
          (2 : ZMod 1070845781) ^ 522873 = (2 : ZMod 1070845781) ^ (261436 + 261436 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 261436 * (2 : ZMod 1070845781) ^ 261436) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 721584540 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 1070845781) ^ 1045747 = 1057262986 := by
        calc
          (2 : ZMod 1070845781) ^ 1045747 = (2 : ZMod 1070845781) ^ (522873 + 522873 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 522873 * (2 : ZMod 1070845781) ^ 522873) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 1057262986 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 1070845781) ^ 2091495 = 96727537 := by
        calc
          (2 : ZMod 1070845781) ^ 2091495 = (2 : ZMod 1070845781) ^ (1045747 + 1045747 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 1045747 * (2 : ZMod 1070845781) ^ 1045747) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 96727537 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 1070845781) ^ 4182991 = 337143536 := by
        calc
          (2 : ZMod 1070845781) ^ 4182991 = (2 : ZMod 1070845781) ^ (2091495 + 2091495 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 2091495 * (2 : ZMod 1070845781) ^ 2091495) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 337143536 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 1070845781) ^ 8365982 = 1040937554 := by
        calc
          (2 : ZMod 1070845781) ^ 8365982 = (2 : ZMod 1070845781) ^ (4182991 + 4182991) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 4182991 * (2 : ZMod 1070845781) ^ 4182991 := by rw [pow_add]
          _ = 1040937554 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 1070845781) ^ 16731965 = 934768313 := by
        calc
          (2 : ZMod 1070845781) ^ 16731965 = (2 : ZMod 1070845781) ^ (8365982 + 8365982 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 8365982 * (2 : ZMod 1070845781) ^ 8365982) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 934768313 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 1070845781) ^ 33463930 = 272935433 := by
        calc
          (2 : ZMod 1070845781) ^ 33463930 = (2 : ZMod 1070845781) ^ (16731965 + 16731965) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 16731965 * (2 : ZMod 1070845781) ^ 16731965 := by rw [pow_add]
          _ = 272935433 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 1070845781) ^ 66927861 = 558979679 := by
        calc
          (2 : ZMod 1070845781) ^ 66927861 = (2 : ZMod 1070845781) ^ (33463930 + 33463930 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 33463930 * (2 : ZMod 1070845781) ^ 33463930) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 558979679 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 1070845781) ^ 133855722 = 95396058 := by
        calc
          (2 : ZMod 1070845781) ^ 133855722 = (2 : ZMod 1070845781) ^ (66927861 + 66927861) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 66927861 * (2 : ZMod 1070845781) ^ 66927861 := by rw [pow_add]
          _ = 95396058 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 1070845781) ^ 267711445 = 190792115 := by
        calc
          (2 : ZMod 1070845781) ^ 267711445 = (2 : ZMod 1070845781) ^ (133855722 + 133855722 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 133855722 * (2 : ZMod 1070845781) ^ 133855722) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 190792115 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 1070845781) ^ 535422890 = 1070845780 := by
        calc
          (2 : ZMod 1070845781) ^ 535422890 = (2 : ZMod 1070845781) ^ (267711445 + 267711445) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 267711445 * (2 : ZMod 1070845781) ^ 267711445 := by rw [pow_add]
          _ = 1070845780 := by rw [factor_0_27]; decide
      change (2 : ZMod 1070845781) ^ 535422890 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (2 : ZMod 1070845781) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 1070845781) ^ 3 = 8 := by
        calc
          (2 : ZMod 1070845781) ^ 3 = (2 : ZMod 1070845781) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 1 * (2 : ZMod 1070845781) ^ 1) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 1070845781) ^ 6 = 64 := by
        calc
          (2 : ZMod 1070845781) ^ 6 = (2 : ZMod 1070845781) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 3 * (2 : ZMod 1070845781) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 1070845781) ^ 12 = 4096 := by
        calc
          (2 : ZMod 1070845781) ^ 12 = (2 : ZMod 1070845781) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 6 * (2 : ZMod 1070845781) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 1070845781) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 1070845781) ^ 25 = (2 : ZMod 1070845781) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 12 * (2 : ZMod 1070845781) ^ 12) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 1070845781) ^ 51 = 675945485 := by
        calc
          (2 : ZMod 1070845781) ^ 51 = (2 : ZMod 1070845781) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 25 * (2 : ZMod 1070845781) ^ 25) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 675945485 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 1070845781) ^ 102 = 705807376 := by
        calc
          (2 : ZMod 1070845781) ^ 102 = (2 : ZMod 1070845781) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 51 * (2 : ZMod 1070845781) ^ 51 := by rw [pow_add]
          _ = 705807376 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 1070845781) ^ 204 = 426485978 := by
        calc
          (2 : ZMod 1070845781) ^ 204 = (2 : ZMod 1070845781) ^ (102 + 102) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 102 * (2 : ZMod 1070845781) ^ 102 := by rw [pow_add]
          _ = 426485978 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 1070845781) ^ 408 = 624019243 := by
        calc
          (2 : ZMod 1070845781) ^ 408 = (2 : ZMod 1070845781) ^ (204 + 204) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 204 * (2 : ZMod 1070845781) ^ 204 := by rw [pow_add]
          _ = 624019243 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 1070845781) ^ 816 = 983713439 := by
        calc
          (2 : ZMod 1070845781) ^ 816 = (2 : ZMod 1070845781) ^ (408 + 408) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 408 * (2 : ZMod 1070845781) ^ 408 := by rw [pow_add]
          _ = 983713439 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 1070845781) ^ 1633 = 167746998 := by
        calc
          (2 : ZMod 1070845781) ^ 1633 = (2 : ZMod 1070845781) ^ (816 + 816 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 816 * (2 : ZMod 1070845781) ^ 816) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 167746998 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 1070845781) ^ 3267 = 195272245 := by
        calc
          (2 : ZMod 1070845781) ^ 3267 = (2 : ZMod 1070845781) ^ (1633 + 1633 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 1633 * (2 : ZMod 1070845781) ^ 1633) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 195272245 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 1070845781) ^ 6535 = 389998380 := by
        calc
          (2 : ZMod 1070845781) ^ 6535 = (2 : ZMod 1070845781) ^ (3267 + 3267 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 3267 * (2 : ZMod 1070845781) ^ 3267) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 389998380 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 1070845781) ^ 13071 = 911383402 := by
        calc
          (2 : ZMod 1070845781) ^ 13071 = (2 : ZMod 1070845781) ^ (6535 + 6535 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 6535 * (2 : ZMod 1070845781) ^ 6535) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 911383402 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 1070845781) ^ 26143 = 956851163 := by
        calc
          (2 : ZMod 1070845781) ^ 26143 = (2 : ZMod 1070845781) ^ (13071 + 13071 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 13071 * (2 : ZMod 1070845781) ^ 13071) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 956851163 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 1070845781) ^ 52287 = 968025938 := by
        calc
          (2 : ZMod 1070845781) ^ 52287 = (2 : ZMod 1070845781) ^ (26143 + 26143 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 26143 * (2 : ZMod 1070845781) ^ 26143) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 968025938 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 1070845781) ^ 104574 = 495851054 := by
        calc
          (2 : ZMod 1070845781) ^ 104574 = (2 : ZMod 1070845781) ^ (52287 + 52287) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 52287 * (2 : ZMod 1070845781) ^ 52287 := by rw [pow_add]
          _ = 495851054 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 1070845781) ^ 209149 = 130683114 := by
        calc
          (2 : ZMod 1070845781) ^ 209149 = (2 : ZMod 1070845781) ^ (104574 + 104574 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 104574 * (2 : ZMod 1070845781) ^ 104574) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 130683114 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 1070845781) ^ 418299 = 429241067 := by
        calc
          (2 : ZMod 1070845781) ^ 418299 = (2 : ZMod 1070845781) ^ (209149 + 209149 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 209149 * (2 : ZMod 1070845781) ^ 209149) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 429241067 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 1070845781) ^ 836598 = 737569780 := by
        calc
          (2 : ZMod 1070845781) ^ 836598 = (2 : ZMod 1070845781) ^ (418299 + 418299) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 418299 * (2 : ZMod 1070845781) ^ 418299 := by rw [pow_add]
          _ = 737569780 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 1070845781) ^ 1673196 = 1031814989 := by
        calc
          (2 : ZMod 1070845781) ^ 1673196 = (2 : ZMod 1070845781) ^ (836598 + 836598) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 836598 * (2 : ZMod 1070845781) ^ 836598 := by rw [pow_add]
          _ = 1031814989 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 1070845781) ^ 3346393 = 765128336 := by
        calc
          (2 : ZMod 1070845781) ^ 3346393 = (2 : ZMod 1070845781) ^ (1673196 + 1673196 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 1673196 * (2 : ZMod 1070845781) ^ 1673196) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 765128336 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 1070845781) ^ 6692786 = 910555932 := by
        calc
          (2 : ZMod 1070845781) ^ 6692786 = (2 : ZMod 1070845781) ^ (3346393 + 3346393) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 3346393 * (2 : ZMod 1070845781) ^ 3346393 := by rw [pow_add]
          _ = 910555932 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 1070845781) ^ 13385572 = 743536371 := by
        calc
          (2 : ZMod 1070845781) ^ 13385572 = (2 : ZMod 1070845781) ^ (6692786 + 6692786) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 6692786 * (2 : ZMod 1070845781) ^ 6692786 := by rw [pow_add]
          _ = 743536371 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 1070845781) ^ 26771144 = 854713730 := by
        calc
          (2 : ZMod 1070845781) ^ 26771144 = (2 : ZMod 1070845781) ^ (13385572 + 13385572) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 13385572 * (2 : ZMod 1070845781) ^ 13385572 := by rw [pow_add]
          _ = 854713730 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 1070845781) ^ 53542289 = 448422308 := by
        calc
          (2 : ZMod 1070845781) ^ 53542289 = (2 : ZMod 1070845781) ^ (26771144 + 26771144 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 26771144 * (2 : ZMod 1070845781) ^ 26771144) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 448422308 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 1070845781) ^ 107084578 = 90800102 := by
        calc
          (2 : ZMod 1070845781) ^ 107084578 = (2 : ZMod 1070845781) ^ (53542289 + 53542289) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 53542289 * (2 : ZMod 1070845781) ^ 53542289 := by rw [pow_add]
          _ = 90800102 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 1070845781) ^ 214169156 = 544443642 := by
        calc
          (2 : ZMod 1070845781) ^ 214169156 = (2 : ZMod 1070845781) ^ (107084578 + 107084578) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 107084578 * (2 : ZMod 1070845781) ^ 107084578 := by rw [pow_add]
          _ = 544443642 := by rw [factor_1_26]; decide
      change (2 : ZMod 1070845781) ^ 214169156 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (2 : ZMod 1070845781) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 1070845781) ^ 2 = 4 := by
        calc
          (2 : ZMod 1070845781) ^ 2 = (2 : ZMod 1070845781) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 1 * (2 : ZMod 1070845781) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 1070845781) ^ 5 = 32 := by
        calc
          (2 : ZMod 1070845781) ^ 5 = (2 : ZMod 1070845781) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 2 * (2 : ZMod 1070845781) ^ 2) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 1070845781) ^ 11 = 2048 := by
        calc
          (2 : ZMod 1070845781) ^ 11 = (2 : ZMod 1070845781) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 5 * (2 : ZMod 1070845781) ^ 5) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 1070845781) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 1070845781) ^ 23 = (2 : ZMod 1070845781) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 11 * (2 : ZMod 1070845781) ^ 11) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 1070845781) ^ 47 = 510741622 := by
        calc
          (2 : ZMod 1070845781) ^ 47 = (2 : ZMod 1070845781) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 23 * (2 : ZMod 1070845781) ^ 23) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 510741622 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 1070845781) ^ 94 = 203540644 := by
        calc
          (2 : ZMod 1070845781) ^ 94 = (2 : ZMod 1070845781) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 47 * (2 : ZMod 1070845781) ^ 47 := by rw [pow_add]
          _ = 203540644 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 1070845781) ^ 188 = 1064806559 := by
        calc
          (2 : ZMod 1070845781) ^ 188 = (2 : ZMod 1070845781) ^ (94 + 94) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 94 * (2 : ZMod 1070845781) ^ 94 := by rw [pow_add]
          _ = 1064806559 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 1070845781) ^ 377 = 531820410 := by
        calc
          (2 : ZMod 1070845781) ^ 377 = (2 : ZMod 1070845781) ^ (188 + 188 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 188 * (2 : ZMod 1070845781) ^ 188) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 531820410 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 1070845781) ^ 755 = 36042992 := by
        calc
          (2 : ZMod 1070845781) ^ 755 = (2 : ZMod 1070845781) ^ (377 + 377 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 377 * (2 : ZMod 1070845781) ^ 377) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 36042992 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 1070845781) ^ 1511 = 355338047 := by
        calc
          (2 : ZMod 1070845781) ^ 1511 = (2 : ZMod 1070845781) ^ (755 + 755 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 755 * (2 : ZMod 1070845781) ^ 755) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 355338047 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 1070845781) ^ 3022 = 34118200 := by
        calc
          (2 : ZMod 1070845781) ^ 3022 = (2 : ZMod 1070845781) ^ (1511 + 1511) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 1511 * (2 : ZMod 1070845781) ^ 1511 := by rw [pow_add]
          _ = 34118200 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 1070845781) ^ 6044 = 444307541 := by
        calc
          (2 : ZMod 1070845781) ^ 6044 = (2 : ZMod 1070845781) ^ (3022 + 3022) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 3022 * (2 : ZMod 1070845781) ^ 3022 := by rw [pow_add]
          _ = 444307541 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 1070845781) ^ 12089 = 115300757 := by
        calc
          (2 : ZMod 1070845781) ^ 12089 = (2 : ZMod 1070845781) ^ (6044 + 6044 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 6044 * (2 : ZMod 1070845781) ^ 6044) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 115300757 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 1070845781) ^ 24179 = 218963152 := by
        calc
          (2 : ZMod 1070845781) ^ 24179 = (2 : ZMod 1070845781) ^ (12089 + 12089 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 12089 * (2 : ZMod 1070845781) ^ 12089) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 218963152 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 1070845781) ^ 48358 = 503252233 := by
        calc
          (2 : ZMod 1070845781) ^ 48358 = (2 : ZMod 1070845781) ^ (24179 + 24179) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 24179 * (2 : ZMod 1070845781) ^ 24179 := by rw [pow_add]
          _ = 503252233 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 1070845781) ^ 96716 = 976695762 := by
        calc
          (2 : ZMod 1070845781) ^ 96716 = (2 : ZMod 1070845781) ^ (48358 + 48358) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 48358 * (2 : ZMod 1070845781) ^ 48358 := by rw [pow_add]
          _ = 976695762 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 1070845781) ^ 193433 = 577308362 := by
        calc
          (2 : ZMod 1070845781) ^ 193433 = (2 : ZMod 1070845781) ^ (96716 + 96716 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 96716 * (2 : ZMod 1070845781) ^ 96716) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 577308362 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 1070845781) ^ 386866 = 111754823 := by
        calc
          (2 : ZMod 1070845781) ^ 386866 = (2 : ZMod 1070845781) ^ (193433 + 193433) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 193433 * (2 : ZMod 1070845781) ^ 193433 := by rw [pow_add]
          _ = 111754823 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 1070845781) ^ 773732 = 1046526735 := by
        calc
          (2 : ZMod 1070845781) ^ 773732 = (2 : ZMod 1070845781) ^ (386866 + 386866) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 386866 * (2 : ZMod 1070845781) ^ 386866 := by rw [pow_add]
          _ = 1046526735 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 1070845781) ^ 1547465 = 376460595 := by
        calc
          (2 : ZMod 1070845781) ^ 1547465 = (2 : ZMod 1070845781) ^ (773732 + 773732 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 773732 * (2 : ZMod 1070845781) ^ 773732) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 376460595 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 1070845781) ^ 3094930 = 871444530 := by
        calc
          (2 : ZMod 1070845781) ^ 3094930 = (2 : ZMod 1070845781) ^ (1547465 + 1547465) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 1547465 * (2 : ZMod 1070845781) ^ 1547465 := by rw [pow_add]
          _ = 871444530 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 1070845781) ^ 6189860 = 601881490 := by
        calc
          (2 : ZMod 1070845781) ^ 6189860 = (2 : ZMod 1070845781) ^ (3094930 + 3094930) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 3094930 * (2 : ZMod 1070845781) ^ 3094930 := by rw [pow_add]
          _ = 601881490 := by rw [factor_2_21]; decide
      change (2 : ZMod 1070845781) ^ 6189860 ≠ 1
      rw [factor_2_22]
      decide
    ·
      have factor_3_0 : (2 : ZMod 1070845781) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 1070845781) ^ 3 = 8 := by
        calc
          (2 : ZMod 1070845781) ^ 3 = (2 : ZMod 1070845781) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 1 * (2 : ZMod 1070845781) ^ 1) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 1070845781) ^ 6 = 64 := by
        calc
          (2 : ZMod 1070845781) ^ 6 = (2 : ZMod 1070845781) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 3 * (2 : ZMod 1070845781) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 1070845781) ^ 13 = 8192 := by
        calc
          (2 : ZMod 1070845781) ^ 13 = (2 : ZMod 1070845781) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 6 * (2 : ZMod 1070845781) ^ 6) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 1070845781) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 1070845781) ^ 27 = (2 : ZMod 1070845781) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 13 * (2 : ZMod 1070845781) ^ 13) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 1070845781) ^ 54 = 53334975 := by
        calc
          (2 : ZMod 1070845781) ^ 54 = (2 : ZMod 1070845781) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 27 * (2 : ZMod 1070845781) ^ 27 := by rw [pow_add]
          _ = 53334975 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 1070845781) ^ 108 = 196149262 := by
        calc
          (2 : ZMod 1070845781) ^ 108 = (2 : ZMod 1070845781) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 54 * (2 : ZMod 1070845781) ^ 54 := by rw [pow_add]
          _ = 196149262 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 1070845781) ^ 216 = 337097077 := by
        calc
          (2 : ZMod 1070845781) ^ 216 = (2 : ZMod 1070845781) ^ (108 + 108) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 108 * (2 : ZMod 1070845781) ^ 108 := by rw [pow_add]
          _ = 337097077 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 1070845781) ^ 432 = 877083999 := by
        calc
          (2 : ZMod 1070845781) ^ 432 = (2 : ZMod 1070845781) ^ (216 + 216) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 216 * (2 : ZMod 1070845781) ^ 216 := by rw [pow_add]
          _ = 877083999 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 1070845781) ^ 865 = 989984849 := by
        calc
          (2 : ZMod 1070845781) ^ 865 = (2 : ZMod 1070845781) ^ (432 + 432 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = ((2 : ZMod 1070845781) ^ 432 * (2 : ZMod 1070845781) ^ 432) * (2 : ZMod 1070845781) := by rw [pow_succ, pow_add]
          _ = 989984849 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 1070845781) ^ 1730 = 219551352 := by
        calc
          (2 : ZMod 1070845781) ^ 1730 = (2 : ZMod 1070845781) ^ (865 + 865) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 865 * (2 : ZMod 1070845781) ^ 865 := by rw [pow_add]
          _ = 219551352 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 1070845781) ^ 3460 = 111235563 := by
        calc
          (2 : ZMod 1070845781) ^ 3460 = (2 : ZMod 1070845781) ^ (1730 + 1730) :=
            congrArg (fun n : ℕ => (2 : ZMod 1070845781) ^ n) (by norm_num)
          _ = (2 : ZMod 1070845781) ^ 1730 * (2 : ZMod 1070845781) ^ 1730 := by rw [pow_add]
          _ = 111235563 := by rw [factor_3_10]; decide
      change (2 : ZMod 1070845781) ^ 3460 ≠ 1
      rw [factor_3_11]
      decide

#print axioms prime_lucas_1070845781

end TotientTailPeriodKiller
end Erdos249257
