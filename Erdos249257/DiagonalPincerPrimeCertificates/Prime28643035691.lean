import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime2864303569

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_28643035691 : Nat.Prime 28643035691 := by
  apply lucas_primality 28643035691 (2 : ZMod 28643035691)
  ·
      have fermat_0 : (2 : ZMod 28643035691) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 28643035691) ^ 3 = 8 := by
        calc
          (2 : ZMod 28643035691) ^ 3 = (2 : ZMod 28643035691) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 1 * (2 : ZMod 28643035691) ^ 1) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 28643035691) ^ 6 = 64 := by
        calc
          (2 : ZMod 28643035691) ^ 6 = (2 : ZMod 28643035691) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 3 * (2 : ZMod 28643035691) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 28643035691) ^ 13 = 8192 := by
        calc
          (2 : ZMod 28643035691) ^ 13 = (2 : ZMod 28643035691) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 6 * (2 : ZMod 28643035691) ^ 6) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 28643035691) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 28643035691) ^ 26 = (2 : ZMod 28643035691) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 13 * (2 : ZMod 28643035691) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 28643035691) ^ 53 = 24322242059 := by
        calc
          (2 : ZMod 28643035691) ^ 53 = (2 : ZMod 28643035691) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 26 * (2 : ZMod 28643035691) ^ 26) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 24322242059 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 28643035691) ^ 106 = 997193727 := by
        calc
          (2 : ZMod 28643035691) ^ 106 = (2 : ZMod 28643035691) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 53 * (2 : ZMod 28643035691) ^ 53 := by rw [pow_add]
          _ = 997193727 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 28643035691) ^ 213 = 14720453 := by
        calc
          (2 : ZMod 28643035691) ^ 213 = (2 : ZMod 28643035691) ^ (106 + 106 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 106 * (2 : ZMod 28643035691) ^ 106) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 14720453 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 28643035691) ^ 426 = 7171522794 := by
        calc
          (2 : ZMod 28643035691) ^ 426 = (2 : ZMod 28643035691) ^ (213 + 213) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 213 * (2 : ZMod 28643035691) ^ 213 := by rw [pow_add]
          _ = 7171522794 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 28643035691) ^ 853 = 17591730270 := by
        calc
          (2 : ZMod 28643035691) ^ 853 = (2 : ZMod 28643035691) ^ (426 + 426 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 426 * (2 : ZMod 28643035691) ^ 426) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 17591730270 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 28643035691) ^ 1707 = 6924574013 := by
        calc
          (2 : ZMod 28643035691) ^ 1707 = (2 : ZMod 28643035691) ^ (853 + 853 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 853 * (2 : ZMod 28643035691) ^ 853) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 6924574013 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 28643035691) ^ 3414 = 20351610459 := by
        calc
          (2 : ZMod 28643035691) ^ 3414 = (2 : ZMod 28643035691) ^ (1707 + 1707) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 1707 * (2 : ZMod 28643035691) ^ 1707 := by rw [pow_add]
          _ = 20351610459 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 28643035691) ^ 6829 = 5454737676 := by
        calc
          (2 : ZMod 28643035691) ^ 6829 = (2 : ZMod 28643035691) ^ (3414 + 3414 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 3414 * (2 : ZMod 28643035691) ^ 3414) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 5454737676 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 28643035691) ^ 13658 = 22692185900 := by
        calc
          (2 : ZMod 28643035691) ^ 13658 = (2 : ZMod 28643035691) ^ (6829 + 6829) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 6829 * (2 : ZMod 28643035691) ^ 6829 := by rw [pow_add]
          _ = 22692185900 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 28643035691) ^ 27316 = 25534049292 := by
        calc
          (2 : ZMod 28643035691) ^ 27316 = (2 : ZMod 28643035691) ^ (13658 + 13658) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 13658 * (2 : ZMod 28643035691) ^ 13658 := by rw [pow_add]
          _ = 25534049292 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 28643035691) ^ 54632 = 10895810208 := by
        calc
          (2 : ZMod 28643035691) ^ 54632 = (2 : ZMod 28643035691) ^ (27316 + 27316) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 27316 * (2 : ZMod 28643035691) ^ 27316 := by rw [pow_add]
          _ = 10895810208 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 28643035691) ^ 109264 = 20916196938 := by
        calc
          (2 : ZMod 28643035691) ^ 109264 = (2 : ZMod 28643035691) ^ (54632 + 54632) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 54632 * (2 : ZMod 28643035691) ^ 54632 := by rw [pow_add]
          _ = 20916196938 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 28643035691) ^ 218529 = 2074478158 := by
        calc
          (2 : ZMod 28643035691) ^ 218529 = (2 : ZMod 28643035691) ^ (109264 + 109264 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 109264 * (2 : ZMod 28643035691) ^ 109264) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 2074478158 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 28643035691) ^ 437058 = 20993338588 := by
        calc
          (2 : ZMod 28643035691) ^ 437058 = (2 : ZMod 28643035691) ^ (218529 + 218529) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 218529 * (2 : ZMod 28643035691) ^ 218529 := by rw [pow_add]
          _ = 20993338588 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 28643035691) ^ 874116 = 5608352407 := by
        calc
          (2 : ZMod 28643035691) ^ 874116 = (2 : ZMod 28643035691) ^ (437058 + 437058) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 437058 * (2 : ZMod 28643035691) ^ 437058 := by rw [pow_add]
          _ = 5608352407 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 28643035691) ^ 1748232 = 23671340648 := by
        calc
          (2 : ZMod 28643035691) ^ 1748232 = (2 : ZMod 28643035691) ^ (874116 + 874116) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 874116 * (2 : ZMod 28643035691) ^ 874116 := by rw [pow_add]
          _ = 23671340648 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 28643035691) ^ 3496464 = 26950377293 := by
        calc
          (2 : ZMod 28643035691) ^ 3496464 = (2 : ZMod 28643035691) ^ (1748232 + 1748232) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 1748232 * (2 : ZMod 28643035691) ^ 1748232 := by rw [pow_add]
          _ = 26950377293 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 28643035691) ^ 6992928 = 25373960573 := by
        calc
          (2 : ZMod 28643035691) ^ 6992928 = (2 : ZMod 28643035691) ^ (3496464 + 3496464) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 3496464 * (2 : ZMod 28643035691) ^ 3496464 := by rw [pow_add]
          _ = 25373960573 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 28643035691) ^ 13985857 = 1225519606 := by
        calc
          (2 : ZMod 28643035691) ^ 13985857 = (2 : ZMod 28643035691) ^ (6992928 + 6992928 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 6992928 * (2 : ZMod 28643035691) ^ 6992928) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 1225519606 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 28643035691) ^ 27971714 = 12156917961 := by
        calc
          (2 : ZMod 28643035691) ^ 27971714 = (2 : ZMod 28643035691) ^ (13985857 + 13985857) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 13985857 * (2 : ZMod 28643035691) ^ 13985857 := by rw [pow_add]
          _ = 12156917961 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 28643035691) ^ 55943429 = 24657104296 := by
        calc
          (2 : ZMod 28643035691) ^ 55943429 = (2 : ZMod 28643035691) ^ (27971714 + 27971714 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 27971714 * (2 : ZMod 28643035691) ^ 27971714) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 24657104296 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 28643035691) ^ 111886858 = 23498959138 := by
        calc
          (2 : ZMod 28643035691) ^ 111886858 = (2 : ZMod 28643035691) ^ (55943429 + 55943429) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 55943429 * (2 : ZMod 28643035691) ^ 55943429 := by rw [pow_add]
          _ = 23498959138 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 28643035691) ^ 223773716 = 8072838522 := by
        calc
          (2 : ZMod 28643035691) ^ 223773716 = (2 : ZMod 28643035691) ^ (111886858 + 111886858) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 111886858 * (2 : ZMod 28643035691) ^ 111886858 := by rw [pow_add]
          _ = 8072838522 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 28643035691) ^ 447547432 = 9257426842 := by
        calc
          (2 : ZMod 28643035691) ^ 447547432 = (2 : ZMod 28643035691) ^ (223773716 + 223773716) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 223773716 * (2 : ZMod 28643035691) ^ 223773716 := by rw [pow_add]
          _ = 9257426842 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 28643035691) ^ 895094865 = 7443739380 := by
        calc
          (2 : ZMod 28643035691) ^ 895094865 = (2 : ZMod 28643035691) ^ (447547432 + 447547432 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 447547432 * (2 : ZMod 28643035691) ^ 447547432) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 7443739380 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 28643035691) ^ 1790189730 = 11751289520 := by
        calc
          (2 : ZMod 28643035691) ^ 1790189730 = (2 : ZMod 28643035691) ^ (895094865 + 895094865) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 895094865 * (2 : ZMod 28643035691) ^ 895094865 := by rw [pow_add]
          _ = 11751289520 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 28643035691) ^ 3580379461 = 10271137646 := by
        calc
          (2 : ZMod 28643035691) ^ 3580379461 = (2 : ZMod 28643035691) ^ (1790189730 + 1790189730 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 1790189730 * (2 : ZMod 28643035691) ^ 1790189730) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 10271137646 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 28643035691) ^ 7160758922 = 1532932940 := by
        calc
          (2 : ZMod 28643035691) ^ 7160758922 = (2 : ZMod 28643035691) ^ (3580379461 + 3580379461) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 3580379461 * (2 : ZMod 28643035691) ^ 3580379461 := by rw [pow_add]
          _ = 1532932940 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 28643035691) ^ 14321517845 = 28643035690 := by
        calc
          (2 : ZMod 28643035691) ^ 14321517845 = (2 : ZMod 28643035691) ^ (7160758922 + 7160758922 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 7160758922 * (2 : ZMod 28643035691) ^ 7160758922) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 28643035690 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 28643035691) ^ 28643035690 = 1 := by
        calc
          (2 : ZMod 28643035691) ^ 28643035690 = (2 : ZMod 28643035691) ^ (14321517845 + 14321517845) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 14321517845 * (2 : ZMod 28643035691) ^ 14321517845 := by rw [pow_add]
          _ = 1 := by rw [fermat_33]; decide
      simpa using fermat_34
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (2864303569, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (2864303569, 1)] : List FactorBlock).map factorBlockValue).prod = 28643035691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_2864303569) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 28643035691) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 28643035691) ^ 3 = 8 := by
        calc
          (2 : ZMod 28643035691) ^ 3 = (2 : ZMod 28643035691) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 1 * (2 : ZMod 28643035691) ^ 1) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 28643035691) ^ 6 = 64 := by
        calc
          (2 : ZMod 28643035691) ^ 6 = (2 : ZMod 28643035691) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 3 * (2 : ZMod 28643035691) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 28643035691) ^ 13 = 8192 := by
        calc
          (2 : ZMod 28643035691) ^ 13 = (2 : ZMod 28643035691) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 6 * (2 : ZMod 28643035691) ^ 6) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 28643035691) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 28643035691) ^ 26 = (2 : ZMod 28643035691) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 13 * (2 : ZMod 28643035691) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 28643035691) ^ 53 = 24322242059 := by
        calc
          (2 : ZMod 28643035691) ^ 53 = (2 : ZMod 28643035691) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 26 * (2 : ZMod 28643035691) ^ 26) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 24322242059 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 28643035691) ^ 106 = 997193727 := by
        calc
          (2 : ZMod 28643035691) ^ 106 = (2 : ZMod 28643035691) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 53 * (2 : ZMod 28643035691) ^ 53 := by rw [pow_add]
          _ = 997193727 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 28643035691) ^ 213 = 14720453 := by
        calc
          (2 : ZMod 28643035691) ^ 213 = (2 : ZMod 28643035691) ^ (106 + 106 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 106 * (2 : ZMod 28643035691) ^ 106) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 14720453 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 28643035691) ^ 426 = 7171522794 := by
        calc
          (2 : ZMod 28643035691) ^ 426 = (2 : ZMod 28643035691) ^ (213 + 213) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 213 * (2 : ZMod 28643035691) ^ 213 := by rw [pow_add]
          _ = 7171522794 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 28643035691) ^ 853 = 17591730270 := by
        calc
          (2 : ZMod 28643035691) ^ 853 = (2 : ZMod 28643035691) ^ (426 + 426 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 426 * (2 : ZMod 28643035691) ^ 426) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 17591730270 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 28643035691) ^ 1707 = 6924574013 := by
        calc
          (2 : ZMod 28643035691) ^ 1707 = (2 : ZMod 28643035691) ^ (853 + 853 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 853 * (2 : ZMod 28643035691) ^ 853) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 6924574013 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 28643035691) ^ 3414 = 20351610459 := by
        calc
          (2 : ZMod 28643035691) ^ 3414 = (2 : ZMod 28643035691) ^ (1707 + 1707) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 1707 * (2 : ZMod 28643035691) ^ 1707 := by rw [pow_add]
          _ = 20351610459 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 28643035691) ^ 6829 = 5454737676 := by
        calc
          (2 : ZMod 28643035691) ^ 6829 = (2 : ZMod 28643035691) ^ (3414 + 3414 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 3414 * (2 : ZMod 28643035691) ^ 3414) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 5454737676 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 28643035691) ^ 13658 = 22692185900 := by
        calc
          (2 : ZMod 28643035691) ^ 13658 = (2 : ZMod 28643035691) ^ (6829 + 6829) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 6829 * (2 : ZMod 28643035691) ^ 6829 := by rw [pow_add]
          _ = 22692185900 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 28643035691) ^ 27316 = 25534049292 := by
        calc
          (2 : ZMod 28643035691) ^ 27316 = (2 : ZMod 28643035691) ^ (13658 + 13658) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 13658 * (2 : ZMod 28643035691) ^ 13658 := by rw [pow_add]
          _ = 25534049292 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 28643035691) ^ 54632 = 10895810208 := by
        calc
          (2 : ZMod 28643035691) ^ 54632 = (2 : ZMod 28643035691) ^ (27316 + 27316) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 27316 * (2 : ZMod 28643035691) ^ 27316 := by rw [pow_add]
          _ = 10895810208 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 28643035691) ^ 109264 = 20916196938 := by
        calc
          (2 : ZMod 28643035691) ^ 109264 = (2 : ZMod 28643035691) ^ (54632 + 54632) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 54632 * (2 : ZMod 28643035691) ^ 54632 := by rw [pow_add]
          _ = 20916196938 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 28643035691) ^ 218529 = 2074478158 := by
        calc
          (2 : ZMod 28643035691) ^ 218529 = (2 : ZMod 28643035691) ^ (109264 + 109264 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 109264 * (2 : ZMod 28643035691) ^ 109264) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 2074478158 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 28643035691) ^ 437058 = 20993338588 := by
        calc
          (2 : ZMod 28643035691) ^ 437058 = (2 : ZMod 28643035691) ^ (218529 + 218529) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 218529 * (2 : ZMod 28643035691) ^ 218529 := by rw [pow_add]
          _ = 20993338588 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 28643035691) ^ 874116 = 5608352407 := by
        calc
          (2 : ZMod 28643035691) ^ 874116 = (2 : ZMod 28643035691) ^ (437058 + 437058) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 437058 * (2 : ZMod 28643035691) ^ 437058 := by rw [pow_add]
          _ = 5608352407 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 28643035691) ^ 1748232 = 23671340648 := by
        calc
          (2 : ZMod 28643035691) ^ 1748232 = (2 : ZMod 28643035691) ^ (874116 + 874116) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 874116 * (2 : ZMod 28643035691) ^ 874116 := by rw [pow_add]
          _ = 23671340648 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 28643035691) ^ 3496464 = 26950377293 := by
        calc
          (2 : ZMod 28643035691) ^ 3496464 = (2 : ZMod 28643035691) ^ (1748232 + 1748232) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 1748232 * (2 : ZMod 28643035691) ^ 1748232 := by rw [pow_add]
          _ = 26950377293 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 28643035691) ^ 6992928 = 25373960573 := by
        calc
          (2 : ZMod 28643035691) ^ 6992928 = (2 : ZMod 28643035691) ^ (3496464 + 3496464) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 3496464 * (2 : ZMod 28643035691) ^ 3496464 := by rw [pow_add]
          _ = 25373960573 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 28643035691) ^ 13985857 = 1225519606 := by
        calc
          (2 : ZMod 28643035691) ^ 13985857 = (2 : ZMod 28643035691) ^ (6992928 + 6992928 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 6992928 * (2 : ZMod 28643035691) ^ 6992928) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 1225519606 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 28643035691) ^ 27971714 = 12156917961 := by
        calc
          (2 : ZMod 28643035691) ^ 27971714 = (2 : ZMod 28643035691) ^ (13985857 + 13985857) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 13985857 * (2 : ZMod 28643035691) ^ 13985857 := by rw [pow_add]
          _ = 12156917961 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 28643035691) ^ 55943429 = 24657104296 := by
        calc
          (2 : ZMod 28643035691) ^ 55943429 = (2 : ZMod 28643035691) ^ (27971714 + 27971714 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 27971714 * (2 : ZMod 28643035691) ^ 27971714) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 24657104296 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 28643035691) ^ 111886858 = 23498959138 := by
        calc
          (2 : ZMod 28643035691) ^ 111886858 = (2 : ZMod 28643035691) ^ (55943429 + 55943429) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 55943429 * (2 : ZMod 28643035691) ^ 55943429 := by rw [pow_add]
          _ = 23498959138 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 28643035691) ^ 223773716 = 8072838522 := by
        calc
          (2 : ZMod 28643035691) ^ 223773716 = (2 : ZMod 28643035691) ^ (111886858 + 111886858) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 111886858 * (2 : ZMod 28643035691) ^ 111886858 := by rw [pow_add]
          _ = 8072838522 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 28643035691) ^ 447547432 = 9257426842 := by
        calc
          (2 : ZMod 28643035691) ^ 447547432 = (2 : ZMod 28643035691) ^ (223773716 + 223773716) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 223773716 * (2 : ZMod 28643035691) ^ 223773716 := by rw [pow_add]
          _ = 9257426842 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 28643035691) ^ 895094865 = 7443739380 := by
        calc
          (2 : ZMod 28643035691) ^ 895094865 = (2 : ZMod 28643035691) ^ (447547432 + 447547432 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 447547432 * (2 : ZMod 28643035691) ^ 447547432) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 7443739380 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 28643035691) ^ 1790189730 = 11751289520 := by
        calc
          (2 : ZMod 28643035691) ^ 1790189730 = (2 : ZMod 28643035691) ^ (895094865 + 895094865) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 895094865 * (2 : ZMod 28643035691) ^ 895094865 := by rw [pow_add]
          _ = 11751289520 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 28643035691) ^ 3580379461 = 10271137646 := by
        calc
          (2 : ZMod 28643035691) ^ 3580379461 = (2 : ZMod 28643035691) ^ (1790189730 + 1790189730 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 1790189730 * (2 : ZMod 28643035691) ^ 1790189730) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 10271137646 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 28643035691) ^ 7160758922 = 1532932940 := by
        calc
          (2 : ZMod 28643035691) ^ 7160758922 = (2 : ZMod 28643035691) ^ (3580379461 + 3580379461) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 3580379461 * (2 : ZMod 28643035691) ^ 3580379461 := by rw [pow_add]
          _ = 1532932940 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 28643035691) ^ 14321517845 = 28643035690 := by
        calc
          (2 : ZMod 28643035691) ^ 14321517845 = (2 : ZMod 28643035691) ^ (7160758922 + 7160758922 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 7160758922 * (2 : ZMod 28643035691) ^ 7160758922) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 28643035690 := by rw [factor_0_32]; decide
      change (2 : ZMod 28643035691) ^ 14321517845 ≠ 1
      rw [factor_0_33]
      decide
    ·
      have factor_1_0 : (2 : ZMod 28643035691) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 28643035691) ^ 2 = 4 := by
        calc
          (2 : ZMod 28643035691) ^ 2 = (2 : ZMod 28643035691) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 1 * (2 : ZMod 28643035691) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 28643035691) ^ 5 = 32 := by
        calc
          (2 : ZMod 28643035691) ^ 5 = (2 : ZMod 28643035691) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 2 * (2 : ZMod 28643035691) ^ 2) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 28643035691) ^ 10 = 1024 := by
        calc
          (2 : ZMod 28643035691) ^ 10 = (2 : ZMod 28643035691) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 5 * (2 : ZMod 28643035691) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 28643035691) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 28643035691) ^ 21 = (2 : ZMod 28643035691) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 10 * (2 : ZMod 28643035691) ^ 10) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 28643035691) ^ 42 = 15662050381 := by
        calc
          (2 : ZMod 28643035691) ^ 42 = (2 : ZMod 28643035691) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 21 * (2 : ZMod 28643035691) ^ 21 := by rw [pow_add]
          _ = 15662050381 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 28643035691) ^ 85 = 7596110180 := by
        calc
          (2 : ZMod 28643035691) ^ 85 = (2 : ZMod 28643035691) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 42 * (2 : ZMod 28643035691) ^ 42) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 7596110180 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 28643035691) ^ 170 = 16760078550 := by
        calc
          (2 : ZMod 28643035691) ^ 170 = (2 : ZMod 28643035691) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 85 * (2 : ZMod 28643035691) ^ 85 := by rw [pow_add]
          _ = 16760078550 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 28643035691) ^ 341 = 22582388119 := by
        calc
          (2 : ZMod 28643035691) ^ 341 = (2 : ZMod 28643035691) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 170 * (2 : ZMod 28643035691) ^ 170) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 22582388119 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 28643035691) ^ 682 = 362571990 := by
        calc
          (2 : ZMod 28643035691) ^ 682 = (2 : ZMod 28643035691) ^ (341 + 341) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 341 * (2 : ZMod 28643035691) ^ 341 := by rw [pow_add]
          _ = 362571990 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 28643035691) ^ 1365 = 7956361774 := by
        calc
          (2 : ZMod 28643035691) ^ 1365 = (2 : ZMod 28643035691) ^ (682 + 682 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 682 * (2 : ZMod 28643035691) ^ 682) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 7956361774 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 28643035691) ^ 2731 = 27318733769 := by
        calc
          (2 : ZMod 28643035691) ^ 2731 = (2 : ZMod 28643035691) ^ (1365 + 1365 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 1365 * (2 : ZMod 28643035691) ^ 1365) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 27318733769 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 28643035691) ^ 5463 = 26616402897 := by
        calc
          (2 : ZMod 28643035691) ^ 5463 = (2 : ZMod 28643035691) ^ (2731 + 2731 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 2731 * (2 : ZMod 28643035691) ^ 2731) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 26616402897 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 28643035691) ^ 10926 = 19334743251 := by
        calc
          (2 : ZMod 28643035691) ^ 10926 = (2 : ZMod 28643035691) ^ (5463 + 5463) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 5463 * (2 : ZMod 28643035691) ^ 5463 := by rw [pow_add]
          _ = 19334743251 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 28643035691) ^ 21852 = 27525263813 := by
        calc
          (2 : ZMod 28643035691) ^ 21852 = (2 : ZMod 28643035691) ^ (10926 + 10926) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 10926 * (2 : ZMod 28643035691) ^ 10926 := by rw [pow_add]
          _ = 27525263813 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 28643035691) ^ 43705 = 27967640047 := by
        calc
          (2 : ZMod 28643035691) ^ 43705 = (2 : ZMod 28643035691) ^ (21852 + 21852 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 21852 * (2 : ZMod 28643035691) ^ 21852) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 27967640047 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 28643035691) ^ 87411 = 27659851661 := by
        calc
          (2 : ZMod 28643035691) ^ 87411 = (2 : ZMod 28643035691) ^ (43705 + 43705 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 43705 * (2 : ZMod 28643035691) ^ 43705) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 27659851661 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 28643035691) ^ 174823 = 22695247855 := by
        calc
          (2 : ZMod 28643035691) ^ 174823 = (2 : ZMod 28643035691) ^ (87411 + 87411 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 87411 * (2 : ZMod 28643035691) ^ 87411) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 22695247855 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 28643035691) ^ 349646 = 14666749777 := by
        calc
          (2 : ZMod 28643035691) ^ 349646 = (2 : ZMod 28643035691) ^ (174823 + 174823) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 174823 * (2 : ZMod 28643035691) ^ 174823 := by rw [pow_add]
          _ = 14666749777 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 28643035691) ^ 699292 = 18668979756 := by
        calc
          (2 : ZMod 28643035691) ^ 699292 = (2 : ZMod 28643035691) ^ (349646 + 349646) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 349646 * (2 : ZMod 28643035691) ^ 349646 := by rw [pow_add]
          _ = 18668979756 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 28643035691) ^ 1398585 = 6727026284 := by
        calc
          (2 : ZMod 28643035691) ^ 1398585 = (2 : ZMod 28643035691) ^ (699292 + 699292 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 699292 * (2 : ZMod 28643035691) ^ 699292) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 6727026284 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 28643035691) ^ 2797171 = 7870598841 := by
        calc
          (2 : ZMod 28643035691) ^ 2797171 = (2 : ZMod 28643035691) ^ (1398585 + 1398585 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 1398585 * (2 : ZMod 28643035691) ^ 1398585) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 7870598841 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 28643035691) ^ 5594342 = 2105941395 := by
        calc
          (2 : ZMod 28643035691) ^ 5594342 = (2 : ZMod 28643035691) ^ (2797171 + 2797171) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 2797171 * (2 : ZMod 28643035691) ^ 2797171 := by rw [pow_add]
          _ = 2105941395 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 28643035691) ^ 11188685 = 3716659057 := by
        calc
          (2 : ZMod 28643035691) ^ 11188685 = (2 : ZMod 28643035691) ^ (5594342 + 5594342 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 5594342 * (2 : ZMod 28643035691) ^ 5594342) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 3716659057 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 28643035691) ^ 22377371 = 801848256 := by
        calc
          (2 : ZMod 28643035691) ^ 22377371 = (2 : ZMod 28643035691) ^ (11188685 + 11188685 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 11188685 * (2 : ZMod 28643035691) ^ 11188685) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 801848256 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 28643035691) ^ 44754743 = 12144817406 := by
        calc
          (2 : ZMod 28643035691) ^ 44754743 = (2 : ZMod 28643035691) ^ (22377371 + 22377371 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 22377371 * (2 : ZMod 28643035691) ^ 22377371) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 12144817406 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 28643035691) ^ 89509486 = 26208338620 := by
        calc
          (2 : ZMod 28643035691) ^ 89509486 = (2 : ZMod 28643035691) ^ (44754743 + 44754743) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 44754743 * (2 : ZMod 28643035691) ^ 44754743 := by rw [pow_add]
          _ = 26208338620 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 28643035691) ^ 179018973 = 14649677724 := by
        calc
          (2 : ZMod 28643035691) ^ 179018973 = (2 : ZMod 28643035691) ^ (89509486 + 89509486 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 89509486 * (2 : ZMod 28643035691) ^ 89509486) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 14649677724 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 28643035691) ^ 358037946 = 6803833586 := by
        calc
          (2 : ZMod 28643035691) ^ 358037946 = (2 : ZMod 28643035691) ^ (179018973 + 179018973) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 179018973 * (2 : ZMod 28643035691) ^ 179018973 := by rw [pow_add]
          _ = 6803833586 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 28643035691) ^ 716075892 = 17836117472 := by
        calc
          (2 : ZMod 28643035691) ^ 716075892 = (2 : ZMod 28643035691) ^ (358037946 + 358037946) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 358037946 * (2 : ZMod 28643035691) ^ 358037946 := by rw [pow_add]
          _ = 17836117472 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 28643035691) ^ 1432151784 = 3664602285 := by
        calc
          (2 : ZMod 28643035691) ^ 1432151784 = (2 : ZMod 28643035691) ^ (716075892 + 716075892) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 716075892 * (2 : ZMod 28643035691) ^ 716075892 := by rw [pow_add]
          _ = 3664602285 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 28643035691) ^ 2864303569 = 19650386361 := by
        calc
          (2 : ZMod 28643035691) ^ 2864303569 = (2 : ZMod 28643035691) ^ (1432151784 + 1432151784 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 1432151784 * (2 : ZMod 28643035691) ^ 1432151784) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 19650386361 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 28643035691) ^ 5728607138 = 540463092 := by
        calc
          (2 : ZMod 28643035691) ^ 5728607138 = (2 : ZMod 28643035691) ^ (2864303569 + 2864303569) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 2864303569 * (2 : ZMod 28643035691) ^ 2864303569 := by rw [pow_add]
          _ = 540463092 := by rw [factor_1_31]; decide
      change (2 : ZMod 28643035691) ^ 5728607138 ≠ 1
      rw [factor_1_32]
      decide
    ·
      have factor_2_0 : (2 : ZMod 28643035691) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 28643035691) ^ 2 = 4 := by
        calc
          (2 : ZMod 28643035691) ^ 2 = (2 : ZMod 28643035691) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 1 * (2 : ZMod 28643035691) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 28643035691) ^ 5 = 32 := by
        calc
          (2 : ZMod 28643035691) ^ 5 = (2 : ZMod 28643035691) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = ((2 : ZMod 28643035691) ^ 2 * (2 : ZMod 28643035691) ^ 2) * (2 : ZMod 28643035691) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 28643035691) ^ 10 = 1024 := by
        calc
          (2 : ZMod 28643035691) ^ 10 = (2 : ZMod 28643035691) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 28643035691) ^ n) (by norm_num)
          _ = (2 : ZMod 28643035691) ^ 5 * (2 : ZMod 28643035691) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_2_2]; decide
      change (2 : ZMod 28643035691) ^ 10 ≠ 1
      rw [factor_2_3]
      decide

#print axioms prime_lucas_28643035691

end TotientTailPeriodKiller
end Erdos249257
