import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1931549951 : Nat.Prime 1931549951 := by
  apply lucas_primality 1931549951 (7 : ZMod 1931549951)
  ·
      have fermat_0 : (7 : ZMod 1931549951) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 1931549951) ^ 3 = 343 := by
        calc
          (7 : ZMod 1931549951) ^ 3 = (7 : ZMod 1931549951) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 1 * (7 : ZMod 1931549951) ^ 1) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 1931549951) ^ 7 = 823543 := by
        calc
          (7 : ZMod 1931549951) ^ 7 = (7 : ZMod 1931549951) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 3 * (7 : ZMod 1931549951) ^ 3) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 1931549951) ^ 14 = 249040048 := by
        calc
          (7 : ZMod 1931549951) ^ 14 = (7 : ZMod 1931549951) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 7 * (7 : ZMod 1931549951) ^ 7 := by rw [pow_add]
          _ = 249040048 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 1931549951) ^ 28 = 743303786 := by
        calc
          (7 : ZMod 1931549951) ^ 28 = (7 : ZMod 1931549951) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 14 * (7 : ZMod 1931549951) ^ 14 := by rw [pow_add]
          _ = 743303786 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 1931549951) ^ 57 = 692651280 := by
        calc
          (7 : ZMod 1931549951) ^ 57 = (7 : ZMod 1931549951) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 28 * (7 : ZMod 1931549951) ^ 28) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 692651280 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 1931549951) ^ 115 = 341826214 := by
        calc
          (7 : ZMod 1931549951) ^ 115 = (7 : ZMod 1931549951) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 57 * (7 : ZMod 1931549951) ^ 57) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 341826214 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 1931549951) ^ 230 = 174578493 := by
        calc
          (7 : ZMod 1931549951) ^ 230 = (7 : ZMod 1931549951) ^ (115 + 115) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 115 * (7 : ZMod 1931549951) ^ 115 := by rw [pow_add]
          _ = 174578493 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 1931549951) ^ 460 = 1684514993 := by
        calc
          (7 : ZMod 1931549951) ^ 460 = (7 : ZMod 1931549951) ^ (230 + 230) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 230 * (7 : ZMod 1931549951) ^ 230 := by rw [pow_add]
          _ = 1684514993 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 1931549951) ^ 921 = 1816180805 := by
        calc
          (7 : ZMod 1931549951) ^ 921 = (7 : ZMod 1931549951) ^ (460 + 460 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 460 * (7 : ZMod 1931549951) ^ 460) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1816180805 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 1931549951) ^ 1842 = 1484971407 := by
        calc
          (7 : ZMod 1931549951) ^ 1842 = (7 : ZMod 1931549951) ^ (921 + 921) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 921 * (7 : ZMod 1931549951) ^ 921 := by rw [pow_add]
          _ = 1484971407 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 1931549951) ^ 3684 = 660456457 := by
        calc
          (7 : ZMod 1931549951) ^ 3684 = (7 : ZMod 1931549951) ^ (1842 + 1842) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 1842 * (7 : ZMod 1931549951) ^ 1842 := by rw [pow_add]
          _ = 660456457 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 1931549951) ^ 7368 = 702333282 := by
        calc
          (7 : ZMod 1931549951) ^ 7368 = (7 : ZMod 1931549951) ^ (3684 + 3684) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 3684 * (7 : ZMod 1931549951) ^ 3684 := by rw [pow_add]
          _ = 702333282 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 1931549951) ^ 14736 = 1747429146 := by
        calc
          (7 : ZMod 1931549951) ^ 14736 = (7 : ZMod 1931549951) ^ (7368 + 7368) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 7368 * (7 : ZMod 1931549951) ^ 7368 := by rw [pow_add]
          _ = 1747429146 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 1931549951) ^ 29473 = 1189850314 := by
        calc
          (7 : ZMod 1931549951) ^ 29473 = (7 : ZMod 1931549951) ^ (14736 + 14736 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 14736 * (7 : ZMod 1931549951) ^ 14736) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1189850314 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 1931549951) ^ 58946 = 1480409628 := by
        calc
          (7 : ZMod 1931549951) ^ 58946 = (7 : ZMod 1931549951) ^ (29473 + 29473) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 29473 * (7 : ZMod 1931549951) ^ 29473 := by rw [pow_add]
          _ = 1480409628 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 1931549951) ^ 117892 = 791728690 := by
        calc
          (7 : ZMod 1931549951) ^ 117892 = (7 : ZMod 1931549951) ^ (58946 + 58946) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 58946 * (7 : ZMod 1931549951) ^ 58946 := by rw [pow_add]
          _ = 791728690 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 1931549951) ^ 235784 = 339242149 := by
        calc
          (7 : ZMod 1931549951) ^ 235784 = (7 : ZMod 1931549951) ^ (117892 + 117892) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 117892 * (7 : ZMod 1931549951) ^ 117892 := by rw [pow_add]
          _ = 339242149 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 1931549951) ^ 471569 = 662227061 := by
        calc
          (7 : ZMod 1931549951) ^ 471569 = (7 : ZMod 1931549951) ^ (235784 + 235784 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 235784 * (7 : ZMod 1931549951) ^ 235784) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 662227061 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 1931549951) ^ 943139 = 179594827 := by
        calc
          (7 : ZMod 1931549951) ^ 943139 = (7 : ZMod 1931549951) ^ (471569 + 471569 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 471569 * (7 : ZMod 1931549951) ^ 471569) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 179594827 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 1931549951) ^ 1886279 = 1300210912 := by
        calc
          (7 : ZMod 1931549951) ^ 1886279 = (7 : ZMod 1931549951) ^ (943139 + 943139 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 943139 * (7 : ZMod 1931549951) ^ 943139) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1300210912 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 1931549951) ^ 3772558 = 1444639755 := by
        calc
          (7 : ZMod 1931549951) ^ 3772558 = (7 : ZMod 1931549951) ^ (1886279 + 1886279) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 1886279 * (7 : ZMod 1931549951) ^ 1886279 := by rw [pow_add]
          _ = 1444639755 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 1931549951) ^ 7545116 = 1708446963 := by
        calc
          (7 : ZMod 1931549951) ^ 7545116 = (7 : ZMod 1931549951) ^ (3772558 + 3772558) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 3772558 * (7 : ZMod 1931549951) ^ 3772558 := by rw [pow_add]
          _ = 1708446963 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 1931549951) ^ 15090233 = 484261841 := by
        calc
          (7 : ZMod 1931549951) ^ 15090233 = (7 : ZMod 1931549951) ^ (7545116 + 7545116 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 7545116 * (7 : ZMod 1931549951) ^ 7545116) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 484261841 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 1931549951) ^ 30180467 = 347854032 := by
        calc
          (7 : ZMod 1931549951) ^ 30180467 = (7 : ZMod 1931549951) ^ (15090233 + 15090233 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 15090233 * (7 : ZMod 1931549951) ^ 15090233) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 347854032 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 1931549951) ^ 60360935 = 1527819526 := by
        calc
          (7 : ZMod 1931549951) ^ 60360935 = (7 : ZMod 1931549951) ^ (30180467 + 30180467 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 30180467 * (7 : ZMod 1931549951) ^ 30180467) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1527819526 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 1931549951) ^ 120721871 = 978903081 := by
        calc
          (7 : ZMod 1931549951) ^ 120721871 = (7 : ZMod 1931549951) ^ (60360935 + 60360935 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 60360935 * (7 : ZMod 1931549951) ^ 60360935) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 978903081 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 1931549951) ^ 241443743 = 879801383 := by
        calc
          (7 : ZMod 1931549951) ^ 241443743 = (7 : ZMod 1931549951) ^ (120721871 + 120721871 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 120721871 * (7 : ZMod 1931549951) ^ 120721871) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 879801383 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 1931549951) ^ 482887487 = 1427862320 := by
        calc
          (7 : ZMod 1931549951) ^ 482887487 = (7 : ZMod 1931549951) ^ (241443743 + 241443743 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 241443743 * (7 : ZMod 1931549951) ^ 241443743) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1427862320 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 1931549951) ^ 965774975 = 1931549950 := by
        calc
          (7 : ZMod 1931549951) ^ 965774975 = (7 : ZMod 1931549951) ^ (482887487 + 482887487 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 482887487 * (7 : ZMod 1931549951) ^ 482887487) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1931549950 := by rw [fermat_28]; decide
      have fermat_30 : (7 : ZMod 1931549951) ^ 1931549950 = 1 := by
        calc
          (7 : ZMod 1931549951) ^ 1931549950 = (7 : ZMod 1931549951) ^ (965774975 + 965774975) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 965774975 * (7 : ZMod 1931549951) ^ 965774975 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (11, 1), (1307, 1), (2687, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (11, 1), (1307, 1), (2687, 1)] : List FactorBlock).map factorBlockValue).prod = 1931549951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 1931549951) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 1931549951) ^ 3 = 343 := by
        calc
          (7 : ZMod 1931549951) ^ 3 = (7 : ZMod 1931549951) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 1 * (7 : ZMod 1931549951) ^ 1) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 1931549951) ^ 7 = 823543 := by
        calc
          (7 : ZMod 1931549951) ^ 7 = (7 : ZMod 1931549951) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 3 * (7 : ZMod 1931549951) ^ 3) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 1931549951) ^ 14 = 249040048 := by
        calc
          (7 : ZMod 1931549951) ^ 14 = (7 : ZMod 1931549951) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 7 * (7 : ZMod 1931549951) ^ 7 := by rw [pow_add]
          _ = 249040048 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 1931549951) ^ 28 = 743303786 := by
        calc
          (7 : ZMod 1931549951) ^ 28 = (7 : ZMod 1931549951) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 14 * (7 : ZMod 1931549951) ^ 14 := by rw [pow_add]
          _ = 743303786 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 1931549951) ^ 57 = 692651280 := by
        calc
          (7 : ZMod 1931549951) ^ 57 = (7 : ZMod 1931549951) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 28 * (7 : ZMod 1931549951) ^ 28) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 692651280 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 1931549951) ^ 115 = 341826214 := by
        calc
          (7 : ZMod 1931549951) ^ 115 = (7 : ZMod 1931549951) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 57 * (7 : ZMod 1931549951) ^ 57) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 341826214 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 1931549951) ^ 230 = 174578493 := by
        calc
          (7 : ZMod 1931549951) ^ 230 = (7 : ZMod 1931549951) ^ (115 + 115) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 115 * (7 : ZMod 1931549951) ^ 115 := by rw [pow_add]
          _ = 174578493 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 1931549951) ^ 460 = 1684514993 := by
        calc
          (7 : ZMod 1931549951) ^ 460 = (7 : ZMod 1931549951) ^ (230 + 230) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 230 * (7 : ZMod 1931549951) ^ 230 := by rw [pow_add]
          _ = 1684514993 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 1931549951) ^ 921 = 1816180805 := by
        calc
          (7 : ZMod 1931549951) ^ 921 = (7 : ZMod 1931549951) ^ (460 + 460 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 460 * (7 : ZMod 1931549951) ^ 460) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1816180805 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 1931549951) ^ 1842 = 1484971407 := by
        calc
          (7 : ZMod 1931549951) ^ 1842 = (7 : ZMod 1931549951) ^ (921 + 921) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 921 * (7 : ZMod 1931549951) ^ 921 := by rw [pow_add]
          _ = 1484971407 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 1931549951) ^ 3684 = 660456457 := by
        calc
          (7 : ZMod 1931549951) ^ 3684 = (7 : ZMod 1931549951) ^ (1842 + 1842) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 1842 * (7 : ZMod 1931549951) ^ 1842 := by rw [pow_add]
          _ = 660456457 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 1931549951) ^ 7368 = 702333282 := by
        calc
          (7 : ZMod 1931549951) ^ 7368 = (7 : ZMod 1931549951) ^ (3684 + 3684) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 3684 * (7 : ZMod 1931549951) ^ 3684 := by rw [pow_add]
          _ = 702333282 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 1931549951) ^ 14736 = 1747429146 := by
        calc
          (7 : ZMod 1931549951) ^ 14736 = (7 : ZMod 1931549951) ^ (7368 + 7368) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 7368 * (7 : ZMod 1931549951) ^ 7368 := by rw [pow_add]
          _ = 1747429146 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 1931549951) ^ 29473 = 1189850314 := by
        calc
          (7 : ZMod 1931549951) ^ 29473 = (7 : ZMod 1931549951) ^ (14736 + 14736 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 14736 * (7 : ZMod 1931549951) ^ 14736) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1189850314 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 1931549951) ^ 58946 = 1480409628 := by
        calc
          (7 : ZMod 1931549951) ^ 58946 = (7 : ZMod 1931549951) ^ (29473 + 29473) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 29473 * (7 : ZMod 1931549951) ^ 29473 := by rw [pow_add]
          _ = 1480409628 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 1931549951) ^ 117892 = 791728690 := by
        calc
          (7 : ZMod 1931549951) ^ 117892 = (7 : ZMod 1931549951) ^ (58946 + 58946) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 58946 * (7 : ZMod 1931549951) ^ 58946 := by rw [pow_add]
          _ = 791728690 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 1931549951) ^ 235784 = 339242149 := by
        calc
          (7 : ZMod 1931549951) ^ 235784 = (7 : ZMod 1931549951) ^ (117892 + 117892) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 117892 * (7 : ZMod 1931549951) ^ 117892 := by rw [pow_add]
          _ = 339242149 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 1931549951) ^ 471569 = 662227061 := by
        calc
          (7 : ZMod 1931549951) ^ 471569 = (7 : ZMod 1931549951) ^ (235784 + 235784 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 235784 * (7 : ZMod 1931549951) ^ 235784) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 662227061 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 1931549951) ^ 943139 = 179594827 := by
        calc
          (7 : ZMod 1931549951) ^ 943139 = (7 : ZMod 1931549951) ^ (471569 + 471569 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 471569 * (7 : ZMod 1931549951) ^ 471569) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 179594827 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 1931549951) ^ 1886279 = 1300210912 := by
        calc
          (7 : ZMod 1931549951) ^ 1886279 = (7 : ZMod 1931549951) ^ (943139 + 943139 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 943139 * (7 : ZMod 1931549951) ^ 943139) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1300210912 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 1931549951) ^ 3772558 = 1444639755 := by
        calc
          (7 : ZMod 1931549951) ^ 3772558 = (7 : ZMod 1931549951) ^ (1886279 + 1886279) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 1886279 * (7 : ZMod 1931549951) ^ 1886279 := by rw [pow_add]
          _ = 1444639755 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 1931549951) ^ 7545116 = 1708446963 := by
        calc
          (7 : ZMod 1931549951) ^ 7545116 = (7 : ZMod 1931549951) ^ (3772558 + 3772558) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 3772558 * (7 : ZMod 1931549951) ^ 3772558 := by rw [pow_add]
          _ = 1708446963 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 1931549951) ^ 15090233 = 484261841 := by
        calc
          (7 : ZMod 1931549951) ^ 15090233 = (7 : ZMod 1931549951) ^ (7545116 + 7545116 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 7545116 * (7 : ZMod 1931549951) ^ 7545116) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 484261841 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 1931549951) ^ 30180467 = 347854032 := by
        calc
          (7 : ZMod 1931549951) ^ 30180467 = (7 : ZMod 1931549951) ^ (15090233 + 15090233 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 15090233 * (7 : ZMod 1931549951) ^ 15090233) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 347854032 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 1931549951) ^ 60360935 = 1527819526 := by
        calc
          (7 : ZMod 1931549951) ^ 60360935 = (7 : ZMod 1931549951) ^ (30180467 + 30180467 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 30180467 * (7 : ZMod 1931549951) ^ 30180467) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1527819526 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 1931549951) ^ 120721871 = 978903081 := by
        calc
          (7 : ZMod 1931549951) ^ 120721871 = (7 : ZMod 1931549951) ^ (60360935 + 60360935 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 60360935 * (7 : ZMod 1931549951) ^ 60360935) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 978903081 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 1931549951) ^ 241443743 = 879801383 := by
        calc
          (7 : ZMod 1931549951) ^ 241443743 = (7 : ZMod 1931549951) ^ (120721871 + 120721871 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 120721871 * (7 : ZMod 1931549951) ^ 120721871) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 879801383 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 1931549951) ^ 482887487 = 1427862320 := by
        calc
          (7 : ZMod 1931549951) ^ 482887487 = (7 : ZMod 1931549951) ^ (241443743 + 241443743 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 241443743 * (7 : ZMod 1931549951) ^ 241443743) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1427862320 := by rw [factor_0_27]; decide
      have factor_0_29 : (7 : ZMod 1931549951) ^ 965774975 = 1931549950 := by
        calc
          (7 : ZMod 1931549951) ^ 965774975 = (7 : ZMod 1931549951) ^ (482887487 + 482887487 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 482887487 * (7 : ZMod 1931549951) ^ 482887487) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1931549950 := by rw [factor_0_28]; decide
      change (7 : ZMod 1931549951) ^ 965774975 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (7 : ZMod 1931549951) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 1931549951) ^ 2 = 49 := by
        calc
          (7 : ZMod 1931549951) ^ 2 = (7 : ZMod 1931549951) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 1 * (7 : ZMod 1931549951) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 1931549951) ^ 5 = 16807 := by
        calc
          (7 : ZMod 1931549951) ^ 5 = (7 : ZMod 1931549951) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 2 * (7 : ZMod 1931549951) ^ 2) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 1931549951) ^ 11 = 45776792 := by
        calc
          (7 : ZMod 1931549951) ^ 11 = (7 : ZMod 1931549951) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 5 * (7 : ZMod 1931549951) ^ 5) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 45776792 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 1931549951) ^ 23 = 1052645285 := by
        calc
          (7 : ZMod 1931549951) ^ 23 = (7 : ZMod 1931549951) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 11 * (7 : ZMod 1931549951) ^ 11) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1052645285 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 1931549951) ^ 46 = 1389953338 := by
        calc
          (7 : ZMod 1931549951) ^ 46 = (7 : ZMod 1931549951) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 23 * (7 : ZMod 1931549951) ^ 23 := by rw [pow_add]
          _ = 1389953338 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 1931549951) ^ 92 = 437855281 := by
        calc
          (7 : ZMod 1931549951) ^ 92 = (7 : ZMod 1931549951) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 46 * (7 : ZMod 1931549951) ^ 46 := by rw [pow_add]
          _ = 437855281 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 1931549951) ^ 184 = 1205615811 := by
        calc
          (7 : ZMod 1931549951) ^ 184 = (7 : ZMod 1931549951) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 92 * (7 : ZMod 1931549951) ^ 92 := by rw [pow_add]
          _ = 1205615811 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 1931549951) ^ 368 = 625448027 := by
        calc
          (7 : ZMod 1931549951) ^ 368 = (7 : ZMod 1931549951) ^ (184 + 184) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 184 * (7 : ZMod 1931549951) ^ 184 := by rw [pow_add]
          _ = 625448027 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 1931549951) ^ 736 = 612569023 := by
        calc
          (7 : ZMod 1931549951) ^ 736 = (7 : ZMod 1931549951) ^ (368 + 368) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 368 * (7 : ZMod 1931549951) ^ 368 := by rw [pow_add]
          _ = 612569023 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 1931549951) ^ 1473 = 1119482881 := by
        calc
          (7 : ZMod 1931549951) ^ 1473 = (7 : ZMod 1931549951) ^ (736 + 736 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 736 * (7 : ZMod 1931549951) ^ 736) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1119482881 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 1931549951) ^ 2947 = 1400010645 := by
        calc
          (7 : ZMod 1931549951) ^ 2947 = (7 : ZMod 1931549951) ^ (1473 + 1473 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 1473 * (7 : ZMod 1931549951) ^ 1473) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1400010645 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 1931549951) ^ 5894 = 967799465 := by
        calc
          (7 : ZMod 1931549951) ^ 5894 = (7 : ZMod 1931549951) ^ (2947 + 2947) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 2947 * (7 : ZMod 1931549951) ^ 2947 := by rw [pow_add]
          _ = 967799465 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 1931549951) ^ 11789 = 109839581 := by
        calc
          (7 : ZMod 1931549951) ^ 11789 = (7 : ZMod 1931549951) ^ (5894 + 5894 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 5894 * (7 : ZMod 1931549951) ^ 5894) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 109839581 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 1931549951) ^ 23578 = 211766470 := by
        calc
          (7 : ZMod 1931549951) ^ 23578 = (7 : ZMod 1931549951) ^ (11789 + 11789) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 11789 * (7 : ZMod 1931549951) ^ 11789 := by rw [pow_add]
          _ = 211766470 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 1931549951) ^ 47156 = 1160150025 := by
        calc
          (7 : ZMod 1931549951) ^ 47156 = (7 : ZMod 1931549951) ^ (23578 + 23578) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 23578 * (7 : ZMod 1931549951) ^ 23578 := by rw [pow_add]
          _ = 1160150025 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 1931549951) ^ 94313 = 1875880998 := by
        calc
          (7 : ZMod 1931549951) ^ 94313 = (7 : ZMod 1931549951) ^ (47156 + 47156 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 47156 * (7 : ZMod 1931549951) ^ 47156) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1875880998 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 1931549951) ^ 188627 = 386432169 := by
        calc
          (7 : ZMod 1931549951) ^ 188627 = (7 : ZMod 1931549951) ^ (94313 + 94313 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 94313 * (7 : ZMod 1931549951) ^ 94313) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 386432169 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 1931549951) ^ 377255 = 35392836 := by
        calc
          (7 : ZMod 1931549951) ^ 377255 = (7 : ZMod 1931549951) ^ (188627 + 188627 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 188627 * (7 : ZMod 1931549951) ^ 188627) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 35392836 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 1931549951) ^ 754511 = 1419603318 := by
        calc
          (7 : ZMod 1931549951) ^ 754511 = (7 : ZMod 1931549951) ^ (377255 + 377255 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 377255 * (7 : ZMod 1931549951) ^ 377255) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1419603318 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 1931549951) ^ 1509023 = 11054855 := by
        calc
          (7 : ZMod 1931549951) ^ 1509023 = (7 : ZMod 1931549951) ^ (754511 + 754511 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 754511 * (7 : ZMod 1931549951) ^ 754511) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 11054855 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 1931549951) ^ 3018046 = 653671255 := by
        calc
          (7 : ZMod 1931549951) ^ 3018046 = (7 : ZMod 1931549951) ^ (1509023 + 1509023) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 1509023 * (7 : ZMod 1931549951) ^ 1509023 := by rw [pow_add]
          _ = 653671255 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 1931549951) ^ 6036093 = 1481765983 := by
        calc
          (7 : ZMod 1931549951) ^ 6036093 = (7 : ZMod 1931549951) ^ (3018046 + 3018046 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 3018046 * (7 : ZMod 1931549951) ^ 3018046) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1481765983 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 1931549951) ^ 12072187 = 523470763 := by
        calc
          (7 : ZMod 1931549951) ^ 12072187 = (7 : ZMod 1931549951) ^ (6036093 + 6036093 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 6036093 * (7 : ZMod 1931549951) ^ 6036093) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 523470763 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 1931549951) ^ 24144374 = 1578095626 := by
        calc
          (7 : ZMod 1931549951) ^ 24144374 = (7 : ZMod 1931549951) ^ (12072187 + 12072187) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 12072187 * (7 : ZMod 1931549951) ^ 12072187 := by rw [pow_add]
          _ = 1578095626 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 1931549951) ^ 48288748 = 1611157319 := by
        calc
          (7 : ZMod 1931549951) ^ 48288748 = (7 : ZMod 1931549951) ^ (24144374 + 24144374) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 24144374 * (7 : ZMod 1931549951) ^ 24144374 := by rw [pow_add]
          _ = 1611157319 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 1931549951) ^ 96577497 = 1059807808 := by
        calc
          (7 : ZMod 1931549951) ^ 96577497 = (7 : ZMod 1931549951) ^ (48288748 + 48288748 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 48288748 * (7 : ZMod 1931549951) ^ 48288748) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1059807808 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 1931549951) ^ 193154995 = 249345831 := by
        calc
          (7 : ZMod 1931549951) ^ 193154995 = (7 : ZMod 1931549951) ^ (96577497 + 96577497 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 96577497 * (7 : ZMod 1931549951) ^ 96577497) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 249345831 := by rw [factor_1_26]; decide
      have factor_1_28 : (7 : ZMod 1931549951) ^ 386309990 = 1312958094 := by
        calc
          (7 : ZMod 1931549951) ^ 386309990 = (7 : ZMod 1931549951) ^ (193154995 + 193154995) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 193154995 * (7 : ZMod 1931549951) ^ 193154995 := by rw [pow_add]
          _ = 1312958094 := by rw [factor_1_27]; decide
      change (7 : ZMod 1931549951) ^ 386309990 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (7 : ZMod 1931549951) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 1931549951) ^ 2 = 49 := by
        calc
          (7 : ZMod 1931549951) ^ 2 = (7 : ZMod 1931549951) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 1 * (7 : ZMod 1931549951) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 1931549951) ^ 5 = 16807 := by
        calc
          (7 : ZMod 1931549951) ^ 5 = (7 : ZMod 1931549951) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 2 * (7 : ZMod 1931549951) ^ 2) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 1931549951) ^ 10 = 282475249 := by
        calc
          (7 : ZMod 1931549951) ^ 10 = (7 : ZMod 1931549951) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 5 * (7 : ZMod 1931549951) ^ 5 := by rw [pow_add]
          _ = 282475249 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 1931549951) ^ 20 = 1562950384 := by
        calc
          (7 : ZMod 1931549951) ^ 20 = (7 : ZMod 1931549951) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 10 * (7 : ZMod 1931549951) ^ 10 := by rw [pow_add]
          _ = 1562950384 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 1931549951) ^ 41 = 171206511 := by
        calc
          (7 : ZMod 1931549951) ^ 41 = (7 : ZMod 1931549951) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 20 * (7 : ZMod 1931549951) ^ 20) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 171206511 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 1931549951) ^ 83 = 1226897652 := by
        calc
          (7 : ZMod 1931549951) ^ 83 = (7 : ZMod 1931549951) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 41 * (7 : ZMod 1931549951) ^ 41) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1226897652 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 1931549951) ^ 167 = 22315826 := by
        calc
          (7 : ZMod 1931549951) ^ 167 = (7 : ZMod 1931549951) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 83 * (7 : ZMod 1931549951) ^ 83) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 22315826 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 1931549951) ^ 334 = 18595554 := by
        calc
          (7 : ZMod 1931549951) ^ 334 = (7 : ZMod 1931549951) ^ (167 + 167) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 167 * (7 : ZMod 1931549951) ^ 167 := by rw [pow_add]
          _ = 18595554 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 1931549951) ^ 669 = 16323791 := by
        calc
          (7 : ZMod 1931549951) ^ 669 = (7 : ZMod 1931549951) ^ (334 + 334 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 334 * (7 : ZMod 1931549951) ^ 334) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 16323791 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 1931549951) ^ 1339 = 48500185 := by
        calc
          (7 : ZMod 1931549951) ^ 1339 = (7 : ZMod 1931549951) ^ (669 + 669 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 669 * (7 : ZMod 1931549951) ^ 669) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 48500185 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 1931549951) ^ 2679 = 1405699630 := by
        calc
          (7 : ZMod 1931549951) ^ 2679 = (7 : ZMod 1931549951) ^ (1339 + 1339 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 1339 * (7 : ZMod 1931549951) ^ 1339) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1405699630 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 1931549951) ^ 5358 = 1541788945 := by
        calc
          (7 : ZMod 1931549951) ^ 5358 = (7 : ZMod 1931549951) ^ (2679 + 2679) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 2679 * (7 : ZMod 1931549951) ^ 2679 := by rw [pow_add]
          _ = 1541788945 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 1931549951) ^ 10717 = 1878883762 := by
        calc
          (7 : ZMod 1931549951) ^ 10717 = (7 : ZMod 1931549951) ^ (5358 + 5358 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 5358 * (7 : ZMod 1931549951) ^ 5358) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1878883762 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 1931549951) ^ 21434 = 487098260 := by
        calc
          (7 : ZMod 1931549951) ^ 21434 = (7 : ZMod 1931549951) ^ (10717 + 10717) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 10717 * (7 : ZMod 1931549951) ^ 10717 := by rw [pow_add]
          _ = 487098260 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 1931549951) ^ 42869 = 1391991238 := by
        calc
          (7 : ZMod 1931549951) ^ 42869 = (7 : ZMod 1931549951) ^ (21434 + 21434 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 21434 * (7 : ZMod 1931549951) ^ 21434) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1391991238 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 1931549951) ^ 85739 = 1342294898 := by
        calc
          (7 : ZMod 1931549951) ^ 85739 = (7 : ZMod 1931549951) ^ (42869 + 42869 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 42869 * (7 : ZMod 1931549951) ^ 42869) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1342294898 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 1931549951) ^ 171479 = 805992563 := by
        calc
          (7 : ZMod 1931549951) ^ 171479 = (7 : ZMod 1931549951) ^ (85739 + 85739 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 85739 * (7 : ZMod 1931549951) ^ 85739) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 805992563 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 1931549951) ^ 342959 = 1670934085 := by
        calc
          (7 : ZMod 1931549951) ^ 342959 = (7 : ZMod 1931549951) ^ (171479 + 171479 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 171479 * (7 : ZMod 1931549951) ^ 171479) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1670934085 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 1931549951) ^ 685919 = 464891916 := by
        calc
          (7 : ZMod 1931549951) ^ 685919 = (7 : ZMod 1931549951) ^ (342959 + 342959 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 342959 * (7 : ZMod 1931549951) ^ 342959) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 464891916 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 1931549951) ^ 1371839 = 656875731 := by
        calc
          (7 : ZMod 1931549951) ^ 1371839 = (7 : ZMod 1931549951) ^ (685919 + 685919 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 685919 * (7 : ZMod 1931549951) ^ 685919) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 656875731 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 1931549951) ^ 2743678 = 385112727 := by
        calc
          (7 : ZMod 1931549951) ^ 2743678 = (7 : ZMod 1931549951) ^ (1371839 + 1371839) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 1371839 * (7 : ZMod 1931549951) ^ 1371839 := by rw [pow_add]
          _ = 385112727 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 1931549951) ^ 5487357 = 290291059 := by
        calc
          (7 : ZMod 1931549951) ^ 5487357 = (7 : ZMod 1931549951) ^ (2743678 + 2743678 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 2743678 * (7 : ZMod 1931549951) ^ 2743678) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 290291059 := by rw [factor_2_21]; decide
      have factor_2_23 : (7 : ZMod 1931549951) ^ 10974715 = 584308980 := by
        calc
          (7 : ZMod 1931549951) ^ 10974715 = (7 : ZMod 1931549951) ^ (5487357 + 5487357 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 5487357 * (7 : ZMod 1931549951) ^ 5487357) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 584308980 := by rw [factor_2_22]; decide
      have factor_2_24 : (7 : ZMod 1931549951) ^ 21949431 = 391390618 := by
        calc
          (7 : ZMod 1931549951) ^ 21949431 = (7 : ZMod 1931549951) ^ (10974715 + 10974715 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 10974715 * (7 : ZMod 1931549951) ^ 10974715) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 391390618 := by rw [factor_2_23]; decide
      have factor_2_25 : (7 : ZMod 1931549951) ^ 43898862 = 1785894912 := by
        calc
          (7 : ZMod 1931549951) ^ 43898862 = (7 : ZMod 1931549951) ^ (21949431 + 21949431) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 21949431 * (7 : ZMod 1931549951) ^ 21949431 := by rw [pow_add]
          _ = 1785894912 := by rw [factor_2_24]; decide
      have factor_2_26 : (7 : ZMod 1931549951) ^ 87797725 = 927718681 := by
        calc
          (7 : ZMod 1931549951) ^ 87797725 = (7 : ZMod 1931549951) ^ (43898862 + 43898862 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 43898862 * (7 : ZMod 1931549951) ^ 43898862) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 927718681 := by rw [factor_2_25]; decide
      have factor_2_27 : (7 : ZMod 1931549951) ^ 175595450 = 86048565 := by
        calc
          (7 : ZMod 1931549951) ^ 175595450 = (7 : ZMod 1931549951) ^ (87797725 + 87797725) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 87797725 * (7 : ZMod 1931549951) ^ 87797725 := by rw [pow_add]
          _ = 86048565 := by rw [factor_2_26]; decide
      change (7 : ZMod 1931549951) ^ 175595450 ≠ 1
      rw [factor_2_27]
      decide
    ·
      have factor_3_0 : (7 : ZMod 1931549951) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 1931549951) ^ 2 = 49 := by
        calc
          (7 : ZMod 1931549951) ^ 2 = (7 : ZMod 1931549951) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 1 * (7 : ZMod 1931549951) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 1931549951) ^ 5 = 16807 := by
        calc
          (7 : ZMod 1931549951) ^ 5 = (7 : ZMod 1931549951) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 2 * (7 : ZMod 1931549951) ^ 2) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 1931549951) ^ 11 = 45776792 := by
        calc
          (7 : ZMod 1931549951) ^ 11 = (7 : ZMod 1931549951) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 5 * (7 : ZMod 1931549951) ^ 5) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 45776792 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 1931549951) ^ 22 = 1254120727 := by
        calc
          (7 : ZMod 1931549951) ^ 22 = (7 : ZMod 1931549951) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 11 * (7 : ZMod 1931549951) ^ 11 := by rw [pow_add]
          _ = 1254120727 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 1931549951) ^ 45 = 1578243299 := by
        calc
          (7 : ZMod 1931549951) ^ 45 = (7 : ZMod 1931549951) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 22 * (7 : ZMod 1931549951) ^ 22) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1578243299 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 1931549951) ^ 90 = 1467453132 := by
        calc
          (7 : ZMod 1931549951) ^ 90 = (7 : ZMod 1931549951) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 45 * (7 : ZMod 1931549951) ^ 45 := by rw [pow_add]
          _ = 1467453132 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 1931549951) ^ 180 = 1055976323 := by
        calc
          (7 : ZMod 1931549951) ^ 180 = (7 : ZMod 1931549951) ^ (90 + 90) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 90 * (7 : ZMod 1931549951) ^ 90 := by rw [pow_add]
          _ = 1055976323 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 1931549951) ^ 360 = 262706336 := by
        calc
          (7 : ZMod 1931549951) ^ 360 = (7 : ZMod 1931549951) ^ (180 + 180) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 180 * (7 : ZMod 1931549951) ^ 180 := by rw [pow_add]
          _ = 262706336 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 1931549951) ^ 721 = 702314493 := by
        calc
          (7 : ZMod 1931549951) ^ 721 = (7 : ZMod 1931549951) ^ (360 + 360 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 360 * (7 : ZMod 1931549951) ^ 360) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 702314493 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 1931549951) ^ 1443 = 248456386 := by
        calc
          (7 : ZMod 1931549951) ^ 1443 = (7 : ZMod 1931549951) ^ (721 + 721 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 721 * (7 : ZMod 1931549951) ^ 721) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 248456386 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 1931549951) ^ 2886 = 883776308 := by
        calc
          (7 : ZMod 1931549951) ^ 2886 = (7 : ZMod 1931549951) ^ (1443 + 1443) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 1443 * (7 : ZMod 1931549951) ^ 1443 := by rw [pow_add]
          _ = 883776308 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 1931549951) ^ 5772 = 560283465 := by
        calc
          (7 : ZMod 1931549951) ^ 5772 = (7 : ZMod 1931549951) ^ (2886 + 2886) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 2886 * (7 : ZMod 1931549951) ^ 2886 := by rw [pow_add]
          _ = 560283465 := by rw [factor_3_11]; decide
      have factor_3_13 : (7 : ZMod 1931549951) ^ 11545 = 1543769899 := by
        calc
          (7 : ZMod 1931549951) ^ 11545 = (7 : ZMod 1931549951) ^ (5772 + 5772 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 5772 * (7 : ZMod 1931549951) ^ 5772) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1543769899 := by rw [factor_3_12]; decide
      have factor_3_14 : (7 : ZMod 1931549951) ^ 23091 = 290750487 := by
        calc
          (7 : ZMod 1931549951) ^ 23091 = (7 : ZMod 1931549951) ^ (11545 + 11545 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 11545 * (7 : ZMod 1931549951) ^ 11545) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 290750487 := by rw [factor_3_13]; decide
      have factor_3_15 : (7 : ZMod 1931549951) ^ 46182 = 1392861761 := by
        calc
          (7 : ZMod 1931549951) ^ 46182 = (7 : ZMod 1931549951) ^ (23091 + 23091) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 23091 * (7 : ZMod 1931549951) ^ 23091 := by rw [pow_add]
          _ = 1392861761 := by rw [factor_3_14]; decide
      have factor_3_16 : (7 : ZMod 1931549951) ^ 92365 = 652781822 := by
        calc
          (7 : ZMod 1931549951) ^ 92365 = (7 : ZMod 1931549951) ^ (46182 + 46182 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 46182 * (7 : ZMod 1931549951) ^ 46182) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 652781822 := by rw [factor_3_15]; decide
      have factor_3_17 : (7 : ZMod 1931549951) ^ 184731 = 1727222981 := by
        calc
          (7 : ZMod 1931549951) ^ 184731 = (7 : ZMod 1931549951) ^ (92365 + 92365 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 92365 * (7 : ZMod 1931549951) ^ 92365) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1727222981 := by rw [factor_3_16]; decide
      have factor_3_18 : (7 : ZMod 1931549951) ^ 369462 = 1074891988 := by
        calc
          (7 : ZMod 1931549951) ^ 369462 = (7 : ZMod 1931549951) ^ (184731 + 184731) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 184731 * (7 : ZMod 1931549951) ^ 184731 := by rw [pow_add]
          _ = 1074891988 := by rw [factor_3_17]; decide
      have factor_3_19 : (7 : ZMod 1931549951) ^ 738925 = 381170231 := by
        calc
          (7 : ZMod 1931549951) ^ 738925 = (7 : ZMod 1931549951) ^ (369462 + 369462 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 369462 * (7 : ZMod 1931549951) ^ 369462) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 381170231 := by rw [factor_3_18]; decide
      have factor_3_20 : (7 : ZMod 1931549951) ^ 1477850 = 11312140 := by
        calc
          (7 : ZMod 1931549951) ^ 1477850 = (7 : ZMod 1931549951) ^ (738925 + 738925) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 738925 * (7 : ZMod 1931549951) ^ 738925 := by rw [pow_add]
          _ = 11312140 := by rw [factor_3_19]; decide
      change (7 : ZMod 1931549951) ^ 1477850 ≠ 1
      rw [factor_3_20]
      decide
    ·
      have factor_4_0 : (7 : ZMod 1931549951) ^ 1 = 7 := by norm_num
      have factor_4_1 : (7 : ZMod 1931549951) ^ 2 = 49 := by
        calc
          (7 : ZMod 1931549951) ^ 2 = (7 : ZMod 1931549951) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 1 * (7 : ZMod 1931549951) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_4_0]; decide
      have factor_4_2 : (7 : ZMod 1931549951) ^ 5 = 16807 := by
        calc
          (7 : ZMod 1931549951) ^ 5 = (7 : ZMod 1931549951) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 2 * (7 : ZMod 1931549951) ^ 2) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_4_1]; decide
      have factor_4_3 : (7 : ZMod 1931549951) ^ 10 = 282475249 := by
        calc
          (7 : ZMod 1931549951) ^ 10 = (7 : ZMod 1931549951) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 5 * (7 : ZMod 1931549951) ^ 5 := by rw [pow_add]
          _ = 282475249 := by rw [factor_4_2]; decide
      have factor_4_4 : (7 : ZMod 1931549951) ^ 21 = 1282902933 := by
        calc
          (7 : ZMod 1931549951) ^ 21 = (7 : ZMod 1931549951) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 10 * (7 : ZMod 1931549951) ^ 10) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1282902933 := by rw [factor_4_3]; decide
      have factor_4_5 : (7 : ZMod 1931549951) ^ 43 = 662919235 := by
        calc
          (7 : ZMod 1931549951) ^ 43 = (7 : ZMod 1931549951) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 21 * (7 : ZMod 1931549951) ^ 21) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 662919235 := by rw [factor_4_4]; decide
      have factor_4_6 : (7 : ZMod 1931549951) ^ 87 = 167587177 := by
        calc
          (7 : ZMod 1931549951) ^ 87 = (7 : ZMod 1931549951) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 43 * (7 : ZMod 1931549951) ^ 43) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 167587177 := by rw [factor_4_5]; decide
      have factor_4_7 : (7 : ZMod 1931549951) ^ 175 = 1206204124 := by
        calc
          (7 : ZMod 1931549951) ^ 175 = (7 : ZMod 1931549951) ^ (87 + 87 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 87 * (7 : ZMod 1931549951) ^ 87) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1206204124 := by rw [factor_4_6]; decide
      have factor_4_8 : (7 : ZMod 1931549951) ^ 351 = 632039614 := by
        calc
          (7 : ZMod 1931549951) ^ 351 = (7 : ZMod 1931549951) ^ (175 + 175 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 175 * (7 : ZMod 1931549951) ^ 175) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 632039614 := by rw [factor_4_7]; decide
      have factor_4_9 : (7 : ZMod 1931549951) ^ 702 = 741968451 := by
        calc
          (7 : ZMod 1931549951) ^ 702 = (7 : ZMod 1931549951) ^ (351 + 351) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 351 * (7 : ZMod 1931549951) ^ 351 := by rw [pow_add]
          _ = 741968451 := by rw [factor_4_8]; decide
      have factor_4_10 : (7 : ZMod 1931549951) ^ 1404 = 5284927 := by
        calc
          (7 : ZMod 1931549951) ^ 1404 = (7 : ZMod 1931549951) ^ (702 + 702) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 702 * (7 : ZMod 1931549951) ^ 702 := by rw [pow_add]
          _ = 5284927 := by rw [factor_4_9]; decide
      have factor_4_11 : (7 : ZMod 1931549951) ^ 2808 = 241103869 := by
        calc
          (7 : ZMod 1931549951) ^ 2808 = (7 : ZMod 1931549951) ^ (1404 + 1404) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 1404 * (7 : ZMod 1931549951) ^ 1404 := by rw [pow_add]
          _ = 241103869 := by rw [factor_4_10]; decide
      have factor_4_12 : (7 : ZMod 1931549951) ^ 5616 = 135001552 := by
        calc
          (7 : ZMod 1931549951) ^ 5616 = (7 : ZMod 1931549951) ^ (2808 + 2808) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 2808 * (7 : ZMod 1931549951) ^ 2808 := by rw [pow_add]
          _ = 135001552 := by rw [factor_4_11]; decide
      have factor_4_13 : (7 : ZMod 1931549951) ^ 11232 = 1336555260 := by
        calc
          (7 : ZMod 1931549951) ^ 11232 = (7 : ZMod 1931549951) ^ (5616 + 5616) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 5616 * (7 : ZMod 1931549951) ^ 5616 := by rw [pow_add]
          _ = 1336555260 := by rw [factor_4_12]; decide
      have factor_4_14 : (7 : ZMod 1931549951) ^ 22464 = 383112203 := by
        calc
          (7 : ZMod 1931549951) ^ 22464 = (7 : ZMod 1931549951) ^ (11232 + 11232) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 11232 * (7 : ZMod 1931549951) ^ 11232 := by rw [pow_add]
          _ = 383112203 := by rw [factor_4_13]; decide
      have factor_4_15 : (7 : ZMod 1931549951) ^ 44928 = 526583882 := by
        calc
          (7 : ZMod 1931549951) ^ 44928 = (7 : ZMod 1931549951) ^ (22464 + 22464) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 22464 * (7 : ZMod 1931549951) ^ 22464 := by rw [pow_add]
          _ = 526583882 := by rw [factor_4_14]; decide
      have factor_4_16 : (7 : ZMod 1931549951) ^ 89856 = 1165160736 := by
        calc
          (7 : ZMod 1931549951) ^ 89856 = (7 : ZMod 1931549951) ^ (44928 + 44928) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 44928 * (7 : ZMod 1931549951) ^ 44928 := by rw [pow_add]
          _ = 1165160736 := by rw [factor_4_15]; decide
      have factor_4_17 : (7 : ZMod 1931549951) ^ 179712 = 1837506647 := by
        calc
          (7 : ZMod 1931549951) ^ 179712 = (7 : ZMod 1931549951) ^ (89856 + 89856) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 89856 * (7 : ZMod 1931549951) ^ 89856 := by rw [pow_add]
          _ = 1837506647 := by rw [factor_4_16]; decide
      have factor_4_18 : (7 : ZMod 1931549951) ^ 359425 = 1335076550 := by
        calc
          (7 : ZMod 1931549951) ^ 359425 = (7 : ZMod 1931549951) ^ (179712 + 179712 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = ((7 : ZMod 1931549951) ^ 179712 * (7 : ZMod 1931549951) ^ 179712) * (7 : ZMod 1931549951) := by rw [pow_succ, pow_add]
          _ = 1335076550 := by rw [factor_4_17]; decide
      have factor_4_19 : (7 : ZMod 1931549951) ^ 718850 = 1850878138 := by
        calc
          (7 : ZMod 1931549951) ^ 718850 = (7 : ZMod 1931549951) ^ (359425 + 359425) :=
            congrArg (fun n : ℕ => (7 : ZMod 1931549951) ^ n) (by norm_num)
          _ = (7 : ZMod 1931549951) ^ 359425 * (7 : ZMod 1931549951) ^ 359425 := by rw [pow_add]
          _ = 1850878138 := by rw [factor_4_18]; decide
      change (7 : ZMod 1931549951) ^ 718850 ≠ 1
      rw [factor_4_19]
      decide

#print axioms prime_lucas_1931549951

end TotientTailPeriodKiller
end Erdos249257
