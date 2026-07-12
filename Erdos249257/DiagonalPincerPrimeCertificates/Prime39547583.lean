import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_39547583 : Nat.Prime 39547583 := by
  apply lucas_primality 39547583 (5 : ZMod 39547583)
  ·
      have fermat_0 : (5 : ZMod 39547583) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 39547583) ^ 2 = 25 := by
        calc
          (5 : ZMod 39547583) ^ 2 = (5 : ZMod 39547583) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 1 * (5 : ZMod 39547583) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 39547583) ^ 4 = 625 := by
        calc
          (5 : ZMod 39547583) ^ 4 = (5 : ZMod 39547583) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 2 * (5 : ZMod 39547583) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 39547583) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 39547583) ^ 9 = (5 : ZMod 39547583) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 4 * (5 : ZMod 39547583) ^ 4) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 39547583) ^ 18 = 16504611 := by
        calc
          (5 : ZMod 39547583) ^ 18 = (5 : ZMod 39547583) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 9 * (5 : ZMod 39547583) ^ 9 := by rw [pow_add]
          _ = 16504611 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 39547583) ^ 37 = 32755622 := by
        calc
          (5 : ZMod 39547583) ^ 37 = (5 : ZMod 39547583) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 18 * (5 : ZMod 39547583) ^ 18) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 32755622 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 39547583) ^ 75 = 25963624 := by
        calc
          (5 : ZMod 39547583) ^ 75 = (5 : ZMod 39547583) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 37 * (5 : ZMod 39547583) ^ 37) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 25963624 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 39547583) ^ 150 = 21473888 := by
        calc
          (5 : ZMod 39547583) ^ 150 = (5 : ZMod 39547583) ^ (75 + 75) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 75 * (5 : ZMod 39547583) ^ 75 := by rw [pow_add]
          _ = 21473888 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 39547583) ^ 301 = 14463265 := by
        calc
          (5 : ZMod 39547583) ^ 301 = (5 : ZMod 39547583) ^ (150 + 150 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 150 * (5 : ZMod 39547583) ^ 150) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 14463265 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 39547583) ^ 603 = 18880670 := by
        calc
          (5 : ZMod 39547583) ^ 603 = (5 : ZMod 39547583) ^ (301 + 301 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 301 * (5 : ZMod 39547583) ^ 301) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 18880670 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 39547583) ^ 1206 = 1151548 := by
        calc
          (5 : ZMod 39547583) ^ 1206 = (5 : ZMod 39547583) ^ (603 + 603) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 603 * (5 : ZMod 39547583) ^ 603 := by rw [pow_add]
          _ = 1151548 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 39547583) ^ 2413 = 3501238 := by
        calc
          (5 : ZMod 39547583) ^ 2413 = (5 : ZMod 39547583) ^ (1206 + 1206 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 1206 * (5 : ZMod 39547583) ^ 1206) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 3501238 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 39547583) ^ 4827 = 2032091 := by
        calc
          (5 : ZMod 39547583) ^ 4827 = (5 : ZMod 39547583) ^ (2413 + 2413 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 2413 * (5 : ZMod 39547583) ^ 2413) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 2032091 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 39547583) ^ 9655 = 6576348 := by
        calc
          (5 : ZMod 39547583) ^ 9655 = (5 : ZMod 39547583) ^ (4827 + 4827 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 4827 * (5 : ZMod 39547583) ^ 4827) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 6576348 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 39547583) ^ 19310 = 25842713 := by
        calc
          (5 : ZMod 39547583) ^ 19310 = (5 : ZMod 39547583) ^ (9655 + 9655) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 9655 * (5 : ZMod 39547583) ^ 9655 := by rw [pow_add]
          _ = 25842713 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 39547583) ^ 38620 = 7132251 := by
        calc
          (5 : ZMod 39547583) ^ 38620 = (5 : ZMod 39547583) ^ (19310 + 19310) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 19310 * (5 : ZMod 39547583) ^ 19310 := by rw [pow_add]
          _ = 7132251 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 39547583) ^ 77241 = 1399044 := by
        calc
          (5 : ZMod 39547583) ^ 77241 = (5 : ZMod 39547583) ^ (38620 + 38620 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 38620 * (5 : ZMod 39547583) ^ 38620) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 1399044 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 39547583) ^ 154482 = 35136100 := by
        calc
          (5 : ZMod 39547583) ^ 154482 = (5 : ZMod 39547583) ^ (77241 + 77241) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 77241 * (5 : ZMod 39547583) ^ 77241 := by rw [pow_add]
          _ = 35136100 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 39547583) ^ 308965 = 32466937 := by
        calc
          (5 : ZMod 39547583) ^ 308965 = (5 : ZMod 39547583) ^ (154482 + 154482 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 154482 * (5 : ZMod 39547583) ^ 154482) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 32466937 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 39547583) ^ 617930 = 9023475 := by
        calc
          (5 : ZMod 39547583) ^ 617930 = (5 : ZMod 39547583) ^ (308965 + 308965) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 308965 * (5 : ZMod 39547583) ^ 308965 := by rw [pow_add]
          _ = 9023475 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 39547583) ^ 1235861 = 30749565 := by
        calc
          (5 : ZMod 39547583) ^ 1235861 = (5 : ZMod 39547583) ^ (617930 + 617930 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 617930 * (5 : ZMod 39547583) ^ 617930) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 30749565 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 39547583) ^ 2471723 = 24343979 := by
        calc
          (5 : ZMod 39547583) ^ 2471723 = (5 : ZMod 39547583) ^ (1235861 + 1235861 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 1235861 * (5 : ZMod 39547583) ^ 1235861) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 24343979 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 39547583) ^ 4943447 = 13670075 := by
        calc
          (5 : ZMod 39547583) ^ 4943447 = (5 : ZMod 39547583) ^ (2471723 + 2471723 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 2471723 * (5 : ZMod 39547583) ^ 2471723) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 13670075 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 39547583) ^ 9886895 = 36835238 := by
        calc
          (5 : ZMod 39547583) ^ 9886895 = (5 : ZMod 39547583) ^ (4943447 + 4943447 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 4943447 * (5 : ZMod 39547583) ^ 4943447) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 36835238 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 39547583) ^ 19773791 = 39547582 := by
        calc
          (5 : ZMod 39547583) ^ 19773791 = (5 : ZMod 39547583) ^ (9886895 + 9886895 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 9886895 * (5 : ZMod 39547583) ^ 9886895) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 39547582 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 39547583) ^ 39547582 = 1 := by
        calc
          (5 : ZMod 39547583) ^ 39547582 = (5 : ZMod 39547583) ^ (19773791 + 19773791) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 19773791 * (5 : ZMod 39547583) ^ 19773791 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (59, 1), (335149, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (59, 1), (335149, 1)] : List FactorBlock).map factorBlockValue).prod = 39547583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 39547583) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 39547583) ^ 2 = 25 := by
        calc
          (5 : ZMod 39547583) ^ 2 = (5 : ZMod 39547583) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 1 * (5 : ZMod 39547583) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 39547583) ^ 4 = 625 := by
        calc
          (5 : ZMod 39547583) ^ 4 = (5 : ZMod 39547583) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 2 * (5 : ZMod 39547583) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 39547583) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 39547583) ^ 9 = (5 : ZMod 39547583) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 4 * (5 : ZMod 39547583) ^ 4) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 39547583) ^ 18 = 16504611 := by
        calc
          (5 : ZMod 39547583) ^ 18 = (5 : ZMod 39547583) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 9 * (5 : ZMod 39547583) ^ 9 := by rw [pow_add]
          _ = 16504611 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 39547583) ^ 37 = 32755622 := by
        calc
          (5 : ZMod 39547583) ^ 37 = (5 : ZMod 39547583) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 18 * (5 : ZMod 39547583) ^ 18) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 32755622 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 39547583) ^ 75 = 25963624 := by
        calc
          (5 : ZMod 39547583) ^ 75 = (5 : ZMod 39547583) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 37 * (5 : ZMod 39547583) ^ 37) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 25963624 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 39547583) ^ 150 = 21473888 := by
        calc
          (5 : ZMod 39547583) ^ 150 = (5 : ZMod 39547583) ^ (75 + 75) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 75 * (5 : ZMod 39547583) ^ 75 := by rw [pow_add]
          _ = 21473888 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 39547583) ^ 301 = 14463265 := by
        calc
          (5 : ZMod 39547583) ^ 301 = (5 : ZMod 39547583) ^ (150 + 150 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 150 * (5 : ZMod 39547583) ^ 150) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 14463265 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 39547583) ^ 603 = 18880670 := by
        calc
          (5 : ZMod 39547583) ^ 603 = (5 : ZMod 39547583) ^ (301 + 301 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 301 * (5 : ZMod 39547583) ^ 301) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 18880670 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 39547583) ^ 1206 = 1151548 := by
        calc
          (5 : ZMod 39547583) ^ 1206 = (5 : ZMod 39547583) ^ (603 + 603) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 603 * (5 : ZMod 39547583) ^ 603 := by rw [pow_add]
          _ = 1151548 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 39547583) ^ 2413 = 3501238 := by
        calc
          (5 : ZMod 39547583) ^ 2413 = (5 : ZMod 39547583) ^ (1206 + 1206 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 1206 * (5 : ZMod 39547583) ^ 1206) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 3501238 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 39547583) ^ 4827 = 2032091 := by
        calc
          (5 : ZMod 39547583) ^ 4827 = (5 : ZMod 39547583) ^ (2413 + 2413 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 2413 * (5 : ZMod 39547583) ^ 2413) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 2032091 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 39547583) ^ 9655 = 6576348 := by
        calc
          (5 : ZMod 39547583) ^ 9655 = (5 : ZMod 39547583) ^ (4827 + 4827 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 4827 * (5 : ZMod 39547583) ^ 4827) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 6576348 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 39547583) ^ 19310 = 25842713 := by
        calc
          (5 : ZMod 39547583) ^ 19310 = (5 : ZMod 39547583) ^ (9655 + 9655) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 9655 * (5 : ZMod 39547583) ^ 9655 := by rw [pow_add]
          _ = 25842713 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 39547583) ^ 38620 = 7132251 := by
        calc
          (5 : ZMod 39547583) ^ 38620 = (5 : ZMod 39547583) ^ (19310 + 19310) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 19310 * (5 : ZMod 39547583) ^ 19310 := by rw [pow_add]
          _ = 7132251 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 39547583) ^ 77241 = 1399044 := by
        calc
          (5 : ZMod 39547583) ^ 77241 = (5 : ZMod 39547583) ^ (38620 + 38620 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 38620 * (5 : ZMod 39547583) ^ 38620) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 1399044 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 39547583) ^ 154482 = 35136100 := by
        calc
          (5 : ZMod 39547583) ^ 154482 = (5 : ZMod 39547583) ^ (77241 + 77241) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 77241 * (5 : ZMod 39547583) ^ 77241 := by rw [pow_add]
          _ = 35136100 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 39547583) ^ 308965 = 32466937 := by
        calc
          (5 : ZMod 39547583) ^ 308965 = (5 : ZMod 39547583) ^ (154482 + 154482 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 154482 * (5 : ZMod 39547583) ^ 154482) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 32466937 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 39547583) ^ 617930 = 9023475 := by
        calc
          (5 : ZMod 39547583) ^ 617930 = (5 : ZMod 39547583) ^ (308965 + 308965) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 308965 * (5 : ZMod 39547583) ^ 308965 := by rw [pow_add]
          _ = 9023475 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 39547583) ^ 1235861 = 30749565 := by
        calc
          (5 : ZMod 39547583) ^ 1235861 = (5 : ZMod 39547583) ^ (617930 + 617930 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 617930 * (5 : ZMod 39547583) ^ 617930) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 30749565 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 39547583) ^ 2471723 = 24343979 := by
        calc
          (5 : ZMod 39547583) ^ 2471723 = (5 : ZMod 39547583) ^ (1235861 + 1235861 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 1235861 * (5 : ZMod 39547583) ^ 1235861) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 24343979 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 39547583) ^ 4943447 = 13670075 := by
        calc
          (5 : ZMod 39547583) ^ 4943447 = (5 : ZMod 39547583) ^ (2471723 + 2471723 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 2471723 * (5 : ZMod 39547583) ^ 2471723) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 13670075 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 39547583) ^ 9886895 = 36835238 := by
        calc
          (5 : ZMod 39547583) ^ 9886895 = (5 : ZMod 39547583) ^ (4943447 + 4943447 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 4943447 * (5 : ZMod 39547583) ^ 4943447) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 36835238 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 39547583) ^ 19773791 = 39547582 := by
        calc
          (5 : ZMod 39547583) ^ 19773791 = (5 : ZMod 39547583) ^ (9886895 + 9886895 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 9886895 * (5 : ZMod 39547583) ^ 9886895) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 39547582 := by rw [factor_0_23]; decide
      change (5 : ZMod 39547583) ^ 19773791 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (5 : ZMod 39547583) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 39547583) ^ 2 = 25 := by
        calc
          (5 : ZMod 39547583) ^ 2 = (5 : ZMod 39547583) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 1 * (5 : ZMod 39547583) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 39547583) ^ 5 = 3125 := by
        calc
          (5 : ZMod 39547583) ^ 5 = (5 : ZMod 39547583) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 2 * (5 : ZMod 39547583) ^ 2) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 39547583) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 39547583) ^ 10 = (5 : ZMod 39547583) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 5 * (5 : ZMod 39547583) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 39547583) ^ 20 = 17139445 := by
        calc
          (5 : ZMod 39547583) ^ 20 = (5 : ZMod 39547583) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 10 * (5 : ZMod 39547583) ^ 10 := by rw [pow_add]
          _ = 17139445 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 39547583) ^ 40 = 21051701 := by
        calc
          (5 : ZMod 39547583) ^ 40 = (5 : ZMod 39547583) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 20 * (5 : ZMod 39547583) ^ 20 := by rw [pow_add]
          _ = 21051701 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 39547583) ^ 81 = 2518586 := by
        calc
          (5 : ZMod 39547583) ^ 81 = (5 : ZMod 39547583) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 40 * (5 : ZMod 39547583) ^ 40) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 2518586 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 39547583) ^ 163 = 6582640 := by
        calc
          (5 : ZMod 39547583) ^ 163 = (5 : ZMod 39547583) ^ (81 + 81 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 81 * (5 : ZMod 39547583) ^ 81) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 6582640 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 39547583) ^ 327 = 8234452 := by
        calc
          (5 : ZMod 39547583) ^ 327 = (5 : ZMod 39547583) ^ (163 + 163 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 163 * (5 : ZMod 39547583) ^ 163) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 8234452 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 39547583) ^ 654 = 9950403 := by
        calc
          (5 : ZMod 39547583) ^ 654 = (5 : ZMod 39547583) ^ (327 + 327) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 327 * (5 : ZMod 39547583) ^ 327 := by rw [pow_add]
          _ = 9950403 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 39547583) ^ 1309 = 28719094 := by
        calc
          (5 : ZMod 39547583) ^ 1309 = (5 : ZMod 39547583) ^ (654 + 654 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 654 * (5 : ZMod 39547583) ^ 654) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 28719094 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 39547583) ^ 2618 = 2830684 := by
        calc
          (5 : ZMod 39547583) ^ 2618 = (5 : ZMod 39547583) ^ (1309 + 1309) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 1309 * (5 : ZMod 39547583) ^ 1309 := by rw [pow_add]
          _ = 2830684 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 39547583) ^ 5236 = 36116226 := by
        calc
          (5 : ZMod 39547583) ^ 5236 = (5 : ZMod 39547583) ^ (2618 + 2618) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 2618 * (5 : ZMod 39547583) ^ 2618 := by rw [pow_add]
          _ = 36116226 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 39547583) ^ 10473 = 8134866 := by
        calc
          (5 : ZMod 39547583) ^ 10473 = (5 : ZMod 39547583) ^ (5236 + 5236 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 5236 * (5 : ZMod 39547583) ^ 5236) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 8134866 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 39547583) ^ 20946 = 6419315 := by
        calc
          (5 : ZMod 39547583) ^ 20946 = (5 : ZMod 39547583) ^ (10473 + 10473) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 10473 * (5 : ZMod 39547583) ^ 10473 := by rw [pow_add]
          _ = 6419315 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 39547583) ^ 41893 = 21816417 := by
        calc
          (5 : ZMod 39547583) ^ 41893 = (5 : ZMod 39547583) ^ (20946 + 20946 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 20946 * (5 : ZMod 39547583) ^ 20946) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 21816417 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 39547583) ^ 83787 = 17235149 := by
        calc
          (5 : ZMod 39547583) ^ 83787 = (5 : ZMod 39547583) ^ (41893 + 41893 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 41893 * (5 : ZMod 39547583) ^ 41893) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 17235149 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 39547583) ^ 167574 = 1956439 := by
        calc
          (5 : ZMod 39547583) ^ 167574 = (5 : ZMod 39547583) ^ (83787 + 83787) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 83787 * (5 : ZMod 39547583) ^ 83787 := by rw [pow_add]
          _ = 1956439 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 39547583) ^ 335149 = 5962415 := by
        calc
          (5 : ZMod 39547583) ^ 335149 = (5 : ZMod 39547583) ^ (167574 + 167574 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 167574 * (5 : ZMod 39547583) ^ 167574) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 5962415 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 39547583) ^ 670298 = 2488784 := by
        calc
          (5 : ZMod 39547583) ^ 670298 = (5 : ZMod 39547583) ^ (335149 + 335149) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 335149 * (5 : ZMod 39547583) ^ 335149 := by rw [pow_add]
          _ = 2488784 := by rw [factor_1_18]; decide
      change (5 : ZMod 39547583) ^ 670298 ≠ 1
      rw [factor_1_19]
      decide
    ·
      have factor_2_0 : (5 : ZMod 39547583) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 39547583) ^ 3 = 125 := by
        calc
          (5 : ZMod 39547583) ^ 3 = (5 : ZMod 39547583) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 1 * (5 : ZMod 39547583) ^ 1) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 39547583) ^ 7 = 78125 := by
        calc
          (5 : ZMod 39547583) ^ 7 = (5 : ZMod 39547583) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 3 * (5 : ZMod 39547583) ^ 3) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 39547583) ^ 14 = 13187843 := by
        calc
          (5 : ZMod 39547583) ^ 14 = (5 : ZMod 39547583) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 7 * (5 : ZMod 39547583) ^ 7 := by rw [pow_add]
          _ = 13187843 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 39547583) ^ 29 = 31409445 := by
        calc
          (5 : ZMod 39547583) ^ 29 = (5 : ZMod 39547583) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 14 * (5 : ZMod 39547583) ^ 14) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 31409445 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 39547583) ^ 59 = 24113259 := by
        calc
          (5 : ZMod 39547583) ^ 59 = (5 : ZMod 39547583) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = ((5 : ZMod 39547583) ^ 29 * (5 : ZMod 39547583) ^ 29) * (5 : ZMod 39547583) := by rw [pow_succ, pow_add]
          _ = 24113259 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 39547583) ^ 118 = 10949172 := by
        calc
          (5 : ZMod 39547583) ^ 118 = (5 : ZMod 39547583) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (5 : ZMod 39547583) ^ n) (by norm_num)
          _ = (5 : ZMod 39547583) ^ 59 * (5 : ZMod 39547583) ^ 59 := by rw [pow_add]
          _ = 10949172 := by rw [factor_2_5]; decide
      change (5 : ZMod 39547583) ^ 118 ≠ 1
      rw [factor_2_6]
      decide

#print axioms prime_lucas_39547583

end TotientTailPeriodKiller
end Erdos249257
