import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_192059807 : Nat.Prime 192059807 := by
  apply lucas_primality 192059807 (5 : ZMod 192059807)
  ·
      have fermat_0 : (5 : ZMod 192059807) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 192059807) ^ 2 = 25 := by
        calc
          (5 : ZMod 192059807) ^ 2 = (5 : ZMod 192059807) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 1 * (5 : ZMod 192059807) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 192059807) ^ 5 = 3125 := by
        calc
          (5 : ZMod 192059807) ^ 5 = (5 : ZMod 192059807) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 2 * (5 : ZMod 192059807) ^ 2) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 192059807) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 192059807) ^ 11 = (5 : ZMod 192059807) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 5 * (5 : ZMod 192059807) ^ 5) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 192059807) ^ 22 = 96852656 := by
        calc
          (5 : ZMod 192059807) ^ 22 = (5 : ZMod 192059807) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 11 * (5 : ZMod 192059807) ^ 11 := by rw [pow_add]
          _ = 96852656 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 192059807) ^ 45 = 178477279 := by
        calc
          (5 : ZMod 192059807) ^ 45 = (5 : ZMod 192059807) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 22 * (5 : ZMod 192059807) ^ 22) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 178477279 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 192059807) ^ 91 = 109174706 := by
        calc
          (5 : ZMod 192059807) ^ 91 = (5 : ZMod 192059807) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 45 * (5 : ZMod 192059807) ^ 45) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 109174706 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 192059807) ^ 183 = 26193373 := by
        calc
          (5 : ZMod 192059807) ^ 183 = (5 : ZMod 192059807) ^ (91 + 91 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 91 * (5 : ZMod 192059807) ^ 91) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 26193373 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 192059807) ^ 366 = 37348520 := by
        calc
          (5 : ZMod 192059807) ^ 366 = (5 : ZMod 192059807) ^ (183 + 183) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 183 * (5 : ZMod 192059807) ^ 183 := by rw [pow_add]
          _ = 37348520 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 192059807) ^ 732 = 5690872 := by
        calc
          (5 : ZMod 192059807) ^ 732 = (5 : ZMod 192059807) ^ (366 + 366) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 366 * (5 : ZMod 192059807) ^ 366 := by rw [pow_add]
          _ = 5690872 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 192059807) ^ 1465 = 79944659 := by
        calc
          (5 : ZMod 192059807) ^ 1465 = (5 : ZMod 192059807) ^ (732 + 732 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 732 * (5 : ZMod 192059807) ^ 732) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 79944659 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 192059807) ^ 2930 = 41101419 := by
        calc
          (5 : ZMod 192059807) ^ 2930 = (5 : ZMod 192059807) ^ (1465 + 1465) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 1465 * (5 : ZMod 192059807) ^ 1465 := by rw [pow_add]
          _ = 41101419 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 192059807) ^ 5861 = 12129931 := by
        calc
          (5 : ZMod 192059807) ^ 5861 = (5 : ZMod 192059807) ^ (2930 + 2930 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 2930 * (5 : ZMod 192059807) ^ 2930) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 12129931 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 192059807) ^ 11722 = 128520131 := by
        calc
          (5 : ZMod 192059807) ^ 11722 = (5 : ZMod 192059807) ^ (5861 + 5861) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 5861 * (5 : ZMod 192059807) ^ 5861 := by rw [pow_add]
          _ = 128520131 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 192059807) ^ 23444 = 70879134 := by
        calc
          (5 : ZMod 192059807) ^ 23444 = (5 : ZMod 192059807) ^ (11722 + 11722) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 11722 * (5 : ZMod 192059807) ^ 11722 := by rw [pow_add]
          _ = 70879134 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 192059807) ^ 46889 = 133434477 := by
        calc
          (5 : ZMod 192059807) ^ 46889 = (5 : ZMod 192059807) ^ (23444 + 23444 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 23444 * (5 : ZMod 192059807) ^ 23444) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 133434477 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 192059807) ^ 93779 = 95055228 := by
        calc
          (5 : ZMod 192059807) ^ 93779 = (5 : ZMod 192059807) ^ (46889 + 46889 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 46889 * (5 : ZMod 192059807) ^ 46889) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 95055228 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 192059807) ^ 187558 = 112539830 := by
        calc
          (5 : ZMod 192059807) ^ 187558 = (5 : ZMod 192059807) ^ (93779 + 93779) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 93779 * (5 : ZMod 192059807) ^ 93779 := by rw [pow_add]
          _ = 112539830 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 192059807) ^ 375116 = 104982323 := by
        calc
          (5 : ZMod 192059807) ^ 375116 = (5 : ZMod 192059807) ^ (187558 + 187558) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 187558 * (5 : ZMod 192059807) ^ 187558 := by rw [pow_add]
          _ = 104982323 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 192059807) ^ 750233 = 176425493 := by
        calc
          (5 : ZMod 192059807) ^ 750233 = (5 : ZMod 192059807) ^ (375116 + 375116 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 375116 * (5 : ZMod 192059807) ^ 375116) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 176425493 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 192059807) ^ 1500467 = 117714584 := by
        calc
          (5 : ZMod 192059807) ^ 1500467 = (5 : ZMod 192059807) ^ (750233 + 750233 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 750233 * (5 : ZMod 192059807) ^ 750233) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 117714584 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 192059807) ^ 3000934 = 13249336 := by
        calc
          (5 : ZMod 192059807) ^ 3000934 = (5 : ZMod 192059807) ^ (1500467 + 1500467) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 1500467 * (5 : ZMod 192059807) ^ 1500467 := by rw [pow_add]
          _ = 13249336 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 192059807) ^ 6001868 = 128185019 := by
        calc
          (5 : ZMod 192059807) ^ 6001868 = (5 : ZMod 192059807) ^ (3000934 + 3000934) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 3000934 * (5 : ZMod 192059807) ^ 3000934 := by rw [pow_add]
          _ = 128185019 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 192059807) ^ 12003737 = 133131415 := by
        calc
          (5 : ZMod 192059807) ^ 12003737 = (5 : ZMod 192059807) ^ (6001868 + 6001868 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 6001868 * (5 : ZMod 192059807) ^ 6001868) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 133131415 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 192059807) ^ 24007475 = 140161337 := by
        calc
          (5 : ZMod 192059807) ^ 24007475 = (5 : ZMod 192059807) ^ (12003737 + 12003737 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 12003737 * (5 : ZMod 192059807) ^ 12003737) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 140161337 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 192059807) ^ 48014951 = 187986695 := by
        calc
          (5 : ZMod 192059807) ^ 48014951 = (5 : ZMod 192059807) ^ (24007475 + 24007475 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 24007475 * (5 : ZMod 192059807) ^ 24007475) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 187986695 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 192059807) ^ 96029903 = 192059806 := by
        calc
          (5 : ZMod 192059807) ^ 96029903 = (5 : ZMod 192059807) ^ (48014951 + 48014951 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 48014951 * (5 : ZMod 192059807) ^ 48014951) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 192059806 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 192059807) ^ 192059806 = 1 := by
        calc
          (5 : ZMod 192059807) ^ 192059806 = (5 : ZMod 192059807) ^ (96029903 + 96029903) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 96029903 * (5 : ZMod 192059807) ^ 96029903 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (97, 1), (989999, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (97, 1), (989999, 1)] : List FactorBlock).map factorBlockValue).prod = 192059807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 192059807) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 192059807) ^ 2 = 25 := by
        calc
          (5 : ZMod 192059807) ^ 2 = (5 : ZMod 192059807) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 1 * (5 : ZMod 192059807) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 192059807) ^ 5 = 3125 := by
        calc
          (5 : ZMod 192059807) ^ 5 = (5 : ZMod 192059807) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 2 * (5 : ZMod 192059807) ^ 2) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 192059807) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 192059807) ^ 11 = (5 : ZMod 192059807) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 5 * (5 : ZMod 192059807) ^ 5) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 192059807) ^ 22 = 96852656 := by
        calc
          (5 : ZMod 192059807) ^ 22 = (5 : ZMod 192059807) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 11 * (5 : ZMod 192059807) ^ 11 := by rw [pow_add]
          _ = 96852656 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 192059807) ^ 45 = 178477279 := by
        calc
          (5 : ZMod 192059807) ^ 45 = (5 : ZMod 192059807) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 22 * (5 : ZMod 192059807) ^ 22) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 178477279 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 192059807) ^ 91 = 109174706 := by
        calc
          (5 : ZMod 192059807) ^ 91 = (5 : ZMod 192059807) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 45 * (5 : ZMod 192059807) ^ 45) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 109174706 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 192059807) ^ 183 = 26193373 := by
        calc
          (5 : ZMod 192059807) ^ 183 = (5 : ZMod 192059807) ^ (91 + 91 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 91 * (5 : ZMod 192059807) ^ 91) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 26193373 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 192059807) ^ 366 = 37348520 := by
        calc
          (5 : ZMod 192059807) ^ 366 = (5 : ZMod 192059807) ^ (183 + 183) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 183 * (5 : ZMod 192059807) ^ 183 := by rw [pow_add]
          _ = 37348520 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 192059807) ^ 732 = 5690872 := by
        calc
          (5 : ZMod 192059807) ^ 732 = (5 : ZMod 192059807) ^ (366 + 366) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 366 * (5 : ZMod 192059807) ^ 366 := by rw [pow_add]
          _ = 5690872 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 192059807) ^ 1465 = 79944659 := by
        calc
          (5 : ZMod 192059807) ^ 1465 = (5 : ZMod 192059807) ^ (732 + 732 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 732 * (5 : ZMod 192059807) ^ 732) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 79944659 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 192059807) ^ 2930 = 41101419 := by
        calc
          (5 : ZMod 192059807) ^ 2930 = (5 : ZMod 192059807) ^ (1465 + 1465) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 1465 * (5 : ZMod 192059807) ^ 1465 := by rw [pow_add]
          _ = 41101419 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 192059807) ^ 5861 = 12129931 := by
        calc
          (5 : ZMod 192059807) ^ 5861 = (5 : ZMod 192059807) ^ (2930 + 2930 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 2930 * (5 : ZMod 192059807) ^ 2930) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 12129931 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 192059807) ^ 11722 = 128520131 := by
        calc
          (5 : ZMod 192059807) ^ 11722 = (5 : ZMod 192059807) ^ (5861 + 5861) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 5861 * (5 : ZMod 192059807) ^ 5861 := by rw [pow_add]
          _ = 128520131 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 192059807) ^ 23444 = 70879134 := by
        calc
          (5 : ZMod 192059807) ^ 23444 = (5 : ZMod 192059807) ^ (11722 + 11722) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 11722 * (5 : ZMod 192059807) ^ 11722 := by rw [pow_add]
          _ = 70879134 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 192059807) ^ 46889 = 133434477 := by
        calc
          (5 : ZMod 192059807) ^ 46889 = (5 : ZMod 192059807) ^ (23444 + 23444 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 23444 * (5 : ZMod 192059807) ^ 23444) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 133434477 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 192059807) ^ 93779 = 95055228 := by
        calc
          (5 : ZMod 192059807) ^ 93779 = (5 : ZMod 192059807) ^ (46889 + 46889 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 46889 * (5 : ZMod 192059807) ^ 46889) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 95055228 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 192059807) ^ 187558 = 112539830 := by
        calc
          (5 : ZMod 192059807) ^ 187558 = (5 : ZMod 192059807) ^ (93779 + 93779) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 93779 * (5 : ZMod 192059807) ^ 93779 := by rw [pow_add]
          _ = 112539830 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 192059807) ^ 375116 = 104982323 := by
        calc
          (5 : ZMod 192059807) ^ 375116 = (5 : ZMod 192059807) ^ (187558 + 187558) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 187558 * (5 : ZMod 192059807) ^ 187558 := by rw [pow_add]
          _ = 104982323 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 192059807) ^ 750233 = 176425493 := by
        calc
          (5 : ZMod 192059807) ^ 750233 = (5 : ZMod 192059807) ^ (375116 + 375116 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 375116 * (5 : ZMod 192059807) ^ 375116) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 176425493 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 192059807) ^ 1500467 = 117714584 := by
        calc
          (5 : ZMod 192059807) ^ 1500467 = (5 : ZMod 192059807) ^ (750233 + 750233 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 750233 * (5 : ZMod 192059807) ^ 750233) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 117714584 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 192059807) ^ 3000934 = 13249336 := by
        calc
          (5 : ZMod 192059807) ^ 3000934 = (5 : ZMod 192059807) ^ (1500467 + 1500467) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 1500467 * (5 : ZMod 192059807) ^ 1500467 := by rw [pow_add]
          _ = 13249336 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 192059807) ^ 6001868 = 128185019 := by
        calc
          (5 : ZMod 192059807) ^ 6001868 = (5 : ZMod 192059807) ^ (3000934 + 3000934) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 3000934 * (5 : ZMod 192059807) ^ 3000934 := by rw [pow_add]
          _ = 128185019 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 192059807) ^ 12003737 = 133131415 := by
        calc
          (5 : ZMod 192059807) ^ 12003737 = (5 : ZMod 192059807) ^ (6001868 + 6001868 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 6001868 * (5 : ZMod 192059807) ^ 6001868) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 133131415 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 192059807) ^ 24007475 = 140161337 := by
        calc
          (5 : ZMod 192059807) ^ 24007475 = (5 : ZMod 192059807) ^ (12003737 + 12003737 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 12003737 * (5 : ZMod 192059807) ^ 12003737) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 140161337 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 192059807) ^ 48014951 = 187986695 := by
        calc
          (5 : ZMod 192059807) ^ 48014951 = (5 : ZMod 192059807) ^ (24007475 + 24007475 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 24007475 * (5 : ZMod 192059807) ^ 24007475) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 187986695 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 192059807) ^ 96029903 = 192059806 := by
        calc
          (5 : ZMod 192059807) ^ 96029903 = (5 : ZMod 192059807) ^ (48014951 + 48014951 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 48014951 * (5 : ZMod 192059807) ^ 48014951) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 192059806 := by rw [factor_0_25]; decide
      change (5 : ZMod 192059807) ^ 96029903 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (5 : ZMod 192059807) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 192059807) ^ 3 = 125 := by
        calc
          (5 : ZMod 192059807) ^ 3 = (5 : ZMod 192059807) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 1 * (5 : ZMod 192059807) ^ 1) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 192059807) ^ 7 = 78125 := by
        calc
          (5 : ZMod 192059807) ^ 7 = (5 : ZMod 192059807) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 3 * (5 : ZMod 192059807) ^ 3) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 192059807) ^ 15 = 172128619 := by
        calc
          (5 : ZMod 192059807) ^ 15 = (5 : ZMod 192059807) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 7 * (5 : ZMod 192059807) ^ 7) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 172128619 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 192059807) ^ 30 = 167668105 := by
        calc
          (5 : ZMod 192059807) ^ 30 = (5 : ZMod 192059807) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 15 * (5 : ZMod 192059807) ^ 15 := by rw [pow_add]
          _ = 167668105 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 192059807) ^ 60 = 130784291 := by
        calc
          (5 : ZMod 192059807) ^ 60 = (5 : ZMod 192059807) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 30 * (5 : ZMod 192059807) ^ 30 := by rw [pow_add]
          _ = 130784291 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 192059807) ^ 120 = 107275389 := by
        calc
          (5 : ZMod 192059807) ^ 120 = (5 : ZMod 192059807) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 60 * (5 : ZMod 192059807) ^ 60 := by rw [pow_add]
          _ = 107275389 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 192059807) ^ 241 = 94388507 := by
        calc
          (5 : ZMod 192059807) ^ 241 = (5 : ZMod 192059807) ^ (120 + 120 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 120 * (5 : ZMod 192059807) ^ 120) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 94388507 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 192059807) ^ 483 = 77562840 := by
        calc
          (5 : ZMod 192059807) ^ 483 = (5 : ZMod 192059807) ^ (241 + 241 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 241 * (5 : ZMod 192059807) ^ 241) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 77562840 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 192059807) ^ 966 = 141609785 := by
        calc
          (5 : ZMod 192059807) ^ 966 = (5 : ZMod 192059807) ^ (483 + 483) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 483 * (5 : ZMod 192059807) ^ 483 := by rw [pow_add]
          _ = 141609785 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 192059807) ^ 1933 = 7343889 := by
        calc
          (5 : ZMod 192059807) ^ 1933 = (5 : ZMod 192059807) ^ (966 + 966 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 966 * (5 : ZMod 192059807) ^ 966) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 7343889 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 192059807) ^ 3867 = 35605185 := by
        calc
          (5 : ZMod 192059807) ^ 3867 = (5 : ZMod 192059807) ^ (1933 + 1933 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 1933 * (5 : ZMod 192059807) ^ 1933) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 35605185 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 192059807) ^ 7734 = 30819325 := by
        calc
          (5 : ZMod 192059807) ^ 7734 = (5 : ZMod 192059807) ^ (3867 + 3867) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 3867 * (5 : ZMod 192059807) ^ 3867 := by rw [pow_add]
          _ = 30819325 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 192059807) ^ 15468 = 170295967 := by
        calc
          (5 : ZMod 192059807) ^ 15468 = (5 : ZMod 192059807) ^ (7734 + 7734) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 7734 * (5 : ZMod 192059807) ^ 7734 := by rw [pow_add]
          _ = 170295967 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 192059807) ^ 30937 = 183025161 := by
        calc
          (5 : ZMod 192059807) ^ 30937 = (5 : ZMod 192059807) ^ (15468 + 15468 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 15468 * (5 : ZMod 192059807) ^ 15468) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 183025161 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 192059807) ^ 61874 = 178609544 := by
        calc
          (5 : ZMod 192059807) ^ 61874 = (5 : ZMod 192059807) ^ (30937 + 30937) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 30937 * (5 : ZMod 192059807) ^ 30937 := by rw [pow_add]
          _ = 178609544 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 192059807) ^ 123749 = 151681612 := by
        calc
          (5 : ZMod 192059807) ^ 123749 = (5 : ZMod 192059807) ^ (61874 + 61874 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 61874 * (5 : ZMod 192059807) ^ 61874) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 151681612 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 192059807) ^ 247499 = 52629793 := by
        calc
          (5 : ZMod 192059807) ^ 247499 = (5 : ZMod 192059807) ^ (123749 + 123749 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 123749 * (5 : ZMod 192059807) ^ 123749) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 52629793 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 192059807) ^ 494999 = 44007284 := by
        calc
          (5 : ZMod 192059807) ^ 494999 = (5 : ZMod 192059807) ^ (247499 + 247499 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 247499 * (5 : ZMod 192059807) ^ 247499) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 44007284 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 192059807) ^ 989999 = 136590695 := by
        calc
          (5 : ZMod 192059807) ^ 989999 = (5 : ZMod 192059807) ^ (494999 + 494999 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 494999 * (5 : ZMod 192059807) ^ 494999) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 136590695 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 192059807) ^ 1979998 = 78392862 := by
        calc
          (5 : ZMod 192059807) ^ 1979998 = (5 : ZMod 192059807) ^ (989999 + 989999) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 989999 * (5 : ZMod 192059807) ^ 989999 := by rw [pow_add]
          _ = 78392862 := by rw [factor_1_19]; decide
      change (5 : ZMod 192059807) ^ 1979998 ≠ 1
      rw [factor_1_20]
      decide
    ·
      have factor_2_0 : (5 : ZMod 192059807) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 192059807) ^ 3 = 125 := by
        calc
          (5 : ZMod 192059807) ^ 3 = (5 : ZMod 192059807) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 1 * (5 : ZMod 192059807) ^ 1) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 192059807) ^ 6 = 15625 := by
        calc
          (5 : ZMod 192059807) ^ 6 = (5 : ZMod 192059807) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 3 * (5 : ZMod 192059807) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 192059807) ^ 12 = 52080818 := by
        calc
          (5 : ZMod 192059807) ^ 12 = (5 : ZMod 192059807) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 6 * (5 : ZMod 192059807) ^ 6 := by rw [pow_add]
          _ = 52080818 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 192059807) ^ 24 = 116598716 := by
        calc
          (5 : ZMod 192059807) ^ 24 = (5 : ZMod 192059807) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 12 * (5 : ZMod 192059807) ^ 12 := by rw [pow_add]
          _ = 116598716 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 192059807) ^ 48 = 30722263 := by
        calc
          (5 : ZMod 192059807) ^ 48 = (5 : ZMod 192059807) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 24 * (5 : ZMod 192059807) ^ 24 := by rw [pow_add]
          _ = 30722263 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 192059807) ^ 97 = 171635283 := by
        calc
          (5 : ZMod 192059807) ^ 97 = (5 : ZMod 192059807) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = ((5 : ZMod 192059807) ^ 48 * (5 : ZMod 192059807) ^ 48) * (5 : ZMod 192059807) := by rw [pow_succ, pow_add]
          _ = 171635283 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 192059807) ^ 194 = 173609717 := by
        calc
          (5 : ZMod 192059807) ^ 194 = (5 : ZMod 192059807) ^ (97 + 97) :=
            congrArg (fun n : ℕ => (5 : ZMod 192059807) ^ n) (by norm_num)
          _ = (5 : ZMod 192059807) ^ 97 * (5 : ZMod 192059807) ^ 97 := by rw [pow_add]
          _ = 173609717 := by rw [factor_2_6]; decide
      change (5 : ZMod 192059807) ^ 194 ≠ 1
      rw [factor_2_7]
      decide

#print axioms prime_lucas_192059807

end TotientTailPeriodKiller
end Erdos249257
