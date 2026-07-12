import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_914622451 : Nat.Prime 914622451 := by
  apply lucas_primality 914622451 (3 : ZMod 914622451)
  ·
      have fermat_0 : (3 : ZMod 914622451) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 914622451) ^ 3 = 27 := by
        calc
          (3 : ZMod 914622451) ^ 3 = (3 : ZMod 914622451) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 1 * (3 : ZMod 914622451) ^ 1) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 914622451) ^ 6 = 729 := by
        calc
          (3 : ZMod 914622451) ^ 6 = (3 : ZMod 914622451) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 3 * (3 : ZMod 914622451) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 914622451) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 914622451) ^ 13 = (3 : ZMod 914622451) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 6 * (3 : ZMod 914622451) ^ 6) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 914622451) ^ 27 = 390111000 := by
        calc
          (3 : ZMod 914622451) ^ 27 = (3 : ZMod 914622451) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 13 * (3 : ZMod 914622451) ^ 13) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 390111000 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 914622451) ^ 54 = 841624749 := by
        calc
          (3 : ZMod 914622451) ^ 54 = (3 : ZMod 914622451) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 27 * (3 : ZMod 914622451) ^ 27 := by rw [pow_add]
          _ = 841624749 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 914622451) ^ 109 = 40008819 := by
        calc
          (3 : ZMod 914622451) ^ 109 = (3 : ZMod 914622451) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 54 * (3 : ZMod 914622451) ^ 54) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 40008819 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 914622451) ^ 218 = 151473484 := by
        calc
          (3 : ZMod 914622451) ^ 218 = (3 : ZMod 914622451) ^ (109 + 109) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 109 * (3 : ZMod 914622451) ^ 109 := by rw [pow_add]
          _ = 151473484 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 914622451) ^ 436 = 293179609 := by
        calc
          (3 : ZMod 914622451) ^ 436 = (3 : ZMod 914622451) ^ (218 + 218) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 218 * (3 : ZMod 914622451) ^ 218 := by rw [pow_add]
          _ = 293179609 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 914622451) ^ 872 = 529519197 := by
        calc
          (3 : ZMod 914622451) ^ 872 = (3 : ZMod 914622451) ^ (436 + 436) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 436 * (3 : ZMod 914622451) ^ 436 := by rw [pow_add]
          _ = 529519197 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 914622451) ^ 1744 = 426517372 := by
        calc
          (3 : ZMod 914622451) ^ 1744 = (3 : ZMod 914622451) ^ (872 + 872) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 872 * (3 : ZMod 914622451) ^ 872 := by rw [pow_add]
          _ = 426517372 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 914622451) ^ 3489 = 875729238 := by
        calc
          (3 : ZMod 914622451) ^ 3489 = (3 : ZMod 914622451) ^ (1744 + 1744 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 1744 * (3 : ZMod 914622451) ^ 1744) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 875729238 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 914622451) ^ 6978 = 750468783 := by
        calc
          (3 : ZMod 914622451) ^ 6978 = (3 : ZMod 914622451) ^ (3489 + 3489) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 3489 * (3 : ZMod 914622451) ^ 3489 := by rw [pow_add]
          _ = 750468783 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 914622451) ^ 13956 = 247115071 := by
        calc
          (3 : ZMod 914622451) ^ 13956 = (3 : ZMod 914622451) ^ (6978 + 6978) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 6978 * (3 : ZMod 914622451) ^ 6978 := by rw [pow_add]
          _ = 247115071 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 914622451) ^ 27912 = 144358449 := by
        calc
          (3 : ZMod 914622451) ^ 27912 = (3 : ZMod 914622451) ^ (13956 + 13956) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 13956 * (3 : ZMod 914622451) ^ 13956 := by rw [pow_add]
          _ = 144358449 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 914622451) ^ 55824 = 223283941 := by
        calc
          (3 : ZMod 914622451) ^ 55824 = (3 : ZMod 914622451) ^ (27912 + 27912) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 27912 * (3 : ZMod 914622451) ^ 27912 := by rw [pow_add]
          _ = 223283941 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 914622451) ^ 111648 = 634125116 := by
        calc
          (3 : ZMod 914622451) ^ 111648 = (3 : ZMod 914622451) ^ (55824 + 55824) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 55824 * (3 : ZMod 914622451) ^ 55824 := by rw [pow_add]
          _ = 634125116 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 914622451) ^ 223296 = 342126770 := by
        calc
          (3 : ZMod 914622451) ^ 223296 = (3 : ZMod 914622451) ^ (111648 + 111648) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 111648 * (3 : ZMod 914622451) ^ 111648 := by rw [pow_add]
          _ = 342126770 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 914622451) ^ 446592 = 620628153 := by
        calc
          (3 : ZMod 914622451) ^ 446592 = (3 : ZMod 914622451) ^ (223296 + 223296) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 223296 * (3 : ZMod 914622451) ^ 223296 := by rw [pow_add]
          _ = 620628153 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 914622451) ^ 893185 = 113441104 := by
        calc
          (3 : ZMod 914622451) ^ 893185 = (3 : ZMod 914622451) ^ (446592 + 446592 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 446592 * (3 : ZMod 914622451) ^ 446592) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 113441104 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 914622451) ^ 1786371 = 469352419 := by
        calc
          (3 : ZMod 914622451) ^ 1786371 = (3 : ZMod 914622451) ^ (893185 + 893185 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 893185 * (3 : ZMod 914622451) ^ 893185) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 469352419 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 914622451) ^ 3572743 = 136545840 := by
        calc
          (3 : ZMod 914622451) ^ 3572743 = (3 : ZMod 914622451) ^ (1786371 + 1786371 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 1786371 * (3 : ZMod 914622451) ^ 1786371) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 136545840 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 914622451) ^ 7145487 = 780204435 := by
        calc
          (3 : ZMod 914622451) ^ 7145487 = (3 : ZMod 914622451) ^ (3572743 + 3572743 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 3572743 * (3 : ZMod 914622451) ^ 3572743) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 780204435 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 914622451) ^ 14290975 = 669869955 := by
        calc
          (3 : ZMod 914622451) ^ 14290975 = (3 : ZMod 914622451) ^ (7145487 + 7145487 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 7145487 * (3 : ZMod 914622451) ^ 7145487) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 669869955 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 914622451) ^ 28581951 = 876359324 := by
        calc
          (3 : ZMod 914622451) ^ 28581951 = (3 : ZMod 914622451) ^ (14290975 + 14290975 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 14290975 * (3 : ZMod 914622451) ^ 14290975) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 876359324 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 914622451) ^ 57163903 = 729262187 := by
        calc
          (3 : ZMod 914622451) ^ 57163903 = (3 : ZMod 914622451) ^ (28581951 + 28581951 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 28581951 * (3 : ZMod 914622451) ^ 28581951) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 729262187 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 914622451) ^ 114327806 = 350353702 := by
        calc
          (3 : ZMod 914622451) ^ 114327806 = (3 : ZMod 914622451) ^ (57163903 + 57163903) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 57163903 * (3 : ZMod 914622451) ^ 57163903 := by rw [pow_add]
          _ = 350353702 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 914622451) ^ 228655612 = 113158218 := by
        calc
          (3 : ZMod 914622451) ^ 228655612 = (3 : ZMod 914622451) ^ (114327806 + 114327806) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 114327806 * (3 : ZMod 914622451) ^ 114327806 := by rw [pow_add]
          _ = 113158218 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 914622451) ^ 457311225 = 914622450 := by
        calc
          (3 : ZMod 914622451) ^ 457311225 = (3 : ZMod 914622451) ^ (228655612 + 228655612 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 228655612 * (3 : ZMod 914622451) ^ 228655612) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 914622450 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 914622451) ^ 914622450 = 1 := by
        calc
          (3 : ZMod 914622451) ^ 914622450 = (3 : ZMod 914622451) ^ (457311225 + 457311225) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 457311225 * (3 : ZMod 914622451) ^ 457311225 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (7, 1), (31, 1), (28099, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (7, 1), (31, 1), (28099, 1)] : List FactorBlock).map factorBlockValue).prod = 914622451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 914622451) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 914622451) ^ 3 = 27 := by
        calc
          (3 : ZMod 914622451) ^ 3 = (3 : ZMod 914622451) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 1 * (3 : ZMod 914622451) ^ 1) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 914622451) ^ 6 = 729 := by
        calc
          (3 : ZMod 914622451) ^ 6 = (3 : ZMod 914622451) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 3 * (3 : ZMod 914622451) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 914622451) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 914622451) ^ 13 = (3 : ZMod 914622451) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 6 * (3 : ZMod 914622451) ^ 6) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 914622451) ^ 27 = 390111000 := by
        calc
          (3 : ZMod 914622451) ^ 27 = (3 : ZMod 914622451) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 13 * (3 : ZMod 914622451) ^ 13) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 390111000 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 914622451) ^ 54 = 841624749 := by
        calc
          (3 : ZMod 914622451) ^ 54 = (3 : ZMod 914622451) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 27 * (3 : ZMod 914622451) ^ 27 := by rw [pow_add]
          _ = 841624749 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 914622451) ^ 109 = 40008819 := by
        calc
          (3 : ZMod 914622451) ^ 109 = (3 : ZMod 914622451) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 54 * (3 : ZMod 914622451) ^ 54) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 40008819 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 914622451) ^ 218 = 151473484 := by
        calc
          (3 : ZMod 914622451) ^ 218 = (3 : ZMod 914622451) ^ (109 + 109) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 109 * (3 : ZMod 914622451) ^ 109 := by rw [pow_add]
          _ = 151473484 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 914622451) ^ 436 = 293179609 := by
        calc
          (3 : ZMod 914622451) ^ 436 = (3 : ZMod 914622451) ^ (218 + 218) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 218 * (3 : ZMod 914622451) ^ 218 := by rw [pow_add]
          _ = 293179609 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 914622451) ^ 872 = 529519197 := by
        calc
          (3 : ZMod 914622451) ^ 872 = (3 : ZMod 914622451) ^ (436 + 436) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 436 * (3 : ZMod 914622451) ^ 436 := by rw [pow_add]
          _ = 529519197 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 914622451) ^ 1744 = 426517372 := by
        calc
          (3 : ZMod 914622451) ^ 1744 = (3 : ZMod 914622451) ^ (872 + 872) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 872 * (3 : ZMod 914622451) ^ 872 := by rw [pow_add]
          _ = 426517372 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 914622451) ^ 3489 = 875729238 := by
        calc
          (3 : ZMod 914622451) ^ 3489 = (3 : ZMod 914622451) ^ (1744 + 1744 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 1744 * (3 : ZMod 914622451) ^ 1744) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 875729238 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 914622451) ^ 6978 = 750468783 := by
        calc
          (3 : ZMod 914622451) ^ 6978 = (3 : ZMod 914622451) ^ (3489 + 3489) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 3489 * (3 : ZMod 914622451) ^ 3489 := by rw [pow_add]
          _ = 750468783 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 914622451) ^ 13956 = 247115071 := by
        calc
          (3 : ZMod 914622451) ^ 13956 = (3 : ZMod 914622451) ^ (6978 + 6978) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 6978 * (3 : ZMod 914622451) ^ 6978 := by rw [pow_add]
          _ = 247115071 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 914622451) ^ 27912 = 144358449 := by
        calc
          (3 : ZMod 914622451) ^ 27912 = (3 : ZMod 914622451) ^ (13956 + 13956) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 13956 * (3 : ZMod 914622451) ^ 13956 := by rw [pow_add]
          _ = 144358449 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 914622451) ^ 55824 = 223283941 := by
        calc
          (3 : ZMod 914622451) ^ 55824 = (3 : ZMod 914622451) ^ (27912 + 27912) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 27912 * (3 : ZMod 914622451) ^ 27912 := by rw [pow_add]
          _ = 223283941 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 914622451) ^ 111648 = 634125116 := by
        calc
          (3 : ZMod 914622451) ^ 111648 = (3 : ZMod 914622451) ^ (55824 + 55824) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 55824 * (3 : ZMod 914622451) ^ 55824 := by rw [pow_add]
          _ = 634125116 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 914622451) ^ 223296 = 342126770 := by
        calc
          (3 : ZMod 914622451) ^ 223296 = (3 : ZMod 914622451) ^ (111648 + 111648) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 111648 * (3 : ZMod 914622451) ^ 111648 := by rw [pow_add]
          _ = 342126770 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 914622451) ^ 446592 = 620628153 := by
        calc
          (3 : ZMod 914622451) ^ 446592 = (3 : ZMod 914622451) ^ (223296 + 223296) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 223296 * (3 : ZMod 914622451) ^ 223296 := by rw [pow_add]
          _ = 620628153 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 914622451) ^ 893185 = 113441104 := by
        calc
          (3 : ZMod 914622451) ^ 893185 = (3 : ZMod 914622451) ^ (446592 + 446592 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 446592 * (3 : ZMod 914622451) ^ 446592) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 113441104 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 914622451) ^ 1786371 = 469352419 := by
        calc
          (3 : ZMod 914622451) ^ 1786371 = (3 : ZMod 914622451) ^ (893185 + 893185 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 893185 * (3 : ZMod 914622451) ^ 893185) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 469352419 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 914622451) ^ 3572743 = 136545840 := by
        calc
          (3 : ZMod 914622451) ^ 3572743 = (3 : ZMod 914622451) ^ (1786371 + 1786371 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 1786371 * (3 : ZMod 914622451) ^ 1786371) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 136545840 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 914622451) ^ 7145487 = 780204435 := by
        calc
          (3 : ZMod 914622451) ^ 7145487 = (3 : ZMod 914622451) ^ (3572743 + 3572743 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 3572743 * (3 : ZMod 914622451) ^ 3572743) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 780204435 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 914622451) ^ 14290975 = 669869955 := by
        calc
          (3 : ZMod 914622451) ^ 14290975 = (3 : ZMod 914622451) ^ (7145487 + 7145487 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 7145487 * (3 : ZMod 914622451) ^ 7145487) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 669869955 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 914622451) ^ 28581951 = 876359324 := by
        calc
          (3 : ZMod 914622451) ^ 28581951 = (3 : ZMod 914622451) ^ (14290975 + 14290975 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 14290975 * (3 : ZMod 914622451) ^ 14290975) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 876359324 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 914622451) ^ 57163903 = 729262187 := by
        calc
          (3 : ZMod 914622451) ^ 57163903 = (3 : ZMod 914622451) ^ (28581951 + 28581951 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 28581951 * (3 : ZMod 914622451) ^ 28581951) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 729262187 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 914622451) ^ 114327806 = 350353702 := by
        calc
          (3 : ZMod 914622451) ^ 114327806 = (3 : ZMod 914622451) ^ (57163903 + 57163903) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 57163903 * (3 : ZMod 914622451) ^ 57163903 := by rw [pow_add]
          _ = 350353702 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 914622451) ^ 228655612 = 113158218 := by
        calc
          (3 : ZMod 914622451) ^ 228655612 = (3 : ZMod 914622451) ^ (114327806 + 114327806) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 114327806 * (3 : ZMod 914622451) ^ 114327806 := by rw [pow_add]
          _ = 113158218 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 914622451) ^ 457311225 = 914622450 := by
        calc
          (3 : ZMod 914622451) ^ 457311225 = (3 : ZMod 914622451) ^ (228655612 + 228655612 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 228655612 * (3 : ZMod 914622451) ^ 228655612) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 914622450 := by rw [factor_0_27]; decide
      change (3 : ZMod 914622451) ^ 457311225 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (3 : ZMod 914622451) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 914622451) ^ 2 = 9 := by
        calc
          (3 : ZMod 914622451) ^ 2 = (3 : ZMod 914622451) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 1 * (3 : ZMod 914622451) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 914622451) ^ 4 = 81 := by
        calc
          (3 : ZMod 914622451) ^ 4 = (3 : ZMod 914622451) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 2 * (3 : ZMod 914622451) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 914622451) ^ 9 = 19683 := by
        calc
          (3 : ZMod 914622451) ^ 9 = (3 : ZMod 914622451) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 4 * (3 : ZMod 914622451) ^ 4) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 914622451) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 914622451) ^ 18 = (3 : ZMod 914622451) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 9 * (3 : ZMod 914622451) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 914622451) ^ 36 = 299336855 := by
        calc
          (3 : ZMod 914622451) ^ 36 = (3 : ZMod 914622451) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 18 * (3 : ZMod 914622451) ^ 18 := by rw [pow_add]
          _ = 299336855 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 914622451) ^ 72 = 344684815 := by
        calc
          (3 : ZMod 914622451) ^ 72 = (3 : ZMod 914622451) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 36 * (3 : ZMod 914622451) ^ 36 := by rw [pow_add]
          _ = 344684815 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 914622451) ^ 145 = 117962793 := by
        calc
          (3 : ZMod 914622451) ^ 145 = (3 : ZMod 914622451) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 72 * (3 : ZMod 914622451) ^ 72) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 117962793 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 914622451) ^ 290 = 906275081 := by
        calc
          (3 : ZMod 914622451) ^ 290 = (3 : ZMod 914622451) ^ (145 + 145) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 145 * (3 : ZMod 914622451) ^ 145 := by rw [pow_add]
          _ = 906275081 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 914622451) ^ 581 = 625819552 := by
        calc
          (3 : ZMod 914622451) ^ 581 = (3 : ZMod 914622451) ^ (290 + 290 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 290 * (3 : ZMod 914622451) ^ 290) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 625819552 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 914622451) ^ 1163 = 632232920 := by
        calc
          (3 : ZMod 914622451) ^ 1163 = (3 : ZMod 914622451) ^ (581 + 581 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 581 * (3 : ZMod 914622451) ^ 581) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 632232920 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 914622451) ^ 2326 = 140275790 := by
        calc
          (3 : ZMod 914622451) ^ 2326 = (3 : ZMod 914622451) ^ (1163 + 1163) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 1163 * (3 : ZMod 914622451) ^ 1163 := by rw [pow_add]
          _ = 140275790 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 914622451) ^ 4652 = 94615980 := by
        calc
          (3 : ZMod 914622451) ^ 4652 = (3 : ZMod 914622451) ^ (2326 + 2326) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 2326 * (3 : ZMod 914622451) ^ 2326 := by rw [pow_add]
          _ = 94615980 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 914622451) ^ 9304 = 887452305 := by
        calc
          (3 : ZMod 914622451) ^ 9304 = (3 : ZMod 914622451) ^ (4652 + 4652) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 4652 * (3 : ZMod 914622451) ^ 4652 := by rw [pow_add]
          _ = 887452305 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 914622451) ^ 18608 = 358653039 := by
        calc
          (3 : ZMod 914622451) ^ 18608 = (3 : ZMod 914622451) ^ (9304 + 9304) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 9304 * (3 : ZMod 914622451) ^ 9304 := by rw [pow_add]
          _ = 358653039 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 914622451) ^ 37216 = 259153767 := by
        calc
          (3 : ZMod 914622451) ^ 37216 = (3 : ZMod 914622451) ^ (18608 + 18608) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 18608 * (3 : ZMod 914622451) ^ 18608 := by rw [pow_add]
          _ = 259153767 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 914622451) ^ 74432 = 506839996 := by
        calc
          (3 : ZMod 914622451) ^ 74432 = (3 : ZMod 914622451) ^ (37216 + 37216) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 37216 * (3 : ZMod 914622451) ^ 37216 := by rw [pow_add]
          _ = 506839996 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 914622451) ^ 148864 = 520917144 := by
        calc
          (3 : ZMod 914622451) ^ 148864 = (3 : ZMod 914622451) ^ (74432 + 74432) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 74432 * (3 : ZMod 914622451) ^ 74432 := by rw [pow_add]
          _ = 520917144 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 914622451) ^ 297728 = 500426836 := by
        calc
          (3 : ZMod 914622451) ^ 297728 = (3 : ZMod 914622451) ^ (148864 + 148864) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 148864 * (3 : ZMod 914622451) ^ 148864 := by rw [pow_add]
          _ = 500426836 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 914622451) ^ 595457 = 884612666 := by
        calc
          (3 : ZMod 914622451) ^ 595457 = (3 : ZMod 914622451) ^ (297728 + 297728 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 297728 * (3 : ZMod 914622451) ^ 297728) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 884612666 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 914622451) ^ 1190914 = 540879271 := by
        calc
          (3 : ZMod 914622451) ^ 1190914 = (3 : ZMod 914622451) ^ (595457 + 595457) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 595457 * (3 : ZMod 914622451) ^ 595457 := by rw [pow_add]
          _ = 540879271 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 914622451) ^ 2381829 = 406236038 := by
        calc
          (3 : ZMod 914622451) ^ 2381829 = (3 : ZMod 914622451) ^ (1190914 + 1190914 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 1190914 * (3 : ZMod 914622451) ^ 1190914) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 406236038 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 914622451) ^ 4763658 = 742165432 := by
        calc
          (3 : ZMod 914622451) ^ 4763658 = (3 : ZMod 914622451) ^ (2381829 + 2381829) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 2381829 * (3 : ZMod 914622451) ^ 2381829 := by rw [pow_add]
          _ = 742165432 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 914622451) ^ 9527317 = 148491767 := by
        calc
          (3 : ZMod 914622451) ^ 9527317 = (3 : ZMod 914622451) ^ (4763658 + 4763658 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 4763658 * (3 : ZMod 914622451) ^ 4763658) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 148491767 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 914622451) ^ 19054634 = 843563895 := by
        calc
          (3 : ZMod 914622451) ^ 19054634 = (3 : ZMod 914622451) ^ (9527317 + 9527317) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 9527317 * (3 : ZMod 914622451) ^ 9527317 := by rw [pow_add]
          _ = 843563895 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 914622451) ^ 38109268 = 629712378 := by
        calc
          (3 : ZMod 914622451) ^ 38109268 = (3 : ZMod 914622451) ^ (19054634 + 19054634) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 19054634 * (3 : ZMod 914622451) ^ 19054634 := by rw [pow_add]
          _ = 629712378 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 914622451) ^ 76218537 = 513890334 := by
        calc
          (3 : ZMod 914622451) ^ 76218537 = (3 : ZMod 914622451) ^ (38109268 + 38109268 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 38109268 * (3 : ZMod 914622451) ^ 38109268) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 513890334 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 914622451) ^ 152437075 = 287573899 := by
        calc
          (3 : ZMod 914622451) ^ 152437075 = (3 : ZMod 914622451) ^ (76218537 + 76218537 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 76218537 * (3 : ZMod 914622451) ^ 76218537) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 287573899 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 914622451) ^ 304874150 = 287573898 := by
        calc
          (3 : ZMod 914622451) ^ 304874150 = (3 : ZMod 914622451) ^ (152437075 + 152437075) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 152437075 * (3 : ZMod 914622451) ^ 152437075 := by rw [pow_add]
          _ = 287573898 := by rw [factor_1_27]; decide
      change (3 : ZMod 914622451) ^ 304874150 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (3 : ZMod 914622451) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 914622451) ^ 2 = 9 := by
        calc
          (3 : ZMod 914622451) ^ 2 = (3 : ZMod 914622451) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 1 * (3 : ZMod 914622451) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 914622451) ^ 5 = 243 := by
        calc
          (3 : ZMod 914622451) ^ 5 = (3 : ZMod 914622451) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 2 * (3 : ZMod 914622451) ^ 2) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 914622451) ^ 10 = 59049 := by
        calc
          (3 : ZMod 914622451) ^ 10 = (3 : ZMod 914622451) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 5 * (3 : ZMod 914622451) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 914622451) ^ 21 = 399506242 := by
        calc
          (3 : ZMod 914622451) ^ 21 = (3 : ZMod 914622451) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 10 * (3 : ZMod 914622451) ^ 10) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 399506242 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 914622451) ^ 43 = 694649420 := by
        calc
          (3 : ZMod 914622451) ^ 43 = (3 : ZMod 914622451) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 21 * (3 : ZMod 914622451) ^ 21) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 694649420 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 914622451) ^ 87 = 183046273 := by
        calc
          (3 : ZMod 914622451) ^ 87 = (3 : ZMod 914622451) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 43 * (3 : ZMod 914622451) ^ 43) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 183046273 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 914622451) ^ 174 = 343430752 := by
        calc
          (3 : ZMod 914622451) ^ 174 = (3 : ZMod 914622451) ^ (87 + 87) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 87 * (3 : ZMod 914622451) ^ 87 := by rw [pow_add]
          _ = 343430752 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 914622451) ^ 348 = 561806004 := by
        calc
          (3 : ZMod 914622451) ^ 348 = (3 : ZMod 914622451) ^ (174 + 174) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 174 * (3 : ZMod 914622451) ^ 174 := by rw [pow_add]
          _ = 561806004 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 914622451) ^ 697 = 332581176 := by
        calc
          (3 : ZMod 914622451) ^ 697 = (3 : ZMod 914622451) ^ (348 + 348 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 348 * (3 : ZMod 914622451) ^ 348) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 332581176 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 914622451) ^ 1395 = 799561257 := by
        calc
          (3 : ZMod 914622451) ^ 1395 = (3 : ZMod 914622451) ^ (697 + 697 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 697 * (3 : ZMod 914622451) ^ 697) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 799561257 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 914622451) ^ 2791 = 278258776 := by
        calc
          (3 : ZMod 914622451) ^ 2791 = (3 : ZMod 914622451) ^ (1395 + 1395 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 1395 * (3 : ZMod 914622451) ^ 1395) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 278258776 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 914622451) ^ 5582 = 217111889 := by
        calc
          (3 : ZMod 914622451) ^ 5582 = (3 : ZMod 914622451) ^ (2791 + 2791) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 2791 * (3 : ZMod 914622451) ^ 2791 := by rw [pow_add]
          _ = 217111889 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 914622451) ^ 11164 = 96592483 := by
        calc
          (3 : ZMod 914622451) ^ 11164 = (3 : ZMod 914622451) ^ (5582 + 5582) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 5582 * (3 : ZMod 914622451) ^ 5582 := by rw [pow_add]
          _ = 96592483 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 914622451) ^ 22329 = 742729923 := by
        calc
          (3 : ZMod 914622451) ^ 22329 = (3 : ZMod 914622451) ^ (11164 + 11164 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 11164 * (3 : ZMod 914622451) ^ 11164) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 742729923 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 914622451) ^ 44659 = 299638518 := by
        calc
          (3 : ZMod 914622451) ^ 44659 = (3 : ZMod 914622451) ^ (22329 + 22329 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 22329 * (3 : ZMod 914622451) ^ 22329) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 299638518 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 914622451) ^ 89318 = 814322809 := by
        calc
          (3 : ZMod 914622451) ^ 89318 = (3 : ZMod 914622451) ^ (44659 + 44659) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 44659 * (3 : ZMod 914622451) ^ 44659 := by rw [pow_add]
          _ = 814322809 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 914622451) ^ 178637 = 531428761 := by
        calc
          (3 : ZMod 914622451) ^ 178637 = (3 : ZMod 914622451) ^ (89318 + 89318 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 89318 * (3 : ZMod 914622451) ^ 89318) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 531428761 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 914622451) ^ 357274 = 273563369 := by
        calc
          (3 : ZMod 914622451) ^ 357274 = (3 : ZMod 914622451) ^ (178637 + 178637) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 178637 * (3 : ZMod 914622451) ^ 178637 := by rw [pow_add]
          _ = 273563369 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 914622451) ^ 714548 = 23049519 := by
        calc
          (3 : ZMod 914622451) ^ 714548 = (3 : ZMod 914622451) ^ (357274 + 357274) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 357274 * (3 : ZMod 914622451) ^ 357274 := by rw [pow_add]
          _ = 23049519 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 914622451) ^ 1429097 = 688210012 := by
        calc
          (3 : ZMod 914622451) ^ 1429097 = (3 : ZMod 914622451) ^ (714548 + 714548 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 714548 * (3 : ZMod 914622451) ^ 714548) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 688210012 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 914622451) ^ 2858195 = 499322860 := by
        calc
          (3 : ZMod 914622451) ^ 2858195 = (3 : ZMod 914622451) ^ (1429097 + 1429097 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 1429097 * (3 : ZMod 914622451) ^ 1429097) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 499322860 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 914622451) ^ 5716390 = 535781620 := by
        calc
          (3 : ZMod 914622451) ^ 5716390 = (3 : ZMod 914622451) ^ (2858195 + 2858195) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 2858195 * (3 : ZMod 914622451) ^ 2858195 := by rw [pow_add]
          _ = 535781620 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 914622451) ^ 11432780 = 681773745 := by
        calc
          (3 : ZMod 914622451) ^ 11432780 = (3 : ZMod 914622451) ^ (5716390 + 5716390) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 5716390 * (3 : ZMod 914622451) ^ 5716390 := by rw [pow_add]
          _ = 681773745 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 914622451) ^ 22865561 = 216407739 := by
        calc
          (3 : ZMod 914622451) ^ 22865561 = (3 : ZMod 914622451) ^ (11432780 + 11432780 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 11432780 * (3 : ZMod 914622451) ^ 11432780) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 216407739 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 914622451) ^ 45731122 = 725159592 := by
        calc
          (3 : ZMod 914622451) ^ 45731122 = (3 : ZMod 914622451) ^ (22865561 + 22865561) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 22865561 * (3 : ZMod 914622451) ^ 22865561 := by rw [pow_add]
          _ = 725159592 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 914622451) ^ 91462245 = 317691134 := by
        calc
          (3 : ZMod 914622451) ^ 91462245 = (3 : ZMod 914622451) ^ (45731122 + 45731122 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 45731122 * (3 : ZMod 914622451) ^ 45731122) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 317691134 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 914622451) ^ 182924490 = 240011074 := by
        calc
          (3 : ZMod 914622451) ^ 182924490 = (3 : ZMod 914622451) ^ (91462245 + 91462245) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 91462245 * (3 : ZMod 914622451) ^ 91462245 := by rw [pow_add]
          _ = 240011074 := by rw [factor_2_26]; decide
      change (3 : ZMod 914622451) ^ 182924490 ≠ 1
      rw [factor_2_27]
      decide
    ·
      have factor_3_0 : (3 : ZMod 914622451) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 914622451) ^ 3 = 27 := by
        calc
          (3 : ZMod 914622451) ^ 3 = (3 : ZMod 914622451) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 1 * (3 : ZMod 914622451) ^ 1) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 914622451) ^ 7 = 2187 := by
        calc
          (3 : ZMod 914622451) ^ 7 = (3 : ZMod 914622451) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 3 * (3 : ZMod 914622451) ^ 3) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 914622451) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 914622451) ^ 15 = (3 : ZMod 914622451) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 7 * (3 : ZMod 914622451) ^ 7) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 914622451) ^ 31 = 501827666 := by
        calc
          (3 : ZMod 914622451) ^ 31 = (3 : ZMod 914622451) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 15 * (3 : ZMod 914622451) ^ 15) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 501827666 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 914622451) ^ 62 = 324241502 := by
        calc
          (3 : ZMod 914622451) ^ 62 = (3 : ZMod 914622451) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 31 * (3 : ZMod 914622451) ^ 31 := by rw [pow_add]
          _ = 324241502 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 914622451) ^ 124 = 834569212 := by
        calc
          (3 : ZMod 914622451) ^ 124 = (3 : ZMod 914622451) ^ (62 + 62) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 62 * (3 : ZMod 914622451) ^ 62 := by rw [pow_add]
          _ = 834569212 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 914622451) ^ 249 = 830081496 := by
        calc
          (3 : ZMod 914622451) ^ 249 = (3 : ZMod 914622451) ^ (124 + 124 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 124 * (3 : ZMod 914622451) ^ 124) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 830081496 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 914622451) ^ 498 = 439319783 := by
        calc
          (3 : ZMod 914622451) ^ 498 = (3 : ZMod 914622451) ^ (249 + 249) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 249 * (3 : ZMod 914622451) ^ 249 := by rw [pow_add]
          _ = 439319783 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 914622451) ^ 996 = 29497911 := by
        calc
          (3 : ZMod 914622451) ^ 996 = (3 : ZMod 914622451) ^ (498 + 498) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 498 * (3 : ZMod 914622451) ^ 498 := by rw [pow_add]
          _ = 29497911 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 914622451) ^ 1993 = 224570311 := by
        calc
          (3 : ZMod 914622451) ^ 1993 = (3 : ZMod 914622451) ^ (996 + 996 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 996 * (3 : ZMod 914622451) ^ 996) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 224570311 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 914622451) ^ 3987 = 751789114 := by
        calc
          (3 : ZMod 914622451) ^ 3987 = (3 : ZMod 914622451) ^ (1993 + 1993 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 1993 * (3 : ZMod 914622451) ^ 1993) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 751789114 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 914622451) ^ 7974 = 232606848 := by
        calc
          (3 : ZMod 914622451) ^ 7974 = (3 : ZMod 914622451) ^ (3987 + 3987) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 3987 * (3 : ZMod 914622451) ^ 3987 := by rw [pow_add]
          _ = 232606848 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 914622451) ^ 15949 = 279056591 := by
        calc
          (3 : ZMod 914622451) ^ 15949 = (3 : ZMod 914622451) ^ (7974 + 7974 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 7974 * (3 : ZMod 914622451) ^ 7974) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 279056591 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 914622451) ^ 31899 = 654917562 := by
        calc
          (3 : ZMod 914622451) ^ 31899 = (3 : ZMod 914622451) ^ (15949 + 15949 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 15949 * (3 : ZMod 914622451) ^ 15949) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 654917562 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 914622451) ^ 63798 = 46991780 := by
        calc
          (3 : ZMod 914622451) ^ 63798 = (3 : ZMod 914622451) ^ (31899 + 31899) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 31899 * (3 : ZMod 914622451) ^ 31899 := by rw [pow_add]
          _ = 46991780 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 914622451) ^ 127597 = 409561022 := by
        calc
          (3 : ZMod 914622451) ^ 127597 = (3 : ZMod 914622451) ^ (63798 + 63798 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 63798 * (3 : ZMod 914622451) ^ 63798) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 409561022 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 914622451) ^ 255195 = 114088060 := by
        calc
          (3 : ZMod 914622451) ^ 255195 = (3 : ZMod 914622451) ^ (127597 + 127597 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 127597 * (3 : ZMod 914622451) ^ 127597) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 114088060 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 914622451) ^ 510391 = 128677794 := by
        calc
          (3 : ZMod 914622451) ^ 510391 = (3 : ZMod 914622451) ^ (255195 + 255195 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 255195 * (3 : ZMod 914622451) ^ 255195) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 128677794 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 914622451) ^ 1020783 = 348603507 := by
        calc
          (3 : ZMod 914622451) ^ 1020783 = (3 : ZMod 914622451) ^ (510391 + 510391 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 510391 * (3 : ZMod 914622451) ^ 510391) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 348603507 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 914622451) ^ 2041567 = 576986752 := by
        calc
          (3 : ZMod 914622451) ^ 2041567 = (3 : ZMod 914622451) ^ (1020783 + 1020783 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 1020783 * (3 : ZMod 914622451) ^ 1020783) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 576986752 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 914622451) ^ 4083135 = 216199474 := by
        calc
          (3 : ZMod 914622451) ^ 4083135 = (3 : ZMod 914622451) ^ (2041567 + 2041567 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 2041567 * (3 : ZMod 914622451) ^ 2041567) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 216199474 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 914622451) ^ 8166271 = 578551961 := by
        calc
          (3 : ZMod 914622451) ^ 8166271 = (3 : ZMod 914622451) ^ (4083135 + 4083135 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 4083135 * (3 : ZMod 914622451) ^ 4083135) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 578551961 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 914622451) ^ 16332543 = 513021496 := by
        calc
          (3 : ZMod 914622451) ^ 16332543 = (3 : ZMod 914622451) ^ (8166271 + 8166271 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 8166271 * (3 : ZMod 914622451) ^ 8166271) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 513021496 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 914622451) ^ 32665087 = 206591348 := by
        calc
          (3 : ZMod 914622451) ^ 32665087 = (3 : ZMod 914622451) ^ (16332543 + 16332543 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 16332543 * (3 : ZMod 914622451) ^ 16332543) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 206591348 := by rw [factor_3_23]; decide
      have factor_3_25 : (3 : ZMod 914622451) ^ 65330175 = 83213721 := by
        calc
          (3 : ZMod 914622451) ^ 65330175 = (3 : ZMod 914622451) ^ (32665087 + 32665087 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 32665087 * (3 : ZMod 914622451) ^ 32665087) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 83213721 := by rw [factor_3_24]; decide
      have factor_3_26 : (3 : ZMod 914622451) ^ 130660350 = 16787882 := by
        calc
          (3 : ZMod 914622451) ^ 130660350 = (3 : ZMod 914622451) ^ (65330175 + 65330175) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 65330175 * (3 : ZMod 914622451) ^ 65330175 := by rw [pow_add]
          _ = 16787882 := by rw [factor_3_25]; decide
      change (3 : ZMod 914622451) ^ 130660350 ≠ 1
      rw [factor_3_26]
      decide
    ·
      have factor_4_0 : (3 : ZMod 914622451) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 914622451) ^ 3 = 27 := by
        calc
          (3 : ZMod 914622451) ^ 3 = (3 : ZMod 914622451) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 1 * (3 : ZMod 914622451) ^ 1) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 914622451) ^ 7 = 2187 := by
        calc
          (3 : ZMod 914622451) ^ 7 = (3 : ZMod 914622451) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 3 * (3 : ZMod 914622451) ^ 3) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 914622451) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 914622451) ^ 14 = (3 : ZMod 914622451) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 7 * (3 : ZMod 914622451) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 914622451) ^ 28 = 255710549 := by
        calc
          (3 : ZMod 914622451) ^ 28 = (3 : ZMod 914622451) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 14 * (3 : ZMod 914622451) ^ 14 := by rw [pow_add]
          _ = 255710549 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 914622451) ^ 56 = 257643133 := by
        calc
          (3 : ZMod 914622451) ^ 56 = (3 : ZMod 914622451) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 28 * (3 : ZMod 914622451) ^ 28 := by rw [pow_add]
          _ = 257643133 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 914622451) ^ 112 = 165615662 := by
        calc
          (3 : ZMod 914622451) ^ 112 = (3 : ZMod 914622451) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 56 * (3 : ZMod 914622451) ^ 56 := by rw [pow_add]
          _ = 165615662 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 914622451) ^ 225 = 179182246 := by
        calc
          (3 : ZMod 914622451) ^ 225 = (3 : ZMod 914622451) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 112 * (3 : ZMod 914622451) ^ 112) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 179182246 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 914622451) ^ 450 = 21946804 := by
        calc
          (3 : ZMod 914622451) ^ 450 = (3 : ZMod 914622451) ^ (225 + 225) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 225 * (3 : ZMod 914622451) ^ 225 := by rw [pow_add]
          _ = 21946804 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 914622451) ^ 900 = 72178992 := by
        calc
          (3 : ZMod 914622451) ^ 900 = (3 : ZMod 914622451) ^ (450 + 450) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 450 * (3 : ZMod 914622451) ^ 450 := by rw [pow_add]
          _ = 72178992 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 914622451) ^ 1800 = 333566336 := by
        calc
          (3 : ZMod 914622451) ^ 1800 = (3 : ZMod 914622451) ^ (900 + 900) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 900 * (3 : ZMod 914622451) ^ 900 := by rw [pow_add]
          _ = 333566336 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 914622451) ^ 3601 = 342845300 := by
        calc
          (3 : ZMod 914622451) ^ 3601 = (3 : ZMod 914622451) ^ (1800 + 1800 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 1800 * (3 : ZMod 914622451) ^ 1800) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 342845300 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 914622451) ^ 7203 = 52483909 := by
        calc
          (3 : ZMod 914622451) ^ 7203 = (3 : ZMod 914622451) ^ (3601 + 3601 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 3601 * (3 : ZMod 914622451) ^ 3601) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 52483909 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 914622451) ^ 14406 = 499845640 := by
        calc
          (3 : ZMod 914622451) ^ 14406 = (3 : ZMod 914622451) ^ (7203 + 7203) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 7203 * (3 : ZMod 914622451) ^ 7203 := by rw [pow_add]
          _ = 499845640 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 914622451) ^ 28812 = 389333265 := by
        calc
          (3 : ZMod 914622451) ^ 28812 = (3 : ZMod 914622451) ^ (14406 + 14406) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 14406 * (3 : ZMod 914622451) ^ 14406 := by rw [pow_add]
          _ = 389333265 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 914622451) ^ 57624 = 541238362 := by
        calc
          (3 : ZMod 914622451) ^ 57624 = (3 : ZMod 914622451) ^ (28812 + 28812) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 28812 * (3 : ZMod 914622451) ^ 28812 := by rw [pow_add]
          _ = 541238362 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 914622451) ^ 115249 = 811678993 := by
        calc
          (3 : ZMod 914622451) ^ 115249 = (3 : ZMod 914622451) ^ (57624 + 57624 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 57624 * (3 : ZMod 914622451) ^ 57624) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 811678993 := by rw [factor_4_15]; decide
      have factor_4_17 : (3 : ZMod 914622451) ^ 230499 = 601397022 := by
        calc
          (3 : ZMod 914622451) ^ 230499 = (3 : ZMod 914622451) ^ (115249 + 115249 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 115249 * (3 : ZMod 914622451) ^ 115249) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 601397022 := by rw [factor_4_16]; decide
      have factor_4_18 : (3 : ZMod 914622451) ^ 460999 = 400095153 := by
        calc
          (3 : ZMod 914622451) ^ 460999 = (3 : ZMod 914622451) ^ (230499 + 230499 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 230499 * (3 : ZMod 914622451) ^ 230499) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 400095153 := by rw [factor_4_17]; decide
      have factor_4_19 : (3 : ZMod 914622451) ^ 921998 = 310035001 := by
        calc
          (3 : ZMod 914622451) ^ 921998 = (3 : ZMod 914622451) ^ (460999 + 460999) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 460999 * (3 : ZMod 914622451) ^ 460999 := by rw [pow_add]
          _ = 310035001 := by rw [factor_4_18]; decide
      have factor_4_20 : (3 : ZMod 914622451) ^ 1843996 = 472205797 := by
        calc
          (3 : ZMod 914622451) ^ 1843996 = (3 : ZMod 914622451) ^ (921998 + 921998) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 921998 * (3 : ZMod 914622451) ^ 921998 := by rw [pow_add]
          _ = 472205797 := by rw [factor_4_19]; decide
      have factor_4_21 : (3 : ZMod 914622451) ^ 3687993 = 318308603 := by
        calc
          (3 : ZMod 914622451) ^ 3687993 = (3 : ZMod 914622451) ^ (1843996 + 1843996 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 1843996 * (3 : ZMod 914622451) ^ 1843996) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 318308603 := by rw [factor_4_20]; decide
      have factor_4_22 : (3 : ZMod 914622451) ^ 7375987 = 417982375 := by
        calc
          (3 : ZMod 914622451) ^ 7375987 = (3 : ZMod 914622451) ^ (3687993 + 3687993 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 3687993 * (3 : ZMod 914622451) ^ 3687993) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 417982375 := by rw [factor_4_21]; decide
      have factor_4_23 : (3 : ZMod 914622451) ^ 14751975 = 405476606 := by
        calc
          (3 : ZMod 914622451) ^ 14751975 = (3 : ZMod 914622451) ^ (7375987 + 7375987 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 7375987 * (3 : ZMod 914622451) ^ 7375987) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 405476606 := by rw [factor_4_22]; decide
      have factor_4_24 : (3 : ZMod 914622451) ^ 29503950 = 168899557 := by
        calc
          (3 : ZMod 914622451) ^ 29503950 = (3 : ZMod 914622451) ^ (14751975 + 14751975) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 14751975 * (3 : ZMod 914622451) ^ 14751975 := by rw [pow_add]
          _ = 168899557 := by rw [factor_4_23]; decide
      change (3 : ZMod 914622451) ^ 29503950 ≠ 1
      rw [factor_4_24]
      decide
    ·
      have factor_5_0 : (3 : ZMod 914622451) ^ 1 = 3 := by norm_num
      have factor_5_1 : (3 : ZMod 914622451) ^ 3 = 27 := by
        calc
          (3 : ZMod 914622451) ^ 3 = (3 : ZMod 914622451) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 1 * (3 : ZMod 914622451) ^ 1) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_5_0]; decide
      have factor_5_2 : (3 : ZMod 914622451) ^ 7 = 2187 := by
        calc
          (3 : ZMod 914622451) ^ 7 = (3 : ZMod 914622451) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 3 * (3 : ZMod 914622451) ^ 3) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_5_1]; decide
      have factor_5_3 : (3 : ZMod 914622451) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 914622451) ^ 15 = (3 : ZMod 914622451) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 7 * (3 : ZMod 914622451) ^ 7) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_5_2]; decide
      have factor_5_4 : (3 : ZMod 914622451) ^ 31 = 501827666 := by
        calc
          (3 : ZMod 914622451) ^ 31 = (3 : ZMod 914622451) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 15 * (3 : ZMod 914622451) ^ 15) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 501827666 := by rw [factor_5_3]; decide
      have factor_5_5 : (3 : ZMod 914622451) ^ 63 = 58102055 := by
        calc
          (3 : ZMod 914622451) ^ 63 = (3 : ZMod 914622451) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 31 * (3 : ZMod 914622451) ^ 31) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 58102055 := by rw [factor_5_4]; decide
      have factor_5_6 : (3 : ZMod 914622451) ^ 127 = 582429900 := by
        calc
          (3 : ZMod 914622451) ^ 127 = (3 : ZMod 914622451) ^ (63 + 63 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 63 * (3 : ZMod 914622451) ^ 63) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 582429900 := by rw [factor_5_5]; decide
      have factor_5_7 : (3 : ZMod 914622451) ^ 254 = 492864308 := by
        calc
          (3 : ZMod 914622451) ^ 254 = (3 : ZMod 914622451) ^ (127 + 127) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 127 * (3 : ZMod 914622451) ^ 127 := by rw [pow_add]
          _ = 492864308 := by rw [factor_5_6]; decide
      have factor_5_8 : (3 : ZMod 914622451) ^ 508 = 871911105 := by
        calc
          (3 : ZMod 914622451) ^ 508 = (3 : ZMod 914622451) ^ (254 + 254) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 254 * (3 : ZMod 914622451) ^ 254 := by rw [pow_add]
          _ = 871911105 := by rw [factor_5_7]; decide
      have factor_5_9 : (3 : ZMod 914622451) ^ 1017 = 260958802 := by
        calc
          (3 : ZMod 914622451) ^ 1017 = (3 : ZMod 914622451) ^ (508 + 508 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 508 * (3 : ZMod 914622451) ^ 508) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 260958802 := by rw [factor_5_8]; decide
      have factor_5_10 : (3 : ZMod 914622451) ^ 2034 = 366016353 := by
        calc
          (3 : ZMod 914622451) ^ 2034 = (3 : ZMod 914622451) ^ (1017 + 1017) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 1017 * (3 : ZMod 914622451) ^ 1017 := by rw [pow_add]
          _ = 366016353 := by rw [factor_5_9]; decide
      have factor_5_11 : (3 : ZMod 914622451) ^ 4068 = 794423089 := by
        calc
          (3 : ZMod 914622451) ^ 4068 = (3 : ZMod 914622451) ^ (2034 + 2034) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 2034 * (3 : ZMod 914622451) ^ 2034 := by rw [pow_add]
          _ = 794423089 := by rw [factor_5_10]; decide
      have factor_5_12 : (3 : ZMod 914622451) ^ 8137 = 89650158 := by
        calc
          (3 : ZMod 914622451) ^ 8137 = (3 : ZMod 914622451) ^ (4068 + 4068 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 4068 * (3 : ZMod 914622451) ^ 4068) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 89650158 := by rw [factor_5_11]; decide
      have factor_5_13 : (3 : ZMod 914622451) ^ 16275 = 742124751 := by
        calc
          (3 : ZMod 914622451) ^ 16275 = (3 : ZMod 914622451) ^ (8137 + 8137 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = ((3 : ZMod 914622451) ^ 8137 * (3 : ZMod 914622451) ^ 8137) * (3 : ZMod 914622451) := by rw [pow_succ, pow_add]
          _ = 742124751 := by rw [factor_5_12]; decide
      have factor_5_14 : (3 : ZMod 914622451) ^ 32550 = 405029352 := by
        calc
          (3 : ZMod 914622451) ^ 32550 = (3 : ZMod 914622451) ^ (16275 + 16275) :=
            congrArg (fun n : ℕ => (3 : ZMod 914622451) ^ n) (by norm_num)
          _ = (3 : ZMod 914622451) ^ 16275 * (3 : ZMod 914622451) ^ 16275 := by rw [pow_add]
          _ = 405029352 := by rw [factor_5_13]; decide
      change (3 : ZMod 914622451) ^ 32550 ≠ 1
      rw [factor_5_14]
      decide

#print axioms prime_lucas_914622451

end TotientTailPeriodKiller
end Erdos249257
