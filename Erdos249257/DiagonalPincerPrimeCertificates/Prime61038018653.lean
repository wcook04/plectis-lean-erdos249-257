import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_61038018653 : Nat.Prime 61038018653 := by
  apply lucas_primality 61038018653 (2 : ZMod 61038018653)
  ·
      have fermat_0 : (2 : ZMod 61038018653) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 61038018653) ^ 3 = 8 := by
        calc
          (2 : ZMod 61038018653) ^ 3 = (2 : ZMod 61038018653) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 1 * (2 : ZMod 61038018653) ^ 1) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 61038018653) ^ 7 = 128 := by
        calc
          (2 : ZMod 61038018653) ^ 7 = (2 : ZMod 61038018653) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 3 * (2 : ZMod 61038018653) ^ 3) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 61038018653) ^ 14 = 16384 := by
        calc
          (2 : ZMod 61038018653) ^ 14 = (2 : ZMod 61038018653) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 7 * (2 : ZMod 61038018653) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 61038018653) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 61038018653) ^ 28 = (2 : ZMod 61038018653) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 14 * (2 : ZMod 61038018653) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 61038018653) ^ 56 = 15649389928 := by
        calc
          (2 : ZMod 61038018653) ^ 56 = (2 : ZMod 61038018653) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 28 * (2 : ZMod 61038018653) ^ 28 := by rw [pow_add]
          _ = 15649389928 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 61038018653) ^ 113 = 30133873089 := by
        calc
          (2 : ZMod 61038018653) ^ 113 = (2 : ZMod 61038018653) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 56 * (2 : ZMod 61038018653) ^ 56) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 30133873089 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 61038018653) ^ 227 = 26346134848 := by
        calc
          (2 : ZMod 61038018653) ^ 227 = (2 : ZMod 61038018653) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 113 * (2 : ZMod 61038018653) ^ 113) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 26346134848 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 61038018653) ^ 454 = 55520937642 := by
        calc
          (2 : ZMod 61038018653) ^ 454 = (2 : ZMod 61038018653) ^ (227 + 227) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 227 * (2 : ZMod 61038018653) ^ 227 := by rw [pow_add]
          _ = 55520937642 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 61038018653) ^ 909 = 16360113483 := by
        calc
          (2 : ZMod 61038018653) ^ 909 = (2 : ZMod 61038018653) ^ (454 + 454 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 454 * (2 : ZMod 61038018653) ^ 454) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 16360113483 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 61038018653) ^ 1819 = 40590041015 := by
        calc
          (2 : ZMod 61038018653) ^ 1819 = (2 : ZMod 61038018653) ^ (909 + 909 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 909 * (2 : ZMod 61038018653) ^ 909) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 40590041015 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 61038018653) ^ 3638 = 4987155169 := by
        calc
          (2 : ZMod 61038018653) ^ 3638 = (2 : ZMod 61038018653) ^ (1819 + 1819) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 1819 * (2 : ZMod 61038018653) ^ 1819 := by rw [pow_add]
          _ = 4987155169 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 61038018653) ^ 7276 = 17327840873 := by
        calc
          (2 : ZMod 61038018653) ^ 7276 = (2 : ZMod 61038018653) ^ (3638 + 3638) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 3638 * (2 : ZMod 61038018653) ^ 3638 := by rw [pow_add]
          _ = 17327840873 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 61038018653) ^ 14552 = 12352653801 := by
        calc
          (2 : ZMod 61038018653) ^ 14552 = (2 : ZMod 61038018653) ^ (7276 + 7276) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 7276 * (2 : ZMod 61038018653) ^ 7276 := by rw [pow_add]
          _ = 12352653801 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 61038018653) ^ 29105 = 19310170035 := by
        calc
          (2 : ZMod 61038018653) ^ 29105 = (2 : ZMod 61038018653) ^ (14552 + 14552 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 14552 * (2 : ZMod 61038018653) ^ 14552) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 19310170035 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 61038018653) ^ 58210 = 57709774436 := by
        calc
          (2 : ZMod 61038018653) ^ 58210 = (2 : ZMod 61038018653) ^ (29105 + 29105) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 29105 * (2 : ZMod 61038018653) ^ 29105 := by rw [pow_add]
          _ = 57709774436 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 61038018653) ^ 116420 = 34218363119 := by
        calc
          (2 : ZMod 61038018653) ^ 116420 = (2 : ZMod 61038018653) ^ (58210 + 58210) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 58210 * (2 : ZMod 61038018653) ^ 58210 := by rw [pow_add]
          _ = 34218363119 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 61038018653) ^ 232841 = 4399710309 := by
        calc
          (2 : ZMod 61038018653) ^ 232841 = (2 : ZMod 61038018653) ^ (116420 + 116420 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 116420 * (2 : ZMod 61038018653) ^ 116420) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 4399710309 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 61038018653) ^ 465683 = 56468426709 := by
        calc
          (2 : ZMod 61038018653) ^ 465683 = (2 : ZMod 61038018653) ^ (232841 + 232841 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 232841 * (2 : ZMod 61038018653) ^ 232841) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 56468426709 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 61038018653) ^ 931366 = 19406738874 := by
        calc
          (2 : ZMod 61038018653) ^ 931366 = (2 : ZMod 61038018653) ^ (465683 + 465683) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 465683 * (2 : ZMod 61038018653) ^ 465683 := by rw [pow_add]
          _ = 19406738874 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 61038018653) ^ 1862732 = 35094412499 := by
        calc
          (2 : ZMod 61038018653) ^ 1862732 = (2 : ZMod 61038018653) ^ (931366 + 931366) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 931366 * (2 : ZMod 61038018653) ^ 931366 := by rw [pow_add]
          _ = 35094412499 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 61038018653) ^ 3725465 = 48818189825 := by
        calc
          (2 : ZMod 61038018653) ^ 3725465 = (2 : ZMod 61038018653) ^ (1862732 + 1862732 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 1862732 * (2 : ZMod 61038018653) ^ 1862732) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 48818189825 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 61038018653) ^ 7450930 = 36819818435 := by
        calc
          (2 : ZMod 61038018653) ^ 7450930 = (2 : ZMod 61038018653) ^ (3725465 + 3725465) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 3725465 * (2 : ZMod 61038018653) ^ 3725465 := by rw [pow_add]
          _ = 36819818435 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 61038018653) ^ 14901860 = 31335469915 := by
        calc
          (2 : ZMod 61038018653) ^ 14901860 = (2 : ZMod 61038018653) ^ (7450930 + 7450930) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 7450930 * (2 : ZMod 61038018653) ^ 7450930 := by rw [pow_add]
          _ = 31335469915 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 61038018653) ^ 29803720 = 17343285946 := by
        calc
          (2 : ZMod 61038018653) ^ 29803720 = (2 : ZMod 61038018653) ^ (14901860 + 14901860) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 14901860 * (2 : ZMod 61038018653) ^ 14901860 := by rw [pow_add]
          _ = 17343285946 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 61038018653) ^ 59607440 = 23236072171 := by
        calc
          (2 : ZMod 61038018653) ^ 59607440 = (2 : ZMod 61038018653) ^ (29803720 + 29803720) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 29803720 * (2 : ZMod 61038018653) ^ 29803720 := by rw [pow_add]
          _ = 23236072171 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 61038018653) ^ 119214880 = 50818164915 := by
        calc
          (2 : ZMod 61038018653) ^ 119214880 = (2 : ZMod 61038018653) ^ (59607440 + 59607440) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 59607440 * (2 : ZMod 61038018653) ^ 59607440 := by rw [pow_add]
          _ = 50818164915 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 61038018653) ^ 238429760 = 25479041829 := by
        calc
          (2 : ZMod 61038018653) ^ 238429760 = (2 : ZMod 61038018653) ^ (119214880 + 119214880) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 119214880 * (2 : ZMod 61038018653) ^ 119214880 := by rw [pow_add]
          _ = 25479041829 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 61038018653) ^ 476859520 = 41757017206 := by
        calc
          (2 : ZMod 61038018653) ^ 476859520 = (2 : ZMod 61038018653) ^ (238429760 + 238429760) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 238429760 * (2 : ZMod 61038018653) ^ 238429760 := by rw [pow_add]
          _ = 41757017206 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 61038018653) ^ 953719041 = 3163109291 := by
        calc
          (2 : ZMod 61038018653) ^ 953719041 = (2 : ZMod 61038018653) ^ (476859520 + 476859520 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 476859520 * (2 : ZMod 61038018653) ^ 476859520) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 3163109291 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 61038018653) ^ 1907438082 = 48314779487 := by
        calc
          (2 : ZMod 61038018653) ^ 1907438082 = (2 : ZMod 61038018653) ^ (953719041 + 953719041) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 953719041 * (2 : ZMod 61038018653) ^ 953719041 := by rw [pow_add]
          _ = 48314779487 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 61038018653) ^ 3814876165 = 38285694160 := by
        calc
          (2 : ZMod 61038018653) ^ 3814876165 = (2 : ZMod 61038018653) ^ (1907438082 + 1907438082 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 1907438082 * (2 : ZMod 61038018653) ^ 1907438082) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 38285694160 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 61038018653) ^ 7629752331 = 14917133305 := by
        calc
          (2 : ZMod 61038018653) ^ 7629752331 = (2 : ZMod 61038018653) ^ (3814876165 + 3814876165 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 3814876165 * (2 : ZMod 61038018653) ^ 3814876165) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 14917133305 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 61038018653) ^ 15259504663 = 29834266609 := by
        calc
          (2 : ZMod 61038018653) ^ 15259504663 = (2 : ZMod 61038018653) ^ (7629752331 + 7629752331 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 7629752331 * (2 : ZMod 61038018653) ^ 7629752331) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 29834266609 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 61038018653) ^ 30519009326 = 61038018652 := by
        calc
          (2 : ZMod 61038018653) ^ 30519009326 = (2 : ZMod 61038018653) ^ (15259504663 + 15259504663) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 15259504663 * (2 : ZMod 61038018653) ^ 15259504663 := by rw [pow_add]
          _ = 61038018652 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 61038018653) ^ 61038018652 = 1 := by
        calc
          (2 : ZMod 61038018653) ^ 61038018652 = (2 : ZMod 61038018653) ^ (30519009326 + 30519009326) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 30519009326 * (2 : ZMod 61038018653) ^ 30519009326 := by rw [pow_add]
          _ = 1 := by rw [fermat_34]; decide
      simpa using fermat_35
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 2), (193, 1), (587, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 2), (193, 1), (587, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod = 61038018653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 61038018653) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 61038018653) ^ 3 = 8 := by
        calc
          (2 : ZMod 61038018653) ^ 3 = (2 : ZMod 61038018653) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 1 * (2 : ZMod 61038018653) ^ 1) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 61038018653) ^ 7 = 128 := by
        calc
          (2 : ZMod 61038018653) ^ 7 = (2 : ZMod 61038018653) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 3 * (2 : ZMod 61038018653) ^ 3) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 61038018653) ^ 14 = 16384 := by
        calc
          (2 : ZMod 61038018653) ^ 14 = (2 : ZMod 61038018653) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 7 * (2 : ZMod 61038018653) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 61038018653) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 61038018653) ^ 28 = (2 : ZMod 61038018653) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 14 * (2 : ZMod 61038018653) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 61038018653) ^ 56 = 15649389928 := by
        calc
          (2 : ZMod 61038018653) ^ 56 = (2 : ZMod 61038018653) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 28 * (2 : ZMod 61038018653) ^ 28 := by rw [pow_add]
          _ = 15649389928 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 61038018653) ^ 113 = 30133873089 := by
        calc
          (2 : ZMod 61038018653) ^ 113 = (2 : ZMod 61038018653) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 56 * (2 : ZMod 61038018653) ^ 56) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 30133873089 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 61038018653) ^ 227 = 26346134848 := by
        calc
          (2 : ZMod 61038018653) ^ 227 = (2 : ZMod 61038018653) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 113 * (2 : ZMod 61038018653) ^ 113) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 26346134848 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 61038018653) ^ 454 = 55520937642 := by
        calc
          (2 : ZMod 61038018653) ^ 454 = (2 : ZMod 61038018653) ^ (227 + 227) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 227 * (2 : ZMod 61038018653) ^ 227 := by rw [pow_add]
          _ = 55520937642 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 61038018653) ^ 909 = 16360113483 := by
        calc
          (2 : ZMod 61038018653) ^ 909 = (2 : ZMod 61038018653) ^ (454 + 454 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 454 * (2 : ZMod 61038018653) ^ 454) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 16360113483 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 61038018653) ^ 1819 = 40590041015 := by
        calc
          (2 : ZMod 61038018653) ^ 1819 = (2 : ZMod 61038018653) ^ (909 + 909 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 909 * (2 : ZMod 61038018653) ^ 909) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 40590041015 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 61038018653) ^ 3638 = 4987155169 := by
        calc
          (2 : ZMod 61038018653) ^ 3638 = (2 : ZMod 61038018653) ^ (1819 + 1819) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 1819 * (2 : ZMod 61038018653) ^ 1819 := by rw [pow_add]
          _ = 4987155169 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 61038018653) ^ 7276 = 17327840873 := by
        calc
          (2 : ZMod 61038018653) ^ 7276 = (2 : ZMod 61038018653) ^ (3638 + 3638) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 3638 * (2 : ZMod 61038018653) ^ 3638 := by rw [pow_add]
          _ = 17327840873 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 61038018653) ^ 14552 = 12352653801 := by
        calc
          (2 : ZMod 61038018653) ^ 14552 = (2 : ZMod 61038018653) ^ (7276 + 7276) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 7276 * (2 : ZMod 61038018653) ^ 7276 := by rw [pow_add]
          _ = 12352653801 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 61038018653) ^ 29105 = 19310170035 := by
        calc
          (2 : ZMod 61038018653) ^ 29105 = (2 : ZMod 61038018653) ^ (14552 + 14552 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 14552 * (2 : ZMod 61038018653) ^ 14552) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 19310170035 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 61038018653) ^ 58210 = 57709774436 := by
        calc
          (2 : ZMod 61038018653) ^ 58210 = (2 : ZMod 61038018653) ^ (29105 + 29105) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 29105 * (2 : ZMod 61038018653) ^ 29105 := by rw [pow_add]
          _ = 57709774436 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 61038018653) ^ 116420 = 34218363119 := by
        calc
          (2 : ZMod 61038018653) ^ 116420 = (2 : ZMod 61038018653) ^ (58210 + 58210) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 58210 * (2 : ZMod 61038018653) ^ 58210 := by rw [pow_add]
          _ = 34218363119 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 61038018653) ^ 232841 = 4399710309 := by
        calc
          (2 : ZMod 61038018653) ^ 232841 = (2 : ZMod 61038018653) ^ (116420 + 116420 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 116420 * (2 : ZMod 61038018653) ^ 116420) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 4399710309 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 61038018653) ^ 465683 = 56468426709 := by
        calc
          (2 : ZMod 61038018653) ^ 465683 = (2 : ZMod 61038018653) ^ (232841 + 232841 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 232841 * (2 : ZMod 61038018653) ^ 232841) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 56468426709 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 61038018653) ^ 931366 = 19406738874 := by
        calc
          (2 : ZMod 61038018653) ^ 931366 = (2 : ZMod 61038018653) ^ (465683 + 465683) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 465683 * (2 : ZMod 61038018653) ^ 465683 := by rw [pow_add]
          _ = 19406738874 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 61038018653) ^ 1862732 = 35094412499 := by
        calc
          (2 : ZMod 61038018653) ^ 1862732 = (2 : ZMod 61038018653) ^ (931366 + 931366) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 931366 * (2 : ZMod 61038018653) ^ 931366 := by rw [pow_add]
          _ = 35094412499 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 61038018653) ^ 3725465 = 48818189825 := by
        calc
          (2 : ZMod 61038018653) ^ 3725465 = (2 : ZMod 61038018653) ^ (1862732 + 1862732 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 1862732 * (2 : ZMod 61038018653) ^ 1862732) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 48818189825 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 61038018653) ^ 7450930 = 36819818435 := by
        calc
          (2 : ZMod 61038018653) ^ 7450930 = (2 : ZMod 61038018653) ^ (3725465 + 3725465) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 3725465 * (2 : ZMod 61038018653) ^ 3725465 := by rw [pow_add]
          _ = 36819818435 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 61038018653) ^ 14901860 = 31335469915 := by
        calc
          (2 : ZMod 61038018653) ^ 14901860 = (2 : ZMod 61038018653) ^ (7450930 + 7450930) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 7450930 * (2 : ZMod 61038018653) ^ 7450930 := by rw [pow_add]
          _ = 31335469915 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 61038018653) ^ 29803720 = 17343285946 := by
        calc
          (2 : ZMod 61038018653) ^ 29803720 = (2 : ZMod 61038018653) ^ (14901860 + 14901860) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 14901860 * (2 : ZMod 61038018653) ^ 14901860 := by rw [pow_add]
          _ = 17343285946 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 61038018653) ^ 59607440 = 23236072171 := by
        calc
          (2 : ZMod 61038018653) ^ 59607440 = (2 : ZMod 61038018653) ^ (29803720 + 29803720) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 29803720 * (2 : ZMod 61038018653) ^ 29803720 := by rw [pow_add]
          _ = 23236072171 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 61038018653) ^ 119214880 = 50818164915 := by
        calc
          (2 : ZMod 61038018653) ^ 119214880 = (2 : ZMod 61038018653) ^ (59607440 + 59607440) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 59607440 * (2 : ZMod 61038018653) ^ 59607440 := by rw [pow_add]
          _ = 50818164915 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 61038018653) ^ 238429760 = 25479041829 := by
        calc
          (2 : ZMod 61038018653) ^ 238429760 = (2 : ZMod 61038018653) ^ (119214880 + 119214880) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 119214880 * (2 : ZMod 61038018653) ^ 119214880 := by rw [pow_add]
          _ = 25479041829 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 61038018653) ^ 476859520 = 41757017206 := by
        calc
          (2 : ZMod 61038018653) ^ 476859520 = (2 : ZMod 61038018653) ^ (238429760 + 238429760) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 238429760 * (2 : ZMod 61038018653) ^ 238429760 := by rw [pow_add]
          _ = 41757017206 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 61038018653) ^ 953719041 = 3163109291 := by
        calc
          (2 : ZMod 61038018653) ^ 953719041 = (2 : ZMod 61038018653) ^ (476859520 + 476859520 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 476859520 * (2 : ZMod 61038018653) ^ 476859520) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 3163109291 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 61038018653) ^ 1907438082 = 48314779487 := by
        calc
          (2 : ZMod 61038018653) ^ 1907438082 = (2 : ZMod 61038018653) ^ (953719041 + 953719041) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 953719041 * (2 : ZMod 61038018653) ^ 953719041 := by rw [pow_add]
          _ = 48314779487 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 61038018653) ^ 3814876165 = 38285694160 := by
        calc
          (2 : ZMod 61038018653) ^ 3814876165 = (2 : ZMod 61038018653) ^ (1907438082 + 1907438082 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 1907438082 * (2 : ZMod 61038018653) ^ 1907438082) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 38285694160 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 61038018653) ^ 7629752331 = 14917133305 := by
        calc
          (2 : ZMod 61038018653) ^ 7629752331 = (2 : ZMod 61038018653) ^ (3814876165 + 3814876165 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 3814876165 * (2 : ZMod 61038018653) ^ 3814876165) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 14917133305 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 61038018653) ^ 15259504663 = 29834266609 := by
        calc
          (2 : ZMod 61038018653) ^ 15259504663 = (2 : ZMod 61038018653) ^ (7629752331 + 7629752331 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 7629752331 * (2 : ZMod 61038018653) ^ 7629752331) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 29834266609 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 61038018653) ^ 30519009326 = 61038018652 := by
        calc
          (2 : ZMod 61038018653) ^ 30519009326 = (2 : ZMod 61038018653) ^ (15259504663 + 15259504663) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 15259504663 * (2 : ZMod 61038018653) ^ 15259504663 := by rw [pow_add]
          _ = 61038018652 := by rw [factor_0_33]; decide
      change (2 : ZMod 61038018653) ^ 30519009326 ≠ 1
      rw [factor_0_34]
      decide
    ·
      have factor_1_0 : (2 : ZMod 61038018653) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 61038018653) ^ 2 = 4 := by
        calc
          (2 : ZMod 61038018653) ^ 2 = (2 : ZMod 61038018653) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 1 * (2 : ZMod 61038018653) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 61038018653) ^ 4 = 16 := by
        calc
          (2 : ZMod 61038018653) ^ 4 = (2 : ZMod 61038018653) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 2 * (2 : ZMod 61038018653) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 61038018653) ^ 8 = 256 := by
        calc
          (2 : ZMod 61038018653) ^ 8 = (2 : ZMod 61038018653) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 4 * (2 : ZMod 61038018653) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 61038018653) ^ 17 = 131072 := by
        calc
          (2 : ZMod 61038018653) ^ 17 = (2 : ZMod 61038018653) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 8 * (2 : ZMod 61038018653) ^ 8) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 61038018653) ^ 34 = 17179869184 := by
        calc
          (2 : ZMod 61038018653) ^ 34 = (2 : ZMod 61038018653) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 17 * (2 : ZMod 61038018653) ^ 17 := by rw [pow_add]
          _ = 17179869184 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 61038018653) ^ 69 = 19963118876 := by
        calc
          (2 : ZMod 61038018653) ^ 69 = (2 : ZMod 61038018653) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 34 * (2 : ZMod 61038018653) ^ 34) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 19963118876 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 61038018653) ^ 139 = 5310604426 := by
        calc
          (2 : ZMod 61038018653) ^ 139 = (2 : ZMod 61038018653) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 69 * (2 : ZMod 61038018653) ^ 69) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 5310604426 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 61038018653) ^ 279 = 46715670104 := by
        calc
          (2 : ZMod 61038018653) ^ 279 = (2 : ZMod 61038018653) ^ (139 + 139 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 139 * (2 : ZMod 61038018653) ^ 139) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 46715670104 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 61038018653) ^ 559 = 19066382623 := by
        calc
          (2 : ZMod 61038018653) ^ 559 = (2 : ZMod 61038018653) ^ (279 + 279 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 279 * (2 : ZMod 61038018653) ^ 279) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 19066382623 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 61038018653) ^ 1119 = 42677803790 := by
        calc
          (2 : ZMod 61038018653) ^ 1119 = (2 : ZMod 61038018653) ^ (559 + 559 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 559 * (2 : ZMod 61038018653) ^ 559) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 42677803790 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 61038018653) ^ 2238 = 32517953112 := by
        calc
          (2 : ZMod 61038018653) ^ 2238 = (2 : ZMod 61038018653) ^ (1119 + 1119) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 1119 * (2 : ZMod 61038018653) ^ 1119 := by rw [pow_add]
          _ = 32517953112 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 61038018653) ^ 4477 = 44179312579 := by
        calc
          (2 : ZMod 61038018653) ^ 4477 = (2 : ZMod 61038018653) ^ (2238 + 2238 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 2238 * (2 : ZMod 61038018653) ^ 2238) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 44179312579 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 61038018653) ^ 8955 = 10632666677 := by
        calc
          (2 : ZMod 61038018653) ^ 8955 = (2 : ZMod 61038018653) ^ (4477 + 4477 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 4477 * (2 : ZMod 61038018653) ^ 4477) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 10632666677 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 61038018653) ^ 17910 = 18870567839 := by
        calc
          (2 : ZMod 61038018653) ^ 17910 = (2 : ZMod 61038018653) ^ (8955 + 8955) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 8955 * (2 : ZMod 61038018653) ^ 8955 := by rw [pow_add]
          _ = 18870567839 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 61038018653) ^ 35821 = 48032112672 := by
        calc
          (2 : ZMod 61038018653) ^ 35821 = (2 : ZMod 61038018653) ^ (17910 + 17910 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 17910 * (2 : ZMod 61038018653) ^ 17910) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 48032112672 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 61038018653) ^ 71643 = 44951766574 := by
        calc
          (2 : ZMod 61038018653) ^ 71643 = (2 : ZMod 61038018653) ^ (35821 + 35821 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 35821 * (2 : ZMod 61038018653) ^ 35821) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 44951766574 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 61038018653) ^ 143287 = 59644668400 := by
        calc
          (2 : ZMod 61038018653) ^ 143287 = (2 : ZMod 61038018653) ^ (71643 + 71643 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 71643 * (2 : ZMod 61038018653) ^ 71643) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 59644668400 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 61038018653) ^ 286574 = 21310662467 := by
        calc
          (2 : ZMod 61038018653) ^ 286574 = (2 : ZMod 61038018653) ^ (143287 + 143287) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 143287 * (2 : ZMod 61038018653) ^ 143287 := by rw [pow_add]
          _ = 21310662467 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 61038018653) ^ 573148 = 21371542651 := by
        calc
          (2 : ZMod 61038018653) ^ 573148 = (2 : ZMod 61038018653) ^ (286574 + 286574) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 286574 * (2 : ZMod 61038018653) ^ 286574 := by rw [pow_add]
          _ = 21371542651 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 61038018653) ^ 1146296 = 2620667455 := by
        calc
          (2 : ZMod 61038018653) ^ 1146296 = (2 : ZMod 61038018653) ^ (573148 + 573148) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 573148 * (2 : ZMod 61038018653) ^ 573148 := by rw [pow_add]
          _ = 2620667455 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 61038018653) ^ 2292593 = 1232322625 := by
        calc
          (2 : ZMod 61038018653) ^ 2292593 = (2 : ZMod 61038018653) ^ (1146296 + 1146296 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 1146296 * (2 : ZMod 61038018653) ^ 1146296) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 1232322625 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 61038018653) ^ 4585187 = 29554698175 := by
        calc
          (2 : ZMod 61038018653) ^ 4585187 = (2 : ZMod 61038018653) ^ (2292593 + 2292593 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 2292593 * (2 : ZMod 61038018653) ^ 2292593) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 29554698175 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 61038018653) ^ 9170375 = 35673747072 := by
        calc
          (2 : ZMod 61038018653) ^ 9170375 = (2 : ZMod 61038018653) ^ (4585187 + 4585187 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 4585187 * (2 : ZMod 61038018653) ^ 4585187) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 35673747072 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 61038018653) ^ 18340750 = 2304275624 := by
        calc
          (2 : ZMod 61038018653) ^ 18340750 = (2 : ZMod 61038018653) ^ (9170375 + 9170375) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 9170375 * (2 : ZMod 61038018653) ^ 9170375 := by rw [pow_add]
          _ = 2304275624 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 61038018653) ^ 36681501 = 35311028444 := by
        calc
          (2 : ZMod 61038018653) ^ 36681501 = (2 : ZMod 61038018653) ^ (18340750 + 18340750 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 18340750 * (2 : ZMod 61038018653) ^ 18340750) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 35311028444 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 61038018653) ^ 73363003 = 53257437936 := by
        calc
          (2 : ZMod 61038018653) ^ 73363003 = (2 : ZMod 61038018653) ^ (36681501 + 36681501 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 36681501 * (2 : ZMod 61038018653) ^ 36681501) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 53257437936 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 61038018653) ^ 146726006 = 14694415610 := by
        calc
          (2 : ZMod 61038018653) ^ 146726006 = (2 : ZMod 61038018653) ^ (73363003 + 73363003) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 73363003 * (2 : ZMod 61038018653) ^ 73363003 := by rw [pow_add]
          _ = 14694415610 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 61038018653) ^ 293452012 = 5694836175 := by
        calc
          (2 : ZMod 61038018653) ^ 293452012 = (2 : ZMod 61038018653) ^ (146726006 + 146726006) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 146726006 * (2 : ZMod 61038018653) ^ 146726006 := by rw [pow_add]
          _ = 5694836175 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 61038018653) ^ 586904025 = 7893036498 := by
        calc
          (2 : ZMod 61038018653) ^ 586904025 = (2 : ZMod 61038018653) ^ (293452012 + 293452012 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 293452012 * (2 : ZMod 61038018653) ^ 293452012) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 7893036498 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 61038018653) ^ 1173808051 = 54608883691 := by
        calc
          (2 : ZMod 61038018653) ^ 1173808051 = (2 : ZMod 61038018653) ^ (586904025 + 586904025 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 586904025 * (2 : ZMod 61038018653) ^ 586904025) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 54608883691 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 61038018653) ^ 2347616102 = 43502663495 := by
        calc
          (2 : ZMod 61038018653) ^ 2347616102 = (2 : ZMod 61038018653) ^ (1173808051 + 1173808051) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 1173808051 * (2 : ZMod 61038018653) ^ 1173808051 := by rw [pow_add]
          _ = 43502663495 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 61038018653) ^ 4695232204 = 27851177553 := by
        calc
          (2 : ZMod 61038018653) ^ 4695232204 = (2 : ZMod 61038018653) ^ (2347616102 + 2347616102) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 2347616102 * (2 : ZMod 61038018653) ^ 2347616102 := by rw [pow_add]
          _ = 27851177553 := by rw [factor_1_31]; decide
      change (2 : ZMod 61038018653) ^ 4695232204 ≠ 1
      rw [factor_1_32]
      decide
    ·
      have factor_2_0 : (2 : ZMod 61038018653) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 61038018653) ^ 2 = 4 := by
        calc
          (2 : ZMod 61038018653) ^ 2 = (2 : ZMod 61038018653) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 1 * (2 : ZMod 61038018653) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 61038018653) ^ 4 = 16 := by
        calc
          (2 : ZMod 61038018653) ^ 4 = (2 : ZMod 61038018653) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 2 * (2 : ZMod 61038018653) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 61038018653) ^ 9 = 512 := by
        calc
          (2 : ZMod 61038018653) ^ 9 = (2 : ZMod 61038018653) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 4 * (2 : ZMod 61038018653) ^ 4) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 61038018653) ^ 18 = 262144 := by
        calc
          (2 : ZMod 61038018653) ^ 18 = (2 : ZMod 61038018653) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 9 * (2 : ZMod 61038018653) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 61038018653) ^ 37 = 15362916166 := by
        calc
          (2 : ZMod 61038018653) ^ 37 = (2 : ZMod 61038018653) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 18 * (2 : ZMod 61038018653) ^ 18) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 15362916166 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 61038018653) ^ 75 = 56879235004 := by
        calc
          (2 : ZMod 61038018653) ^ 75 = (2 : ZMod 61038018653) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 37 * (2 : ZMod 61038018653) ^ 37) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 56879235004 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 61038018653) ^ 150 = 11350544214 := by
        calc
          (2 : ZMod 61038018653) ^ 150 = (2 : ZMod 61038018653) ^ (75 + 75) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 75 * (2 : ZMod 61038018653) ^ 75 := by rw [pow_add]
          _ = 11350544214 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 61038018653) ^ 301 = 52351425991 := by
        calc
          (2 : ZMod 61038018653) ^ 301 = (2 : ZMod 61038018653) ^ (150 + 150 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 150 * (2 : ZMod 61038018653) ^ 150) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 52351425991 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 61038018653) ^ 603 = 16806293477 := by
        calc
          (2 : ZMod 61038018653) ^ 603 = (2 : ZMod 61038018653) ^ (301 + 301 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 301 * (2 : ZMod 61038018653) ^ 301) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 16806293477 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 61038018653) ^ 1206 = 56015337184 := by
        calc
          (2 : ZMod 61038018653) ^ 1206 = (2 : ZMod 61038018653) ^ (603 + 603) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 603 * (2 : ZMod 61038018653) ^ 603 := by rw [pow_add]
          _ = 56015337184 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 61038018653) ^ 2412 = 35928531380 := by
        calc
          (2 : ZMod 61038018653) ^ 2412 = (2 : ZMod 61038018653) ^ (1206 + 1206) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 1206 * (2 : ZMod 61038018653) ^ 1206 := by rw [pow_add]
          _ = 35928531380 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 61038018653) ^ 4825 = 32802119746 := by
        calc
          (2 : ZMod 61038018653) ^ 4825 = (2 : ZMod 61038018653) ^ (2412 + 2412 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 2412 * (2 : ZMod 61038018653) ^ 2412) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 32802119746 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 61038018653) ^ 9651 = 2606295955 := by
        calc
          (2 : ZMod 61038018653) ^ 9651 = (2 : ZMod 61038018653) ^ (4825 + 4825 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 4825 * (2 : ZMod 61038018653) ^ 4825) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 2606295955 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 61038018653) ^ 19302 = 32930546780 := by
        calc
          (2 : ZMod 61038018653) ^ 19302 = (2 : ZMod 61038018653) ^ (9651 + 9651) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 9651 * (2 : ZMod 61038018653) ^ 9651 := by rw [pow_add]
          _ = 32930546780 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 61038018653) ^ 38605 = 21365693781 := by
        calc
          (2 : ZMod 61038018653) ^ 38605 = (2 : ZMod 61038018653) ^ (19302 + 19302 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 19302 * (2 : ZMod 61038018653) ^ 19302) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 21365693781 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 61038018653) ^ 77211 = 9169809692 := by
        calc
          (2 : ZMod 61038018653) ^ 77211 = (2 : ZMod 61038018653) ^ (38605 + 38605 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 38605 * (2 : ZMod 61038018653) ^ 38605) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 9169809692 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 61038018653) ^ 154423 = 29745824840 := by
        calc
          (2 : ZMod 61038018653) ^ 154423 = (2 : ZMod 61038018653) ^ (77211 + 77211 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 77211 * (2 : ZMod 61038018653) ^ 77211) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 29745824840 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 61038018653) ^ 308846 = 6312875782 := by
        calc
          (2 : ZMod 61038018653) ^ 308846 = (2 : ZMod 61038018653) ^ (154423 + 154423) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 154423 * (2 : ZMod 61038018653) ^ 154423 := by rw [pow_add]
          _ = 6312875782 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 61038018653) ^ 617693 = 11910278776 := by
        calc
          (2 : ZMod 61038018653) ^ 617693 = (2 : ZMod 61038018653) ^ (308846 + 308846 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 308846 * (2 : ZMod 61038018653) ^ 308846) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 11910278776 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 61038018653) ^ 1235387 = 40656328443 := by
        calc
          (2 : ZMod 61038018653) ^ 1235387 = (2 : ZMod 61038018653) ^ (617693 + 617693 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 617693 * (2 : ZMod 61038018653) ^ 617693) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 40656328443 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 61038018653) ^ 2470774 = 19637721014 := by
        calc
          (2 : ZMod 61038018653) ^ 2470774 = (2 : ZMod 61038018653) ^ (1235387 + 1235387) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 1235387 * (2 : ZMod 61038018653) ^ 1235387 := by rw [pow_add]
          _ = 19637721014 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 61038018653) ^ 4941549 = 23168423071 := by
        calc
          (2 : ZMod 61038018653) ^ 4941549 = (2 : ZMod 61038018653) ^ (2470774 + 2470774 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 2470774 * (2 : ZMod 61038018653) ^ 2470774) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 23168423071 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 61038018653) ^ 9883098 = 105676433 := by
        calc
          (2 : ZMod 61038018653) ^ 9883098 = (2 : ZMod 61038018653) ^ (4941549 + 4941549) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 4941549 * (2 : ZMod 61038018653) ^ 4941549 := by rw [pow_add]
          _ = 105676433 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 61038018653) ^ 19766197 = 46235719871 := by
        calc
          (2 : ZMod 61038018653) ^ 19766197 = (2 : ZMod 61038018653) ^ (9883098 + 9883098 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 9883098 * (2 : ZMod 61038018653) ^ 9883098) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 46235719871 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 61038018653) ^ 39532395 = 43246390468 := by
        calc
          (2 : ZMod 61038018653) ^ 39532395 = (2 : ZMod 61038018653) ^ (19766197 + 19766197 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 19766197 * (2 : ZMod 61038018653) ^ 19766197) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 43246390468 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 61038018653) ^ 79064791 = 34932217854 := by
        calc
          (2 : ZMod 61038018653) ^ 79064791 = (2 : ZMod 61038018653) ^ (39532395 + 39532395 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 39532395 * (2 : ZMod 61038018653) ^ 39532395) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 34932217854 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 61038018653) ^ 158129582 = 43954206809 := by
        calc
          (2 : ZMod 61038018653) ^ 158129582 = (2 : ZMod 61038018653) ^ (79064791 + 79064791) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 79064791 * (2 : ZMod 61038018653) ^ 79064791 := by rw [pow_add]
          _ = 43954206809 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 61038018653) ^ 316259164 = 15924208381 := by
        calc
          (2 : ZMod 61038018653) ^ 316259164 = (2 : ZMod 61038018653) ^ (158129582 + 158129582) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 158129582 * (2 : ZMod 61038018653) ^ 158129582 := by rw [pow_add]
          _ = 15924208381 := by rw [factor_2_27]; decide
      change (2 : ZMod 61038018653) ^ 316259164 ≠ 1
      rw [factor_2_28]
      decide
    ·
      have factor_3_0 : (2 : ZMod 61038018653) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 61038018653) ^ 3 = 8 := by
        calc
          (2 : ZMod 61038018653) ^ 3 = (2 : ZMod 61038018653) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 1 * (2 : ZMod 61038018653) ^ 1) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 61038018653) ^ 6 = 64 := by
        calc
          (2 : ZMod 61038018653) ^ 6 = (2 : ZMod 61038018653) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 3 * (2 : ZMod 61038018653) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 61038018653) ^ 12 = 4096 := by
        calc
          (2 : ZMod 61038018653) ^ 12 = (2 : ZMod 61038018653) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 6 * (2 : ZMod 61038018653) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 61038018653) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 61038018653) ^ 24 = (2 : ZMod 61038018653) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 12 * (2 : ZMod 61038018653) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 61038018653) ^ 49 = 57345403346 := by
        calc
          (2 : ZMod 61038018653) ^ 49 = (2 : ZMod 61038018653) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 24 * (2 : ZMod 61038018653) ^ 24) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 57345403346 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 61038018653) ^ 99 = 52735796381 := by
        calc
          (2 : ZMod 61038018653) ^ 99 = (2 : ZMod 61038018653) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 49 * (2 : ZMod 61038018653) ^ 49) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 52735796381 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 61038018653) ^ 198 = 6126578185 := by
        calc
          (2 : ZMod 61038018653) ^ 198 = (2 : ZMod 61038018653) ^ (99 + 99) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 99 * (2 : ZMod 61038018653) ^ 99 := by rw [pow_add]
          _ = 6126578185 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 61038018653) ^ 396 = 27306413528 := by
        calc
          (2 : ZMod 61038018653) ^ 396 = (2 : ZMod 61038018653) ^ (198 + 198) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 198 * (2 : ZMod 61038018653) ^ 198 := by rw [pow_add]
          _ = 27306413528 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 61038018653) ^ 793 = 4396895461 := by
        calc
          (2 : ZMod 61038018653) ^ 793 = (2 : ZMod 61038018653) ^ (396 + 396 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 396 * (2 : ZMod 61038018653) ^ 396) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 4396895461 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 61038018653) ^ 1586 = 60507656272 := by
        calc
          (2 : ZMod 61038018653) ^ 1586 = (2 : ZMod 61038018653) ^ (793 + 793) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 793 * (2 : ZMod 61038018653) ^ 793 := by rw [pow_add]
          _ = 60507656272 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 61038018653) ^ 3173 = 14221059752 := by
        calc
          (2 : ZMod 61038018653) ^ 3173 = (2 : ZMod 61038018653) ^ (1586 + 1586 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 1586 * (2 : ZMod 61038018653) ^ 1586) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 14221059752 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 61038018653) ^ 6346 = 13900299924 := by
        calc
          (2 : ZMod 61038018653) ^ 6346 = (2 : ZMod 61038018653) ^ (3173 + 3173) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 3173 * (2 : ZMod 61038018653) ^ 3173 := by rw [pow_add]
          _ = 13900299924 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 61038018653) ^ 12693 = 14375987894 := by
        calc
          (2 : ZMod 61038018653) ^ 12693 = (2 : ZMod 61038018653) ^ (6346 + 6346 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 6346 * (2 : ZMod 61038018653) ^ 6346) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 14375987894 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 61038018653) ^ 25386 = 39763454250 := by
        calc
          (2 : ZMod 61038018653) ^ 25386 = (2 : ZMod 61038018653) ^ (12693 + 12693) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 12693 * (2 : ZMod 61038018653) ^ 12693 := by rw [pow_add]
          _ = 39763454250 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 61038018653) ^ 50772 = 46242108908 := by
        calc
          (2 : ZMod 61038018653) ^ 50772 = (2 : ZMod 61038018653) ^ (25386 + 25386) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 25386 * (2 : ZMod 61038018653) ^ 25386 := by rw [pow_add]
          _ = 46242108908 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 61038018653) ^ 101545 = 49297996433 := by
        calc
          (2 : ZMod 61038018653) ^ 101545 = (2 : ZMod 61038018653) ^ (50772 + 50772 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 50772 * (2 : ZMod 61038018653) ^ 50772) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 49297996433 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 61038018653) ^ 203091 = 32978246112 := by
        calc
          (2 : ZMod 61038018653) ^ 203091 = (2 : ZMod 61038018653) ^ (101545 + 101545 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 101545 * (2 : ZMod 61038018653) ^ 101545) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 32978246112 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 61038018653) ^ 406183 = 31051844317 := by
        calc
          (2 : ZMod 61038018653) ^ 406183 = (2 : ZMod 61038018653) ^ (203091 + 203091 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 203091 * (2 : ZMod 61038018653) ^ 203091) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 31051844317 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 61038018653) ^ 812367 = 34693610170 := by
        calc
          (2 : ZMod 61038018653) ^ 812367 = (2 : ZMod 61038018653) ^ (406183 + 406183 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 406183 * (2 : ZMod 61038018653) ^ 406183) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 34693610170 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 61038018653) ^ 1624734 = 12703303484 := by
        calc
          (2 : ZMod 61038018653) ^ 1624734 = (2 : ZMod 61038018653) ^ (812367 + 812367) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 812367 * (2 : ZMod 61038018653) ^ 812367 := by rw [pow_add]
          _ = 12703303484 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 61038018653) ^ 3249468 = 25686452438 := by
        calc
          (2 : ZMod 61038018653) ^ 3249468 = (2 : ZMod 61038018653) ^ (1624734 + 1624734) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 1624734 * (2 : ZMod 61038018653) ^ 1624734 := by rw [pow_add]
          _ = 25686452438 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 61038018653) ^ 6498937 = 48213780910 := by
        calc
          (2 : ZMod 61038018653) ^ 6498937 = (2 : ZMod 61038018653) ^ (3249468 + 3249468 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 3249468 * (2 : ZMod 61038018653) ^ 3249468) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 48213780910 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 61038018653) ^ 12997874 = 13210346939 := by
        calc
          (2 : ZMod 61038018653) ^ 12997874 = (2 : ZMod 61038018653) ^ (6498937 + 6498937) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 6498937 * (2 : ZMod 61038018653) ^ 6498937 := by rw [pow_add]
          _ = 13210346939 := by rw [factor_3_22]; decide
      have factor_3_24 : (2 : ZMod 61038018653) ^ 25995749 = 20752439475 := by
        calc
          (2 : ZMod 61038018653) ^ 25995749 = (2 : ZMod 61038018653) ^ (12997874 + 12997874 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 12997874 * (2 : ZMod 61038018653) ^ 12997874) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 20752439475 := by rw [factor_3_23]; decide
      have factor_3_25 : (2 : ZMod 61038018653) ^ 51991498 = 36419735455 := by
        calc
          (2 : ZMod 61038018653) ^ 51991498 = (2 : ZMod 61038018653) ^ (25995749 + 25995749) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 25995749 * (2 : ZMod 61038018653) ^ 25995749 := by rw [pow_add]
          _ = 36419735455 := by rw [factor_3_24]; decide
      have factor_3_26 : (2 : ZMod 61038018653) ^ 103982996 = 23071108462 := by
        calc
          (2 : ZMod 61038018653) ^ 103982996 = (2 : ZMod 61038018653) ^ (51991498 + 51991498) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 51991498 * (2 : ZMod 61038018653) ^ 51991498 := by rw [pow_add]
          _ = 23071108462 := by rw [factor_3_25]; decide
      change (2 : ZMod 61038018653) ^ 103982996 ≠ 1
      rw [factor_3_26]
      decide
    ·
      have factor_4_0 : (2 : ZMod 61038018653) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 61038018653) ^ 2 = 4 := by
        calc
          (2 : ZMod 61038018653) ^ 2 = (2 : ZMod 61038018653) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 1 * (2 : ZMod 61038018653) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 61038018653) ^ 4 = 16 := by
        calc
          (2 : ZMod 61038018653) ^ 4 = (2 : ZMod 61038018653) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 2 * (2 : ZMod 61038018653) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 61038018653) ^ 9 = 512 := by
        calc
          (2 : ZMod 61038018653) ^ 9 = (2 : ZMod 61038018653) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 4 * (2 : ZMod 61038018653) ^ 4) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 61038018653) ^ 18 = 262144 := by
        calc
          (2 : ZMod 61038018653) ^ 18 = (2 : ZMod 61038018653) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 9 * (2 : ZMod 61038018653) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 61038018653) ^ 36 = 7681458083 := by
        calc
          (2 : ZMod 61038018653) ^ 36 = (2 : ZMod 61038018653) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 18 * (2 : ZMod 61038018653) ^ 18 := by rw [pow_add]
          _ = 7681458083 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 61038018653) ^ 73 = 14219808751 := by
        calc
          (2 : ZMod 61038018653) ^ 73 = (2 : ZMod 61038018653) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 36 * (2 : ZMod 61038018653) ^ 36) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 14219808751 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 61038018653) ^ 146 = 8339161345 := by
        calc
          (2 : ZMod 61038018653) ^ 146 = (2 : ZMod 61038018653) ^ (73 + 73) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 73 * (2 : ZMod 61038018653) ^ 73 := by rw [pow_add]
          _ = 8339161345 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 61038018653) ^ 292 = 47430556311 := by
        calc
          (2 : ZMod 61038018653) ^ 292 = (2 : ZMod 61038018653) ^ (146 + 146) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 146 * (2 : ZMod 61038018653) ^ 146 := by rw [pow_add]
          _ = 47430556311 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 61038018653) ^ 584 = 8906571097 := by
        calc
          (2 : ZMod 61038018653) ^ 584 = (2 : ZMod 61038018653) ^ (292 + 292) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 292 * (2 : ZMod 61038018653) ^ 292 := by rw [pow_add]
          _ = 8906571097 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 61038018653) ^ 1168 = 58985911129 := by
        calc
          (2 : ZMod 61038018653) ^ 1168 = (2 : ZMod 61038018653) ^ (584 + 584) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 584 * (2 : ZMod 61038018653) ^ 584 := by rw [pow_add]
          _ = 58985911129 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 61038018653) ^ 2337 = 44486983091 := by
        calc
          (2 : ZMod 61038018653) ^ 2337 = (2 : ZMod 61038018653) ^ (1168 + 1168 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 1168 * (2 : ZMod 61038018653) ^ 1168) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 44486983091 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 61038018653) ^ 4674 = 33965879050 := by
        calc
          (2 : ZMod 61038018653) ^ 4674 = (2 : ZMod 61038018653) ^ (2337 + 2337) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 2337 * (2 : ZMod 61038018653) ^ 2337 := by rw [pow_add]
          _ = 33965879050 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 61038018653) ^ 9348 = 16587633894 := by
        calc
          (2 : ZMod 61038018653) ^ 9348 = (2 : ZMod 61038018653) ^ (4674 + 4674) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 4674 * (2 : ZMod 61038018653) ^ 4674 := by rw [pow_add]
          _ = 16587633894 := by rw [factor_4_12]; decide
      have factor_4_14 : (2 : ZMod 61038018653) ^ 18697 = 2930715812 := by
        calc
          (2 : ZMod 61038018653) ^ 18697 = (2 : ZMod 61038018653) ^ (9348 + 9348 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 9348 * (2 : ZMod 61038018653) ^ 9348) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 2930715812 := by rw [factor_4_13]; decide
      have factor_4_15 : (2 : ZMod 61038018653) ^ 37394 = 59780100189 := by
        calc
          (2 : ZMod 61038018653) ^ 37394 = (2 : ZMod 61038018653) ^ (18697 + 18697) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 18697 * (2 : ZMod 61038018653) ^ 18697 := by rw [pow_add]
          _ = 59780100189 := by rw [factor_4_14]; decide
      have factor_4_16 : (2 : ZMod 61038018653) ^ 74789 = 38503842733 := by
        calc
          (2 : ZMod 61038018653) ^ 74789 = (2 : ZMod 61038018653) ^ (37394 + 37394 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 37394 * (2 : ZMod 61038018653) ^ 37394) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 38503842733 := by rw [factor_4_15]; decide
      have factor_4_17 : (2 : ZMod 61038018653) ^ 149579 = 45268833111 := by
        calc
          (2 : ZMod 61038018653) ^ 149579 = (2 : ZMod 61038018653) ^ (74789 + 74789 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 74789 * (2 : ZMod 61038018653) ^ 74789) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 45268833111 := by rw [factor_4_16]; decide
      have factor_4_18 : (2 : ZMod 61038018653) ^ 299159 = 13433623963 := by
        calc
          (2 : ZMod 61038018653) ^ 299159 = (2 : ZMod 61038018653) ^ (149579 + 149579 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 149579 * (2 : ZMod 61038018653) ^ 149579) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 13433623963 := by rw [factor_4_17]; decide
      have factor_4_19 : (2 : ZMod 61038018653) ^ 598318 = 10697387587 := by
        calc
          (2 : ZMod 61038018653) ^ 598318 = (2 : ZMod 61038018653) ^ (299159 + 299159) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 299159 * (2 : ZMod 61038018653) ^ 299159 := by rw [pow_add]
          _ = 10697387587 := by rw [factor_4_18]; decide
      have factor_4_20 : (2 : ZMod 61038018653) ^ 1196636 = 11030007899 := by
        calc
          (2 : ZMod 61038018653) ^ 1196636 = (2 : ZMod 61038018653) ^ (598318 + 598318) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 598318 * (2 : ZMod 61038018653) ^ 598318 := by rw [pow_add]
          _ = 11030007899 := by rw [factor_4_19]; decide
      have factor_4_21 : (2 : ZMod 61038018653) ^ 2393272 = 9381620909 := by
        calc
          (2 : ZMod 61038018653) ^ 2393272 = (2 : ZMod 61038018653) ^ (1196636 + 1196636) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 1196636 * (2 : ZMod 61038018653) ^ 1196636 := by rw [pow_add]
          _ = 9381620909 := by rw [factor_4_20]; decide
      have factor_4_22 : (2 : ZMod 61038018653) ^ 4786544 = 39806863773 := by
        calc
          (2 : ZMod 61038018653) ^ 4786544 = (2 : ZMod 61038018653) ^ (2393272 + 2393272) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 2393272 * (2 : ZMod 61038018653) ^ 2393272 := by rw [pow_add]
          _ = 39806863773 := by rw [factor_4_21]; decide
      have factor_4_23 : (2 : ZMod 61038018653) ^ 9573089 = 26740636259 := by
        calc
          (2 : ZMod 61038018653) ^ 9573089 = (2 : ZMod 61038018653) ^ (4786544 + 4786544 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 4786544 * (2 : ZMod 61038018653) ^ 4786544) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 26740636259 := by rw [factor_4_22]; decide
      have factor_4_24 : (2 : ZMod 61038018653) ^ 19146179 = 11019755668 := by
        calc
          (2 : ZMod 61038018653) ^ 19146179 = (2 : ZMod 61038018653) ^ (9573089 + 9573089 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = ((2 : ZMod 61038018653) ^ 9573089 * (2 : ZMod 61038018653) ^ 9573089) * (2 : ZMod 61038018653) := by rw [pow_succ, pow_add]
          _ = 11019755668 := by rw [factor_4_23]; decide
      have factor_4_25 : (2 : ZMod 61038018653) ^ 38292358 = 46996267978 := by
        calc
          (2 : ZMod 61038018653) ^ 38292358 = (2 : ZMod 61038018653) ^ (19146179 + 19146179) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 19146179 * (2 : ZMod 61038018653) ^ 19146179 := by rw [pow_add]
          _ = 46996267978 := by rw [factor_4_24]; decide
      have factor_4_26 : (2 : ZMod 61038018653) ^ 76584716 = 50885918662 := by
        calc
          (2 : ZMod 61038018653) ^ 76584716 = (2 : ZMod 61038018653) ^ (38292358 + 38292358) :=
            congrArg (fun n : ℕ => (2 : ZMod 61038018653) ^ n) (by norm_num)
          _ = (2 : ZMod 61038018653) ^ 38292358 * (2 : ZMod 61038018653) ^ 38292358 := by rw [pow_add]
          _ = 50885918662 := by rw [factor_4_25]; decide
      change (2 : ZMod 61038018653) ^ 76584716 ≠ 1
      rw [factor_4_26]
      decide

#print axioms prime_lucas_61038018653

end TotientTailPeriodKiller
end Erdos249257
