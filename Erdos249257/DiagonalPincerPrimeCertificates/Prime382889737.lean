import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_382889737 : Nat.Prime 382889737 := by
  apply lucas_primality 382889737 (7 : ZMod 382889737)
  ·
      have fermat_0 : (7 : ZMod 382889737) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 382889737) ^ 2 = 49 := by
        calc
          (7 : ZMod 382889737) ^ 2 = (7 : ZMod 382889737) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 1 * (7 : ZMod 382889737) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 382889737) ^ 5 = 16807 := by
        calc
          (7 : ZMod 382889737) ^ 5 = (7 : ZMod 382889737) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 2 * (7 : ZMod 382889737) ^ 2) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 382889737) ^ 11 = 62878058 := by
        calc
          (7 : ZMod 382889737) ^ 11 = (7 : ZMod 382889737) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 5 * (7 : ZMod 382889737) ^ 5) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 62878058 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 382889737) ^ 22 = 56631761 := by
        calc
          (7 : ZMod 382889737) ^ 22 = (7 : ZMod 382889737) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 11 * (7 : ZMod 382889737) ^ 11 := by rw [pow_add]
          _ = 56631761 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 382889737) ^ 45 = 300829429 := by
        calc
          (7 : ZMod 382889737) ^ 45 = (7 : ZMod 382889737) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 22 * (7 : ZMod 382889737) ^ 22) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 300829429 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 382889737) ^ 91 = 260860223 := by
        calc
          (7 : ZMod 382889737) ^ 91 = (7 : ZMod 382889737) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 45 * (7 : ZMod 382889737) ^ 45) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 260860223 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 382889737) ^ 182 = 133772256 := by
        calc
          (7 : ZMod 382889737) ^ 182 = (7 : ZMod 382889737) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 91 * (7 : ZMod 382889737) ^ 91 := by rw [pow_add]
          _ = 133772256 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 382889737) ^ 365 = 206137202 := by
        calc
          (7 : ZMod 382889737) ^ 365 = (7 : ZMod 382889737) ^ (182 + 182 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 182 * (7 : ZMod 382889737) ^ 182) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 206137202 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 382889737) ^ 730 = 140696139 := by
        calc
          (7 : ZMod 382889737) ^ 730 = (7 : ZMod 382889737) ^ (365 + 365) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 365 * (7 : ZMod 382889737) ^ 365 := by rw [pow_add]
          _ = 140696139 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 382889737) ^ 1460 = 297709951 := by
        calc
          (7 : ZMod 382889737) ^ 1460 = (7 : ZMod 382889737) ^ (730 + 730) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 730 * (7 : ZMod 382889737) ^ 730 := by rw [pow_add]
          _ = 297709951 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 382889737) ^ 2921 = 103209205 := by
        calc
          (7 : ZMod 382889737) ^ 2921 = (7 : ZMod 382889737) ^ (1460 + 1460 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 1460 * (7 : ZMod 382889737) ^ 1460) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 103209205 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 382889737) ^ 5842 = 100843280 := by
        calc
          (7 : ZMod 382889737) ^ 5842 = (7 : ZMod 382889737) ^ (2921 + 2921) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 2921 * (7 : ZMod 382889737) ^ 2921 := by rw [pow_add]
          _ = 100843280 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 382889737) ^ 11684 = 259291634 := by
        calc
          (7 : ZMod 382889737) ^ 11684 = (7 : ZMod 382889737) ^ (5842 + 5842) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 5842 * (7 : ZMod 382889737) ^ 5842 := by rw [pow_add]
          _ = 259291634 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 382889737) ^ 23369 = 297508126 := by
        calc
          (7 : ZMod 382889737) ^ 23369 = (7 : ZMod 382889737) ^ (11684 + 11684 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 11684 * (7 : ZMod 382889737) ^ 11684) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 297508126 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 382889737) ^ 46739 = 216890196 := by
        calc
          (7 : ZMod 382889737) ^ 46739 = (7 : ZMod 382889737) ^ (23369 + 23369 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 23369 * (7 : ZMod 382889737) ^ 23369) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 216890196 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 382889737) ^ 93478 = 347931244 := by
        calc
          (7 : ZMod 382889737) ^ 93478 = (7 : ZMod 382889737) ^ (46739 + 46739) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 46739 * (7 : ZMod 382889737) ^ 46739 := by rw [pow_add]
          _ = 347931244 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 382889737) ^ 186957 = 267206965 := by
        calc
          (7 : ZMod 382889737) ^ 186957 = (7 : ZMod 382889737) ^ (93478 + 93478 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 93478 * (7 : ZMod 382889737) ^ 93478) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 267206965 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 382889737) ^ 373915 = 320977476 := by
        calc
          (7 : ZMod 382889737) ^ 373915 = (7 : ZMod 382889737) ^ (186957 + 186957 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 186957 * (7 : ZMod 382889737) ^ 186957) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 320977476 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 382889737) ^ 747831 = 238216582 := by
        calc
          (7 : ZMod 382889737) ^ 747831 = (7 : ZMod 382889737) ^ (373915 + 373915 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 373915 * (7 : ZMod 382889737) ^ 373915) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 238216582 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 382889737) ^ 1495663 = 377870752 := by
        calc
          (7 : ZMod 382889737) ^ 1495663 = (7 : ZMod 382889737) ^ (747831 + 747831 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 747831 * (7 : ZMod 382889737) ^ 747831) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 377870752 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 382889737) ^ 2991326 = 277522732 := by
        calc
          (7 : ZMod 382889737) ^ 2991326 = (7 : ZMod 382889737) ^ (1495663 + 1495663) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 1495663 * (7 : ZMod 382889737) ^ 1495663 := by rw [pow_add]
          _ = 277522732 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 382889737) ^ 5982652 = 19873315 := by
        calc
          (7 : ZMod 382889737) ^ 5982652 = (7 : ZMod 382889737) ^ (2991326 + 2991326) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 2991326 * (7 : ZMod 382889737) ^ 2991326 := by rw [pow_add]
          _ = 19873315 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 382889737) ^ 11965304 = 182712147 := by
        calc
          (7 : ZMod 382889737) ^ 11965304 = (7 : ZMod 382889737) ^ (5982652 + 5982652) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 5982652 * (7 : ZMod 382889737) ^ 5982652 := by rw [pow_add]
          _ = 182712147 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 382889737) ^ 23930608 = 180155838 := by
        calc
          (7 : ZMod 382889737) ^ 23930608 = (7 : ZMod 382889737) ^ (11965304 + 11965304) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 11965304 * (7 : ZMod 382889737) ^ 11965304 := by rw [pow_add]
          _ = 180155838 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 382889737) ^ 47861217 = 382005909 := by
        calc
          (7 : ZMod 382889737) ^ 47861217 = (7 : ZMod 382889737) ^ (23930608 + 23930608 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 23930608 * (7 : ZMod 382889737) ^ 23930608) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 382005909 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 382889737) ^ 95722434 = 56870104 := by
        calc
          (7 : ZMod 382889737) ^ 95722434 = (7 : ZMod 382889737) ^ (47861217 + 47861217) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 47861217 * (7 : ZMod 382889737) ^ 47861217 := by rw [pow_add]
          _ = 56870104 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 382889737) ^ 191444868 = 382889736 := by
        calc
          (7 : ZMod 382889737) ^ 191444868 = (7 : ZMod 382889737) ^ (95722434 + 95722434) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 95722434 * (7 : ZMod 382889737) ^ 95722434 := by rw [pow_add]
          _ = 382889736 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 382889737) ^ 382889736 = 1 := by
        calc
          (7 : ZMod 382889737) ^ 382889736 = (7 : ZMod 382889737) ^ (191444868 + 191444868) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 191444868 * (7 : ZMod 382889737) ^ 191444868 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (5317913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (5317913, 1)] : List FactorBlock).map factorBlockValue).prod = 382889737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 382889737) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 382889737) ^ 2 = 49 := by
        calc
          (7 : ZMod 382889737) ^ 2 = (7 : ZMod 382889737) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 1 * (7 : ZMod 382889737) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 382889737) ^ 5 = 16807 := by
        calc
          (7 : ZMod 382889737) ^ 5 = (7 : ZMod 382889737) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 2 * (7 : ZMod 382889737) ^ 2) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 382889737) ^ 11 = 62878058 := by
        calc
          (7 : ZMod 382889737) ^ 11 = (7 : ZMod 382889737) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 5 * (7 : ZMod 382889737) ^ 5) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 62878058 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 382889737) ^ 22 = 56631761 := by
        calc
          (7 : ZMod 382889737) ^ 22 = (7 : ZMod 382889737) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 11 * (7 : ZMod 382889737) ^ 11 := by rw [pow_add]
          _ = 56631761 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 382889737) ^ 45 = 300829429 := by
        calc
          (7 : ZMod 382889737) ^ 45 = (7 : ZMod 382889737) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 22 * (7 : ZMod 382889737) ^ 22) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 300829429 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 382889737) ^ 91 = 260860223 := by
        calc
          (7 : ZMod 382889737) ^ 91 = (7 : ZMod 382889737) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 45 * (7 : ZMod 382889737) ^ 45) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 260860223 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 382889737) ^ 182 = 133772256 := by
        calc
          (7 : ZMod 382889737) ^ 182 = (7 : ZMod 382889737) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 91 * (7 : ZMod 382889737) ^ 91 := by rw [pow_add]
          _ = 133772256 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 382889737) ^ 365 = 206137202 := by
        calc
          (7 : ZMod 382889737) ^ 365 = (7 : ZMod 382889737) ^ (182 + 182 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 182 * (7 : ZMod 382889737) ^ 182) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 206137202 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 382889737) ^ 730 = 140696139 := by
        calc
          (7 : ZMod 382889737) ^ 730 = (7 : ZMod 382889737) ^ (365 + 365) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 365 * (7 : ZMod 382889737) ^ 365 := by rw [pow_add]
          _ = 140696139 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 382889737) ^ 1460 = 297709951 := by
        calc
          (7 : ZMod 382889737) ^ 1460 = (7 : ZMod 382889737) ^ (730 + 730) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 730 * (7 : ZMod 382889737) ^ 730 := by rw [pow_add]
          _ = 297709951 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 382889737) ^ 2921 = 103209205 := by
        calc
          (7 : ZMod 382889737) ^ 2921 = (7 : ZMod 382889737) ^ (1460 + 1460 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 1460 * (7 : ZMod 382889737) ^ 1460) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 103209205 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 382889737) ^ 5842 = 100843280 := by
        calc
          (7 : ZMod 382889737) ^ 5842 = (7 : ZMod 382889737) ^ (2921 + 2921) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 2921 * (7 : ZMod 382889737) ^ 2921 := by rw [pow_add]
          _ = 100843280 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 382889737) ^ 11684 = 259291634 := by
        calc
          (7 : ZMod 382889737) ^ 11684 = (7 : ZMod 382889737) ^ (5842 + 5842) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 5842 * (7 : ZMod 382889737) ^ 5842 := by rw [pow_add]
          _ = 259291634 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 382889737) ^ 23369 = 297508126 := by
        calc
          (7 : ZMod 382889737) ^ 23369 = (7 : ZMod 382889737) ^ (11684 + 11684 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 11684 * (7 : ZMod 382889737) ^ 11684) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 297508126 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 382889737) ^ 46739 = 216890196 := by
        calc
          (7 : ZMod 382889737) ^ 46739 = (7 : ZMod 382889737) ^ (23369 + 23369 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 23369 * (7 : ZMod 382889737) ^ 23369) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 216890196 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 382889737) ^ 93478 = 347931244 := by
        calc
          (7 : ZMod 382889737) ^ 93478 = (7 : ZMod 382889737) ^ (46739 + 46739) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 46739 * (7 : ZMod 382889737) ^ 46739 := by rw [pow_add]
          _ = 347931244 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 382889737) ^ 186957 = 267206965 := by
        calc
          (7 : ZMod 382889737) ^ 186957 = (7 : ZMod 382889737) ^ (93478 + 93478 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 93478 * (7 : ZMod 382889737) ^ 93478) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 267206965 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 382889737) ^ 373915 = 320977476 := by
        calc
          (7 : ZMod 382889737) ^ 373915 = (7 : ZMod 382889737) ^ (186957 + 186957 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 186957 * (7 : ZMod 382889737) ^ 186957) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 320977476 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 382889737) ^ 747831 = 238216582 := by
        calc
          (7 : ZMod 382889737) ^ 747831 = (7 : ZMod 382889737) ^ (373915 + 373915 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 373915 * (7 : ZMod 382889737) ^ 373915) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 238216582 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 382889737) ^ 1495663 = 377870752 := by
        calc
          (7 : ZMod 382889737) ^ 1495663 = (7 : ZMod 382889737) ^ (747831 + 747831 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 747831 * (7 : ZMod 382889737) ^ 747831) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 377870752 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 382889737) ^ 2991326 = 277522732 := by
        calc
          (7 : ZMod 382889737) ^ 2991326 = (7 : ZMod 382889737) ^ (1495663 + 1495663) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 1495663 * (7 : ZMod 382889737) ^ 1495663 := by rw [pow_add]
          _ = 277522732 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 382889737) ^ 5982652 = 19873315 := by
        calc
          (7 : ZMod 382889737) ^ 5982652 = (7 : ZMod 382889737) ^ (2991326 + 2991326) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 2991326 * (7 : ZMod 382889737) ^ 2991326 := by rw [pow_add]
          _ = 19873315 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 382889737) ^ 11965304 = 182712147 := by
        calc
          (7 : ZMod 382889737) ^ 11965304 = (7 : ZMod 382889737) ^ (5982652 + 5982652) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 5982652 * (7 : ZMod 382889737) ^ 5982652 := by rw [pow_add]
          _ = 182712147 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 382889737) ^ 23930608 = 180155838 := by
        calc
          (7 : ZMod 382889737) ^ 23930608 = (7 : ZMod 382889737) ^ (11965304 + 11965304) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 11965304 * (7 : ZMod 382889737) ^ 11965304 := by rw [pow_add]
          _ = 180155838 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 382889737) ^ 47861217 = 382005909 := by
        calc
          (7 : ZMod 382889737) ^ 47861217 = (7 : ZMod 382889737) ^ (23930608 + 23930608 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 23930608 * (7 : ZMod 382889737) ^ 23930608) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 382005909 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 382889737) ^ 95722434 = 56870104 := by
        calc
          (7 : ZMod 382889737) ^ 95722434 = (7 : ZMod 382889737) ^ (47861217 + 47861217) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 47861217 * (7 : ZMod 382889737) ^ 47861217 := by rw [pow_add]
          _ = 56870104 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 382889737) ^ 191444868 = 382889736 := by
        calc
          (7 : ZMod 382889737) ^ 191444868 = (7 : ZMod 382889737) ^ (95722434 + 95722434) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 95722434 * (7 : ZMod 382889737) ^ 95722434 := by rw [pow_add]
          _ = 382889736 := by rw [factor_0_26]; decide
      change (7 : ZMod 382889737) ^ 191444868 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (7 : ZMod 382889737) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 382889737) ^ 3 = 343 := by
        calc
          (7 : ZMod 382889737) ^ 3 = (7 : ZMod 382889737) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 1 * (7 : ZMod 382889737) ^ 1) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 382889737) ^ 7 = 823543 := by
        calc
          (7 : ZMod 382889737) ^ 7 = (7 : ZMod 382889737) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 3 * (7 : ZMod 382889737) ^ 3) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 382889737) ^ 15 = 111660880 := by
        calc
          (7 : ZMod 382889737) ^ 15 = (7 : ZMod 382889737) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 7 * (7 : ZMod 382889737) ^ 7) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 111660880 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 382889737) ^ 30 = 281081248 := by
        calc
          (7 : ZMod 382889737) ^ 30 = (7 : ZMod 382889737) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 15 * (7 : ZMod 382889737) ^ 15 := by rw [pow_add]
          _ = 281081248 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 382889737) ^ 60 = 51111483 := by
        calc
          (7 : ZMod 382889737) ^ 60 = (7 : ZMod 382889737) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 30 * (7 : ZMod 382889737) ^ 30 := by rw [pow_add]
          _ = 51111483 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 382889737) ^ 121 = 290156918 := by
        calc
          (7 : ZMod 382889737) ^ 121 = (7 : ZMod 382889737) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 60 * (7 : ZMod 382889737) ^ 60) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 290156918 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 382889737) ^ 243 = 244861168 := by
        calc
          (7 : ZMod 382889737) ^ 243 = (7 : ZMod 382889737) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 121 * (7 : ZMod 382889737) ^ 121) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 244861168 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 382889737) ^ 486 = 127301737 := by
        calc
          (7 : ZMod 382889737) ^ 486 = (7 : ZMod 382889737) ^ (243 + 243) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 243 * (7 : ZMod 382889737) ^ 243 := by rw [pow_add]
          _ = 127301737 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 382889737) ^ 973 = 323800139 := by
        calc
          (7 : ZMod 382889737) ^ 973 = (7 : ZMod 382889737) ^ (486 + 486 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 486 * (7 : ZMod 382889737) ^ 486) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 323800139 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 382889737) ^ 1947 = 993886 := by
        calc
          (7 : ZMod 382889737) ^ 1947 = (7 : ZMod 382889737) ^ (973 + 973 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 973 * (7 : ZMod 382889737) ^ 973) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 993886 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 382889737) ^ 3894 = 336749273 := by
        calc
          (7 : ZMod 382889737) ^ 3894 = (7 : ZMod 382889737) ^ (1947 + 1947) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 1947 * (7 : ZMod 382889737) ^ 1947 := by rw [pow_add]
          _ = 336749273 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 382889737) ^ 7789 = 357959749 := by
        calc
          (7 : ZMod 382889737) ^ 7789 = (7 : ZMod 382889737) ^ (3894 + 3894 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 3894 * (7 : ZMod 382889737) ^ 3894) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 357959749 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 382889737) ^ 15579 = 228330899 := by
        calc
          (7 : ZMod 382889737) ^ 15579 = (7 : ZMod 382889737) ^ (7789 + 7789 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 7789 * (7 : ZMod 382889737) ^ 7789) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 228330899 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 382889737) ^ 31159 = 363790818 := by
        calc
          (7 : ZMod 382889737) ^ 31159 = (7 : ZMod 382889737) ^ (15579 + 15579 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 15579 * (7 : ZMod 382889737) ^ 15579) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 363790818 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 382889737) ^ 62319 = 330750657 := by
        calc
          (7 : ZMod 382889737) ^ 62319 = (7 : ZMod 382889737) ^ (31159 + 31159 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 31159 * (7 : ZMod 382889737) ^ 31159) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 330750657 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 382889737) ^ 124638 = 224843256 := by
        calc
          (7 : ZMod 382889737) ^ 124638 = (7 : ZMod 382889737) ^ (62319 + 62319) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 62319 * (7 : ZMod 382889737) ^ 62319 := by rw [pow_add]
          _ = 224843256 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 382889737) ^ 249277 = 231180729 := by
        calc
          (7 : ZMod 382889737) ^ 249277 = (7 : ZMod 382889737) ^ (124638 + 124638 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 124638 * (7 : ZMod 382889737) ^ 124638) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 231180729 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 382889737) ^ 498554 = 24117172 := by
        calc
          (7 : ZMod 382889737) ^ 498554 = (7 : ZMod 382889737) ^ (249277 + 249277) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 249277 * (7 : ZMod 382889737) ^ 249277 := by rw [pow_add]
          _ = 24117172 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 382889737) ^ 997108 = 140934046 := by
        calc
          (7 : ZMod 382889737) ^ 997108 = (7 : ZMod 382889737) ^ (498554 + 498554) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 498554 * (7 : ZMod 382889737) ^ 498554 := by rw [pow_add]
          _ = 140934046 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 382889737) ^ 1994217 = 356716601 := by
        calc
          (7 : ZMod 382889737) ^ 1994217 = (7 : ZMod 382889737) ^ (997108 + 997108 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 997108 * (7 : ZMod 382889737) ^ 997108) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 356716601 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 382889737) ^ 3988434 = 42041215 := by
        calc
          (7 : ZMod 382889737) ^ 3988434 = (7 : ZMod 382889737) ^ (1994217 + 1994217) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 1994217 * (7 : ZMod 382889737) ^ 1994217 := by rw [pow_add]
          _ = 42041215 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 382889737) ^ 7976869 = 307874446 := by
        calc
          (7 : ZMod 382889737) ^ 7976869 = (7 : ZMod 382889737) ^ (3988434 + 3988434 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 3988434 * (7 : ZMod 382889737) ^ 3988434) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 307874446 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 382889737) ^ 15953739 = 87113820 := by
        calc
          (7 : ZMod 382889737) ^ 15953739 = (7 : ZMod 382889737) ^ (7976869 + 7976869 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 7976869 * (7 : ZMod 382889737) ^ 7976869) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 87113820 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 382889737) ^ 31907478 = 98223213 := by
        calc
          (7 : ZMod 382889737) ^ 31907478 = (7 : ZMod 382889737) ^ (15953739 + 15953739) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 15953739 * (7 : ZMod 382889737) ^ 15953739 := by rw [pow_add]
          _ = 98223213 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 382889737) ^ 63814956 = 132351422 := by
        calc
          (7 : ZMod 382889737) ^ 63814956 = (7 : ZMod 382889737) ^ (31907478 + 31907478) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 31907478 * (7 : ZMod 382889737) ^ 31907478 := by rw [pow_add]
          _ = 132351422 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 382889737) ^ 127629912 = 132351421 := by
        calc
          (7 : ZMod 382889737) ^ 127629912 = (7 : ZMod 382889737) ^ (63814956 + 63814956) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 63814956 * (7 : ZMod 382889737) ^ 63814956 := by rw [pow_add]
          _ = 132351421 := by rw [factor_1_25]; decide
      change (7 : ZMod 382889737) ^ 127629912 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (7 : ZMod 382889737) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 382889737) ^ 2 = 49 := by
        calc
          (7 : ZMod 382889737) ^ 2 = (7 : ZMod 382889737) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 1 * (7 : ZMod 382889737) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 382889737) ^ 4 = 2401 := by
        calc
          (7 : ZMod 382889737) ^ 4 = (7 : ZMod 382889737) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 2 * (7 : ZMod 382889737) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 382889737) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 382889737) ^ 9 = (7 : ZMod 382889737) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = ((7 : ZMod 382889737) ^ 4 * (7 : ZMod 382889737) ^ 4) * (7 : ZMod 382889737) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 382889737) ^ 18 = 10708140 := by
        calc
          (7 : ZMod 382889737) ^ 18 = (7 : ZMod 382889737) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 9 * (7 : ZMod 382889737) ^ 9 := by rw [pow_add]
          _ = 10708140 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 382889737) ^ 36 = 272720210 := by
        calc
          (7 : ZMod 382889737) ^ 36 = (7 : ZMod 382889737) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 18 * (7 : ZMod 382889737) ^ 18 := by rw [pow_add]
          _ = 272720210 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 382889737) ^ 72 = 291791213 := by
        calc
          (7 : ZMod 382889737) ^ 72 = (7 : ZMod 382889737) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (7 : ZMod 382889737) ^ n) (by norm_num)
          _ = (7 : ZMod 382889737) ^ 36 * (7 : ZMod 382889737) ^ 36 := by rw [pow_add]
          _ = 291791213 := by rw [factor_2_5]; decide
      change (7 : ZMod 382889737) ^ 72 ≠ 1
      rw [factor_2_6]
      decide

#print axioms prime_lucas_382889737

end TotientTailPeriodKiller
end Erdos249257
