import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_87158321 : Nat.Prime 87158321 := by
  apply lucas_primality 87158321 (6 : ZMod 87158321)
  ·
      have fermat_0 : (6 : ZMod 87158321) ^ 1 = 6 := by norm_num
      have fermat_1 : (6 : ZMod 87158321) ^ 2 = 36 := by
        calc
          (6 : ZMod 87158321) ^ 2 = (6 : ZMod 87158321) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 1 * (6 : ZMod 87158321) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [fermat_0]; decide
      have fermat_2 : (6 : ZMod 87158321) ^ 5 = 7776 := by
        calc
          (6 : ZMod 87158321) ^ 5 = (6 : ZMod 87158321) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 2 * (6 : ZMod 87158321) ^ 2) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [fermat_1]; decide
      have fermat_3 : (6 : ZMod 87158321) ^ 10 = 60466176 := by
        calc
          (6 : ZMod 87158321) ^ 10 = (6 : ZMod 87158321) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 5 * (6 : ZMod 87158321) ^ 5 := by rw [pow_add]
          _ = 60466176 := by rw [fermat_2]; decide
      have fermat_4 : (6 : ZMod 87158321) ^ 20 = 52027464 := by
        calc
          (6 : ZMod 87158321) ^ 20 = (6 : ZMod 87158321) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 10 * (6 : ZMod 87158321) ^ 10 := by rw [pow_add]
          _ = 52027464 := by rw [fermat_3]; decide
      have fermat_5 : (6 : ZMod 87158321) ^ 41 = 38613002 := by
        calc
          (6 : ZMod 87158321) ^ 41 = (6 : ZMod 87158321) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 20 * (6 : ZMod 87158321) ^ 20) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 38613002 := by rw [fermat_4]; decide
      have fermat_6 : (6 : ZMod 87158321) ^ 83 = 73567946 := by
        calc
          (6 : ZMod 87158321) ^ 83 = (6 : ZMod 87158321) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 41 * (6 : ZMod 87158321) ^ 41) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 73567946 := by rw [fermat_5]; decide
      have fermat_7 : (6 : ZMod 87158321) ^ 166 = 48709673 := by
        calc
          (6 : ZMod 87158321) ^ 166 = (6 : ZMod 87158321) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 83 * (6 : ZMod 87158321) ^ 83 := by rw [pow_add]
          _ = 48709673 := by rw [fermat_6]; decide
      have fermat_8 : (6 : ZMod 87158321) ^ 332 = 62306113 := by
        calc
          (6 : ZMod 87158321) ^ 332 = (6 : ZMod 87158321) ^ (166 + 166) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 166 * (6 : ZMod 87158321) ^ 166 := by rw [pow_add]
          _ = 62306113 := by rw [fermat_7]; decide
      have fermat_9 : (6 : ZMod 87158321) ^ 664 = 53414939 := by
        calc
          (6 : ZMod 87158321) ^ 664 = (6 : ZMod 87158321) ^ (332 + 332) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 332 * (6 : ZMod 87158321) ^ 332 := by rw [pow_add]
          _ = 53414939 := by rw [fermat_8]; decide
      have fermat_10 : (6 : ZMod 87158321) ^ 1329 = 32756154 := by
        calc
          (6 : ZMod 87158321) ^ 1329 = (6 : ZMod 87158321) ^ (664 + 664 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 664 * (6 : ZMod 87158321) ^ 664) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 32756154 := by rw [fermat_9]; decide
      have fermat_11 : (6 : ZMod 87158321) ^ 2659 = 33326602 := by
        calc
          (6 : ZMod 87158321) ^ 2659 = (6 : ZMod 87158321) ^ (1329 + 1329 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 1329 * (6 : ZMod 87158321) ^ 1329) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 33326602 := by rw [fermat_10]; decide
      have fermat_12 : (6 : ZMod 87158321) ^ 5319 = 52592075 := by
        calc
          (6 : ZMod 87158321) ^ 5319 = (6 : ZMod 87158321) ^ (2659 + 2659 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 2659 * (6 : ZMod 87158321) ^ 2659) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 52592075 := by rw [fermat_11]; decide
      have fermat_13 : (6 : ZMod 87158321) ^ 10639 = 29537268 := by
        calc
          (6 : ZMod 87158321) ^ 10639 = (6 : ZMod 87158321) ^ (5319 + 5319 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 5319 * (6 : ZMod 87158321) ^ 5319) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 29537268 := by rw [fermat_12]; decide
      have fermat_14 : (6 : ZMod 87158321) ^ 21278 = 27084837 := by
        calc
          (6 : ZMod 87158321) ^ 21278 = (6 : ZMod 87158321) ^ (10639 + 10639) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 10639 * (6 : ZMod 87158321) ^ 10639 := by rw [pow_add]
          _ = 27084837 := by rw [fermat_13]; decide
      have fermat_15 : (6 : ZMod 87158321) ^ 42557 = 36596051 := by
        calc
          (6 : ZMod 87158321) ^ 42557 = (6 : ZMod 87158321) ^ (21278 + 21278 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 21278 * (6 : ZMod 87158321) ^ 21278) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 36596051 := by rw [fermat_14]; decide
      have fermat_16 : (6 : ZMod 87158321) ^ 85115 = 52490029 := by
        calc
          (6 : ZMod 87158321) ^ 85115 = (6 : ZMod 87158321) ^ (42557 + 42557 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 42557 * (6 : ZMod 87158321) ^ 42557) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 52490029 := by rw [fermat_15]; decide
      have fermat_17 : (6 : ZMod 87158321) ^ 170231 = 5890912 := by
        calc
          (6 : ZMod 87158321) ^ 170231 = (6 : ZMod 87158321) ^ (85115 + 85115 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 85115 * (6 : ZMod 87158321) ^ 85115) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 5890912 := by rw [fermat_16]; decide
      have fermat_18 : (6 : ZMod 87158321) ^ 340462 = 61419026 := by
        calc
          (6 : ZMod 87158321) ^ 340462 = (6 : ZMod 87158321) ^ (170231 + 170231) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 170231 * (6 : ZMod 87158321) ^ 170231 := by rw [pow_add]
          _ = 61419026 := by rw [fermat_17]; decide
      have fermat_19 : (6 : ZMod 87158321) ^ 680924 = 78337306 := by
        calc
          (6 : ZMod 87158321) ^ 680924 = (6 : ZMod 87158321) ^ (340462 + 340462) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 340462 * (6 : ZMod 87158321) ^ 340462 := by rw [pow_add]
          _ = 78337306 := by rw [fermat_18]; decide
      have fermat_20 : (6 : ZMod 87158321) ^ 1361848 = 63190759 := by
        calc
          (6 : ZMod 87158321) ^ 1361848 = (6 : ZMod 87158321) ^ (680924 + 680924) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 680924 * (6 : ZMod 87158321) ^ 680924 := by rw [pow_add]
          _ = 63190759 := by rw [fermat_19]; decide
      have fermat_21 : (6 : ZMod 87158321) ^ 2723697 = 44613078 := by
        calc
          (6 : ZMod 87158321) ^ 2723697 = (6 : ZMod 87158321) ^ (1361848 + 1361848 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 1361848 * (6 : ZMod 87158321) ^ 1361848) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 44613078 := by rw [fermat_20]; decide
      have fermat_22 : (6 : ZMod 87158321) ^ 5447395 = 62275929 := by
        calc
          (6 : ZMod 87158321) ^ 5447395 = (6 : ZMod 87158321) ^ (2723697 + 2723697 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 2723697 * (6 : ZMod 87158321) ^ 2723697) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 62275929 := by rw [fermat_21]; decide
      have fermat_23 : (6 : ZMod 87158321) ^ 10894790 = 27660435 := by
        calc
          (6 : ZMod 87158321) ^ 10894790 = (6 : ZMod 87158321) ^ (5447395 + 5447395) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 5447395 * (6 : ZMod 87158321) ^ 5447395 := by rw [pow_add]
          _ = 27660435 := by rw [fermat_22]; decide
      have fermat_24 : (6 : ZMod 87158321) ^ 21789580 = 41271271 := by
        calc
          (6 : ZMod 87158321) ^ 21789580 = (6 : ZMod 87158321) ^ (10894790 + 10894790) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 10894790 * (6 : ZMod 87158321) ^ 10894790 := by rw [pow_add]
          _ = 41271271 := by rw [fermat_23]; decide
      have fermat_25 : (6 : ZMod 87158321) ^ 43579160 = 87158320 := by
        calc
          (6 : ZMod 87158321) ^ 43579160 = (6 : ZMod 87158321) ^ (21789580 + 21789580) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 21789580 * (6 : ZMod 87158321) ^ 21789580 := by rw [pow_add]
          _ = 87158320 := by rw [fermat_24]; decide
      have fermat_26 : (6 : ZMod 87158321) ^ 87158320 = 1 := by
        calc
          (6 : ZMod 87158321) ^ 87158320 = (6 : ZMod 87158321) ^ (43579160 + 43579160) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 43579160 * (6 : ZMod 87158321) ^ 43579160 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (17, 1), (19, 1), (3373, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (17, 1), (19, 1), (3373, 1)] : List FactorBlock).map factorBlockValue).prod = 87158321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (6 : ZMod 87158321) ^ 1 = 6 := by norm_num
      have factor_0_1 : (6 : ZMod 87158321) ^ 2 = 36 := by
        calc
          (6 : ZMod 87158321) ^ 2 = (6 : ZMod 87158321) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 1 * (6 : ZMod 87158321) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_0_0]; decide
      have factor_0_2 : (6 : ZMod 87158321) ^ 5 = 7776 := by
        calc
          (6 : ZMod 87158321) ^ 5 = (6 : ZMod 87158321) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 2 * (6 : ZMod 87158321) ^ 2) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_0_1]; decide
      have factor_0_3 : (6 : ZMod 87158321) ^ 10 = 60466176 := by
        calc
          (6 : ZMod 87158321) ^ 10 = (6 : ZMod 87158321) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 5 * (6 : ZMod 87158321) ^ 5 := by rw [pow_add]
          _ = 60466176 := by rw [factor_0_2]; decide
      have factor_0_4 : (6 : ZMod 87158321) ^ 20 = 52027464 := by
        calc
          (6 : ZMod 87158321) ^ 20 = (6 : ZMod 87158321) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 10 * (6 : ZMod 87158321) ^ 10 := by rw [pow_add]
          _ = 52027464 := by rw [factor_0_3]; decide
      have factor_0_5 : (6 : ZMod 87158321) ^ 41 = 38613002 := by
        calc
          (6 : ZMod 87158321) ^ 41 = (6 : ZMod 87158321) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 20 * (6 : ZMod 87158321) ^ 20) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 38613002 := by rw [factor_0_4]; decide
      have factor_0_6 : (6 : ZMod 87158321) ^ 83 = 73567946 := by
        calc
          (6 : ZMod 87158321) ^ 83 = (6 : ZMod 87158321) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 41 * (6 : ZMod 87158321) ^ 41) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 73567946 := by rw [factor_0_5]; decide
      have factor_0_7 : (6 : ZMod 87158321) ^ 166 = 48709673 := by
        calc
          (6 : ZMod 87158321) ^ 166 = (6 : ZMod 87158321) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 83 * (6 : ZMod 87158321) ^ 83 := by rw [pow_add]
          _ = 48709673 := by rw [factor_0_6]; decide
      have factor_0_8 : (6 : ZMod 87158321) ^ 332 = 62306113 := by
        calc
          (6 : ZMod 87158321) ^ 332 = (6 : ZMod 87158321) ^ (166 + 166) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 166 * (6 : ZMod 87158321) ^ 166 := by rw [pow_add]
          _ = 62306113 := by rw [factor_0_7]; decide
      have factor_0_9 : (6 : ZMod 87158321) ^ 664 = 53414939 := by
        calc
          (6 : ZMod 87158321) ^ 664 = (6 : ZMod 87158321) ^ (332 + 332) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 332 * (6 : ZMod 87158321) ^ 332 := by rw [pow_add]
          _ = 53414939 := by rw [factor_0_8]; decide
      have factor_0_10 : (6 : ZMod 87158321) ^ 1329 = 32756154 := by
        calc
          (6 : ZMod 87158321) ^ 1329 = (6 : ZMod 87158321) ^ (664 + 664 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 664 * (6 : ZMod 87158321) ^ 664) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 32756154 := by rw [factor_0_9]; decide
      have factor_0_11 : (6 : ZMod 87158321) ^ 2659 = 33326602 := by
        calc
          (6 : ZMod 87158321) ^ 2659 = (6 : ZMod 87158321) ^ (1329 + 1329 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 1329 * (6 : ZMod 87158321) ^ 1329) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 33326602 := by rw [factor_0_10]; decide
      have factor_0_12 : (6 : ZMod 87158321) ^ 5319 = 52592075 := by
        calc
          (6 : ZMod 87158321) ^ 5319 = (6 : ZMod 87158321) ^ (2659 + 2659 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 2659 * (6 : ZMod 87158321) ^ 2659) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 52592075 := by rw [factor_0_11]; decide
      have factor_0_13 : (6 : ZMod 87158321) ^ 10639 = 29537268 := by
        calc
          (6 : ZMod 87158321) ^ 10639 = (6 : ZMod 87158321) ^ (5319 + 5319 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 5319 * (6 : ZMod 87158321) ^ 5319) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 29537268 := by rw [factor_0_12]; decide
      have factor_0_14 : (6 : ZMod 87158321) ^ 21278 = 27084837 := by
        calc
          (6 : ZMod 87158321) ^ 21278 = (6 : ZMod 87158321) ^ (10639 + 10639) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 10639 * (6 : ZMod 87158321) ^ 10639 := by rw [pow_add]
          _ = 27084837 := by rw [factor_0_13]; decide
      have factor_0_15 : (6 : ZMod 87158321) ^ 42557 = 36596051 := by
        calc
          (6 : ZMod 87158321) ^ 42557 = (6 : ZMod 87158321) ^ (21278 + 21278 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 21278 * (6 : ZMod 87158321) ^ 21278) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 36596051 := by rw [factor_0_14]; decide
      have factor_0_16 : (6 : ZMod 87158321) ^ 85115 = 52490029 := by
        calc
          (6 : ZMod 87158321) ^ 85115 = (6 : ZMod 87158321) ^ (42557 + 42557 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 42557 * (6 : ZMod 87158321) ^ 42557) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 52490029 := by rw [factor_0_15]; decide
      have factor_0_17 : (6 : ZMod 87158321) ^ 170231 = 5890912 := by
        calc
          (6 : ZMod 87158321) ^ 170231 = (6 : ZMod 87158321) ^ (85115 + 85115 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 85115 * (6 : ZMod 87158321) ^ 85115) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 5890912 := by rw [factor_0_16]; decide
      have factor_0_18 : (6 : ZMod 87158321) ^ 340462 = 61419026 := by
        calc
          (6 : ZMod 87158321) ^ 340462 = (6 : ZMod 87158321) ^ (170231 + 170231) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 170231 * (6 : ZMod 87158321) ^ 170231 := by rw [pow_add]
          _ = 61419026 := by rw [factor_0_17]; decide
      have factor_0_19 : (6 : ZMod 87158321) ^ 680924 = 78337306 := by
        calc
          (6 : ZMod 87158321) ^ 680924 = (6 : ZMod 87158321) ^ (340462 + 340462) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 340462 * (6 : ZMod 87158321) ^ 340462 := by rw [pow_add]
          _ = 78337306 := by rw [factor_0_18]; decide
      have factor_0_20 : (6 : ZMod 87158321) ^ 1361848 = 63190759 := by
        calc
          (6 : ZMod 87158321) ^ 1361848 = (6 : ZMod 87158321) ^ (680924 + 680924) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 680924 * (6 : ZMod 87158321) ^ 680924 := by rw [pow_add]
          _ = 63190759 := by rw [factor_0_19]; decide
      have factor_0_21 : (6 : ZMod 87158321) ^ 2723697 = 44613078 := by
        calc
          (6 : ZMod 87158321) ^ 2723697 = (6 : ZMod 87158321) ^ (1361848 + 1361848 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 1361848 * (6 : ZMod 87158321) ^ 1361848) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 44613078 := by rw [factor_0_20]; decide
      have factor_0_22 : (6 : ZMod 87158321) ^ 5447395 = 62275929 := by
        calc
          (6 : ZMod 87158321) ^ 5447395 = (6 : ZMod 87158321) ^ (2723697 + 2723697 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 2723697 * (6 : ZMod 87158321) ^ 2723697) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 62275929 := by rw [factor_0_21]; decide
      have factor_0_23 : (6 : ZMod 87158321) ^ 10894790 = 27660435 := by
        calc
          (6 : ZMod 87158321) ^ 10894790 = (6 : ZMod 87158321) ^ (5447395 + 5447395) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 5447395 * (6 : ZMod 87158321) ^ 5447395 := by rw [pow_add]
          _ = 27660435 := by rw [factor_0_22]; decide
      have factor_0_24 : (6 : ZMod 87158321) ^ 21789580 = 41271271 := by
        calc
          (6 : ZMod 87158321) ^ 21789580 = (6 : ZMod 87158321) ^ (10894790 + 10894790) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 10894790 * (6 : ZMod 87158321) ^ 10894790 := by rw [pow_add]
          _ = 41271271 := by rw [factor_0_23]; decide
      have factor_0_25 : (6 : ZMod 87158321) ^ 43579160 = 87158320 := by
        calc
          (6 : ZMod 87158321) ^ 43579160 = (6 : ZMod 87158321) ^ (21789580 + 21789580) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 21789580 * (6 : ZMod 87158321) ^ 21789580 := by rw [pow_add]
          _ = 87158320 := by rw [factor_0_24]; decide
      change (6 : ZMod 87158321) ^ 43579160 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (6 : ZMod 87158321) ^ 1 = 6 := by norm_num
      have factor_1_1 : (6 : ZMod 87158321) ^ 2 = 36 := by
        calc
          (6 : ZMod 87158321) ^ 2 = (6 : ZMod 87158321) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 1 * (6 : ZMod 87158321) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_1_0]; decide
      have factor_1_2 : (6 : ZMod 87158321) ^ 4 = 1296 := by
        calc
          (6 : ZMod 87158321) ^ 4 = (6 : ZMod 87158321) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 2 * (6 : ZMod 87158321) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_1_1]; decide
      have factor_1_3 : (6 : ZMod 87158321) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 87158321) ^ 8 = (6 : ZMod 87158321) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 4 * (6 : ZMod 87158321) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_1_2]; decide
      have factor_1_4 : (6 : ZMod 87158321) ^ 16 = 56531649 := by
        calc
          (6 : ZMod 87158321) ^ 16 = (6 : ZMod 87158321) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 8 * (6 : ZMod 87158321) ^ 8 := by rw [pow_add]
          _ = 56531649 := by rw [factor_1_3]; decide
      have factor_1_5 : (6 : ZMod 87158321) ^ 33 = 59724076 := by
        calc
          (6 : ZMod 87158321) ^ 33 = (6 : ZMod 87158321) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 16 * (6 : ZMod 87158321) ^ 16) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 59724076 := by rw [factor_1_4]; decide
      have factor_1_6 : (6 : ZMod 87158321) ^ 66 = 72338651 := by
        calc
          (6 : ZMod 87158321) ^ 66 = (6 : ZMod 87158321) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 33 * (6 : ZMod 87158321) ^ 33 := by rw [pow_add]
          _ = 72338651 := by rw [factor_1_5]; decide
      have factor_1_7 : (6 : ZMod 87158321) ^ 132 = 35753248 := by
        calc
          (6 : ZMod 87158321) ^ 132 = (6 : ZMod 87158321) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 66 * (6 : ZMod 87158321) ^ 66 := by rw [pow_add]
          _ = 35753248 := by rw [factor_1_6]; decide
      have factor_1_8 : (6 : ZMod 87158321) ^ 265 = 64940504 := by
        calc
          (6 : ZMod 87158321) ^ 265 = (6 : ZMod 87158321) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 132 * (6 : ZMod 87158321) ^ 132) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 64940504 := by rw [factor_1_7]; decide
      have factor_1_9 : (6 : ZMod 87158321) ^ 531 = 955629 := by
        calc
          (6 : ZMod 87158321) ^ 531 = (6 : ZMod 87158321) ^ (265 + 265 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 265 * (6 : ZMod 87158321) ^ 265) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 955629 := by rw [factor_1_8]; decide
      have factor_1_10 : (6 : ZMod 87158321) ^ 1063 = 65705860 := by
        calc
          (6 : ZMod 87158321) ^ 1063 = (6 : ZMod 87158321) ^ (531 + 531 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 531 * (6 : ZMod 87158321) ^ 531) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 65705860 := by rw [factor_1_9]; decide
      have factor_1_11 : (6 : ZMod 87158321) ^ 2127 = 24102770 := by
        calc
          (6 : ZMod 87158321) ^ 2127 = (6 : ZMod 87158321) ^ (1063 + 1063 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 1063 * (6 : ZMod 87158321) ^ 1063) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 24102770 := by rw [factor_1_10]; decide
      have factor_1_12 : (6 : ZMod 87158321) ^ 4255 = 19217347 := by
        calc
          (6 : ZMod 87158321) ^ 4255 = (6 : ZMod 87158321) ^ (2127 + 2127 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 2127 * (6 : ZMod 87158321) ^ 2127) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 19217347 := by rw [factor_1_11]; decide
      have factor_1_13 : (6 : ZMod 87158321) ^ 8511 = 8729230 := by
        calc
          (6 : ZMod 87158321) ^ 8511 = (6 : ZMod 87158321) ^ (4255 + 4255 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 4255 * (6 : ZMod 87158321) ^ 4255) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 8729230 := by rw [factor_1_12]; decide
      have factor_1_14 : (6 : ZMod 87158321) ^ 17023 = 8461331 := by
        calc
          (6 : ZMod 87158321) ^ 17023 = (6 : ZMod 87158321) ^ (8511 + 8511 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 8511 * (6 : ZMod 87158321) ^ 8511) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 8461331 := by rw [factor_1_13]; decide
      have factor_1_15 : (6 : ZMod 87158321) ^ 34046 = 11305815 := by
        calc
          (6 : ZMod 87158321) ^ 34046 = (6 : ZMod 87158321) ^ (17023 + 17023) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 17023 * (6 : ZMod 87158321) ^ 17023 := by rw [pow_add]
          _ = 11305815 := by rw [factor_1_14]; decide
      have factor_1_16 : (6 : ZMod 87158321) ^ 68092 = 27259922 := by
        calc
          (6 : ZMod 87158321) ^ 68092 = (6 : ZMod 87158321) ^ (34046 + 34046) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 34046 * (6 : ZMod 87158321) ^ 34046 := by rw [pow_add]
          _ = 27259922 := by rw [factor_1_15]; decide
      have factor_1_17 : (6 : ZMod 87158321) ^ 136184 = 44115542 := by
        calc
          (6 : ZMod 87158321) ^ 136184 = (6 : ZMod 87158321) ^ (68092 + 68092) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 68092 * (6 : ZMod 87158321) ^ 68092 := by rw [pow_add]
          _ = 44115542 := by rw [factor_1_16]; decide
      have factor_1_18 : (6 : ZMod 87158321) ^ 272369 = 16554688 := by
        calc
          (6 : ZMod 87158321) ^ 272369 = (6 : ZMod 87158321) ^ (136184 + 136184 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 136184 * (6 : ZMod 87158321) ^ 136184) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 16554688 := by rw [factor_1_17]; decide
      have factor_1_19 : (6 : ZMod 87158321) ^ 544739 = 27330506 := by
        calc
          (6 : ZMod 87158321) ^ 544739 = (6 : ZMod 87158321) ^ (272369 + 272369 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 272369 * (6 : ZMod 87158321) ^ 272369) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 27330506 := by rw [factor_1_18]; decide
      have factor_1_20 : (6 : ZMod 87158321) ^ 1089479 = 242825 := by
        calc
          (6 : ZMod 87158321) ^ 1089479 = (6 : ZMod 87158321) ^ (544739 + 544739 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 544739 * (6 : ZMod 87158321) ^ 544739) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 242825 := by rw [factor_1_19]; decide
      have factor_1_21 : (6 : ZMod 87158321) ^ 2178958 = 44955629 := by
        calc
          (6 : ZMod 87158321) ^ 2178958 = (6 : ZMod 87158321) ^ (1089479 + 1089479) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 1089479 * (6 : ZMod 87158321) ^ 1089479 := by rw [pow_add]
          _ = 44955629 := by rw [factor_1_20]; decide
      have factor_1_22 : (6 : ZMod 87158321) ^ 4357916 = 83318335 := by
        calc
          (6 : ZMod 87158321) ^ 4357916 = (6 : ZMod 87158321) ^ (2178958 + 2178958) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 2178958 * (6 : ZMod 87158321) ^ 2178958 := by rw [pow_add]
          _ = 83318335 := by rw [factor_1_21]; decide
      have factor_1_23 : (6 : ZMod 87158321) ^ 8715832 = 47733416 := by
        calc
          (6 : ZMod 87158321) ^ 8715832 = (6 : ZMod 87158321) ^ (4357916 + 4357916) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 4357916 * (6 : ZMod 87158321) ^ 4357916 := by rw [pow_add]
          _ = 47733416 := by rw [factor_1_22]; decide
      have factor_1_24 : (6 : ZMod 87158321) ^ 17431664 = 33620095 := by
        calc
          (6 : ZMod 87158321) ^ 17431664 = (6 : ZMod 87158321) ^ (8715832 + 8715832) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 8715832 * (6 : ZMod 87158321) ^ 8715832 := by rw [pow_add]
          _ = 33620095 := by rw [factor_1_23]; decide
      change (6 : ZMod 87158321) ^ 17431664 ≠ 1
      rw [factor_1_24]
      decide
    ·
      have factor_2_0 : (6 : ZMod 87158321) ^ 1 = 6 := by norm_num
      have factor_2_1 : (6 : ZMod 87158321) ^ 2 = 36 := by
        calc
          (6 : ZMod 87158321) ^ 2 = (6 : ZMod 87158321) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 1 * (6 : ZMod 87158321) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_2_0]; decide
      have factor_2_2 : (6 : ZMod 87158321) ^ 4 = 1296 := by
        calc
          (6 : ZMod 87158321) ^ 4 = (6 : ZMod 87158321) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 2 * (6 : ZMod 87158321) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_2_1]; decide
      have factor_2_3 : (6 : ZMod 87158321) ^ 9 = 10077696 := by
        calc
          (6 : ZMod 87158321) ^ 9 = (6 : ZMod 87158321) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 4 * (6 : ZMod 87158321) ^ 4) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 10077696 := by rw [factor_2_2]; decide
      have factor_2_4 : (6 : ZMod 87158321) ^ 19 = 8671244 := by
        calc
          (6 : ZMod 87158321) ^ 19 = (6 : ZMod 87158321) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 9 * (6 : ZMod 87158321) ^ 9) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 8671244 := by rw [factor_2_3]; decide
      have factor_2_5 : (6 : ZMod 87158321) ^ 39 = 34967486 := by
        calc
          (6 : ZMod 87158321) ^ 39 = (6 : ZMod 87158321) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 19 * (6 : ZMod 87158321) ^ 19) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 34967486 := by rw [factor_2_4]; decide
      have factor_2_6 : (6 : ZMod 87158321) ^ 78 = 79523495 := by
        calc
          (6 : ZMod 87158321) ^ 78 = (6 : ZMod 87158321) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 39 * (6 : ZMod 87158321) ^ 39 := by rw [pow_add]
          _ = 79523495 := by rw [factor_2_5]; decide
      have factor_2_7 : (6 : ZMod 87158321) ^ 156 = 41707007 := by
        calc
          (6 : ZMod 87158321) ^ 156 = (6 : ZMod 87158321) ^ (78 + 78) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 78 * (6 : ZMod 87158321) ^ 78 := by rw [pow_add]
          _ = 41707007 := by rw [factor_2_6]; decide
      have factor_2_8 : (6 : ZMod 87158321) ^ 312 = 39375609 := by
        calc
          (6 : ZMod 87158321) ^ 312 = (6 : ZMod 87158321) ^ (156 + 156) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 156 * (6 : ZMod 87158321) ^ 156 := by rw [pow_add]
          _ = 39375609 := by rw [factor_2_7]; decide
      have factor_2_9 : (6 : ZMod 87158321) ^ 625 = 81826958 := by
        calc
          (6 : ZMod 87158321) ^ 625 = (6 : ZMod 87158321) ^ (312 + 312 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 312 * (6 : ZMod 87158321) ^ 312) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 81826958 := by rw [factor_2_8]; decide
      have factor_2_10 : (6 : ZMod 87158321) ^ 1251 = 80883939 := by
        calc
          (6 : ZMod 87158321) ^ 1251 = (6 : ZMod 87158321) ^ (625 + 625 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 625 * (6 : ZMod 87158321) ^ 625) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 80883939 := by rw [factor_2_9]; decide
      have factor_2_11 : (6 : ZMod 87158321) ^ 2503 = 61257691 := by
        calc
          (6 : ZMod 87158321) ^ 2503 = (6 : ZMod 87158321) ^ (1251 + 1251 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 1251 * (6 : ZMod 87158321) ^ 1251) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 61257691 := by rw [factor_2_10]; decide
      have factor_2_12 : (6 : ZMod 87158321) ^ 5006 = 28891112 := by
        calc
          (6 : ZMod 87158321) ^ 5006 = (6 : ZMod 87158321) ^ (2503 + 2503) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 2503 * (6 : ZMod 87158321) ^ 2503 := by rw [pow_add]
          _ = 28891112 := by rw [factor_2_11]; decide
      have factor_2_13 : (6 : ZMod 87158321) ^ 10013 = 67252885 := by
        calc
          (6 : ZMod 87158321) ^ 10013 = (6 : ZMod 87158321) ^ (5006 + 5006 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 5006 * (6 : ZMod 87158321) ^ 5006) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 67252885 := by rw [factor_2_12]; decide
      have factor_2_14 : (6 : ZMod 87158321) ^ 20027 = 39841856 := by
        calc
          (6 : ZMod 87158321) ^ 20027 = (6 : ZMod 87158321) ^ (10013 + 10013 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 10013 * (6 : ZMod 87158321) ^ 10013) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 39841856 := by rw [factor_2_13]; decide
      have factor_2_15 : (6 : ZMod 87158321) ^ 40054 = 40720927 := by
        calc
          (6 : ZMod 87158321) ^ 40054 = (6 : ZMod 87158321) ^ (20027 + 20027) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 20027 * (6 : ZMod 87158321) ^ 20027 := by rw [pow_add]
          _ = 40720927 := by rw [factor_2_14]; decide
      have factor_2_16 : (6 : ZMod 87158321) ^ 80108 = 40365291 := by
        calc
          (6 : ZMod 87158321) ^ 80108 = (6 : ZMod 87158321) ^ (40054 + 40054) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 40054 * (6 : ZMod 87158321) ^ 40054 := by rw [pow_add]
          _ = 40365291 := by rw [factor_2_15]; decide
      have factor_2_17 : (6 : ZMod 87158321) ^ 160217 = 36726934 := by
        calc
          (6 : ZMod 87158321) ^ 160217 = (6 : ZMod 87158321) ^ (80108 + 80108 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 80108 * (6 : ZMod 87158321) ^ 80108) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 36726934 := by rw [factor_2_16]; decide
      have factor_2_18 : (6 : ZMod 87158321) ^ 320435 = 85620798 := by
        calc
          (6 : ZMod 87158321) ^ 320435 = (6 : ZMod 87158321) ^ (160217 + 160217 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 160217 * (6 : ZMod 87158321) ^ 160217) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 85620798 := by rw [factor_2_17]; decide
      have factor_2_19 : (6 : ZMod 87158321) ^ 640870 = 68993367 := by
        calc
          (6 : ZMod 87158321) ^ 640870 = (6 : ZMod 87158321) ^ (320435 + 320435) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 320435 * (6 : ZMod 87158321) ^ 320435 := by rw [pow_add]
          _ = 68993367 := by rw [factor_2_18]; decide
      have factor_2_20 : (6 : ZMod 87158321) ^ 1281740 = 13330538 := by
        calc
          (6 : ZMod 87158321) ^ 1281740 = (6 : ZMod 87158321) ^ (640870 + 640870) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 640870 * (6 : ZMod 87158321) ^ 640870 := by rw [pow_add]
          _ = 13330538 := by rw [factor_2_19]; decide
      have factor_2_21 : (6 : ZMod 87158321) ^ 2563480 = 64806989 := by
        calc
          (6 : ZMod 87158321) ^ 2563480 = (6 : ZMod 87158321) ^ (1281740 + 1281740) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 1281740 * (6 : ZMod 87158321) ^ 1281740 := by rw [pow_add]
          _ = 64806989 := by rw [factor_2_20]; decide
      have factor_2_22 : (6 : ZMod 87158321) ^ 5126960 = 46459213 := by
        calc
          (6 : ZMod 87158321) ^ 5126960 = (6 : ZMod 87158321) ^ (2563480 + 2563480) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 2563480 * (6 : ZMod 87158321) ^ 2563480 := by rw [pow_add]
          _ = 46459213 := by rw [factor_2_21]; decide
      change (6 : ZMod 87158321) ^ 5126960 ≠ 1
      rw [factor_2_22]
      decide
    ·
      have factor_3_0 : (6 : ZMod 87158321) ^ 1 = 6 := by norm_num
      have factor_3_1 : (6 : ZMod 87158321) ^ 2 = 36 := by
        calc
          (6 : ZMod 87158321) ^ 2 = (6 : ZMod 87158321) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 1 * (6 : ZMod 87158321) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_3_0]; decide
      have factor_3_2 : (6 : ZMod 87158321) ^ 4 = 1296 := by
        calc
          (6 : ZMod 87158321) ^ 4 = (6 : ZMod 87158321) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 2 * (6 : ZMod 87158321) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_3_1]; decide
      have factor_3_3 : (6 : ZMod 87158321) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 87158321) ^ 8 = (6 : ZMod 87158321) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 4 * (6 : ZMod 87158321) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_3_2]; decide
      have factor_3_4 : (6 : ZMod 87158321) ^ 17 = 77714931 := by
        calc
          (6 : ZMod 87158321) ^ 17 = (6 : ZMod 87158321) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 8 * (6 : ZMod 87158321) ^ 8) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 77714931 := by rw [factor_3_3]; decide
      have factor_3_5 : (6 : ZMod 87158321) ^ 34 = 9711172 := by
        calc
          (6 : ZMod 87158321) ^ 34 = (6 : ZMod 87158321) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 17 * (6 : ZMod 87158321) ^ 17 := by rw [pow_add]
          _ = 9711172 := by rw [factor_3_4]; decide
      have factor_3_6 : (6 : ZMod 87158321) ^ 69 = 23809157 := by
        calc
          (6 : ZMod 87158321) ^ 69 = (6 : ZMod 87158321) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 34 * (6 : ZMod 87158321) ^ 34) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 23809157 := by rw [factor_3_5]; decide
      have factor_3_7 : (6 : ZMod 87158321) ^ 139 = 56915056 := by
        calc
          (6 : ZMod 87158321) ^ 139 = (6 : ZMod 87158321) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 69 * (6 : ZMod 87158321) ^ 69) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 56915056 := by rw [factor_3_6]; decide
      have factor_3_8 : (6 : ZMod 87158321) ^ 279 = 74205633 := by
        calc
          (6 : ZMod 87158321) ^ 279 = (6 : ZMod 87158321) ^ (139 + 139 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 139 * (6 : ZMod 87158321) ^ 139) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 74205633 := by rw [factor_3_7]; decide
      have factor_3_9 : (6 : ZMod 87158321) ^ 559 = 83437231 := by
        calc
          (6 : ZMod 87158321) ^ 559 = (6 : ZMod 87158321) ^ (279 + 279 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 279 * (6 : ZMod 87158321) ^ 279) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 83437231 := by rw [factor_3_8]; decide
      have factor_3_10 : (6 : ZMod 87158321) ^ 1119 = 14626363 := by
        calc
          (6 : ZMod 87158321) ^ 1119 = (6 : ZMod 87158321) ^ (559 + 559 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 559 * (6 : ZMod 87158321) ^ 559) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 14626363 := by rw [factor_3_9]; decide
      have factor_3_11 : (6 : ZMod 87158321) ^ 2239 = 21004947 := by
        calc
          (6 : ZMod 87158321) ^ 2239 = (6 : ZMod 87158321) ^ (1119 + 1119 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 1119 * (6 : ZMod 87158321) ^ 1119) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 21004947 := by rw [factor_3_10]; decide
      have factor_3_12 : (6 : ZMod 87158321) ^ 4479 = 6535362 := by
        calc
          (6 : ZMod 87158321) ^ 4479 = (6 : ZMod 87158321) ^ (2239 + 2239 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 2239 * (6 : ZMod 87158321) ^ 2239) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 6535362 := by rw [factor_3_11]; decide
      have factor_3_13 : (6 : ZMod 87158321) ^ 8959 = 54355792 := by
        calc
          (6 : ZMod 87158321) ^ 8959 = (6 : ZMod 87158321) ^ (4479 + 4479 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 4479 * (6 : ZMod 87158321) ^ 4479) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 54355792 := by rw [factor_3_12]; decide
      have factor_3_14 : (6 : ZMod 87158321) ^ 17919 = 23235978 := by
        calc
          (6 : ZMod 87158321) ^ 17919 = (6 : ZMod 87158321) ^ (8959 + 8959 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 8959 * (6 : ZMod 87158321) ^ 8959) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 23235978 := by rw [factor_3_13]; decide
      have factor_3_15 : (6 : ZMod 87158321) ^ 35838 = 86983168 := by
        calc
          (6 : ZMod 87158321) ^ 35838 = (6 : ZMod 87158321) ^ (17919 + 17919) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 17919 * (6 : ZMod 87158321) ^ 17919 := by rw [pow_add]
          _ = 86983168 := by rw [factor_3_14]; decide
      have factor_3_16 : (6 : ZMod 87158321) ^ 71676 = 86002738 := by
        calc
          (6 : ZMod 87158321) ^ 71676 = (6 : ZMod 87158321) ^ (35838 + 35838) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 35838 * (6 : ZMod 87158321) ^ 35838 := by rw [pow_add]
          _ = 86002738 := by rw [factor_3_15]; decide
      have factor_3_17 : (6 : ZMod 87158321) ^ 143352 = 19433848 := by
        calc
          (6 : ZMod 87158321) ^ 143352 = (6 : ZMod 87158321) ^ (71676 + 71676) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 71676 * (6 : ZMod 87158321) ^ 71676 := by rw [pow_add]
          _ = 19433848 := by rw [factor_3_16]; decide
      have factor_3_18 : (6 : ZMod 87158321) ^ 286705 = 69179424 := by
        calc
          (6 : ZMod 87158321) ^ 286705 = (6 : ZMod 87158321) ^ (143352 + 143352 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 143352 * (6 : ZMod 87158321) ^ 143352) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 69179424 := by rw [factor_3_17]; decide
      have factor_3_19 : (6 : ZMod 87158321) ^ 573410 = 71418428 := by
        calc
          (6 : ZMod 87158321) ^ 573410 = (6 : ZMod 87158321) ^ (286705 + 286705) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 286705 * (6 : ZMod 87158321) ^ 286705 := by rw [pow_add]
          _ = 71418428 := by rw [factor_3_18]; decide
      have factor_3_20 : (6 : ZMod 87158321) ^ 1146820 = 16225147 := by
        calc
          (6 : ZMod 87158321) ^ 1146820 = (6 : ZMod 87158321) ^ (573410 + 573410) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 573410 * (6 : ZMod 87158321) ^ 573410 := by rw [pow_add]
          _ = 16225147 := by rw [factor_3_19]; decide
      have factor_3_21 : (6 : ZMod 87158321) ^ 2293640 = 49148542 := by
        calc
          (6 : ZMod 87158321) ^ 2293640 = (6 : ZMod 87158321) ^ (1146820 + 1146820) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 1146820 * (6 : ZMod 87158321) ^ 1146820 := by rw [pow_add]
          _ = 49148542 := by rw [factor_3_20]; decide
      have factor_3_22 : (6 : ZMod 87158321) ^ 4587280 = 85225482 := by
        calc
          (6 : ZMod 87158321) ^ 4587280 = (6 : ZMod 87158321) ^ (2293640 + 2293640) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 2293640 * (6 : ZMod 87158321) ^ 2293640 := by rw [pow_add]
          _ = 85225482 := by rw [factor_3_21]; decide
      change (6 : ZMod 87158321) ^ 4587280 ≠ 1
      rw [factor_3_22]
      decide
    ·
      have factor_4_0 : (6 : ZMod 87158321) ^ 1 = 6 := by norm_num
      have factor_4_1 : (6 : ZMod 87158321) ^ 3 = 216 := by
        calc
          (6 : ZMod 87158321) ^ 3 = (6 : ZMod 87158321) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 1 * (6 : ZMod 87158321) ^ 1) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_4_0]; decide
      have factor_4_2 : (6 : ZMod 87158321) ^ 6 = 46656 := by
        calc
          (6 : ZMod 87158321) ^ 6 = (6 : ZMod 87158321) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 3 * (6 : ZMod 87158321) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [factor_4_1]; decide
      have factor_4_3 : (6 : ZMod 87158321) ^ 12 = 84982632 := by
        calc
          (6 : ZMod 87158321) ^ 12 = (6 : ZMod 87158321) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 6 * (6 : ZMod 87158321) ^ 6 := by rw [pow_add]
          _ = 84982632 := by rw [factor_4_2]; decide
      have factor_4_4 : (6 : ZMod 87158321) ^ 25 = 63792303 := by
        calc
          (6 : ZMod 87158321) ^ 25 = (6 : ZMod 87158321) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 12 * (6 : ZMod 87158321) ^ 12) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 63792303 := by rw [factor_4_3]; decide
      have factor_4_5 : (6 : ZMod 87158321) ^ 50 = 5325557 := by
        calc
          (6 : ZMod 87158321) ^ 50 = (6 : ZMod 87158321) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 25 * (6 : ZMod 87158321) ^ 25 := by rw [pow_add]
          _ = 5325557 := by rw [factor_4_4]; decide
      have factor_4_6 : (6 : ZMod 87158321) ^ 100 = 65390207 := by
        calc
          (6 : ZMod 87158321) ^ 100 = (6 : ZMod 87158321) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 50 * (6 : ZMod 87158321) ^ 50 := by rw [pow_add]
          _ = 65390207 := by rw [factor_4_5]; decide
      have factor_4_7 : (6 : ZMod 87158321) ^ 201 = 30207013 := by
        calc
          (6 : ZMod 87158321) ^ 201 = (6 : ZMod 87158321) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 100 * (6 : ZMod 87158321) ^ 100) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 30207013 := by rw [factor_4_6]; decide
      have factor_4_8 : (6 : ZMod 87158321) ^ 403 = 30485036 := by
        calc
          (6 : ZMod 87158321) ^ 403 = (6 : ZMod 87158321) ^ (201 + 201 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 201 * (6 : ZMod 87158321) ^ 201) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 30485036 := by rw [factor_4_7]; decide
      have factor_4_9 : (6 : ZMod 87158321) ^ 807 = 73837803 := by
        calc
          (6 : ZMod 87158321) ^ 807 = (6 : ZMod 87158321) ^ (403 + 403 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 403 * (6 : ZMod 87158321) ^ 403) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 73837803 := by rw [factor_4_8]; decide
      have factor_4_10 : (6 : ZMod 87158321) ^ 1615 = 10136873 := by
        calc
          (6 : ZMod 87158321) ^ 1615 = (6 : ZMod 87158321) ^ (807 + 807 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = ((6 : ZMod 87158321) ^ 807 * (6 : ZMod 87158321) ^ 807) * (6 : ZMod 87158321) := by rw [pow_succ, pow_add]
          _ = 10136873 := by rw [factor_4_9]; decide
      have factor_4_11 : (6 : ZMod 87158321) ^ 3230 = 20091969 := by
        calc
          (6 : ZMod 87158321) ^ 3230 = (6 : ZMod 87158321) ^ (1615 + 1615) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 1615 * (6 : ZMod 87158321) ^ 1615 := by rw [pow_add]
          _ = 20091969 := by rw [factor_4_10]; decide
      have factor_4_12 : (6 : ZMod 87158321) ^ 6460 = 32204027 := by
        calc
          (6 : ZMod 87158321) ^ 6460 = (6 : ZMod 87158321) ^ (3230 + 3230) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 3230 * (6 : ZMod 87158321) ^ 3230 := by rw [pow_add]
          _ = 32204027 := by rw [factor_4_11]; decide
      have factor_4_13 : (6 : ZMod 87158321) ^ 12920 = 53004741 := by
        calc
          (6 : ZMod 87158321) ^ 12920 = (6 : ZMod 87158321) ^ (6460 + 6460) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 6460 * (6 : ZMod 87158321) ^ 6460 := by rw [pow_add]
          _ = 53004741 := by rw [factor_4_12]; decide
      have factor_4_14 : (6 : ZMod 87158321) ^ 25840 = 23477248 := by
        calc
          (6 : ZMod 87158321) ^ 25840 = (6 : ZMod 87158321) ^ (12920 + 12920) :=
            congrArg (fun n : ℕ => (6 : ZMod 87158321) ^ n) (by norm_num)
          _ = (6 : ZMod 87158321) ^ 12920 * (6 : ZMod 87158321) ^ 12920 := by rw [pow_add]
          _ = 23477248 := by rw [factor_4_13]; decide
      change (6 : ZMod 87158321) ^ 25840 ≠ 1
      rw [factor_4_14]
      decide

#print axioms prime_lucas_87158321

end TotientTailPeriodKiller
end Erdos249257
