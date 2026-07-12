import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_308171749 : Nat.Prime 308171749 := by
  apply lucas_primality 308171749 (11 : ZMod 308171749)
  ·
      have fermat_0 : (11 : ZMod 308171749) ^ 1 = 11 := by norm_num
      have fermat_1 : (11 : ZMod 308171749) ^ 2 = 121 := by
        calc
          (11 : ZMod 308171749) ^ 2 = (11 : ZMod 308171749) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 1 * (11 : ZMod 308171749) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [fermat_0]; decide
      have fermat_2 : (11 : ZMod 308171749) ^ 4 = 14641 := by
        calc
          (11 : ZMod 308171749) ^ 4 = (11 : ZMod 308171749) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 2 * (11 : ZMod 308171749) ^ 2 := by rw [pow_add]
          _ = 14641 := by rw [fermat_1]; decide
      have fermat_3 : (11 : ZMod 308171749) ^ 9 = 200745448 := by
        calc
          (11 : ZMod 308171749) ^ 9 = (11 : ZMod 308171749) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 4 * (11 : ZMod 308171749) ^ 4) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 200745448 := by rw [fermat_2]; decide
      have fermat_4 : (11 : ZMod 308171749) ^ 18 = 37082083 := by
        calc
          (11 : ZMod 308171749) ^ 18 = (11 : ZMod 308171749) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 9 * (11 : ZMod 308171749) ^ 9 := by rw [pow_add]
          _ = 37082083 := by rw [fermat_3]; decide
      have fermat_5 : (11 : ZMod 308171749) ^ 36 = 45275949 := by
        calc
          (11 : ZMod 308171749) ^ 36 = (11 : ZMod 308171749) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 18 * (11 : ZMod 308171749) ^ 18 := by rw [pow_add]
          _ = 45275949 := by rw [fermat_4]; decide
      have fermat_6 : (11 : ZMod 308171749) ^ 73 = 106208186 := by
        calc
          (11 : ZMod 308171749) ^ 73 = (11 : ZMod 308171749) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 36 * (11 : ZMod 308171749) ^ 36) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 106208186 := by rw [fermat_5]; decide
      have fermat_7 : (11 : ZMod 308171749) ^ 146 = 291160391 := by
        calc
          (11 : ZMod 308171749) ^ 146 = (11 : ZMod 308171749) ^ (73 + 73) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 73 * (11 : ZMod 308171749) ^ 73 := by rw [pow_add]
          _ = 291160391 := by rw [fermat_6]; decide
      have fermat_8 : (11 : ZMod 308171749) ^ 293 = 15761519 := by
        calc
          (11 : ZMod 308171749) ^ 293 = (11 : ZMod 308171749) ^ (146 + 146 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 146 * (11 : ZMod 308171749) ^ 146) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 15761519 := by rw [fermat_7]; decide
      have fermat_9 : (11 : ZMod 308171749) ^ 587 = 283180614 := by
        calc
          (11 : ZMod 308171749) ^ 587 = (11 : ZMod 308171749) ^ (293 + 293 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 293 * (11 : ZMod 308171749) ^ 293) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 283180614 := by rw [fermat_8]; decide
      have fermat_10 : (11 : ZMod 308171749) ^ 1175 = 232987894 := by
        calc
          (11 : ZMod 308171749) ^ 1175 = (11 : ZMod 308171749) ^ (587 + 587 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 587 * (11 : ZMod 308171749) ^ 587) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 232987894 := by rw [fermat_9]; decide
      have fermat_11 : (11 : ZMod 308171749) ^ 2351 = 158208516 := by
        calc
          (11 : ZMod 308171749) ^ 2351 = (11 : ZMod 308171749) ^ (1175 + 1175 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 1175 * (11 : ZMod 308171749) ^ 1175) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 158208516 := by rw [fermat_10]; decide
      have fermat_12 : (11 : ZMod 308171749) ^ 4702 = 115765486 := by
        calc
          (11 : ZMod 308171749) ^ 4702 = (11 : ZMod 308171749) ^ (2351 + 2351) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 2351 * (11 : ZMod 308171749) ^ 2351 := by rw [pow_add]
          _ = 115765486 := by rw [fermat_11]; decide
      have fermat_13 : (11 : ZMod 308171749) ^ 9404 = 154206039 := by
        calc
          (11 : ZMod 308171749) ^ 9404 = (11 : ZMod 308171749) ^ (4702 + 4702) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 4702 * (11 : ZMod 308171749) ^ 4702 := by rw [pow_add]
          _ = 154206039 := by rw [fermat_12]; decide
      have fermat_14 : (11 : ZMod 308171749) ^ 18809 = 203169865 := by
        calc
          (11 : ZMod 308171749) ^ 18809 = (11 : ZMod 308171749) ^ (9404 + 9404 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 9404 * (11 : ZMod 308171749) ^ 9404) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 203169865 := by rw [fermat_13]; decide
      have fermat_15 : (11 : ZMod 308171749) ^ 37618 = 3815495 := by
        calc
          (11 : ZMod 308171749) ^ 37618 = (11 : ZMod 308171749) ^ (18809 + 18809) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 18809 * (11 : ZMod 308171749) ^ 18809 := by rw [pow_add]
          _ = 3815495 := by rw [fermat_14]; decide
      have fermat_16 : (11 : ZMod 308171749) ^ 75237 = 271738413 := by
        calc
          (11 : ZMod 308171749) ^ 75237 = (11 : ZMod 308171749) ^ (37618 + 37618 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 37618 * (11 : ZMod 308171749) ^ 37618) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 271738413 := by rw [fermat_15]; decide
      have fermat_17 : (11 : ZMod 308171749) ^ 150474 = 105792945 := by
        calc
          (11 : ZMod 308171749) ^ 150474 = (11 : ZMod 308171749) ^ (75237 + 75237) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 75237 * (11 : ZMod 308171749) ^ 75237 := by rw [pow_add]
          _ = 105792945 := by rw [fermat_16]; decide
      have fermat_18 : (11 : ZMod 308171749) ^ 300948 = 146826913 := by
        calc
          (11 : ZMod 308171749) ^ 300948 = (11 : ZMod 308171749) ^ (150474 + 150474) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 150474 * (11 : ZMod 308171749) ^ 150474 := by rw [pow_add]
          _ = 146826913 := by rw [fermat_17]; decide
      have fermat_19 : (11 : ZMod 308171749) ^ 601897 = 73529819 := by
        calc
          (11 : ZMod 308171749) ^ 601897 = (11 : ZMod 308171749) ^ (300948 + 300948 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 300948 * (11 : ZMod 308171749) ^ 300948) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 73529819 := by rw [fermat_18]; decide
      have fermat_20 : (11 : ZMod 308171749) ^ 1203795 = 35179588 := by
        calc
          (11 : ZMod 308171749) ^ 1203795 = (11 : ZMod 308171749) ^ (601897 + 601897 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 601897 * (11 : ZMod 308171749) ^ 601897) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 35179588 := by rw [fermat_19]; decide
      have fermat_21 : (11 : ZMod 308171749) ^ 2407591 = 130458672 := by
        calc
          (11 : ZMod 308171749) ^ 2407591 = (11 : ZMod 308171749) ^ (1203795 + 1203795 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 1203795 * (11 : ZMod 308171749) ^ 1203795) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 130458672 := by rw [fermat_20]; decide
      have fermat_22 : (11 : ZMod 308171749) ^ 4815183 = 158026955 := by
        calc
          (11 : ZMod 308171749) ^ 4815183 = (11 : ZMod 308171749) ^ (2407591 + 2407591 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 2407591 * (11 : ZMod 308171749) ^ 2407591) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 158026955 := by rw [fermat_21]; decide
      have fermat_23 : (11 : ZMod 308171749) ^ 9630367 = 156433879 := by
        calc
          (11 : ZMod 308171749) ^ 9630367 = (11 : ZMod 308171749) ^ (4815183 + 4815183 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 4815183 * (11 : ZMod 308171749) ^ 4815183) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 156433879 := by rw [fermat_22]; decide
      have fermat_24 : (11 : ZMod 308171749) ^ 19260734 = 163671222 := by
        calc
          (11 : ZMod 308171749) ^ 19260734 = (11 : ZMod 308171749) ^ (9630367 + 9630367) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 9630367 * (11 : ZMod 308171749) ^ 9630367 := by rw [pow_add]
          _ = 163671222 := by rw [fermat_23]; decide
      have fermat_25 : (11 : ZMod 308171749) ^ 38521468 = 176234210 := by
        calc
          (11 : ZMod 308171749) ^ 38521468 = (11 : ZMod 308171749) ^ (19260734 + 19260734) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 19260734 * (11 : ZMod 308171749) ^ 19260734 := by rw [pow_add]
          _ = 176234210 := by rw [fermat_24]; decide
      have fermat_26 : (11 : ZMod 308171749) ^ 77042937 = 20017685 := by
        calc
          (11 : ZMod 308171749) ^ 77042937 = (11 : ZMod 308171749) ^ (38521468 + 38521468 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 38521468 * (11 : ZMod 308171749) ^ 38521468) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 20017685 := by rw [fermat_25]; decide
      have fermat_27 : (11 : ZMod 308171749) ^ 154085874 = 308171748 := by
        calc
          (11 : ZMod 308171749) ^ 154085874 = (11 : ZMod 308171749) ^ (77042937 + 77042937) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 77042937 * (11 : ZMod 308171749) ^ 77042937 := by rw [pow_add]
          _ = 308171748 := by rw [fermat_26]; decide
      have fermat_28 : (11 : ZMod 308171749) ^ 308171748 = 1 := by
        calc
          (11 : ZMod 308171749) ^ 308171748 = (11 : ZMod 308171749) ^ (154085874 + 154085874) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 154085874 * (11 : ZMod 308171749) ^ 154085874 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (29, 1), (885551, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (29, 1), (885551, 1)] : List FactorBlock).map factorBlockValue).prod = 308171749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (11 : ZMod 308171749) ^ 1 = 11 := by norm_num
      have factor_0_1 : (11 : ZMod 308171749) ^ 2 = 121 := by
        calc
          (11 : ZMod 308171749) ^ 2 = (11 : ZMod 308171749) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 1 * (11 : ZMod 308171749) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_0_0]; decide
      have factor_0_2 : (11 : ZMod 308171749) ^ 4 = 14641 := by
        calc
          (11 : ZMod 308171749) ^ 4 = (11 : ZMod 308171749) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 2 * (11 : ZMod 308171749) ^ 2 := by rw [pow_add]
          _ = 14641 := by rw [factor_0_1]; decide
      have factor_0_3 : (11 : ZMod 308171749) ^ 9 = 200745448 := by
        calc
          (11 : ZMod 308171749) ^ 9 = (11 : ZMod 308171749) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 4 * (11 : ZMod 308171749) ^ 4) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 200745448 := by rw [factor_0_2]; decide
      have factor_0_4 : (11 : ZMod 308171749) ^ 18 = 37082083 := by
        calc
          (11 : ZMod 308171749) ^ 18 = (11 : ZMod 308171749) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 9 * (11 : ZMod 308171749) ^ 9 := by rw [pow_add]
          _ = 37082083 := by rw [factor_0_3]; decide
      have factor_0_5 : (11 : ZMod 308171749) ^ 36 = 45275949 := by
        calc
          (11 : ZMod 308171749) ^ 36 = (11 : ZMod 308171749) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 18 * (11 : ZMod 308171749) ^ 18 := by rw [pow_add]
          _ = 45275949 := by rw [factor_0_4]; decide
      have factor_0_6 : (11 : ZMod 308171749) ^ 73 = 106208186 := by
        calc
          (11 : ZMod 308171749) ^ 73 = (11 : ZMod 308171749) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 36 * (11 : ZMod 308171749) ^ 36) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 106208186 := by rw [factor_0_5]; decide
      have factor_0_7 : (11 : ZMod 308171749) ^ 146 = 291160391 := by
        calc
          (11 : ZMod 308171749) ^ 146 = (11 : ZMod 308171749) ^ (73 + 73) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 73 * (11 : ZMod 308171749) ^ 73 := by rw [pow_add]
          _ = 291160391 := by rw [factor_0_6]; decide
      have factor_0_8 : (11 : ZMod 308171749) ^ 293 = 15761519 := by
        calc
          (11 : ZMod 308171749) ^ 293 = (11 : ZMod 308171749) ^ (146 + 146 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 146 * (11 : ZMod 308171749) ^ 146) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 15761519 := by rw [factor_0_7]; decide
      have factor_0_9 : (11 : ZMod 308171749) ^ 587 = 283180614 := by
        calc
          (11 : ZMod 308171749) ^ 587 = (11 : ZMod 308171749) ^ (293 + 293 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 293 * (11 : ZMod 308171749) ^ 293) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 283180614 := by rw [factor_0_8]; decide
      have factor_0_10 : (11 : ZMod 308171749) ^ 1175 = 232987894 := by
        calc
          (11 : ZMod 308171749) ^ 1175 = (11 : ZMod 308171749) ^ (587 + 587 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 587 * (11 : ZMod 308171749) ^ 587) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 232987894 := by rw [factor_0_9]; decide
      have factor_0_11 : (11 : ZMod 308171749) ^ 2351 = 158208516 := by
        calc
          (11 : ZMod 308171749) ^ 2351 = (11 : ZMod 308171749) ^ (1175 + 1175 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 1175 * (11 : ZMod 308171749) ^ 1175) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 158208516 := by rw [factor_0_10]; decide
      have factor_0_12 : (11 : ZMod 308171749) ^ 4702 = 115765486 := by
        calc
          (11 : ZMod 308171749) ^ 4702 = (11 : ZMod 308171749) ^ (2351 + 2351) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 2351 * (11 : ZMod 308171749) ^ 2351 := by rw [pow_add]
          _ = 115765486 := by rw [factor_0_11]; decide
      have factor_0_13 : (11 : ZMod 308171749) ^ 9404 = 154206039 := by
        calc
          (11 : ZMod 308171749) ^ 9404 = (11 : ZMod 308171749) ^ (4702 + 4702) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 4702 * (11 : ZMod 308171749) ^ 4702 := by rw [pow_add]
          _ = 154206039 := by rw [factor_0_12]; decide
      have factor_0_14 : (11 : ZMod 308171749) ^ 18809 = 203169865 := by
        calc
          (11 : ZMod 308171749) ^ 18809 = (11 : ZMod 308171749) ^ (9404 + 9404 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 9404 * (11 : ZMod 308171749) ^ 9404) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 203169865 := by rw [factor_0_13]; decide
      have factor_0_15 : (11 : ZMod 308171749) ^ 37618 = 3815495 := by
        calc
          (11 : ZMod 308171749) ^ 37618 = (11 : ZMod 308171749) ^ (18809 + 18809) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 18809 * (11 : ZMod 308171749) ^ 18809 := by rw [pow_add]
          _ = 3815495 := by rw [factor_0_14]; decide
      have factor_0_16 : (11 : ZMod 308171749) ^ 75237 = 271738413 := by
        calc
          (11 : ZMod 308171749) ^ 75237 = (11 : ZMod 308171749) ^ (37618 + 37618 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 37618 * (11 : ZMod 308171749) ^ 37618) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 271738413 := by rw [factor_0_15]; decide
      have factor_0_17 : (11 : ZMod 308171749) ^ 150474 = 105792945 := by
        calc
          (11 : ZMod 308171749) ^ 150474 = (11 : ZMod 308171749) ^ (75237 + 75237) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 75237 * (11 : ZMod 308171749) ^ 75237 := by rw [pow_add]
          _ = 105792945 := by rw [factor_0_16]; decide
      have factor_0_18 : (11 : ZMod 308171749) ^ 300948 = 146826913 := by
        calc
          (11 : ZMod 308171749) ^ 300948 = (11 : ZMod 308171749) ^ (150474 + 150474) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 150474 * (11 : ZMod 308171749) ^ 150474 := by rw [pow_add]
          _ = 146826913 := by rw [factor_0_17]; decide
      have factor_0_19 : (11 : ZMod 308171749) ^ 601897 = 73529819 := by
        calc
          (11 : ZMod 308171749) ^ 601897 = (11 : ZMod 308171749) ^ (300948 + 300948 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 300948 * (11 : ZMod 308171749) ^ 300948) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 73529819 := by rw [factor_0_18]; decide
      have factor_0_20 : (11 : ZMod 308171749) ^ 1203795 = 35179588 := by
        calc
          (11 : ZMod 308171749) ^ 1203795 = (11 : ZMod 308171749) ^ (601897 + 601897 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 601897 * (11 : ZMod 308171749) ^ 601897) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 35179588 := by rw [factor_0_19]; decide
      have factor_0_21 : (11 : ZMod 308171749) ^ 2407591 = 130458672 := by
        calc
          (11 : ZMod 308171749) ^ 2407591 = (11 : ZMod 308171749) ^ (1203795 + 1203795 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 1203795 * (11 : ZMod 308171749) ^ 1203795) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 130458672 := by rw [factor_0_20]; decide
      have factor_0_22 : (11 : ZMod 308171749) ^ 4815183 = 158026955 := by
        calc
          (11 : ZMod 308171749) ^ 4815183 = (11 : ZMod 308171749) ^ (2407591 + 2407591 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 2407591 * (11 : ZMod 308171749) ^ 2407591) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 158026955 := by rw [factor_0_21]; decide
      have factor_0_23 : (11 : ZMod 308171749) ^ 9630367 = 156433879 := by
        calc
          (11 : ZMod 308171749) ^ 9630367 = (11 : ZMod 308171749) ^ (4815183 + 4815183 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 4815183 * (11 : ZMod 308171749) ^ 4815183) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 156433879 := by rw [factor_0_22]; decide
      have factor_0_24 : (11 : ZMod 308171749) ^ 19260734 = 163671222 := by
        calc
          (11 : ZMod 308171749) ^ 19260734 = (11 : ZMod 308171749) ^ (9630367 + 9630367) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 9630367 * (11 : ZMod 308171749) ^ 9630367 := by rw [pow_add]
          _ = 163671222 := by rw [factor_0_23]; decide
      have factor_0_25 : (11 : ZMod 308171749) ^ 38521468 = 176234210 := by
        calc
          (11 : ZMod 308171749) ^ 38521468 = (11 : ZMod 308171749) ^ (19260734 + 19260734) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 19260734 * (11 : ZMod 308171749) ^ 19260734 := by rw [pow_add]
          _ = 176234210 := by rw [factor_0_24]; decide
      have factor_0_26 : (11 : ZMod 308171749) ^ 77042937 = 20017685 := by
        calc
          (11 : ZMod 308171749) ^ 77042937 = (11 : ZMod 308171749) ^ (38521468 + 38521468 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 38521468 * (11 : ZMod 308171749) ^ 38521468) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 20017685 := by rw [factor_0_25]; decide
      have factor_0_27 : (11 : ZMod 308171749) ^ 154085874 = 308171748 := by
        calc
          (11 : ZMod 308171749) ^ 154085874 = (11 : ZMod 308171749) ^ (77042937 + 77042937) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 77042937 * (11 : ZMod 308171749) ^ 77042937 := by rw [pow_add]
          _ = 308171748 := by rw [factor_0_26]; decide
      change (11 : ZMod 308171749) ^ 154085874 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (11 : ZMod 308171749) ^ 1 = 11 := by norm_num
      have factor_1_1 : (11 : ZMod 308171749) ^ 3 = 1331 := by
        calc
          (11 : ZMod 308171749) ^ 3 = (11 : ZMod 308171749) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 1 * (11 : ZMod 308171749) ^ 1) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 1331 := by rw [factor_1_0]; decide
      have factor_1_2 : (11 : ZMod 308171749) ^ 6 = 1771561 := by
        calc
          (11 : ZMod 308171749) ^ 6 = (11 : ZMod 308171749) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 3 * (11 : ZMod 308171749) ^ 3 := by rw [pow_add]
          _ = 1771561 := by rw [factor_1_1]; decide
      have factor_1_3 : (11 : ZMod 308171749) ^ 12 = 7284905 := by
        calc
          (11 : ZMod 308171749) ^ 12 = (11 : ZMod 308171749) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 6 * (11 : ZMod 308171749) ^ 6 := by rw [pow_add]
          _ = 7284905 := by rw [factor_1_2]; decide
      have factor_1_4 : (11 : ZMod 308171749) ^ 24 = 200307233 := by
        calc
          (11 : ZMod 308171749) ^ 24 = (11 : ZMod 308171749) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 12 * (11 : ZMod 308171749) ^ 12 := by rw [pow_add]
          _ = 200307233 := by rw [factor_1_3]; decide
      have factor_1_5 : (11 : ZMod 308171749) ^ 48 = 3214878 := by
        calc
          (11 : ZMod 308171749) ^ 48 = (11 : ZMod 308171749) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 24 * (11 : ZMod 308171749) ^ 24 := by rw [pow_add]
          _ = 3214878 := by rw [factor_1_4]; decide
      have factor_1_6 : (11 : ZMod 308171749) ^ 97 = 48977891 := by
        calc
          (11 : ZMod 308171749) ^ 97 = (11 : ZMod 308171749) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 48 * (11 : ZMod 308171749) ^ 48) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 48977891 := by rw [factor_1_5]; decide
      have factor_1_7 : (11 : ZMod 308171749) ^ 195 = 73825830 := by
        calc
          (11 : ZMod 308171749) ^ 195 = (11 : ZMod 308171749) ^ (97 + 97 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 97 * (11 : ZMod 308171749) ^ 97) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 73825830 := by rw [factor_1_6]; decide
      have factor_1_8 : (11 : ZMod 308171749) ^ 391 = 161923316 := by
        calc
          (11 : ZMod 308171749) ^ 391 = (11 : ZMod 308171749) ^ (195 + 195 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 195 * (11 : ZMod 308171749) ^ 195) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 161923316 := by rw [factor_1_7]; decide
      have factor_1_9 : (11 : ZMod 308171749) ^ 783 = 31556877 := by
        calc
          (11 : ZMod 308171749) ^ 783 = (11 : ZMod 308171749) ^ (391 + 391 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 391 * (11 : ZMod 308171749) ^ 391) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 31556877 := by rw [factor_1_8]; decide
      have factor_1_10 : (11 : ZMod 308171749) ^ 1567 = 159987936 := by
        calc
          (11 : ZMod 308171749) ^ 1567 = (11 : ZMod 308171749) ^ (783 + 783 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 783 * (11 : ZMod 308171749) ^ 783) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 159987936 := by rw [factor_1_9]; decide
      have factor_1_11 : (11 : ZMod 308171749) ^ 3134 = 59258630 := by
        calc
          (11 : ZMod 308171749) ^ 3134 = (11 : ZMod 308171749) ^ (1567 + 1567) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 1567 * (11 : ZMod 308171749) ^ 1567 := by rw [pow_add]
          _ = 59258630 := by rw [factor_1_10]; decide
      have factor_1_12 : (11 : ZMod 308171749) ^ 6269 = 37119513 := by
        calc
          (11 : ZMod 308171749) ^ 6269 = (11 : ZMod 308171749) ^ (3134 + 3134 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 3134 * (11 : ZMod 308171749) ^ 3134) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 37119513 := by rw [factor_1_11]; decide
      have factor_1_13 : (11 : ZMod 308171749) ^ 12539 = 298475906 := by
        calc
          (11 : ZMod 308171749) ^ 12539 = (11 : ZMod 308171749) ^ (6269 + 6269 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 6269 * (11 : ZMod 308171749) ^ 6269) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 298475906 := by rw [factor_1_12]; decide
      have factor_1_14 : (11 : ZMod 308171749) ^ 25079 = 116312245 := by
        calc
          (11 : ZMod 308171749) ^ 25079 = (11 : ZMod 308171749) ^ (12539 + 12539 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 12539 * (11 : ZMod 308171749) ^ 12539) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 116312245 := by rw [factor_1_13]; decide
      have factor_1_15 : (11 : ZMod 308171749) ^ 50158 = 100163871 := by
        calc
          (11 : ZMod 308171749) ^ 50158 = (11 : ZMod 308171749) ^ (25079 + 25079) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 25079 * (11 : ZMod 308171749) ^ 25079 := by rw [pow_add]
          _ = 100163871 := by rw [factor_1_14]; decide
      have factor_1_16 : (11 : ZMod 308171749) ^ 100316 = 114729266 := by
        calc
          (11 : ZMod 308171749) ^ 100316 = (11 : ZMod 308171749) ^ (50158 + 50158) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 50158 * (11 : ZMod 308171749) ^ 50158 := by rw [pow_add]
          _ = 114729266 := by rw [factor_1_15]; decide
      have factor_1_17 : (11 : ZMod 308171749) ^ 200632 = 157431316 := by
        calc
          (11 : ZMod 308171749) ^ 200632 = (11 : ZMod 308171749) ^ (100316 + 100316) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 100316 * (11 : ZMod 308171749) ^ 100316 := by rw [pow_add]
          _ = 157431316 := by rw [factor_1_16]; decide
      have factor_1_18 : (11 : ZMod 308171749) ^ 401265 = 3992323 := by
        calc
          (11 : ZMod 308171749) ^ 401265 = (11 : ZMod 308171749) ^ (200632 + 200632 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 200632 * (11 : ZMod 308171749) ^ 200632) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 3992323 := by rw [factor_1_17]; decide
      have factor_1_19 : (11 : ZMod 308171749) ^ 802530 = 78049 := by
        calc
          (11 : ZMod 308171749) ^ 802530 = (11 : ZMod 308171749) ^ (401265 + 401265) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 401265 * (11 : ZMod 308171749) ^ 401265 := by rw [pow_add]
          _ = 78049 := by rw [factor_1_18]; decide
      have factor_1_20 : (11 : ZMod 308171749) ^ 1605061 = 134840878 := by
        calc
          (11 : ZMod 308171749) ^ 1605061 = (11 : ZMod 308171749) ^ (802530 + 802530 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 802530 * (11 : ZMod 308171749) ^ 802530) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 134840878 := by rw [factor_1_19]; decide
      have factor_1_21 : (11 : ZMod 308171749) ^ 3210122 = 68313154 := by
        calc
          (11 : ZMod 308171749) ^ 3210122 = (11 : ZMod 308171749) ^ (1605061 + 1605061) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 1605061 * (11 : ZMod 308171749) ^ 1605061 := by rw [pow_add]
          _ = 68313154 := by rw [factor_1_20]; decide
      have factor_1_22 : (11 : ZMod 308171749) ^ 6420244 = 302962852 := by
        calc
          (11 : ZMod 308171749) ^ 6420244 = (11 : ZMod 308171749) ^ (3210122 + 3210122) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 3210122 * (11 : ZMod 308171749) ^ 3210122 := by rw [pow_add]
          _ = 302962852 := by rw [factor_1_21]; decide
      have factor_1_23 : (11 : ZMod 308171749) ^ 12840489 = 203879430 := by
        calc
          (11 : ZMod 308171749) ^ 12840489 = (11 : ZMod 308171749) ^ (6420244 + 6420244 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 6420244 * (11 : ZMod 308171749) ^ 6420244) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 203879430 := by rw [factor_1_22]; decide
      have factor_1_24 : (11 : ZMod 308171749) ^ 25680979 = 180888904 := by
        calc
          (11 : ZMod 308171749) ^ 25680979 = (11 : ZMod 308171749) ^ (12840489 + 12840489 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 12840489 * (11 : ZMod 308171749) ^ 12840489) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 180888904 := by rw [factor_1_23]; decide
      have factor_1_25 : (11 : ZMod 308171749) ^ 51361958 = 36359858 := by
        calc
          (11 : ZMod 308171749) ^ 51361958 = (11 : ZMod 308171749) ^ (25680979 + 25680979) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 25680979 * (11 : ZMod 308171749) ^ 25680979 := by rw [pow_add]
          _ = 36359858 := by rw [factor_1_24]; decide
      have factor_1_26 : (11 : ZMod 308171749) ^ 102723916 = 36359857 := by
        calc
          (11 : ZMod 308171749) ^ 102723916 = (11 : ZMod 308171749) ^ (51361958 + 51361958) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 51361958 * (11 : ZMod 308171749) ^ 51361958 := by rw [pow_add]
          _ = 36359857 := by rw [factor_1_25]; decide
      change (11 : ZMod 308171749) ^ 102723916 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (11 : ZMod 308171749) ^ 1 = 11 := by norm_num
      have factor_2_1 : (11 : ZMod 308171749) ^ 2 = 121 := by
        calc
          (11 : ZMod 308171749) ^ 2 = (11 : ZMod 308171749) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 1 * (11 : ZMod 308171749) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_2_0]; decide
      have factor_2_2 : (11 : ZMod 308171749) ^ 5 = 161051 := by
        calc
          (11 : ZMod 308171749) ^ 5 = (11 : ZMod 308171749) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 2 * (11 : ZMod 308171749) ^ 2) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 161051 := by rw [factor_2_1]; decide
      have factor_2_3 : (11 : ZMod 308171749) ^ 10 = 50997685 := by
        calc
          (11 : ZMod 308171749) ^ 10 = (11 : ZMod 308171749) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 5 * (11 : ZMod 308171749) ^ 5 := by rw [pow_add]
          _ = 50997685 := by rw [factor_2_2]; decide
      have factor_2_4 : (11 : ZMod 308171749) ^ 20 = 172527557 := by
        calc
          (11 : ZMod 308171749) ^ 20 = (11 : ZMod 308171749) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 10 * (11 : ZMod 308171749) ^ 10 := by rw [pow_add]
          _ = 172527557 := by rw [factor_2_3]; decide
      have factor_2_5 : (11 : ZMod 308171749) ^ 40 = 7737210 := by
        calc
          (11 : ZMod 308171749) ^ 40 = (11 : ZMod 308171749) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 20 * (11 : ZMod 308171749) ^ 20 := by rw [pow_add]
          _ = 7737210 := by rw [factor_2_4]; decide
      have factor_2_6 : (11 : ZMod 308171749) ^ 81 = 123211673 := by
        calc
          (11 : ZMod 308171749) ^ 81 = (11 : ZMod 308171749) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 40 * (11 : ZMod 308171749) ^ 40) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 123211673 := by rw [factor_2_5]; decide
      have factor_2_7 : (11 : ZMod 308171749) ^ 162 = 34720048 := by
        calc
          (11 : ZMod 308171749) ^ 162 = (11 : ZMod 308171749) ^ (81 + 81) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 81 * (11 : ZMod 308171749) ^ 81 := by rw [pow_add]
          _ = 34720048 := by rw [factor_2_6]; decide
      have factor_2_8 : (11 : ZMod 308171749) ^ 324 = 139124024 := by
        calc
          (11 : ZMod 308171749) ^ 324 = (11 : ZMod 308171749) ^ (162 + 162) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 162 * (11 : ZMod 308171749) ^ 162 := by rw [pow_add]
          _ = 139124024 := by rw [factor_2_7]; decide
      have factor_2_9 : (11 : ZMod 308171749) ^ 648 = 10352566 := by
        calc
          (11 : ZMod 308171749) ^ 648 = (11 : ZMod 308171749) ^ (324 + 324) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 324 * (11 : ZMod 308171749) ^ 324 := by rw [pow_add]
          _ = 10352566 := by rw [factor_2_8]; decide
      have factor_2_10 : (11 : ZMod 308171749) ^ 1297 = 177321233 := by
        calc
          (11 : ZMod 308171749) ^ 1297 = (11 : ZMod 308171749) ^ (648 + 648 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 648 * (11 : ZMod 308171749) ^ 648) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 177321233 := by rw [factor_2_9]; decide
      have factor_2_11 : (11 : ZMod 308171749) ^ 2594 = 34911971 := by
        calc
          (11 : ZMod 308171749) ^ 2594 = (11 : ZMod 308171749) ^ (1297 + 1297) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 1297 * (11 : ZMod 308171749) ^ 1297 := by rw [pow_add]
          _ = 34911971 := by rw [factor_2_10]; decide
      have factor_2_12 : (11 : ZMod 308171749) ^ 5188 = 257211176 := by
        calc
          (11 : ZMod 308171749) ^ 5188 = (11 : ZMod 308171749) ^ (2594 + 2594) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 2594 * (11 : ZMod 308171749) ^ 2594 := by rw [pow_add]
          _ = 257211176 := by rw [factor_2_11]; decide
      have factor_2_13 : (11 : ZMod 308171749) ^ 10377 = 26127964 := by
        calc
          (11 : ZMod 308171749) ^ 10377 = (11 : ZMod 308171749) ^ (5188 + 5188 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 5188 * (11 : ZMod 308171749) ^ 5188) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 26127964 := by rw [factor_2_12]; decide
      have factor_2_14 : (11 : ZMod 308171749) ^ 20755 = 128709007 := by
        calc
          (11 : ZMod 308171749) ^ 20755 = (11 : ZMod 308171749) ^ (10377 + 10377 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 10377 * (11 : ZMod 308171749) ^ 10377) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 128709007 := by rw [factor_2_13]; decide
      have factor_2_15 : (11 : ZMod 308171749) ^ 41510 = 55871315 := by
        calc
          (11 : ZMod 308171749) ^ 41510 = (11 : ZMod 308171749) ^ (20755 + 20755) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 20755 * (11 : ZMod 308171749) ^ 20755 := by rw [pow_add]
          _ = 55871315 := by rw [factor_2_14]; decide
      have factor_2_16 : (11 : ZMod 308171749) ^ 83020 = 296699653 := by
        calc
          (11 : ZMod 308171749) ^ 83020 = (11 : ZMod 308171749) ^ (41510 + 41510) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 41510 * (11 : ZMod 308171749) ^ 41510 := by rw [pow_add]
          _ = 296699653 := by rw [factor_2_15]; decide
      have factor_2_17 : (11 : ZMod 308171749) ^ 166040 = 234990029 := by
        calc
          (11 : ZMod 308171749) ^ 166040 = (11 : ZMod 308171749) ^ (83020 + 83020) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 83020 * (11 : ZMod 308171749) ^ 83020 := by rw [pow_add]
          _ = 234990029 := by rw [factor_2_16]; decide
      have factor_2_18 : (11 : ZMod 308171749) ^ 332081 = 15193450 := by
        calc
          (11 : ZMod 308171749) ^ 332081 = (11 : ZMod 308171749) ^ (166040 + 166040 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 166040 * (11 : ZMod 308171749) ^ 166040) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 15193450 := by rw [factor_2_17]; decide
      have factor_2_19 : (11 : ZMod 308171749) ^ 664163 = 303741973 := by
        calc
          (11 : ZMod 308171749) ^ 664163 = (11 : ZMod 308171749) ^ (332081 + 332081 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 332081 * (11 : ZMod 308171749) ^ 332081) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 303741973 := by rw [factor_2_18]; decide
      have factor_2_20 : (11 : ZMod 308171749) ^ 1328326 = 79292601 := by
        calc
          (11 : ZMod 308171749) ^ 1328326 = (11 : ZMod 308171749) ^ (664163 + 664163) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 664163 * (11 : ZMod 308171749) ^ 664163 := by rw [pow_add]
          _ = 79292601 := by rw [factor_2_19]; decide
      have factor_2_21 : (11 : ZMod 308171749) ^ 2656653 = 266016087 := by
        calc
          (11 : ZMod 308171749) ^ 2656653 = (11 : ZMod 308171749) ^ (1328326 + 1328326 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 1328326 * (11 : ZMod 308171749) ^ 1328326) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 266016087 := by rw [factor_2_20]; decide
      have factor_2_22 : (11 : ZMod 308171749) ^ 5313306 = 20764083 := by
        calc
          (11 : ZMod 308171749) ^ 5313306 = (11 : ZMod 308171749) ^ (2656653 + 2656653) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 2656653 * (11 : ZMod 308171749) ^ 2656653 := by rw [pow_add]
          _ = 20764083 := by rw [factor_2_21]; decide
      have factor_2_23 : (11 : ZMod 308171749) ^ 10626612 = 73735937 := by
        calc
          (11 : ZMod 308171749) ^ 10626612 = (11 : ZMod 308171749) ^ (5313306 + 5313306) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 5313306 * (11 : ZMod 308171749) ^ 5313306 := by rw [pow_add]
          _ = 73735937 := by rw [factor_2_22]; decide
      change (11 : ZMod 308171749) ^ 10626612 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (11 : ZMod 308171749) ^ 1 = 11 := by norm_num
      have factor_3_1 : (11 : ZMod 308171749) ^ 2 = 121 := by
        calc
          (11 : ZMod 308171749) ^ 2 = (11 : ZMod 308171749) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 1 * (11 : ZMod 308171749) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_3_0]; decide
      have factor_3_2 : (11 : ZMod 308171749) ^ 5 = 161051 := by
        calc
          (11 : ZMod 308171749) ^ 5 = (11 : ZMod 308171749) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 2 * (11 : ZMod 308171749) ^ 2) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 161051 := by rw [factor_3_1]; decide
      have factor_3_3 : (11 : ZMod 308171749) ^ 10 = 50997685 := by
        calc
          (11 : ZMod 308171749) ^ 10 = (11 : ZMod 308171749) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 5 * (11 : ZMod 308171749) ^ 5 := by rw [pow_add]
          _ = 50997685 := by rw [factor_3_2]; decide
      have factor_3_4 : (11 : ZMod 308171749) ^ 21 = 48772633 := by
        calc
          (11 : ZMod 308171749) ^ 21 = (11 : ZMod 308171749) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 10 * (11 : ZMod 308171749) ^ 10) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 48772633 := by rw [factor_3_3]; decide
      have factor_3_5 : (11 : ZMod 308171749) ^ 43 = 128558793 := by
        calc
          (11 : ZMod 308171749) ^ 43 = (11 : ZMod 308171749) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 21 * (11 : ZMod 308171749) ^ 21) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 128558793 := by rw [factor_3_4]; decide
      have factor_3_6 : (11 : ZMod 308171749) ^ 87 = 177501849 := by
        calc
          (11 : ZMod 308171749) ^ 87 = (11 : ZMod 308171749) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = ((11 : ZMod 308171749) ^ 43 * (11 : ZMod 308171749) ^ 43) * (11 : ZMod 308171749) := by rw [pow_succ, pow_add]
          _ = 177501849 := by rw [factor_3_5]; decide
      have factor_3_7 : (11 : ZMod 308171749) ^ 174 = 288283690 := by
        calc
          (11 : ZMod 308171749) ^ 174 = (11 : ZMod 308171749) ^ (87 + 87) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 87 * (11 : ZMod 308171749) ^ 87 := by rw [pow_add]
          _ = 288283690 := by rw [factor_3_6]; decide
      have factor_3_8 : (11 : ZMod 308171749) ^ 348 = 149006969 := by
        calc
          (11 : ZMod 308171749) ^ 348 = (11 : ZMod 308171749) ^ (174 + 174) :=
            congrArg (fun n : ℕ => (11 : ZMod 308171749) ^ n) (by norm_num)
          _ = (11 : ZMod 308171749) ^ 174 * (11 : ZMod 308171749) ^ 174 := by rw [pow_add]
          _ = 149006969 := by rw [factor_3_7]; decide
      change (11 : ZMod 308171749) ^ 348 ≠ 1
      rw [factor_3_8]
      decide

#print axioms prime_lucas_308171749

end TotientTailPeriodKiller
end Erdos249257
