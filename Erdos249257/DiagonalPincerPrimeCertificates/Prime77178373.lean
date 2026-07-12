import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=32 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_77178373 : Nat.Prime 77178373 := by
  apply lucas_primality 77178373 (2 : ZMod 77178373)
  ·
      have fermat_0 : (2 : ZMod 77178373) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 77178373) ^ 2 = 4 := by
        calc
          (2 : ZMod 77178373) ^ 2 = (2 : ZMod 77178373) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 1 * (2 : ZMod 77178373) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 77178373) ^ 4 = 16 := by
        calc
          (2 : ZMod 77178373) ^ 4 = (2 : ZMod 77178373) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 2 * (2 : ZMod 77178373) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 77178373) ^ 9 = 512 := by
        calc
          (2 : ZMod 77178373) ^ 9 = (2 : ZMod 77178373) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 4 * (2 : ZMod 77178373) ^ 4) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 77178373) ^ 18 = 262144 := by
        calc
          (2 : ZMod 77178373) ^ 18 = (2 : ZMod 77178373) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 9 * (2 : ZMod 77178373) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 77178373) ^ 36 = 30724766 := by
        calc
          (2 : ZMod 77178373) ^ 36 = (2 : ZMod 77178373) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 18 * (2 : ZMod 77178373) ^ 18 := by rw [pow_add]
          _ = 30724766 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 77178373) ^ 73 = 3438093 := by
        calc
          (2 : ZMod 77178373) ^ 73 = (2 : ZMod 77178373) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 36 * (2 : ZMod 77178373) ^ 36) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 3438093 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 77178373) ^ 147 = 73627803 := by
        calc
          (2 : ZMod 77178373) ^ 147 = (2 : ZMod 77178373) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 73 * (2 : ZMod 77178373) ^ 73) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 73627803 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 77178373) ^ 294 = 343961 := by
        calc
          (2 : ZMod 77178373) ^ 294 = (2 : ZMod 77178373) ^ (147 + 147) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 147 * (2 : ZMod 77178373) ^ 147 := by rw [pow_add]
          _ = 343961 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 77178373) ^ 588 = 71902085 := by
        calc
          (2 : ZMod 77178373) ^ 588 = (2 : ZMod 77178373) ^ (294 + 294) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 294 * (2 : ZMod 77178373) ^ 294 := by rw [pow_add]
          _ = 71902085 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 77178373) ^ 1177 = 22376363 := by
        calc
          (2 : ZMod 77178373) ^ 1177 = (2 : ZMod 77178373) ^ (588 + 588 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 588 * (2 : ZMod 77178373) ^ 588) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 22376363 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 77178373) ^ 2355 = 37611771 := by
        calc
          (2 : ZMod 77178373) ^ 2355 = (2 : ZMod 77178373) ^ (1177 + 1177 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 1177 * (2 : ZMod 77178373) ^ 1177) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 37611771 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 77178373) ^ 4710 = 7864053 := by
        calc
          (2 : ZMod 77178373) ^ 4710 = (2 : ZMod 77178373) ^ (2355 + 2355) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 2355 * (2 : ZMod 77178373) ^ 2355 := by rw [pow_add]
          _ = 7864053 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 77178373) ^ 9421 = 58355207 := by
        calc
          (2 : ZMod 77178373) ^ 9421 = (2 : ZMod 77178373) ^ (4710 + 4710 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 4710 * (2 : ZMod 77178373) ^ 4710) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 58355207 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 77178373) ^ 18842 = 22997934 := by
        calc
          (2 : ZMod 77178373) ^ 18842 = (2 : ZMod 77178373) ^ (9421 + 9421) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 9421 * (2 : ZMod 77178373) ^ 9421 := by rw [pow_add]
          _ = 22997934 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 77178373) ^ 37684 = 34531896 := by
        calc
          (2 : ZMod 77178373) ^ 37684 = (2 : ZMod 77178373) ^ (18842 + 18842) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 18842 * (2 : ZMod 77178373) ^ 18842 := by rw [pow_add]
          _ = 34531896 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 77178373) ^ 75369 = 37567389 := by
        calc
          (2 : ZMod 77178373) ^ 75369 = (2 : ZMod 77178373) ^ (37684 + 37684 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 37684 * (2 : ZMod 77178373) ^ 37684) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 37567389 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 77178373) ^ 150739 = 40791311 := by
        calc
          (2 : ZMod 77178373) ^ 150739 = (2 : ZMod 77178373) ^ (75369 + 75369 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 75369 * (2 : ZMod 77178373) ^ 75369) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 40791311 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 77178373) ^ 301478 = 61486571 := by
        calc
          (2 : ZMod 77178373) ^ 301478 = (2 : ZMod 77178373) ^ (150739 + 150739) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 150739 * (2 : ZMod 77178373) ^ 150739 := by rw [pow_add]
          _ = 61486571 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 77178373) ^ 602956 = 67544949 := by
        calc
          (2 : ZMod 77178373) ^ 602956 = (2 : ZMod 77178373) ^ (301478 + 301478) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 301478 * (2 : ZMod 77178373) ^ 301478 := by rw [pow_add]
          _ = 67544949 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 77178373) ^ 1205912 = 32063418 := by
        calc
          (2 : ZMod 77178373) ^ 1205912 = (2 : ZMod 77178373) ^ (602956 + 602956) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 602956 * (2 : ZMod 77178373) ^ 602956 := by rw [pow_add]
          _ = 32063418 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 77178373) ^ 2411824 = 75388686 := by
        calc
          (2 : ZMod 77178373) ^ 2411824 = (2 : ZMod 77178373) ^ (1205912 + 1205912) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 1205912 * (2 : ZMod 77178373) ^ 1205912 := by rw [pow_add]
          _ = 75388686 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 77178373) ^ 4823648 = 77078469 := by
        calc
          (2 : ZMod 77178373) ^ 4823648 = (2 : ZMod 77178373) ^ (2411824 + 2411824) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 2411824 * (2 : ZMod 77178373) ^ 2411824 := by rw [pow_add]
          _ = 77078469 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 77178373) ^ 9647296 = 24799099 := by
        calc
          (2 : ZMod 77178373) ^ 9647296 = (2 : ZMod 77178373) ^ (4823648 + 4823648) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 4823648 * (2 : ZMod 77178373) ^ 4823648 := by rw [pow_add]
          _ = 24799099 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 77178373) ^ 19294593 = 49598197 := by
        calc
          (2 : ZMod 77178373) ^ 19294593 = (2 : ZMod 77178373) ^ (9647296 + 9647296 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 9647296 * (2 : ZMod 77178373) ^ 9647296) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 49598197 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 77178373) ^ 38589186 = 77178372 := by
        calc
          (2 : ZMod 77178373) ^ 38589186 = (2 : ZMod 77178373) ^ (19294593 + 19294593) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 19294593 * (2 : ZMod 77178373) ^ 19294593 := by rw [pow_add]
          _ = 77178372 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 77178373) ^ 77178372 = 1 := by
        calc
          (2 : ZMod 77178373) ^ 77178372 = (2 : ZMod 77178373) ^ (38589186 + 38589186) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 38589186 * (2 : ZMod 77178373) ^ 38589186 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (59, 1), (67, 1), (1627, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (59, 1), (67, 1), (1627, 1)] : List FactorBlock).map factorBlockValue).prod = 77178373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 77178373) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 77178373) ^ 2 = 4 := by
        calc
          (2 : ZMod 77178373) ^ 2 = (2 : ZMod 77178373) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 1 * (2 : ZMod 77178373) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 77178373) ^ 4 = 16 := by
        calc
          (2 : ZMod 77178373) ^ 4 = (2 : ZMod 77178373) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 2 * (2 : ZMod 77178373) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 77178373) ^ 9 = 512 := by
        calc
          (2 : ZMod 77178373) ^ 9 = (2 : ZMod 77178373) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 4 * (2 : ZMod 77178373) ^ 4) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 77178373) ^ 18 = 262144 := by
        calc
          (2 : ZMod 77178373) ^ 18 = (2 : ZMod 77178373) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 9 * (2 : ZMod 77178373) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 77178373) ^ 36 = 30724766 := by
        calc
          (2 : ZMod 77178373) ^ 36 = (2 : ZMod 77178373) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 18 * (2 : ZMod 77178373) ^ 18 := by rw [pow_add]
          _ = 30724766 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 77178373) ^ 73 = 3438093 := by
        calc
          (2 : ZMod 77178373) ^ 73 = (2 : ZMod 77178373) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 36 * (2 : ZMod 77178373) ^ 36) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 3438093 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 77178373) ^ 147 = 73627803 := by
        calc
          (2 : ZMod 77178373) ^ 147 = (2 : ZMod 77178373) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 73 * (2 : ZMod 77178373) ^ 73) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 73627803 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 77178373) ^ 294 = 343961 := by
        calc
          (2 : ZMod 77178373) ^ 294 = (2 : ZMod 77178373) ^ (147 + 147) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 147 * (2 : ZMod 77178373) ^ 147 := by rw [pow_add]
          _ = 343961 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 77178373) ^ 588 = 71902085 := by
        calc
          (2 : ZMod 77178373) ^ 588 = (2 : ZMod 77178373) ^ (294 + 294) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 294 * (2 : ZMod 77178373) ^ 294 := by rw [pow_add]
          _ = 71902085 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 77178373) ^ 1177 = 22376363 := by
        calc
          (2 : ZMod 77178373) ^ 1177 = (2 : ZMod 77178373) ^ (588 + 588 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 588 * (2 : ZMod 77178373) ^ 588) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 22376363 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 77178373) ^ 2355 = 37611771 := by
        calc
          (2 : ZMod 77178373) ^ 2355 = (2 : ZMod 77178373) ^ (1177 + 1177 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 1177 * (2 : ZMod 77178373) ^ 1177) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 37611771 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 77178373) ^ 4710 = 7864053 := by
        calc
          (2 : ZMod 77178373) ^ 4710 = (2 : ZMod 77178373) ^ (2355 + 2355) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 2355 * (2 : ZMod 77178373) ^ 2355 := by rw [pow_add]
          _ = 7864053 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 77178373) ^ 9421 = 58355207 := by
        calc
          (2 : ZMod 77178373) ^ 9421 = (2 : ZMod 77178373) ^ (4710 + 4710 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 4710 * (2 : ZMod 77178373) ^ 4710) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 58355207 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 77178373) ^ 18842 = 22997934 := by
        calc
          (2 : ZMod 77178373) ^ 18842 = (2 : ZMod 77178373) ^ (9421 + 9421) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 9421 * (2 : ZMod 77178373) ^ 9421 := by rw [pow_add]
          _ = 22997934 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 77178373) ^ 37684 = 34531896 := by
        calc
          (2 : ZMod 77178373) ^ 37684 = (2 : ZMod 77178373) ^ (18842 + 18842) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 18842 * (2 : ZMod 77178373) ^ 18842 := by rw [pow_add]
          _ = 34531896 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 77178373) ^ 75369 = 37567389 := by
        calc
          (2 : ZMod 77178373) ^ 75369 = (2 : ZMod 77178373) ^ (37684 + 37684 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 37684 * (2 : ZMod 77178373) ^ 37684) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 37567389 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 77178373) ^ 150739 = 40791311 := by
        calc
          (2 : ZMod 77178373) ^ 150739 = (2 : ZMod 77178373) ^ (75369 + 75369 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 75369 * (2 : ZMod 77178373) ^ 75369) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 40791311 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 77178373) ^ 301478 = 61486571 := by
        calc
          (2 : ZMod 77178373) ^ 301478 = (2 : ZMod 77178373) ^ (150739 + 150739) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 150739 * (2 : ZMod 77178373) ^ 150739 := by rw [pow_add]
          _ = 61486571 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 77178373) ^ 602956 = 67544949 := by
        calc
          (2 : ZMod 77178373) ^ 602956 = (2 : ZMod 77178373) ^ (301478 + 301478) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 301478 * (2 : ZMod 77178373) ^ 301478 := by rw [pow_add]
          _ = 67544949 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 77178373) ^ 1205912 = 32063418 := by
        calc
          (2 : ZMod 77178373) ^ 1205912 = (2 : ZMod 77178373) ^ (602956 + 602956) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 602956 * (2 : ZMod 77178373) ^ 602956 := by rw [pow_add]
          _ = 32063418 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 77178373) ^ 2411824 = 75388686 := by
        calc
          (2 : ZMod 77178373) ^ 2411824 = (2 : ZMod 77178373) ^ (1205912 + 1205912) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 1205912 * (2 : ZMod 77178373) ^ 1205912 := by rw [pow_add]
          _ = 75388686 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 77178373) ^ 4823648 = 77078469 := by
        calc
          (2 : ZMod 77178373) ^ 4823648 = (2 : ZMod 77178373) ^ (2411824 + 2411824) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 2411824 * (2 : ZMod 77178373) ^ 2411824 := by rw [pow_add]
          _ = 77078469 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 77178373) ^ 9647296 = 24799099 := by
        calc
          (2 : ZMod 77178373) ^ 9647296 = (2 : ZMod 77178373) ^ (4823648 + 4823648) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 4823648 * (2 : ZMod 77178373) ^ 4823648 := by rw [pow_add]
          _ = 24799099 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 77178373) ^ 19294593 = 49598197 := by
        calc
          (2 : ZMod 77178373) ^ 19294593 = (2 : ZMod 77178373) ^ (9647296 + 9647296 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 9647296 * (2 : ZMod 77178373) ^ 9647296) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 49598197 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 77178373) ^ 38589186 = 77178372 := by
        calc
          (2 : ZMod 77178373) ^ 38589186 = (2 : ZMod 77178373) ^ (19294593 + 19294593) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 19294593 * (2 : ZMod 77178373) ^ 19294593 := by rw [pow_add]
          _ = 77178372 := by rw [factor_0_24]; decide
      change (2 : ZMod 77178373) ^ 38589186 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (2 : ZMod 77178373) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 77178373) ^ 3 = 8 := by
        calc
          (2 : ZMod 77178373) ^ 3 = (2 : ZMod 77178373) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 1 * (2 : ZMod 77178373) ^ 1) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 77178373) ^ 6 = 64 := by
        calc
          (2 : ZMod 77178373) ^ 6 = (2 : ZMod 77178373) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 3 * (2 : ZMod 77178373) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 77178373) ^ 12 = 4096 := by
        calc
          (2 : ZMod 77178373) ^ 12 = (2 : ZMod 77178373) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 6 * (2 : ZMod 77178373) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 77178373) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 77178373) ^ 24 = (2 : ZMod 77178373) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 12 * (2 : ZMod 77178373) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 77178373) ^ 49 = 18608719 := by
        calc
          (2 : ZMod 77178373) ^ 49 = (2 : ZMod 77178373) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 24 * (2 : ZMod 77178373) ^ 24) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 18608719 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 77178373) ^ 98 = 35774323 := by
        calc
          (2 : ZMod 77178373) ^ 98 = (2 : ZMod 77178373) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 49 * (2 : ZMod 77178373) ^ 49 := by rw [pow_add]
          _ = 35774323 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 77178373) ^ 196 = 73921740 := by
        calc
          (2 : ZMod 77178373) ^ 196 = (2 : ZMod 77178373) ^ (98 + 98) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 98 * (2 : ZMod 77178373) ^ 98 := by rw [pow_add]
          _ = 73921740 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 77178373) ^ 392 = 38014148 := by
        calc
          (2 : ZMod 77178373) ^ 392 = (2 : ZMod 77178373) ^ (196 + 196) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 196 * (2 : ZMod 77178373) ^ 196 := by rw [pow_add]
          _ = 38014148 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 77178373) ^ 785 = 35663914 := by
        calc
          (2 : ZMod 77178373) ^ 785 = (2 : ZMod 77178373) ^ (392 + 392 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 392 * (2 : ZMod 77178373) ^ 392) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 35663914 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 77178373) ^ 1570 = 47798288 := by
        calc
          (2 : ZMod 77178373) ^ 1570 = (2 : ZMod 77178373) ^ (785 + 785) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 785 * (2 : ZMod 77178373) ^ 785 := by rw [pow_add]
          _ = 47798288 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 77178373) ^ 3140 = 75971659 := by
        calc
          (2 : ZMod 77178373) ^ 3140 = (2 : ZMod 77178373) ^ (1570 + 1570) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 1570 * (2 : ZMod 77178373) ^ 1570 := by rw [pow_add]
          _ = 75971659 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 77178373) ^ 6280 = 34314405 := by
        calc
          (2 : ZMod 77178373) ^ 6280 = (2 : ZMod 77178373) ^ (3140 + 3140) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 3140 * (2 : ZMod 77178373) ^ 3140 := by rw [pow_add]
          _ = 34314405 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 77178373) ^ 12561 = 42514013 := by
        calc
          (2 : ZMod 77178373) ^ 12561 = (2 : ZMod 77178373) ^ (6280 + 6280 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 6280 * (2 : ZMod 77178373) ^ 6280) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 42514013 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 77178373) ^ 25123 = 38695013 := by
        calc
          (2 : ZMod 77178373) ^ 25123 = (2 : ZMod 77178373) ^ (12561 + 12561 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 12561 * (2 : ZMod 77178373) ^ 12561) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 38695013 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 77178373) ^ 50246 = 66267797 := by
        calc
          (2 : ZMod 77178373) ^ 50246 = (2 : ZMod 77178373) ^ (25123 + 25123) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 25123 * (2 : ZMod 77178373) ^ 25123 := by rw [pow_add]
          _ = 66267797 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 77178373) ^ 100492 = 51531219 := by
        calc
          (2 : ZMod 77178373) ^ 100492 = (2 : ZMod 77178373) ^ (50246 + 50246) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 50246 * (2 : ZMod 77178373) ^ 50246 := by rw [pow_add]
          _ = 51531219 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 77178373) ^ 200985 = 29758291 := by
        calc
          (2 : ZMod 77178373) ^ 200985 = (2 : ZMod 77178373) ^ (100492 + 100492 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 100492 * (2 : ZMod 77178373) ^ 100492) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 29758291 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 77178373) ^ 401970 = 40574596 := by
        calc
          (2 : ZMod 77178373) ^ 401970 = (2 : ZMod 77178373) ^ (200985 + 200985) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 200985 * (2 : ZMod 77178373) ^ 200985 := by rw [pow_add]
          _ = 40574596 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 77178373) ^ 803941 = 46730990 := by
        calc
          (2 : ZMod 77178373) ^ 803941 = (2 : ZMod 77178373) ^ (401970 + 401970 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 401970 * (2 : ZMod 77178373) ^ 401970) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 46730990 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 77178373) ^ 1607882 = 54476454 := by
        calc
          (2 : ZMod 77178373) ^ 1607882 = (2 : ZMod 77178373) ^ (803941 + 803941) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 803941 * (2 : ZMod 77178373) ^ 803941 := by rw [pow_add]
          _ = 54476454 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 77178373) ^ 3215765 = 35531082 := by
        calc
          (2 : ZMod 77178373) ^ 3215765 = (2 : ZMod 77178373) ^ (1607882 + 1607882 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 1607882 * (2 : ZMod 77178373) ^ 1607882) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 35531082 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 77178373) ^ 6431531 = 20515223 := by
        calc
          (2 : ZMod 77178373) ^ 6431531 = (2 : ZMod 77178373) ^ (3215765 + 3215765 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 3215765 * (2 : ZMod 77178373) ^ 3215765) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 20515223 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 77178373) ^ 12863062 = 22966765 := by
        calc
          (2 : ZMod 77178373) ^ 12863062 = (2 : ZMod 77178373) ^ (6431531 + 6431531) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 6431531 * (2 : ZMod 77178373) ^ 6431531 := by rw [pow_add]
          _ = 22966765 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 77178373) ^ 25726124 = 22966764 := by
        calc
          (2 : ZMod 77178373) ^ 25726124 = (2 : ZMod 77178373) ^ (12863062 + 12863062) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 12863062 * (2 : ZMod 77178373) ^ 12863062 := by rw [pow_add]
          _ = 22966764 := by rw [factor_1_23]; decide
      change (2 : ZMod 77178373) ^ 25726124 ≠ 1
      rw [factor_1_24]
      decide
    ·
      have factor_2_0 : (2 : ZMod 77178373) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 77178373) ^ 2 = 4 := by
        calc
          (2 : ZMod 77178373) ^ 2 = (2 : ZMod 77178373) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 1 * (2 : ZMod 77178373) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 77178373) ^ 4 = 16 := by
        calc
          (2 : ZMod 77178373) ^ 4 = (2 : ZMod 77178373) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 2 * (2 : ZMod 77178373) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 77178373) ^ 9 = 512 := by
        calc
          (2 : ZMod 77178373) ^ 9 = (2 : ZMod 77178373) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 4 * (2 : ZMod 77178373) ^ 4) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 77178373) ^ 19 = 524288 := by
        calc
          (2 : ZMod 77178373) ^ 19 = (2 : ZMod 77178373) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 9 * (2 : ZMod 77178373) ^ 9) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 77178373) ^ 39 = 14263009 := by
        calc
          (2 : ZMod 77178373) ^ 39 = (2 : ZMod 77178373) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 19 * (2 : ZMod 77178373) ^ 19) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 14263009 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 77178373) ^ 79 = 65681206 := by
        calc
          (2 : ZMod 77178373) ^ 79 = (2 : ZMod 77178373) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 39 * (2 : ZMod 77178373) ^ 39) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 65681206 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 77178373) ^ 159 = 43577777 := by
        calc
          (2 : ZMod 77178373) ^ 159 = (2 : ZMod 77178373) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 79 * (2 : ZMod 77178373) ^ 79) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 43577777 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 77178373) ^ 319 = 7729986 := by
        calc
          (2 : ZMod 77178373) ^ 319 = (2 : ZMod 77178373) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 159 * (2 : ZMod 77178373) ^ 159) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 7729986 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 77178373) ^ 638 = 29508001 := by
        calc
          (2 : ZMod 77178373) ^ 638 = (2 : ZMod 77178373) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 319 * (2 : ZMod 77178373) ^ 319 := by rw [pow_add]
          _ = 29508001 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 77178373) ^ 1277 = 4459405 := by
        calc
          (2 : ZMod 77178373) ^ 1277 = (2 : ZMod 77178373) ^ (638 + 638 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 638 * (2 : ZMod 77178373) ^ 638) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 4459405 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 77178373) ^ 2554 = 50296607 := by
        calc
          (2 : ZMod 77178373) ^ 2554 = (2 : ZMod 77178373) ^ (1277 + 1277) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 1277 * (2 : ZMod 77178373) ^ 1277 := by rw [pow_add]
          _ = 50296607 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 77178373) ^ 5109 = 34766063 := by
        calc
          (2 : ZMod 77178373) ^ 5109 = (2 : ZMod 77178373) ^ (2554 + 2554 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 2554 * (2 : ZMod 77178373) ^ 2554) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 34766063 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 77178373) ^ 10219 = 41553973 := by
        calc
          (2 : ZMod 77178373) ^ 10219 = (2 : ZMod 77178373) ^ (5109 + 5109 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 5109 * (2 : ZMod 77178373) ^ 5109) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 41553973 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 77178373) ^ 20439 = 35233292 := by
        calc
          (2 : ZMod 77178373) ^ 20439 = (2 : ZMod 77178373) ^ (10219 + 10219 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 10219 * (2 : ZMod 77178373) ^ 10219) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 35233292 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 77178373) ^ 40878 = 63234004 := by
        calc
          (2 : ZMod 77178373) ^ 40878 = (2 : ZMod 77178373) ^ (20439 + 20439) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 20439 * (2 : ZMod 77178373) ^ 20439 := by rw [pow_add]
          _ = 63234004 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 77178373) ^ 81756 = 72877517 := by
        calc
          (2 : ZMod 77178373) ^ 81756 = (2 : ZMod 77178373) ^ (40878 + 40878) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 40878 * (2 : ZMod 77178373) ^ 40878 := by rw [pow_add]
          _ = 72877517 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 77178373) ^ 163513 = 43351652 := by
        calc
          (2 : ZMod 77178373) ^ 163513 = (2 : ZMod 77178373) ^ (81756 + 81756 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 81756 * (2 : ZMod 77178373) ^ 81756) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 43351652 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 77178373) ^ 327027 = 64887206 := by
        calc
          (2 : ZMod 77178373) ^ 327027 = (2 : ZMod 77178373) ^ (163513 + 163513 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 163513 * (2 : ZMod 77178373) ^ 163513) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 64887206 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 77178373) ^ 654054 = 57171412 := by
        calc
          (2 : ZMod 77178373) ^ 654054 = (2 : ZMod 77178373) ^ (327027 + 327027) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 327027 * (2 : ZMod 77178373) ^ 327027 := by rw [pow_add]
          _ = 57171412 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 77178373) ^ 1308108 = 34479710 := by
        calc
          (2 : ZMod 77178373) ^ 1308108 = (2 : ZMod 77178373) ^ (654054 + 654054) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 654054 * (2 : ZMod 77178373) ^ 654054 := by rw [pow_add]
          _ = 34479710 := by rw [factor_2_19]; decide
      change (2 : ZMod 77178373) ^ 1308108 ≠ 1
      rw [factor_2_20]
      decide
    ·
      have factor_3_0 : (2 : ZMod 77178373) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 77178373) ^ 2 = 4 := by
        calc
          (2 : ZMod 77178373) ^ 2 = (2 : ZMod 77178373) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 1 * (2 : ZMod 77178373) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 77178373) ^ 4 = 16 := by
        calc
          (2 : ZMod 77178373) ^ 4 = (2 : ZMod 77178373) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 2 * (2 : ZMod 77178373) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 77178373) ^ 8 = 256 := by
        calc
          (2 : ZMod 77178373) ^ 8 = (2 : ZMod 77178373) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 4 * (2 : ZMod 77178373) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 77178373) ^ 17 = 131072 := by
        calc
          (2 : ZMod 77178373) ^ 17 = (2 : ZMod 77178373) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 8 * (2 : ZMod 77178373) ^ 8) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 77178373) ^ 35 = 15362383 := by
        calc
          (2 : ZMod 77178373) ^ 35 = (2 : ZMod 77178373) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 17 * (2 : ZMod 77178373) ^ 17) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 15362383 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 77178373) ^ 70 = 67960838 := by
        calc
          (2 : ZMod 77178373) ^ 70 = (2 : ZMod 77178373) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 35 * (2 : ZMod 77178373) ^ 35 := by rw [pow_add]
          _ = 67960838 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 77178373) ^ 140 = 59061953 := by
        calc
          (2 : ZMod 77178373) ^ 140 = (2 : ZMod 77178373) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 70 * (2 : ZMod 77178373) ^ 70 := by rw [pow_add]
          _ = 59061953 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 77178373) ^ 281 = 30100738 := by
        calc
          (2 : ZMod 77178373) ^ 281 = (2 : ZMod 77178373) ^ (140 + 140 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 140 * (2 : ZMod 77178373) ^ 140) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 30100738 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 77178373) ^ 562 = 9609759 := by
        calc
          (2 : ZMod 77178373) ^ 562 = (2 : ZMod 77178373) ^ (281 + 281) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 281 * (2 : ZMod 77178373) ^ 281 := by rw [pow_add]
          _ = 9609759 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 77178373) ^ 1124 = 71716796 := by
        calc
          (2 : ZMod 77178373) ^ 1124 = (2 : ZMod 77178373) ^ (562 + 562) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 562 * (2 : ZMod 77178373) ^ 562 := by rw [pow_add]
          _ = 71716796 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 77178373) ^ 2249 = 76357199 := by
        calc
          (2 : ZMod 77178373) ^ 2249 = (2 : ZMod 77178373) ^ (1124 + 1124 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 1124 * (2 : ZMod 77178373) ^ 1124) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 76357199 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 77178373) ^ 4499 = 38586750 := by
        calc
          (2 : ZMod 77178373) ^ 4499 = (2 : ZMod 77178373) ^ (2249 + 2249 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 2249 * (2 : ZMod 77178373) ^ 2249) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 38586750 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 77178373) ^ 8999 = 50462251 := by
        calc
          (2 : ZMod 77178373) ^ 8999 = (2 : ZMod 77178373) ^ (4499 + 4499 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 4499 * (2 : ZMod 77178373) ^ 4499) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 50462251 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 77178373) ^ 17998 = 24372028 := by
        calc
          (2 : ZMod 77178373) ^ 17998 = (2 : ZMod 77178373) ^ (8999 + 8999) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 8999 * (2 : ZMod 77178373) ^ 8999 := by rw [pow_add]
          _ = 24372028 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 77178373) ^ 35997 = 6216049 := by
        calc
          (2 : ZMod 77178373) ^ 35997 = (2 : ZMod 77178373) ^ (17998 + 17998 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 17998 * (2 : ZMod 77178373) ^ 17998) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 6216049 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 77178373) ^ 71994 = 67084697 := by
        calc
          (2 : ZMod 77178373) ^ 71994 = (2 : ZMod 77178373) ^ (35997 + 35997) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 35997 * (2 : ZMod 77178373) ^ 35997 := by rw [pow_add]
          _ = 67084697 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 77178373) ^ 143989 = 25093931 := by
        calc
          (2 : ZMod 77178373) ^ 143989 = (2 : ZMod 77178373) ^ (71994 + 71994 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 71994 * (2 : ZMod 77178373) ^ 71994) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 25093931 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 77178373) ^ 287979 = 8987636 := by
        calc
          (2 : ZMod 77178373) ^ 287979 = (2 : ZMod 77178373) ^ (143989 + 143989 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 143989 * (2 : ZMod 77178373) ^ 143989) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 8987636 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 77178373) ^ 575958 = 14443641 := by
        calc
          (2 : ZMod 77178373) ^ 575958 = (2 : ZMod 77178373) ^ (287979 + 287979) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 287979 * (2 : ZMod 77178373) ^ 287979 := by rw [pow_add]
          _ = 14443641 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 77178373) ^ 1151916 = 66275025 := by
        calc
          (2 : ZMod 77178373) ^ 1151916 = (2 : ZMod 77178373) ^ (575958 + 575958) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 575958 * (2 : ZMod 77178373) ^ 575958 := by rw [pow_add]
          _ = 66275025 := by rw [factor_3_19]; decide
      change (2 : ZMod 77178373) ^ 1151916 ≠ 1
      rw [factor_3_20]
      decide
    ·
      have factor_4_0 : (2 : ZMod 77178373) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 77178373) ^ 2 = 4 := by
        calc
          (2 : ZMod 77178373) ^ 2 = (2 : ZMod 77178373) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 1 * (2 : ZMod 77178373) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 77178373) ^ 5 = 32 := by
        calc
          (2 : ZMod 77178373) ^ 5 = (2 : ZMod 77178373) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 2 * (2 : ZMod 77178373) ^ 2) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 77178373) ^ 11 = 2048 := by
        calc
          (2 : ZMod 77178373) ^ 11 = (2 : ZMod 77178373) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 5 * (2 : ZMod 77178373) ^ 5) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 77178373) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 77178373) ^ 23 = (2 : ZMod 77178373) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 11 * (2 : ZMod 77178373) ^ 11) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 77178373) ^ 46 = 50562573 := by
        calc
          (2 : ZMod 77178373) ^ 46 = (2 : ZMod 77178373) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 23 * (2 : ZMod 77178373) ^ 23 := by rw [pow_add]
          _ = 50562573 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 77178373) ^ 92 = 50001369 := by
        calc
          (2 : ZMod 77178373) ^ 92 = (2 : ZMod 77178373) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 46 * (2 : ZMod 77178373) ^ 46 := by rw [pow_add]
          _ = 50001369 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 77178373) ^ 185 = 6216394 := by
        calc
          (2 : ZMod 77178373) ^ 185 = (2 : ZMod 77178373) ^ (92 + 92 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 92 * (2 : ZMod 77178373) ^ 92) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 6216394 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 77178373) ^ 370 = 34288644 := by
        calc
          (2 : ZMod 77178373) ^ 370 = (2 : ZMod 77178373) ^ (185 + 185) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 185 * (2 : ZMod 77178373) ^ 185 := by rw [pow_add]
          _ = 34288644 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 77178373) ^ 741 = 14171716 := by
        calc
          (2 : ZMod 77178373) ^ 741 = (2 : ZMod 77178373) ^ (370 + 370 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 370 * (2 : ZMod 77178373) ^ 370) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 14171716 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 77178373) ^ 1482 = 36067033 := by
        calc
          (2 : ZMod 77178373) ^ 1482 = (2 : ZMod 77178373) ^ (741 + 741) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 741 * (2 : ZMod 77178373) ^ 741 := by rw [pow_add]
          _ = 36067033 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 77178373) ^ 2964 = 43123563 := by
        calc
          (2 : ZMod 77178373) ^ 2964 = (2 : ZMod 77178373) ^ (1482 + 1482) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 1482 * (2 : ZMod 77178373) ^ 1482 := by rw [pow_add]
          _ = 43123563 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 77178373) ^ 5929 = 1693680 := by
        calc
          (2 : ZMod 77178373) ^ 5929 = (2 : ZMod 77178373) ^ (2964 + 2964 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 2964 * (2 : ZMod 77178373) ^ 2964) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 1693680 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 77178373) ^ 11859 = 49527845 := by
        calc
          (2 : ZMod 77178373) ^ 11859 = (2 : ZMod 77178373) ^ (5929 + 5929 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = ((2 : ZMod 77178373) ^ 5929 * (2 : ZMod 77178373) ^ 5929) * (2 : ZMod 77178373) := by rw [pow_succ, pow_add]
          _ = 49527845 := by rw [factor_4_12]; decide
      have factor_4_14 : (2 : ZMod 77178373) ^ 23718 = 45299122 := by
        calc
          (2 : ZMod 77178373) ^ 23718 = (2 : ZMod 77178373) ^ (11859 + 11859) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 11859 * (2 : ZMod 77178373) ^ 11859 := by rw [pow_add]
          _ = 45299122 := by rw [factor_4_13]; decide
      have factor_4_15 : (2 : ZMod 77178373) ^ 47436 = 53554422 := by
        calc
          (2 : ZMod 77178373) ^ 47436 = (2 : ZMod 77178373) ^ (23718 + 23718) :=
            congrArg (fun n : ℕ => (2 : ZMod 77178373) ^ n) (by norm_num)
          _ = (2 : ZMod 77178373) ^ 23718 * (2 : ZMod 77178373) ^ 23718 := by rw [pow_add]
          _ = 53554422 := by rw [factor_4_14]; decide
      change (2 : ZMod 77178373) ^ 47436 ≠ 1
      rw [factor_4_15]
      decide

#print axioms prime_lucas_77178373

end TotientTailPeriodKiller
end Erdos249257
