import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_76276391 : Nat.Prime 76276391 := by
  apply lucas_primality 76276391 (7 : ZMod 76276391)
  ·
      have fermat_0 : (7 : ZMod 76276391) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 76276391) ^ 2 = 49 := by
        calc
          (7 : ZMod 76276391) ^ 2 = (7 : ZMod 76276391) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 1 * (7 : ZMod 76276391) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 76276391) ^ 4 = 2401 := by
        calc
          (7 : ZMod 76276391) ^ 4 = (7 : ZMod 76276391) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 2 * (7 : ZMod 76276391) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 76276391) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 76276391) ^ 9 = (7 : ZMod 76276391) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 4 * (7 : ZMod 76276391) ^ 4) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 76276391) ^ 18 = 62804535 := by
        calc
          (7 : ZMod 76276391) ^ 18 = (7 : ZMod 76276391) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 9 * (7 : ZMod 76276391) ^ 9 := by rw [pow_add]
          _ = 62804535 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 76276391) ^ 36 = 3485201 := by
        calc
          (7 : ZMod 76276391) ^ 36 = (7 : ZMod 76276391) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 18 * (7 : ZMod 76276391) ^ 18 := by rw [pow_add]
          _ = 3485201 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 76276391) ^ 72 = 68401997 := by
        calc
          (7 : ZMod 76276391) ^ 72 = (7 : ZMod 76276391) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 36 * (7 : ZMod 76276391) ^ 36 := by rw [pow_add]
          _ = 68401997 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 76276391) ^ 145 = 935380 := by
        calc
          (7 : ZMod 76276391) ^ 145 = (7 : ZMod 76276391) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 72 * (7 : ZMod 76276391) ^ 72) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 935380 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 76276391) ^ 290 = 45539630 := by
        calc
          (7 : ZMod 76276391) ^ 290 = (7 : ZMod 76276391) ^ (145 + 145) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 145 * (7 : ZMod 76276391) ^ 145 := by rw [pow_add]
          _ = 45539630 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 76276391) ^ 581 = 37583238 := by
        calc
          (7 : ZMod 76276391) ^ 581 = (7 : ZMod 76276391) ^ (290 + 290 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 290 * (7 : ZMod 76276391) ^ 290) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 37583238 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 76276391) ^ 1163 = 26079713 := by
        calc
          (7 : ZMod 76276391) ^ 1163 = (7 : ZMod 76276391) ^ (581 + 581 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 581 * (7 : ZMod 76276391) ^ 581) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 26079713 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 76276391) ^ 2327 = 40040526 := by
        calc
          (7 : ZMod 76276391) ^ 2327 = (7 : ZMod 76276391) ^ (1163 + 1163 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 1163 * (7 : ZMod 76276391) ^ 1163) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 40040526 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 76276391) ^ 4655 = 10587286 := by
        calc
          (7 : ZMod 76276391) ^ 4655 = (7 : ZMod 76276391) ^ (2327 + 2327 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 2327 * (7 : ZMod 76276391) ^ 2327) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 10587286 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 76276391) ^ 9311 = 39434706 := by
        calc
          (7 : ZMod 76276391) ^ 9311 = (7 : ZMod 76276391) ^ (4655 + 4655 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 4655 * (7 : ZMod 76276391) ^ 4655) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 39434706 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 76276391) ^ 18622 = 55717241 := by
        calc
          (7 : ZMod 76276391) ^ 18622 = (7 : ZMod 76276391) ^ (9311 + 9311) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 9311 * (7 : ZMod 76276391) ^ 9311 := by rw [pow_add]
          _ = 55717241 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 76276391) ^ 37244 = 45423972 := by
        calc
          (7 : ZMod 76276391) ^ 37244 = (7 : ZMod 76276391) ^ (18622 + 18622) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 18622 * (7 : ZMod 76276391) ^ 18622 := by rw [pow_add]
          _ = 45423972 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 76276391) ^ 74488 = 63423157 := by
        calc
          (7 : ZMod 76276391) ^ 74488 = (7 : ZMod 76276391) ^ (37244 + 37244) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 37244 * (7 : ZMod 76276391) ^ 37244 := by rw [pow_add]
          _ = 63423157 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 76276391) ^ 148977 = 38873822 := by
        calc
          (7 : ZMod 76276391) ^ 148977 = (7 : ZMod 76276391) ^ (74488 + 74488 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 74488 * (7 : ZMod 76276391) ^ 74488) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 38873822 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 76276391) ^ 297954 = 60698846 := by
        calc
          (7 : ZMod 76276391) ^ 297954 = (7 : ZMod 76276391) ^ (148977 + 148977) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 148977 * (7 : ZMod 76276391) ^ 148977 := by rw [pow_add]
          _ = 60698846 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 76276391) ^ 595909 = 40613778 := by
        calc
          (7 : ZMod 76276391) ^ 595909 = (7 : ZMod 76276391) ^ (297954 + 297954 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 297954 * (7 : ZMod 76276391) ^ 297954) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 40613778 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 76276391) ^ 1191818 = 24872118 := by
        calc
          (7 : ZMod 76276391) ^ 1191818 = (7 : ZMod 76276391) ^ (595909 + 595909) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 595909 * (7 : ZMod 76276391) ^ 595909 := by rw [pow_add]
          _ = 24872118 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 76276391) ^ 2383637 = 58152177 := by
        calc
          (7 : ZMod 76276391) ^ 2383637 = (7 : ZMod 76276391) ^ (1191818 + 1191818 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 1191818 * (7 : ZMod 76276391) ^ 1191818) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 58152177 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 76276391) ^ 4767274 = 33049829 := by
        calc
          (7 : ZMod 76276391) ^ 4767274 = (7 : ZMod 76276391) ^ (2383637 + 2383637) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 2383637 * (7 : ZMod 76276391) ^ 2383637 := by rw [pow_add]
          _ = 33049829 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 76276391) ^ 9534548 = 5717207 := by
        calc
          (7 : ZMod 76276391) ^ 9534548 = (7 : ZMod 76276391) ^ (4767274 + 4767274) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 4767274 * (7 : ZMod 76276391) ^ 4767274 := by rw [pow_add]
          _ = 5717207 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 76276391) ^ 19069097 = 45229108 := by
        calc
          (7 : ZMod 76276391) ^ 19069097 = (7 : ZMod 76276391) ^ (9534548 + 9534548 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 9534548 * (7 : ZMod 76276391) ^ 9534548) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 45229108 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 76276391) ^ 38138195 = 76276390 := by
        calc
          (7 : ZMod 76276391) ^ 38138195 = (7 : ZMod 76276391) ^ (19069097 + 19069097 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 19069097 * (7 : ZMod 76276391) ^ 19069097) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 76276390 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 76276391) ^ 76276390 = 1 := by
        calc
          (7 : ZMod 76276391) ^ 76276390 = (7 : ZMod 76276391) ^ (38138195 + 38138195) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 38138195 * (7 : ZMod 76276391) ^ 38138195 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (251, 1), (30389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (251, 1), (30389, 1)] : List FactorBlock).map factorBlockValue).prod = 76276391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 76276391) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 76276391) ^ 2 = 49 := by
        calc
          (7 : ZMod 76276391) ^ 2 = (7 : ZMod 76276391) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 1 * (7 : ZMod 76276391) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 76276391) ^ 4 = 2401 := by
        calc
          (7 : ZMod 76276391) ^ 4 = (7 : ZMod 76276391) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 2 * (7 : ZMod 76276391) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 76276391) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 76276391) ^ 9 = (7 : ZMod 76276391) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 4 * (7 : ZMod 76276391) ^ 4) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 76276391) ^ 18 = 62804535 := by
        calc
          (7 : ZMod 76276391) ^ 18 = (7 : ZMod 76276391) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 9 * (7 : ZMod 76276391) ^ 9 := by rw [pow_add]
          _ = 62804535 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 76276391) ^ 36 = 3485201 := by
        calc
          (7 : ZMod 76276391) ^ 36 = (7 : ZMod 76276391) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 18 * (7 : ZMod 76276391) ^ 18 := by rw [pow_add]
          _ = 3485201 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 76276391) ^ 72 = 68401997 := by
        calc
          (7 : ZMod 76276391) ^ 72 = (7 : ZMod 76276391) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 36 * (7 : ZMod 76276391) ^ 36 := by rw [pow_add]
          _ = 68401997 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 76276391) ^ 145 = 935380 := by
        calc
          (7 : ZMod 76276391) ^ 145 = (7 : ZMod 76276391) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 72 * (7 : ZMod 76276391) ^ 72) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 935380 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 76276391) ^ 290 = 45539630 := by
        calc
          (7 : ZMod 76276391) ^ 290 = (7 : ZMod 76276391) ^ (145 + 145) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 145 * (7 : ZMod 76276391) ^ 145 := by rw [pow_add]
          _ = 45539630 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 76276391) ^ 581 = 37583238 := by
        calc
          (7 : ZMod 76276391) ^ 581 = (7 : ZMod 76276391) ^ (290 + 290 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 290 * (7 : ZMod 76276391) ^ 290) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 37583238 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 76276391) ^ 1163 = 26079713 := by
        calc
          (7 : ZMod 76276391) ^ 1163 = (7 : ZMod 76276391) ^ (581 + 581 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 581 * (7 : ZMod 76276391) ^ 581) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 26079713 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 76276391) ^ 2327 = 40040526 := by
        calc
          (7 : ZMod 76276391) ^ 2327 = (7 : ZMod 76276391) ^ (1163 + 1163 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 1163 * (7 : ZMod 76276391) ^ 1163) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 40040526 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 76276391) ^ 4655 = 10587286 := by
        calc
          (7 : ZMod 76276391) ^ 4655 = (7 : ZMod 76276391) ^ (2327 + 2327 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 2327 * (7 : ZMod 76276391) ^ 2327) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 10587286 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 76276391) ^ 9311 = 39434706 := by
        calc
          (7 : ZMod 76276391) ^ 9311 = (7 : ZMod 76276391) ^ (4655 + 4655 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 4655 * (7 : ZMod 76276391) ^ 4655) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 39434706 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 76276391) ^ 18622 = 55717241 := by
        calc
          (7 : ZMod 76276391) ^ 18622 = (7 : ZMod 76276391) ^ (9311 + 9311) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 9311 * (7 : ZMod 76276391) ^ 9311 := by rw [pow_add]
          _ = 55717241 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 76276391) ^ 37244 = 45423972 := by
        calc
          (7 : ZMod 76276391) ^ 37244 = (7 : ZMod 76276391) ^ (18622 + 18622) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 18622 * (7 : ZMod 76276391) ^ 18622 := by rw [pow_add]
          _ = 45423972 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 76276391) ^ 74488 = 63423157 := by
        calc
          (7 : ZMod 76276391) ^ 74488 = (7 : ZMod 76276391) ^ (37244 + 37244) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 37244 * (7 : ZMod 76276391) ^ 37244 := by rw [pow_add]
          _ = 63423157 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 76276391) ^ 148977 = 38873822 := by
        calc
          (7 : ZMod 76276391) ^ 148977 = (7 : ZMod 76276391) ^ (74488 + 74488 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 74488 * (7 : ZMod 76276391) ^ 74488) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 38873822 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 76276391) ^ 297954 = 60698846 := by
        calc
          (7 : ZMod 76276391) ^ 297954 = (7 : ZMod 76276391) ^ (148977 + 148977) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 148977 * (7 : ZMod 76276391) ^ 148977 := by rw [pow_add]
          _ = 60698846 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 76276391) ^ 595909 = 40613778 := by
        calc
          (7 : ZMod 76276391) ^ 595909 = (7 : ZMod 76276391) ^ (297954 + 297954 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 297954 * (7 : ZMod 76276391) ^ 297954) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 40613778 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 76276391) ^ 1191818 = 24872118 := by
        calc
          (7 : ZMod 76276391) ^ 1191818 = (7 : ZMod 76276391) ^ (595909 + 595909) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 595909 * (7 : ZMod 76276391) ^ 595909 := by rw [pow_add]
          _ = 24872118 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 76276391) ^ 2383637 = 58152177 := by
        calc
          (7 : ZMod 76276391) ^ 2383637 = (7 : ZMod 76276391) ^ (1191818 + 1191818 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 1191818 * (7 : ZMod 76276391) ^ 1191818) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 58152177 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 76276391) ^ 4767274 = 33049829 := by
        calc
          (7 : ZMod 76276391) ^ 4767274 = (7 : ZMod 76276391) ^ (2383637 + 2383637) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 2383637 * (7 : ZMod 76276391) ^ 2383637 := by rw [pow_add]
          _ = 33049829 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 76276391) ^ 9534548 = 5717207 := by
        calc
          (7 : ZMod 76276391) ^ 9534548 = (7 : ZMod 76276391) ^ (4767274 + 4767274) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 4767274 * (7 : ZMod 76276391) ^ 4767274 := by rw [pow_add]
          _ = 5717207 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 76276391) ^ 19069097 = 45229108 := by
        calc
          (7 : ZMod 76276391) ^ 19069097 = (7 : ZMod 76276391) ^ (9534548 + 9534548 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 9534548 * (7 : ZMod 76276391) ^ 9534548) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 45229108 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 76276391) ^ 38138195 = 76276390 := by
        calc
          (7 : ZMod 76276391) ^ 38138195 = (7 : ZMod 76276391) ^ (19069097 + 19069097 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 19069097 * (7 : ZMod 76276391) ^ 19069097) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 76276390 := by rw [factor_0_24]; decide
      change (7 : ZMod 76276391) ^ 38138195 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (7 : ZMod 76276391) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 76276391) ^ 3 = 343 := by
        calc
          (7 : ZMod 76276391) ^ 3 = (7 : ZMod 76276391) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 1 * (7 : ZMod 76276391) ^ 1) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 76276391) ^ 7 = 823543 := by
        calc
          (7 : ZMod 76276391) ^ 7 = (7 : ZMod 76276391) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 3 * (7 : ZMod 76276391) ^ 3) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 76276391) ^ 14 = 49680468 := by
        calc
          (7 : ZMod 76276391) ^ 14 = (7 : ZMod 76276391) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 7 * (7 : ZMod 76276391) ^ 7 := by rw [pow_add]
          _ = 49680468 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 76276391) ^ 29 = 9999053 := by
        calc
          (7 : ZMod 76276391) ^ 29 = (7 : ZMod 76276391) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 14 * (7 : ZMod 76276391) ^ 14) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 9999053 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 76276391) ^ 58 = 27036566 := by
        calc
          (7 : ZMod 76276391) ^ 58 = (7 : ZMod 76276391) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 29 * (7 : ZMod 76276391) ^ 29 := by rw [pow_add]
          _ = 27036566 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 76276391) ^ 116 = 24468824 := by
        calc
          (7 : ZMod 76276391) ^ 116 = (7 : ZMod 76276391) ^ (58 + 58) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 58 * (7 : ZMod 76276391) ^ 58 := by rw [pow_add]
          _ = 24468824 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 76276391) ^ 232 = 54638704 := by
        calc
          (7 : ZMod 76276391) ^ 232 = (7 : ZMod 76276391) ^ (116 + 116) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 116 * (7 : ZMod 76276391) ^ 116 := by rw [pow_add]
          _ = 54638704 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 76276391) ^ 465 = 64400314 := by
        calc
          (7 : ZMod 76276391) ^ 465 = (7 : ZMod 76276391) ^ (232 + 232 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 232 * (7 : ZMod 76276391) ^ 232) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 64400314 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 76276391) ^ 931 = 9495588 := by
        calc
          (7 : ZMod 76276391) ^ 931 = (7 : ZMod 76276391) ^ (465 + 465 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 465 * (7 : ZMod 76276391) ^ 465) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 9495588 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 76276391) ^ 1862 = 22217426 := by
        calc
          (7 : ZMod 76276391) ^ 1862 = (7 : ZMod 76276391) ^ (931 + 931) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 931 * (7 : ZMod 76276391) ^ 931 := by rw [pow_add]
          _ = 22217426 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 76276391) ^ 3724 = 49217550 := by
        calc
          (7 : ZMod 76276391) ^ 3724 = (7 : ZMod 76276391) ^ (1862 + 1862) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 1862 * (7 : ZMod 76276391) ^ 1862 := by rw [pow_add]
          _ = 49217550 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 76276391) ^ 7448 = 61511122 := by
        calc
          (7 : ZMod 76276391) ^ 7448 = (7 : ZMod 76276391) ^ (3724 + 3724) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 3724 * (7 : ZMod 76276391) ^ 3724 := by rw [pow_add]
          _ = 61511122 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 76276391) ^ 14897 = 67755909 := by
        calc
          (7 : ZMod 76276391) ^ 14897 = (7 : ZMod 76276391) ^ (7448 + 7448 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 7448 * (7 : ZMod 76276391) ^ 7448) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 67755909 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 76276391) ^ 29795 = 59971024 := by
        calc
          (7 : ZMod 76276391) ^ 29795 = (7 : ZMod 76276391) ^ (14897 + 14897 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 14897 * (7 : ZMod 76276391) ^ 14897) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 59971024 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 76276391) ^ 59590 = 47183812 := by
        calc
          (7 : ZMod 76276391) ^ 59590 = (7 : ZMod 76276391) ^ (29795 + 29795) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 29795 * (7 : ZMod 76276391) ^ 29795 := by rw [pow_add]
          _ = 47183812 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 76276391) ^ 119181 = 60017332 := by
        calc
          (7 : ZMod 76276391) ^ 119181 = (7 : ZMod 76276391) ^ (59590 + 59590 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 59590 * (7 : ZMod 76276391) ^ 59590) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 60017332 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 76276391) ^ 238363 = 37133545 := by
        calc
          (7 : ZMod 76276391) ^ 238363 = (7 : ZMod 76276391) ^ (119181 + 119181 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 119181 * (7 : ZMod 76276391) ^ 119181) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 37133545 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 76276391) ^ 476727 = 62328188 := by
        calc
          (7 : ZMod 76276391) ^ 476727 = (7 : ZMod 76276391) ^ (238363 + 238363 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 238363 * (7 : ZMod 76276391) ^ 238363) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 62328188 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 76276391) ^ 953454 = 49687616 := by
        calc
          (7 : ZMod 76276391) ^ 953454 = (7 : ZMod 76276391) ^ (476727 + 476727) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 476727 * (7 : ZMod 76276391) ^ 476727 := by rw [pow_add]
          _ = 49687616 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 76276391) ^ 1906909 = 67455524 := by
        calc
          (7 : ZMod 76276391) ^ 1906909 = (7 : ZMod 76276391) ^ (953454 + 953454 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 953454 * (7 : ZMod 76276391) ^ 953454) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 67455524 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 76276391) ^ 3813819 = 4194593 := by
        calc
          (7 : ZMod 76276391) ^ 3813819 = (7 : ZMod 76276391) ^ (1906909 + 1906909 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 1906909 * (7 : ZMod 76276391) ^ 1906909) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 4194593 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 76276391) ^ 7627639 = 4924099 := by
        calc
          (7 : ZMod 76276391) ^ 7627639 = (7 : ZMod 76276391) ^ (3813819 + 3813819 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 3813819 * (7 : ZMod 76276391) ^ 3813819) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 4924099 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 76276391) ^ 15255278 = 11790721 := by
        calc
          (7 : ZMod 76276391) ^ 15255278 = (7 : ZMod 76276391) ^ (7627639 + 7627639) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 7627639 * (7 : ZMod 76276391) ^ 7627639 := by rw [pow_add]
          _ = 11790721 := by rw [factor_1_22]; decide
      change (7 : ZMod 76276391) ^ 15255278 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (7 : ZMod 76276391) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 76276391) ^ 2 = 49 := by
        calc
          (7 : ZMod 76276391) ^ 2 = (7 : ZMod 76276391) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 1 * (7 : ZMod 76276391) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 76276391) ^ 4 = 2401 := by
        calc
          (7 : ZMod 76276391) ^ 4 = (7 : ZMod 76276391) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 2 * (7 : ZMod 76276391) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 76276391) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 76276391) ^ 9 = (7 : ZMod 76276391) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 4 * (7 : ZMod 76276391) ^ 4) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 76276391) ^ 18 = 62804535 := by
        calc
          (7 : ZMod 76276391) ^ 18 = (7 : ZMod 76276391) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 9 * (7 : ZMod 76276391) ^ 9 := by rw [pow_add]
          _ = 62804535 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 76276391) ^ 37 = 24396407 := by
        calc
          (7 : ZMod 76276391) ^ 37 = (7 : ZMod 76276391) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 18 * (7 : ZMod 76276391) ^ 18) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 24396407 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 76276391) ^ 74 = 71813040 := by
        calc
          (7 : ZMod 76276391) ^ 74 = (7 : ZMod 76276391) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 37 * (7 : ZMod 76276391) ^ 37 := by rw [pow_add]
          _ = 71813040 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 76276391) ^ 148 = 15729776 := by
        calc
          (7 : ZMod 76276391) ^ 148 = (7 : ZMod 76276391) ^ (74 + 74) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 74 * (7 : ZMod 76276391) ^ 74 := by rw [pow_add]
          _ = 15729776 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 76276391) ^ 296 = 38226030 := by
        calc
          (7 : ZMod 76276391) ^ 296 = (7 : ZMod 76276391) ^ (148 + 148) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 148 * (7 : ZMod 76276391) ^ 148 := by rw [pow_add]
          _ = 38226030 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 76276391) ^ 593 = 57818197 := by
        calc
          (7 : ZMod 76276391) ^ 593 = (7 : ZMod 76276391) ^ (296 + 296 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 296 * (7 : ZMod 76276391) ^ 296) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 57818197 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 76276391) ^ 1187 = 28859715 := by
        calc
          (7 : ZMod 76276391) ^ 1187 = (7 : ZMod 76276391) ^ (593 + 593 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 593 * (7 : ZMod 76276391) ^ 593) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 28859715 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 76276391) ^ 2374 = 31715527 := by
        calc
          (7 : ZMod 76276391) ^ 2374 = (7 : ZMod 76276391) ^ (1187 + 1187) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 1187 * (7 : ZMod 76276391) ^ 1187 := by rw [pow_add]
          _ = 31715527 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 76276391) ^ 4748 = 36095235 := by
        calc
          (7 : ZMod 76276391) ^ 4748 = (7 : ZMod 76276391) ^ (2374 + 2374) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 2374 * (7 : ZMod 76276391) ^ 2374 := by rw [pow_add]
          _ = 36095235 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 76276391) ^ 9496 = 15110920 := by
        calc
          (7 : ZMod 76276391) ^ 9496 = (7 : ZMod 76276391) ^ (4748 + 4748) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 4748 * (7 : ZMod 76276391) ^ 4748 := by rw [pow_add]
          _ = 15110920 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 76276391) ^ 18993 = 74233482 := by
        calc
          (7 : ZMod 76276391) ^ 18993 = (7 : ZMod 76276391) ^ (9496 + 9496 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 9496 * (7 : ZMod 76276391) ^ 9496) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 74233482 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 76276391) ^ 37986 = 14448716 := by
        calc
          (7 : ZMod 76276391) ^ 37986 = (7 : ZMod 76276391) ^ (18993 + 18993) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 18993 * (7 : ZMod 76276391) ^ 18993 := by rw [pow_add]
          _ = 14448716 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 76276391) ^ 75972 = 39213687 := by
        calc
          (7 : ZMod 76276391) ^ 75972 = (7 : ZMod 76276391) ^ (37986 + 37986) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 37986 * (7 : ZMod 76276391) ^ 37986 := by rw [pow_add]
          _ = 39213687 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 76276391) ^ 151945 = 15792258 := by
        calc
          (7 : ZMod 76276391) ^ 151945 = (7 : ZMod 76276391) ^ (75972 + 75972 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 75972 * (7 : ZMod 76276391) ^ 75972) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 15792258 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 76276391) ^ 303890 = 65262407 := by
        calc
          (7 : ZMod 76276391) ^ 303890 = (7 : ZMod 76276391) ^ (151945 + 151945) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 151945 * (7 : ZMod 76276391) ^ 151945 := by rw [pow_add]
          _ = 65262407 := by rw [factor_2_17]; decide
      change (7 : ZMod 76276391) ^ 303890 ≠ 1
      rw [factor_2_18]
      decide
    ·
      have factor_3_0 : (7 : ZMod 76276391) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 76276391) ^ 2 = 49 := by
        calc
          (7 : ZMod 76276391) ^ 2 = (7 : ZMod 76276391) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 1 * (7 : ZMod 76276391) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 76276391) ^ 4 = 2401 := by
        calc
          (7 : ZMod 76276391) ^ 4 = (7 : ZMod 76276391) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 2 * (7 : ZMod 76276391) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 76276391) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 76276391) ^ 9 = (7 : ZMod 76276391) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 4 * (7 : ZMod 76276391) ^ 4) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 76276391) ^ 19 = 58249790 := by
        calc
          (7 : ZMod 76276391) ^ 19 = (7 : ZMod 76276391) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 9 * (7 : ZMod 76276391) ^ 9) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 58249790 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 76276391) ^ 39 = 51278078 := by
        calc
          (7 : ZMod 76276391) ^ 39 = (7 : ZMod 76276391) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 19 * (7 : ZMod 76276391) ^ 19) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 51278078 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 76276391) ^ 78 = 38465380 := by
        calc
          (7 : ZMod 76276391) ^ 78 = (7 : ZMod 76276391) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 39 * (7 : ZMod 76276391) ^ 39 := by rw [pow_add]
          _ = 38465380 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 76276391) ^ 156 = 52989565 := by
        calc
          (7 : ZMod 76276391) ^ 156 = (7 : ZMod 76276391) ^ (78 + 78) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 78 * (7 : ZMod 76276391) ^ 78 := by rw [pow_add]
          _ = 52989565 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 76276391) ^ 313 = 51899958 := by
        calc
          (7 : ZMod 76276391) ^ 313 = (7 : ZMod 76276391) ^ (156 + 156 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 156 * (7 : ZMod 76276391) ^ 156) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 51899958 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 76276391) ^ 627 = 62274387 := by
        calc
          (7 : ZMod 76276391) ^ 627 = (7 : ZMod 76276391) ^ (313 + 313 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 313 * (7 : ZMod 76276391) ^ 313) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 62274387 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 76276391) ^ 1255 = 68081006 := by
        calc
          (7 : ZMod 76276391) ^ 1255 = (7 : ZMod 76276391) ^ (627 + 627 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = ((7 : ZMod 76276391) ^ 627 * (7 : ZMod 76276391) ^ 627) * (7 : ZMod 76276391) := by rw [pow_succ, pow_add]
          _ = 68081006 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 76276391) ^ 2510 = 74519867 := by
        calc
          (7 : ZMod 76276391) ^ 2510 = (7 : ZMod 76276391) ^ (1255 + 1255) :=
            congrArg (fun n : ℕ => (7 : ZMod 76276391) ^ n) (by norm_num)
          _ = (7 : ZMod 76276391) ^ 1255 * (7 : ZMod 76276391) ^ 1255 := by rw [pow_add]
          _ = 74519867 := by rw [factor_3_10]; decide
      change (7 : ZMod 76276391) ^ 2510 ≠ 1
      rw [factor_3_11]
      decide

#print axioms prime_lucas_76276391

end TotientTailPeriodKiller
end Erdos249257
