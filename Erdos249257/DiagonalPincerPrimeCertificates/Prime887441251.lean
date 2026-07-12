import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=27 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_887441251 : Nat.Prime 887441251 := by
  apply lucas_primality 887441251 (3 : ZMod 887441251)
  ·
      have fermat_0 : (3 : ZMod 887441251) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 887441251) ^ 3 = 27 := by
        calc
          (3 : ZMod 887441251) ^ 3 = (3 : ZMod 887441251) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 1 * (3 : ZMod 887441251) ^ 1) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 887441251) ^ 6 = 729 := by
        calc
          (3 : ZMod 887441251) ^ 6 = (3 : ZMod 887441251) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 3 * (3 : ZMod 887441251) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 887441251) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 887441251) ^ 13 = (3 : ZMod 887441251) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 6 * (3 : ZMod 887441251) ^ 6) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 887441251) ^ 26 = 234085465 := by
        calc
          (3 : ZMod 887441251) ^ 26 = (3 : ZMod 887441251) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 13 * (3 : ZMod 887441251) ^ 13 := by rw [pow_add]
          _ = 234085465 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 887441251) ^ 52 = 643780161 := by
        calc
          (3 : ZMod 887441251) ^ 52 = (3 : ZMod 887441251) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 26 * (3 : ZMod 887441251) ^ 26 := by rw [pow_add]
          _ = 643780161 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 887441251) ^ 105 = 369388734 := by
        calc
          (3 : ZMod 887441251) ^ 105 = (3 : ZMod 887441251) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 52 * (3 : ZMod 887441251) ^ 52) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 369388734 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 887441251) ^ 211 = 252977434 := by
        calc
          (3 : ZMod 887441251) ^ 211 = (3 : ZMod 887441251) ^ (105 + 105 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 105 * (3 : ZMod 887441251) ^ 105) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 252977434 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 887441251) ^ 423 = 143668892 := by
        calc
          (3 : ZMod 887441251) ^ 423 = (3 : ZMod 887441251) ^ (211 + 211 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 211 * (3 : ZMod 887441251) ^ 211) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 143668892 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 887441251) ^ 846 = 292725191 := by
        calc
          (3 : ZMod 887441251) ^ 846 = (3 : ZMod 887441251) ^ (423 + 423) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 423 * (3 : ZMod 887441251) ^ 423 := by rw [pow_add]
          _ = 292725191 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 887441251) ^ 1692 = 881585189 := by
        calc
          (3 : ZMod 887441251) ^ 1692 = (3 : ZMod 887441251) ^ (846 + 846) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 846 * (3 : ZMod 887441251) ^ 846 := by rw [pow_add]
          _ = 881585189 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 887441251) ^ 3385 = 209656353 := by
        calc
          (3 : ZMod 887441251) ^ 3385 = (3 : ZMod 887441251) ^ (1692 + 1692 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 1692 * (3 : ZMod 887441251) ^ 1692) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 209656353 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 887441251) ^ 6770 = 308073434 := by
        calc
          (3 : ZMod 887441251) ^ 6770 = (3 : ZMod 887441251) ^ (3385 + 3385) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 3385 * (3 : ZMod 887441251) ^ 3385 := by rw [pow_add]
          _ = 308073434 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 887441251) ^ 13541 = 97227111 := by
        calc
          (3 : ZMod 887441251) ^ 13541 = (3 : ZMod 887441251) ^ (6770 + 6770 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 6770 * (3 : ZMod 887441251) ^ 6770) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 97227111 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 887441251) ^ 27082 = 825952974 := by
        calc
          (3 : ZMod 887441251) ^ 27082 = (3 : ZMod 887441251) ^ (13541 + 13541) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 13541 * (3 : ZMod 887441251) ^ 13541 := by rw [pow_add]
          _ = 825952974 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 887441251) ^ 54165 = 723722645 := by
        calc
          (3 : ZMod 887441251) ^ 54165 = (3 : ZMod 887441251) ^ (27082 + 27082 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 27082 * (3 : ZMod 887441251) ^ 27082) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 723722645 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 887441251) ^ 108330 = 710156043 := by
        calc
          (3 : ZMod 887441251) ^ 108330 = (3 : ZMod 887441251) ^ (54165 + 54165) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 54165 * (3 : ZMod 887441251) ^ 54165 := by rw [pow_add]
          _ = 710156043 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 887441251) ^ 216660 = 545828035 := by
        calc
          (3 : ZMod 887441251) ^ 216660 = (3 : ZMod 887441251) ^ (108330 + 108330) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 108330 * (3 : ZMod 887441251) ^ 108330 := by rw [pow_add]
          _ = 545828035 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 887441251) ^ 433320 = 797302707 := by
        calc
          (3 : ZMod 887441251) ^ 433320 = (3 : ZMod 887441251) ^ (216660 + 216660) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 216660 * (3 : ZMod 887441251) ^ 216660 := by rw [pow_add]
          _ = 797302707 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 887441251) ^ 866641 = 832937097 := by
        calc
          (3 : ZMod 887441251) ^ 866641 = (3 : ZMod 887441251) ^ (433320 + 433320 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 433320 * (3 : ZMod 887441251) ^ 433320) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 832937097 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 887441251) ^ 1733283 = 57748421 := by
        calc
          (3 : ZMod 887441251) ^ 1733283 = (3 : ZMod 887441251) ^ (866641 + 866641 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 866641 * (3 : ZMod 887441251) ^ 866641) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 57748421 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 887441251) ^ 3466567 = 445531143 := by
        calc
          (3 : ZMod 887441251) ^ 3466567 = (3 : ZMod 887441251) ^ (1733283 + 1733283 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 1733283 * (3 : ZMod 887441251) ^ 1733283) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 445531143 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 887441251) ^ 6933134 = 874938176 := by
        calc
          (3 : ZMod 887441251) ^ 6933134 = (3 : ZMod 887441251) ^ (3466567 + 3466567) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 3466567 * (3 : ZMod 887441251) ^ 3466567 := by rw [pow_add]
          _ = 874938176 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 887441251) ^ 13866269 = 787539662 := by
        calc
          (3 : ZMod 887441251) ^ 13866269 = (3 : ZMod 887441251) ^ (6933134 + 6933134 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 6933134 * (3 : ZMod 887441251) ^ 6933134) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 787539662 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 887441251) ^ 27732539 = 547807462 := by
        calc
          (3 : ZMod 887441251) ^ 27732539 = (3 : ZMod 887441251) ^ (13866269 + 13866269 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 13866269 * (3 : ZMod 887441251) ^ 13866269) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 547807462 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 887441251) ^ 55465078 = 599567335 := by
        calc
          (3 : ZMod 887441251) ^ 55465078 = (3 : ZMod 887441251) ^ (27732539 + 27732539) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 27732539 * (3 : ZMod 887441251) ^ 27732539 := by rw [pow_add]
          _ = 599567335 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 887441251) ^ 110930156 = 298116409 := by
        calc
          (3 : ZMod 887441251) ^ 110930156 = (3 : ZMod 887441251) ^ (55465078 + 55465078) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 55465078 * (3 : ZMod 887441251) ^ 55465078 := by rw [pow_add]
          _ = 298116409 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 887441251) ^ 221860312 = 860110868 := by
        calc
          (3 : ZMod 887441251) ^ 221860312 = (3 : ZMod 887441251) ^ (110930156 + 110930156) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 110930156 * (3 : ZMod 887441251) ^ 110930156 := by rw [pow_add]
          _ = 860110868 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 887441251) ^ 443720625 = 887441250 := by
        calc
          (3 : ZMod 887441251) ^ 443720625 = (3 : ZMod 887441251) ^ (221860312 + 221860312 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 221860312 * (3 : ZMod 887441251) ^ 221860312) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 887441250 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 887441251) ^ 887441250 = 1 := by
        calc
          (3 : ZMod 887441251) ^ 887441250 = (3 : ZMod 887441251) ^ (443720625 + 443720625) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 443720625 * (3 : ZMod 887441251) ^ 443720625 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 4), (89, 1), (2659, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 4), (89, 1), (2659, 1)] : List FactorBlock).map factorBlockValue).prod = 887441251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 887441251) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 887441251) ^ 3 = 27 := by
        calc
          (3 : ZMod 887441251) ^ 3 = (3 : ZMod 887441251) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 1 * (3 : ZMod 887441251) ^ 1) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 887441251) ^ 6 = 729 := by
        calc
          (3 : ZMod 887441251) ^ 6 = (3 : ZMod 887441251) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 3 * (3 : ZMod 887441251) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 887441251) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 887441251) ^ 13 = (3 : ZMod 887441251) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 6 * (3 : ZMod 887441251) ^ 6) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 887441251) ^ 26 = 234085465 := by
        calc
          (3 : ZMod 887441251) ^ 26 = (3 : ZMod 887441251) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 13 * (3 : ZMod 887441251) ^ 13 := by rw [pow_add]
          _ = 234085465 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 887441251) ^ 52 = 643780161 := by
        calc
          (3 : ZMod 887441251) ^ 52 = (3 : ZMod 887441251) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 26 * (3 : ZMod 887441251) ^ 26 := by rw [pow_add]
          _ = 643780161 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 887441251) ^ 105 = 369388734 := by
        calc
          (3 : ZMod 887441251) ^ 105 = (3 : ZMod 887441251) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 52 * (3 : ZMod 887441251) ^ 52) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 369388734 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 887441251) ^ 211 = 252977434 := by
        calc
          (3 : ZMod 887441251) ^ 211 = (3 : ZMod 887441251) ^ (105 + 105 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 105 * (3 : ZMod 887441251) ^ 105) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 252977434 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 887441251) ^ 423 = 143668892 := by
        calc
          (3 : ZMod 887441251) ^ 423 = (3 : ZMod 887441251) ^ (211 + 211 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 211 * (3 : ZMod 887441251) ^ 211) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 143668892 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 887441251) ^ 846 = 292725191 := by
        calc
          (3 : ZMod 887441251) ^ 846 = (3 : ZMod 887441251) ^ (423 + 423) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 423 * (3 : ZMod 887441251) ^ 423 := by rw [pow_add]
          _ = 292725191 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 887441251) ^ 1692 = 881585189 := by
        calc
          (3 : ZMod 887441251) ^ 1692 = (3 : ZMod 887441251) ^ (846 + 846) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 846 * (3 : ZMod 887441251) ^ 846 := by rw [pow_add]
          _ = 881585189 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 887441251) ^ 3385 = 209656353 := by
        calc
          (3 : ZMod 887441251) ^ 3385 = (3 : ZMod 887441251) ^ (1692 + 1692 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 1692 * (3 : ZMod 887441251) ^ 1692) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 209656353 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 887441251) ^ 6770 = 308073434 := by
        calc
          (3 : ZMod 887441251) ^ 6770 = (3 : ZMod 887441251) ^ (3385 + 3385) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 3385 * (3 : ZMod 887441251) ^ 3385 := by rw [pow_add]
          _ = 308073434 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 887441251) ^ 13541 = 97227111 := by
        calc
          (3 : ZMod 887441251) ^ 13541 = (3 : ZMod 887441251) ^ (6770 + 6770 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 6770 * (3 : ZMod 887441251) ^ 6770) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 97227111 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 887441251) ^ 27082 = 825952974 := by
        calc
          (3 : ZMod 887441251) ^ 27082 = (3 : ZMod 887441251) ^ (13541 + 13541) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 13541 * (3 : ZMod 887441251) ^ 13541 := by rw [pow_add]
          _ = 825952974 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 887441251) ^ 54165 = 723722645 := by
        calc
          (3 : ZMod 887441251) ^ 54165 = (3 : ZMod 887441251) ^ (27082 + 27082 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 27082 * (3 : ZMod 887441251) ^ 27082) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 723722645 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 887441251) ^ 108330 = 710156043 := by
        calc
          (3 : ZMod 887441251) ^ 108330 = (3 : ZMod 887441251) ^ (54165 + 54165) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 54165 * (3 : ZMod 887441251) ^ 54165 := by rw [pow_add]
          _ = 710156043 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 887441251) ^ 216660 = 545828035 := by
        calc
          (3 : ZMod 887441251) ^ 216660 = (3 : ZMod 887441251) ^ (108330 + 108330) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 108330 * (3 : ZMod 887441251) ^ 108330 := by rw [pow_add]
          _ = 545828035 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 887441251) ^ 433320 = 797302707 := by
        calc
          (3 : ZMod 887441251) ^ 433320 = (3 : ZMod 887441251) ^ (216660 + 216660) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 216660 * (3 : ZMod 887441251) ^ 216660 := by rw [pow_add]
          _ = 797302707 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 887441251) ^ 866641 = 832937097 := by
        calc
          (3 : ZMod 887441251) ^ 866641 = (3 : ZMod 887441251) ^ (433320 + 433320 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 433320 * (3 : ZMod 887441251) ^ 433320) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 832937097 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 887441251) ^ 1733283 = 57748421 := by
        calc
          (3 : ZMod 887441251) ^ 1733283 = (3 : ZMod 887441251) ^ (866641 + 866641 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 866641 * (3 : ZMod 887441251) ^ 866641) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 57748421 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 887441251) ^ 3466567 = 445531143 := by
        calc
          (3 : ZMod 887441251) ^ 3466567 = (3 : ZMod 887441251) ^ (1733283 + 1733283 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 1733283 * (3 : ZMod 887441251) ^ 1733283) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 445531143 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 887441251) ^ 6933134 = 874938176 := by
        calc
          (3 : ZMod 887441251) ^ 6933134 = (3 : ZMod 887441251) ^ (3466567 + 3466567) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 3466567 * (3 : ZMod 887441251) ^ 3466567 := by rw [pow_add]
          _ = 874938176 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 887441251) ^ 13866269 = 787539662 := by
        calc
          (3 : ZMod 887441251) ^ 13866269 = (3 : ZMod 887441251) ^ (6933134 + 6933134 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 6933134 * (3 : ZMod 887441251) ^ 6933134) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 787539662 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 887441251) ^ 27732539 = 547807462 := by
        calc
          (3 : ZMod 887441251) ^ 27732539 = (3 : ZMod 887441251) ^ (13866269 + 13866269 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 13866269 * (3 : ZMod 887441251) ^ 13866269) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 547807462 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 887441251) ^ 55465078 = 599567335 := by
        calc
          (3 : ZMod 887441251) ^ 55465078 = (3 : ZMod 887441251) ^ (27732539 + 27732539) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 27732539 * (3 : ZMod 887441251) ^ 27732539 := by rw [pow_add]
          _ = 599567335 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 887441251) ^ 110930156 = 298116409 := by
        calc
          (3 : ZMod 887441251) ^ 110930156 = (3 : ZMod 887441251) ^ (55465078 + 55465078) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 55465078 * (3 : ZMod 887441251) ^ 55465078 := by rw [pow_add]
          _ = 298116409 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 887441251) ^ 221860312 = 860110868 := by
        calc
          (3 : ZMod 887441251) ^ 221860312 = (3 : ZMod 887441251) ^ (110930156 + 110930156) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 110930156 * (3 : ZMod 887441251) ^ 110930156 := by rw [pow_add]
          _ = 860110868 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 887441251) ^ 443720625 = 887441250 := by
        calc
          (3 : ZMod 887441251) ^ 443720625 = (3 : ZMod 887441251) ^ (221860312 + 221860312 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 221860312 * (3 : ZMod 887441251) ^ 221860312) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 887441250 := by rw [factor_0_27]; decide
      change (3 : ZMod 887441251) ^ 443720625 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (3 : ZMod 887441251) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 887441251) ^ 2 = 9 := by
        calc
          (3 : ZMod 887441251) ^ 2 = (3 : ZMod 887441251) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 1 * (3 : ZMod 887441251) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 887441251) ^ 4 = 81 := by
        calc
          (3 : ZMod 887441251) ^ 4 = (3 : ZMod 887441251) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 2 * (3 : ZMod 887441251) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 887441251) ^ 8 = 6561 := by
        calc
          (3 : ZMod 887441251) ^ 8 = (3 : ZMod 887441251) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 4 * (3 : ZMod 887441251) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 887441251) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 887441251) ^ 17 = (3 : ZMod 887441251) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 8 * (3 : ZMod 887441251) ^ 8) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 887441251) ^ 35 = 796673654 := by
        calc
          (3 : ZMod 887441251) ^ 35 = (3 : ZMod 887441251) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 17 * (3 : ZMod 887441251) ^ 17) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 796673654 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 887441251) ^ 70 = 574420689 := by
        calc
          (3 : ZMod 887441251) ^ 70 = (3 : ZMod 887441251) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 35 * (3 : ZMod 887441251) ^ 35 := by rw [pow_add]
          _ = 574420689 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 887441251) ^ 141 = 608081778 := by
        calc
          (3 : ZMod 887441251) ^ 141 = (3 : ZMod 887441251) ^ (70 + 70 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 70 * (3 : ZMod 887441251) ^ 70) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 608081778 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 887441251) ^ 282 = 200592581 := by
        calc
          (3 : ZMod 887441251) ^ 282 = (3 : ZMod 887441251) ^ (141 + 141) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 141 * (3 : ZMod 887441251) ^ 141 := by rw [pow_add]
          _ = 200592581 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 887441251) ^ 564 = 309658163 := by
        calc
          (3 : ZMod 887441251) ^ 564 = (3 : ZMod 887441251) ^ (282 + 282) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 282 * (3 : ZMod 887441251) ^ 282 := by rw [pow_add]
          _ = 309658163 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 887441251) ^ 1128 = 764413150 := by
        calc
          (3 : ZMod 887441251) ^ 1128 = (3 : ZMod 887441251) ^ (564 + 564) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 564 * (3 : ZMod 887441251) ^ 564 := by rw [pow_add]
          _ = 764413150 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 887441251) ^ 2256 = 527251772 := by
        calc
          (3 : ZMod 887441251) ^ 2256 = (3 : ZMod 887441251) ^ (1128 + 1128) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 1128 * (3 : ZMod 887441251) ^ 1128 := by rw [pow_add]
          _ = 527251772 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 887441251) ^ 4513 = 753622009 := by
        calc
          (3 : ZMod 887441251) ^ 4513 = (3 : ZMod 887441251) ^ (2256 + 2256 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 2256 * (3 : ZMod 887441251) ^ 2256) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 753622009 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 887441251) ^ 9027 = 259186988 := by
        calc
          (3 : ZMod 887441251) ^ 9027 = (3 : ZMod 887441251) ^ (4513 + 4513 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 4513 * (3 : ZMod 887441251) ^ 4513) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 259186988 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 887441251) ^ 18055 = 363791192 := by
        calc
          (3 : ZMod 887441251) ^ 18055 = (3 : ZMod 887441251) ^ (9027 + 9027 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 9027 * (3 : ZMod 887441251) ^ 9027) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 363791192 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 887441251) ^ 36110 = 147187207 := by
        calc
          (3 : ZMod 887441251) ^ 36110 = (3 : ZMod 887441251) ^ (18055 + 18055) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 18055 * (3 : ZMod 887441251) ^ 18055 := by rw [pow_add]
          _ = 147187207 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 887441251) ^ 72220 = 75649009 := by
        calc
          (3 : ZMod 887441251) ^ 72220 = (3 : ZMod 887441251) ^ (36110 + 36110) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 36110 * (3 : ZMod 887441251) ^ 36110 := by rw [pow_add]
          _ = 75649009 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 887441251) ^ 144440 = 275217210 := by
        calc
          (3 : ZMod 887441251) ^ 144440 = (3 : ZMod 887441251) ^ (72220 + 72220) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 72220 * (3 : ZMod 887441251) ^ 72220 := by rw [pow_add]
          _ = 275217210 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 887441251) ^ 288880 = 637598771 := by
        calc
          (3 : ZMod 887441251) ^ 288880 = (3 : ZMod 887441251) ^ (144440 + 144440) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 144440 * (3 : ZMod 887441251) ^ 144440 := by rw [pow_add]
          _ = 637598771 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 887441251) ^ 577761 = 807913274 := by
        calc
          (3 : ZMod 887441251) ^ 577761 = (3 : ZMod 887441251) ^ (288880 + 288880 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 288880 * (3 : ZMod 887441251) ^ 288880) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 807913274 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 887441251) ^ 1155522 = 286049386 := by
        calc
          (3 : ZMod 887441251) ^ 1155522 = (3 : ZMod 887441251) ^ (577761 + 577761) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 577761 * (3 : ZMod 887441251) ^ 577761 := by rw [pow_add]
          _ = 286049386 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 887441251) ^ 2311044 = 757242054 := by
        calc
          (3 : ZMod 887441251) ^ 2311044 = (3 : ZMod 887441251) ^ (1155522 + 1155522) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 1155522 * (3 : ZMod 887441251) ^ 1155522 := by rw [pow_add]
          _ = 757242054 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 887441251) ^ 4622089 = 16752420 := by
        calc
          (3 : ZMod 887441251) ^ 4622089 = (3 : ZMod 887441251) ^ (2311044 + 2311044 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 2311044 * (3 : ZMod 887441251) ^ 2311044) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 16752420 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 887441251) ^ 9244179 = 126244233 := by
        calc
          (3 : ZMod 887441251) ^ 9244179 = (3 : ZMod 887441251) ^ (4622089 + 4622089 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 4622089 * (3 : ZMod 887441251) ^ 4622089) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 126244233 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 887441251) ^ 18488359 = 389341452 := by
        calc
          (3 : ZMod 887441251) ^ 18488359 = (3 : ZMod 887441251) ^ (9244179 + 9244179 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 9244179 * (3 : ZMod 887441251) ^ 9244179) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 389341452 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 887441251) ^ 36976718 = 268353757 := by
        calc
          (3 : ZMod 887441251) ^ 36976718 = (3 : ZMod 887441251) ^ (18488359 + 18488359) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 18488359 * (3 : ZMod 887441251) ^ 18488359 := by rw [pow_add]
          _ = 268353757 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 887441251) ^ 73953437 = 873776060 := by
        calc
          (3 : ZMod 887441251) ^ 73953437 = (3 : ZMod 887441251) ^ (36976718 + 36976718 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 36976718 * (3 : ZMod 887441251) ^ 36976718) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 873776060 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 887441251) ^ 147906875 = 846445677 := by
        calc
          (3 : ZMod 887441251) ^ 147906875 = (3 : ZMod 887441251) ^ (73953437 + 73953437 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 73953437 * (3 : ZMod 887441251) ^ 73953437) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 846445677 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 887441251) ^ 295813750 = 846445676 := by
        calc
          (3 : ZMod 887441251) ^ 295813750 = (3 : ZMod 887441251) ^ (147906875 + 147906875) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 147906875 * (3 : ZMod 887441251) ^ 147906875 := by rw [pow_add]
          _ = 846445676 := by rw [factor_1_27]; decide
      change (3 : ZMod 887441251) ^ 295813750 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (3 : ZMod 887441251) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 887441251) ^ 2 = 9 := by
        calc
          (3 : ZMod 887441251) ^ 2 = (3 : ZMod 887441251) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 1 * (3 : ZMod 887441251) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 887441251) ^ 5 = 243 := by
        calc
          (3 : ZMod 887441251) ^ 5 = (3 : ZMod 887441251) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 2 * (3 : ZMod 887441251) ^ 2) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 887441251) ^ 10 = 59049 := by
        calc
          (3 : ZMod 887441251) ^ 10 = (3 : ZMod 887441251) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 5 * (3 : ZMod 887441251) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 887441251) ^ 21 = 698499442 := by
        calc
          (3 : ZMod 887441251) ^ 21 = (3 : ZMod 887441251) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 10 * (3 : ZMod 887441251) ^ 10) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 698499442 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 887441251) ^ 42 = 278105585 := by
        calc
          (3 : ZMod 887441251) ^ 42 = (3 : ZMod 887441251) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 21 * (3 : ZMod 887441251) ^ 21 := by rw [pow_add]
          _ = 278105585 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 887441251) ^ 84 = 767385984 := by
        calc
          (3 : ZMod 887441251) ^ 84 = (3 : ZMod 887441251) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 42 * (3 : ZMod 887441251) ^ 42 := by rw [pow_add]
          _ = 767385984 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 887441251) ^ 169 = 297119739 := by
        calc
          (3 : ZMod 887441251) ^ 169 = (3 : ZMod 887441251) ^ (84 + 84 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 84 * (3 : ZMod 887441251) ^ 84) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 297119739 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 887441251) ^ 338 = 437335957 := by
        calc
          (3 : ZMod 887441251) ^ 338 = (3 : ZMod 887441251) ^ (169 + 169) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 169 * (3 : ZMod 887441251) ^ 169 := by rw [pow_add]
          _ = 437335957 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 887441251) ^ 677 = 574434062 := by
        calc
          (3 : ZMod 887441251) ^ 677 = (3 : ZMod 887441251) ^ (338 + 338 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 338 * (3 : ZMod 887441251) ^ 338) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 574434062 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 887441251) ^ 1354 = 454341737 := by
        calc
          (3 : ZMod 887441251) ^ 1354 = (3 : ZMod 887441251) ^ (677 + 677) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 677 * (3 : ZMod 887441251) ^ 677 := by rw [pow_add]
          _ = 454341737 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 887441251) ^ 2708 = 249293629 := by
        calc
          (3 : ZMod 887441251) ^ 2708 = (3 : ZMod 887441251) ^ (1354 + 1354) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 1354 * (3 : ZMod 887441251) ^ 1354 := by rw [pow_add]
          _ = 249293629 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 887441251) ^ 5416 = 551858614 := by
        calc
          (3 : ZMod 887441251) ^ 5416 = (3 : ZMod 887441251) ^ (2708 + 2708) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 2708 * (3 : ZMod 887441251) ^ 2708 := by rw [pow_add]
          _ = 551858614 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 887441251) ^ 10833 = 520010797 := by
        calc
          (3 : ZMod 887441251) ^ 10833 = (3 : ZMod 887441251) ^ (5416 + 5416 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 5416 * (3 : ZMod 887441251) ^ 5416) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 520010797 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 887441251) ^ 21666 = 226007580 := by
        calc
          (3 : ZMod 887441251) ^ 21666 = (3 : ZMod 887441251) ^ (10833 + 10833) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 10833 * (3 : ZMod 887441251) ^ 10833 := by rw [pow_add]
          _ = 226007580 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 887441251) ^ 43332 = 160362057 := by
        calc
          (3 : ZMod 887441251) ^ 43332 = (3 : ZMod 887441251) ^ (21666 + 21666) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 21666 * (3 : ZMod 887441251) ^ 21666 := by rw [pow_add]
          _ = 160362057 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 887441251) ^ 86664 = 734993569 := by
        calc
          (3 : ZMod 887441251) ^ 86664 = (3 : ZMod 887441251) ^ (43332 + 43332) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 43332 * (3 : ZMod 887441251) ^ 43332 := by rw [pow_add]
          _ = 734993569 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 887441251) ^ 173328 = 239927642 := by
        calc
          (3 : ZMod 887441251) ^ 173328 = (3 : ZMod 887441251) ^ (86664 + 86664) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 86664 * (3 : ZMod 887441251) ^ 86664 := by rw [pow_add]
          _ = 239927642 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 887441251) ^ 346656 = 704477341 := by
        calc
          (3 : ZMod 887441251) ^ 346656 = (3 : ZMod 887441251) ^ (173328 + 173328) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 173328 * (3 : ZMod 887441251) ^ 173328 := by rw [pow_add]
          _ = 704477341 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 887441251) ^ 693313 = 61365451 := by
        calc
          (3 : ZMod 887441251) ^ 693313 = (3 : ZMod 887441251) ^ (346656 + 346656 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 346656 * (3 : ZMod 887441251) ^ 346656) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 61365451 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 887441251) ^ 1386626 = 68650057 := by
        calc
          (3 : ZMod 887441251) ^ 1386626 = (3 : ZMod 887441251) ^ (693313 + 693313) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 693313 * (3 : ZMod 887441251) ^ 693313 := by rw [pow_add]
          _ = 68650057 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 887441251) ^ 2773253 = 602572999 := by
        calc
          (3 : ZMod 887441251) ^ 2773253 = (3 : ZMod 887441251) ^ (1386626 + 1386626 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 1386626 * (3 : ZMod 887441251) ^ 1386626) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 602572999 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 887441251) ^ 5546507 = 461150011 := by
        calc
          (3 : ZMod 887441251) ^ 5546507 = (3 : ZMod 887441251) ^ (2773253 + 2773253 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 2773253 * (3 : ZMod 887441251) ^ 2773253) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 461150011 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 887441251) ^ 11093015 = 409119327 := by
        calc
          (3 : ZMod 887441251) ^ 11093015 = (3 : ZMod 887441251) ^ (5546507 + 5546507 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 5546507 * (3 : ZMod 887441251) ^ 5546507) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 409119327 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 887441251) ^ 22186031 = 389654435 := by
        calc
          (3 : ZMod 887441251) ^ 22186031 = (3 : ZMod 887441251) ^ (11093015 + 11093015 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 11093015 * (3 : ZMod 887441251) ^ 11093015) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 389654435 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 887441251) ^ 44372062 = 678519942 := by
        calc
          (3 : ZMod 887441251) ^ 44372062 = (3 : ZMod 887441251) ^ (22186031 + 22186031) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 22186031 * (3 : ZMod 887441251) ^ 22186031 := by rw [pow_add]
          _ = 678519942 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 887441251) ^ 88744125 = 698011508 := by
        calc
          (3 : ZMod 887441251) ^ 88744125 = (3 : ZMod 887441251) ^ (44372062 + 44372062 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 44372062 * (3 : ZMod 887441251) ^ 44372062) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 698011508 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 887441251) ^ 177488250 = 7424866 := by
        calc
          (3 : ZMod 887441251) ^ 177488250 = (3 : ZMod 887441251) ^ (88744125 + 88744125) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 88744125 * (3 : ZMod 887441251) ^ 88744125 := by rw [pow_add]
          _ = 7424866 := by rw [factor_2_26]; decide
      change (3 : ZMod 887441251) ^ 177488250 ≠ 1
      rw [factor_2_27]
      decide
    ·
      have factor_3_0 : (3 : ZMod 887441251) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 887441251) ^ 2 = 9 := by
        calc
          (3 : ZMod 887441251) ^ 2 = (3 : ZMod 887441251) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 1 * (3 : ZMod 887441251) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 887441251) ^ 4 = 81 := by
        calc
          (3 : ZMod 887441251) ^ 4 = (3 : ZMod 887441251) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 2 * (3 : ZMod 887441251) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 887441251) ^ 9 = 19683 := by
        calc
          (3 : ZMod 887441251) ^ 9 = (3 : ZMod 887441251) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 4 * (3 : ZMod 887441251) ^ 4) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 887441251) ^ 19 = 274820216 := by
        calc
          (3 : ZMod 887441251) ^ 19 = (3 : ZMod 887441251) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 9 * (3 : ZMod 887441251) ^ 9) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 274820216 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 887441251) ^ 38 = 211598634 := by
        calc
          (3 : ZMod 887441251) ^ 38 = (3 : ZMod 887441251) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 19 * (3 : ZMod 887441251) ^ 19 := by rw [pow_add]
          _ = 211598634 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 887441251) ^ 76 = 767853060 := by
        calc
          (3 : ZMod 887441251) ^ 76 = (3 : ZMod 887441251) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 38 * (3 : ZMod 887441251) ^ 38 := by rw [pow_add]
          _ = 767853060 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 887441251) ^ 152 = 468798484 := by
        calc
          (3 : ZMod 887441251) ^ 152 = (3 : ZMod 887441251) ^ (76 + 76) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 76 * (3 : ZMod 887441251) ^ 76 := by rw [pow_add]
          _ = 468798484 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 887441251) ^ 304 = 654666420 := by
        calc
          (3 : ZMod 887441251) ^ 304 = (3 : ZMod 887441251) ^ (152 + 152) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 152 * (3 : ZMod 887441251) ^ 152 := by rw [pow_add]
          _ = 654666420 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 887441251) ^ 608 = 422185738 := by
        calc
          (3 : ZMod 887441251) ^ 608 = (3 : ZMod 887441251) ^ (304 + 304) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 304 * (3 : ZMod 887441251) ^ 304 := by rw [pow_add]
          _ = 422185738 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 887441251) ^ 1217 = 731123693 := by
        calc
          (3 : ZMod 887441251) ^ 1217 = (3 : ZMod 887441251) ^ (608 + 608 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 608 * (3 : ZMod 887441251) ^ 608) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 731123693 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 887441251) ^ 2434 = 583606446 := by
        calc
          (3 : ZMod 887441251) ^ 2434 = (3 : ZMod 887441251) ^ (1217 + 1217) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 1217 * (3 : ZMod 887441251) ^ 1217 := by rw [pow_add]
          _ = 583606446 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 887441251) ^ 4868 = 686801075 := by
        calc
          (3 : ZMod 887441251) ^ 4868 = (3 : ZMod 887441251) ^ (2434 + 2434) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 2434 * (3 : ZMod 887441251) ^ 2434 := by rw [pow_add]
          _ = 686801075 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 887441251) ^ 9737 = 403341927 := by
        calc
          (3 : ZMod 887441251) ^ 9737 = (3 : ZMod 887441251) ^ (4868 + 4868 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 4868 * (3 : ZMod 887441251) ^ 4868) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 403341927 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 887441251) ^ 19475 = 613134686 := by
        calc
          (3 : ZMod 887441251) ^ 19475 = (3 : ZMod 887441251) ^ (9737 + 9737 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 9737 * (3 : ZMod 887441251) ^ 9737) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 613134686 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 887441251) ^ 38950 = 581422788 := by
        calc
          (3 : ZMod 887441251) ^ 38950 = (3 : ZMod 887441251) ^ (19475 + 19475) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 19475 * (3 : ZMod 887441251) ^ 19475 := by rw [pow_add]
          _ = 581422788 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 887441251) ^ 77900 = 451661050 := by
        calc
          (3 : ZMod 887441251) ^ 77900 = (3 : ZMod 887441251) ^ (38950 + 38950) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 38950 * (3 : ZMod 887441251) ^ 38950 := by rw [pow_add]
          _ = 451661050 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 887441251) ^ 155800 = 524540716 := by
        calc
          (3 : ZMod 887441251) ^ 155800 = (3 : ZMod 887441251) ^ (77900 + 77900) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 77900 * (3 : ZMod 887441251) ^ 77900 := by rw [pow_add]
          _ = 524540716 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 887441251) ^ 311601 = 492234429 := by
        calc
          (3 : ZMod 887441251) ^ 311601 = (3 : ZMod 887441251) ^ (155800 + 155800 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 155800 * (3 : ZMod 887441251) ^ 155800) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 492234429 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 887441251) ^ 623203 = 594093204 := by
        calc
          (3 : ZMod 887441251) ^ 623203 = (3 : ZMod 887441251) ^ (311601 + 311601 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 311601 * (3 : ZMod 887441251) ^ 311601) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 594093204 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 887441251) ^ 1246406 = 30126577 := by
        calc
          (3 : ZMod 887441251) ^ 1246406 = (3 : ZMod 887441251) ^ (623203 + 623203) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 623203 * (3 : ZMod 887441251) ^ 623203 := by rw [pow_add]
          _ = 30126577 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 887441251) ^ 2492812 = 513425452 := by
        calc
          (3 : ZMod 887441251) ^ 2492812 = (3 : ZMod 887441251) ^ (1246406 + 1246406) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 1246406 * (3 : ZMod 887441251) ^ 1246406 := by rw [pow_add]
          _ = 513425452 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 887441251) ^ 4985625 = 71997420 := by
        calc
          (3 : ZMod 887441251) ^ 4985625 = (3 : ZMod 887441251) ^ (2492812 + 2492812 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 2492812 * (3 : ZMod 887441251) ^ 2492812) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 71997420 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 887441251) ^ 9971250 = 720087806 := by
        calc
          (3 : ZMod 887441251) ^ 9971250 = (3 : ZMod 887441251) ^ (4985625 + 4985625) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 4985625 * (3 : ZMod 887441251) ^ 4985625 := by rw [pow_add]
          _ = 720087806 := by rw [factor_3_22]; decide
      change (3 : ZMod 887441251) ^ 9971250 ≠ 1
      rw [factor_3_23]
      decide
    ·
      have factor_4_0 : (3 : ZMod 887441251) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 887441251) ^ 2 = 9 := by
        calc
          (3 : ZMod 887441251) ^ 2 = (3 : ZMod 887441251) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 1 * (3 : ZMod 887441251) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 887441251) ^ 5 = 243 := by
        calc
          (3 : ZMod 887441251) ^ 5 = (3 : ZMod 887441251) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 2 * (3 : ZMod 887441251) ^ 2) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 887441251) ^ 10 = 59049 := by
        calc
          (3 : ZMod 887441251) ^ 10 = (3 : ZMod 887441251) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 5 * (3 : ZMod 887441251) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 887441251) ^ 20 = 824460648 := by
        calc
          (3 : ZMod 887441251) ^ 20 = (3 : ZMod 887441251) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 10 * (3 : ZMod 887441251) ^ 10 := by rw [pow_add]
          _ = 824460648 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 887441251) ^ 40 = 129505204 := by
        calc
          (3 : ZMod 887441251) ^ 40 = (3 : ZMod 887441251) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 20 * (3 : ZMod 887441251) ^ 20 := by rw [pow_add]
          _ = 129505204 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 887441251) ^ 81 = 225630870 := by
        calc
          (3 : ZMod 887441251) ^ 81 = (3 : ZMod 887441251) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 40 * (3 : ZMod 887441251) ^ 40) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 225630870 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 887441251) ^ 162 = 126739273 := by
        calc
          (3 : ZMod 887441251) ^ 162 = (3 : ZMod 887441251) ^ (81 + 81) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 81 * (3 : ZMod 887441251) ^ 81 := by rw [pow_add]
          _ = 126739273 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 887441251) ^ 325 = 575983808 := by
        calc
          (3 : ZMod 887441251) ^ 325 = (3 : ZMod 887441251) ^ (162 + 162 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 162 * (3 : ZMod 887441251) ^ 162) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 575983808 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 887441251) ^ 651 = 242628817 := by
        calc
          (3 : ZMod 887441251) ^ 651 = (3 : ZMod 887441251) ^ (325 + 325 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 325 * (3 : ZMod 887441251) ^ 325) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 242628817 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 887441251) ^ 1303 = 851179861 := by
        calc
          (3 : ZMod 887441251) ^ 1303 = (3 : ZMod 887441251) ^ (651 + 651 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 651 * (3 : ZMod 887441251) ^ 651) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 851179861 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 887441251) ^ 2607 = 390237563 := by
        calc
          (3 : ZMod 887441251) ^ 2607 = (3 : ZMod 887441251) ^ (1303 + 1303 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 1303 * (3 : ZMod 887441251) ^ 1303) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 390237563 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 887441251) ^ 5214 = 283483477 := by
        calc
          (3 : ZMod 887441251) ^ 5214 = (3 : ZMod 887441251) ^ (2607 + 2607) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 2607 * (3 : ZMod 887441251) ^ 2607 := by rw [pow_add]
          _ = 283483477 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 887441251) ^ 10429 = 870011427 := by
        calc
          (3 : ZMod 887441251) ^ 10429 = (3 : ZMod 887441251) ^ (5214 + 5214 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 5214 * (3 : ZMod 887441251) ^ 5214) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 870011427 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 887441251) ^ 20859 = 341324685 := by
        calc
          (3 : ZMod 887441251) ^ 20859 = (3 : ZMod 887441251) ^ (10429 + 10429 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 10429 * (3 : ZMod 887441251) ^ 10429) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 341324685 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 887441251) ^ 41718 = 384602567 := by
        calc
          (3 : ZMod 887441251) ^ 41718 = (3 : ZMod 887441251) ^ (20859 + 20859) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 20859 * (3 : ZMod 887441251) ^ 20859 := by rw [pow_add]
          _ = 384602567 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 887441251) ^ 83437 = 788644525 := by
        calc
          (3 : ZMod 887441251) ^ 83437 = (3 : ZMod 887441251) ^ (41718 + 41718 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 41718 * (3 : ZMod 887441251) ^ 41718) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 788644525 := by rw [factor_4_15]; decide
      have factor_4_17 : (3 : ZMod 887441251) ^ 166875 = 286283314 := by
        calc
          (3 : ZMod 887441251) ^ 166875 = (3 : ZMod 887441251) ^ (83437 + 83437 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = ((3 : ZMod 887441251) ^ 83437 * (3 : ZMod 887441251) ^ 83437) * (3 : ZMod 887441251) := by rw [pow_succ, pow_add]
          _ = 286283314 := by rw [factor_4_16]; decide
      have factor_4_18 : (3 : ZMod 887441251) ^ 333750 = 689314288 := by
        calc
          (3 : ZMod 887441251) ^ 333750 = (3 : ZMod 887441251) ^ (166875 + 166875) :=
            congrArg (fun n : ℕ => (3 : ZMod 887441251) ^ n) (by norm_num)
          _ = (3 : ZMod 887441251) ^ 166875 * (3 : ZMod 887441251) ^ 166875 := by rw [pow_add]
          _ = 689314288 := by rw [factor_4_17]; decide
      change (3 : ZMod 887441251) ^ 333750 ≠ 1
      rw [factor_4_18]
      decide

#print axioms prime_lucas_887441251

end TotientTailPeriodKiller
end Erdos249257
