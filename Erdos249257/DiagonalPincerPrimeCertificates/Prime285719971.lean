import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_285719971 : Nat.Prime 285719971 := by
  apply lucas_primality 285719971 (3 : ZMod 285719971)
  ·
      have fermat_0 : (3 : ZMod 285719971) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 285719971) ^ 2 = 9 := by
        calc
          (3 : ZMod 285719971) ^ 2 = (3 : ZMod 285719971) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 1 * (3 : ZMod 285719971) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 285719971) ^ 4 = 81 := by
        calc
          (3 : ZMod 285719971) ^ 4 = (3 : ZMod 285719971) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 2 * (3 : ZMod 285719971) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 285719971) ^ 8 = 6561 := by
        calc
          (3 : ZMod 285719971) ^ 8 = (3 : ZMod 285719971) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 4 * (3 : ZMod 285719971) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 285719971) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 285719971) ^ 17 = (3 : ZMod 285719971) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 8 * (3 : ZMod 285719971) ^ 8) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 285719971) ^ 34 = 141086815 := by
        calc
          (3 : ZMod 285719971) ^ 34 = (3 : ZMod 285719971) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 17 * (3 : ZMod 285719971) ^ 17 := by rw [pow_add]
          _ = 141086815 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 285719971) ^ 68 = 142491179 := by
        calc
          (3 : ZMod 285719971) ^ 68 = (3 : ZMod 285719971) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 34 * (3 : ZMod 285719971) ^ 34 := by rw [pow_add]
          _ = 142491179 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 285719971) ^ 136 = 86958239 := by
        calc
          (3 : ZMod 285719971) ^ 136 = (3 : ZMod 285719971) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 68 * (3 : ZMod 285719971) ^ 68 := by rw [pow_add]
          _ = 86958239 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 285719971) ^ 272 = 8641984 := by
        calc
          (3 : ZMod 285719971) ^ 272 = (3 : ZMod 285719971) ^ (136 + 136) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 136 * (3 : ZMod 285719971) ^ 136 := by rw [pow_add]
          _ = 8641984 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 285719971) ^ 544 = 115676508 := by
        calc
          (3 : ZMod 285719971) ^ 544 = (3 : ZMod 285719971) ^ (272 + 272) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 272 * (3 : ZMod 285719971) ^ 272 := by rw [pow_add]
          _ = 115676508 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 285719971) ^ 1089 = 164952196 := by
        calc
          (3 : ZMod 285719971) ^ 1089 = (3 : ZMod 285719971) ^ (544 + 544 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 544 * (3 : ZMod 285719971) ^ 544) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 164952196 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 285719971) ^ 2179 = 88151990 := by
        calc
          (3 : ZMod 285719971) ^ 2179 = (3 : ZMod 285719971) ^ (1089 + 1089 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 1089 * (3 : ZMod 285719971) ^ 1089) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 88151990 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 285719971) ^ 4359 = 151913684 := by
        calc
          (3 : ZMod 285719971) ^ 4359 = (3 : ZMod 285719971) ^ (2179 + 2179 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 2179 * (3 : ZMod 285719971) ^ 2179) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 151913684 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 285719971) ^ 8719 = 262195883 := by
        calc
          (3 : ZMod 285719971) ^ 8719 = (3 : ZMod 285719971) ^ (4359 + 4359 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 4359 * (3 : ZMod 285719971) ^ 4359) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 262195883 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 285719971) ^ 17438 = 276398944 := by
        calc
          (3 : ZMod 285719971) ^ 17438 = (3 : ZMod 285719971) ^ (8719 + 8719) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 8719 * (3 : ZMod 285719971) ^ 8719 := by rw [pow_add]
          _ = 276398944 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 285719971) ^ 34877 = 18099089 := by
        calc
          (3 : ZMod 285719971) ^ 34877 = (3 : ZMod 285719971) ^ (17438 + 17438 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 17438 * (3 : ZMod 285719971) ^ 17438) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 18099089 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 285719971) ^ 69755 = 84834973 := by
        calc
          (3 : ZMod 285719971) ^ 69755 = (3 : ZMod 285719971) ^ (34877 + 34877 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 34877 * (3 : ZMod 285719971) ^ 34877) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 84834973 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 285719971) ^ 139511 = 27686748 := by
        calc
          (3 : ZMod 285719971) ^ 139511 = (3 : ZMod 285719971) ^ (69755 + 69755 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 69755 * (3 : ZMod 285719971) ^ 69755) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 27686748 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 285719971) ^ 279023 = 285418145 := by
        calc
          (3 : ZMod 285719971) ^ 279023 = (3 : ZMod 285719971) ^ (139511 + 139511 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 139511 * (3 : ZMod 285719971) ^ 139511) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 285418145 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 285719971) ^ 558046 = 239983498 := by
        calc
          (3 : ZMod 285719971) ^ 558046 = (3 : ZMod 285719971) ^ (279023 + 279023) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 279023 * (3 : ZMod 285719971) ^ 279023 := by rw [pow_add]
          _ = 239983498 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 285719971) ^ 1116093 = 17387212 := by
        calc
          (3 : ZMod 285719971) ^ 1116093 = (3 : ZMod 285719971) ^ (558046 + 558046 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 558046 * (3 : ZMod 285719971) ^ 558046) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 17387212 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 285719971) ^ 2232187 = 234051937 := by
        calc
          (3 : ZMod 285719971) ^ 2232187 = (3 : ZMod 285719971) ^ (1116093 + 1116093 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 1116093 * (3 : ZMod 285719971) ^ 1116093) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 234051937 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 285719971) ^ 4464374 = 46302712 := by
        calc
          (3 : ZMod 285719971) ^ 4464374 = (3 : ZMod 285719971) ^ (2232187 + 2232187) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 2232187 * (3 : ZMod 285719971) ^ 2232187 := by rw [pow_add]
          _ = 46302712 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 285719971) ^ 8928749 = 6001918 := by
        calc
          (3 : ZMod 285719971) ^ 8928749 = (3 : ZMod 285719971) ^ (4464374 + 4464374 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 4464374 * (3 : ZMod 285719971) ^ 4464374) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 6001918 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 285719971) ^ 17857498 = 17174986 := by
        calc
          (3 : ZMod 285719971) ^ 17857498 = (3 : ZMod 285719971) ^ (8928749 + 8928749) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 8928749 * (3 : ZMod 285719971) ^ 8928749 := by rw [pow_add]
          _ = 17174986 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 285719971) ^ 35714996 = 274560057 := by
        calc
          (3 : ZMod 285719971) ^ 35714996 = (3 : ZMod 285719971) ^ (17857498 + 17857498) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 17857498 * (3 : ZMod 285719971) ^ 17857498 := by rw [pow_add]
          _ = 274560057 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 285719971) ^ 71429992 = 59448322 := by
        calc
          (3 : ZMod 285719971) ^ 71429992 = (3 : ZMod 285719971) ^ (35714996 + 35714996) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 35714996 * (3 : ZMod 285719971) ^ 35714996 := by rw [pow_add]
          _ = 59448322 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 285719971) ^ 142859985 = 285719970 := by
        calc
          (3 : ZMod 285719971) ^ 142859985 = (3 : ZMod 285719971) ^ (71429992 + 71429992 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 71429992 * (3 : ZMod 285719971) ^ 71429992) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 285719970 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 285719971) ^ 285719970 = 1 := by
        calc
          (3 : ZMod 285719971) ^ 285719970 = (3 : ZMod 285719971) ^ (142859985 + 142859985) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 142859985 * (3 : ZMod 285719971) ^ 142859985 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (9523999, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (9523999, 1)] : List FactorBlock).map factorBlockValue).prod = 285719971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 285719971) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 285719971) ^ 2 = 9 := by
        calc
          (3 : ZMod 285719971) ^ 2 = (3 : ZMod 285719971) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 1 * (3 : ZMod 285719971) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 285719971) ^ 4 = 81 := by
        calc
          (3 : ZMod 285719971) ^ 4 = (3 : ZMod 285719971) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 2 * (3 : ZMod 285719971) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 285719971) ^ 8 = 6561 := by
        calc
          (3 : ZMod 285719971) ^ 8 = (3 : ZMod 285719971) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 4 * (3 : ZMod 285719971) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 285719971) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 285719971) ^ 17 = (3 : ZMod 285719971) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 8 * (3 : ZMod 285719971) ^ 8) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 285719971) ^ 34 = 141086815 := by
        calc
          (3 : ZMod 285719971) ^ 34 = (3 : ZMod 285719971) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 17 * (3 : ZMod 285719971) ^ 17 := by rw [pow_add]
          _ = 141086815 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 285719971) ^ 68 = 142491179 := by
        calc
          (3 : ZMod 285719971) ^ 68 = (3 : ZMod 285719971) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 34 * (3 : ZMod 285719971) ^ 34 := by rw [pow_add]
          _ = 142491179 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 285719971) ^ 136 = 86958239 := by
        calc
          (3 : ZMod 285719971) ^ 136 = (3 : ZMod 285719971) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 68 * (3 : ZMod 285719971) ^ 68 := by rw [pow_add]
          _ = 86958239 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 285719971) ^ 272 = 8641984 := by
        calc
          (3 : ZMod 285719971) ^ 272 = (3 : ZMod 285719971) ^ (136 + 136) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 136 * (3 : ZMod 285719971) ^ 136 := by rw [pow_add]
          _ = 8641984 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 285719971) ^ 544 = 115676508 := by
        calc
          (3 : ZMod 285719971) ^ 544 = (3 : ZMod 285719971) ^ (272 + 272) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 272 * (3 : ZMod 285719971) ^ 272 := by rw [pow_add]
          _ = 115676508 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 285719971) ^ 1089 = 164952196 := by
        calc
          (3 : ZMod 285719971) ^ 1089 = (3 : ZMod 285719971) ^ (544 + 544 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 544 * (3 : ZMod 285719971) ^ 544) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 164952196 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 285719971) ^ 2179 = 88151990 := by
        calc
          (3 : ZMod 285719971) ^ 2179 = (3 : ZMod 285719971) ^ (1089 + 1089 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 1089 * (3 : ZMod 285719971) ^ 1089) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 88151990 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 285719971) ^ 4359 = 151913684 := by
        calc
          (3 : ZMod 285719971) ^ 4359 = (3 : ZMod 285719971) ^ (2179 + 2179 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 2179 * (3 : ZMod 285719971) ^ 2179) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 151913684 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 285719971) ^ 8719 = 262195883 := by
        calc
          (3 : ZMod 285719971) ^ 8719 = (3 : ZMod 285719971) ^ (4359 + 4359 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 4359 * (3 : ZMod 285719971) ^ 4359) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 262195883 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 285719971) ^ 17438 = 276398944 := by
        calc
          (3 : ZMod 285719971) ^ 17438 = (3 : ZMod 285719971) ^ (8719 + 8719) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 8719 * (3 : ZMod 285719971) ^ 8719 := by rw [pow_add]
          _ = 276398944 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 285719971) ^ 34877 = 18099089 := by
        calc
          (3 : ZMod 285719971) ^ 34877 = (3 : ZMod 285719971) ^ (17438 + 17438 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 17438 * (3 : ZMod 285719971) ^ 17438) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 18099089 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 285719971) ^ 69755 = 84834973 := by
        calc
          (3 : ZMod 285719971) ^ 69755 = (3 : ZMod 285719971) ^ (34877 + 34877 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 34877 * (3 : ZMod 285719971) ^ 34877) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 84834973 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 285719971) ^ 139511 = 27686748 := by
        calc
          (3 : ZMod 285719971) ^ 139511 = (3 : ZMod 285719971) ^ (69755 + 69755 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 69755 * (3 : ZMod 285719971) ^ 69755) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 27686748 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 285719971) ^ 279023 = 285418145 := by
        calc
          (3 : ZMod 285719971) ^ 279023 = (3 : ZMod 285719971) ^ (139511 + 139511 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 139511 * (3 : ZMod 285719971) ^ 139511) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 285418145 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 285719971) ^ 558046 = 239983498 := by
        calc
          (3 : ZMod 285719971) ^ 558046 = (3 : ZMod 285719971) ^ (279023 + 279023) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 279023 * (3 : ZMod 285719971) ^ 279023 := by rw [pow_add]
          _ = 239983498 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 285719971) ^ 1116093 = 17387212 := by
        calc
          (3 : ZMod 285719971) ^ 1116093 = (3 : ZMod 285719971) ^ (558046 + 558046 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 558046 * (3 : ZMod 285719971) ^ 558046) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 17387212 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 285719971) ^ 2232187 = 234051937 := by
        calc
          (3 : ZMod 285719971) ^ 2232187 = (3 : ZMod 285719971) ^ (1116093 + 1116093 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 1116093 * (3 : ZMod 285719971) ^ 1116093) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 234051937 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 285719971) ^ 4464374 = 46302712 := by
        calc
          (3 : ZMod 285719971) ^ 4464374 = (3 : ZMod 285719971) ^ (2232187 + 2232187) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 2232187 * (3 : ZMod 285719971) ^ 2232187 := by rw [pow_add]
          _ = 46302712 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 285719971) ^ 8928749 = 6001918 := by
        calc
          (3 : ZMod 285719971) ^ 8928749 = (3 : ZMod 285719971) ^ (4464374 + 4464374 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 4464374 * (3 : ZMod 285719971) ^ 4464374) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 6001918 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 285719971) ^ 17857498 = 17174986 := by
        calc
          (3 : ZMod 285719971) ^ 17857498 = (3 : ZMod 285719971) ^ (8928749 + 8928749) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 8928749 * (3 : ZMod 285719971) ^ 8928749 := by rw [pow_add]
          _ = 17174986 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 285719971) ^ 35714996 = 274560057 := by
        calc
          (3 : ZMod 285719971) ^ 35714996 = (3 : ZMod 285719971) ^ (17857498 + 17857498) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 17857498 * (3 : ZMod 285719971) ^ 17857498 := by rw [pow_add]
          _ = 274560057 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 285719971) ^ 71429992 = 59448322 := by
        calc
          (3 : ZMod 285719971) ^ 71429992 = (3 : ZMod 285719971) ^ (35714996 + 35714996) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 35714996 * (3 : ZMod 285719971) ^ 35714996 := by rw [pow_add]
          _ = 59448322 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 285719971) ^ 142859985 = 285719970 := by
        calc
          (3 : ZMod 285719971) ^ 142859985 = (3 : ZMod 285719971) ^ (71429992 + 71429992 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 71429992 * (3 : ZMod 285719971) ^ 71429992) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 285719970 := by rw [factor_0_26]; decide
      change (3 : ZMod 285719971) ^ 142859985 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (3 : ZMod 285719971) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 285719971) ^ 2 = 9 := by
        calc
          (3 : ZMod 285719971) ^ 2 = (3 : ZMod 285719971) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 1 * (3 : ZMod 285719971) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 285719971) ^ 5 = 243 := by
        calc
          (3 : ZMod 285719971) ^ 5 = (3 : ZMod 285719971) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 2 * (3 : ZMod 285719971) ^ 2) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 285719971) ^ 11 = 177147 := by
        calc
          (3 : ZMod 285719971) ^ 11 = (3 : ZMod 285719971) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 5 * (3 : ZMod 285719971) ^ 5) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 285719971) ^ 22 = 237582770 := by
        calc
          (3 : ZMod 285719971) ^ 22 = (3 : ZMod 285719971) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 11 * (3 : ZMod 285719971) ^ 11 := by rw [pow_add]
          _ = 237582770 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 285719971) ^ 45 = 37273551 := by
        calc
          (3 : ZMod 285719971) ^ 45 = (3 : ZMod 285719971) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 22 * (3 : ZMod 285719971) ^ 22) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 37273551 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 285719971) ^ 90 = 245082507 := by
        calc
          (3 : ZMod 285719971) ^ 90 = (3 : ZMod 285719971) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 45 * (3 : ZMod 285719971) ^ 45 := by rw [pow_add]
          _ = 245082507 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 285719971) ^ 181 = 147376227 := by
        calc
          (3 : ZMod 285719971) ^ 181 = (3 : ZMod 285719971) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 90 * (3 : ZMod 285719971) ^ 90) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 147376227 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 285719971) ^ 363 = 22879556 := by
        calc
          (3 : ZMod 285719971) ^ 363 = (3 : ZMod 285719971) ^ (181 + 181 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 181 * (3 : ZMod 285719971) ^ 181) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 22879556 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 285719971) ^ 726 = 238048674 := by
        calc
          (3 : ZMod 285719971) ^ 726 = (3 : ZMod 285719971) ^ (363 + 363) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 363 * (3 : ZMod 285719971) ^ 363 := by rw [pow_add]
          _ = 238048674 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 285719971) ^ 1453 = 14525110 := by
        calc
          (3 : ZMod 285719971) ^ 1453 = (3 : ZMod 285719971) ^ (726 + 726 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 726 * (3 : ZMod 285719971) ^ 726) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 14525110 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 285719971) ^ 2906 = 51006019 := by
        calc
          (3 : ZMod 285719971) ^ 2906 = (3 : ZMod 285719971) ^ (1453 + 1453) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 1453 * (3 : ZMod 285719971) ^ 1453 := by rw [pow_add]
          _ = 51006019 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 285719971) ^ 5812 = 207046904 := by
        calc
          (3 : ZMod 285719971) ^ 5812 = (3 : ZMod 285719971) ^ (2906 + 2906) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 2906 * (3 : ZMod 285719971) ^ 2906 := by rw [pow_add]
          _ = 207046904 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 285719971) ^ 11625 = 81369930 := by
        calc
          (3 : ZMod 285719971) ^ 11625 = (3 : ZMod 285719971) ^ (5812 + 5812 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 5812 * (3 : ZMod 285719971) ^ 5812) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 81369930 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 285719971) ^ 23251 = 141809016 := by
        calc
          (3 : ZMod 285719971) ^ 23251 = (3 : ZMod 285719971) ^ (11625 + 11625 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 11625 * (3 : ZMod 285719971) ^ 11625) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 141809016 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 285719971) ^ 46503 = 44736111 := by
        calc
          (3 : ZMod 285719971) ^ 46503 = (3 : ZMod 285719971) ^ (23251 + 23251 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 23251 * (3 : ZMod 285719971) ^ 23251) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 44736111 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 285719971) ^ 93007 = 271962636 := by
        calc
          (3 : ZMod 285719971) ^ 93007 = (3 : ZMod 285719971) ^ (46503 + 46503 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 46503 * (3 : ZMod 285719971) ^ 46503) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 271962636 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 285719971) ^ 186015 = 72336490 := by
        calc
          (3 : ZMod 285719971) ^ 186015 = (3 : ZMod 285719971) ^ (93007 + 93007 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 93007 * (3 : ZMod 285719971) ^ 93007) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 72336490 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 285719971) ^ 372031 = 144885472 := by
        calc
          (3 : ZMod 285719971) ^ 372031 = (3 : ZMod 285719971) ^ (186015 + 186015 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 186015 * (3 : ZMod 285719971) ^ 186015) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 144885472 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 285719971) ^ 744062 = 13928086 := by
        calc
          (3 : ZMod 285719971) ^ 744062 = (3 : ZMod 285719971) ^ (372031 + 372031) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 372031 * (3 : ZMod 285719971) ^ 372031 := by rw [pow_add]
          _ = 13928086 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 285719971) ^ 1488124 = 5273149 := by
        calc
          (3 : ZMod 285719971) ^ 1488124 = (3 : ZMod 285719971) ^ (744062 + 744062) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 744062 * (3 : ZMod 285719971) ^ 744062 := by rw [pow_add]
          _ = 5273149 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 285719971) ^ 2976249 = 69835385 := by
        calc
          (3 : ZMod 285719971) ^ 2976249 = (3 : ZMod 285719971) ^ (1488124 + 1488124 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 1488124 * (3 : ZMod 285719971) ^ 1488124) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 69835385 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 285719971) ^ 5952499 = 151985824 := by
        calc
          (3 : ZMod 285719971) ^ 5952499 = (3 : ZMod 285719971) ^ (2976249 + 2976249 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 2976249 * (3 : ZMod 285719971) ^ 2976249) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 151985824 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 285719971) ^ 11904998 = 199770908 := by
        calc
          (3 : ZMod 285719971) ^ 11904998 = (3 : ZMod 285719971) ^ (5952499 + 5952499) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 5952499 * (3 : ZMod 285719971) ^ 5952499 := by rw [pow_add]
          _ = 199770908 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 285719971) ^ 23809997 = 172584146 := by
        calc
          (3 : ZMod 285719971) ^ 23809997 = (3 : ZMod 285719971) ^ (11904998 + 11904998 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 11904998 * (3 : ZMod 285719971) ^ 11904998) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 172584146 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 285719971) ^ 47619995 = 53687503 := by
        calc
          (3 : ZMod 285719971) ^ 47619995 = (3 : ZMod 285719971) ^ (23809997 + 23809997 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 23809997 * (3 : ZMod 285719971) ^ 23809997) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 53687503 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 285719971) ^ 95239990 = 53687502 := by
        calc
          (3 : ZMod 285719971) ^ 95239990 = (3 : ZMod 285719971) ^ (47619995 + 47619995) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 47619995 * (3 : ZMod 285719971) ^ 47619995 := by rw [pow_add]
          _ = 53687502 := by rw [factor_1_25]; decide
      change (3 : ZMod 285719971) ^ 95239990 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (3 : ZMod 285719971) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 285719971) ^ 3 = 27 := by
        calc
          (3 : ZMod 285719971) ^ 3 = (3 : ZMod 285719971) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 1 * (3 : ZMod 285719971) ^ 1) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 285719971) ^ 6 = 729 := by
        calc
          (3 : ZMod 285719971) ^ 6 = (3 : ZMod 285719971) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 3 * (3 : ZMod 285719971) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 285719971) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 285719971) ^ 13 = (3 : ZMod 285719971) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 6 * (3 : ZMod 285719971) ^ 6) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 285719971) ^ 27 = 17178968 := by
        calc
          (3 : ZMod 285719971) ^ 27 = (3 : ZMod 285719971) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 13 * (3 : ZMod 285719971) ^ 13) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 17178968 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 285719971) ^ 54 = 212138776 := by
        calc
          (3 : ZMod 285719971) ^ 54 = (3 : ZMod 285719971) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 27 * (3 : ZMod 285719971) ^ 27 := by rw [pow_add]
          _ = 212138776 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 285719971) ^ 108 = 239757580 := by
        calc
          (3 : ZMod 285719971) ^ 108 = (3 : ZMod 285719971) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 54 * (3 : ZMod 285719971) ^ 54 := by rw [pow_add]
          _ = 239757580 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 285719971) ^ 217 = 52606690 := by
        calc
          (3 : ZMod 285719971) ^ 217 = (3 : ZMod 285719971) ^ (108 + 108 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 108 * (3 : ZMod 285719971) ^ 108) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 52606690 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 285719971) ^ 435 = 10704268 := by
        calc
          (3 : ZMod 285719971) ^ 435 = (3 : ZMod 285719971) ^ (217 + 217 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 217 * (3 : ZMod 285719971) ^ 217) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 10704268 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 285719971) ^ 871 = 77536792 := by
        calc
          (3 : ZMod 285719971) ^ 871 = (3 : ZMod 285719971) ^ (435 + 435 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 435 * (3 : ZMod 285719971) ^ 435) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 77536792 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 285719971) ^ 1743 = 32917390 := by
        calc
          (3 : ZMod 285719971) ^ 1743 = (3 : ZMod 285719971) ^ (871 + 871 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 871 * (3 : ZMod 285719971) ^ 871) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 32917390 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 285719971) ^ 3487 = 154052084 := by
        calc
          (3 : ZMod 285719971) ^ 3487 = (3 : ZMod 285719971) ^ (1743 + 1743 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 1743 * (3 : ZMod 285719971) ^ 1743) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 154052084 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 285719971) ^ 6975 = 229012929 := by
        calc
          (3 : ZMod 285719971) ^ 6975 = (3 : ZMod 285719971) ^ (3487 + 3487 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 3487 * (3 : ZMod 285719971) ^ 3487) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 229012929 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 285719971) ^ 13951 = 164566974 := by
        calc
          (3 : ZMod 285719971) ^ 13951 = (3 : ZMod 285719971) ^ (6975 + 6975 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 6975 * (3 : ZMod 285719971) ^ 6975) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 164566974 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 285719971) ^ 27902 = 45314301 := by
        calc
          (3 : ZMod 285719971) ^ 27902 = (3 : ZMod 285719971) ^ (13951 + 13951) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 13951 * (3 : ZMod 285719971) ^ 13951 := by rw [pow_add]
          _ = 45314301 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 285719971) ^ 55804 = 159493104 := by
        calc
          (3 : ZMod 285719971) ^ 55804 = (3 : ZMod 285719971) ^ (27902 + 27902) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 27902 * (3 : ZMod 285719971) ^ 27902 := by rw [pow_add]
          _ = 159493104 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 285719971) ^ 111609 = 163756596 := by
        calc
          (3 : ZMod 285719971) ^ 111609 = (3 : ZMod 285719971) ^ (55804 + 55804 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 55804 * (3 : ZMod 285719971) ^ 55804) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 163756596 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 285719971) ^ 223218 = 284379635 := by
        calc
          (3 : ZMod 285719971) ^ 223218 = (3 : ZMod 285719971) ^ (111609 + 111609) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 111609 * (3 : ZMod 285719971) ^ 111609 := by rw [pow_add]
          _ = 284379635 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 285719971) ^ 446437 = 251685686 := by
        calc
          (3 : ZMod 285719971) ^ 446437 = (3 : ZMod 285719971) ^ (223218 + 223218 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 223218 * (3 : ZMod 285719971) ^ 223218) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 251685686 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 285719971) ^ 892874 = 78269632 := by
        calc
          (3 : ZMod 285719971) ^ 892874 = (3 : ZMod 285719971) ^ (446437 + 446437) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 446437 * (3 : ZMod 285719971) ^ 446437 := by rw [pow_add]
          _ = 78269632 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 285719971) ^ 1785749 = 184817332 := by
        calc
          (3 : ZMod 285719971) ^ 1785749 = (3 : ZMod 285719971) ^ (892874 + 892874 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 892874 * (3 : ZMod 285719971) ^ 892874) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 184817332 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 285719971) ^ 3571499 = 188970064 := by
        calc
          (3 : ZMod 285719971) ^ 3571499 = (3 : ZMod 285719971) ^ (1785749 + 1785749 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 1785749 * (3 : ZMod 285719971) ^ 1785749) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 188970064 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 285719971) ^ 7142999 = 170835016 := by
        calc
          (3 : ZMod 285719971) ^ 7142999 = (3 : ZMod 285719971) ^ (3571499 + 3571499 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 3571499 * (3 : ZMod 285719971) ^ 3571499) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 170835016 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 285719971) ^ 14285998 = 259178460 := by
        calc
          (3 : ZMod 285719971) ^ 14285998 = (3 : ZMod 285719971) ^ (7142999 + 7142999) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 7142999 * (3 : ZMod 285719971) ^ 7142999 := by rw [pow_add]
          _ = 259178460 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 285719971) ^ 28571997 = 223870647 := by
        calc
          (3 : ZMod 285719971) ^ 28571997 = (3 : ZMod 285719971) ^ (14285998 + 14285998 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 14285998 * (3 : ZMod 285719971) ^ 14285998) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 223870647 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 285719971) ^ 57143994 = 190841127 := by
        calc
          (3 : ZMod 285719971) ^ 57143994 = (3 : ZMod 285719971) ^ (28571997 + 28571997) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 28571997 * (3 : ZMod 285719971) ^ 28571997 := by rw [pow_add]
          _ = 190841127 := by rw [factor_2_24]; decide
      change (3 : ZMod 285719971) ^ 57143994 ≠ 1
      rw [factor_2_25]
      decide
    ·
      have factor_3_0 : (3 : ZMod 285719971) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 285719971) ^ 3 = 27 := by
        calc
          (3 : ZMod 285719971) ^ 3 = (3 : ZMod 285719971) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 1 * (3 : ZMod 285719971) ^ 1) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 285719971) ^ 7 = 2187 := by
        calc
          (3 : ZMod 285719971) ^ 7 = (3 : ZMod 285719971) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 3 * (3 : ZMod 285719971) ^ 3) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 285719971) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 285719971) ^ 15 = (3 : ZMod 285719971) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = ((3 : ZMod 285719971) ^ 7 * (3 : ZMod 285719971) ^ 7) * (3 : ZMod 285719971) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 285719971) ^ 30 = 178112165 := by
        calc
          (3 : ZMod 285719971) ^ 30 = (3 : ZMod 285719971) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (3 : ZMod 285719971) ^ n) (by norm_num)
          _ = (3 : ZMod 285719971) ^ 15 * (3 : ZMod 285719971) ^ 15 := by rw [pow_add]
          _ = 178112165 := by rw [factor_3_3]; decide
      change (3 : ZMod 285719971) ^ 30 ≠ 1
      rw [factor_3_4]
      decide

#print axioms prime_lucas_285719971

end TotientTailPeriodKiller
end Erdos249257
