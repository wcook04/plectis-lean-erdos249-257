import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_35574847613 : Nat.Prime 35574847613 := by
  apply lucas_primality 35574847613 (2 : ZMod 35574847613)
  ·
      have fermat_0 : (2 : ZMod 35574847613) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 35574847613) ^ 2 = 4 := by
        calc
          (2 : ZMod 35574847613) ^ 2 = (2 : ZMod 35574847613) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 1 * (2 : ZMod 35574847613) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 35574847613) ^ 4 = 16 := by
        calc
          (2 : ZMod 35574847613) ^ 4 = (2 : ZMod 35574847613) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 2 * (2 : ZMod 35574847613) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 35574847613) ^ 8 = 256 := by
        calc
          (2 : ZMod 35574847613) ^ 8 = (2 : ZMod 35574847613) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 4 * (2 : ZMod 35574847613) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 35574847613) ^ 16 = 65536 := by
        calc
          (2 : ZMod 35574847613) ^ 16 = (2 : ZMod 35574847613) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 8 * (2 : ZMod 35574847613) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 35574847613) ^ 33 = 8589934592 := by
        calc
          (2 : ZMod 35574847613) ^ 33 = (2 : ZMod 35574847613) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 16 * (2 : ZMod 35574847613) ^ 16) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 8589934592 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 35574847613) ^ 66 = 4840307886 := by
        calc
          (2 : ZMod 35574847613) ^ 66 = (2 : ZMod 35574847613) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 33 * (2 : ZMod 35574847613) ^ 33 := by rw [pow_add]
          _ = 4840307886 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 35574847613) ^ 132 = 32257435626 := by
        calc
          (2 : ZMod 35574847613) ^ 132 = (2 : ZMod 35574847613) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 66 * (2 : ZMod 35574847613) ^ 66 := by rw [pow_add]
          _ = 32257435626 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 35574847613) ^ 265 = 22871039301 := by
        calc
          (2 : ZMod 35574847613) ^ 265 = (2 : ZMod 35574847613) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 132 * (2 : ZMod 35574847613) ^ 132) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 22871039301 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 35574847613) ^ 530 = 5649492885 := by
        calc
          (2 : ZMod 35574847613) ^ 530 = (2 : ZMod 35574847613) ^ (265 + 265) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 265 * (2 : ZMod 35574847613) ^ 265 := by rw [pow_add]
          _ = 5649492885 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 35574847613) ^ 1060 = 10369436997 := by
        calc
          (2 : ZMod 35574847613) ^ 1060 = (2 : ZMod 35574847613) ^ (530 + 530) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 530 * (2 : ZMod 35574847613) ^ 530 := by rw [pow_add]
          _ = 10369436997 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 35574847613) ^ 2120 = 12891681854 := by
        calc
          (2 : ZMod 35574847613) ^ 2120 = (2 : ZMod 35574847613) ^ (1060 + 1060) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 1060 * (2 : ZMod 35574847613) ^ 1060 := by rw [pow_add]
          _ = 12891681854 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 35574847613) ^ 4240 = 34008662556 := by
        calc
          (2 : ZMod 35574847613) ^ 4240 = (2 : ZMod 35574847613) ^ (2120 + 2120) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 2120 * (2 : ZMod 35574847613) ^ 2120 := by rw [pow_add]
          _ = 34008662556 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 35574847613) ^ 8481 = 27834779646 := by
        calc
          (2 : ZMod 35574847613) ^ 8481 = (2 : ZMod 35574847613) ^ (4240 + 4240 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 4240 * (2 : ZMod 35574847613) ^ 4240) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 27834779646 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 35574847613) ^ 16963 = 28965166479 := by
        calc
          (2 : ZMod 35574847613) ^ 16963 = (2 : ZMod 35574847613) ^ (8481 + 8481 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 8481 * (2 : ZMod 35574847613) ^ 8481) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 28965166479 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 35574847613) ^ 33926 = 17312880205 := by
        calc
          (2 : ZMod 35574847613) ^ 33926 = (2 : ZMod 35574847613) ^ (16963 + 16963) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 16963 * (2 : ZMod 35574847613) ^ 16963 := by rw [pow_add]
          _ = 17312880205 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 35574847613) ^ 67853 = 14480407331 := by
        calc
          (2 : ZMod 35574847613) ^ 67853 = (2 : ZMod 35574847613) ^ (33926 + 33926 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 33926 * (2 : ZMod 35574847613) ^ 33926) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 14480407331 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 35574847613) ^ 135707 = 23438909891 := by
        calc
          (2 : ZMod 35574847613) ^ 135707 = (2 : ZMod 35574847613) ^ (67853 + 67853 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 67853 * (2 : ZMod 35574847613) ^ 67853) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 23438909891 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 35574847613) ^ 271414 = 2969881734 := by
        calc
          (2 : ZMod 35574847613) ^ 271414 = (2 : ZMod 35574847613) ^ (135707 + 135707) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 135707 * (2 : ZMod 35574847613) ^ 135707 := by rw [pow_add]
          _ = 2969881734 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 35574847613) ^ 542829 = 3237060958 := by
        calc
          (2 : ZMod 35574847613) ^ 542829 = (2 : ZMod 35574847613) ^ (271414 + 271414 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 271414 * (2 : ZMod 35574847613) ^ 271414) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 3237060958 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 35574847613) ^ 1085658 = 1140659785 := by
        calc
          (2 : ZMod 35574847613) ^ 1085658 = (2 : ZMod 35574847613) ^ (542829 + 542829) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 542829 * (2 : ZMod 35574847613) ^ 542829 := by rw [pow_add]
          _ = 1140659785 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 35574847613) ^ 2171316 = 16026630187 := by
        calc
          (2 : ZMod 35574847613) ^ 2171316 = (2 : ZMod 35574847613) ^ (1085658 + 1085658) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 1085658 * (2 : ZMod 35574847613) ^ 1085658 := by rw [pow_add]
          _ = 16026630187 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 35574847613) ^ 4342632 = 15953047203 := by
        calc
          (2 : ZMod 35574847613) ^ 4342632 = (2 : ZMod 35574847613) ^ (2171316 + 2171316) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 2171316 * (2 : ZMod 35574847613) ^ 2171316 := by rw [pow_add]
          _ = 15953047203 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 35574847613) ^ 8685265 = 30223408448 := by
        calc
          (2 : ZMod 35574847613) ^ 8685265 = (2 : ZMod 35574847613) ^ (4342632 + 4342632 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 4342632 * (2 : ZMod 35574847613) ^ 4342632) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 30223408448 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 35574847613) ^ 17370531 = 32861511705 := by
        calc
          (2 : ZMod 35574847613) ^ 17370531 = (2 : ZMod 35574847613) ^ (8685265 + 8685265 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 8685265 * (2 : ZMod 35574847613) ^ 8685265) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 32861511705 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 35574847613) ^ 34741062 = 17483392462 := by
        calc
          (2 : ZMod 35574847613) ^ 34741062 = (2 : ZMod 35574847613) ^ (17370531 + 17370531) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 17370531 * (2 : ZMod 35574847613) ^ 17370531 := by rw [pow_add]
          _ = 17483392462 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 35574847613) ^ 69482124 = 33620717552 := by
        calc
          (2 : ZMod 35574847613) ^ 69482124 = (2 : ZMod 35574847613) ^ (34741062 + 34741062) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 34741062 * (2 : ZMod 35574847613) ^ 34741062 := by rw [pow_add]
          _ = 33620717552 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 35574847613) ^ 138964248 = 17160694763 := by
        calc
          (2 : ZMod 35574847613) ^ 138964248 = (2 : ZMod 35574847613) ^ (69482124 + 69482124) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 69482124 * (2 : ZMod 35574847613) ^ 69482124 := by rw [pow_add]
          _ = 17160694763 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 35574847613) ^ 277928496 = 28584124098 := by
        calc
          (2 : ZMod 35574847613) ^ 277928496 = (2 : ZMod 35574847613) ^ (138964248 + 138964248) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 138964248 * (2 : ZMod 35574847613) ^ 138964248 := by rw [pow_add]
          _ = 28584124098 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 35574847613) ^ 555856993 = 9837275979 := by
        calc
          (2 : ZMod 35574847613) ^ 555856993 = (2 : ZMod 35574847613) ^ (277928496 + 277928496 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 277928496 * (2 : ZMod 35574847613) ^ 277928496) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 9837275979 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 35574847613) ^ 1111713987 = 25577429690 := by
        calc
          (2 : ZMod 35574847613) ^ 1111713987 = (2 : ZMod 35574847613) ^ (555856993 + 555856993 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 555856993 * (2 : ZMod 35574847613) ^ 555856993) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 25577429690 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 35574847613) ^ 2223427975 = 29113350306 := by
        calc
          (2 : ZMod 35574847613) ^ 2223427975 = (2 : ZMod 35574847613) ^ (1111713987 + 1111713987 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 1111713987 * (2 : ZMod 35574847613) ^ 1111713987) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 29113350306 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 35574847613) ^ 4446855951 = 16201856251 := by
        calc
          (2 : ZMod 35574847613) ^ 4446855951 = (2 : ZMod 35574847613) ^ (2223427975 + 2223427975 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 2223427975 * (2 : ZMod 35574847613) ^ 2223427975) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 16201856251 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 35574847613) ^ 8893711903 = 3171135110 := by
        calc
          (2 : ZMod 35574847613) ^ 8893711903 = (2 : ZMod 35574847613) ^ (4446855951 + 4446855951 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 4446855951 * (2 : ZMod 35574847613) ^ 4446855951) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 3171135110 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 35574847613) ^ 17787423806 = 35574847612 := by
        calc
          (2 : ZMod 35574847613) ^ 17787423806 = (2 : ZMod 35574847613) ^ (8893711903 + 8893711903) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 8893711903 * (2 : ZMod 35574847613) ^ 8893711903 := by rw [pow_add]
          _ = 35574847612 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 35574847613) ^ 35574847612 = 1 := by
        calc
          (2 : ZMod 35574847613) ^ 35574847612 = (2 : ZMod 35574847613) ^ (17787423806 + 17787423806) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 17787423806 * (2 : ZMod 35574847613) ^ 17787423806 := by rw [pow_add]
          _ = 1 := by rw [fermat_34]; decide
      simpa using fermat_35
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (463, 1), (3929, 1), (4889, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (463, 1), (3929, 1), (4889, 1)] : List FactorBlock).map factorBlockValue).prod = 35574847613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 35574847613) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 35574847613) ^ 2 = 4 := by
        calc
          (2 : ZMod 35574847613) ^ 2 = (2 : ZMod 35574847613) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 1 * (2 : ZMod 35574847613) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 35574847613) ^ 4 = 16 := by
        calc
          (2 : ZMod 35574847613) ^ 4 = (2 : ZMod 35574847613) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 2 * (2 : ZMod 35574847613) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 35574847613) ^ 8 = 256 := by
        calc
          (2 : ZMod 35574847613) ^ 8 = (2 : ZMod 35574847613) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 4 * (2 : ZMod 35574847613) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 35574847613) ^ 16 = 65536 := by
        calc
          (2 : ZMod 35574847613) ^ 16 = (2 : ZMod 35574847613) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 8 * (2 : ZMod 35574847613) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 35574847613) ^ 33 = 8589934592 := by
        calc
          (2 : ZMod 35574847613) ^ 33 = (2 : ZMod 35574847613) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 16 * (2 : ZMod 35574847613) ^ 16) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 8589934592 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 35574847613) ^ 66 = 4840307886 := by
        calc
          (2 : ZMod 35574847613) ^ 66 = (2 : ZMod 35574847613) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 33 * (2 : ZMod 35574847613) ^ 33 := by rw [pow_add]
          _ = 4840307886 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 35574847613) ^ 132 = 32257435626 := by
        calc
          (2 : ZMod 35574847613) ^ 132 = (2 : ZMod 35574847613) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 66 * (2 : ZMod 35574847613) ^ 66 := by rw [pow_add]
          _ = 32257435626 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 35574847613) ^ 265 = 22871039301 := by
        calc
          (2 : ZMod 35574847613) ^ 265 = (2 : ZMod 35574847613) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 132 * (2 : ZMod 35574847613) ^ 132) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 22871039301 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 35574847613) ^ 530 = 5649492885 := by
        calc
          (2 : ZMod 35574847613) ^ 530 = (2 : ZMod 35574847613) ^ (265 + 265) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 265 * (2 : ZMod 35574847613) ^ 265 := by rw [pow_add]
          _ = 5649492885 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 35574847613) ^ 1060 = 10369436997 := by
        calc
          (2 : ZMod 35574847613) ^ 1060 = (2 : ZMod 35574847613) ^ (530 + 530) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 530 * (2 : ZMod 35574847613) ^ 530 := by rw [pow_add]
          _ = 10369436997 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 35574847613) ^ 2120 = 12891681854 := by
        calc
          (2 : ZMod 35574847613) ^ 2120 = (2 : ZMod 35574847613) ^ (1060 + 1060) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 1060 * (2 : ZMod 35574847613) ^ 1060 := by rw [pow_add]
          _ = 12891681854 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 35574847613) ^ 4240 = 34008662556 := by
        calc
          (2 : ZMod 35574847613) ^ 4240 = (2 : ZMod 35574847613) ^ (2120 + 2120) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 2120 * (2 : ZMod 35574847613) ^ 2120 := by rw [pow_add]
          _ = 34008662556 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 35574847613) ^ 8481 = 27834779646 := by
        calc
          (2 : ZMod 35574847613) ^ 8481 = (2 : ZMod 35574847613) ^ (4240 + 4240 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 4240 * (2 : ZMod 35574847613) ^ 4240) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 27834779646 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 35574847613) ^ 16963 = 28965166479 := by
        calc
          (2 : ZMod 35574847613) ^ 16963 = (2 : ZMod 35574847613) ^ (8481 + 8481 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 8481 * (2 : ZMod 35574847613) ^ 8481) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 28965166479 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 35574847613) ^ 33926 = 17312880205 := by
        calc
          (2 : ZMod 35574847613) ^ 33926 = (2 : ZMod 35574847613) ^ (16963 + 16963) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 16963 * (2 : ZMod 35574847613) ^ 16963 := by rw [pow_add]
          _ = 17312880205 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 35574847613) ^ 67853 = 14480407331 := by
        calc
          (2 : ZMod 35574847613) ^ 67853 = (2 : ZMod 35574847613) ^ (33926 + 33926 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 33926 * (2 : ZMod 35574847613) ^ 33926) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 14480407331 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 35574847613) ^ 135707 = 23438909891 := by
        calc
          (2 : ZMod 35574847613) ^ 135707 = (2 : ZMod 35574847613) ^ (67853 + 67853 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 67853 * (2 : ZMod 35574847613) ^ 67853) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 23438909891 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 35574847613) ^ 271414 = 2969881734 := by
        calc
          (2 : ZMod 35574847613) ^ 271414 = (2 : ZMod 35574847613) ^ (135707 + 135707) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 135707 * (2 : ZMod 35574847613) ^ 135707 := by rw [pow_add]
          _ = 2969881734 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 35574847613) ^ 542829 = 3237060958 := by
        calc
          (2 : ZMod 35574847613) ^ 542829 = (2 : ZMod 35574847613) ^ (271414 + 271414 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 271414 * (2 : ZMod 35574847613) ^ 271414) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 3237060958 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 35574847613) ^ 1085658 = 1140659785 := by
        calc
          (2 : ZMod 35574847613) ^ 1085658 = (2 : ZMod 35574847613) ^ (542829 + 542829) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 542829 * (2 : ZMod 35574847613) ^ 542829 := by rw [pow_add]
          _ = 1140659785 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 35574847613) ^ 2171316 = 16026630187 := by
        calc
          (2 : ZMod 35574847613) ^ 2171316 = (2 : ZMod 35574847613) ^ (1085658 + 1085658) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 1085658 * (2 : ZMod 35574847613) ^ 1085658 := by rw [pow_add]
          _ = 16026630187 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 35574847613) ^ 4342632 = 15953047203 := by
        calc
          (2 : ZMod 35574847613) ^ 4342632 = (2 : ZMod 35574847613) ^ (2171316 + 2171316) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 2171316 * (2 : ZMod 35574847613) ^ 2171316 := by rw [pow_add]
          _ = 15953047203 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 35574847613) ^ 8685265 = 30223408448 := by
        calc
          (2 : ZMod 35574847613) ^ 8685265 = (2 : ZMod 35574847613) ^ (4342632 + 4342632 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 4342632 * (2 : ZMod 35574847613) ^ 4342632) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 30223408448 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 35574847613) ^ 17370531 = 32861511705 := by
        calc
          (2 : ZMod 35574847613) ^ 17370531 = (2 : ZMod 35574847613) ^ (8685265 + 8685265 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 8685265 * (2 : ZMod 35574847613) ^ 8685265) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 32861511705 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 35574847613) ^ 34741062 = 17483392462 := by
        calc
          (2 : ZMod 35574847613) ^ 34741062 = (2 : ZMod 35574847613) ^ (17370531 + 17370531) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 17370531 * (2 : ZMod 35574847613) ^ 17370531 := by rw [pow_add]
          _ = 17483392462 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 35574847613) ^ 69482124 = 33620717552 := by
        calc
          (2 : ZMod 35574847613) ^ 69482124 = (2 : ZMod 35574847613) ^ (34741062 + 34741062) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 34741062 * (2 : ZMod 35574847613) ^ 34741062 := by rw [pow_add]
          _ = 33620717552 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 35574847613) ^ 138964248 = 17160694763 := by
        calc
          (2 : ZMod 35574847613) ^ 138964248 = (2 : ZMod 35574847613) ^ (69482124 + 69482124) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 69482124 * (2 : ZMod 35574847613) ^ 69482124 := by rw [pow_add]
          _ = 17160694763 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 35574847613) ^ 277928496 = 28584124098 := by
        calc
          (2 : ZMod 35574847613) ^ 277928496 = (2 : ZMod 35574847613) ^ (138964248 + 138964248) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 138964248 * (2 : ZMod 35574847613) ^ 138964248 := by rw [pow_add]
          _ = 28584124098 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 35574847613) ^ 555856993 = 9837275979 := by
        calc
          (2 : ZMod 35574847613) ^ 555856993 = (2 : ZMod 35574847613) ^ (277928496 + 277928496 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 277928496 * (2 : ZMod 35574847613) ^ 277928496) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 9837275979 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 35574847613) ^ 1111713987 = 25577429690 := by
        calc
          (2 : ZMod 35574847613) ^ 1111713987 = (2 : ZMod 35574847613) ^ (555856993 + 555856993 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 555856993 * (2 : ZMod 35574847613) ^ 555856993) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 25577429690 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 35574847613) ^ 2223427975 = 29113350306 := by
        calc
          (2 : ZMod 35574847613) ^ 2223427975 = (2 : ZMod 35574847613) ^ (1111713987 + 1111713987 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 1111713987 * (2 : ZMod 35574847613) ^ 1111713987) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 29113350306 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 35574847613) ^ 4446855951 = 16201856251 := by
        calc
          (2 : ZMod 35574847613) ^ 4446855951 = (2 : ZMod 35574847613) ^ (2223427975 + 2223427975 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 2223427975 * (2 : ZMod 35574847613) ^ 2223427975) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 16201856251 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 35574847613) ^ 8893711903 = 3171135110 := by
        calc
          (2 : ZMod 35574847613) ^ 8893711903 = (2 : ZMod 35574847613) ^ (4446855951 + 4446855951 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 4446855951 * (2 : ZMod 35574847613) ^ 4446855951) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 3171135110 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 35574847613) ^ 17787423806 = 35574847612 := by
        calc
          (2 : ZMod 35574847613) ^ 17787423806 = (2 : ZMod 35574847613) ^ (8893711903 + 8893711903) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 8893711903 * (2 : ZMod 35574847613) ^ 8893711903 := by rw [pow_add]
          _ = 35574847612 := by rw [factor_0_33]; decide
      change (2 : ZMod 35574847613) ^ 17787423806 ≠ 1
      rw [factor_0_34]
      decide
    ·
      have factor_1_0 : (2 : ZMod 35574847613) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 35574847613) ^ 2 = 4 := by
        calc
          (2 : ZMod 35574847613) ^ 2 = (2 : ZMod 35574847613) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 1 * (2 : ZMod 35574847613) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 35574847613) ^ 4 = 16 := by
        calc
          (2 : ZMod 35574847613) ^ 4 = (2 : ZMod 35574847613) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 2 * (2 : ZMod 35574847613) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 35574847613) ^ 9 = 512 := by
        calc
          (2 : ZMod 35574847613) ^ 9 = (2 : ZMod 35574847613) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 4 * (2 : ZMod 35574847613) ^ 4) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 35574847613) ^ 18 = 262144 := by
        calc
          (2 : ZMod 35574847613) ^ 18 = (2 : ZMod 35574847613) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 9 * (2 : ZMod 35574847613) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 35574847613) ^ 36 = 33144629123 := by
        calc
          (2 : ZMod 35574847613) ^ 36 = (2 : ZMod 35574847613) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 18 * (2 : ZMod 35574847613) ^ 18 := by rw [pow_add]
          _ = 33144629123 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 35574847613) ^ 73 = 14786999987 := by
        calc
          (2 : ZMod 35574847613) ^ 73 = (2 : ZMod 35574847613) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 36 * (2 : ZMod 35574847613) ^ 36) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 14786999987 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 35574847613) ^ 146 = 5889157656 := by
        calc
          (2 : ZMod 35574847613) ^ 146 = (2 : ZMod 35574847613) ^ (73 + 73) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 73 * (2 : ZMod 35574847613) ^ 73 := by rw [pow_add]
          _ = 5889157656 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 35574847613) ^ 293 = 19987878618 := by
        calc
          (2 : ZMod 35574847613) ^ 293 = (2 : ZMod 35574847613) ^ (146 + 146 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 146 * (2 : ZMod 35574847613) ^ 146) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 19987878618 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 35574847613) ^ 586 = 2713943135 := by
        calc
          (2 : ZMod 35574847613) ^ 586 = (2 : ZMod 35574847613) ^ (293 + 293) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 293 * (2 : ZMod 35574847613) ^ 293 := by rw [pow_add]
          _ = 2713943135 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 35574847613) ^ 1172 = 25121663129 := by
        calc
          (2 : ZMod 35574847613) ^ 1172 = (2 : ZMod 35574847613) ^ (586 + 586) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 586 * (2 : ZMod 35574847613) ^ 586 := by rw [pow_add]
          _ = 25121663129 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 35574847613) ^ 2344 = 24655669556 := by
        calc
          (2 : ZMod 35574847613) ^ 2344 = (2 : ZMod 35574847613) ^ (1172 + 1172) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 1172 * (2 : ZMod 35574847613) ^ 1172 := by rw [pow_add]
          _ = 24655669556 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 35574847613) ^ 4689 = 2962949660 := by
        calc
          (2 : ZMod 35574847613) ^ 4689 = (2 : ZMod 35574847613) ^ (2344 + 2344 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 2344 * (2 : ZMod 35574847613) ^ 2344) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 2962949660 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 35574847613) ^ 9379 = 23143044336 := by
        calc
          (2 : ZMod 35574847613) ^ 9379 = (2 : ZMod 35574847613) ^ (4689 + 4689 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 4689 * (2 : ZMod 35574847613) ^ 4689) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 23143044336 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 35574847613) ^ 18758 = 17130965500 := by
        calc
          (2 : ZMod 35574847613) ^ 18758 = (2 : ZMod 35574847613) ^ (9379 + 9379) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 9379 * (2 : ZMod 35574847613) ^ 9379 := by rw [pow_add]
          _ = 17130965500 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 35574847613) ^ 37517 = 34851531134 := by
        calc
          (2 : ZMod 35574847613) ^ 37517 = (2 : ZMod 35574847613) ^ (18758 + 18758 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 18758 * (2 : ZMod 35574847613) ^ 18758) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 34851531134 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 35574847613) ^ 75034 = 2869773830 := by
        calc
          (2 : ZMod 35574847613) ^ 75034 = (2 : ZMod 35574847613) ^ (37517 + 37517) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 37517 * (2 : ZMod 35574847613) ^ 37517 := by rw [pow_add]
          _ = 2869773830 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 35574847613) ^ 150069 = 25872489021 := by
        calc
          (2 : ZMod 35574847613) ^ 150069 = (2 : ZMod 35574847613) ^ (75034 + 75034 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 75034 * (2 : ZMod 35574847613) ^ 75034) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 25872489021 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 35574847613) ^ 300138 = 17707119314 := by
        calc
          (2 : ZMod 35574847613) ^ 300138 = (2 : ZMod 35574847613) ^ (150069 + 150069) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 150069 * (2 : ZMod 35574847613) ^ 150069 := by rw [pow_add]
          _ = 17707119314 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 35574847613) ^ 600277 = 15391543382 := by
        calc
          (2 : ZMod 35574847613) ^ 600277 = (2 : ZMod 35574847613) ^ (300138 + 300138 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 300138 * (2 : ZMod 35574847613) ^ 300138) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 15391543382 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 35574847613) ^ 1200555 = 30544511023 := by
        calc
          (2 : ZMod 35574847613) ^ 1200555 = (2 : ZMod 35574847613) ^ (600277 + 600277 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 600277 * (2 : ZMod 35574847613) ^ 600277) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 30544511023 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 35574847613) ^ 2401110 = 19600072509 := by
        calc
          (2 : ZMod 35574847613) ^ 2401110 = (2 : ZMod 35574847613) ^ (1200555 + 1200555) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 1200555 * (2 : ZMod 35574847613) ^ 1200555 := by rw [pow_add]
          _ = 19600072509 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 35574847613) ^ 4802220 = 729751532 := by
        calc
          (2 : ZMod 35574847613) ^ 4802220 = (2 : ZMod 35574847613) ^ (2401110 + 2401110) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 2401110 * (2 : ZMod 35574847613) ^ 2401110 := by rw [pow_add]
          _ = 729751532 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 35574847613) ^ 9604440 = 8436867267 := by
        calc
          (2 : ZMod 35574847613) ^ 9604440 = (2 : ZMod 35574847613) ^ (4802220 + 4802220) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 4802220 * (2 : ZMod 35574847613) ^ 4802220 := by rw [pow_add]
          _ = 8436867267 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 35574847613) ^ 19208881 = 32974440444 := by
        calc
          (2 : ZMod 35574847613) ^ 19208881 = (2 : ZMod 35574847613) ^ (9604440 + 9604440 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 9604440 * (2 : ZMod 35574847613) ^ 9604440) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 32974440444 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 35574847613) ^ 38417762 = 748486940 := by
        calc
          (2 : ZMod 35574847613) ^ 38417762 = (2 : ZMod 35574847613) ^ (19208881 + 19208881) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 19208881 * (2 : ZMod 35574847613) ^ 19208881 := by rw [pow_add]
          _ = 748486940 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 35574847613) ^ 76835524 = 34715887213 := by
        calc
          (2 : ZMod 35574847613) ^ 76835524 = (2 : ZMod 35574847613) ^ (38417762 + 38417762) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 38417762 * (2 : ZMod 35574847613) ^ 38417762 := by rw [pow_add]
          _ = 34715887213 := by rw [factor_1_25]; decide
      change (2 : ZMod 35574847613) ^ 76835524 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (2 : ZMod 35574847613) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 35574847613) ^ 2 = 4 := by
        calc
          (2 : ZMod 35574847613) ^ 2 = (2 : ZMod 35574847613) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 1 * (2 : ZMod 35574847613) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 35574847613) ^ 4 = 16 := by
        calc
          (2 : ZMod 35574847613) ^ 4 = (2 : ZMod 35574847613) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 2 * (2 : ZMod 35574847613) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 35574847613) ^ 8 = 256 := by
        calc
          (2 : ZMod 35574847613) ^ 8 = (2 : ZMod 35574847613) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 4 * (2 : ZMod 35574847613) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 35574847613) ^ 17 = 131072 := by
        calc
          (2 : ZMod 35574847613) ^ 17 = (2 : ZMod 35574847613) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 8 * (2 : ZMod 35574847613) ^ 8) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 35574847613) ^ 34 = 17179869184 := by
        calc
          (2 : ZMod 35574847613) ^ 34 = (2 : ZMod 35574847613) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 17 * (2 : ZMod 35574847613) ^ 17 := by rw [pow_add]
          _ = 17179869184 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 35574847613) ^ 69 = 3147615475 := by
        calc
          (2 : ZMod 35574847613) ^ 69 = (2 : ZMod 35574847613) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 34 * (2 : ZMod 35574847613) ^ 34) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 3147615475 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 35574847613) ^ 138 = 1134718510 := by
        calc
          (2 : ZMod 35574847613) ^ 138 = (2 : ZMod 35574847613) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 69 * (2 : ZMod 35574847613) ^ 69 := by rw [pow_add]
          _ = 1134718510 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 35574847613) ^ 276 = 23389029740 := by
        calc
          (2 : ZMod 35574847613) ^ 276 = (2 : ZMod 35574847613) ^ (138 + 138) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 138 * (2 : ZMod 35574847613) ^ 138 := by rw [pow_add]
          _ = 23389029740 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 35574847613) ^ 552 = 31682307613 := by
        calc
          (2 : ZMod 35574847613) ^ 552 = (2 : ZMod 35574847613) ^ (276 + 276) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 276 * (2 : ZMod 35574847613) ^ 276 := by rw [pow_add]
          _ = 31682307613 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 35574847613) ^ 1105 = 18498221707 := by
        calc
          (2 : ZMod 35574847613) ^ 1105 = (2 : ZMod 35574847613) ^ (552 + 552 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 552 * (2 : ZMod 35574847613) ^ 552) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 18498221707 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 35574847613) ^ 2210 = 16410146127 := by
        calc
          (2 : ZMod 35574847613) ^ 2210 = (2 : ZMod 35574847613) ^ (1105 + 1105) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 1105 * (2 : ZMod 35574847613) ^ 1105 := by rw [pow_add]
          _ = 16410146127 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 35574847613) ^ 4421 = 3552775465 := by
        calc
          (2 : ZMod 35574847613) ^ 4421 = (2 : ZMod 35574847613) ^ (2210 + 2210 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 2210 * (2 : ZMod 35574847613) ^ 2210) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 3552775465 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 35574847613) ^ 8842 = 9716848105 := by
        calc
          (2 : ZMod 35574847613) ^ 8842 = (2 : ZMod 35574847613) ^ (4421 + 4421) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 4421 * (2 : ZMod 35574847613) ^ 4421 := by rw [pow_add]
          _ = 9716848105 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 35574847613) ^ 17684 = 19679068387 := by
        calc
          (2 : ZMod 35574847613) ^ 17684 = (2 : ZMod 35574847613) ^ (8842 + 8842) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 8842 * (2 : ZMod 35574847613) ^ 8842 := by rw [pow_add]
          _ = 19679068387 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 35574847613) ^ 35368 = 3661908014 := by
        calc
          (2 : ZMod 35574847613) ^ 35368 = (2 : ZMod 35574847613) ^ (17684 + 17684) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 17684 * (2 : ZMod 35574847613) ^ 17684 := by rw [pow_add]
          _ = 3661908014 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 35574847613) ^ 70737 = 30246994526 := by
        calc
          (2 : ZMod 35574847613) ^ 70737 = (2 : ZMod 35574847613) ^ (35368 + 35368 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 35368 * (2 : ZMod 35574847613) ^ 35368) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 30246994526 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 35574847613) ^ 141475 = 35421852075 := by
        calc
          (2 : ZMod 35574847613) ^ 141475 = (2 : ZMod 35574847613) ^ (70737 + 70737 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 70737 * (2 : ZMod 35574847613) ^ 70737) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 35421852075 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 35574847613) ^ 282950 = 25265812478 := by
        calc
          (2 : ZMod 35574847613) ^ 282950 = (2 : ZMod 35574847613) ^ (141475 + 141475) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 141475 * (2 : ZMod 35574847613) ^ 141475 := by rw [pow_add]
          _ = 25265812478 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 35574847613) ^ 565901 = 168275802 := by
        calc
          (2 : ZMod 35574847613) ^ 565901 = (2 : ZMod 35574847613) ^ (282950 + 282950 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 282950 * (2 : ZMod 35574847613) ^ 282950) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 168275802 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 35574847613) ^ 1131803 = 5695428219 := by
        calc
          (2 : ZMod 35574847613) ^ 1131803 = (2 : ZMod 35574847613) ^ (565901 + 565901 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 565901 * (2 : ZMod 35574847613) ^ 565901) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 5695428219 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 35574847613) ^ 2263607 = 19077547806 := by
        calc
          (2 : ZMod 35574847613) ^ 2263607 = (2 : ZMod 35574847613) ^ (1131803 + 1131803 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 1131803 * (2 : ZMod 35574847613) ^ 1131803) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 19077547806 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 35574847613) ^ 4527214 = 21034958185 := by
        calc
          (2 : ZMod 35574847613) ^ 4527214 = (2 : ZMod 35574847613) ^ (2263607 + 2263607) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 2263607 * (2 : ZMod 35574847613) ^ 2263607 := by rw [pow_add]
          _ = 21034958185 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 35574847613) ^ 9054428 = 15550168306 := by
        calc
          (2 : ZMod 35574847613) ^ 9054428 = (2 : ZMod 35574847613) ^ (4527214 + 4527214) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 4527214 * (2 : ZMod 35574847613) ^ 4527214 := by rw [pow_add]
          _ = 15550168306 := by rw [factor_2_22]; decide
      change (2 : ZMod 35574847613) ^ 9054428 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (2 : ZMod 35574847613) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 35574847613) ^ 3 = 8 := by
        calc
          (2 : ZMod 35574847613) ^ 3 = (2 : ZMod 35574847613) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 1 * (2 : ZMod 35574847613) ^ 1) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 35574847613) ^ 6 = 64 := by
        calc
          (2 : ZMod 35574847613) ^ 6 = (2 : ZMod 35574847613) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 3 * (2 : ZMod 35574847613) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 35574847613) ^ 13 = 8192 := by
        calc
          (2 : ZMod 35574847613) ^ 13 = (2 : ZMod 35574847613) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 6 * (2 : ZMod 35574847613) ^ 6) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 35574847613) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 35574847613) ^ 27 = (2 : ZMod 35574847613) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 13 * (2 : ZMod 35574847613) ^ 13) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 35574847613) ^ 55 = 14350422088 := by
        calc
          (2 : ZMod 35574847613) ^ 55 = (2 : ZMod 35574847613) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 27 * (2 : ZMod 35574847613) ^ 27) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 14350422088 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 35574847613) ^ 111 = 1434407340 := by
        calc
          (2 : ZMod 35574847613) ^ 111 = (2 : ZMod 35574847613) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 55 * (2 : ZMod 35574847613) ^ 55) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 1434407340 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 35574847613) ^ 222 = 27675382004 := by
        calc
          (2 : ZMod 35574847613) ^ 222 = (2 : ZMod 35574847613) ^ (111 + 111) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 111 * (2 : ZMod 35574847613) ^ 111 := by rw [pow_add]
          _ = 27675382004 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 35574847613) ^ 444 = 27896830813 := by
        calc
          (2 : ZMod 35574847613) ^ 444 = (2 : ZMod 35574847613) ^ (222 + 222) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 222 * (2 : ZMod 35574847613) ^ 222 := by rw [pow_add]
          _ = 27896830813 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 35574847613) ^ 888 = 23022277010 := by
        calc
          (2 : ZMod 35574847613) ^ 888 = (2 : ZMod 35574847613) ^ (444 + 444) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 444 * (2 : ZMod 35574847613) ^ 444 := by rw [pow_add]
          _ = 23022277010 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 35574847613) ^ 1776 = 9346894177 := by
        calc
          (2 : ZMod 35574847613) ^ 1776 = (2 : ZMod 35574847613) ^ (888 + 888) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 888 * (2 : ZMod 35574847613) ^ 888 := by rw [pow_add]
          _ = 9346894177 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 35574847613) ^ 3552 = 33231516865 := by
        calc
          (2 : ZMod 35574847613) ^ 3552 = (2 : ZMod 35574847613) ^ (1776 + 1776) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 1776 * (2 : ZMod 35574847613) ^ 1776 := by rw [pow_add]
          _ = 33231516865 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 35574847613) ^ 7105 = 15381920901 := by
        calc
          (2 : ZMod 35574847613) ^ 7105 = (2 : ZMod 35574847613) ^ (3552 + 3552 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 3552 * (2 : ZMod 35574847613) ^ 3552) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 15381920901 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 35574847613) ^ 14211 = 5339312153 := by
        calc
          (2 : ZMod 35574847613) ^ 14211 = (2 : ZMod 35574847613) ^ (7105 + 7105 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 7105 * (2 : ZMod 35574847613) ^ 7105) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 5339312153 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 35574847613) ^ 28423 = 9691476526 := by
        calc
          (2 : ZMod 35574847613) ^ 28423 = (2 : ZMod 35574847613) ^ (14211 + 14211 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 14211 * (2 : ZMod 35574847613) ^ 14211) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 9691476526 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 35574847613) ^ 56847 = 29597020811 := by
        calc
          (2 : ZMod 35574847613) ^ 56847 = (2 : ZMod 35574847613) ^ (28423 + 28423 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 28423 * (2 : ZMod 35574847613) ^ 28423) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 29597020811 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 35574847613) ^ 113695 = 2362307695 := by
        calc
          (2 : ZMod 35574847613) ^ 113695 = (2 : ZMod 35574847613) ^ (56847 + 56847 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 56847 * (2 : ZMod 35574847613) ^ 56847) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 2362307695 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 35574847613) ^ 227390 = 10603566859 := by
        calc
          (2 : ZMod 35574847613) ^ 227390 = (2 : ZMod 35574847613) ^ (113695 + 113695) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 113695 * (2 : ZMod 35574847613) ^ 113695 := by rw [pow_add]
          _ = 10603566859 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 35574847613) ^ 454781 = 28538159138 := by
        calc
          (2 : ZMod 35574847613) ^ 454781 = (2 : ZMod 35574847613) ^ (227390 + 227390 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 227390 * (2 : ZMod 35574847613) ^ 227390) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 28538159138 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 35574847613) ^ 909563 = 23802253623 := by
        calc
          (2 : ZMod 35574847613) ^ 909563 = (2 : ZMod 35574847613) ^ (454781 + 454781 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 454781 * (2 : ZMod 35574847613) ^ 454781) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 23802253623 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 35574847613) ^ 1819127 = 2378971256 := by
        calc
          (2 : ZMod 35574847613) ^ 1819127 = (2 : ZMod 35574847613) ^ (909563 + 909563 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = ((2 : ZMod 35574847613) ^ 909563 * (2 : ZMod 35574847613) ^ 909563) * (2 : ZMod 35574847613) := by rw [pow_succ, pow_add]
          _ = 2378971256 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 35574847613) ^ 3638254 = 23426002255 := by
        calc
          (2 : ZMod 35574847613) ^ 3638254 = (2 : ZMod 35574847613) ^ (1819127 + 1819127) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 1819127 * (2 : ZMod 35574847613) ^ 1819127 := by rw [pow_add]
          _ = 23426002255 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 35574847613) ^ 7276508 = 18251501073 := by
        calc
          (2 : ZMod 35574847613) ^ 7276508 = (2 : ZMod 35574847613) ^ (3638254 + 3638254) :=
            congrArg (fun n : ℕ => (2 : ZMod 35574847613) ^ n) (by norm_num)
          _ = (2 : ZMod 35574847613) ^ 3638254 * (2 : ZMod 35574847613) ^ 3638254 := by rw [pow_add]
          _ = 18251501073 := by rw [factor_3_21]; decide
      change (2 : ZMod 35574847613) ^ 7276508 ≠ 1
      rw [factor_3_22]
      decide

#print axioms prime_lucas_35574847613

end TotientTailPeriodKiller
end Erdos249257
