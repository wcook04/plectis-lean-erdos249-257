import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_3930112903 : Nat.Prime 3930112903 := by
  apply lucas_primality 3930112903 (3 : ZMod 3930112903)
  ·
      have fermat_0 : (3 : ZMod 3930112903) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 3930112903) ^ 3 = 27 := by
        calc
          (3 : ZMod 3930112903) ^ 3 = (3 : ZMod 3930112903) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 1 * (3 : ZMod 3930112903) ^ 1) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 3930112903) ^ 7 = 2187 := by
        calc
          (3 : ZMod 3930112903) ^ 7 = (3 : ZMod 3930112903) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 3 * (3 : ZMod 3930112903) ^ 3) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 3930112903) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 3930112903) ^ 14 = (3 : ZMod 3930112903) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 7 * (3 : ZMod 3930112903) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 3930112903) ^ 29 = 2745852697 := by
        calc
          (3 : ZMod 3930112903) ^ 29 = (3 : ZMod 3930112903) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 14 * (3 : ZMod 3930112903) ^ 14) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 2745852697 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 3930112903) ^ 58 = 1590838900 := by
        calc
          (3 : ZMod 3930112903) ^ 58 = (3 : ZMod 3930112903) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 29 * (3 : ZMod 3930112903) ^ 29 := by rw [pow_add]
          _ = 1590838900 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 3930112903) ^ 117 = 2594881660 := by
        calc
          (3 : ZMod 3930112903) ^ 117 = (3 : ZMod 3930112903) ^ (58 + 58 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 58 * (3 : ZMod 3930112903) ^ 58) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 2594881660 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 3930112903) ^ 234 = 2937097796 := by
        calc
          (3 : ZMod 3930112903) ^ 234 = (3 : ZMod 3930112903) ^ (117 + 117) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 117 * (3 : ZMod 3930112903) ^ 117 := by rw [pow_add]
          _ = 2937097796 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 3930112903) ^ 468 = 2504731912 := by
        calc
          (3 : ZMod 3930112903) ^ 468 = (3 : ZMod 3930112903) ^ (234 + 234) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 234 * (3 : ZMod 3930112903) ^ 234 := by rw [pow_add]
          _ = 2504731912 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 3930112903) ^ 937 = 2954834596 := by
        calc
          (3 : ZMod 3930112903) ^ 937 = (3 : ZMod 3930112903) ^ (468 + 468 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 468 * (3 : ZMod 3930112903) ^ 468) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 2954834596 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 3930112903) ^ 1874 = 237548936 := by
        calc
          (3 : ZMod 3930112903) ^ 1874 = (3 : ZMod 3930112903) ^ (937 + 937) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 937 * (3 : ZMod 3930112903) ^ 937 := by rw [pow_add]
          _ = 237548936 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 3930112903) ^ 3748 = 566587182 := by
        calc
          (3 : ZMod 3930112903) ^ 3748 = (3 : ZMod 3930112903) ^ (1874 + 1874) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 1874 * (3 : ZMod 3930112903) ^ 1874 := by rw [pow_add]
          _ = 566587182 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 3930112903) ^ 7496 = 269258439 := by
        calc
          (3 : ZMod 3930112903) ^ 7496 = (3 : ZMod 3930112903) ^ (3748 + 3748) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 3748 * (3 : ZMod 3930112903) ^ 3748 := by rw [pow_add]
          _ = 269258439 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 3930112903) ^ 14992 = 1593366119 := by
        calc
          (3 : ZMod 3930112903) ^ 14992 = (3 : ZMod 3930112903) ^ (7496 + 7496) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 7496 * (3 : ZMod 3930112903) ^ 7496 := by rw [pow_add]
          _ = 1593366119 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 3930112903) ^ 29984 = 1702039370 := by
        calc
          (3 : ZMod 3930112903) ^ 29984 = (3 : ZMod 3930112903) ^ (14992 + 14992) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 14992 * (3 : ZMod 3930112903) ^ 14992 := by rw [pow_add]
          _ = 1702039370 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 3930112903) ^ 59968 = 1270748263 := by
        calc
          (3 : ZMod 3930112903) ^ 59968 = (3 : ZMod 3930112903) ^ (29984 + 29984) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 29984 * (3 : ZMod 3930112903) ^ 29984 := by rw [pow_add]
          _ = 1270748263 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 3930112903) ^ 119937 = 712501847 := by
        calc
          (3 : ZMod 3930112903) ^ 119937 = (3 : ZMod 3930112903) ^ (59968 + 59968 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 59968 * (3 : ZMod 3930112903) ^ 59968) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 712501847 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 3930112903) ^ 239875 = 1529560134 := by
        calc
          (3 : ZMod 3930112903) ^ 239875 = (3 : ZMod 3930112903) ^ (119937 + 119937 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 119937 * (3 : ZMod 3930112903) ^ 119937) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 1529560134 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 3930112903) ^ 479750 = 1343018123 := by
        calc
          (3 : ZMod 3930112903) ^ 479750 = (3 : ZMod 3930112903) ^ (239875 + 239875) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 239875 * (3 : ZMod 3930112903) ^ 239875 := by rw [pow_add]
          _ = 1343018123 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 3930112903) ^ 959500 = 2358639928 := by
        calc
          (3 : ZMod 3930112903) ^ 959500 = (3 : ZMod 3930112903) ^ (479750 + 479750) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 479750 * (3 : ZMod 3930112903) ^ 479750 := by rw [pow_add]
          _ = 2358639928 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 3930112903) ^ 1919000 = 3241335231 := by
        calc
          (3 : ZMod 3930112903) ^ 1919000 = (3 : ZMod 3930112903) ^ (959500 + 959500) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 959500 * (3 : ZMod 3930112903) ^ 959500 := by rw [pow_add]
          _ = 3241335231 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 3930112903) ^ 3838000 = 135706976 := by
        calc
          (3 : ZMod 3930112903) ^ 3838000 = (3 : ZMod 3930112903) ^ (1919000 + 1919000) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 1919000 * (3 : ZMod 3930112903) ^ 1919000 := by rw [pow_add]
          _ = 135706976 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 3930112903) ^ 7676001 = 105658416 := by
        calc
          (3 : ZMod 3930112903) ^ 7676001 = (3 : ZMod 3930112903) ^ (3838000 + 3838000 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 3838000 * (3 : ZMod 3930112903) ^ 3838000) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 105658416 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 3930112903) ^ 15352003 = 973456576 := by
        calc
          (3 : ZMod 3930112903) ^ 15352003 = (3 : ZMod 3930112903) ^ (7676001 + 7676001 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 7676001 * (3 : ZMod 3930112903) ^ 7676001) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 973456576 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 3930112903) ^ 30704007 = 1427059089 := by
        calc
          (3 : ZMod 3930112903) ^ 30704007 = (3 : ZMod 3930112903) ^ (15352003 + 15352003 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 15352003 * (3 : ZMod 3930112903) ^ 15352003) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 1427059089 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 3930112903) ^ 61408014 = 518292027 := by
        calc
          (3 : ZMod 3930112903) ^ 61408014 = (3 : ZMod 3930112903) ^ (30704007 + 30704007) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 30704007 * (3 : ZMod 3930112903) ^ 30704007 := by rw [pow_add]
          _ = 518292027 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 3930112903) ^ 122816028 = 923831828 := by
        calc
          (3 : ZMod 3930112903) ^ 122816028 = (3 : ZMod 3930112903) ^ (61408014 + 61408014) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 61408014 * (3 : ZMod 3930112903) ^ 61408014 := by rw [pow_add]
          _ = 923831828 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 3930112903) ^ 245632056 = 2655019114 := by
        calc
          (3 : ZMod 3930112903) ^ 245632056 = (3 : ZMod 3930112903) ^ (122816028 + 122816028) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 122816028 * (3 : ZMod 3930112903) ^ 122816028 := by rw [pow_add]
          _ = 2655019114 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 3930112903) ^ 491264112 = 221452588 := by
        calc
          (3 : ZMod 3930112903) ^ 491264112 = (3 : ZMod 3930112903) ^ (245632056 + 245632056) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 245632056 * (3 : ZMod 3930112903) ^ 245632056 := by rw [pow_add]
          _ = 221452588 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 3930112903) ^ 982528225 = 1112791456 := by
        calc
          (3 : ZMod 3930112903) ^ 982528225 = (3 : ZMod 3930112903) ^ (491264112 + 491264112 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 491264112 * (3 : ZMod 3930112903) ^ 491264112) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 1112791456 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 3930112903) ^ 1965056451 = 3930112902 := by
        calc
          (3 : ZMod 3930112903) ^ 1965056451 = (3 : ZMod 3930112903) ^ (982528225 + 982528225 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 982528225 * (3 : ZMod 3930112903) ^ 982528225) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 3930112902 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 3930112903) ^ 3930112902 = 1 := by
        calc
          (3 : ZMod 3930112903) ^ 3930112902 = (3 : ZMod 3930112903) ^ (1965056451 + 1965056451) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 1965056451 * (3 : ZMod 3930112903) ^ 1965056451 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (23, 1), (179, 1), (389, 1), (409, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (23, 1), (179, 1), (389, 1), (409, 1)] : List FactorBlock).map factorBlockValue).prod = 3930112903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 3930112903) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 3930112903) ^ 3 = 27 := by
        calc
          (3 : ZMod 3930112903) ^ 3 = (3 : ZMod 3930112903) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 1 * (3 : ZMod 3930112903) ^ 1) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 3930112903) ^ 7 = 2187 := by
        calc
          (3 : ZMod 3930112903) ^ 7 = (3 : ZMod 3930112903) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 3 * (3 : ZMod 3930112903) ^ 3) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 3930112903) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 3930112903) ^ 14 = (3 : ZMod 3930112903) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 7 * (3 : ZMod 3930112903) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 3930112903) ^ 29 = 2745852697 := by
        calc
          (3 : ZMod 3930112903) ^ 29 = (3 : ZMod 3930112903) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 14 * (3 : ZMod 3930112903) ^ 14) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 2745852697 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 3930112903) ^ 58 = 1590838900 := by
        calc
          (3 : ZMod 3930112903) ^ 58 = (3 : ZMod 3930112903) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 29 * (3 : ZMod 3930112903) ^ 29 := by rw [pow_add]
          _ = 1590838900 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 3930112903) ^ 117 = 2594881660 := by
        calc
          (3 : ZMod 3930112903) ^ 117 = (3 : ZMod 3930112903) ^ (58 + 58 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 58 * (3 : ZMod 3930112903) ^ 58) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 2594881660 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 3930112903) ^ 234 = 2937097796 := by
        calc
          (3 : ZMod 3930112903) ^ 234 = (3 : ZMod 3930112903) ^ (117 + 117) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 117 * (3 : ZMod 3930112903) ^ 117 := by rw [pow_add]
          _ = 2937097796 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 3930112903) ^ 468 = 2504731912 := by
        calc
          (3 : ZMod 3930112903) ^ 468 = (3 : ZMod 3930112903) ^ (234 + 234) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 234 * (3 : ZMod 3930112903) ^ 234 := by rw [pow_add]
          _ = 2504731912 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 3930112903) ^ 937 = 2954834596 := by
        calc
          (3 : ZMod 3930112903) ^ 937 = (3 : ZMod 3930112903) ^ (468 + 468 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 468 * (3 : ZMod 3930112903) ^ 468) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 2954834596 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 3930112903) ^ 1874 = 237548936 := by
        calc
          (3 : ZMod 3930112903) ^ 1874 = (3 : ZMod 3930112903) ^ (937 + 937) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 937 * (3 : ZMod 3930112903) ^ 937 := by rw [pow_add]
          _ = 237548936 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 3930112903) ^ 3748 = 566587182 := by
        calc
          (3 : ZMod 3930112903) ^ 3748 = (3 : ZMod 3930112903) ^ (1874 + 1874) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 1874 * (3 : ZMod 3930112903) ^ 1874 := by rw [pow_add]
          _ = 566587182 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 3930112903) ^ 7496 = 269258439 := by
        calc
          (3 : ZMod 3930112903) ^ 7496 = (3 : ZMod 3930112903) ^ (3748 + 3748) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 3748 * (3 : ZMod 3930112903) ^ 3748 := by rw [pow_add]
          _ = 269258439 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 3930112903) ^ 14992 = 1593366119 := by
        calc
          (3 : ZMod 3930112903) ^ 14992 = (3 : ZMod 3930112903) ^ (7496 + 7496) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 7496 * (3 : ZMod 3930112903) ^ 7496 := by rw [pow_add]
          _ = 1593366119 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 3930112903) ^ 29984 = 1702039370 := by
        calc
          (3 : ZMod 3930112903) ^ 29984 = (3 : ZMod 3930112903) ^ (14992 + 14992) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 14992 * (3 : ZMod 3930112903) ^ 14992 := by rw [pow_add]
          _ = 1702039370 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 3930112903) ^ 59968 = 1270748263 := by
        calc
          (3 : ZMod 3930112903) ^ 59968 = (3 : ZMod 3930112903) ^ (29984 + 29984) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 29984 * (3 : ZMod 3930112903) ^ 29984 := by rw [pow_add]
          _ = 1270748263 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 3930112903) ^ 119937 = 712501847 := by
        calc
          (3 : ZMod 3930112903) ^ 119937 = (3 : ZMod 3930112903) ^ (59968 + 59968 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 59968 * (3 : ZMod 3930112903) ^ 59968) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 712501847 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 3930112903) ^ 239875 = 1529560134 := by
        calc
          (3 : ZMod 3930112903) ^ 239875 = (3 : ZMod 3930112903) ^ (119937 + 119937 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 119937 * (3 : ZMod 3930112903) ^ 119937) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 1529560134 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 3930112903) ^ 479750 = 1343018123 := by
        calc
          (3 : ZMod 3930112903) ^ 479750 = (3 : ZMod 3930112903) ^ (239875 + 239875) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 239875 * (3 : ZMod 3930112903) ^ 239875 := by rw [pow_add]
          _ = 1343018123 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 3930112903) ^ 959500 = 2358639928 := by
        calc
          (3 : ZMod 3930112903) ^ 959500 = (3 : ZMod 3930112903) ^ (479750 + 479750) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 479750 * (3 : ZMod 3930112903) ^ 479750 := by rw [pow_add]
          _ = 2358639928 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 3930112903) ^ 1919000 = 3241335231 := by
        calc
          (3 : ZMod 3930112903) ^ 1919000 = (3 : ZMod 3930112903) ^ (959500 + 959500) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 959500 * (3 : ZMod 3930112903) ^ 959500 := by rw [pow_add]
          _ = 3241335231 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 3930112903) ^ 3838000 = 135706976 := by
        calc
          (3 : ZMod 3930112903) ^ 3838000 = (3 : ZMod 3930112903) ^ (1919000 + 1919000) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 1919000 * (3 : ZMod 3930112903) ^ 1919000 := by rw [pow_add]
          _ = 135706976 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 3930112903) ^ 7676001 = 105658416 := by
        calc
          (3 : ZMod 3930112903) ^ 7676001 = (3 : ZMod 3930112903) ^ (3838000 + 3838000 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 3838000 * (3 : ZMod 3930112903) ^ 3838000) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 105658416 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 3930112903) ^ 15352003 = 973456576 := by
        calc
          (3 : ZMod 3930112903) ^ 15352003 = (3 : ZMod 3930112903) ^ (7676001 + 7676001 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 7676001 * (3 : ZMod 3930112903) ^ 7676001) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 973456576 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 3930112903) ^ 30704007 = 1427059089 := by
        calc
          (3 : ZMod 3930112903) ^ 30704007 = (3 : ZMod 3930112903) ^ (15352003 + 15352003 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 15352003 * (3 : ZMod 3930112903) ^ 15352003) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 1427059089 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 3930112903) ^ 61408014 = 518292027 := by
        calc
          (3 : ZMod 3930112903) ^ 61408014 = (3 : ZMod 3930112903) ^ (30704007 + 30704007) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 30704007 * (3 : ZMod 3930112903) ^ 30704007 := by rw [pow_add]
          _ = 518292027 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 3930112903) ^ 122816028 = 923831828 := by
        calc
          (3 : ZMod 3930112903) ^ 122816028 = (3 : ZMod 3930112903) ^ (61408014 + 61408014) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 61408014 * (3 : ZMod 3930112903) ^ 61408014 := by rw [pow_add]
          _ = 923831828 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 3930112903) ^ 245632056 = 2655019114 := by
        calc
          (3 : ZMod 3930112903) ^ 245632056 = (3 : ZMod 3930112903) ^ (122816028 + 122816028) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 122816028 * (3 : ZMod 3930112903) ^ 122816028 := by rw [pow_add]
          _ = 2655019114 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 3930112903) ^ 491264112 = 221452588 := by
        calc
          (3 : ZMod 3930112903) ^ 491264112 = (3 : ZMod 3930112903) ^ (245632056 + 245632056) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 245632056 * (3 : ZMod 3930112903) ^ 245632056 := by rw [pow_add]
          _ = 221452588 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 3930112903) ^ 982528225 = 1112791456 := by
        calc
          (3 : ZMod 3930112903) ^ 982528225 = (3 : ZMod 3930112903) ^ (491264112 + 491264112 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 491264112 * (3 : ZMod 3930112903) ^ 491264112) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 1112791456 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 3930112903) ^ 1965056451 = 3930112902 := by
        calc
          (3 : ZMod 3930112903) ^ 1965056451 = (3 : ZMod 3930112903) ^ (982528225 + 982528225 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 982528225 * (3 : ZMod 3930112903) ^ 982528225) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 3930112902 := by rw [factor_0_29]; decide
      change (3 : ZMod 3930112903) ^ 1965056451 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (3 : ZMod 3930112903) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 3930112903) ^ 2 = 9 := by
        calc
          (3 : ZMod 3930112903) ^ 2 = (3 : ZMod 3930112903) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 1 * (3 : ZMod 3930112903) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 3930112903) ^ 4 = 81 := by
        calc
          (3 : ZMod 3930112903) ^ 4 = (3 : ZMod 3930112903) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 2 * (3 : ZMod 3930112903) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 3930112903) ^ 9 = 19683 := by
        calc
          (3 : ZMod 3930112903) ^ 9 = (3 : ZMod 3930112903) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 4 * (3 : ZMod 3930112903) ^ 4) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 3930112903) ^ 19 = 1162261467 := by
        calc
          (3 : ZMod 3930112903) ^ 19 = (3 : ZMod 3930112903) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 9 * (3 : ZMod 3930112903) ^ 9) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 1162261467 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 3930112903) ^ 39 = 3048091888 := by
        calc
          (3 : ZMod 3930112903) ^ 39 = (3 : ZMod 3930112903) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 19 * (3 : ZMod 3930112903) ^ 19) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 3048091888 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 3930112903) ^ 78 = 770070273 := by
        calc
          (3 : ZMod 3930112903) ^ 78 = (3 : ZMod 3930112903) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 39 * (3 : ZMod 3930112903) ^ 39 := by rw [pow_add]
          _ = 770070273 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 3930112903) ^ 156 = 1621704800 := by
        calc
          (3 : ZMod 3930112903) ^ 156 = (3 : ZMod 3930112903) ^ (78 + 78) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 78 * (3 : ZMod 3930112903) ^ 78 := by rw [pow_add]
          _ = 1621704800 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 3930112903) ^ 312 = 2734692026 := by
        calc
          (3 : ZMod 3930112903) ^ 312 = (3 : ZMod 3930112903) ^ (156 + 156) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 156 * (3 : ZMod 3930112903) ^ 156 := by rw [pow_add]
          _ = 2734692026 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 3930112903) ^ 624 = 869490253 := by
        calc
          (3 : ZMod 3930112903) ^ 624 = (3 : ZMod 3930112903) ^ (312 + 312) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 312 * (3 : ZMod 3930112903) ^ 312 := by rw [pow_add]
          _ = 869490253 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 3930112903) ^ 1249 = 1376484597 := by
        calc
          (3 : ZMod 3930112903) ^ 1249 = (3 : ZMod 3930112903) ^ (624 + 624 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 624 * (3 : ZMod 3930112903) ^ 624) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 1376484597 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 3930112903) ^ 2498 = 2152629967 := by
        calc
          (3 : ZMod 3930112903) ^ 2498 = (3 : ZMod 3930112903) ^ (1249 + 1249) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 1249 * (3 : ZMod 3930112903) ^ 1249 := by rw [pow_add]
          _ = 2152629967 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 3930112903) ^ 4997 = 3480493471 := by
        calc
          (3 : ZMod 3930112903) ^ 4997 = (3 : ZMod 3930112903) ^ (2498 + 2498 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 2498 * (3 : ZMod 3930112903) ^ 2498) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 3480493471 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 3930112903) ^ 9994 = 2723601555 := by
        calc
          (3 : ZMod 3930112903) ^ 9994 = (3 : ZMod 3930112903) ^ (4997 + 4997) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 4997 * (3 : ZMod 3930112903) ^ 4997 := by rw [pow_add]
          _ = 2723601555 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 3930112903) ^ 19989 = 3452949502 := by
        calc
          (3 : ZMod 3930112903) ^ 19989 = (3 : ZMod 3930112903) ^ (9994 + 9994 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 9994 * (3 : ZMod 3930112903) ^ 9994) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 3452949502 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 3930112903) ^ 39979 = 2928421757 := by
        calc
          (3 : ZMod 3930112903) ^ 39979 = (3 : ZMod 3930112903) ^ (19989 + 19989 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 19989 * (3 : ZMod 3930112903) ^ 19989) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 2928421757 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 3930112903) ^ 79958 = 1763878757 := by
        calc
          (3 : ZMod 3930112903) ^ 79958 = (3 : ZMod 3930112903) ^ (39979 + 39979) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 39979 * (3 : ZMod 3930112903) ^ 39979 := by rw [pow_add]
          _ = 1763878757 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 3930112903) ^ 159916 = 1937140533 := by
        calc
          (3 : ZMod 3930112903) ^ 159916 = (3 : ZMod 3930112903) ^ (79958 + 79958) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 79958 * (3 : ZMod 3930112903) ^ 79958 := by rw [pow_add]
          _ = 1937140533 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 3930112903) ^ 319833 = 62298800 := by
        calc
          (3 : ZMod 3930112903) ^ 319833 = (3 : ZMod 3930112903) ^ (159916 + 159916 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 159916 * (3 : ZMod 3930112903) ^ 159916) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 62298800 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 3930112903) ^ 639666 = 715324283 := by
        calc
          (3 : ZMod 3930112903) ^ 639666 = (3 : ZMod 3930112903) ^ (319833 + 319833) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 319833 * (3 : ZMod 3930112903) ^ 319833 := by rw [pow_add]
          _ = 715324283 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 3930112903) ^ 1279333 = 389606350 := by
        calc
          (3 : ZMod 3930112903) ^ 1279333 = (3 : ZMod 3930112903) ^ (639666 + 639666 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 639666 * (3 : ZMod 3930112903) ^ 639666) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 389606350 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 3930112903) ^ 2558667 = 2932550884 := by
        calc
          (3 : ZMod 3930112903) ^ 2558667 = (3 : ZMod 3930112903) ^ (1279333 + 1279333 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 1279333 * (3 : ZMod 3930112903) ^ 1279333) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 2932550884 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 3930112903) ^ 5117334 = 2252290078 := by
        calc
          (3 : ZMod 3930112903) ^ 5117334 = (3 : ZMod 3930112903) ^ (2558667 + 2558667) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 2558667 * (3 : ZMod 3930112903) ^ 2558667 := by rw [pow_add]
          _ = 2252290078 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 3930112903) ^ 10234669 = 153346084 := by
        calc
          (3 : ZMod 3930112903) ^ 10234669 = (3 : ZMod 3930112903) ^ (5117334 + 5117334 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 5117334 * (3 : ZMod 3930112903) ^ 5117334) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 153346084 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 3930112903) ^ 20469338 = 526292574 := by
        calc
          (3 : ZMod 3930112903) ^ 20469338 = (3 : ZMod 3930112903) ^ (10234669 + 10234669) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 10234669 * (3 : ZMod 3930112903) ^ 10234669 := by rw [pow_add]
          _ = 526292574 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 3930112903) ^ 40938676 = 1585330680 := by
        calc
          (3 : ZMod 3930112903) ^ 40938676 = (3 : ZMod 3930112903) ^ (20469338 + 20469338) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 20469338 * (3 : ZMod 3930112903) ^ 20469338 := by rw [pow_add]
          _ = 1585330680 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 3930112903) ^ 81877352 = 1752857230 := by
        calc
          (3 : ZMod 3930112903) ^ 81877352 = (3 : ZMod 3930112903) ^ (40938676 + 40938676) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 40938676 * (3 : ZMod 3930112903) ^ 40938676 := by rw [pow_add]
          _ = 1752857230 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 3930112903) ^ 163754704 = 513402067 := by
        calc
          (3 : ZMod 3930112903) ^ 163754704 = (3 : ZMod 3930112903) ^ (81877352 + 81877352) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 81877352 * (3 : ZMod 3930112903) ^ 81877352 := by rw [pow_add]
          _ = 513402067 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 3930112903) ^ 327509408 = 2521452180 := by
        calc
          (3 : ZMod 3930112903) ^ 327509408 = (3 : ZMod 3930112903) ^ (163754704 + 163754704) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 163754704 * (3 : ZMod 3930112903) ^ 163754704 := by rw [pow_add]
          _ = 2521452180 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 3930112903) ^ 655018817 = 3634243636 := by
        calc
          (3 : ZMod 3930112903) ^ 655018817 = (3 : ZMod 3930112903) ^ (327509408 + 327509408 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 327509408 * (3 : ZMod 3930112903) ^ 327509408) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 3634243636 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 3930112903) ^ 1310037634 = 3634243635 := by
        calc
          (3 : ZMod 3930112903) ^ 1310037634 = (3 : ZMod 3930112903) ^ (655018817 + 655018817) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 655018817 * (3 : ZMod 3930112903) ^ 655018817 := by rw [pow_add]
          _ = 3634243635 := by rw [factor_1_29]; decide
      change (3 : ZMod 3930112903) ^ 1310037634 ≠ 1
      rw [factor_1_30]
      decide
    ·
      have factor_2_0 : (3 : ZMod 3930112903) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 3930112903) ^ 2 = 9 := by
        calc
          (3 : ZMod 3930112903) ^ 2 = (3 : ZMod 3930112903) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 1 * (3 : ZMod 3930112903) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 3930112903) ^ 5 = 243 := by
        calc
          (3 : ZMod 3930112903) ^ 5 = (3 : ZMod 3930112903) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 2 * (3 : ZMod 3930112903) ^ 2) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 3930112903) ^ 10 = 59049 := by
        calc
          (3 : ZMod 3930112903) ^ 10 = (3 : ZMod 3930112903) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 5 * (3 : ZMod 3930112903) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 3930112903) ^ 20 = 3486784401 := by
        calc
          (3 : ZMod 3930112903) ^ 20 = (3 : ZMod 3930112903) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 10 * (3 : ZMod 3930112903) ^ 10 := by rw [pow_add]
          _ = 3486784401 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 3930112903) ^ 40 = 1284049858 := by
        calc
          (3 : ZMod 3930112903) ^ 40 = (3 : ZMod 3930112903) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 20 * (3 : ZMod 3930112903) ^ 20 := by rw [pow_add]
          _ = 1284049858 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 3930112903) ^ 81 = 1141332856 := by
        calc
          (3 : ZMod 3930112903) ^ 81 = (3 : ZMod 3930112903) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 40 * (3 : ZMod 3930112903) ^ 40) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 1141332856 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 3930112903) ^ 162 = 3188928300 := by
        calc
          (3 : ZMod 3930112903) ^ 162 = (3 : ZMod 3930112903) ^ (81 + 81) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 81 * (3 : ZMod 3930112903) ^ 81 := by rw [pow_add]
          _ = 3188928300 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 3930112903) ^ 325 = 1602864064 := by
        calc
          (3 : ZMod 3930112903) ^ 325 = (3 : ZMod 3930112903) ^ (162 + 162 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 162 * (3 : ZMod 3930112903) ^ 162) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 1602864064 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 3930112903) ^ 651 = 551159645 := by
        calc
          (3 : ZMod 3930112903) ^ 651 = (3 : ZMod 3930112903) ^ (325 + 325 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 325 * (3 : ZMod 3930112903) ^ 325) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 551159645 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 3930112903) ^ 1303 = 424180946 := by
        calc
          (3 : ZMod 3930112903) ^ 1303 = (3 : ZMod 3930112903) ^ (651 + 651 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 651 * (3 : ZMod 3930112903) ^ 651) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 424180946 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 3930112903) ^ 2607 = 1842830154 := by
        calc
          (3 : ZMod 3930112903) ^ 2607 = (3 : ZMod 3930112903) ^ (1303 + 1303 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 1303 * (3 : ZMod 3930112903) ^ 1303) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 1842830154 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 3930112903) ^ 5214 = 1782703139 := by
        calc
          (3 : ZMod 3930112903) ^ 5214 = (3 : ZMod 3930112903) ^ (2607 + 2607) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 2607 * (3 : ZMod 3930112903) ^ 2607 := by rw [pow_add]
          _ = 1782703139 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 3930112903) ^ 10429 = 1315952041 := by
        calc
          (3 : ZMod 3930112903) ^ 10429 = (3 : ZMod 3930112903) ^ (5214 + 5214 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 5214 * (3 : ZMod 3930112903) ^ 5214) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 1315952041 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 3930112903) ^ 20858 = 3074740434 := by
        calc
          (3 : ZMod 3930112903) ^ 20858 = (3 : ZMod 3930112903) ^ (10429 + 10429) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 10429 * (3 : ZMod 3930112903) ^ 10429 := by rw [pow_add]
          _ = 3074740434 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 3930112903) ^ 41717 = 163259247 := by
        calc
          (3 : ZMod 3930112903) ^ 41717 = (3 : ZMod 3930112903) ^ (20858 + 20858 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 20858 * (3 : ZMod 3930112903) ^ 20858) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 163259247 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 3930112903) ^ 83434 = 125619048 := by
        calc
          (3 : ZMod 3930112903) ^ 83434 = (3 : ZMod 3930112903) ^ (41717 + 41717) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 41717 * (3 : ZMod 3930112903) ^ 41717 := by rw [pow_add]
          _ = 125619048 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 3930112903) ^ 166869 = 1300740814 := by
        calc
          (3 : ZMod 3930112903) ^ 166869 = (3 : ZMod 3930112903) ^ (83434 + 83434 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 83434 * (3 : ZMod 3930112903) ^ 83434) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 1300740814 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 3930112903) ^ 333739 = 2096117781 := by
        calc
          (3 : ZMod 3930112903) ^ 333739 = (3 : ZMod 3930112903) ^ (166869 + 166869 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 166869 * (3 : ZMod 3930112903) ^ 166869) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 2096117781 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 3930112903) ^ 667478 = 3715596906 := by
        calc
          (3 : ZMod 3930112903) ^ 667478 = (3 : ZMod 3930112903) ^ (333739 + 333739) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 333739 * (3 : ZMod 3930112903) ^ 333739 := by rw [pow_add]
          _ = 3715596906 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 3930112903) ^ 1334956 = 2644386653 := by
        calc
          (3 : ZMod 3930112903) ^ 1334956 = (3 : ZMod 3930112903) ^ (667478 + 667478) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 667478 * (3 : ZMod 3930112903) ^ 667478 := by rw [pow_add]
          _ = 2644386653 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 3930112903) ^ 2669913 = 3456802410 := by
        calc
          (3 : ZMod 3930112903) ^ 2669913 = (3 : ZMod 3930112903) ^ (1334956 + 1334956 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 1334956 * (3 : ZMod 3930112903) ^ 1334956) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 3456802410 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 3930112903) ^ 5339827 = 2638307022 := by
        calc
          (3 : ZMod 3930112903) ^ 5339827 = (3 : ZMod 3930112903) ^ (2669913 + 2669913 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 2669913 * (3 : ZMod 3930112903) ^ 2669913) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 2638307022 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 3930112903) ^ 10679654 = 543968903 := by
        calc
          (3 : ZMod 3930112903) ^ 10679654 = (3 : ZMod 3930112903) ^ (5339827 + 5339827) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 5339827 * (3 : ZMod 3930112903) ^ 5339827 := by rw [pow_add]
          _ = 543968903 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 3930112903) ^ 21359309 = 510589943 := by
        calc
          (3 : ZMod 3930112903) ^ 21359309 = (3 : ZMod 3930112903) ^ (10679654 + 10679654 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 10679654 * (3 : ZMod 3930112903) ^ 10679654) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 510589943 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 3930112903) ^ 42718618 = 3738351040 := by
        calc
          (3 : ZMod 3930112903) ^ 42718618 = (3 : ZMod 3930112903) ^ (21359309 + 21359309) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 21359309 * (3 : ZMod 3930112903) ^ 21359309 := by rw [pow_add]
          _ = 3738351040 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 3930112903) ^ 85437237 = 3359014540 := by
        calc
          (3 : ZMod 3930112903) ^ 85437237 = (3 : ZMod 3930112903) ^ (42718618 + 42718618 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 42718618 * (3 : ZMod 3930112903) ^ 42718618) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 3359014540 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 3930112903) ^ 170874474 = 2684712608 := by
        calc
          (3 : ZMod 3930112903) ^ 170874474 = (3 : ZMod 3930112903) ^ (85437237 + 85437237) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 85437237 * (3 : ZMod 3930112903) ^ 85437237 := by rw [pow_add]
          _ = 2684712608 := by rw [factor_2_26]; decide
      change (3 : ZMod 3930112903) ^ 170874474 ≠ 1
      rw [factor_2_27]
      decide
    ·
      have factor_3_0 : (3 : ZMod 3930112903) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 3930112903) ^ 2 = 9 := by
        calc
          (3 : ZMod 3930112903) ^ 2 = (3 : ZMod 3930112903) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 1 * (3 : ZMod 3930112903) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 3930112903) ^ 5 = 243 := by
        calc
          (3 : ZMod 3930112903) ^ 5 = (3 : ZMod 3930112903) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 2 * (3 : ZMod 3930112903) ^ 2) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 3930112903) ^ 10 = 59049 := by
        calc
          (3 : ZMod 3930112903) ^ 10 = (3 : ZMod 3930112903) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 5 * (3 : ZMod 3930112903) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 3930112903) ^ 20 = 3486784401 := by
        calc
          (3 : ZMod 3930112903) ^ 20 = (3 : ZMod 3930112903) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 10 * (3 : ZMod 3930112903) ^ 10 := by rw [pow_add]
          _ = 3486784401 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 3930112903) ^ 41 = 3852149574 := by
        calc
          (3 : ZMod 3930112903) ^ 41 = (3 : ZMod 3930112903) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 20 * (3 : ZMod 3930112903) ^ 20) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 3852149574 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 3930112903) ^ 83 = 2411769898 := by
        calc
          (3 : ZMod 3930112903) ^ 83 = (3 : ZMod 3930112903) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 41 * (3 : ZMod 3930112903) ^ 41) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 2411769898 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 3930112903) ^ 167 = 677335009 := by
        calc
          (3 : ZMod 3930112903) ^ 167 = (3 : ZMod 3930112903) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 83 * (3 : ZMod 3930112903) ^ 83) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 677335009 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 3930112903) ^ 335 = 2541185090 := by
        calc
          (3 : ZMod 3930112903) ^ 335 = (3 : ZMod 3930112903) ^ (167 + 167 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 167 * (3 : ZMod 3930112903) ^ 167) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 2541185090 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 3930112903) ^ 670 = 3802220831 := by
        calc
          (3 : ZMod 3930112903) ^ 670 = (3 : ZMod 3930112903) ^ (335 + 335) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 335 * (3 : ZMod 3930112903) ^ 335 := by rw [pow_add]
          _ = 3802220831 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 3930112903) ^ 1340 = 2829731657 := by
        calc
          (3 : ZMod 3930112903) ^ 1340 = (3 : ZMod 3930112903) ^ (670 + 670) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 670 * (3 : ZMod 3930112903) ^ 670 := by rw [pow_add]
          _ = 2829731657 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 3930112903) ^ 2680 = 3184501178 := by
        calc
          (3 : ZMod 3930112903) ^ 2680 = (3 : ZMod 3930112903) ^ (1340 + 1340) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 1340 * (3 : ZMod 3930112903) ^ 1340 := by rw [pow_add]
          _ = 3184501178 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 3930112903) ^ 5360 = 195368846 := by
        calc
          (3 : ZMod 3930112903) ^ 5360 = (3 : ZMod 3930112903) ^ (2680 + 2680) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 2680 * (3 : ZMod 3930112903) ^ 2680 := by rw [pow_add]
          _ = 195368846 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 3930112903) ^ 10720 = 651226023 := by
        calc
          (3 : ZMod 3930112903) ^ 10720 = (3 : ZMod 3930112903) ^ (5360 + 5360) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 5360 * (3 : ZMod 3930112903) ^ 5360 := by rw [pow_add]
          _ = 651226023 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 3930112903) ^ 21441 = 930531302 := by
        calc
          (3 : ZMod 3930112903) ^ 21441 = (3 : ZMod 3930112903) ^ (10720 + 10720 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 10720 * (3 : ZMod 3930112903) ^ 10720) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 930531302 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 3930112903) ^ 42882 = 419662002 := by
        calc
          (3 : ZMod 3930112903) ^ 42882 = (3 : ZMod 3930112903) ^ (21441 + 21441) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 21441 * (3 : ZMod 3930112903) ^ 21441 := by rw [pow_add]
          _ = 419662002 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 3930112903) ^ 85765 = 282268266 := by
        calc
          (3 : ZMod 3930112903) ^ 85765 = (3 : ZMod 3930112903) ^ (42882 + 42882 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 42882 * (3 : ZMod 3930112903) ^ 42882) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 282268266 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 3930112903) ^ 171530 = 2532595509 := by
        calc
          (3 : ZMod 3930112903) ^ 171530 = (3 : ZMod 3930112903) ^ (85765 + 85765) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 85765 * (3 : ZMod 3930112903) ^ 85765 := by rw [pow_add]
          _ = 2532595509 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 3930112903) ^ 343061 = 3720601167 := by
        calc
          (3 : ZMod 3930112903) ^ 343061 = (3 : ZMod 3930112903) ^ (171530 + 171530 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 171530 * (3 : ZMod 3930112903) ^ 171530) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 3720601167 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 3930112903) ^ 686123 = 3407186494 := by
        calc
          (3 : ZMod 3930112903) ^ 686123 = (3 : ZMod 3930112903) ^ (343061 + 343061 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 343061 * (3 : ZMod 3930112903) ^ 343061) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 3407186494 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 3930112903) ^ 1372246 = 489056271 := by
        calc
          (3 : ZMod 3930112903) ^ 1372246 = (3 : ZMod 3930112903) ^ (686123 + 686123) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 686123 * (3 : ZMod 3930112903) ^ 686123 := by rw [pow_add]
          _ = 489056271 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 3930112903) ^ 2744492 = 3743473862 := by
        calc
          (3 : ZMod 3930112903) ^ 2744492 = (3 : ZMod 3930112903) ^ (1372246 + 1372246) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 1372246 * (3 : ZMod 3930112903) ^ 1372246 := by rw [pow_add]
          _ = 3743473862 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 3930112903) ^ 5488984 = 361852705 := by
        calc
          (3 : ZMod 3930112903) ^ 5488984 = (3 : ZMod 3930112903) ^ (2744492 + 2744492) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 2744492 * (3 : ZMod 3930112903) ^ 2744492 := by rw [pow_add]
          _ = 361852705 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 3930112903) ^ 10977969 = 658584794 := by
        calc
          (3 : ZMod 3930112903) ^ 10977969 = (3 : ZMod 3930112903) ^ (5488984 + 5488984 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 5488984 * (3 : ZMod 3930112903) ^ 5488984) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 658584794 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 3930112903) ^ 21955938 = 1511346045 := by
        calc
          (3 : ZMod 3930112903) ^ 21955938 = (3 : ZMod 3930112903) ^ (10977969 + 10977969) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 10977969 * (3 : ZMod 3930112903) ^ 10977969 := by rw [pow_add]
          _ = 1511346045 := by rw [factor_3_23]; decide
      change (3 : ZMod 3930112903) ^ 21955938 ≠ 1
      rw [factor_3_24]
      decide
    ·
      have factor_4_0 : (3 : ZMod 3930112903) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 3930112903) ^ 2 = 9 := by
        calc
          (3 : ZMod 3930112903) ^ 2 = (3 : ZMod 3930112903) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 1 * (3 : ZMod 3930112903) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 3930112903) ^ 4 = 81 := by
        calc
          (3 : ZMod 3930112903) ^ 4 = (3 : ZMod 3930112903) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 2 * (3 : ZMod 3930112903) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 3930112903) ^ 9 = 19683 := by
        calc
          (3 : ZMod 3930112903) ^ 9 = (3 : ZMod 3930112903) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 4 * (3 : ZMod 3930112903) ^ 4) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 3930112903) ^ 19 = 1162261467 := by
        calc
          (3 : ZMod 3930112903) ^ 19 = (3 : ZMod 3930112903) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 9 * (3 : ZMod 3930112903) ^ 9) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 1162261467 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 3930112903) ^ 38 = 3636105898 := by
        calc
          (3 : ZMod 3930112903) ^ 38 = (3 : ZMod 3930112903) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 19 * (3 : ZMod 3930112903) ^ 19 := by rw [pow_add]
          _ = 3636105898 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 3930112903) ^ 77 = 256690091 := by
        calc
          (3 : ZMod 3930112903) ^ 77 = (3 : ZMod 3930112903) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 38 * (3 : ZMod 3930112903) ^ 38) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 256690091 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 3930112903) ^ 154 = 1926906268 := by
        calc
          (3 : ZMod 3930112903) ^ 154 = (3 : ZMod 3930112903) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 77 * (3 : ZMod 3930112903) ^ 77 := by rw [pow_add]
          _ = 1926906268 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 3930112903) ^ 308 = 2702356811 := by
        calc
          (3 : ZMod 3930112903) ^ 308 = (3 : ZMod 3930112903) ^ (154 + 154) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 154 * (3 : ZMod 3930112903) ^ 154 := by rw [pow_add]
          _ = 2702356811 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 3930112903) ^ 616 = 3478590934 := by
        calc
          (3 : ZMod 3930112903) ^ 616 = (3 : ZMod 3930112903) ^ (308 + 308) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 308 * (3 : ZMod 3930112903) ^ 308 := by rw [pow_add]
          _ = 3478590934 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 3930112903) ^ 1233 = 2546648352 := by
        calc
          (3 : ZMod 3930112903) ^ 1233 = (3 : ZMod 3930112903) ^ (616 + 616 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 616 * (3 : ZMod 3930112903) ^ 616) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 2546648352 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 3930112903) ^ 2466 = 3299003096 := by
        calc
          (3 : ZMod 3930112903) ^ 2466 = (3 : ZMod 3930112903) ^ (1233 + 1233) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 1233 * (3 : ZMod 3930112903) ^ 1233 := by rw [pow_add]
          _ = 3299003096 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 3930112903) ^ 4933 = 3453320691 := by
        calc
          (3 : ZMod 3930112903) ^ 4933 = (3 : ZMod 3930112903) ^ (2466 + 2466 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 2466 * (3 : ZMod 3930112903) ^ 2466) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 3453320691 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 3930112903) ^ 9866 = 3698591760 := by
        calc
          (3 : ZMod 3930112903) ^ 9866 = (3 : ZMod 3930112903) ^ (4933 + 4933) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 4933 * (3 : ZMod 3930112903) ^ 4933 := by rw [pow_add]
          _ = 3698591760 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 3930112903) ^ 19732 = 74138437 := by
        calc
          (3 : ZMod 3930112903) ^ 19732 = (3 : ZMod 3930112903) ^ (9866 + 9866) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 9866 * (3 : ZMod 3930112903) ^ 9866 := by rw [pow_add]
          _ = 74138437 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 3930112903) ^ 39465 = 3836872449 := by
        calc
          (3 : ZMod 3930112903) ^ 39465 = (3 : ZMod 3930112903) ^ (19732 + 19732 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 19732 * (3 : ZMod 3930112903) ^ 19732) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 3836872449 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 3930112903) ^ 78930 = 3090077234 := by
        calc
          (3 : ZMod 3930112903) ^ 78930 = (3 : ZMod 3930112903) ^ (39465 + 39465) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 39465 * (3 : ZMod 3930112903) ^ 39465 := by rw [pow_add]
          _ = 3090077234 := by rw [factor_4_15]; decide
      have factor_4_17 : (3 : ZMod 3930112903) ^ 157861 = 3283287314 := by
        calc
          (3 : ZMod 3930112903) ^ 157861 = (3 : ZMod 3930112903) ^ (78930 + 78930 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 78930 * (3 : ZMod 3930112903) ^ 78930) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 3283287314 := by rw [factor_4_16]; decide
      have factor_4_18 : (3 : ZMod 3930112903) ^ 315722 = 1895219200 := by
        calc
          (3 : ZMod 3930112903) ^ 315722 = (3 : ZMod 3930112903) ^ (157861 + 157861) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 157861 * (3 : ZMod 3930112903) ^ 157861 := by rw [pow_add]
          _ = 1895219200 := by rw [factor_4_17]; decide
      have factor_4_19 : (3 : ZMod 3930112903) ^ 631444 = 77769799 := by
        calc
          (3 : ZMod 3930112903) ^ 631444 = (3 : ZMod 3930112903) ^ (315722 + 315722) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 315722 * (3 : ZMod 3930112903) ^ 315722 := by rw [pow_add]
          _ = 77769799 := by rw [factor_4_18]; decide
      have factor_4_20 : (3 : ZMod 3930112903) ^ 1262889 = 1492430796 := by
        calc
          (3 : ZMod 3930112903) ^ 1262889 = (3 : ZMod 3930112903) ^ (631444 + 631444 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 631444 * (3 : ZMod 3930112903) ^ 631444) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 1492430796 := by rw [factor_4_19]; decide
      have factor_4_21 : (3 : ZMod 3930112903) ^ 2525779 = 914904287 := by
        calc
          (3 : ZMod 3930112903) ^ 2525779 = (3 : ZMod 3930112903) ^ (1262889 + 1262889 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 1262889 * (3 : ZMod 3930112903) ^ 1262889) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 914904287 := by rw [factor_4_20]; decide
      have factor_4_22 : (3 : ZMod 3930112903) ^ 5051559 = 1488407913 := by
        calc
          (3 : ZMod 3930112903) ^ 5051559 = (3 : ZMod 3930112903) ^ (2525779 + 2525779 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 2525779 * (3 : ZMod 3930112903) ^ 2525779) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 1488407913 := by rw [factor_4_21]; decide
      have factor_4_23 : (3 : ZMod 3930112903) ^ 10103118 = 666574186 := by
        calc
          (3 : ZMod 3930112903) ^ 10103118 = (3 : ZMod 3930112903) ^ (5051559 + 5051559) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 5051559 * (3 : ZMod 3930112903) ^ 5051559 := by rw [pow_add]
          _ = 666574186 := by rw [factor_4_22]; decide
      change (3 : ZMod 3930112903) ^ 10103118 ≠ 1
      rw [factor_4_23]
      decide
    ·
      have factor_5_0 : (3 : ZMod 3930112903) ^ 1 = 3 := by norm_num
      have factor_5_1 : (3 : ZMod 3930112903) ^ 2 = 9 := by
        calc
          (3 : ZMod 3930112903) ^ 2 = (3 : ZMod 3930112903) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 1 * (3 : ZMod 3930112903) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_5_0]; decide
      have factor_5_2 : (3 : ZMod 3930112903) ^ 4 = 81 := by
        calc
          (3 : ZMod 3930112903) ^ 4 = (3 : ZMod 3930112903) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 2 * (3 : ZMod 3930112903) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_5_1]; decide
      have factor_5_3 : (3 : ZMod 3930112903) ^ 9 = 19683 := by
        calc
          (3 : ZMod 3930112903) ^ 9 = (3 : ZMod 3930112903) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 4 * (3 : ZMod 3930112903) ^ 4) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_5_2]; decide
      have factor_5_4 : (3 : ZMod 3930112903) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 3930112903) ^ 18 = (3 : ZMod 3930112903) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 9 * (3 : ZMod 3930112903) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [factor_5_3]; decide
      have factor_5_5 : (3 : ZMod 3930112903) ^ 36 = 3897445458 := by
        calc
          (3 : ZMod 3930112903) ^ 36 = (3 : ZMod 3930112903) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 18 * (3 : ZMod 3930112903) ^ 18 := by rw [pow_add]
          _ = 3897445458 := by rw [factor_5_4]; decide
      have factor_5_6 : (3 : ZMod 3930112903) ^ 73 = 197248663 := by
        calc
          (3 : ZMod 3930112903) ^ 73 = (3 : ZMod 3930112903) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 36 * (3 : ZMod 3930112903) ^ 36) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 197248663 := by rw [factor_5_5]; decide
      have factor_5_7 : (3 : ZMod 3930112903) ^ 146 = 2026748797 := by
        calc
          (3 : ZMod 3930112903) ^ 146 = (3 : ZMod 3930112903) ^ (73 + 73) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 73 * (3 : ZMod 3930112903) ^ 73 := by rw [pow_add]
          _ = 2026748797 := by rw [factor_5_6]; decide
      have factor_5_8 : (3 : ZMod 3930112903) ^ 293 = 749518031 := by
        calc
          (3 : ZMod 3930112903) ^ 293 = (3 : ZMod 3930112903) ^ (146 + 146 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 146 * (3 : ZMod 3930112903) ^ 146) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 749518031 := by rw [factor_5_7]; decide
      have factor_5_9 : (3 : ZMod 3930112903) ^ 586 = 3790023166 := by
        calc
          (3 : ZMod 3930112903) ^ 586 = (3 : ZMod 3930112903) ^ (293 + 293) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 293 * (3 : ZMod 3930112903) ^ 293 := by rw [pow_add]
          _ = 3790023166 := by rw [factor_5_8]; decide
      have factor_5_10 : (3 : ZMod 3930112903) ^ 1172 = 1658324482 := by
        calc
          (3 : ZMod 3930112903) ^ 1172 = (3 : ZMod 3930112903) ^ (586 + 586) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 586 * (3 : ZMod 3930112903) ^ 586 := by rw [pow_add]
          _ = 1658324482 := by rw [factor_5_9]; decide
      have factor_5_11 : (3 : ZMod 3930112903) ^ 2345 = 1491122667 := by
        calc
          (3 : ZMod 3930112903) ^ 2345 = (3 : ZMod 3930112903) ^ (1172 + 1172 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 1172 * (3 : ZMod 3930112903) ^ 1172) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 1491122667 := by rw [factor_5_10]; decide
      have factor_5_12 : (3 : ZMod 3930112903) ^ 4691 = 2362310027 := by
        calc
          (3 : ZMod 3930112903) ^ 4691 = (3 : ZMod 3930112903) ^ (2345 + 2345 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 2345 * (3 : ZMod 3930112903) ^ 2345) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 2362310027 := by rw [factor_5_11]; decide
      have factor_5_13 : (3 : ZMod 3930112903) ^ 9383 = 2833001390 := by
        calc
          (3 : ZMod 3930112903) ^ 9383 = (3 : ZMod 3930112903) ^ (4691 + 4691 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 4691 * (3 : ZMod 3930112903) ^ 4691) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 2833001390 := by rw [factor_5_12]; decide
      have factor_5_14 : (3 : ZMod 3930112903) ^ 18767 = 1432675004 := by
        calc
          (3 : ZMod 3930112903) ^ 18767 = (3 : ZMod 3930112903) ^ (9383 + 9383 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 9383 * (3 : ZMod 3930112903) ^ 9383) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 1432675004 := by rw [factor_5_13]; decide
      have factor_5_15 : (3 : ZMod 3930112903) ^ 37535 = 780185542 := by
        calc
          (3 : ZMod 3930112903) ^ 37535 = (3 : ZMod 3930112903) ^ (18767 + 18767 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 18767 * (3 : ZMod 3930112903) ^ 18767) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 780185542 := by rw [factor_5_14]; decide
      have factor_5_16 : (3 : ZMod 3930112903) ^ 75070 = 3543338557 := by
        calc
          (3 : ZMod 3930112903) ^ 75070 = (3 : ZMod 3930112903) ^ (37535 + 37535) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 37535 * (3 : ZMod 3930112903) ^ 37535 := by rw [pow_add]
          _ = 3543338557 := by rw [factor_5_15]; decide
      have factor_5_17 : (3 : ZMod 3930112903) ^ 150141 = 3584532709 := by
        calc
          (3 : ZMod 3930112903) ^ 150141 = (3 : ZMod 3930112903) ^ (75070 + 75070 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 75070 * (3 : ZMod 3930112903) ^ 75070) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 3584532709 := by rw [factor_5_16]; decide
      have factor_5_18 : (3 : ZMod 3930112903) ^ 300283 = 40253363 := by
        calc
          (3 : ZMod 3930112903) ^ 300283 = (3 : ZMod 3930112903) ^ (150141 + 150141 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 150141 * (3 : ZMod 3930112903) ^ 150141) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 40253363 := by rw [factor_5_17]; decide
      have factor_5_19 : (3 : ZMod 3930112903) ^ 600567 = 253224727 := by
        calc
          (3 : ZMod 3930112903) ^ 600567 = (3 : ZMod 3930112903) ^ (300283 + 300283 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 300283 * (3 : ZMod 3930112903) ^ 300283) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 253224727 := by rw [factor_5_18]; decide
      have factor_5_20 : (3 : ZMod 3930112903) ^ 1201134 = 3116537764 := by
        calc
          (3 : ZMod 3930112903) ^ 1201134 = (3 : ZMod 3930112903) ^ (600567 + 600567) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 600567 * (3 : ZMod 3930112903) ^ 600567 := by rw [pow_add]
          _ = 3116537764 := by rw [factor_5_19]; decide
      have factor_5_21 : (3 : ZMod 3930112903) ^ 2402269 = 2467149663 := by
        calc
          (3 : ZMod 3930112903) ^ 2402269 = (3 : ZMod 3930112903) ^ (1201134 + 1201134 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 1201134 * (3 : ZMod 3930112903) ^ 1201134) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 2467149663 := by rw [factor_5_20]; decide
      have factor_5_22 : (3 : ZMod 3930112903) ^ 4804539 = 328689025 := by
        calc
          (3 : ZMod 3930112903) ^ 4804539 = (3 : ZMod 3930112903) ^ (2402269 + 2402269 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = ((3 : ZMod 3930112903) ^ 2402269 * (3 : ZMod 3930112903) ^ 2402269) * (3 : ZMod 3930112903) := by rw [pow_succ, pow_add]
          _ = 328689025 := by rw [factor_5_21]; decide
      have factor_5_23 : (3 : ZMod 3930112903) ^ 9609078 = 2008932104 := by
        calc
          (3 : ZMod 3930112903) ^ 9609078 = (3 : ZMod 3930112903) ^ (4804539 + 4804539) :=
            congrArg (fun n : ℕ => (3 : ZMod 3930112903) ^ n) (by norm_num)
          _ = (3 : ZMod 3930112903) ^ 4804539 * (3 : ZMod 3930112903) ^ 4804539 := by rw [pow_add]
          _ = 2008932104 := by rw [factor_5_22]; decide
      change (3 : ZMod 3930112903) ^ 9609078 ≠ 1
      rw [factor_5_23]
      decide

#print axioms prime_lucas_3930112903

end TotientTailPeriodKiller
end Erdos249257
