import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=32 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_289946887 : Nat.Prime 289946887 := by
  apply lucas_primality 289946887 (3 : ZMod 289946887)
  ·
      have fermat_0 : (3 : ZMod 289946887) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 289946887) ^ 2 = 9 := by
        calc
          (3 : ZMod 289946887) ^ 2 = (3 : ZMod 289946887) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 1 * (3 : ZMod 289946887) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 289946887) ^ 4 = 81 := by
        calc
          (3 : ZMod 289946887) ^ 4 = (3 : ZMod 289946887) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 2 * (3 : ZMod 289946887) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 289946887) ^ 8 = 6561 := by
        calc
          (3 : ZMod 289946887) ^ 8 = (3 : ZMod 289946887) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 4 * (3 : ZMod 289946887) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 289946887) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 289946887) ^ 17 = (3 : ZMod 289946887) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 8 * (3 : ZMod 289946887) ^ 8) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 289946887) ^ 34 = 126228010 := by
        calc
          (3 : ZMod 289946887) ^ 34 = (3 : ZMod 289946887) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 17 * (3 : ZMod 289946887) ^ 17 := by rw [pow_add]
          _ = 126228010 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 289946887) ^ 69 = 234252456 := by
        calc
          (3 : ZMod 289946887) ^ 69 = (3 : ZMod 289946887) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 34 * (3 : ZMod 289946887) ^ 34) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 234252456 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 289946887) ^ 138 = 160527654 := by
        calc
          (3 : ZMod 289946887) ^ 138 = (3 : ZMod 289946887) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 69 * (3 : ZMod 289946887) ^ 69 := by rw [pow_add]
          _ = 160527654 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 289946887) ^ 276 = 114570910 := by
        calc
          (3 : ZMod 289946887) ^ 276 = (3 : ZMod 289946887) ^ (138 + 138) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 138 * (3 : ZMod 289946887) ^ 138 := by rw [pow_add]
          _ = 114570910 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 289946887) ^ 553 = 209718205 := by
        calc
          (3 : ZMod 289946887) ^ 553 = (3 : ZMod 289946887) ^ (276 + 276 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 276 * (3 : ZMod 289946887) ^ 276) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 209718205 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 289946887) ^ 1106 = 1180177 := by
        calc
          (3 : ZMod 289946887) ^ 1106 = (3 : ZMod 289946887) ^ (553 + 553) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 553 * (3 : ZMod 289946887) ^ 553 := by rw [pow_add]
          _ = 1180177 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 289946887) ^ 2212 = 202853068 := by
        calc
          (3 : ZMod 289946887) ^ 2212 = (3 : ZMod 289946887) ^ (1106 + 1106) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 1106 * (3 : ZMod 289946887) ^ 1106 := by rw [pow_add]
          _ = 202853068 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 289946887) ^ 4424 = 33199530 := by
        calc
          (3 : ZMod 289946887) ^ 4424 = (3 : ZMod 289946887) ^ (2212 + 2212) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 2212 * (3 : ZMod 289946887) ^ 2212 := by rw [pow_add]
          _ = 33199530 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 289946887) ^ 8848 = 56828908 := by
        calc
          (3 : ZMod 289946887) ^ 8848 = (3 : ZMod 289946887) ^ (4424 + 4424) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 4424 * (3 : ZMod 289946887) ^ 4424 := by rw [pow_add]
          _ = 56828908 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 289946887) ^ 17696 = 94699980 := by
        calc
          (3 : ZMod 289946887) ^ 17696 = (3 : ZMod 289946887) ^ (8848 + 8848) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 8848 * (3 : ZMod 289946887) ^ 8848 := by rw [pow_add]
          _ = 94699980 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 289946887) ^ 35393 = 7205100 := by
        calc
          (3 : ZMod 289946887) ^ 35393 = (3 : ZMod 289946887) ^ (17696 + 17696 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 17696 * (3 : ZMod 289946887) ^ 17696) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 7205100 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 289946887) ^ 70787 = 66828142 := by
        calc
          (3 : ZMod 289946887) ^ 70787 = (3 : ZMod 289946887) ^ (35393 + 35393 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 35393 * (3 : ZMod 289946887) ^ 35393) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 66828142 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 289946887) ^ 141575 = 239877376 := by
        calc
          (3 : ZMod 289946887) ^ 141575 = (3 : ZMod 289946887) ^ (70787 + 70787 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 70787 * (3 : ZMod 289946887) ^ 70787) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 239877376 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 289946887) ^ 283151 = 151600164 := by
        calc
          (3 : ZMod 289946887) ^ 283151 = (3 : ZMod 289946887) ^ (141575 + 141575 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 141575 * (3 : ZMod 289946887) ^ 141575) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 151600164 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 289946887) ^ 566302 = 171195031 := by
        calc
          (3 : ZMod 289946887) ^ 566302 = (3 : ZMod 289946887) ^ (283151 + 283151) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 283151 * (3 : ZMod 289946887) ^ 283151 := by rw [pow_add]
          _ = 171195031 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 289946887) ^ 1132605 = 252404403 := by
        calc
          (3 : ZMod 289946887) ^ 1132605 = (3 : ZMod 289946887) ^ (566302 + 566302 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 566302 * (3 : ZMod 289946887) ^ 566302) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 252404403 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 289946887) ^ 2265210 = 198298629 := by
        calc
          (3 : ZMod 289946887) ^ 2265210 = (3 : ZMod 289946887) ^ (1132605 + 1132605) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 1132605 * (3 : ZMod 289946887) ^ 1132605 := by rw [pow_add]
          _ = 198298629 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 289946887) ^ 4530420 = 252396896 := by
        calc
          (3 : ZMod 289946887) ^ 4530420 = (3 : ZMod 289946887) ^ (2265210 + 2265210) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 2265210 * (3 : ZMod 289946887) ^ 2265210 := by rw [pow_add]
          _ = 252396896 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 289946887) ^ 9060840 = 260760126 := by
        calc
          (3 : ZMod 289946887) ^ 9060840 = (3 : ZMod 289946887) ^ (4530420 + 4530420) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 4530420 * (3 : ZMod 289946887) ^ 4530420 := by rw [pow_add]
          _ = 260760126 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 289946887) ^ 18121680 = 164196251 := by
        calc
          (3 : ZMod 289946887) ^ 18121680 = (3 : ZMod 289946887) ^ (9060840 + 9060840) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 9060840 * (3 : ZMod 289946887) ^ 9060840 := by rw [pow_add]
          _ = 164196251 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 289946887) ^ 36243360 = 259310029 := by
        calc
          (3 : ZMod 289946887) ^ 36243360 = (3 : ZMod 289946887) ^ (18121680 + 18121680) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 18121680 * (3 : ZMod 289946887) ^ 18121680 := by rw [pow_add]
          _ = 259310029 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 289946887) ^ 72486721 = 117078422 := by
        calc
          (3 : ZMod 289946887) ^ 72486721 = (3 : ZMod 289946887) ^ (36243360 + 36243360 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 36243360 * (3 : ZMod 289946887) ^ 36243360) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 117078422 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 289946887) ^ 144973443 = 289946886 := by
        calc
          (3 : ZMod 289946887) ^ 144973443 = (3 : ZMod 289946887) ^ (72486721 + 72486721 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 72486721 * (3 : ZMod 289946887) ^ 72486721) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 289946886 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 289946887) ^ 289946886 = 1 := by
        calc
          (3 : ZMod 289946887) ^ 289946886 = (3 : ZMod 289946887) ^ (144973443 + 144973443) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 144973443 * (3 : ZMod 289946887) ^ 144973443 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (59, 1), (257, 1), (3187, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (59, 1), (257, 1), (3187, 1)] : List FactorBlock).map factorBlockValue).prod = 289946887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 289946887) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 289946887) ^ 2 = 9 := by
        calc
          (3 : ZMod 289946887) ^ 2 = (3 : ZMod 289946887) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 1 * (3 : ZMod 289946887) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 289946887) ^ 4 = 81 := by
        calc
          (3 : ZMod 289946887) ^ 4 = (3 : ZMod 289946887) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 2 * (3 : ZMod 289946887) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 289946887) ^ 8 = 6561 := by
        calc
          (3 : ZMod 289946887) ^ 8 = (3 : ZMod 289946887) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 4 * (3 : ZMod 289946887) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 289946887) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 289946887) ^ 17 = (3 : ZMod 289946887) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 8 * (3 : ZMod 289946887) ^ 8) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 289946887) ^ 34 = 126228010 := by
        calc
          (3 : ZMod 289946887) ^ 34 = (3 : ZMod 289946887) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 17 * (3 : ZMod 289946887) ^ 17 := by rw [pow_add]
          _ = 126228010 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 289946887) ^ 69 = 234252456 := by
        calc
          (3 : ZMod 289946887) ^ 69 = (3 : ZMod 289946887) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 34 * (3 : ZMod 289946887) ^ 34) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 234252456 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 289946887) ^ 138 = 160527654 := by
        calc
          (3 : ZMod 289946887) ^ 138 = (3 : ZMod 289946887) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 69 * (3 : ZMod 289946887) ^ 69 := by rw [pow_add]
          _ = 160527654 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 289946887) ^ 276 = 114570910 := by
        calc
          (3 : ZMod 289946887) ^ 276 = (3 : ZMod 289946887) ^ (138 + 138) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 138 * (3 : ZMod 289946887) ^ 138 := by rw [pow_add]
          _ = 114570910 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 289946887) ^ 553 = 209718205 := by
        calc
          (3 : ZMod 289946887) ^ 553 = (3 : ZMod 289946887) ^ (276 + 276 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 276 * (3 : ZMod 289946887) ^ 276) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 209718205 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 289946887) ^ 1106 = 1180177 := by
        calc
          (3 : ZMod 289946887) ^ 1106 = (3 : ZMod 289946887) ^ (553 + 553) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 553 * (3 : ZMod 289946887) ^ 553 := by rw [pow_add]
          _ = 1180177 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 289946887) ^ 2212 = 202853068 := by
        calc
          (3 : ZMod 289946887) ^ 2212 = (3 : ZMod 289946887) ^ (1106 + 1106) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 1106 * (3 : ZMod 289946887) ^ 1106 := by rw [pow_add]
          _ = 202853068 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 289946887) ^ 4424 = 33199530 := by
        calc
          (3 : ZMod 289946887) ^ 4424 = (3 : ZMod 289946887) ^ (2212 + 2212) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 2212 * (3 : ZMod 289946887) ^ 2212 := by rw [pow_add]
          _ = 33199530 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 289946887) ^ 8848 = 56828908 := by
        calc
          (3 : ZMod 289946887) ^ 8848 = (3 : ZMod 289946887) ^ (4424 + 4424) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 4424 * (3 : ZMod 289946887) ^ 4424 := by rw [pow_add]
          _ = 56828908 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 289946887) ^ 17696 = 94699980 := by
        calc
          (3 : ZMod 289946887) ^ 17696 = (3 : ZMod 289946887) ^ (8848 + 8848) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 8848 * (3 : ZMod 289946887) ^ 8848 := by rw [pow_add]
          _ = 94699980 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 289946887) ^ 35393 = 7205100 := by
        calc
          (3 : ZMod 289946887) ^ 35393 = (3 : ZMod 289946887) ^ (17696 + 17696 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 17696 * (3 : ZMod 289946887) ^ 17696) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 7205100 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 289946887) ^ 70787 = 66828142 := by
        calc
          (3 : ZMod 289946887) ^ 70787 = (3 : ZMod 289946887) ^ (35393 + 35393 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 35393 * (3 : ZMod 289946887) ^ 35393) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 66828142 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 289946887) ^ 141575 = 239877376 := by
        calc
          (3 : ZMod 289946887) ^ 141575 = (3 : ZMod 289946887) ^ (70787 + 70787 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 70787 * (3 : ZMod 289946887) ^ 70787) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 239877376 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 289946887) ^ 283151 = 151600164 := by
        calc
          (3 : ZMod 289946887) ^ 283151 = (3 : ZMod 289946887) ^ (141575 + 141575 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 141575 * (3 : ZMod 289946887) ^ 141575) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 151600164 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 289946887) ^ 566302 = 171195031 := by
        calc
          (3 : ZMod 289946887) ^ 566302 = (3 : ZMod 289946887) ^ (283151 + 283151) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 283151 * (3 : ZMod 289946887) ^ 283151 := by rw [pow_add]
          _ = 171195031 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 289946887) ^ 1132605 = 252404403 := by
        calc
          (3 : ZMod 289946887) ^ 1132605 = (3 : ZMod 289946887) ^ (566302 + 566302 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 566302 * (3 : ZMod 289946887) ^ 566302) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 252404403 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 289946887) ^ 2265210 = 198298629 := by
        calc
          (3 : ZMod 289946887) ^ 2265210 = (3 : ZMod 289946887) ^ (1132605 + 1132605) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 1132605 * (3 : ZMod 289946887) ^ 1132605 := by rw [pow_add]
          _ = 198298629 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 289946887) ^ 4530420 = 252396896 := by
        calc
          (3 : ZMod 289946887) ^ 4530420 = (3 : ZMod 289946887) ^ (2265210 + 2265210) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 2265210 * (3 : ZMod 289946887) ^ 2265210 := by rw [pow_add]
          _ = 252396896 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 289946887) ^ 9060840 = 260760126 := by
        calc
          (3 : ZMod 289946887) ^ 9060840 = (3 : ZMod 289946887) ^ (4530420 + 4530420) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 4530420 * (3 : ZMod 289946887) ^ 4530420 := by rw [pow_add]
          _ = 260760126 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 289946887) ^ 18121680 = 164196251 := by
        calc
          (3 : ZMod 289946887) ^ 18121680 = (3 : ZMod 289946887) ^ (9060840 + 9060840) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 9060840 * (3 : ZMod 289946887) ^ 9060840 := by rw [pow_add]
          _ = 164196251 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 289946887) ^ 36243360 = 259310029 := by
        calc
          (3 : ZMod 289946887) ^ 36243360 = (3 : ZMod 289946887) ^ (18121680 + 18121680) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 18121680 * (3 : ZMod 289946887) ^ 18121680 := by rw [pow_add]
          _ = 259310029 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 289946887) ^ 72486721 = 117078422 := by
        calc
          (3 : ZMod 289946887) ^ 72486721 = (3 : ZMod 289946887) ^ (36243360 + 36243360 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 36243360 * (3 : ZMod 289946887) ^ 36243360) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 117078422 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 289946887) ^ 144973443 = 289946886 := by
        calc
          (3 : ZMod 289946887) ^ 144973443 = (3 : ZMod 289946887) ^ (72486721 + 72486721 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 72486721 * (3 : ZMod 289946887) ^ 72486721) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 289946886 := by rw [factor_0_26]; decide
      change (3 : ZMod 289946887) ^ 144973443 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (3 : ZMod 289946887) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 289946887) ^ 2 = 9 := by
        calc
          (3 : ZMod 289946887) ^ 2 = (3 : ZMod 289946887) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 1 * (3 : ZMod 289946887) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 289946887) ^ 5 = 243 := by
        calc
          (3 : ZMod 289946887) ^ 5 = (3 : ZMod 289946887) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 2 * (3 : ZMod 289946887) ^ 2) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 289946887) ^ 11 = 177147 := by
        calc
          (3 : ZMod 289946887) ^ 11 = (3 : ZMod 289946887) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 5 * (3 : ZMod 289946887) ^ 5) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 289946887) ^ 23 = 200387439 := by
        calc
          (3 : ZMod 289946887) ^ 23 = (3 : ZMod 289946887) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 11 * (3 : ZMod 289946887) ^ 11) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 200387439 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 289946887) ^ 46 = 48192316 := by
        calc
          (3 : ZMod 289946887) ^ 46 = (3 : ZMod 289946887) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 23 * (3 : ZMod 289946887) ^ 23 := by rw [pow_add]
          _ = 48192316 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 289946887) ^ 92 = 111088461 := by
        calc
          (3 : ZMod 289946887) ^ 92 = (3 : ZMod 289946887) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 46 * (3 : ZMod 289946887) ^ 46 := by rw [pow_add]
          _ = 111088461 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 289946887) ^ 184 = 119416932 := by
        calc
          (3 : ZMod 289946887) ^ 184 = (3 : ZMod 289946887) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 92 * (3 : ZMod 289946887) ^ 92 := by rw [pow_add]
          _ = 119416932 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 289946887) ^ 368 = 125039493 := by
        calc
          (3 : ZMod 289946887) ^ 368 = (3 : ZMod 289946887) ^ (184 + 184) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 184 * (3 : ZMod 289946887) ^ 184 := by rw [pow_add]
          _ = 125039493 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 289946887) ^ 737 = 23804603 := by
        calc
          (3 : ZMod 289946887) ^ 737 = (3 : ZMod 289946887) ^ (368 + 368 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 368 * (3 : ZMod 289946887) ^ 368) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 23804603 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 289946887) ^ 1474 = 265591611 := by
        calc
          (3 : ZMod 289946887) ^ 1474 = (3 : ZMod 289946887) ^ (737 + 737) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 737 * (3 : ZMod 289946887) ^ 737 := by rw [pow_add]
          _ = 265591611 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 289946887) ^ 2949 = 116180847 := by
        calc
          (3 : ZMod 289946887) ^ 2949 = (3 : ZMod 289946887) ^ (1474 + 1474 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 1474 * (3 : ZMod 289946887) ^ 1474) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 116180847 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 289946887) ^ 5898 = 155910117 := by
        calc
          (3 : ZMod 289946887) ^ 5898 = (3 : ZMod 289946887) ^ (2949 + 2949) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 2949 * (3 : ZMod 289946887) ^ 2949 := by rw [pow_add]
          _ = 155910117 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 289946887) ^ 11797 = 230783512 := by
        calc
          (3 : ZMod 289946887) ^ 11797 = (3 : ZMod 289946887) ^ (5898 + 5898 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 5898 * (3 : ZMod 289946887) ^ 5898) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 230783512 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 289946887) ^ 23595 = 40909167 := by
        calc
          (3 : ZMod 289946887) ^ 23595 = (3 : ZMod 289946887) ^ (11797 + 11797 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 11797 * (3 : ZMod 289946887) ^ 11797) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 40909167 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 289946887) ^ 47191 = 131173847 := by
        calc
          (3 : ZMod 289946887) ^ 47191 = (3 : ZMod 289946887) ^ (23595 + 23595 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 23595 * (3 : ZMod 289946887) ^ 23595) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 131173847 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 289946887) ^ 94383 = 107489197 := by
        calc
          (3 : ZMod 289946887) ^ 94383 = (3 : ZMod 289946887) ^ (47191 + 47191 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 47191 * (3 : ZMod 289946887) ^ 47191) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 107489197 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 289946887) ^ 188767 = 43677293 := by
        calc
          (3 : ZMod 289946887) ^ 188767 = (3 : ZMod 289946887) ^ (94383 + 94383 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 94383 * (3 : ZMod 289946887) ^ 94383) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 43677293 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 289946887) ^ 377535 = 272533386 := by
        calc
          (3 : ZMod 289946887) ^ 377535 = (3 : ZMod 289946887) ^ (188767 + 188767 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 188767 * (3 : ZMod 289946887) ^ 188767) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 272533386 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 289946887) ^ 755070 = 83289757 := by
        calc
          (3 : ZMod 289946887) ^ 755070 = (3 : ZMod 289946887) ^ (377535 + 377535) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 377535 * (3 : ZMod 289946887) ^ 377535 := by rw [pow_add]
          _ = 83289757 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 289946887) ^ 1510140 = 227035601 := by
        calc
          (3 : ZMod 289946887) ^ 1510140 = (3 : ZMod 289946887) ^ (755070 + 755070) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 755070 * (3 : ZMod 289946887) ^ 755070 := by rw [pow_add]
          _ = 227035601 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 289946887) ^ 3020280 = 98662153 := by
        calc
          (3 : ZMod 289946887) ^ 3020280 = (3 : ZMod 289946887) ^ (1510140 + 1510140) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 1510140 * (3 : ZMod 289946887) ^ 1510140 := by rw [pow_add]
          _ = 98662153 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 289946887) ^ 6040560 = 26857547 := by
        calc
          (3 : ZMod 289946887) ^ 6040560 = (3 : ZMod 289946887) ^ (3020280 + 3020280) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 3020280 * (3 : ZMod 289946887) ^ 3020280 := by rw [pow_add]
          _ = 26857547 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 289946887) ^ 12081120 = 284953705 := by
        calc
          (3 : ZMod 289946887) ^ 12081120 = (3 : ZMod 289946887) ^ (6040560 + 6040560) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 6040560 * (3 : ZMod 289946887) ^ 6040560 := by rw [pow_add]
          _ = 284953705 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 289946887) ^ 24162240 = 203512655 := by
        calc
          (3 : ZMod 289946887) ^ 24162240 = (3 : ZMod 289946887) ^ (12081120 + 12081120) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 12081120 * (3 : ZMod 289946887) ^ 12081120 := by rw [pow_add]
          _ = 203512655 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 289946887) ^ 48324481 = 30644190 := by
        calc
          (3 : ZMod 289946887) ^ 48324481 = (3 : ZMod 289946887) ^ (24162240 + 24162240 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 24162240 * (3 : ZMod 289946887) ^ 24162240) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 30644190 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 289946887) ^ 96648962 = 30644189 := by
        calc
          (3 : ZMod 289946887) ^ 96648962 = (3 : ZMod 289946887) ^ (48324481 + 48324481) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 48324481 * (3 : ZMod 289946887) ^ 48324481 := by rw [pow_add]
          _ = 30644189 := by rw [factor_1_25]; decide
      change (3 : ZMod 289946887) ^ 96648962 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (3 : ZMod 289946887) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 289946887) ^ 2 = 9 := by
        calc
          (3 : ZMod 289946887) ^ 2 = (3 : ZMod 289946887) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 1 * (3 : ZMod 289946887) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 289946887) ^ 4 = 81 := by
        calc
          (3 : ZMod 289946887) ^ 4 = (3 : ZMod 289946887) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 2 * (3 : ZMod 289946887) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 289946887) ^ 9 = 19683 := by
        calc
          (3 : ZMod 289946887) ^ 9 = (3 : ZMod 289946887) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 4 * (3 : ZMod 289946887) ^ 4) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 289946887) ^ 18 = 97473602 := by
        calc
          (3 : ZMod 289946887) ^ 18 = (3 : ZMod 289946887) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 9 * (3 : ZMod 289946887) ^ 9 := by rw [pow_add]
          _ = 97473602 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 289946887) ^ 37 = 218740513 := by
        calc
          (3 : ZMod 289946887) ^ 37 = (3 : ZMod 289946887) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 18 * (3 : ZMod 289946887) ^ 18) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 218740513 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 289946887) ^ 74 = 93756956 := by
        calc
          (3 : ZMod 289946887) ^ 74 = (3 : ZMod 289946887) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 37 * (3 : ZMod 289946887) ^ 37 := by rw [pow_add]
          _ = 93756956 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 289946887) ^ 149 = 161433726 := by
        calc
          (3 : ZMod 289946887) ^ 149 = (3 : ZMod 289946887) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 74 * (3 : ZMod 289946887) ^ 74) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 161433726 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 289946887) ^ 299 = 21781247 := by
        calc
          (3 : ZMod 289946887) ^ 299 = (3 : ZMod 289946887) ^ (149 + 149 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 149 * (3 : ZMod 289946887) ^ 149) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 21781247 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 289946887) ^ 599 = 79470387 := by
        calc
          (3 : ZMod 289946887) ^ 599 = (3 : ZMod 289946887) ^ (299 + 299 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 299 * (3 : ZMod 289946887) ^ 299) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 79470387 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 289946887) ^ 1199 = 57537952 := by
        calc
          (3 : ZMod 289946887) ^ 1199 = (3 : ZMod 289946887) ^ (599 + 599 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 599 * (3 : ZMod 289946887) ^ 599) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 57537952 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 289946887) ^ 2399 = 135039624 := by
        calc
          (3 : ZMod 289946887) ^ 2399 = (3 : ZMod 289946887) ^ (1199 + 1199 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 1199 * (3 : ZMod 289946887) ^ 1199) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 135039624 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 289946887) ^ 4799 = 86630505 := by
        calc
          (3 : ZMod 289946887) ^ 4799 = (3 : ZMod 289946887) ^ (2399 + 2399 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 2399 * (3 : ZMod 289946887) ^ 2399) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 86630505 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 289946887) ^ 9598 = 87634107 := by
        calc
          (3 : ZMod 289946887) ^ 9598 = (3 : ZMod 289946887) ^ (4799 + 4799) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 4799 * (3 : ZMod 289946887) ^ 4799 := by rw [pow_add]
          _ = 87634107 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 289946887) ^ 19196 = 207837662 := by
        calc
          (3 : ZMod 289946887) ^ 19196 = (3 : ZMod 289946887) ^ (9598 + 9598) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 9598 * (3 : ZMod 289946887) ^ 9598 := by rw [pow_add]
          _ = 207837662 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 289946887) ^ 38393 = 234548100 := by
        calc
          (3 : ZMod 289946887) ^ 38393 = (3 : ZMod 289946887) ^ (19196 + 19196 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 19196 * (3 : ZMod 289946887) ^ 19196) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 234548100 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 289946887) ^ 76786 = 140757074 := by
        calc
          (3 : ZMod 289946887) ^ 76786 = (3 : ZMod 289946887) ^ (38393 + 38393) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 38393 * (3 : ZMod 289946887) ^ 38393 := by rw [pow_add]
          _ = 140757074 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 289946887) ^ 153573 = 122453202 := by
        calc
          (3 : ZMod 289946887) ^ 153573 = (3 : ZMod 289946887) ^ (76786 + 76786 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 76786 * (3 : ZMod 289946887) ^ 76786) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 122453202 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 289946887) ^ 307147 = 227298773 := by
        calc
          (3 : ZMod 289946887) ^ 307147 = (3 : ZMod 289946887) ^ (153573 + 153573 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 153573 * (3 : ZMod 289946887) ^ 153573) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 227298773 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 289946887) ^ 614294 = 177222308 := by
        calc
          (3 : ZMod 289946887) ^ 614294 = (3 : ZMod 289946887) ^ (307147 + 307147) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 307147 * (3 : ZMod 289946887) ^ 307147 := by rw [pow_add]
          _ = 177222308 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 289946887) ^ 1228588 = 11168533 := by
        calc
          (3 : ZMod 289946887) ^ 1228588 = (3 : ZMod 289946887) ^ (614294 + 614294) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 614294 * (3 : ZMod 289946887) ^ 614294 := by rw [pow_add]
          _ = 11168533 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 289946887) ^ 2457177 = 36285197 := by
        calc
          (3 : ZMod 289946887) ^ 2457177 = (3 : ZMod 289946887) ^ (1228588 + 1228588 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 1228588 * (3 : ZMod 289946887) ^ 1228588) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 36285197 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 289946887) ^ 4914354 = 51353814 := by
        calc
          (3 : ZMod 289946887) ^ 4914354 = (3 : ZMod 289946887) ^ (2457177 + 2457177) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 2457177 * (3 : ZMod 289946887) ^ 2457177 := by rw [pow_add]
          _ = 51353814 := by rw [factor_2_21]; decide
      change (3 : ZMod 289946887) ^ 4914354 ≠ 1
      rw [factor_2_22]
      decide
    ·
      have factor_3_0 : (3 : ZMod 289946887) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 289946887) ^ 2 = 9 := by
        calc
          (3 : ZMod 289946887) ^ 2 = (3 : ZMod 289946887) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 1 * (3 : ZMod 289946887) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 289946887) ^ 4 = 81 := by
        calc
          (3 : ZMod 289946887) ^ 4 = (3 : ZMod 289946887) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 2 * (3 : ZMod 289946887) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 289946887) ^ 8 = 6561 := by
        calc
          (3 : ZMod 289946887) ^ 8 = (3 : ZMod 289946887) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 4 * (3 : ZMod 289946887) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 289946887) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 289946887) ^ 17 = (3 : ZMod 289946887) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 8 * (3 : ZMod 289946887) ^ 8) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 289946887) ^ 34 = 126228010 := by
        calc
          (3 : ZMod 289946887) ^ 34 = (3 : ZMod 289946887) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 17 * (3 : ZMod 289946887) ^ 17 := by rw [pow_add]
          _ = 126228010 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 289946887) ^ 68 = 78084152 := by
        calc
          (3 : ZMod 289946887) ^ 68 = (3 : ZMod 289946887) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 34 * (3 : ZMod 289946887) ^ 34 := by rw [pow_add]
          _ = 78084152 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 289946887) ^ 137 = 53509218 := by
        calc
          (3 : ZMod 289946887) ^ 137 = (3 : ZMod 289946887) ^ (68 + 68 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 68 * (3 : ZMod 289946887) ^ 68) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 53509218 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 289946887) ^ 275 = 231488228 := by
        calc
          (3 : ZMod 289946887) ^ 275 = (3 : ZMod 289946887) ^ (137 + 137 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 137 * (3 : ZMod 289946887) ^ 137) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 231488228 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 289946887) ^ 550 = 190326492 := by
        calc
          (3 : ZMod 289946887) ^ 550 = (3 : ZMod 289946887) ^ (275 + 275) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 275 * (3 : ZMod 289946887) ^ 275 := by rw [pow_add]
          _ = 190326492 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 289946887) ^ 1101 = 41766754 := by
        calc
          (3 : ZMod 289946887) ^ 1101 = (3 : ZMod 289946887) ^ (550 + 550 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 550 * (3 : ZMod 289946887) ^ 550) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 41766754 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 289946887) ^ 2203 = 190111641 := by
        calc
          (3 : ZMod 289946887) ^ 2203 = (3 : ZMod 289946887) ^ (1101 + 1101 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 1101 * (3 : ZMod 289946887) ^ 1101) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 190111641 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 289946887) ^ 4407 = 223313297 := by
        calc
          (3 : ZMod 289946887) ^ 4407 = (3 : ZMod 289946887) ^ (2203 + 2203 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 2203 * (3 : ZMod 289946887) ^ 2203) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 223313297 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 289946887) ^ 8814 = 60050723 := by
        calc
          (3 : ZMod 289946887) ^ 8814 = (3 : ZMod 289946887) ^ (4407 + 4407) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 4407 * (3 : ZMod 289946887) ^ 4407 := by rw [pow_add]
          _ = 60050723 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 289946887) ^ 17628 = 182815413 := by
        calc
          (3 : ZMod 289946887) ^ 17628 = (3 : ZMod 289946887) ^ (8814 + 8814) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 8814 * (3 : ZMod 289946887) ^ 8814 := by rw [pow_add]
          _ = 182815413 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 289946887) ^ 35256 = 107177770 := by
        calc
          (3 : ZMod 289946887) ^ 35256 = (3 : ZMod 289946887) ^ (17628 + 17628) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 17628 * (3 : ZMod 289946887) ^ 17628 := by rw [pow_add]
          _ = 107177770 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 289946887) ^ 70512 = 75411741 := by
        calc
          (3 : ZMod 289946887) ^ 70512 = (3 : ZMod 289946887) ^ (35256 + 35256) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 35256 * (3 : ZMod 289946887) ^ 35256 := by rw [pow_add]
          _ = 75411741 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 289946887) ^ 141024 = 2992955 := by
        calc
          (3 : ZMod 289946887) ^ 141024 = (3 : ZMod 289946887) ^ (70512 + 70512) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 70512 * (3 : ZMod 289946887) ^ 70512 := by rw [pow_add]
          _ = 2992955 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 289946887) ^ 282049 = 191568254 := by
        calc
          (3 : ZMod 289946887) ^ 282049 = (3 : ZMod 289946887) ^ (141024 + 141024 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 141024 * (3 : ZMod 289946887) ^ 141024) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 191568254 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 289946887) ^ 564099 = 169256221 := by
        calc
          (3 : ZMod 289946887) ^ 564099 = (3 : ZMod 289946887) ^ (282049 + 282049 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 282049 * (3 : ZMod 289946887) ^ 282049) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 169256221 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 289946887) ^ 1128198 = 259331695 := by
        calc
          (3 : ZMod 289946887) ^ 1128198 = (3 : ZMod 289946887) ^ (564099 + 564099) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 564099 * (3 : ZMod 289946887) ^ 564099 := by rw [pow_add]
          _ = 259331695 := by rw [factor_3_19]; decide
      change (3 : ZMod 289946887) ^ 1128198 ≠ 1
      rw [factor_3_20]
      decide
    ·
      have factor_4_0 : (3 : ZMod 289946887) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 289946887) ^ 2 = 9 := by
        calc
          (3 : ZMod 289946887) ^ 2 = (3 : ZMod 289946887) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 1 * (3 : ZMod 289946887) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 289946887) ^ 5 = 243 := by
        calc
          (3 : ZMod 289946887) ^ 5 = (3 : ZMod 289946887) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 2 * (3 : ZMod 289946887) ^ 2) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 289946887) ^ 11 = 177147 := by
        calc
          (3 : ZMod 289946887) ^ 11 = (3 : ZMod 289946887) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 5 * (3 : ZMod 289946887) ^ 5) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 289946887) ^ 22 = 66795813 := by
        calc
          (3 : ZMod 289946887) ^ 22 = (3 : ZMod 289946887) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 11 * (3 : ZMod 289946887) ^ 11 := by rw [pow_add]
          _ = 66795813 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 289946887) ^ 44 = 263085268 := by
        calc
          (3 : ZMod 289946887) ^ 44 = (3 : ZMod 289946887) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 22 * (3 : ZMod 289946887) ^ 22 := by rw [pow_add]
          _ = 263085268 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 289946887) ^ 88 = 119497972 := by
        calc
          (3 : ZMod 289946887) ^ 88 = (3 : ZMod 289946887) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 44 * (3 : ZMod 289946887) ^ 44 := by rw [pow_add]
          _ = 119497972 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 289946887) ^ 177 = 16759362 := by
        calc
          (3 : ZMod 289946887) ^ 177 = (3 : ZMod 289946887) ^ (88 + 88 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 88 * (3 : ZMod 289946887) ^ 88) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 16759362 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 289946887) ^ 355 = 78179856 := by
        calc
          (3 : ZMod 289946887) ^ 355 = (3 : ZMod 289946887) ^ (177 + 177 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 177 * (3 : ZMod 289946887) ^ 177) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 78179856 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 289946887) ^ 710 = 227920352 := by
        calc
          (3 : ZMod 289946887) ^ 710 = (3 : ZMod 289946887) ^ (355 + 355) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 355 * (3 : ZMod 289946887) ^ 355 := by rw [pow_add]
          _ = 227920352 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 289946887) ^ 1421 = 23702064 := by
        calc
          (3 : ZMod 289946887) ^ 1421 = (3 : ZMod 289946887) ^ (710 + 710 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 710 * (3 : ZMod 289946887) ^ 710) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 23702064 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 289946887) ^ 2843 = 261497094 := by
        calc
          (3 : ZMod 289946887) ^ 2843 = (3 : ZMod 289946887) ^ (1421 + 1421 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 1421 * (3 : ZMod 289946887) ^ 1421) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 261497094 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 289946887) ^ 5686 = 217372818 := by
        calc
          (3 : ZMod 289946887) ^ 5686 = (3 : ZMod 289946887) ^ (2843 + 2843) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 2843 * (3 : ZMod 289946887) ^ 2843 := by rw [pow_add]
          _ = 217372818 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 289946887) ^ 11372 = 109044701 := by
        calc
          (3 : ZMod 289946887) ^ 11372 = (3 : ZMod 289946887) ^ (5686 + 5686) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 5686 * (3 : ZMod 289946887) ^ 5686 := by rw [pow_add]
          _ = 109044701 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 289946887) ^ 22744 = 44877119 := by
        calc
          (3 : ZMod 289946887) ^ 22744 = (3 : ZMod 289946887) ^ (11372 + 11372) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 11372 * (3 : ZMod 289946887) ^ 11372 := by rw [pow_add]
          _ = 44877119 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 289946887) ^ 45489 = 9522629 := by
        calc
          (3 : ZMod 289946887) ^ 45489 = (3 : ZMod 289946887) ^ (22744 + 22744 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = ((3 : ZMod 289946887) ^ 22744 * (3 : ZMod 289946887) ^ 22744) * (3 : ZMod 289946887) := by rw [pow_succ, pow_add]
          _ = 9522629 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 289946887) ^ 90978 = 154056165 := by
        calc
          (3 : ZMod 289946887) ^ 90978 = (3 : ZMod 289946887) ^ (45489 + 45489) :=
            congrArg (fun n : ℕ => (3 : ZMod 289946887) ^ n) (by norm_num)
          _ = (3 : ZMod 289946887) ^ 45489 * (3 : ZMod 289946887) ^ 45489 := by rw [pow_add]
          _ = 154056165 := by rw [factor_4_15]; decide
      change (3 : ZMod 289946887) ^ 90978 ≠ 1
      rw [factor_4_16]
      decide

#print axioms prime_lucas_289946887

end TotientTailPeriodKiller
end Erdos249257
