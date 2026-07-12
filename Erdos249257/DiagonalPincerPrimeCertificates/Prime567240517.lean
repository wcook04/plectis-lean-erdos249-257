import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_567240517 : Nat.Prime 567240517 := by
  apply lucas_primality 567240517 (5 : ZMod 567240517)
  ·
      have fermat_0 : (5 : ZMod 567240517) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 567240517) ^ 2 = 25 := by
        calc
          (5 : ZMod 567240517) ^ 2 = (5 : ZMod 567240517) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 1 * (5 : ZMod 567240517) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 567240517) ^ 4 = 625 := by
        calc
          (5 : ZMod 567240517) ^ 4 = (5 : ZMod 567240517) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 2 * (5 : ZMod 567240517) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 567240517) ^ 8 = 390625 := by
        calc
          (5 : ZMod 567240517) ^ 8 = (5 : ZMod 567240517) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 4 * (5 : ZMod 567240517) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 567240517) ^ 16 = 191552 := by
        calc
          (5 : ZMod 567240517) ^ 16 = (5 : ZMod 567240517) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 8 * (5 : ZMod 567240517) ^ 8 := by rw [pow_add]
          _ = 191552 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 567240517) ^ 33 = 242156529 := by
        calc
          (5 : ZMod 567240517) ^ 33 = (5 : ZMod 567240517) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 16 * (5 : ZMod 567240517) ^ 16) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 242156529 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 567240517) ^ 67 = 306597997 := by
        calc
          (5 : ZMod 567240517) ^ 67 = (5 : ZMod 567240517) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 33 * (5 : ZMod 567240517) ^ 33) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 306597997 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 567240517) ^ 135 = 414514448 := by
        calc
          (5 : ZMod 567240517) ^ 135 = (5 : ZMod 567240517) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 67 * (5 : ZMod 567240517) ^ 67) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 414514448 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 567240517) ^ 270 = 467779622 := by
        calc
          (5 : ZMod 567240517) ^ 270 = (5 : ZMod 567240517) ^ (135 + 135) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 135 * (5 : ZMod 567240517) ^ 135 := by rw [pow_add]
          _ = 467779622 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 567240517) ^ 540 = 358788179 := by
        calc
          (5 : ZMod 567240517) ^ 540 = (5 : ZMod 567240517) ^ (270 + 270) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 270 * (5 : ZMod 567240517) ^ 270 := by rw [pow_add]
          _ = 358788179 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 567240517) ^ 1081 = 240659951 := by
        calc
          (5 : ZMod 567240517) ^ 1081 = (5 : ZMod 567240517) ^ (540 + 540 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 540 * (5 : ZMod 567240517) ^ 540) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 240659951 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 567240517) ^ 2163 = 325042027 := by
        calc
          (5 : ZMod 567240517) ^ 2163 = (5 : ZMod 567240517) ^ (1081 + 1081 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 1081 * (5 : ZMod 567240517) ^ 1081) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 325042027 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 567240517) ^ 4327 = 407219776 := by
        calc
          (5 : ZMod 567240517) ^ 4327 = (5 : ZMod 567240517) ^ (2163 + 2163 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 2163 * (5 : ZMod 567240517) ^ 2163) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 407219776 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 567240517) ^ 8655 = 479863040 := by
        calc
          (5 : ZMod 567240517) ^ 8655 = (5 : ZMod 567240517) ^ (4327 + 4327 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 4327 * (5 : ZMod 567240517) ^ 4327) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 479863040 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 567240517) ^ 17310 = 398399050 := by
        calc
          (5 : ZMod 567240517) ^ 17310 = (5 : ZMod 567240517) ^ (8655 + 8655) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 8655 * (5 : ZMod 567240517) ^ 8655 := by rw [pow_add]
          _ = 398399050 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 567240517) ^ 34621 = 362642253 := by
        calc
          (5 : ZMod 567240517) ^ 34621 = (5 : ZMod 567240517) ^ (17310 + 17310 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 17310 * (5 : ZMod 567240517) ^ 17310) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 362642253 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 567240517) ^ 69243 = 366449781 := by
        calc
          (5 : ZMod 567240517) ^ 69243 = (5 : ZMod 567240517) ^ (34621 + 34621 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 34621 * (5 : ZMod 567240517) ^ 34621) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 366449781 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 567240517) ^ 138486 = 414653720 := by
        calc
          (5 : ZMod 567240517) ^ 138486 = (5 : ZMod 567240517) ^ (69243 + 69243) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 69243 * (5 : ZMod 567240517) ^ 69243 := by rw [pow_add]
          _ = 414653720 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 567240517) ^ 276972 = 417941424 := by
        calc
          (5 : ZMod 567240517) ^ 276972 = (5 : ZMod 567240517) ^ (138486 + 138486) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 138486 * (5 : ZMod 567240517) ^ 138486 := by rw [pow_add]
          _ = 417941424 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 567240517) ^ 553945 = 131085867 := by
        calc
          (5 : ZMod 567240517) ^ 553945 = (5 : ZMod 567240517) ^ (276972 + 276972 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 276972 * (5 : ZMod 567240517) ^ 276972) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 131085867 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 567240517) ^ 1107891 = 385864838 := by
        calc
          (5 : ZMod 567240517) ^ 1107891 = (5 : ZMod 567240517) ^ (553945 + 553945 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 553945 * (5 : ZMod 567240517) ^ 553945) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 385864838 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 567240517) ^ 2215783 = 29414737 := by
        calc
          (5 : ZMod 567240517) ^ 2215783 = (5 : ZMod 567240517) ^ (1107891 + 1107891 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 1107891 * (5 : ZMod 567240517) ^ 1107891) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 29414737 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 567240517) ^ 4431566 = 43945627 := by
        calc
          (5 : ZMod 567240517) ^ 4431566 = (5 : ZMod 567240517) ^ (2215783 + 2215783) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 2215783 * (5 : ZMod 567240517) ^ 2215783 := by rw [pow_add]
          _ = 43945627 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 567240517) ^ 8863133 = 153225488 := by
        calc
          (5 : ZMod 567240517) ^ 8863133 = (5 : ZMod 567240517) ^ (4431566 + 4431566 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 4431566 * (5 : ZMod 567240517) ^ 4431566) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 153225488 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 567240517) ^ 17726266 = 343120198 := by
        calc
          (5 : ZMod 567240517) ^ 17726266 = (5 : ZMod 567240517) ^ (8863133 + 8863133) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 8863133 * (5 : ZMod 567240517) ^ 8863133 := by rw [pow_add]
          _ = 343120198 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 567240517) ^ 35452532 = 430170709 := by
        calc
          (5 : ZMod 567240517) ^ 35452532 = (5 : ZMod 567240517) ^ (17726266 + 17726266) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 17726266 * (5 : ZMod 567240517) ^ 17726266 := by rw [pow_add]
          _ = 430170709 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 567240517) ^ 70905064 = 369690619 := by
        calc
          (5 : ZMod 567240517) ^ 70905064 = (5 : ZMod 567240517) ^ (35452532 + 35452532) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 35452532 * (5 : ZMod 567240517) ^ 35452532 := by rw [pow_add]
          _ = 369690619 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 567240517) ^ 141810129 = 22056798 := by
        calc
          (5 : ZMod 567240517) ^ 141810129 = (5 : ZMod 567240517) ^ (70905064 + 70905064 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 70905064 * (5 : ZMod 567240517) ^ 70905064) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 22056798 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 567240517) ^ 283620258 = 567240516 := by
        calc
          (5 : ZMod 567240517) ^ 283620258 = (5 : ZMod 567240517) ^ (141810129 + 141810129) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 141810129 * (5 : ZMod 567240517) ^ 141810129 := by rw [pow_add]
          _ = 567240516 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 567240517) ^ 567240516 = 1 := by
        calc
          (5 : ZMod 567240517) ^ 567240516 = (5 : ZMod 567240517) ^ (283620258 + 283620258) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 283620258 * (5 : ZMod 567240517) ^ 283620258 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (19, 1), (491, 1), (563, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (19, 1), (491, 1), (563, 1)] : List FactorBlock).map factorBlockValue).prod = 567240517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 567240517) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 567240517) ^ 2 = 25 := by
        calc
          (5 : ZMod 567240517) ^ 2 = (5 : ZMod 567240517) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 1 * (5 : ZMod 567240517) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 567240517) ^ 4 = 625 := by
        calc
          (5 : ZMod 567240517) ^ 4 = (5 : ZMod 567240517) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 2 * (5 : ZMod 567240517) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 567240517) ^ 8 = 390625 := by
        calc
          (5 : ZMod 567240517) ^ 8 = (5 : ZMod 567240517) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 4 * (5 : ZMod 567240517) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 567240517) ^ 16 = 191552 := by
        calc
          (5 : ZMod 567240517) ^ 16 = (5 : ZMod 567240517) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 8 * (5 : ZMod 567240517) ^ 8 := by rw [pow_add]
          _ = 191552 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 567240517) ^ 33 = 242156529 := by
        calc
          (5 : ZMod 567240517) ^ 33 = (5 : ZMod 567240517) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 16 * (5 : ZMod 567240517) ^ 16) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 242156529 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 567240517) ^ 67 = 306597997 := by
        calc
          (5 : ZMod 567240517) ^ 67 = (5 : ZMod 567240517) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 33 * (5 : ZMod 567240517) ^ 33) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 306597997 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 567240517) ^ 135 = 414514448 := by
        calc
          (5 : ZMod 567240517) ^ 135 = (5 : ZMod 567240517) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 67 * (5 : ZMod 567240517) ^ 67) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 414514448 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 567240517) ^ 270 = 467779622 := by
        calc
          (5 : ZMod 567240517) ^ 270 = (5 : ZMod 567240517) ^ (135 + 135) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 135 * (5 : ZMod 567240517) ^ 135 := by rw [pow_add]
          _ = 467779622 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 567240517) ^ 540 = 358788179 := by
        calc
          (5 : ZMod 567240517) ^ 540 = (5 : ZMod 567240517) ^ (270 + 270) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 270 * (5 : ZMod 567240517) ^ 270 := by rw [pow_add]
          _ = 358788179 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 567240517) ^ 1081 = 240659951 := by
        calc
          (5 : ZMod 567240517) ^ 1081 = (5 : ZMod 567240517) ^ (540 + 540 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 540 * (5 : ZMod 567240517) ^ 540) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 240659951 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 567240517) ^ 2163 = 325042027 := by
        calc
          (5 : ZMod 567240517) ^ 2163 = (5 : ZMod 567240517) ^ (1081 + 1081 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 1081 * (5 : ZMod 567240517) ^ 1081) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 325042027 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 567240517) ^ 4327 = 407219776 := by
        calc
          (5 : ZMod 567240517) ^ 4327 = (5 : ZMod 567240517) ^ (2163 + 2163 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 2163 * (5 : ZMod 567240517) ^ 2163) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 407219776 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 567240517) ^ 8655 = 479863040 := by
        calc
          (5 : ZMod 567240517) ^ 8655 = (5 : ZMod 567240517) ^ (4327 + 4327 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 4327 * (5 : ZMod 567240517) ^ 4327) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 479863040 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 567240517) ^ 17310 = 398399050 := by
        calc
          (5 : ZMod 567240517) ^ 17310 = (5 : ZMod 567240517) ^ (8655 + 8655) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 8655 * (5 : ZMod 567240517) ^ 8655 := by rw [pow_add]
          _ = 398399050 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 567240517) ^ 34621 = 362642253 := by
        calc
          (5 : ZMod 567240517) ^ 34621 = (5 : ZMod 567240517) ^ (17310 + 17310 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 17310 * (5 : ZMod 567240517) ^ 17310) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 362642253 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 567240517) ^ 69243 = 366449781 := by
        calc
          (5 : ZMod 567240517) ^ 69243 = (5 : ZMod 567240517) ^ (34621 + 34621 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 34621 * (5 : ZMod 567240517) ^ 34621) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 366449781 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 567240517) ^ 138486 = 414653720 := by
        calc
          (5 : ZMod 567240517) ^ 138486 = (5 : ZMod 567240517) ^ (69243 + 69243) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 69243 * (5 : ZMod 567240517) ^ 69243 := by rw [pow_add]
          _ = 414653720 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 567240517) ^ 276972 = 417941424 := by
        calc
          (5 : ZMod 567240517) ^ 276972 = (5 : ZMod 567240517) ^ (138486 + 138486) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 138486 * (5 : ZMod 567240517) ^ 138486 := by rw [pow_add]
          _ = 417941424 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 567240517) ^ 553945 = 131085867 := by
        calc
          (5 : ZMod 567240517) ^ 553945 = (5 : ZMod 567240517) ^ (276972 + 276972 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 276972 * (5 : ZMod 567240517) ^ 276972) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 131085867 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 567240517) ^ 1107891 = 385864838 := by
        calc
          (5 : ZMod 567240517) ^ 1107891 = (5 : ZMod 567240517) ^ (553945 + 553945 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 553945 * (5 : ZMod 567240517) ^ 553945) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 385864838 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 567240517) ^ 2215783 = 29414737 := by
        calc
          (5 : ZMod 567240517) ^ 2215783 = (5 : ZMod 567240517) ^ (1107891 + 1107891 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 1107891 * (5 : ZMod 567240517) ^ 1107891) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 29414737 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 567240517) ^ 4431566 = 43945627 := by
        calc
          (5 : ZMod 567240517) ^ 4431566 = (5 : ZMod 567240517) ^ (2215783 + 2215783) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 2215783 * (5 : ZMod 567240517) ^ 2215783 := by rw [pow_add]
          _ = 43945627 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 567240517) ^ 8863133 = 153225488 := by
        calc
          (5 : ZMod 567240517) ^ 8863133 = (5 : ZMod 567240517) ^ (4431566 + 4431566 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 4431566 * (5 : ZMod 567240517) ^ 4431566) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 153225488 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 567240517) ^ 17726266 = 343120198 := by
        calc
          (5 : ZMod 567240517) ^ 17726266 = (5 : ZMod 567240517) ^ (8863133 + 8863133) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 8863133 * (5 : ZMod 567240517) ^ 8863133 := by rw [pow_add]
          _ = 343120198 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 567240517) ^ 35452532 = 430170709 := by
        calc
          (5 : ZMod 567240517) ^ 35452532 = (5 : ZMod 567240517) ^ (17726266 + 17726266) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 17726266 * (5 : ZMod 567240517) ^ 17726266 := by rw [pow_add]
          _ = 430170709 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 567240517) ^ 70905064 = 369690619 := by
        calc
          (5 : ZMod 567240517) ^ 70905064 = (5 : ZMod 567240517) ^ (35452532 + 35452532) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 35452532 * (5 : ZMod 567240517) ^ 35452532 := by rw [pow_add]
          _ = 369690619 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 567240517) ^ 141810129 = 22056798 := by
        calc
          (5 : ZMod 567240517) ^ 141810129 = (5 : ZMod 567240517) ^ (70905064 + 70905064 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 70905064 * (5 : ZMod 567240517) ^ 70905064) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 22056798 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 567240517) ^ 283620258 = 567240516 := by
        calc
          (5 : ZMod 567240517) ^ 283620258 = (5 : ZMod 567240517) ^ (141810129 + 141810129) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 141810129 * (5 : ZMod 567240517) ^ 141810129 := by rw [pow_add]
          _ = 567240516 := by rw [factor_0_27]; decide
      change (5 : ZMod 567240517) ^ 283620258 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (5 : ZMod 567240517) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 567240517) ^ 2 = 25 := by
        calc
          (5 : ZMod 567240517) ^ 2 = (5 : ZMod 567240517) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 1 * (5 : ZMod 567240517) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 567240517) ^ 5 = 3125 := by
        calc
          (5 : ZMod 567240517) ^ 5 = (5 : ZMod 567240517) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 2 * (5 : ZMod 567240517) ^ 2) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 567240517) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 567240517) ^ 11 = (5 : ZMod 567240517) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 5 * (5 : ZMod 567240517) ^ 5) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 567240517) ^ 22 = 156797415 := by
        calc
          (5 : ZMod 567240517) ^ 22 = (5 : ZMod 567240517) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 11 * (5 : ZMod 567240517) ^ 11 := by rw [pow_add]
          _ = 156797415 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 567240517) ^ 45 = 521927525 := by
        calc
          (5 : ZMod 567240517) ^ 45 = (5 : ZMod 567240517) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 22 * (5 : ZMod 567240517) ^ 22) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 521927525 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 567240517) ^ 90 = 84302865 := by
        calc
          (5 : ZMod 567240517) ^ 90 = (5 : ZMod 567240517) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 45 * (5 : ZMod 567240517) ^ 45 := by rw [pow_add]
          _ = 84302865 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 567240517) ^ 180 = 159740232 := by
        calc
          (5 : ZMod 567240517) ^ 180 = (5 : ZMod 567240517) ^ (90 + 90) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 90 * (5 : ZMod 567240517) ^ 90 := by rw [pow_add]
          _ = 159740232 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 567240517) ^ 360 = 306429010 := by
        calc
          (5 : ZMod 567240517) ^ 360 = (5 : ZMod 567240517) ^ (180 + 180) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 180 * (5 : ZMod 567240517) ^ 180 := by rw [pow_add]
          _ = 306429010 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 567240517) ^ 721 = 177086215 := by
        calc
          (5 : ZMod 567240517) ^ 721 = (5 : ZMod 567240517) ^ (360 + 360 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 360 * (5 : ZMod 567240517) ^ 360) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 177086215 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 567240517) ^ 1442 = 296333656 := by
        calc
          (5 : ZMod 567240517) ^ 1442 = (5 : ZMod 567240517) ^ (721 + 721) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 721 * (5 : ZMod 567240517) ^ 721 := by rw [pow_add]
          _ = 296333656 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 567240517) ^ 2885 = 135660866 := by
        calc
          (5 : ZMod 567240517) ^ 2885 = (5 : ZMod 567240517) ^ (1442 + 1442 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 1442 * (5 : ZMod 567240517) ^ 1442) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 135660866 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 567240517) ^ 5770 = 441151402 := by
        calc
          (5 : ZMod 567240517) ^ 5770 = (5 : ZMod 567240517) ^ (2885 + 2885) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 2885 * (5 : ZMod 567240517) ^ 2885 := by rw [pow_add]
          _ = 441151402 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 567240517) ^ 11540 = 298706298 := by
        calc
          (5 : ZMod 567240517) ^ 11540 = (5 : ZMod 567240517) ^ (5770 + 5770) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 5770 * (5 : ZMod 567240517) ^ 5770 := by rw [pow_add]
          _ = 298706298 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 567240517) ^ 23081 = 461532938 := by
        calc
          (5 : ZMod 567240517) ^ 23081 = (5 : ZMod 567240517) ^ (11540 + 11540 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 11540 * (5 : ZMod 567240517) ^ 11540) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 461532938 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 567240517) ^ 46162 = 325759112 := by
        calc
          (5 : ZMod 567240517) ^ 46162 = (5 : ZMod 567240517) ^ (23081 + 23081) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 23081 * (5 : ZMod 567240517) ^ 23081 := by rw [pow_add]
          _ = 325759112 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 567240517) ^ 92324 = 492194254 := by
        calc
          (5 : ZMod 567240517) ^ 92324 = (5 : ZMod 567240517) ^ (46162 + 46162) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 46162 * (5 : ZMod 567240517) ^ 46162 := by rw [pow_add]
          _ = 492194254 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 567240517) ^ 184648 = 522545364 := by
        calc
          (5 : ZMod 567240517) ^ 184648 = (5 : ZMod 567240517) ^ (92324 + 92324) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 92324 * (5 : ZMod 567240517) ^ 92324 := by rw [pow_add]
          _ = 522545364 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 567240517) ^ 369297 = 502846695 := by
        calc
          (5 : ZMod 567240517) ^ 369297 = (5 : ZMod 567240517) ^ (184648 + 184648 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 184648 * (5 : ZMod 567240517) ^ 184648) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 502846695 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 567240517) ^ 738594 = 396345113 := by
        calc
          (5 : ZMod 567240517) ^ 738594 = (5 : ZMod 567240517) ^ (369297 + 369297) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 369297 * (5 : ZMod 567240517) ^ 369297 := by rw [pow_add]
          _ = 396345113 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 567240517) ^ 1477188 = 19473410 := by
        calc
          (5 : ZMod 567240517) ^ 1477188 = (5 : ZMod 567240517) ^ (738594 + 738594) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 738594 * (5 : ZMod 567240517) ^ 738594 := by rw [pow_add]
          _ = 19473410 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 567240517) ^ 2954377 = 122686994 := by
        calc
          (5 : ZMod 567240517) ^ 2954377 = (5 : ZMod 567240517) ^ (1477188 + 1477188 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 1477188 * (5 : ZMod 567240517) ^ 1477188) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 122686994 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 567240517) ^ 5908755 = 312593039 := by
        calc
          (5 : ZMod 567240517) ^ 5908755 = (5 : ZMod 567240517) ^ (2954377 + 2954377 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 2954377 * (5 : ZMod 567240517) ^ 2954377) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 312593039 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 567240517) ^ 11817510 = 64856873 := by
        calc
          (5 : ZMod 567240517) ^ 11817510 = (5 : ZMod 567240517) ^ (5908755 + 5908755) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 5908755 * (5 : ZMod 567240517) ^ 5908755 := by rw [pow_add]
          _ = 64856873 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 567240517) ^ 23635021 = 295872372 := by
        calc
          (5 : ZMod 567240517) ^ 23635021 = (5 : ZMod 567240517) ^ (11817510 + 11817510 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 11817510 * (5 : ZMod 567240517) ^ 11817510) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 295872372 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 567240517) ^ 47270043 = 333901433 := by
        calc
          (5 : ZMod 567240517) ^ 47270043 = (5 : ZMod 567240517) ^ (23635021 + 23635021 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 23635021 * (5 : ZMod 567240517) ^ 23635021) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 333901433 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 567240517) ^ 94540086 = 277855668 := by
        calc
          (5 : ZMod 567240517) ^ 94540086 = (5 : ZMod 567240517) ^ (47270043 + 47270043) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 47270043 * (5 : ZMod 567240517) ^ 47270043 := by rw [pow_add]
          _ = 277855668 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 567240517) ^ 189080172 = 277855667 := by
        calc
          (5 : ZMod 567240517) ^ 189080172 = (5 : ZMod 567240517) ^ (94540086 + 94540086) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 94540086 * (5 : ZMod 567240517) ^ 94540086 := by rw [pow_add]
          _ = 277855667 := by rw [factor_1_26]; decide
      change (5 : ZMod 567240517) ^ 189080172 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (5 : ZMod 567240517) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 567240517) ^ 3 = 125 := by
        calc
          (5 : ZMod 567240517) ^ 3 = (5 : ZMod 567240517) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 1 * (5 : ZMod 567240517) ^ 1) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 567240517) ^ 7 = 78125 := by
        calc
          (5 : ZMod 567240517) ^ 7 = (5 : ZMod 567240517) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 3 * (5 : ZMod 567240517) ^ 3) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 567240517) ^ 14 = 431110455 := by
        calc
          (5 : ZMod 567240517) ^ 14 = (5 : ZMod 567240517) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 7 * (5 : ZMod 567240517) ^ 7 := by rw [pow_add]
          _ = 431110455 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 567240517) ^ 28 = 47816452 := by
        calc
          (5 : ZMod 567240517) ^ 28 = (5 : ZMod 567240517) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 14 * (5 : ZMod 567240517) ^ 14 := by rw [pow_add]
          _ = 47816452 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 567240517) ^ 56 = 426603316 := by
        calc
          (5 : ZMod 567240517) ^ 56 = (5 : ZMod 567240517) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 28 * (5 : ZMod 567240517) ^ 28 := by rw [pow_add]
          _ = 426603316 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 567240517) ^ 113 = 409436566 := by
        calc
          (5 : ZMod 567240517) ^ 113 = (5 : ZMod 567240517) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 56 * (5 : ZMod 567240517) ^ 56) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 409436566 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 567240517) ^ 227 = 553872318 := by
        calc
          (5 : ZMod 567240517) ^ 227 = (5 : ZMod 567240517) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 113 * (5 : ZMod 567240517) ^ 113) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 553872318 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 567240517) ^ 455 = 367075823 := by
        calc
          (5 : ZMod 567240517) ^ 455 = (5 : ZMod 567240517) ^ (227 + 227 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 227 * (5 : ZMod 567240517) ^ 227) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 367075823 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 567240517) ^ 911 = 341199398 := by
        calc
          (5 : ZMod 567240517) ^ 911 = (5 : ZMod 567240517) ^ (455 + 455 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 455 * (5 : ZMod 567240517) ^ 455) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 341199398 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 567240517) ^ 1822 = 274394744 := by
        calc
          (5 : ZMod 567240517) ^ 1822 = (5 : ZMod 567240517) ^ (911 + 911) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 911 * (5 : ZMod 567240517) ^ 911 := by rw [pow_add]
          _ = 274394744 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 567240517) ^ 3644 = 74327867 := by
        calc
          (5 : ZMod 567240517) ^ 3644 = (5 : ZMod 567240517) ^ (1822 + 1822) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 1822 * (5 : ZMod 567240517) ^ 1822 := by rw [pow_add]
          _ = 74327867 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 567240517) ^ 7288 = 171574910 := by
        calc
          (5 : ZMod 567240517) ^ 7288 = (5 : ZMod 567240517) ^ (3644 + 3644) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 3644 * (5 : ZMod 567240517) ^ 3644 := by rw [pow_add]
          _ = 171574910 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 567240517) ^ 14577 = 18314186 := by
        calc
          (5 : ZMod 567240517) ^ 14577 = (5 : ZMod 567240517) ^ (7288 + 7288 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 7288 * (5 : ZMod 567240517) ^ 7288) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 18314186 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 567240517) ^ 29155 = 455702480 := by
        calc
          (5 : ZMod 567240517) ^ 29155 = (5 : ZMod 567240517) ^ (14577 + 14577 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 14577 * (5 : ZMod 567240517) ^ 14577) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 455702480 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 567240517) ^ 58310 = 497956444 := by
        calc
          (5 : ZMod 567240517) ^ 58310 = (5 : ZMod 567240517) ^ (29155 + 29155) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 29155 * (5 : ZMod 567240517) ^ 29155 := by rw [pow_add]
          _ = 497956444 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 567240517) ^ 116620 = 253268040 := by
        calc
          (5 : ZMod 567240517) ^ 116620 = (5 : ZMod 567240517) ^ (58310 + 58310) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 58310 * (5 : ZMod 567240517) ^ 58310 := by rw [pow_add]
          _ = 253268040 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 567240517) ^ 233240 = 680362 := by
        calc
          (5 : ZMod 567240517) ^ 233240 = (5 : ZMod 567240517) ^ (116620 + 116620) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 116620 * (5 : ZMod 567240517) ^ 116620 := by rw [pow_add]
          _ = 680362 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 567240517) ^ 466480 = 24189172 := by
        calc
          (5 : ZMod 567240517) ^ 466480 = (5 : ZMod 567240517) ^ (233240 + 233240) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 233240 * (5 : ZMod 567240517) ^ 233240 := by rw [pow_add]
          _ = 24189172 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 567240517) ^ 932961 = 373166815 := by
        calc
          (5 : ZMod 567240517) ^ 932961 = (5 : ZMod 567240517) ^ (466480 + 466480 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 466480 * (5 : ZMod 567240517) ^ 466480) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 373166815 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 567240517) ^ 1865922 = 516858870 := by
        calc
          (5 : ZMod 567240517) ^ 1865922 = (5 : ZMod 567240517) ^ (932961 + 932961) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 932961 * (5 : ZMod 567240517) ^ 932961 := by rw [pow_add]
          _ = 516858870 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 567240517) ^ 3731845 = 131182679 := by
        calc
          (5 : ZMod 567240517) ^ 3731845 = (5 : ZMod 567240517) ^ (1865922 + 1865922 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 1865922 * (5 : ZMod 567240517) ^ 1865922) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 131182679 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 567240517) ^ 7463691 = 565372345 := by
        calc
          (5 : ZMod 567240517) ^ 7463691 = (5 : ZMod 567240517) ^ (3731845 + 3731845 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 3731845 * (5 : ZMod 567240517) ^ 3731845) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 565372345 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 567240517) ^ 14927382 = 402961000 := by
        calc
          (5 : ZMod 567240517) ^ 14927382 = (5 : ZMod 567240517) ^ (7463691 + 7463691) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 7463691 * (5 : ZMod 567240517) ^ 7463691 := by rw [pow_add]
          _ = 402961000 := by rw [factor_2_22]; decide
      have factor_2_24 : (5 : ZMod 567240517) ^ 29854764 = 502821080 := by
        calc
          (5 : ZMod 567240517) ^ 29854764 = (5 : ZMod 567240517) ^ (14927382 + 14927382) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 14927382 * (5 : ZMod 567240517) ^ 14927382 := by rw [pow_add]
          _ = 502821080 := by rw [factor_2_23]; decide
      change (5 : ZMod 567240517) ^ 29854764 ≠ 1
      rw [factor_2_24]
      decide
    ·
      have factor_3_0 : (5 : ZMod 567240517) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 567240517) ^ 2 = 25 := by
        calc
          (5 : ZMod 567240517) ^ 2 = (5 : ZMod 567240517) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 1 * (5 : ZMod 567240517) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 567240517) ^ 4 = 625 := by
        calc
          (5 : ZMod 567240517) ^ 4 = (5 : ZMod 567240517) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 2 * (5 : ZMod 567240517) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 567240517) ^ 8 = 390625 := by
        calc
          (5 : ZMod 567240517) ^ 8 = (5 : ZMod 567240517) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 4 * (5 : ZMod 567240517) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 567240517) ^ 17 = 957760 := by
        calc
          (5 : ZMod 567240517) ^ 17 = (5 : ZMod 567240517) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 8 * (5 : ZMod 567240517) ^ 8) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 957760 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 567240517) ^ 35 = 381508055 := by
        calc
          (5 : ZMod 567240517) ^ 35 = (5 : ZMod 567240517) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 17 * (5 : ZMod 567240517) ^ 17) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 381508055 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 567240517) ^ 70 = 319634986 := by
        calc
          (5 : ZMod 567240517) ^ 70 = (5 : ZMod 567240517) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 35 * (5 : ZMod 567240517) ^ 35 := by rw [pow_add]
          _ = 319634986 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 567240517) ^ 141 = 36026894 := by
        calc
          (5 : ZMod 567240517) ^ 141 = (5 : ZMod 567240517) ^ (70 + 70 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 70 * (5 : ZMod 567240517) ^ 70) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 36026894 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 567240517) ^ 282 = 29908516 := by
        calc
          (5 : ZMod 567240517) ^ 282 = (5 : ZMod 567240517) ^ (141 + 141) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 141 * (5 : ZMod 567240517) ^ 141 := by rw [pow_add]
          _ = 29908516 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 567240517) ^ 564 = 320190834 := by
        calc
          (5 : ZMod 567240517) ^ 564 = (5 : ZMod 567240517) ^ (282 + 282) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 282 * (5 : ZMod 567240517) ^ 282 := by rw [pow_add]
          _ = 320190834 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 567240517) ^ 1128 = 59558457 := by
        calc
          (5 : ZMod 567240517) ^ 1128 = (5 : ZMod 567240517) ^ (564 + 564) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 564 * (5 : ZMod 567240517) ^ 564 := by rw [pow_add]
          _ = 59558457 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 567240517) ^ 2256 = 156427716 := by
        calc
          (5 : ZMod 567240517) ^ 2256 = (5 : ZMod 567240517) ^ (1128 + 1128) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 1128 * (5 : ZMod 567240517) ^ 1128 := by rw [pow_add]
          _ = 156427716 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 567240517) ^ 4512 = 402022901 := by
        calc
          (5 : ZMod 567240517) ^ 4512 = (5 : ZMod 567240517) ^ (2256 + 2256) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 2256 * (5 : ZMod 567240517) ^ 2256 := by rw [pow_add]
          _ = 402022901 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 567240517) ^ 9025 = 252894933 := by
        calc
          (5 : ZMod 567240517) ^ 9025 = (5 : ZMod 567240517) ^ (4512 + 4512 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 4512 * (5 : ZMod 567240517) ^ 4512) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 252894933 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 567240517) ^ 18051 = 129557543 := by
        calc
          (5 : ZMod 567240517) ^ 18051 = (5 : ZMod 567240517) ^ (9025 + 9025 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 9025 * (5 : ZMod 567240517) ^ 9025) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 129557543 := by rw [factor_3_13]; decide
      have factor_3_15 : (5 : ZMod 567240517) ^ 36102 = 100942066 := by
        calc
          (5 : ZMod 567240517) ^ 36102 = (5 : ZMod 567240517) ^ (18051 + 18051) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 18051 * (5 : ZMod 567240517) ^ 18051 := by rw [pow_add]
          _ = 100942066 := by rw [factor_3_14]; decide
      have factor_3_16 : (5 : ZMod 567240517) ^ 72204 = 122794580 := by
        calc
          (5 : ZMod 567240517) ^ 72204 = (5 : ZMod 567240517) ^ (36102 + 36102) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 36102 * (5 : ZMod 567240517) ^ 36102 := by rw [pow_add]
          _ = 122794580 := by rw [factor_3_15]; decide
      have factor_3_17 : (5 : ZMod 567240517) ^ 144409 = 325058810 := by
        calc
          (5 : ZMod 567240517) ^ 144409 = (5 : ZMod 567240517) ^ (72204 + 72204 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 72204 * (5 : ZMod 567240517) ^ 72204) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 325058810 := by rw [factor_3_16]; decide
      have factor_3_18 : (5 : ZMod 567240517) ^ 288819 = 396715190 := by
        calc
          (5 : ZMod 567240517) ^ 288819 = (5 : ZMod 567240517) ^ (144409 + 144409 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 144409 * (5 : ZMod 567240517) ^ 144409) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 396715190 := by rw [factor_3_17]; decide
      have factor_3_19 : (5 : ZMod 567240517) ^ 577638 = 317528356 := by
        calc
          (5 : ZMod 567240517) ^ 577638 = (5 : ZMod 567240517) ^ (288819 + 288819) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 288819 * (5 : ZMod 567240517) ^ 288819 := by rw [pow_add]
          _ = 317528356 := by rw [factor_3_18]; decide
      have factor_3_20 : (5 : ZMod 567240517) ^ 1155276 = 411415016 := by
        calc
          (5 : ZMod 567240517) ^ 1155276 = (5 : ZMod 567240517) ^ (577638 + 577638) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 577638 * (5 : ZMod 567240517) ^ 577638 := by rw [pow_add]
          _ = 411415016 := by rw [factor_3_19]; decide
      change (5 : ZMod 567240517) ^ 1155276 ≠ 1
      rw [factor_3_20]
      decide
    ·
      have factor_4_0 : (5 : ZMod 567240517) ^ 1 = 5 := by norm_num
      have factor_4_1 : (5 : ZMod 567240517) ^ 3 = 125 := by
        calc
          (5 : ZMod 567240517) ^ 3 = (5 : ZMod 567240517) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 1 * (5 : ZMod 567240517) ^ 1) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_4_0]; decide
      have factor_4_2 : (5 : ZMod 567240517) ^ 7 = 78125 := by
        calc
          (5 : ZMod 567240517) ^ 7 = (5 : ZMod 567240517) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 3 * (5 : ZMod 567240517) ^ 3) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_4_1]; decide
      have factor_4_3 : (5 : ZMod 567240517) ^ 15 = 453830724 := by
        calc
          (5 : ZMod 567240517) ^ 15 = (5 : ZMod 567240517) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 7 * (5 : ZMod 567240517) ^ 7) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 453830724 := by rw [factor_4_2]; decide
      have factor_4_4 : (5 : ZMod 567240517) ^ 30 = 60930266 := by
        calc
          (5 : ZMod 567240517) ^ 30 = (5 : ZMod 567240517) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 15 * (5 : ZMod 567240517) ^ 15 := by rw [pow_add]
          _ = 60930266 := by rw [factor_4_3]; decide
      have factor_4_5 : (5 : ZMod 567240517) ^ 61 = 120147550 := by
        calc
          (5 : ZMod 567240517) ^ 61 = (5 : ZMod 567240517) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 30 * (5 : ZMod 567240517) ^ 30) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 120147550 := by rw [factor_4_4]; decide
      have factor_4_6 : (5 : ZMod 567240517) ^ 122 = 427596109 := by
        calc
          (5 : ZMod 567240517) ^ 122 = (5 : ZMod 567240517) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 61 * (5 : ZMod 567240517) ^ 61 := by rw [pow_add]
          _ = 427596109 := by rw [factor_4_5]; decide
      have factor_4_7 : (5 : ZMod 567240517) ^ 245 = 566136903 := by
        calc
          (5 : ZMod 567240517) ^ 245 = (5 : ZMod 567240517) ^ (122 + 122 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 122 * (5 : ZMod 567240517) ^ 122) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 566136903 := by rw [factor_4_6]; decide
      have factor_4_8 : (5 : ZMod 567240517) ^ 491 = 492354985 := by
        calc
          (5 : ZMod 567240517) ^ 491 = (5 : ZMod 567240517) ^ (245 + 245 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 245 * (5 : ZMod 567240517) ^ 245) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 492354985 := by rw [factor_4_7]; decide
      have factor_4_9 : (5 : ZMod 567240517) ^ 983 = 137675167 := by
        calc
          (5 : ZMod 567240517) ^ 983 = (5 : ZMod 567240517) ^ (491 + 491 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 491 * (5 : ZMod 567240517) ^ 491) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 137675167 := by rw [factor_4_8]; decide
      have factor_4_10 : (5 : ZMod 567240517) ^ 1967 = 143034506 := by
        calc
          (5 : ZMod 567240517) ^ 1967 = (5 : ZMod 567240517) ^ (983 + 983 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 983 * (5 : ZMod 567240517) ^ 983) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 143034506 := by rw [factor_4_9]; decide
      have factor_4_11 : (5 : ZMod 567240517) ^ 3935 = 224105791 := by
        calc
          (5 : ZMod 567240517) ^ 3935 = (5 : ZMod 567240517) ^ (1967 + 1967 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 1967 * (5 : ZMod 567240517) ^ 1967) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 224105791 := by rw [factor_4_10]; decide
      have factor_4_12 : (5 : ZMod 567240517) ^ 7871 = 342936877 := by
        calc
          (5 : ZMod 567240517) ^ 7871 = (5 : ZMod 567240517) ^ (3935 + 3935 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 3935 * (5 : ZMod 567240517) ^ 3935) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 342936877 := by rw [factor_4_11]; decide
      have factor_4_13 : (5 : ZMod 567240517) ^ 15742 = 328553874 := by
        calc
          (5 : ZMod 567240517) ^ 15742 = (5 : ZMod 567240517) ^ (7871 + 7871) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 7871 * (5 : ZMod 567240517) ^ 7871 := by rw [pow_add]
          _ = 328553874 := by rw [factor_4_12]; decide
      have factor_4_14 : (5 : ZMod 567240517) ^ 31485 = 17637990 := by
        calc
          (5 : ZMod 567240517) ^ 31485 = (5 : ZMod 567240517) ^ (15742 + 15742 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 15742 * (5 : ZMod 567240517) ^ 15742) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 17637990 := by rw [factor_4_13]; decide
      have factor_4_15 : (5 : ZMod 567240517) ^ 62970 = 167615586 := by
        calc
          (5 : ZMod 567240517) ^ 62970 = (5 : ZMod 567240517) ^ (31485 + 31485) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 31485 * (5 : ZMod 567240517) ^ 31485 := by rw [pow_add]
          _ = 167615586 := by rw [factor_4_14]; decide
      have factor_4_16 : (5 : ZMod 567240517) ^ 125941 = 565684151 := by
        calc
          (5 : ZMod 567240517) ^ 125941 = (5 : ZMod 567240517) ^ (62970 + 62970 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 62970 * (5 : ZMod 567240517) ^ 62970) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 565684151 := by rw [factor_4_15]; decide
      have factor_4_17 : (5 : ZMod 567240517) ^ 251883 = 223351313 := by
        calc
          (5 : ZMod 567240517) ^ 251883 = (5 : ZMod 567240517) ^ (125941 + 125941 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = ((5 : ZMod 567240517) ^ 125941 * (5 : ZMod 567240517) ^ 125941) * (5 : ZMod 567240517) := by rw [pow_succ, pow_add]
          _ = 223351313 := by rw [factor_4_16]; decide
      have factor_4_18 : (5 : ZMod 567240517) ^ 503766 = 11363212 := by
        calc
          (5 : ZMod 567240517) ^ 503766 = (5 : ZMod 567240517) ^ (251883 + 251883) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 251883 * (5 : ZMod 567240517) ^ 251883 := by rw [pow_add]
          _ = 11363212 := by rw [factor_4_17]; decide
      have factor_4_19 : (5 : ZMod 567240517) ^ 1007532 = 493591200 := by
        calc
          (5 : ZMod 567240517) ^ 1007532 = (5 : ZMod 567240517) ^ (503766 + 503766) :=
            congrArg (fun n : ℕ => (5 : ZMod 567240517) ^ n) (by norm_num)
          _ = (5 : ZMod 567240517) ^ 503766 * (5 : ZMod 567240517) ^ 503766 := by rw [pow_add]
          _ = 493591200 := by rw [factor_4_18]; decide
      change (5 : ZMod 567240517) ^ 1007532 ≠ 1
      rw [factor_4_19]
      decide

#print axioms prime_lucas_567240517

end TotientTailPeriodKiller
end Erdos249257
