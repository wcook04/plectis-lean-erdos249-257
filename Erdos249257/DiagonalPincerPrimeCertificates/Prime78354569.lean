import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=27 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_78354569 : Nat.Prime 78354569 := by
  apply lucas_primality 78354569 (3 : ZMod 78354569)
  ·
      have fermat_0 : (3 : ZMod 78354569) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 78354569) ^ 2 = 9 := by
        calc
          (3 : ZMod 78354569) ^ 2 = (3 : ZMod 78354569) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 1 * (3 : ZMod 78354569) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 78354569) ^ 4 = 81 := by
        calc
          (3 : ZMod 78354569) ^ 4 = (3 : ZMod 78354569) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 2 * (3 : ZMod 78354569) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 78354569) ^ 9 = 19683 := by
        calc
          (3 : ZMod 78354569) ^ 9 = (3 : ZMod 78354569) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 4 * (3 : ZMod 78354569) ^ 4) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 78354569) ^ 18 = 74002213 := by
        calc
          (3 : ZMod 78354569) ^ 18 = (3 : ZMod 78354569) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 9 * (3 : ZMod 78354569) ^ 9 := by rw [pow_add]
          _ = 74002213 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 78354569) ^ 37 = 6447888 := by
        calc
          (3 : ZMod 78354569) ^ 37 = (3 : ZMod 78354569) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 18 * (3 : ZMod 78354569) ^ 18) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 6447888 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 78354569) ^ 74 = 11930868 := by
        calc
          (3 : ZMod 78354569) ^ 74 = (3 : ZMod 78354569) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 37 * (3 : ZMod 78354569) ^ 37 := by rw [pow_add]
          _ = 11930868 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 78354569) ^ 149 = 44794408 := by
        calc
          (3 : ZMod 78354569) ^ 149 = (3 : ZMod 78354569) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 74 * (3 : ZMod 78354569) ^ 74) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 44794408 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 78354569) ^ 298 = 3916983 := by
        calc
          (3 : ZMod 78354569) ^ 298 = (3 : ZMod 78354569) ^ (149 + 149) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 149 * (3 : ZMod 78354569) ^ 149 := by rw [pow_add]
          _ = 3916983 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 78354569) ^ 597 = 51226352 := by
        calc
          (3 : ZMod 78354569) ^ 597 = (3 : ZMod 78354569) ^ (298 + 298 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 298 * (3 : ZMod 78354569) ^ 298) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 51226352 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 78354569) ^ 1195 = 40649860 := by
        calc
          (3 : ZMod 78354569) ^ 1195 = (3 : ZMod 78354569) ^ (597 + 597 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 597 * (3 : ZMod 78354569) ^ 597) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 40649860 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 78354569) ^ 2391 = 67307018 := by
        calc
          (3 : ZMod 78354569) ^ 2391 = (3 : ZMod 78354569) ^ (1195 + 1195 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 1195 * (3 : ZMod 78354569) ^ 1195) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 67307018 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 78354569) ^ 4782 = 15531303 := by
        calc
          (3 : ZMod 78354569) ^ 4782 = (3 : ZMod 78354569) ^ (2391 + 2391) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 2391 * (3 : ZMod 78354569) ^ 2391 := by rw [pow_add]
          _ = 15531303 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 78354569) ^ 9564 = 15363806 := by
        calc
          (3 : ZMod 78354569) ^ 9564 = (3 : ZMod 78354569) ^ (4782 + 4782) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 4782 * (3 : ZMod 78354569) ^ 4782 := by rw [pow_add]
          _ = 15363806 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 78354569) ^ 19129 = 985438 := by
        calc
          (3 : ZMod 78354569) ^ 19129 = (3 : ZMod 78354569) ^ (9564 + 9564 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 9564 * (3 : ZMod 78354569) ^ 9564) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 985438 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 78354569) ^ 38259 = 41280112 := by
        calc
          (3 : ZMod 78354569) ^ 38259 = (3 : ZMod 78354569) ^ (19129 + 19129 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 19129 * (3 : ZMod 78354569) ^ 19129) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 41280112 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 78354569) ^ 76518 = 2159168 := by
        calc
          (3 : ZMod 78354569) ^ 76518 = (3 : ZMod 78354569) ^ (38259 + 38259) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 38259 * (3 : ZMod 78354569) ^ 38259 := by rw [pow_add]
          _ = 2159168 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 78354569) ^ 153036 = 66305862 := by
        calc
          (3 : ZMod 78354569) ^ 153036 = (3 : ZMod 78354569) ^ (76518 + 76518) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 76518 * (3 : ZMod 78354569) ^ 76518 := by rw [pow_add]
          _ = 66305862 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 78354569) ^ 306072 = 69366237 := by
        calc
          (3 : ZMod 78354569) ^ 306072 = (3 : ZMod 78354569) ^ (153036 + 153036) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 153036 * (3 : ZMod 78354569) ^ 153036 := by rw [pow_add]
          _ = 69366237 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 78354569) ^ 612145 = 65867422 := by
        calc
          (3 : ZMod 78354569) ^ 612145 = (3 : ZMod 78354569) ^ (306072 + 306072 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 306072 * (3 : ZMod 78354569) ^ 306072) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 65867422 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 78354569) ^ 1224290 = 35352280 := by
        calc
          (3 : ZMod 78354569) ^ 1224290 = (3 : ZMod 78354569) ^ (612145 + 612145) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 612145 * (3 : ZMod 78354569) ^ 612145 := by rw [pow_add]
          _ = 35352280 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 78354569) ^ 2448580 = 39648991 := by
        calc
          (3 : ZMod 78354569) ^ 2448580 = (3 : ZMod 78354569) ^ (1224290 + 1224290) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 1224290 * (3 : ZMod 78354569) ^ 1224290 := by rw [pow_add]
          _ = 39648991 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 78354569) ^ 4897160 = 38812109 := by
        calc
          (3 : ZMod 78354569) ^ 4897160 = (3 : ZMod 78354569) ^ (2448580 + 2448580) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 2448580 * (3 : ZMod 78354569) ^ 2448580 := by rw [pow_add]
          _ = 38812109 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 78354569) ^ 9794321 = 596729 := by
        calc
          (3 : ZMod 78354569) ^ 9794321 = (3 : ZMod 78354569) ^ (4897160 + 4897160 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 4897160 * (3 : ZMod 78354569) ^ 4897160) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 596729 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 78354569) ^ 19588642 = 42337905 := by
        calc
          (3 : ZMod 78354569) ^ 19588642 = (3 : ZMod 78354569) ^ (9794321 + 9794321) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 9794321 * (3 : ZMod 78354569) ^ 9794321 := by rw [pow_add]
          _ = 42337905 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 78354569) ^ 39177284 = 78354568 := by
        calc
          (3 : ZMod 78354569) ^ 39177284 = (3 : ZMod 78354569) ^ (19588642 + 19588642) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 19588642 * (3 : ZMod 78354569) ^ 19588642 := by rw [pow_add]
          _ = 78354568 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 78354569) ^ 78354568 = 1 := by
        calc
          (3 : ZMod 78354569) ^ 78354568 = (3 : ZMod 78354569) ^ (39177284 + 39177284) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 39177284 * (3 : ZMod 78354569) ^ 39177284 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (9794321, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (9794321, 1)] : List FactorBlock).map factorBlockValue).prod = 78354569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 78354569) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 78354569) ^ 2 = 9 := by
        calc
          (3 : ZMod 78354569) ^ 2 = (3 : ZMod 78354569) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 1 * (3 : ZMod 78354569) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 78354569) ^ 4 = 81 := by
        calc
          (3 : ZMod 78354569) ^ 4 = (3 : ZMod 78354569) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 2 * (3 : ZMod 78354569) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 78354569) ^ 9 = 19683 := by
        calc
          (3 : ZMod 78354569) ^ 9 = (3 : ZMod 78354569) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 4 * (3 : ZMod 78354569) ^ 4) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 78354569) ^ 18 = 74002213 := by
        calc
          (3 : ZMod 78354569) ^ 18 = (3 : ZMod 78354569) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 9 * (3 : ZMod 78354569) ^ 9 := by rw [pow_add]
          _ = 74002213 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 78354569) ^ 37 = 6447888 := by
        calc
          (3 : ZMod 78354569) ^ 37 = (3 : ZMod 78354569) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 18 * (3 : ZMod 78354569) ^ 18) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 6447888 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 78354569) ^ 74 = 11930868 := by
        calc
          (3 : ZMod 78354569) ^ 74 = (3 : ZMod 78354569) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 37 * (3 : ZMod 78354569) ^ 37 := by rw [pow_add]
          _ = 11930868 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 78354569) ^ 149 = 44794408 := by
        calc
          (3 : ZMod 78354569) ^ 149 = (3 : ZMod 78354569) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 74 * (3 : ZMod 78354569) ^ 74) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 44794408 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 78354569) ^ 298 = 3916983 := by
        calc
          (3 : ZMod 78354569) ^ 298 = (3 : ZMod 78354569) ^ (149 + 149) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 149 * (3 : ZMod 78354569) ^ 149 := by rw [pow_add]
          _ = 3916983 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 78354569) ^ 597 = 51226352 := by
        calc
          (3 : ZMod 78354569) ^ 597 = (3 : ZMod 78354569) ^ (298 + 298 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 298 * (3 : ZMod 78354569) ^ 298) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 51226352 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 78354569) ^ 1195 = 40649860 := by
        calc
          (3 : ZMod 78354569) ^ 1195 = (3 : ZMod 78354569) ^ (597 + 597 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 597 * (3 : ZMod 78354569) ^ 597) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 40649860 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 78354569) ^ 2391 = 67307018 := by
        calc
          (3 : ZMod 78354569) ^ 2391 = (3 : ZMod 78354569) ^ (1195 + 1195 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 1195 * (3 : ZMod 78354569) ^ 1195) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 67307018 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 78354569) ^ 4782 = 15531303 := by
        calc
          (3 : ZMod 78354569) ^ 4782 = (3 : ZMod 78354569) ^ (2391 + 2391) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 2391 * (3 : ZMod 78354569) ^ 2391 := by rw [pow_add]
          _ = 15531303 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 78354569) ^ 9564 = 15363806 := by
        calc
          (3 : ZMod 78354569) ^ 9564 = (3 : ZMod 78354569) ^ (4782 + 4782) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 4782 * (3 : ZMod 78354569) ^ 4782 := by rw [pow_add]
          _ = 15363806 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 78354569) ^ 19129 = 985438 := by
        calc
          (3 : ZMod 78354569) ^ 19129 = (3 : ZMod 78354569) ^ (9564 + 9564 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 9564 * (3 : ZMod 78354569) ^ 9564) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 985438 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 78354569) ^ 38259 = 41280112 := by
        calc
          (3 : ZMod 78354569) ^ 38259 = (3 : ZMod 78354569) ^ (19129 + 19129 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 19129 * (3 : ZMod 78354569) ^ 19129) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 41280112 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 78354569) ^ 76518 = 2159168 := by
        calc
          (3 : ZMod 78354569) ^ 76518 = (3 : ZMod 78354569) ^ (38259 + 38259) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 38259 * (3 : ZMod 78354569) ^ 38259 := by rw [pow_add]
          _ = 2159168 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 78354569) ^ 153036 = 66305862 := by
        calc
          (3 : ZMod 78354569) ^ 153036 = (3 : ZMod 78354569) ^ (76518 + 76518) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 76518 * (3 : ZMod 78354569) ^ 76518 := by rw [pow_add]
          _ = 66305862 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 78354569) ^ 306072 = 69366237 := by
        calc
          (3 : ZMod 78354569) ^ 306072 = (3 : ZMod 78354569) ^ (153036 + 153036) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 153036 * (3 : ZMod 78354569) ^ 153036 := by rw [pow_add]
          _ = 69366237 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 78354569) ^ 612145 = 65867422 := by
        calc
          (3 : ZMod 78354569) ^ 612145 = (3 : ZMod 78354569) ^ (306072 + 306072 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 306072 * (3 : ZMod 78354569) ^ 306072) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 65867422 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 78354569) ^ 1224290 = 35352280 := by
        calc
          (3 : ZMod 78354569) ^ 1224290 = (3 : ZMod 78354569) ^ (612145 + 612145) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 612145 * (3 : ZMod 78354569) ^ 612145 := by rw [pow_add]
          _ = 35352280 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 78354569) ^ 2448580 = 39648991 := by
        calc
          (3 : ZMod 78354569) ^ 2448580 = (3 : ZMod 78354569) ^ (1224290 + 1224290) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 1224290 * (3 : ZMod 78354569) ^ 1224290 := by rw [pow_add]
          _ = 39648991 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 78354569) ^ 4897160 = 38812109 := by
        calc
          (3 : ZMod 78354569) ^ 4897160 = (3 : ZMod 78354569) ^ (2448580 + 2448580) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 2448580 * (3 : ZMod 78354569) ^ 2448580 := by rw [pow_add]
          _ = 38812109 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 78354569) ^ 9794321 = 596729 := by
        calc
          (3 : ZMod 78354569) ^ 9794321 = (3 : ZMod 78354569) ^ (4897160 + 4897160 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = ((3 : ZMod 78354569) ^ 4897160 * (3 : ZMod 78354569) ^ 4897160) * (3 : ZMod 78354569) := by rw [pow_succ, pow_add]
          _ = 596729 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 78354569) ^ 19588642 = 42337905 := by
        calc
          (3 : ZMod 78354569) ^ 19588642 = (3 : ZMod 78354569) ^ (9794321 + 9794321) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 9794321 * (3 : ZMod 78354569) ^ 9794321 := by rw [pow_add]
          _ = 42337905 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 78354569) ^ 39177284 = 78354568 := by
        calc
          (3 : ZMod 78354569) ^ 39177284 = (3 : ZMod 78354569) ^ (19588642 + 19588642) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 19588642 * (3 : ZMod 78354569) ^ 19588642 := by rw [pow_add]
          _ = 78354568 := by rw [factor_0_24]; decide
      change (3 : ZMod 78354569) ^ 39177284 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (3 : ZMod 78354569) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 78354569) ^ 2 = 9 := by
        calc
          (3 : ZMod 78354569) ^ 2 = (3 : ZMod 78354569) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 1 * (3 : ZMod 78354569) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 78354569) ^ 4 = 81 := by
        calc
          (3 : ZMod 78354569) ^ 4 = (3 : ZMod 78354569) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 2 * (3 : ZMod 78354569) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 78354569) ^ 8 = 6561 := by
        calc
          (3 : ZMod 78354569) ^ 8 = (3 : ZMod 78354569) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 78354569) ^ n) (by norm_num)
          _ = (3 : ZMod 78354569) ^ 4 * (3 : ZMod 78354569) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_1_2]; decide
      change (3 : ZMod 78354569) ^ 8 ≠ 1
      rw [factor_1_3]
      decide

#print axioms prime_lucas_78354569

end TotientTailPeriodKiller
end Erdos249257
