import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_40185923 : Nat.Prime 40185923 := by
  apply lucas_primality 40185923 (2 : ZMod 40185923)
  ·
      have fermat_0 : (2 : ZMod 40185923) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 40185923) ^ 2 = 4 := by
        calc
          (2 : ZMod 40185923) ^ 2 = (2 : ZMod 40185923) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 1 * (2 : ZMod 40185923) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 40185923) ^ 4 = 16 := by
        calc
          (2 : ZMod 40185923) ^ 4 = (2 : ZMod 40185923) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 2 * (2 : ZMod 40185923) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 40185923) ^ 9 = 512 := by
        calc
          (2 : ZMod 40185923) ^ 9 = (2 : ZMod 40185923) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 4 * (2 : ZMod 40185923) ^ 4) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 40185923) ^ 19 = 524288 := by
        calc
          (2 : ZMod 40185923) ^ 19 = (2 : ZMod 40185923) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 9 * (2 : ZMod 40185923) ^ 9) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 40185923) ^ 38 = 6193624 := by
        calc
          (2 : ZMod 40185923) ^ 38 = (2 : ZMod 40185923) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 19 * (2 : ZMod 40185923) ^ 19 := by rw [pow_add]
          _ = 6193624 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 40185923) ^ 76 = 18574575 := by
        calc
          (2 : ZMod 40185923) ^ 76 = (2 : ZMod 40185923) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 38 * (2 : ZMod 40185923) ^ 38 := by rw [pow_add]
          _ = 18574575 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 40185923) ^ 153 = 2042860 := by
        calc
          (2 : ZMod 40185923) ^ 153 = (2 : ZMod 40185923) ^ (76 + 76 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 76 * (2 : ZMod 40185923) ^ 76) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 2042860 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 40185923) ^ 306 = 9061973 := by
        calc
          (2 : ZMod 40185923) ^ 306 = (2 : ZMod 40185923) ^ (153 + 153) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 153 * (2 : ZMod 40185923) ^ 153 := by rw [pow_add]
          _ = 9061973 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 40185923) ^ 613 = 7396225 := by
        calc
          (2 : ZMod 40185923) ^ 613 = (2 : ZMod 40185923) ^ (306 + 306 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 306 * (2 : ZMod 40185923) ^ 306) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 7396225 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 40185923) ^ 1226 = 11732877 := by
        calc
          (2 : ZMod 40185923) ^ 1226 = (2 : ZMod 40185923) ^ (613 + 613) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 613 * (2 : ZMod 40185923) ^ 613 := by rw [pow_add]
          _ = 11732877 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 40185923) ^ 2452 = 27285328 := by
        calc
          (2 : ZMod 40185923) ^ 2452 = (2 : ZMod 40185923) ^ (1226 + 1226) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 1226 * (2 : ZMod 40185923) ^ 1226 := by rw [pow_add]
          _ = 27285328 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 40185923) ^ 4905 = 25633186 := by
        calc
          (2 : ZMod 40185923) ^ 4905 = (2 : ZMod 40185923) ^ (2452 + 2452 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 2452 * (2 : ZMod 40185923) ^ 2452) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 25633186 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 40185923) ^ 9811 = 18395270 := by
        calc
          (2 : ZMod 40185923) ^ 9811 = (2 : ZMod 40185923) ^ (4905 + 4905 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 4905 * (2 : ZMod 40185923) ^ 4905) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 18395270 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 40185923) ^ 19622 = 32078093 := by
        calc
          (2 : ZMod 40185923) ^ 19622 = (2 : ZMod 40185923) ^ (9811 + 9811) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 9811 * (2 : ZMod 40185923) ^ 9811 := by rw [pow_add]
          _ = 32078093 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 40185923) ^ 39244 = 10932963 := by
        calc
          (2 : ZMod 40185923) ^ 39244 = (2 : ZMod 40185923) ^ (19622 + 19622) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 19622 * (2 : ZMod 40185923) ^ 19622 := by rw [pow_add]
          _ = 10932963 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 40185923) ^ 78488 = 27613401 := by
        calc
          (2 : ZMod 40185923) ^ 78488 = (2 : ZMod 40185923) ^ (39244 + 39244) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 39244 * (2 : ZMod 40185923) ^ 39244 := by rw [pow_add]
          _ = 27613401 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 40185923) ^ 156976 = 35450132 := by
        calc
          (2 : ZMod 40185923) ^ 156976 = (2 : ZMod 40185923) ^ (78488 + 78488) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 78488 * (2 : ZMod 40185923) ^ 78488 := by rw [pow_add]
          _ = 35450132 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 40185923) ^ 313952 = 33141227 := by
        calc
          (2 : ZMod 40185923) ^ 313952 = (2 : ZMod 40185923) ^ (156976 + 156976) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 156976 * (2 : ZMod 40185923) ^ 156976 := by rw [pow_add]
          _ = 33141227 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 40185923) ^ 627905 = 31131594 := by
        calc
          (2 : ZMod 40185923) ^ 627905 = (2 : ZMod 40185923) ^ (313952 + 313952 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 313952 * (2 : ZMod 40185923) ^ 313952) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 31131594 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 40185923) ^ 1255810 = 23469244 := by
        calc
          (2 : ZMod 40185923) ^ 1255810 = (2 : ZMod 40185923) ^ (627905 + 627905) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 627905 * (2 : ZMod 40185923) ^ 627905 := by rw [pow_add]
          _ = 23469244 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 40185923) ^ 2511620 = 34090338 := by
        calc
          (2 : ZMod 40185923) ^ 2511620 = (2 : ZMod 40185923) ^ (1255810 + 1255810) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 1255810 * (2 : ZMod 40185923) ^ 1255810 := by rw [pow_add]
          _ = 34090338 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 40185923) ^ 5023240 = 10970887 := by
        calc
          (2 : ZMod 40185923) ^ 5023240 = (2 : ZMod 40185923) ^ (2511620 + 2511620) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 2511620 * (2 : ZMod 40185923) ^ 2511620 := by rw [pow_add]
          _ = 10970887 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 40185923) ^ 10046480 = 26006468 := by
        calc
          (2 : ZMod 40185923) ^ 10046480 = (2 : ZMod 40185923) ^ (5023240 + 5023240) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 5023240 * (2 : ZMod 40185923) ^ 5023240 := by rw [pow_add]
          _ = 26006468 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 40185923) ^ 20092961 = 40185922 := by
        calc
          (2 : ZMod 40185923) ^ 20092961 = (2 : ZMod 40185923) ^ (10046480 + 10046480 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 10046480 * (2 : ZMod 40185923) ^ 10046480) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 40185922 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 40185923) ^ 40185922 = 1 := by
        calc
          (2 : ZMod 40185923) ^ 40185922 = (2 : ZMod 40185923) ^ (20092961 + 20092961) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 20092961 * (2 : ZMod 40185923) ^ 20092961 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (23, 1), (37, 1), (3373, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (23, 1), (37, 1), (3373, 1)] : List FactorBlock).map factorBlockValue).prod = 40185923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 40185923) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 40185923) ^ 2 = 4 := by
        calc
          (2 : ZMod 40185923) ^ 2 = (2 : ZMod 40185923) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 1 * (2 : ZMod 40185923) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 40185923) ^ 4 = 16 := by
        calc
          (2 : ZMod 40185923) ^ 4 = (2 : ZMod 40185923) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 2 * (2 : ZMod 40185923) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 40185923) ^ 9 = 512 := by
        calc
          (2 : ZMod 40185923) ^ 9 = (2 : ZMod 40185923) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 4 * (2 : ZMod 40185923) ^ 4) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 40185923) ^ 19 = 524288 := by
        calc
          (2 : ZMod 40185923) ^ 19 = (2 : ZMod 40185923) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 9 * (2 : ZMod 40185923) ^ 9) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 40185923) ^ 38 = 6193624 := by
        calc
          (2 : ZMod 40185923) ^ 38 = (2 : ZMod 40185923) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 19 * (2 : ZMod 40185923) ^ 19 := by rw [pow_add]
          _ = 6193624 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 40185923) ^ 76 = 18574575 := by
        calc
          (2 : ZMod 40185923) ^ 76 = (2 : ZMod 40185923) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 38 * (2 : ZMod 40185923) ^ 38 := by rw [pow_add]
          _ = 18574575 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 40185923) ^ 153 = 2042860 := by
        calc
          (2 : ZMod 40185923) ^ 153 = (2 : ZMod 40185923) ^ (76 + 76 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 76 * (2 : ZMod 40185923) ^ 76) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 2042860 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 40185923) ^ 306 = 9061973 := by
        calc
          (2 : ZMod 40185923) ^ 306 = (2 : ZMod 40185923) ^ (153 + 153) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 153 * (2 : ZMod 40185923) ^ 153 := by rw [pow_add]
          _ = 9061973 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 40185923) ^ 613 = 7396225 := by
        calc
          (2 : ZMod 40185923) ^ 613 = (2 : ZMod 40185923) ^ (306 + 306 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 306 * (2 : ZMod 40185923) ^ 306) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 7396225 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 40185923) ^ 1226 = 11732877 := by
        calc
          (2 : ZMod 40185923) ^ 1226 = (2 : ZMod 40185923) ^ (613 + 613) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 613 * (2 : ZMod 40185923) ^ 613 := by rw [pow_add]
          _ = 11732877 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 40185923) ^ 2452 = 27285328 := by
        calc
          (2 : ZMod 40185923) ^ 2452 = (2 : ZMod 40185923) ^ (1226 + 1226) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 1226 * (2 : ZMod 40185923) ^ 1226 := by rw [pow_add]
          _ = 27285328 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 40185923) ^ 4905 = 25633186 := by
        calc
          (2 : ZMod 40185923) ^ 4905 = (2 : ZMod 40185923) ^ (2452 + 2452 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 2452 * (2 : ZMod 40185923) ^ 2452) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 25633186 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 40185923) ^ 9811 = 18395270 := by
        calc
          (2 : ZMod 40185923) ^ 9811 = (2 : ZMod 40185923) ^ (4905 + 4905 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 4905 * (2 : ZMod 40185923) ^ 4905) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 18395270 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 40185923) ^ 19622 = 32078093 := by
        calc
          (2 : ZMod 40185923) ^ 19622 = (2 : ZMod 40185923) ^ (9811 + 9811) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 9811 * (2 : ZMod 40185923) ^ 9811 := by rw [pow_add]
          _ = 32078093 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 40185923) ^ 39244 = 10932963 := by
        calc
          (2 : ZMod 40185923) ^ 39244 = (2 : ZMod 40185923) ^ (19622 + 19622) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 19622 * (2 : ZMod 40185923) ^ 19622 := by rw [pow_add]
          _ = 10932963 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 40185923) ^ 78488 = 27613401 := by
        calc
          (2 : ZMod 40185923) ^ 78488 = (2 : ZMod 40185923) ^ (39244 + 39244) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 39244 * (2 : ZMod 40185923) ^ 39244 := by rw [pow_add]
          _ = 27613401 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 40185923) ^ 156976 = 35450132 := by
        calc
          (2 : ZMod 40185923) ^ 156976 = (2 : ZMod 40185923) ^ (78488 + 78488) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 78488 * (2 : ZMod 40185923) ^ 78488 := by rw [pow_add]
          _ = 35450132 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 40185923) ^ 313952 = 33141227 := by
        calc
          (2 : ZMod 40185923) ^ 313952 = (2 : ZMod 40185923) ^ (156976 + 156976) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 156976 * (2 : ZMod 40185923) ^ 156976 := by rw [pow_add]
          _ = 33141227 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 40185923) ^ 627905 = 31131594 := by
        calc
          (2 : ZMod 40185923) ^ 627905 = (2 : ZMod 40185923) ^ (313952 + 313952 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 313952 * (2 : ZMod 40185923) ^ 313952) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 31131594 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 40185923) ^ 1255810 = 23469244 := by
        calc
          (2 : ZMod 40185923) ^ 1255810 = (2 : ZMod 40185923) ^ (627905 + 627905) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 627905 * (2 : ZMod 40185923) ^ 627905 := by rw [pow_add]
          _ = 23469244 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 40185923) ^ 2511620 = 34090338 := by
        calc
          (2 : ZMod 40185923) ^ 2511620 = (2 : ZMod 40185923) ^ (1255810 + 1255810) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 1255810 * (2 : ZMod 40185923) ^ 1255810 := by rw [pow_add]
          _ = 34090338 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 40185923) ^ 5023240 = 10970887 := by
        calc
          (2 : ZMod 40185923) ^ 5023240 = (2 : ZMod 40185923) ^ (2511620 + 2511620) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 2511620 * (2 : ZMod 40185923) ^ 2511620 := by rw [pow_add]
          _ = 10970887 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 40185923) ^ 10046480 = 26006468 := by
        calc
          (2 : ZMod 40185923) ^ 10046480 = (2 : ZMod 40185923) ^ (5023240 + 5023240) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 5023240 * (2 : ZMod 40185923) ^ 5023240 := by rw [pow_add]
          _ = 26006468 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 40185923) ^ 20092961 = 40185922 := by
        calc
          (2 : ZMod 40185923) ^ 20092961 = (2 : ZMod 40185923) ^ (10046480 + 10046480 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 10046480 * (2 : ZMod 40185923) ^ 10046480) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 40185922 := by rw [factor_0_23]; decide
      change (2 : ZMod 40185923) ^ 20092961 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (2 : ZMod 40185923) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 40185923) ^ 2 = 4 := by
        calc
          (2 : ZMod 40185923) ^ 2 = (2 : ZMod 40185923) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 1 * (2 : ZMod 40185923) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 40185923) ^ 5 = 32 := by
        calc
          (2 : ZMod 40185923) ^ 5 = (2 : ZMod 40185923) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 2 * (2 : ZMod 40185923) ^ 2) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 40185923) ^ 10 = 1024 := by
        calc
          (2 : ZMod 40185923) ^ 10 = (2 : ZMod 40185923) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 5 * (2 : ZMod 40185923) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 40185923) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 40185923) ^ 21 = (2 : ZMod 40185923) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 10 * (2 : ZMod 40185923) ^ 10) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 40185923) ^ 43 = 37452276 := by
        calc
          (2 : ZMod 40185923) ^ 43 = (2 : ZMod 40185923) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 21 * (2 : ZMod 40185923) ^ 21) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 37452276 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 40185923) ^ 87 = 24846442 := by
        calc
          (2 : ZMod 40185923) ^ 87 = (2 : ZMod 40185923) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 43 * (2 : ZMod 40185923) ^ 43) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 24846442 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 40185923) ^ 175 = 13739226 := by
        calc
          (2 : ZMod 40185923) ^ 175 = (2 : ZMod 40185923) ^ (87 + 87 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 87 * (2 : ZMod 40185923) ^ 87) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 13739226 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 40185923) ^ 350 = 30509024 := by
        calc
          (2 : ZMod 40185923) ^ 350 = (2 : ZMod 40185923) ^ (175 + 175) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 175 * (2 : ZMod 40185923) ^ 175 := by rw [pow_add]
          _ = 30509024 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 40185923) ^ 700 = 11275757 := by
        calc
          (2 : ZMod 40185923) ^ 700 = (2 : ZMod 40185923) ^ (350 + 350) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 350 * (2 : ZMod 40185923) ^ 350 := by rw [pow_add]
          _ = 11275757 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 40185923) ^ 1401 = 2602769 := by
        calc
          (2 : ZMod 40185923) ^ 1401 = (2 : ZMod 40185923) ^ (700 + 700 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 700 * (2 : ZMod 40185923) ^ 700) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 2602769 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 40185923) ^ 2803 = 8437503 := by
        calc
          (2 : ZMod 40185923) ^ 2803 = (2 : ZMod 40185923) ^ (1401 + 1401 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 1401 * (2 : ZMod 40185923) ^ 1401) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 8437503 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 40185923) ^ 5606 = 4612513 := by
        calc
          (2 : ZMod 40185923) ^ 5606 = (2 : ZMod 40185923) ^ (2803 + 2803) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 2803 * (2 : ZMod 40185923) ^ 2803 := by rw [pow_add]
          _ = 4612513 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 40185923) ^ 11212 = 4634586 := by
        calc
          (2 : ZMod 40185923) ^ 11212 = (2 : ZMod 40185923) ^ (5606 + 5606) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 5606 * (2 : ZMod 40185923) ^ 5606 := by rw [pow_add]
          _ = 4634586 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 40185923) ^ 22425 = 23095792 := by
        calc
          (2 : ZMod 40185923) ^ 22425 = (2 : ZMod 40185923) ^ (11212 + 11212 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 11212 * (2 : ZMod 40185923) ^ 11212) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 23095792 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 40185923) ^ 44850 = 3283625 := by
        calc
          (2 : ZMod 40185923) ^ 44850 = (2 : ZMod 40185923) ^ (22425 + 22425) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 22425 * (2 : ZMod 40185923) ^ 22425 := by rw [pow_add]
          _ = 3283625 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 40185923) ^ 89700 = 28698264 := by
        calc
          (2 : ZMod 40185923) ^ 89700 = (2 : ZMod 40185923) ^ (44850 + 44850) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 44850 * (2 : ZMod 40185923) ^ 44850 := by rw [pow_add]
          _ = 28698264 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 40185923) ^ 179401 = 35938161 := by
        calc
          (2 : ZMod 40185923) ^ 179401 = (2 : ZMod 40185923) ^ (89700 + 89700 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 89700 * (2 : ZMod 40185923) ^ 89700) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 35938161 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 40185923) ^ 358802 = 2581644 := by
        calc
          (2 : ZMod 40185923) ^ 358802 = (2 : ZMod 40185923) ^ (179401 + 179401) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 179401 * (2 : ZMod 40185923) ^ 179401 := by rw [pow_add]
          _ = 2581644 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 40185923) ^ 717605 = 20454526 := by
        calc
          (2 : ZMod 40185923) ^ 717605 = (2 : ZMod 40185923) ^ (358802 + 358802 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 358802 * (2 : ZMod 40185923) ^ 358802) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 20454526 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 40185923) ^ 1435211 = 28253244 := by
        calc
          (2 : ZMod 40185923) ^ 1435211 = (2 : ZMod 40185923) ^ (717605 + 717605 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 717605 * (2 : ZMod 40185923) ^ 717605) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 28253244 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 40185923) ^ 2870423 = 32522736 := by
        calc
          (2 : ZMod 40185923) ^ 2870423 = (2 : ZMod 40185923) ^ (1435211 + 1435211 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 1435211 * (2 : ZMod 40185923) ^ 1435211) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 32522736 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 40185923) ^ 5740846 = 22370455 := by
        calc
          (2 : ZMod 40185923) ^ 5740846 = (2 : ZMod 40185923) ^ (2870423 + 2870423) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 2870423 * (2 : ZMod 40185923) ^ 2870423 := by rw [pow_add]
          _ = 22370455 := by rw [factor_1_21]; decide
      change (2 : ZMod 40185923) ^ 5740846 ≠ 1
      rw [factor_1_22]
      decide
    ·
      have factor_2_0 : (2 : ZMod 40185923) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 40185923) ^ 3 = 8 := by
        calc
          (2 : ZMod 40185923) ^ 3 = (2 : ZMod 40185923) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 1 * (2 : ZMod 40185923) ^ 1) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 40185923) ^ 6 = 64 := by
        calc
          (2 : ZMod 40185923) ^ 6 = (2 : ZMod 40185923) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 3 * (2 : ZMod 40185923) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 40185923) ^ 13 = 8192 := by
        calc
          (2 : ZMod 40185923) ^ 13 = (2 : ZMod 40185923) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 6 * (2 : ZMod 40185923) ^ 6) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 40185923) ^ 26 = 26922941 := by
        calc
          (2 : ZMod 40185923) ^ 26 = (2 : ZMod 40185923) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 13 * (2 : ZMod 40185923) ^ 13 := by rw [pow_add]
          _ = 26922941 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 40185923) ^ 53 = 13760082 := by
        calc
          (2 : ZMod 40185923) ^ 53 = (2 : ZMod 40185923) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 26 * (2 : ZMod 40185923) ^ 26) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 13760082 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 40185923) ^ 106 = 22583616 := by
        calc
          (2 : ZMod 40185923) ^ 106 = (2 : ZMod 40185923) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 53 * (2 : ZMod 40185923) ^ 53 := by rw [pow_add]
          _ = 22583616 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 40185923) ^ 213 = 19204143 := by
        calc
          (2 : ZMod 40185923) ^ 213 = (2 : ZMod 40185923) ^ (106 + 106 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 106 * (2 : ZMod 40185923) ^ 106) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 19204143 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 40185923) ^ 426 = 33498089 := by
        calc
          (2 : ZMod 40185923) ^ 426 = (2 : ZMod 40185923) ^ (213 + 213) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 213 * (2 : ZMod 40185923) ^ 213 := by rw [pow_add]
          _ = 33498089 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 40185923) ^ 853 = 20951805 := by
        calc
          (2 : ZMod 40185923) ^ 853 = (2 : ZMod 40185923) ^ (426 + 426 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 426 * (2 : ZMod 40185923) ^ 426) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 20951805 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 40185923) ^ 1706 = 9587308 := by
        calc
          (2 : ZMod 40185923) ^ 1706 = (2 : ZMod 40185923) ^ (853 + 853) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 853 * (2 : ZMod 40185923) ^ 853 := by rw [pow_add]
          _ = 9587308 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 40185923) ^ 3412 = 16727424 := by
        calc
          (2 : ZMod 40185923) ^ 3412 = (2 : ZMod 40185923) ^ (1706 + 1706) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 1706 * (2 : ZMod 40185923) ^ 1706 := by rw [pow_add]
          _ = 16727424 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 40185923) ^ 6825 = 16535368 := by
        calc
          (2 : ZMod 40185923) ^ 6825 = (2 : ZMod 40185923) ^ (3412 + 3412 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 3412 * (2 : ZMod 40185923) ^ 3412) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 16535368 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 40185923) ^ 13650 = 5480719 := by
        calc
          (2 : ZMod 40185923) ^ 13650 = (2 : ZMod 40185923) ^ (6825 + 6825) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 6825 * (2 : ZMod 40185923) ^ 6825 := by rw [pow_add]
          _ = 5480719 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 40185923) ^ 27300 = 26661075 := by
        calc
          (2 : ZMod 40185923) ^ 27300 = (2 : ZMod 40185923) ^ (13650 + 13650) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 13650 * (2 : ZMod 40185923) ^ 13650 := by rw [pow_add]
          _ = 26661075 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 40185923) ^ 54600 = 14237864 := by
        calc
          (2 : ZMod 40185923) ^ 54600 = (2 : ZMod 40185923) ^ (27300 + 27300) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 27300 * (2 : ZMod 40185923) ^ 27300 := by rw [pow_add]
          _ = 14237864 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 40185923) ^ 109200 = 7914840 := by
        calc
          (2 : ZMod 40185923) ^ 109200 = (2 : ZMod 40185923) ^ (54600 + 54600) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 54600 * (2 : ZMod 40185923) ^ 54600 := by rw [pow_add]
          _ = 7914840 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 40185923) ^ 218401 = 4319411 := by
        calc
          (2 : ZMod 40185923) ^ 218401 = (2 : ZMod 40185923) ^ (109200 + 109200 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 109200 * (2 : ZMod 40185923) ^ 109200) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 4319411 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 40185923) ^ 436803 = 24158115 := by
        calc
          (2 : ZMod 40185923) ^ 436803 = (2 : ZMod 40185923) ^ (218401 + 218401 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 218401 * (2 : ZMod 40185923) ^ 218401) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 24158115 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 40185923) ^ 873607 = 13492813 := by
        calc
          (2 : ZMod 40185923) ^ 873607 = (2 : ZMod 40185923) ^ (436803 + 436803 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 436803 * (2 : ZMod 40185923) ^ 436803) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 13492813 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 40185923) ^ 1747214 = 27877303 := by
        calc
          (2 : ZMod 40185923) ^ 1747214 = (2 : ZMod 40185923) ^ (873607 + 873607) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 873607 * (2 : ZMod 40185923) ^ 873607 := by rw [pow_add]
          _ = 27877303 := by rw [factor_2_19]; decide
      change (2 : ZMod 40185923) ^ 1747214 ≠ 1
      rw [factor_2_20]
      decide
    ·
      have factor_3_0 : (2 : ZMod 40185923) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 40185923) ^ 2 = 4 := by
        calc
          (2 : ZMod 40185923) ^ 2 = (2 : ZMod 40185923) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 1 * (2 : ZMod 40185923) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 40185923) ^ 4 = 16 := by
        calc
          (2 : ZMod 40185923) ^ 4 = (2 : ZMod 40185923) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 2 * (2 : ZMod 40185923) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 40185923) ^ 8 = 256 := by
        calc
          (2 : ZMod 40185923) ^ 8 = (2 : ZMod 40185923) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 4 * (2 : ZMod 40185923) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 40185923) ^ 16 = 65536 := by
        calc
          (2 : ZMod 40185923) ^ 16 = (2 : ZMod 40185923) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 8 * (2 : ZMod 40185923) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 40185923) ^ 33 = 30332993 := by
        calc
          (2 : ZMod 40185923) ^ 33 = (2 : ZMod 40185923) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 16 * (2 : ZMod 40185923) ^ 16) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 30332993 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 40185923) ^ 66 = 1077729 := by
        calc
          (2 : ZMod 40185923) ^ 66 = (2 : ZMod 40185923) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 33 * (2 : ZMod 40185923) ^ 33 := by rw [pow_add]
          _ = 1077729 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 40185923) ^ 132 = 6064972 := by
        calc
          (2 : ZMod 40185923) ^ 132 = (2 : ZMod 40185923) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 66 * (2 : ZMod 40185923) ^ 66 := by rw [pow_add]
          _ = 6064972 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 40185923) ^ 265 = 4274313 := by
        calc
          (2 : ZMod 40185923) ^ 265 = (2 : ZMod 40185923) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 132 * (2 : ZMod 40185923) ^ 132) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 4274313 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 40185923) ^ 530 = 25448479 := by
        calc
          (2 : ZMod 40185923) ^ 530 = (2 : ZMod 40185923) ^ (265 + 265) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 265 * (2 : ZMod 40185923) ^ 265 := by rw [pow_add]
          _ = 25448479 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 40185923) ^ 1060 = 403881 := by
        calc
          (2 : ZMod 40185923) ^ 1060 = (2 : ZMod 40185923) ^ (530 + 530) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 530 * (2 : ZMod 40185923) ^ 530 := by rw [pow_add]
          _ = 403881 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 40185923) ^ 2121 = 10401408 := by
        calc
          (2 : ZMod 40185923) ^ 2121 = (2 : ZMod 40185923) ^ (1060 + 1060 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 1060 * (2 : ZMod 40185923) ^ 1060) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 10401408 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 40185923) ^ 4242 = 23135250 := by
        calc
          (2 : ZMod 40185923) ^ 4242 = (2 : ZMod 40185923) ^ (2121 + 2121) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 2121 * (2 : ZMod 40185923) ^ 2121 := by rw [pow_add]
          _ = 23135250 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 40185923) ^ 8485 = 16086321 := by
        calc
          (2 : ZMod 40185923) ^ 8485 = (2 : ZMod 40185923) ^ (4242 + 4242 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 4242 * (2 : ZMod 40185923) ^ 4242) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 16086321 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 40185923) ^ 16970 = 27110065 := by
        calc
          (2 : ZMod 40185923) ^ 16970 = (2 : ZMod 40185923) ^ (8485 + 8485) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 8485 * (2 : ZMod 40185923) ^ 8485 := by rw [pow_add]
          _ = 27110065 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 40185923) ^ 33940 = 20496139 := by
        calc
          (2 : ZMod 40185923) ^ 33940 = (2 : ZMod 40185923) ^ (16970 + 16970) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 16970 * (2 : ZMod 40185923) ^ 16970 := by rw [pow_add]
          _ = 20496139 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 40185923) ^ 67881 = 20168904 := by
        calc
          (2 : ZMod 40185923) ^ 67881 = (2 : ZMod 40185923) ^ (33940 + 33940 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 33940 * (2 : ZMod 40185923) ^ 33940) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 20168904 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 40185923) ^ 135763 = 21259673 := by
        calc
          (2 : ZMod 40185923) ^ 135763 = (2 : ZMod 40185923) ^ (67881 + 67881 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 67881 * (2 : ZMod 40185923) ^ 67881) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 21259673 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 40185923) ^ 271526 = 8000934 := by
        calc
          (2 : ZMod 40185923) ^ 271526 = (2 : ZMod 40185923) ^ (135763 + 135763) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 135763 * (2 : ZMod 40185923) ^ 135763 := by rw [pow_add]
          _ = 8000934 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 40185923) ^ 543053 = 30593938 := by
        calc
          (2 : ZMod 40185923) ^ 543053 = (2 : ZMod 40185923) ^ (271526 + 271526 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 271526 * (2 : ZMod 40185923) ^ 271526) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 30593938 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 40185923) ^ 1086106 = 23300649 := by
        calc
          (2 : ZMod 40185923) ^ 1086106 = (2 : ZMod 40185923) ^ (543053 + 543053) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 543053 * (2 : ZMod 40185923) ^ 543053 := by rw [pow_add]
          _ = 23300649 := by rw [factor_3_19]; decide
      change (2 : ZMod 40185923) ^ 1086106 ≠ 1
      rw [factor_3_20]
      decide
    ·
      have factor_4_0 : (2 : ZMod 40185923) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 40185923) ^ 2 = 4 := by
        calc
          (2 : ZMod 40185923) ^ 2 = (2 : ZMod 40185923) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 1 * (2 : ZMod 40185923) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 40185923) ^ 5 = 32 := by
        calc
          (2 : ZMod 40185923) ^ 5 = (2 : ZMod 40185923) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 2 * (2 : ZMod 40185923) ^ 2) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 40185923) ^ 11 = 2048 := by
        calc
          (2 : ZMod 40185923) ^ 11 = (2 : ZMod 40185923) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 5 * (2 : ZMod 40185923) ^ 5) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 40185923) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 40185923) ^ 23 = (2 : ZMod 40185923) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 11 * (2 : ZMod 40185923) ^ 11) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 40185923) ^ 46 = 18316747 := by
        calc
          (2 : ZMod 40185923) ^ 46 = (2 : ZMod 40185923) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 23 * (2 : ZMod 40185923) ^ 23 := by rw [pow_add]
          _ = 18316747 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 40185923) ^ 93 = 22921291 := by
        calc
          (2 : ZMod 40185923) ^ 93 = (2 : ZMod 40185923) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 46 * (2 : ZMod 40185923) ^ 46) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 22921291 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 40185923) ^ 186 = 7788748 := by
        calc
          (2 : ZMod 40185923) ^ 186 = (2 : ZMod 40185923) ^ (93 + 93) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 93 * (2 : ZMod 40185923) ^ 93 := by rw [pow_add]
          _ = 7788748 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 40185923) ^ 372 = 6418550 := by
        calc
          (2 : ZMod 40185923) ^ 372 = (2 : ZMod 40185923) ^ (186 + 186) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 186 * (2 : ZMod 40185923) ^ 186 := by rw [pow_add]
          _ = 6418550 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 40185923) ^ 744 = 19747283 := by
        calc
          (2 : ZMod 40185923) ^ 744 = (2 : ZMod 40185923) ^ (372 + 372) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 372 * (2 : ZMod 40185923) ^ 372 := by rw [pow_add]
          _ = 19747283 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 40185923) ^ 1489 = 21659605 := by
        calc
          (2 : ZMod 40185923) ^ 1489 = (2 : ZMod 40185923) ^ (744 + 744 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 744 * (2 : ZMod 40185923) ^ 744) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 21659605 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 40185923) ^ 2978 = 26655348 := by
        calc
          (2 : ZMod 40185923) ^ 2978 = (2 : ZMod 40185923) ^ (1489 + 1489) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 1489 * (2 : ZMod 40185923) ^ 1489 := by rw [pow_add]
          _ = 26655348 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 40185923) ^ 5957 = 7452594 := by
        calc
          (2 : ZMod 40185923) ^ 5957 = (2 : ZMod 40185923) ^ (2978 + 2978 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = ((2 : ZMod 40185923) ^ 2978 * (2 : ZMod 40185923) ^ 2978) * (2 : ZMod 40185923) := by rw [pow_succ, pow_add]
          _ = 7452594 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 40185923) ^ 11914 = 32406844 := by
        calc
          (2 : ZMod 40185923) ^ 11914 = (2 : ZMod 40185923) ^ (5957 + 5957) :=
            congrArg (fun n : ℕ => (2 : ZMod 40185923) ^ n) (by norm_num)
          _ = (2 : ZMod 40185923) ^ 5957 * (2 : ZMod 40185923) ^ 5957 := by rw [pow_add]
          _ = 32406844 := by rw [factor_4_12]; decide
      change (2 : ZMod 40185923) ^ 11914 ≠ 1
      rw [factor_4_13]
      decide

#print axioms prime_lucas_40185923

end TotientTailPeriodKiller
end Erdos249257
