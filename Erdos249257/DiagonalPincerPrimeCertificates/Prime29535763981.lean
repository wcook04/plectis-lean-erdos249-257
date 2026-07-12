import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_29535763981 : Nat.Prime 29535763981 := by
  apply lucas_primality 29535763981 (2 : ZMod 29535763981)
  ·
      have fermat_0 : (2 : ZMod 29535763981) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 29535763981) ^ 3 = 8 := by
        calc
          (2 : ZMod 29535763981) ^ 3 = (2 : ZMod 29535763981) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 1 * (2 : ZMod 29535763981) ^ 1) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 29535763981) ^ 6 = 64 := by
        calc
          (2 : ZMod 29535763981) ^ 6 = (2 : ZMod 29535763981) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 3 * (2 : ZMod 29535763981) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 29535763981) ^ 13 = 8192 := by
        calc
          (2 : ZMod 29535763981) ^ 13 = (2 : ZMod 29535763981) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 6 * (2 : ZMod 29535763981) ^ 6) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 29535763981) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 29535763981) ^ 27 = (2 : ZMod 29535763981) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 13 * (2 : ZMod 29535763981) ^ 13) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 29535763981) ^ 55 = 8827436852 := by
        calc
          (2 : ZMod 29535763981) ^ 55 = (2 : ZMod 29535763981) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 27 * (2 : ZMod 29535763981) ^ 27) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 8827436852 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 29535763981) ^ 110 = 18318450605 := by
        calc
          (2 : ZMod 29535763981) ^ 110 = (2 : ZMod 29535763981) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 55 * (2 : ZMod 29535763981) ^ 55 := by rw [pow_add]
          _ = 18318450605 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 29535763981) ^ 220 = 25914705796 := by
        calc
          (2 : ZMod 29535763981) ^ 220 = (2 : ZMod 29535763981) ^ (110 + 110) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 110 * (2 : ZMod 29535763981) ^ 110 := by rw [pow_add]
          _ = 25914705796 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 29535763981) ^ 440 = 5041257478 := by
        calc
          (2 : ZMod 29535763981) ^ 440 = (2 : ZMod 29535763981) ^ (220 + 220) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 220 * (2 : ZMod 29535763981) ^ 220 := by rw [pow_add]
          _ = 5041257478 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 29535763981) ^ 880 = 28475909677 := by
        calc
          (2 : ZMod 29535763981) ^ 880 = (2 : ZMod 29535763981) ^ (440 + 440) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 440 * (2 : ZMod 29535763981) ^ 440 := by rw [pow_add]
          _ = 28475909677 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 29535763981) ^ 1760 = 24789612018 := by
        calc
          (2 : ZMod 29535763981) ^ 1760 = (2 : ZMod 29535763981) ^ (880 + 880) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 880 * (2 : ZMod 29535763981) ^ 880 := by rw [pow_add]
          _ = 24789612018 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 29535763981) ^ 3520 = 11102866188 := by
        calc
          (2 : ZMod 29535763981) ^ 3520 = (2 : ZMod 29535763981) ^ (1760 + 1760) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 1760 * (2 : ZMod 29535763981) ^ 1760 := by rw [pow_add]
          _ = 11102866188 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 29535763981) ^ 7041 = 20815145028 := by
        calc
          (2 : ZMod 29535763981) ^ 7041 = (2 : ZMod 29535763981) ^ (3520 + 3520 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 3520 * (2 : ZMod 29535763981) ^ 3520) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 20815145028 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 29535763981) ^ 14083 = 16643880336 := by
        calc
          (2 : ZMod 29535763981) ^ 14083 = (2 : ZMod 29535763981) ^ (7041 + 7041 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 7041 * (2 : ZMod 29535763981) ^ 7041) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 16643880336 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 29535763981) ^ 28167 = 1794064844 := by
        calc
          (2 : ZMod 29535763981) ^ 28167 = (2 : ZMod 29535763981) ^ (14083 + 14083 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 14083 * (2 : ZMod 29535763981) ^ 14083) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 1794064844 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 29535763981) ^ 56334 = 12525366979 := by
        calc
          (2 : ZMod 29535763981) ^ 56334 = (2 : ZMod 29535763981) ^ (28167 + 28167) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 28167 * (2 : ZMod 29535763981) ^ 28167 := by rw [pow_add]
          _ = 12525366979 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 29535763981) ^ 112669 = 3999891448 := by
        calc
          (2 : ZMod 29535763981) ^ 112669 = (2 : ZMod 29535763981) ^ (56334 + 56334 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 56334 * (2 : ZMod 29535763981) ^ 56334) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 3999891448 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 29535763981) ^ 225339 = 19298561376 := by
        calc
          (2 : ZMod 29535763981) ^ 225339 = (2 : ZMod 29535763981) ^ (112669 + 112669 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 112669 * (2 : ZMod 29535763981) ^ 112669) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 19298561376 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 29535763981) ^ 450679 = 20256222884 := by
        calc
          (2 : ZMod 29535763981) ^ 450679 = (2 : ZMod 29535763981) ^ (225339 + 225339 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 225339 * (2 : ZMod 29535763981) ^ 225339) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 20256222884 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 29535763981) ^ 901359 = 1299872801 := by
        calc
          (2 : ZMod 29535763981) ^ 901359 = (2 : ZMod 29535763981) ^ (450679 + 450679 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 450679 * (2 : ZMod 29535763981) ^ 450679) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 1299872801 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 29535763981) ^ 1802719 = 26666098862 := by
        calc
          (2 : ZMod 29535763981) ^ 1802719 = (2 : ZMod 29535763981) ^ (901359 + 901359 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 901359 * (2 : ZMod 29535763981) ^ 901359) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 26666098862 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 29535763981) ^ 3605439 = 25235763810 := by
        calc
          (2 : ZMod 29535763981) ^ 3605439 = (2 : ZMod 29535763981) ^ (1802719 + 1802719 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 1802719 * (2 : ZMod 29535763981) ^ 1802719) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 25235763810 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 29535763981) ^ 7210879 = 23460275419 := by
        calc
          (2 : ZMod 29535763981) ^ 7210879 = (2 : ZMod 29535763981) ^ (3605439 + 3605439 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 3605439 * (2 : ZMod 29535763981) ^ 3605439) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 23460275419 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 29535763981) ^ 14421759 = 19461450176 := by
        calc
          (2 : ZMod 29535763981) ^ 14421759 = (2 : ZMod 29535763981) ^ (7210879 + 7210879 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 7210879 * (2 : ZMod 29535763981) ^ 7210879) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 19461450176 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 29535763981) ^ 28843519 = 8351686919 := by
        calc
          (2 : ZMod 29535763981) ^ 28843519 = (2 : ZMod 29535763981) ^ (14421759 + 14421759 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 14421759 * (2 : ZMod 29535763981) ^ 14421759) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 8351686919 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 29535763981) ^ 57687039 = 10856776777 := by
        calc
          (2 : ZMod 29535763981) ^ 57687039 = (2 : ZMod 29535763981) ^ (28843519 + 28843519 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 28843519 * (2 : ZMod 29535763981) ^ 28843519) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 10856776777 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 29535763981) ^ 115374078 = 8383962110 := by
        calc
          (2 : ZMod 29535763981) ^ 115374078 = (2 : ZMod 29535763981) ^ (57687039 + 57687039) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 57687039 * (2 : ZMod 29535763981) ^ 57687039 := by rw [pow_add]
          _ = 8383962110 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 29535763981) ^ 230748156 = 18009471486 := by
        calc
          (2 : ZMod 29535763981) ^ 230748156 = (2 : ZMod 29535763981) ^ (115374078 + 115374078) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 115374078 * (2 : ZMod 29535763981) ^ 115374078 := by rw [pow_add]
          _ = 18009471486 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 29535763981) ^ 461496312 = 27421330155 := by
        calc
          (2 : ZMod 29535763981) ^ 461496312 = (2 : ZMod 29535763981) ^ (230748156 + 230748156) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 230748156 * (2 : ZMod 29535763981) ^ 230748156 := by rw [pow_add]
          _ = 27421330155 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 29535763981) ^ 922992624 = 9047425435 := by
        calc
          (2 : ZMod 29535763981) ^ 922992624 = (2 : ZMod 29535763981) ^ (461496312 + 461496312) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 461496312 * (2 : ZMod 29535763981) ^ 461496312 := by rw [pow_add]
          _ = 9047425435 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 29535763981) ^ 1845985248 = 27294522872 := by
        calc
          (2 : ZMod 29535763981) ^ 1845985248 = (2 : ZMod 29535763981) ^ (922992624 + 922992624) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 922992624 * (2 : ZMod 29535763981) ^ 922992624 := by rw [pow_add]
          _ = 27294522872 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 29535763981) ^ 3691970497 = 7154698192 := by
        calc
          (2 : ZMod 29535763981) ^ 3691970497 = (2 : ZMod 29535763981) ^ (1845985248 + 1845985248 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 1845985248 * (2 : ZMod 29535763981) ^ 1845985248) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 7154698192 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 29535763981) ^ 7383940995 = 14309396383 := by
        calc
          (2 : ZMod 29535763981) ^ 7383940995 = (2 : ZMod 29535763981) ^ (3691970497 + 3691970497 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 3691970497 * (2 : ZMod 29535763981) ^ 3691970497) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 14309396383 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 29535763981) ^ 14767881990 = 29535763980 := by
        calc
          (2 : ZMod 29535763981) ^ 14767881990 = (2 : ZMod 29535763981) ^ (7383940995 + 7383940995) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 7383940995 * (2 : ZMod 29535763981) ^ 7383940995 := by rw [pow_add]
          _ = 29535763980 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 29535763981) ^ 29535763980 = 1 := by
        calc
          (2 : ZMod 29535763981) ^ 29535763980 = (2 : ZMod 29535763981) ^ (14767881990 + 14767881990) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 14767881990 * (2 : ZMod 29535763981) ^ 14767881990 := by rw [pow_add]
          _ = 1 := by rw [fermat_33]; decide
      simpa using fermat_34
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (29, 1), (31, 1), (547567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (29, 1), (31, 1), (547567, 1)] : List FactorBlock).map factorBlockValue).prod = 29535763981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 29535763981) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 29535763981) ^ 3 = 8 := by
        calc
          (2 : ZMod 29535763981) ^ 3 = (2 : ZMod 29535763981) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 1 * (2 : ZMod 29535763981) ^ 1) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 29535763981) ^ 6 = 64 := by
        calc
          (2 : ZMod 29535763981) ^ 6 = (2 : ZMod 29535763981) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 3 * (2 : ZMod 29535763981) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 29535763981) ^ 13 = 8192 := by
        calc
          (2 : ZMod 29535763981) ^ 13 = (2 : ZMod 29535763981) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 6 * (2 : ZMod 29535763981) ^ 6) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 29535763981) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 29535763981) ^ 27 = (2 : ZMod 29535763981) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 13 * (2 : ZMod 29535763981) ^ 13) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 29535763981) ^ 55 = 8827436852 := by
        calc
          (2 : ZMod 29535763981) ^ 55 = (2 : ZMod 29535763981) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 27 * (2 : ZMod 29535763981) ^ 27) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 8827436852 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 29535763981) ^ 110 = 18318450605 := by
        calc
          (2 : ZMod 29535763981) ^ 110 = (2 : ZMod 29535763981) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 55 * (2 : ZMod 29535763981) ^ 55 := by rw [pow_add]
          _ = 18318450605 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 29535763981) ^ 220 = 25914705796 := by
        calc
          (2 : ZMod 29535763981) ^ 220 = (2 : ZMod 29535763981) ^ (110 + 110) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 110 * (2 : ZMod 29535763981) ^ 110 := by rw [pow_add]
          _ = 25914705796 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 29535763981) ^ 440 = 5041257478 := by
        calc
          (2 : ZMod 29535763981) ^ 440 = (2 : ZMod 29535763981) ^ (220 + 220) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 220 * (2 : ZMod 29535763981) ^ 220 := by rw [pow_add]
          _ = 5041257478 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 29535763981) ^ 880 = 28475909677 := by
        calc
          (2 : ZMod 29535763981) ^ 880 = (2 : ZMod 29535763981) ^ (440 + 440) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 440 * (2 : ZMod 29535763981) ^ 440 := by rw [pow_add]
          _ = 28475909677 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 29535763981) ^ 1760 = 24789612018 := by
        calc
          (2 : ZMod 29535763981) ^ 1760 = (2 : ZMod 29535763981) ^ (880 + 880) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 880 * (2 : ZMod 29535763981) ^ 880 := by rw [pow_add]
          _ = 24789612018 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 29535763981) ^ 3520 = 11102866188 := by
        calc
          (2 : ZMod 29535763981) ^ 3520 = (2 : ZMod 29535763981) ^ (1760 + 1760) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 1760 * (2 : ZMod 29535763981) ^ 1760 := by rw [pow_add]
          _ = 11102866188 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 29535763981) ^ 7041 = 20815145028 := by
        calc
          (2 : ZMod 29535763981) ^ 7041 = (2 : ZMod 29535763981) ^ (3520 + 3520 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 3520 * (2 : ZMod 29535763981) ^ 3520) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 20815145028 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 29535763981) ^ 14083 = 16643880336 := by
        calc
          (2 : ZMod 29535763981) ^ 14083 = (2 : ZMod 29535763981) ^ (7041 + 7041 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 7041 * (2 : ZMod 29535763981) ^ 7041) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 16643880336 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 29535763981) ^ 28167 = 1794064844 := by
        calc
          (2 : ZMod 29535763981) ^ 28167 = (2 : ZMod 29535763981) ^ (14083 + 14083 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 14083 * (2 : ZMod 29535763981) ^ 14083) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 1794064844 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 29535763981) ^ 56334 = 12525366979 := by
        calc
          (2 : ZMod 29535763981) ^ 56334 = (2 : ZMod 29535763981) ^ (28167 + 28167) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 28167 * (2 : ZMod 29535763981) ^ 28167 := by rw [pow_add]
          _ = 12525366979 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 29535763981) ^ 112669 = 3999891448 := by
        calc
          (2 : ZMod 29535763981) ^ 112669 = (2 : ZMod 29535763981) ^ (56334 + 56334 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 56334 * (2 : ZMod 29535763981) ^ 56334) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 3999891448 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 29535763981) ^ 225339 = 19298561376 := by
        calc
          (2 : ZMod 29535763981) ^ 225339 = (2 : ZMod 29535763981) ^ (112669 + 112669 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 112669 * (2 : ZMod 29535763981) ^ 112669) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 19298561376 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 29535763981) ^ 450679 = 20256222884 := by
        calc
          (2 : ZMod 29535763981) ^ 450679 = (2 : ZMod 29535763981) ^ (225339 + 225339 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 225339 * (2 : ZMod 29535763981) ^ 225339) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 20256222884 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 29535763981) ^ 901359 = 1299872801 := by
        calc
          (2 : ZMod 29535763981) ^ 901359 = (2 : ZMod 29535763981) ^ (450679 + 450679 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 450679 * (2 : ZMod 29535763981) ^ 450679) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 1299872801 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 29535763981) ^ 1802719 = 26666098862 := by
        calc
          (2 : ZMod 29535763981) ^ 1802719 = (2 : ZMod 29535763981) ^ (901359 + 901359 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 901359 * (2 : ZMod 29535763981) ^ 901359) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 26666098862 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 29535763981) ^ 3605439 = 25235763810 := by
        calc
          (2 : ZMod 29535763981) ^ 3605439 = (2 : ZMod 29535763981) ^ (1802719 + 1802719 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 1802719 * (2 : ZMod 29535763981) ^ 1802719) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 25235763810 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 29535763981) ^ 7210879 = 23460275419 := by
        calc
          (2 : ZMod 29535763981) ^ 7210879 = (2 : ZMod 29535763981) ^ (3605439 + 3605439 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 3605439 * (2 : ZMod 29535763981) ^ 3605439) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 23460275419 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 29535763981) ^ 14421759 = 19461450176 := by
        calc
          (2 : ZMod 29535763981) ^ 14421759 = (2 : ZMod 29535763981) ^ (7210879 + 7210879 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 7210879 * (2 : ZMod 29535763981) ^ 7210879) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 19461450176 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 29535763981) ^ 28843519 = 8351686919 := by
        calc
          (2 : ZMod 29535763981) ^ 28843519 = (2 : ZMod 29535763981) ^ (14421759 + 14421759 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 14421759 * (2 : ZMod 29535763981) ^ 14421759) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 8351686919 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 29535763981) ^ 57687039 = 10856776777 := by
        calc
          (2 : ZMod 29535763981) ^ 57687039 = (2 : ZMod 29535763981) ^ (28843519 + 28843519 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 28843519 * (2 : ZMod 29535763981) ^ 28843519) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 10856776777 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 29535763981) ^ 115374078 = 8383962110 := by
        calc
          (2 : ZMod 29535763981) ^ 115374078 = (2 : ZMod 29535763981) ^ (57687039 + 57687039) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 57687039 * (2 : ZMod 29535763981) ^ 57687039 := by rw [pow_add]
          _ = 8383962110 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 29535763981) ^ 230748156 = 18009471486 := by
        calc
          (2 : ZMod 29535763981) ^ 230748156 = (2 : ZMod 29535763981) ^ (115374078 + 115374078) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 115374078 * (2 : ZMod 29535763981) ^ 115374078 := by rw [pow_add]
          _ = 18009471486 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 29535763981) ^ 461496312 = 27421330155 := by
        calc
          (2 : ZMod 29535763981) ^ 461496312 = (2 : ZMod 29535763981) ^ (230748156 + 230748156) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 230748156 * (2 : ZMod 29535763981) ^ 230748156 := by rw [pow_add]
          _ = 27421330155 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 29535763981) ^ 922992624 = 9047425435 := by
        calc
          (2 : ZMod 29535763981) ^ 922992624 = (2 : ZMod 29535763981) ^ (461496312 + 461496312) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 461496312 * (2 : ZMod 29535763981) ^ 461496312 := by rw [pow_add]
          _ = 9047425435 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 29535763981) ^ 1845985248 = 27294522872 := by
        calc
          (2 : ZMod 29535763981) ^ 1845985248 = (2 : ZMod 29535763981) ^ (922992624 + 922992624) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 922992624 * (2 : ZMod 29535763981) ^ 922992624 := by rw [pow_add]
          _ = 27294522872 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 29535763981) ^ 3691970497 = 7154698192 := by
        calc
          (2 : ZMod 29535763981) ^ 3691970497 = (2 : ZMod 29535763981) ^ (1845985248 + 1845985248 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 1845985248 * (2 : ZMod 29535763981) ^ 1845985248) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 7154698192 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 29535763981) ^ 7383940995 = 14309396383 := by
        calc
          (2 : ZMod 29535763981) ^ 7383940995 = (2 : ZMod 29535763981) ^ (3691970497 + 3691970497 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 3691970497 * (2 : ZMod 29535763981) ^ 3691970497) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 14309396383 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 29535763981) ^ 14767881990 = 29535763980 := by
        calc
          (2 : ZMod 29535763981) ^ 14767881990 = (2 : ZMod 29535763981) ^ (7383940995 + 7383940995) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 7383940995 * (2 : ZMod 29535763981) ^ 7383940995 := by rw [pow_add]
          _ = 29535763980 := by rw [factor_0_32]; decide
      change (2 : ZMod 29535763981) ^ 14767881990 ≠ 1
      rw [factor_0_33]
      decide
    ·
      have factor_1_0 : (2 : ZMod 29535763981) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 29535763981) ^ 2 = 4 := by
        calc
          (2 : ZMod 29535763981) ^ 2 = (2 : ZMod 29535763981) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 1 * (2 : ZMod 29535763981) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 29535763981) ^ 4 = 16 := by
        calc
          (2 : ZMod 29535763981) ^ 4 = (2 : ZMod 29535763981) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 2 * (2 : ZMod 29535763981) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 29535763981) ^ 9 = 512 := by
        calc
          (2 : ZMod 29535763981) ^ 9 = (2 : ZMod 29535763981) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 4 * (2 : ZMod 29535763981) ^ 4) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 29535763981) ^ 18 = 262144 := by
        calc
          (2 : ZMod 29535763981) ^ 18 = (2 : ZMod 29535763981) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 9 * (2 : ZMod 29535763981) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 29535763981) ^ 36 = 9647948774 := by
        calc
          (2 : ZMod 29535763981) ^ 36 = (2 : ZMod 29535763981) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 18 * (2 : ZMod 29535763981) ^ 18 := by rw [pow_add]
          _ = 9647948774 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 29535763981) ^ 73 = 21105511281 := by
        calc
          (2 : ZMod 29535763981) ^ 73 = (2 : ZMod 29535763981) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 36 * (2 : ZMod 29535763981) ^ 36) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 21105511281 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 29535763981) ^ 146 = 21215422050 := by
        calc
          (2 : ZMod 29535763981) ^ 146 = (2 : ZMod 29535763981) ^ (73 + 73) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 73 * (2 : ZMod 29535763981) ^ 73 := by rw [pow_add]
          _ = 21215422050 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 29535763981) ^ 293 = 6638464537 := by
        calc
          (2 : ZMod 29535763981) ^ 293 = (2 : ZMod 29535763981) ^ (146 + 146 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 146 * (2 : ZMod 29535763981) ^ 146) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 6638464537 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 29535763981) ^ 586 = 11382183441 := by
        calc
          (2 : ZMod 29535763981) ^ 586 = (2 : ZMod 29535763981) ^ (293 + 293) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 293 * (2 : ZMod 29535763981) ^ 293 := by rw [pow_add]
          _ = 11382183441 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 29535763981) ^ 1173 = 7968962289 := by
        calc
          (2 : ZMod 29535763981) ^ 1173 = (2 : ZMod 29535763981) ^ (586 + 586 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 586 * (2 : ZMod 29535763981) ^ 586) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 7968962289 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 29535763981) ^ 2347 = 2798057543 := by
        calc
          (2 : ZMod 29535763981) ^ 2347 = (2 : ZMod 29535763981) ^ (1173 + 1173 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 1173 * (2 : ZMod 29535763981) ^ 1173) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 2798057543 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 29535763981) ^ 4694 = 9359162985 := by
        calc
          (2 : ZMod 29535763981) ^ 4694 = (2 : ZMod 29535763981) ^ (2347 + 2347) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 2347 * (2 : ZMod 29535763981) ^ 2347 := by rw [pow_add]
          _ = 9359162985 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 29535763981) ^ 9389 = 21674435745 := by
        calc
          (2 : ZMod 29535763981) ^ 9389 = (2 : ZMod 29535763981) ^ (4694 + 4694 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 4694 * (2 : ZMod 29535763981) ^ 4694) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 21674435745 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 29535763981) ^ 18778 = 8040414606 := by
        calc
          (2 : ZMod 29535763981) ^ 18778 = (2 : ZMod 29535763981) ^ (9389 + 9389) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 9389 * (2 : ZMod 29535763981) ^ 9389 := by rw [pow_add]
          _ = 8040414606 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 29535763981) ^ 37556 = 4864476079 := by
        calc
          (2 : ZMod 29535763981) ^ 37556 = (2 : ZMod 29535763981) ^ (18778 + 18778) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 18778 * (2 : ZMod 29535763981) ^ 18778 := by rw [pow_add]
          _ = 4864476079 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 29535763981) ^ 75113 = 5611488365 := by
        calc
          (2 : ZMod 29535763981) ^ 75113 = (2 : ZMod 29535763981) ^ (37556 + 37556 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 37556 * (2 : ZMod 29535763981) ^ 37556) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 5611488365 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 29535763981) ^ 150226 = 5097210763 := by
        calc
          (2 : ZMod 29535763981) ^ 150226 = (2 : ZMod 29535763981) ^ (75113 + 75113) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 75113 * (2 : ZMod 29535763981) ^ 75113 := by rw [pow_add]
          _ = 5097210763 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 29535763981) ^ 300453 = 3261536270 := by
        calc
          (2 : ZMod 29535763981) ^ 300453 = (2 : ZMod 29535763981) ^ (150226 + 150226 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 150226 * (2 : ZMod 29535763981) ^ 150226) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 3261536270 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 29535763981) ^ 600906 = 9240996528 := by
        calc
          (2 : ZMod 29535763981) ^ 600906 = (2 : ZMod 29535763981) ^ (300453 + 300453) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 300453 * (2 : ZMod 29535763981) ^ 300453 := by rw [pow_add]
          _ = 9240996528 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 29535763981) ^ 1201813 = 28217540613 := by
        calc
          (2 : ZMod 29535763981) ^ 1201813 = (2 : ZMod 29535763981) ^ (600906 + 600906 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 600906 * (2 : ZMod 29535763981) ^ 600906) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 28217540613 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 29535763981) ^ 2403626 = 9480661091 := by
        calc
          (2 : ZMod 29535763981) ^ 2403626 = (2 : ZMod 29535763981) ^ (1201813 + 1201813) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 1201813 * (2 : ZMod 29535763981) ^ 1201813 := by rw [pow_add]
          _ = 9480661091 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 29535763981) ^ 4807253 = 254091727 := by
        calc
          (2 : ZMod 29535763981) ^ 4807253 = (2 : ZMod 29535763981) ^ (2403626 + 2403626 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 2403626 * (2 : ZMod 29535763981) ^ 2403626) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 254091727 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 29535763981) ^ 9614506 = 24814606857 := by
        calc
          (2 : ZMod 29535763981) ^ 9614506 = (2 : ZMod 29535763981) ^ (4807253 + 4807253) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 4807253 * (2 : ZMod 29535763981) ^ 4807253 := by rw [pow_add]
          _ = 24814606857 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 29535763981) ^ 19229013 = 21286352978 := by
        calc
          (2 : ZMod 29535763981) ^ 19229013 = (2 : ZMod 29535763981) ^ (9614506 + 9614506 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 9614506 * (2 : ZMod 29535763981) ^ 9614506) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 21286352978 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 29535763981) ^ 38458026 = 8793330112 := by
        calc
          (2 : ZMod 29535763981) ^ 38458026 = (2 : ZMod 29535763981) ^ (19229013 + 19229013) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 19229013 * (2 : ZMod 29535763981) ^ 19229013 := by rw [pow_add]
          _ = 8793330112 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 29535763981) ^ 76916052 = 3600621634 := by
        calc
          (2 : ZMod 29535763981) ^ 76916052 = (2 : ZMod 29535763981) ^ (38458026 + 38458026) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 38458026 * (2 : ZMod 29535763981) ^ 38458026 := by rw [pow_add]
          _ = 3600621634 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 29535763981) ^ 153832104 = 2399512774 := by
        calc
          (2 : ZMod 29535763981) ^ 153832104 = (2 : ZMod 29535763981) ^ (76916052 + 76916052) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 76916052 * (2 : ZMod 29535763981) ^ 76916052 := by rw [pow_add]
          _ = 2399512774 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 29535763981) ^ 307664208 = 8915105160 := by
        calc
          (2 : ZMod 29535763981) ^ 307664208 = (2 : ZMod 29535763981) ^ (153832104 + 153832104) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 153832104 * (2 : ZMod 29535763981) ^ 153832104 := by rw [pow_add]
          _ = 8915105160 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 29535763981) ^ 615328416 = 355590055 := by
        calc
          (2 : ZMod 29535763981) ^ 615328416 = (2 : ZMod 29535763981) ^ (307664208 + 307664208) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 307664208 * (2 : ZMod 29535763981) ^ 307664208 := by rw [pow_add]
          _ = 355590055 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 29535763981) ^ 1230656832 = 27609459089 := by
        calc
          (2 : ZMod 29535763981) ^ 1230656832 = (2 : ZMod 29535763981) ^ (615328416 + 615328416) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 615328416 * (2 : ZMod 29535763981) ^ 615328416 := by rw [pow_add]
          _ = 27609459089 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 29535763981) ^ 2461313665 = 24954820599 := by
        calc
          (2 : ZMod 29535763981) ^ 2461313665 = (2 : ZMod 29535763981) ^ (1230656832 + 1230656832 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 1230656832 * (2 : ZMod 29535763981) ^ 1230656832) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 24954820599 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 29535763981) ^ 4922627330 = 15037729981 := by
        calc
          (2 : ZMod 29535763981) ^ 4922627330 = (2 : ZMod 29535763981) ^ (2461313665 + 2461313665) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 2461313665 * (2 : ZMod 29535763981) ^ 2461313665 := by rw [pow_add]
          _ = 15037729981 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 29535763981) ^ 9845254660 = 15037729980 := by
        calc
          (2 : ZMod 29535763981) ^ 9845254660 = (2 : ZMod 29535763981) ^ (4922627330 + 4922627330) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 4922627330 * (2 : ZMod 29535763981) ^ 4922627330 := by rw [pow_add]
          _ = 15037729980 := by rw [factor_1_32]; decide
      change (2 : ZMod 29535763981) ^ 9845254660 ≠ 1
      rw [factor_1_33]
      decide
    ·
      have factor_2_0 : (2 : ZMod 29535763981) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 29535763981) ^ 2 = 4 := by
        calc
          (2 : ZMod 29535763981) ^ 2 = (2 : ZMod 29535763981) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 1 * (2 : ZMod 29535763981) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 29535763981) ^ 5 = 32 := by
        calc
          (2 : ZMod 29535763981) ^ 5 = (2 : ZMod 29535763981) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 2 * (2 : ZMod 29535763981) ^ 2) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 29535763981) ^ 11 = 2048 := by
        calc
          (2 : ZMod 29535763981) ^ 11 = (2 : ZMod 29535763981) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 5 * (2 : ZMod 29535763981) ^ 5) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 29535763981) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 29535763981) ^ 22 = (2 : ZMod 29535763981) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 11 * (2 : ZMod 29535763981) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 29535763981) ^ 44 = 18406475721 := by
        calc
          (2 : ZMod 29535763981) ^ 44 = (2 : ZMod 29535763981) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 22 * (2 : ZMod 29535763981) ^ 22 := by rw [pow_add]
          _ = 18406475721 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 29535763981) ^ 88 = 5480040693 := by
        calc
          (2 : ZMod 29535763981) ^ 88 = (2 : ZMod 29535763981) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 44 * (2 : ZMod 29535763981) ^ 44 := by rw [pow_add]
          _ = 5480040693 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 29535763981) ^ 176 = 25330484510 := by
        calc
          (2 : ZMod 29535763981) ^ 176 = (2 : ZMod 29535763981) ^ (88 + 88) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 88 * (2 : ZMod 29535763981) ^ 88 := by rw [pow_add]
          _ = 25330484510 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 29535763981) ^ 352 = 19293576809 := by
        calc
          (2 : ZMod 29535763981) ^ 352 = (2 : ZMod 29535763981) ^ (176 + 176) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 176 * (2 : ZMod 29535763981) ^ 176 := by rw [pow_add]
          _ = 19293576809 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 29535763981) ^ 704 = 13370594402 := by
        calc
          (2 : ZMod 29535763981) ^ 704 = (2 : ZMod 29535763981) ^ (352 + 352) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 352 * (2 : ZMod 29535763981) ^ 352 := by rw [pow_add]
          _ = 13370594402 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 29535763981) ^ 1408 = 8067935759 := by
        calc
          (2 : ZMod 29535763981) ^ 1408 = (2 : ZMod 29535763981) ^ (704 + 704) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 704 * (2 : ZMod 29535763981) ^ 704 := by rw [pow_add]
          _ = 8067935759 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 29535763981) ^ 2816 = 22358861552 := by
        calc
          (2 : ZMod 29535763981) ^ 2816 = (2 : ZMod 29535763981) ^ (1408 + 1408) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 1408 * (2 : ZMod 29535763981) ^ 1408 := by rw [pow_add]
          _ = 22358861552 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 29535763981) ^ 5633 = 29089651791 := by
        calc
          (2 : ZMod 29535763981) ^ 5633 = (2 : ZMod 29535763981) ^ (2816 + 2816 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 2816 * (2 : ZMod 29535763981) ^ 2816) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 29089651791 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 29535763981) ^ 11266 = 2891424741 := by
        calc
          (2 : ZMod 29535763981) ^ 11266 = (2 : ZMod 29535763981) ^ (5633 + 5633) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 5633 * (2 : ZMod 29535763981) ^ 5633 := by rw [pow_add]
          _ = 2891424741 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 29535763981) ^ 22533 = 10213937696 := by
        calc
          (2 : ZMod 29535763981) ^ 22533 = (2 : ZMod 29535763981) ^ (11266 + 11266 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 11266 * (2 : ZMod 29535763981) ^ 11266) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 10213937696 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 29535763981) ^ 45067 = 6141502721 := by
        calc
          (2 : ZMod 29535763981) ^ 45067 = (2 : ZMod 29535763981) ^ (22533 + 22533 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 22533 * (2 : ZMod 29535763981) ^ 22533) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 6141502721 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 29535763981) ^ 90135 = 28755662371 := by
        calc
          (2 : ZMod 29535763981) ^ 90135 = (2 : ZMod 29535763981) ^ (45067 + 45067 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 45067 * (2 : ZMod 29535763981) ^ 45067) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 28755662371 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 29535763981) ^ 180271 = 15922196874 := by
        calc
          (2 : ZMod 29535763981) ^ 180271 = (2 : ZMod 29535763981) ^ (90135 + 90135 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 90135 * (2 : ZMod 29535763981) ^ 90135) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 15922196874 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 29535763981) ^ 360543 = 26228271891 := by
        calc
          (2 : ZMod 29535763981) ^ 360543 = (2 : ZMod 29535763981) ^ (180271 + 180271 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 180271 * (2 : ZMod 29535763981) ^ 180271) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 26228271891 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 29535763981) ^ 721087 = 12349209513 := by
        calc
          (2 : ZMod 29535763981) ^ 721087 = (2 : ZMod 29535763981) ^ (360543 + 360543 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 360543 * (2 : ZMod 29535763981) ^ 360543) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 12349209513 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 29535763981) ^ 1442175 = 24246064425 := by
        calc
          (2 : ZMod 29535763981) ^ 1442175 = (2 : ZMod 29535763981) ^ (721087 + 721087 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 721087 * (2 : ZMod 29535763981) ^ 721087) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 24246064425 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 29535763981) ^ 2884351 = 21110595368 := by
        calc
          (2 : ZMod 29535763981) ^ 2884351 = (2 : ZMod 29535763981) ^ (1442175 + 1442175 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 1442175 * (2 : ZMod 29535763981) ^ 1442175) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 21110595368 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 29535763981) ^ 5768703 = 17332283274 := by
        calc
          (2 : ZMod 29535763981) ^ 5768703 = (2 : ZMod 29535763981) ^ (2884351 + 2884351 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 2884351 * (2 : ZMod 29535763981) ^ 2884351) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 17332283274 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 29535763981) ^ 11537407 = 5678737445 := by
        calc
          (2 : ZMod 29535763981) ^ 11537407 = (2 : ZMod 29535763981) ^ (5768703 + 5768703 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 5768703 * (2 : ZMod 29535763981) ^ 5768703) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 5678737445 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 29535763981) ^ 23074815 = 23831649205 := by
        calc
          (2 : ZMod 29535763981) ^ 23074815 = (2 : ZMod 29535763981) ^ (11537407 + 11537407 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 11537407 * (2 : ZMod 29535763981) ^ 11537407) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 23831649205 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 29535763981) ^ 46149631 = 6342302057 := by
        calc
          (2 : ZMod 29535763981) ^ 46149631 = (2 : ZMod 29535763981) ^ (23074815 + 23074815 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 23074815 * (2 : ZMod 29535763981) ^ 23074815) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 6342302057 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 29535763981) ^ 92299262 = 20009355949 := by
        calc
          (2 : ZMod 29535763981) ^ 92299262 = (2 : ZMod 29535763981) ^ (46149631 + 46149631) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 46149631 * (2 : ZMod 29535763981) ^ 46149631 := by rw [pow_add]
          _ = 20009355949 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 29535763981) ^ 184598524 = 25898187254 := by
        calc
          (2 : ZMod 29535763981) ^ 184598524 = (2 : ZMod 29535763981) ^ (92299262 + 92299262) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 92299262 * (2 : ZMod 29535763981) ^ 92299262 := by rw [pow_add]
          _ = 25898187254 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 29535763981) ^ 369197049 = 24699814654 := by
        calc
          (2 : ZMod 29535763981) ^ 369197049 = (2 : ZMod 29535763981) ^ (184598524 + 184598524 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 184598524 * (2 : ZMod 29535763981) ^ 184598524) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 24699814654 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 29535763981) ^ 738394099 = 17959550373 := by
        calc
          (2 : ZMod 29535763981) ^ 738394099 = (2 : ZMod 29535763981) ^ (369197049 + 369197049 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 369197049 * (2 : ZMod 29535763981) ^ 369197049) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 17959550373 := by rw [factor_2_28]; decide
      have factor_2_30 : (2 : ZMod 29535763981) ^ 1476788199 = 12409997143 := by
        calc
          (2 : ZMod 29535763981) ^ 1476788199 = (2 : ZMod 29535763981) ^ (738394099 + 738394099 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 738394099 * (2 : ZMod 29535763981) ^ 738394099) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 12409997143 := by rw [factor_2_29]; decide
      have factor_2_31 : (2 : ZMod 29535763981) ^ 2953576398 = 8510258217 := by
        calc
          (2 : ZMod 29535763981) ^ 2953576398 = (2 : ZMod 29535763981) ^ (1476788199 + 1476788199) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 1476788199 * (2 : ZMod 29535763981) ^ 1476788199 := by rw [pow_add]
          _ = 8510258217 := by rw [factor_2_30]; decide
      have factor_2_32 : (2 : ZMod 29535763981) ^ 5907152796 = 23711601334 := by
        calc
          (2 : ZMod 29535763981) ^ 5907152796 = (2 : ZMod 29535763981) ^ (2953576398 + 2953576398) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 2953576398 * (2 : ZMod 29535763981) ^ 2953576398 := by rw [pow_add]
          _ = 23711601334 := by rw [factor_2_31]; decide
      change (2 : ZMod 29535763981) ^ 5907152796 ≠ 1
      rw [factor_2_32]
      decide
    ·
      have factor_3_0 : (2 : ZMod 29535763981) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 29535763981) ^ 3 = 8 := by
        calc
          (2 : ZMod 29535763981) ^ 3 = (2 : ZMod 29535763981) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 1 * (2 : ZMod 29535763981) ^ 1) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 29535763981) ^ 7 = 128 := by
        calc
          (2 : ZMod 29535763981) ^ 7 = (2 : ZMod 29535763981) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 3 * (2 : ZMod 29535763981) ^ 3) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 29535763981) ^ 15 = 32768 := by
        calc
          (2 : ZMod 29535763981) ^ 15 = (2 : ZMod 29535763981) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 7 * (2 : ZMod 29535763981) ^ 7) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 29535763981) ^ 30 = 1073741824 := by
        calc
          (2 : ZMod 29535763981) ^ 30 = (2 : ZMod 29535763981) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 15 * (2 : ZMod 29535763981) ^ 15 := by rw [pow_add]
          _ = 1073741824 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 29535763981) ^ 60 = 16656103435 := by
        calc
          (2 : ZMod 29535763981) ^ 60 = (2 : ZMod 29535763981) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 30 * (2 : ZMod 29535763981) ^ 30 := by rw [pow_add]
          _ = 16656103435 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 29535763981) ^ 121 = 5766583170 := by
        calc
          (2 : ZMod 29535763981) ^ 121 = (2 : ZMod 29535763981) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 60 * (2 : ZMod 29535763981) ^ 60) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 5766583170 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 29535763981) ^ 242 = 2653203618 := by
        calc
          (2 : ZMod 29535763981) ^ 242 = (2 : ZMod 29535763981) ^ (121 + 121) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 121 * (2 : ZMod 29535763981) ^ 121 := by rw [pow_add]
          _ = 2653203618 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 29535763981) ^ 485 = 3497860799 := by
        calc
          (2 : ZMod 29535763981) ^ 485 = (2 : ZMod 29535763981) ^ (242 + 242 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 242 * (2 : ZMod 29535763981) ^ 242) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 3497860799 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 29535763981) ^ 971 = 18249126861 := by
        calc
          (2 : ZMod 29535763981) ^ 971 = (2 : ZMod 29535763981) ^ (485 + 485 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 485 * (2 : ZMod 29535763981) ^ 485) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 18249126861 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 29535763981) ^ 1942 = 16468325349 := by
        calc
          (2 : ZMod 29535763981) ^ 1942 = (2 : ZMod 29535763981) ^ (971 + 971) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 971 * (2 : ZMod 29535763981) ^ 971 := by rw [pow_add]
          _ = 16468325349 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 29535763981) ^ 3885 = 25011456833 := by
        calc
          (2 : ZMod 29535763981) ^ 3885 = (2 : ZMod 29535763981) ^ (1942 + 1942 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 1942 * (2 : ZMod 29535763981) ^ 1942) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 25011456833 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 29535763981) ^ 7770 = 95054692 := by
        calc
          (2 : ZMod 29535763981) ^ 7770 = (2 : ZMod 29535763981) ^ (3885 + 3885) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 3885 * (2 : ZMod 29535763981) ^ 3885 := by rw [pow_add]
          _ = 95054692 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 29535763981) ^ 15540 = 20304495211 := by
        calc
          (2 : ZMod 29535763981) ^ 15540 = (2 : ZMod 29535763981) ^ (7770 + 7770) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 7770 * (2 : ZMod 29535763981) ^ 7770 := by rw [pow_add]
          _ = 20304495211 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 29535763981) ^ 31081 = 234839258 := by
        calc
          (2 : ZMod 29535763981) ^ 31081 = (2 : ZMod 29535763981) ^ (15540 + 15540 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 15540 * (2 : ZMod 29535763981) ^ 15540) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 234839258 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 29535763981) ^ 62162 = 3235027554 := by
        calc
          (2 : ZMod 29535763981) ^ 62162 = (2 : ZMod 29535763981) ^ (31081 + 31081) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 31081 * (2 : ZMod 29535763981) ^ 31081 := by rw [pow_add]
          _ = 3235027554 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 29535763981) ^ 124325 = 22159260702 := by
        calc
          (2 : ZMod 29535763981) ^ 124325 = (2 : ZMod 29535763981) ^ (62162 + 62162 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 62162 * (2 : ZMod 29535763981) ^ 62162) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 22159260702 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 29535763981) ^ 248651 = 9350069695 := by
        calc
          (2 : ZMod 29535763981) ^ 248651 = (2 : ZMod 29535763981) ^ (124325 + 124325 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 124325 * (2 : ZMod 29535763981) ^ 124325) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 9350069695 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 29535763981) ^ 497302 = 28703117067 := by
        calc
          (2 : ZMod 29535763981) ^ 497302 = (2 : ZMod 29535763981) ^ (248651 + 248651) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 248651 * (2 : ZMod 29535763981) ^ 248651 := by rw [pow_add]
          _ = 28703117067 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 29535763981) ^ 994604 = 9418727469 := by
        calc
          (2 : ZMod 29535763981) ^ 994604 = (2 : ZMod 29535763981) ^ (497302 + 497302) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 497302 * (2 : ZMod 29535763981) ^ 497302 := by rw [pow_add]
          _ = 9418727469 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 29535763981) ^ 1989208 = 11721782152 := by
        calc
          (2 : ZMod 29535763981) ^ 1989208 = (2 : ZMod 29535763981) ^ (994604 + 994604) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 994604 * (2 : ZMod 29535763981) ^ 994604 := by rw [pow_add]
          _ = 11721782152 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 29535763981) ^ 3978416 = 19165616222 := by
        calc
          (2 : ZMod 29535763981) ^ 3978416 = (2 : ZMod 29535763981) ^ (1989208 + 1989208) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 1989208 * (2 : ZMod 29535763981) ^ 1989208 := by rw [pow_add]
          _ = 19165616222 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 29535763981) ^ 7956832 = 24540393529 := by
        calc
          (2 : ZMod 29535763981) ^ 7956832 = (2 : ZMod 29535763981) ^ (3978416 + 3978416) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 3978416 * (2 : ZMod 29535763981) ^ 3978416 := by rw [pow_add]
          _ = 24540393529 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 29535763981) ^ 15913665 = 24481645222 := by
        calc
          (2 : ZMod 29535763981) ^ 15913665 = (2 : ZMod 29535763981) ^ (7956832 + 7956832 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 7956832 * (2 : ZMod 29535763981) ^ 7956832) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 24481645222 := by rw [factor_3_22]; decide
      have factor_3_24 : (2 : ZMod 29535763981) ^ 31827331 = 20910909 := by
        calc
          (2 : ZMod 29535763981) ^ 31827331 = (2 : ZMod 29535763981) ^ (15913665 + 15913665 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 15913665 * (2 : ZMod 29535763981) ^ 15913665) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 20910909 := by rw [factor_3_23]; decide
      have factor_3_25 : (2 : ZMod 29535763981) ^ 63654663 = 7794699133 := by
        calc
          (2 : ZMod 29535763981) ^ 63654663 = (2 : ZMod 29535763981) ^ (31827331 + 31827331 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 31827331 * (2 : ZMod 29535763981) ^ 31827331) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 7794699133 := by rw [factor_3_24]; decide
      have factor_3_26 : (2 : ZMod 29535763981) ^ 127309327 = 27515701398 := by
        calc
          (2 : ZMod 29535763981) ^ 127309327 = (2 : ZMod 29535763981) ^ (63654663 + 63654663 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 63654663 * (2 : ZMod 29535763981) ^ 63654663) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 27515701398 := by rw [factor_3_25]; decide
      have factor_3_27 : (2 : ZMod 29535763981) ^ 254618655 = 3878465081 := by
        calc
          (2 : ZMod 29535763981) ^ 254618655 = (2 : ZMod 29535763981) ^ (127309327 + 127309327 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 127309327 * (2 : ZMod 29535763981) ^ 127309327) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 3878465081 := by rw [factor_3_26]; decide
      have factor_3_28 : (2 : ZMod 29535763981) ^ 509237310 = 8171945460 := by
        calc
          (2 : ZMod 29535763981) ^ 509237310 = (2 : ZMod 29535763981) ^ (254618655 + 254618655) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 254618655 * (2 : ZMod 29535763981) ^ 254618655 := by rw [pow_add]
          _ = 8171945460 := by rw [factor_3_27]; decide
      have factor_3_29 : (2 : ZMod 29535763981) ^ 1018474620 = 796540039 := by
        calc
          (2 : ZMod 29535763981) ^ 1018474620 = (2 : ZMod 29535763981) ^ (509237310 + 509237310) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 509237310 * (2 : ZMod 29535763981) ^ 509237310 := by rw [pow_add]
          _ = 796540039 := by rw [factor_3_28]; decide
      change (2 : ZMod 29535763981) ^ 1018474620 ≠ 1
      rw [factor_3_29]
      decide
    ·
      have factor_4_0 : (2 : ZMod 29535763981) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 29535763981) ^ 3 = 8 := by
        calc
          (2 : ZMod 29535763981) ^ 3 = (2 : ZMod 29535763981) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 1 * (2 : ZMod 29535763981) ^ 1) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 29535763981) ^ 7 = 128 := by
        calc
          (2 : ZMod 29535763981) ^ 7 = (2 : ZMod 29535763981) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 3 * (2 : ZMod 29535763981) ^ 3) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 29535763981) ^ 14 = 16384 := by
        calc
          (2 : ZMod 29535763981) ^ 14 = (2 : ZMod 29535763981) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 7 * (2 : ZMod 29535763981) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 29535763981) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 29535763981) ^ 28 = (2 : ZMod 29535763981) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 14 * (2 : ZMod 29535763981) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 29535763981) ^ 56 = 17654873704 := by
        calc
          (2 : ZMod 29535763981) ^ 56 = (2 : ZMod 29535763981) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 28 * (2 : ZMod 29535763981) ^ 28 := by rw [pow_add]
          _ = 17654873704 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 29535763981) ^ 113 = 28404548916 := by
        calc
          (2 : ZMod 29535763981) ^ 113 = (2 : ZMod 29535763981) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 56 * (2 : ZMod 29535763981) ^ 56) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 28404548916 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 29535763981) ^ 227 = 9076776016 := by
        calc
          (2 : ZMod 29535763981) ^ 227 = (2 : ZMod 29535763981) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 113 * (2 : ZMod 29535763981) ^ 113) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 9076776016 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 29535763981) ^ 454 = 13966428676 := by
        calc
          (2 : ZMod 29535763981) ^ 454 = (2 : ZMod 29535763981) ^ (227 + 227) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 227 * (2 : ZMod 29535763981) ^ 227 := by rw [pow_add]
          _ = 13966428676 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 29535763981) ^ 908 = 5229316370 := by
        calc
          (2 : ZMod 29535763981) ^ 908 = (2 : ZMod 29535763981) ^ (454 + 454) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 454 * (2 : ZMod 29535763981) ^ 454 := by rw [pow_add]
          _ = 5229316370 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 29535763981) ^ 1817 = 29378738341 := by
        calc
          (2 : ZMod 29535763981) ^ 1817 = (2 : ZMod 29535763981) ^ (908 + 908 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 908 * (2 : ZMod 29535763981) ^ 908) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 29378738341 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 29535763981) ^ 3634 = 5130791180 := by
        calc
          (2 : ZMod 29535763981) ^ 3634 = (2 : ZMod 29535763981) ^ (1817 + 1817) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 1817 * (2 : ZMod 29535763981) ^ 1817 := by rw [pow_add]
          _ = 5130791180 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 29535763981) ^ 7269 = 24487700786 := by
        calc
          (2 : ZMod 29535763981) ^ 7269 = (2 : ZMod 29535763981) ^ (3634 + 3634 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 3634 * (2 : ZMod 29535763981) ^ 3634) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 24487700786 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 29535763981) ^ 14538 = 20702164627 := by
        calc
          (2 : ZMod 29535763981) ^ 14538 = (2 : ZMod 29535763981) ^ (7269 + 7269) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 7269 * (2 : ZMod 29535763981) ^ 7269 := by rw [pow_add]
          _ = 20702164627 := by rw [factor_4_12]; decide
      have factor_4_14 : (2 : ZMod 29535763981) ^ 29076 = 245231022 := by
        calc
          (2 : ZMod 29535763981) ^ 29076 = (2 : ZMod 29535763981) ^ (14538 + 14538) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 14538 * (2 : ZMod 29535763981) ^ 14538 := by rw [pow_add]
          _ = 245231022 := by rw [factor_4_13]; decide
      have factor_4_15 : (2 : ZMod 29535763981) ^ 58152 = 12537226688 := by
        calc
          (2 : ZMod 29535763981) ^ 58152 = (2 : ZMod 29535763981) ^ (29076 + 29076) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 29076 * (2 : ZMod 29535763981) ^ 29076 := by rw [pow_add]
          _ = 12537226688 := by rw [factor_4_14]; decide
      have factor_4_16 : (2 : ZMod 29535763981) ^ 116304 = 18564120343 := by
        calc
          (2 : ZMod 29535763981) ^ 116304 = (2 : ZMod 29535763981) ^ (58152 + 58152) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 58152 * (2 : ZMod 29535763981) ^ 58152 := by rw [pow_add]
          _ = 18564120343 := by rw [factor_4_15]; decide
      have factor_4_17 : (2 : ZMod 29535763981) ^ 232609 = 1617382373 := by
        calc
          (2 : ZMod 29535763981) ^ 232609 = (2 : ZMod 29535763981) ^ (116304 + 116304 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 116304 * (2 : ZMod 29535763981) ^ 116304) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 1617382373 := by rw [factor_4_16]; decide
      have factor_4_18 : (2 : ZMod 29535763981) ^ 465218 = 10575368535 := by
        calc
          (2 : ZMod 29535763981) ^ 465218 = (2 : ZMod 29535763981) ^ (232609 + 232609) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 232609 * (2 : ZMod 29535763981) ^ 232609 := by rw [pow_add]
          _ = 10575368535 := by rw [factor_4_17]; decide
      have factor_4_19 : (2 : ZMod 29535763981) ^ 930436 = 3730913906 := by
        calc
          (2 : ZMod 29535763981) ^ 930436 = (2 : ZMod 29535763981) ^ (465218 + 465218) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 465218 * (2 : ZMod 29535763981) ^ 465218 := by rw [pow_add]
          _ = 3730913906 := by rw [factor_4_18]; decide
      have factor_4_20 : (2 : ZMod 29535763981) ^ 1860872 = 24951159545 := by
        calc
          (2 : ZMod 29535763981) ^ 1860872 = (2 : ZMod 29535763981) ^ (930436 + 930436) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 930436 * (2 : ZMod 29535763981) ^ 930436 := by rw [pow_add]
          _ = 24951159545 := by rw [factor_4_19]; decide
      have factor_4_21 : (2 : ZMod 29535763981) ^ 3721744 = 28615960034 := by
        calc
          (2 : ZMod 29535763981) ^ 3721744 = (2 : ZMod 29535763981) ^ (1860872 + 1860872) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 1860872 * (2 : ZMod 29535763981) ^ 1860872 := by rw [pow_add]
          _ = 28615960034 := by rw [factor_4_20]; decide
      have factor_4_22 : (2 : ZMod 29535763981) ^ 7443488 = 12523781658 := by
        calc
          (2 : ZMod 29535763981) ^ 7443488 = (2 : ZMod 29535763981) ^ (3721744 + 3721744) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 3721744 * (2 : ZMod 29535763981) ^ 3721744 := by rw [pow_add]
          _ = 12523781658 := by rw [factor_4_21]; decide
      have factor_4_23 : (2 : ZMod 29535763981) ^ 14886977 = 26898197342 := by
        calc
          (2 : ZMod 29535763981) ^ 14886977 = (2 : ZMod 29535763981) ^ (7443488 + 7443488 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 7443488 * (2 : ZMod 29535763981) ^ 7443488) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 26898197342 := by rw [factor_4_22]; decide
      have factor_4_24 : (2 : ZMod 29535763981) ^ 29773955 = 13842493028 := by
        calc
          (2 : ZMod 29535763981) ^ 29773955 = (2 : ZMod 29535763981) ^ (14886977 + 14886977 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 14886977 * (2 : ZMod 29535763981) ^ 14886977) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 13842493028 := by rw [factor_4_23]; decide
      have factor_4_25 : (2 : ZMod 29535763981) ^ 59547911 = 18708207233 := by
        calc
          (2 : ZMod 29535763981) ^ 59547911 = (2 : ZMod 29535763981) ^ (29773955 + 29773955 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 29773955 * (2 : ZMod 29535763981) ^ 29773955) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 18708207233 := by rw [factor_4_24]; decide
      have factor_4_26 : (2 : ZMod 29535763981) ^ 119095822 = 16813111815 := by
        calc
          (2 : ZMod 29535763981) ^ 119095822 = (2 : ZMod 29535763981) ^ (59547911 + 59547911) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 59547911 * (2 : ZMod 29535763981) ^ 59547911 := by rw [pow_add]
          _ = 16813111815 := by rw [factor_4_25]; decide
      have factor_4_27 : (2 : ZMod 29535763981) ^ 238191645 = 17110273293 := by
        calc
          (2 : ZMod 29535763981) ^ 238191645 = (2 : ZMod 29535763981) ^ (119095822 + 119095822 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 119095822 * (2 : ZMod 29535763981) ^ 119095822) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 17110273293 := by rw [factor_4_26]; decide
      have factor_4_28 : (2 : ZMod 29535763981) ^ 476383290 = 9318875706 := by
        calc
          (2 : ZMod 29535763981) ^ 476383290 = (2 : ZMod 29535763981) ^ (238191645 + 238191645) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 238191645 * (2 : ZMod 29535763981) ^ 238191645 := by rw [pow_add]
          _ = 9318875706 := by rw [factor_4_27]; decide
      have factor_4_29 : (2 : ZMod 29535763981) ^ 952766580 = 24818398053 := by
        calc
          (2 : ZMod 29535763981) ^ 952766580 = (2 : ZMod 29535763981) ^ (476383290 + 476383290) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 476383290 * (2 : ZMod 29535763981) ^ 476383290 := by rw [pow_add]
          _ = 24818398053 := by rw [factor_4_28]; decide
      change (2 : ZMod 29535763981) ^ 952766580 ≠ 1
      rw [factor_4_29]
      decide
    ·
      have factor_5_0 : (2 : ZMod 29535763981) ^ 1 = 2 := by norm_num
      have factor_5_1 : (2 : ZMod 29535763981) ^ 3 = 8 := by
        calc
          (2 : ZMod 29535763981) ^ 3 = (2 : ZMod 29535763981) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 1 * (2 : ZMod 29535763981) ^ 1) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_5_0]; decide
      have factor_5_2 : (2 : ZMod 29535763981) ^ 6 = 64 := by
        calc
          (2 : ZMod 29535763981) ^ 6 = (2 : ZMod 29535763981) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 3 * (2 : ZMod 29535763981) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_5_1]; decide
      have factor_5_3 : (2 : ZMod 29535763981) ^ 13 = 8192 := by
        calc
          (2 : ZMod 29535763981) ^ 13 = (2 : ZMod 29535763981) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 6 * (2 : ZMod 29535763981) ^ 6) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_5_2]; decide
      have factor_5_4 : (2 : ZMod 29535763981) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 29535763981) ^ 26 = (2 : ZMod 29535763981) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 13 * (2 : ZMod 29535763981) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [factor_5_3]; decide
      have factor_5_5 : (2 : ZMod 29535763981) ^ 52 = 15871311597 := by
        calc
          (2 : ZMod 29535763981) ^ 52 = (2 : ZMod 29535763981) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 26 * (2 : ZMod 29535763981) ^ 26 := by rw [pow_add]
          _ = 15871311597 := by rw [factor_5_4]; decide
      have factor_5_6 : (2 : ZMod 29535763981) ^ 105 = 29185222938 := by
        calc
          (2 : ZMod 29535763981) ^ 105 = (2 : ZMod 29535763981) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 52 * (2 : ZMod 29535763981) ^ 52) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 29185222938 := by rw [factor_5_5]; decide
      have factor_5_7 : (2 : ZMod 29535763981) ^ 210 = 25292230423 := by
        calc
          (2 : ZMod 29535763981) ^ 210 = (2 : ZMod 29535763981) ^ (105 + 105) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 105 * (2 : ZMod 29535763981) ^ 105 := by rw [pow_add]
          _ = 25292230423 := by rw [factor_5_6]; decide
      have factor_5_8 : (2 : ZMod 29535763981) ^ 421 = 16835724081 := by
        calc
          (2 : ZMod 29535763981) ^ 421 = (2 : ZMod 29535763981) ^ (210 + 210 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 210 * (2 : ZMod 29535763981) ^ 210) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 16835724081 := by rw [factor_5_7]; decide
      have factor_5_9 : (2 : ZMod 29535763981) ^ 842 = 23484021583 := by
        calc
          (2 : ZMod 29535763981) ^ 842 = (2 : ZMod 29535763981) ^ (421 + 421) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 421 * (2 : ZMod 29535763981) ^ 421 := by rw [pow_add]
          _ = 23484021583 := by rw [factor_5_8]; decide
      have factor_5_10 : (2 : ZMod 29535763981) ^ 1685 = 28790565339 := by
        calc
          (2 : ZMod 29535763981) ^ 1685 = (2 : ZMod 29535763981) ^ (842 + 842 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 842 * (2 : ZMod 29535763981) ^ 842) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 28790565339 := by rw [factor_5_9]; decide
      have factor_5_11 : (2 : ZMod 29535763981) ^ 3371 = 15585134914 := by
        calc
          (2 : ZMod 29535763981) ^ 3371 = (2 : ZMod 29535763981) ^ (1685 + 1685 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 1685 * (2 : ZMod 29535763981) ^ 1685) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 15585134914 := by rw [factor_5_10]; decide
      have factor_5_12 : (2 : ZMod 29535763981) ^ 6742 = 1451721355 := by
        calc
          (2 : ZMod 29535763981) ^ 6742 = (2 : ZMod 29535763981) ^ (3371 + 3371) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 3371 * (2 : ZMod 29535763981) ^ 3371 := by rw [pow_add]
          _ = 1451721355 := by rw [factor_5_11]; decide
      have factor_5_13 : (2 : ZMod 29535763981) ^ 13485 = 8461288031 := by
        calc
          (2 : ZMod 29535763981) ^ 13485 = (2 : ZMod 29535763981) ^ (6742 + 6742 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = ((2 : ZMod 29535763981) ^ 6742 * (2 : ZMod 29535763981) ^ 6742) * (2 : ZMod 29535763981) := by rw [pow_succ, pow_add]
          _ = 8461288031 := by rw [factor_5_12]; decide
      have factor_5_14 : (2 : ZMod 29535763981) ^ 26970 = 21317442766 := by
        calc
          (2 : ZMod 29535763981) ^ 26970 = (2 : ZMod 29535763981) ^ (13485 + 13485) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 13485 * (2 : ZMod 29535763981) ^ 13485 := by rw [pow_add]
          _ = 21317442766 := by rw [factor_5_13]; decide
      have factor_5_15 : (2 : ZMod 29535763981) ^ 53940 = 13650638870 := by
        calc
          (2 : ZMod 29535763981) ^ 53940 = (2 : ZMod 29535763981) ^ (26970 + 26970) :=
            congrArg (fun n : ℕ => (2 : ZMod 29535763981) ^ n) (by norm_num)
          _ = (2 : ZMod 29535763981) ^ 26970 * (2 : ZMod 29535763981) ^ 26970 := by rw [pow_add]
          _ = 13650638870 := by rw [factor_5_14]; decide
      change (2 : ZMod 29535763981) ^ 53940 ≠ 1
      rw [factor_5_15]
      decide

#print axioms prime_lucas_29535763981

end TotientTailPeriodKiller
end Erdos249257
