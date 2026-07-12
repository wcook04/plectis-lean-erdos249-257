import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_72644472739 : Nat.Prime 72644472739 := by
  apply lucas_primality 72644472739 (3 : ZMod 72644472739)
  ·
      have fermat_0 : (3 : ZMod 72644472739) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 72644472739) ^ 2 = 9 := by
        calc
          (3 : ZMod 72644472739) ^ 2 = (3 : ZMod 72644472739) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 1 * (3 : ZMod 72644472739) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 72644472739) ^ 4 = 81 := by
        calc
          (3 : ZMod 72644472739) ^ 4 = (3 : ZMod 72644472739) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 2 * (3 : ZMod 72644472739) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 72644472739) ^ 8 = 6561 := by
        calc
          (3 : ZMod 72644472739) ^ 8 = (3 : ZMod 72644472739) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 4 * (3 : ZMod 72644472739) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 72644472739) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 72644472739) ^ 16 = (3 : ZMod 72644472739) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 8 * (3 : ZMod 72644472739) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 72644472739) ^ 33 = 14934676287 := by
        calc
          (3 : ZMod 72644472739) ^ 33 = (3 : ZMod 72644472739) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 16 * (3 : ZMod 72644472739) ^ 16) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 14934676287 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 72644472739) ^ 67 = 54130115420 := by
        calc
          (3 : ZMod 72644472739) ^ 67 = (3 : ZMod 72644472739) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 33 * (3 : ZMod 72644472739) ^ 33) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 54130115420 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 72644472739) ^ 135 = 26978468017 := by
        calc
          (3 : ZMod 72644472739) ^ 135 = (3 : ZMod 72644472739) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 67 * (3 : ZMod 72644472739) ^ 67) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 26978468017 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 72644472739) ^ 270 = 29879360816 := by
        calc
          (3 : ZMod 72644472739) ^ 270 = (3 : ZMod 72644472739) ^ (135 + 135) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 135 * (3 : ZMod 72644472739) ^ 135 := by rw [pow_add]
          _ = 29879360816 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 72644472739) ^ 541 = 55624504095 := by
        calc
          (3 : ZMod 72644472739) ^ 541 = (3 : ZMod 72644472739) ^ (270 + 270 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 270 * (3 : ZMod 72644472739) ^ 270) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 55624504095 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 72644472739) ^ 1082 = 57614801876 := by
        calc
          (3 : ZMod 72644472739) ^ 1082 = (3 : ZMod 72644472739) ^ (541 + 541) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 541 * (3 : ZMod 72644472739) ^ 541 := by rw [pow_add]
          _ = 57614801876 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 72644472739) ^ 2164 = 35637304797 := by
        calc
          (3 : ZMod 72644472739) ^ 2164 = (3 : ZMod 72644472739) ^ (1082 + 1082) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 1082 * (3 : ZMod 72644472739) ^ 1082 := by rw [pow_add]
          _ = 35637304797 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 72644472739) ^ 4329 = 11823358265 := by
        calc
          (3 : ZMod 72644472739) ^ 4329 = (3 : ZMod 72644472739) ^ (2164 + 2164 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 2164 * (3 : ZMod 72644472739) ^ 2164) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 11823358265 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 72644472739) ^ 8659 = 3361450934 := by
        calc
          (3 : ZMod 72644472739) ^ 8659 = (3 : ZMod 72644472739) ^ (4329 + 4329 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 4329 * (3 : ZMod 72644472739) ^ 4329) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 3361450934 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 72644472739) ^ 17319 = 29392888791 := by
        calc
          (3 : ZMod 72644472739) ^ 17319 = (3 : ZMod 72644472739) ^ (8659 + 8659 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 8659 * (3 : ZMod 72644472739) ^ 8659) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 29392888791 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 72644472739) ^ 34639 = 18581158543 := by
        calc
          (3 : ZMod 72644472739) ^ 34639 = (3 : ZMod 72644472739) ^ (17319 + 17319 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 17319 * (3 : ZMod 72644472739) ^ 17319) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 18581158543 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 72644472739) ^ 69279 = 54376492856 := by
        calc
          (3 : ZMod 72644472739) ^ 69279 = (3 : ZMod 72644472739) ^ (34639 + 34639 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 34639 * (3 : ZMod 72644472739) ^ 34639) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 54376492856 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 72644472739) ^ 138558 = 24717591940 := by
        calc
          (3 : ZMod 72644472739) ^ 138558 = (3 : ZMod 72644472739) ^ (69279 + 69279) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 69279 * (3 : ZMod 72644472739) ^ 69279 := by rw [pow_add]
          _ = 24717591940 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 72644472739) ^ 277116 = 15987442187 := by
        calc
          (3 : ZMod 72644472739) ^ 277116 = (3 : ZMod 72644472739) ^ (138558 + 138558) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 138558 * (3 : ZMod 72644472739) ^ 138558 := by rw [pow_add]
          _ = 15987442187 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 72644472739) ^ 554233 = 19126652894 := by
        calc
          (3 : ZMod 72644472739) ^ 554233 = (3 : ZMod 72644472739) ^ (277116 + 277116 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 277116 * (3 : ZMod 72644472739) ^ 277116) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 19126652894 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 72644472739) ^ 1108466 = 63748563764 := by
        calc
          (3 : ZMod 72644472739) ^ 1108466 = (3 : ZMod 72644472739) ^ (554233 + 554233) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 554233 * (3 : ZMod 72644472739) ^ 554233 := by rw [pow_add]
          _ = 63748563764 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 72644472739) ^ 2216933 = 64611853195 := by
        calc
          (3 : ZMod 72644472739) ^ 2216933 = (3 : ZMod 72644472739) ^ (1108466 + 1108466 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 1108466 * (3 : ZMod 72644472739) ^ 1108466) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 64611853195 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 72644472739) ^ 4433866 = 11543524564 := by
        calc
          (3 : ZMod 72644472739) ^ 4433866 = (3 : ZMod 72644472739) ^ (2216933 + 2216933) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 2216933 * (3 : ZMod 72644472739) ^ 2216933 := by rw [pow_add]
          _ = 11543524564 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 72644472739) ^ 8867733 = 66165396768 := by
        calc
          (3 : ZMod 72644472739) ^ 8867733 = (3 : ZMod 72644472739) ^ (4433866 + 4433866 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 4433866 * (3 : ZMod 72644472739) ^ 4433866) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 66165396768 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 72644472739) ^ 17735466 = 51306965525 := by
        calc
          (3 : ZMod 72644472739) ^ 17735466 = (3 : ZMod 72644472739) ^ (8867733 + 8867733) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 8867733 * (3 : ZMod 72644472739) ^ 8867733 := by rw [pow_add]
          _ = 51306965525 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 72644472739) ^ 35470933 = 7476495682 := by
        calc
          (3 : ZMod 72644472739) ^ 35470933 = (3 : ZMod 72644472739) ^ (17735466 + 17735466 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 17735466 * (3 : ZMod 72644472739) ^ 17735466) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 7476495682 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 72644472739) ^ 70941867 = 62883517519 := by
        calc
          (3 : ZMod 72644472739) ^ 70941867 = (3 : ZMod 72644472739) ^ (35470933 + 35470933 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 35470933 * (3 : ZMod 72644472739) ^ 35470933) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 62883517519 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 72644472739) ^ 141883735 = 30966054950 := by
        calc
          (3 : ZMod 72644472739) ^ 141883735 = (3 : ZMod 72644472739) ^ (70941867 + 70941867 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 70941867 * (3 : ZMod 72644472739) ^ 70941867) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 30966054950 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 72644472739) ^ 283767471 = 32572019826 := by
        calc
          (3 : ZMod 72644472739) ^ 283767471 = (3 : ZMod 72644472739) ^ (141883735 + 141883735 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 141883735 * (3 : ZMod 72644472739) ^ 141883735) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 32572019826 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 72644472739) ^ 567534943 = 57093014779 := by
        calc
          (3 : ZMod 72644472739) ^ 567534943 = (3 : ZMod 72644472739) ^ (283767471 + 283767471 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 283767471 * (3 : ZMod 72644472739) ^ 283767471) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 57093014779 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 72644472739) ^ 1135069886 = 68020765055 := by
        calc
          (3 : ZMod 72644472739) ^ 1135069886 = (3 : ZMod 72644472739) ^ (567534943 + 567534943) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 567534943 * (3 : ZMod 72644472739) ^ 567534943 := by rw [pow_add]
          _ = 68020765055 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 72644472739) ^ 2270139773 = 23430320012 := by
        calc
          (3 : ZMod 72644472739) ^ 2270139773 = (3 : ZMod 72644472739) ^ (1135069886 + 1135069886 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 1135069886 * (3 : ZMod 72644472739) ^ 1135069886) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 23430320012 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 72644472739) ^ 4540279546 = 31006428183 := by
        calc
          (3 : ZMod 72644472739) ^ 4540279546 = (3 : ZMod 72644472739) ^ (2270139773 + 2270139773) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 2270139773 * (3 : ZMod 72644472739) ^ 2270139773 := by rw [pow_add]
          _ = 31006428183 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 72644472739) ^ 9080559092 = 9850097729 := by
        calc
          (3 : ZMod 72644472739) ^ 9080559092 = (3 : ZMod 72644472739) ^ (4540279546 + 4540279546) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 4540279546 * (3 : ZMod 72644472739) ^ 4540279546 := by rw [pow_add]
          _ = 9850097729 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 72644472739) ^ 18161118184 = 13460481976 := by
        calc
          (3 : ZMod 72644472739) ^ 18161118184 = (3 : ZMod 72644472739) ^ (9080559092 + 9080559092) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 9080559092 * (3 : ZMod 72644472739) ^ 9080559092 := by rw [pow_add]
          _ = 13460481976 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 72644472739) ^ 36322236369 = 72644472738 := by
        calc
          (3 : ZMod 72644472739) ^ 36322236369 = (3 : ZMod 72644472739) ^ (18161118184 + 18161118184 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 18161118184 * (3 : ZMod 72644472739) ^ 18161118184) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 72644472738 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 72644472739) ^ 72644472738 = 1 := by
        calc
          (3 : ZMod 72644472739) ^ 72644472738 = (3 : ZMod 72644472739) ^ (36322236369 + 36322236369) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 36322236369 * (3 : ZMod 72644472739) ^ 36322236369 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (19, 1), (269, 1), (789631, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (19, 1), (269, 1), (789631, 1)] : List FactorBlock).map factorBlockValue).prod = 72644472739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 72644472739) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 72644472739) ^ 2 = 9 := by
        calc
          (3 : ZMod 72644472739) ^ 2 = (3 : ZMod 72644472739) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 1 * (3 : ZMod 72644472739) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 72644472739) ^ 4 = 81 := by
        calc
          (3 : ZMod 72644472739) ^ 4 = (3 : ZMod 72644472739) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 2 * (3 : ZMod 72644472739) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 72644472739) ^ 8 = 6561 := by
        calc
          (3 : ZMod 72644472739) ^ 8 = (3 : ZMod 72644472739) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 4 * (3 : ZMod 72644472739) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 72644472739) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 72644472739) ^ 16 = (3 : ZMod 72644472739) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 8 * (3 : ZMod 72644472739) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 72644472739) ^ 33 = 14934676287 := by
        calc
          (3 : ZMod 72644472739) ^ 33 = (3 : ZMod 72644472739) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 16 * (3 : ZMod 72644472739) ^ 16) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 14934676287 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 72644472739) ^ 67 = 54130115420 := by
        calc
          (3 : ZMod 72644472739) ^ 67 = (3 : ZMod 72644472739) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 33 * (3 : ZMod 72644472739) ^ 33) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 54130115420 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 72644472739) ^ 135 = 26978468017 := by
        calc
          (3 : ZMod 72644472739) ^ 135 = (3 : ZMod 72644472739) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 67 * (3 : ZMod 72644472739) ^ 67) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 26978468017 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 72644472739) ^ 270 = 29879360816 := by
        calc
          (3 : ZMod 72644472739) ^ 270 = (3 : ZMod 72644472739) ^ (135 + 135) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 135 * (3 : ZMod 72644472739) ^ 135 := by rw [pow_add]
          _ = 29879360816 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 72644472739) ^ 541 = 55624504095 := by
        calc
          (3 : ZMod 72644472739) ^ 541 = (3 : ZMod 72644472739) ^ (270 + 270 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 270 * (3 : ZMod 72644472739) ^ 270) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 55624504095 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 72644472739) ^ 1082 = 57614801876 := by
        calc
          (3 : ZMod 72644472739) ^ 1082 = (3 : ZMod 72644472739) ^ (541 + 541) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 541 * (3 : ZMod 72644472739) ^ 541 := by rw [pow_add]
          _ = 57614801876 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 72644472739) ^ 2164 = 35637304797 := by
        calc
          (3 : ZMod 72644472739) ^ 2164 = (3 : ZMod 72644472739) ^ (1082 + 1082) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 1082 * (3 : ZMod 72644472739) ^ 1082 := by rw [pow_add]
          _ = 35637304797 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 72644472739) ^ 4329 = 11823358265 := by
        calc
          (3 : ZMod 72644472739) ^ 4329 = (3 : ZMod 72644472739) ^ (2164 + 2164 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 2164 * (3 : ZMod 72644472739) ^ 2164) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 11823358265 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 72644472739) ^ 8659 = 3361450934 := by
        calc
          (3 : ZMod 72644472739) ^ 8659 = (3 : ZMod 72644472739) ^ (4329 + 4329 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 4329 * (3 : ZMod 72644472739) ^ 4329) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 3361450934 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 72644472739) ^ 17319 = 29392888791 := by
        calc
          (3 : ZMod 72644472739) ^ 17319 = (3 : ZMod 72644472739) ^ (8659 + 8659 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 8659 * (3 : ZMod 72644472739) ^ 8659) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 29392888791 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 72644472739) ^ 34639 = 18581158543 := by
        calc
          (3 : ZMod 72644472739) ^ 34639 = (3 : ZMod 72644472739) ^ (17319 + 17319 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 17319 * (3 : ZMod 72644472739) ^ 17319) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 18581158543 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 72644472739) ^ 69279 = 54376492856 := by
        calc
          (3 : ZMod 72644472739) ^ 69279 = (3 : ZMod 72644472739) ^ (34639 + 34639 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 34639 * (3 : ZMod 72644472739) ^ 34639) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 54376492856 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 72644472739) ^ 138558 = 24717591940 := by
        calc
          (3 : ZMod 72644472739) ^ 138558 = (3 : ZMod 72644472739) ^ (69279 + 69279) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 69279 * (3 : ZMod 72644472739) ^ 69279 := by rw [pow_add]
          _ = 24717591940 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 72644472739) ^ 277116 = 15987442187 := by
        calc
          (3 : ZMod 72644472739) ^ 277116 = (3 : ZMod 72644472739) ^ (138558 + 138558) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 138558 * (3 : ZMod 72644472739) ^ 138558 := by rw [pow_add]
          _ = 15987442187 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 72644472739) ^ 554233 = 19126652894 := by
        calc
          (3 : ZMod 72644472739) ^ 554233 = (3 : ZMod 72644472739) ^ (277116 + 277116 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 277116 * (3 : ZMod 72644472739) ^ 277116) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 19126652894 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 72644472739) ^ 1108466 = 63748563764 := by
        calc
          (3 : ZMod 72644472739) ^ 1108466 = (3 : ZMod 72644472739) ^ (554233 + 554233) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 554233 * (3 : ZMod 72644472739) ^ 554233 := by rw [pow_add]
          _ = 63748563764 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 72644472739) ^ 2216933 = 64611853195 := by
        calc
          (3 : ZMod 72644472739) ^ 2216933 = (3 : ZMod 72644472739) ^ (1108466 + 1108466 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 1108466 * (3 : ZMod 72644472739) ^ 1108466) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 64611853195 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 72644472739) ^ 4433866 = 11543524564 := by
        calc
          (3 : ZMod 72644472739) ^ 4433866 = (3 : ZMod 72644472739) ^ (2216933 + 2216933) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 2216933 * (3 : ZMod 72644472739) ^ 2216933 := by rw [pow_add]
          _ = 11543524564 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 72644472739) ^ 8867733 = 66165396768 := by
        calc
          (3 : ZMod 72644472739) ^ 8867733 = (3 : ZMod 72644472739) ^ (4433866 + 4433866 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 4433866 * (3 : ZMod 72644472739) ^ 4433866) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 66165396768 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 72644472739) ^ 17735466 = 51306965525 := by
        calc
          (3 : ZMod 72644472739) ^ 17735466 = (3 : ZMod 72644472739) ^ (8867733 + 8867733) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 8867733 * (3 : ZMod 72644472739) ^ 8867733 := by rw [pow_add]
          _ = 51306965525 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 72644472739) ^ 35470933 = 7476495682 := by
        calc
          (3 : ZMod 72644472739) ^ 35470933 = (3 : ZMod 72644472739) ^ (17735466 + 17735466 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 17735466 * (3 : ZMod 72644472739) ^ 17735466) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 7476495682 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 72644472739) ^ 70941867 = 62883517519 := by
        calc
          (3 : ZMod 72644472739) ^ 70941867 = (3 : ZMod 72644472739) ^ (35470933 + 35470933 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 35470933 * (3 : ZMod 72644472739) ^ 35470933) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 62883517519 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 72644472739) ^ 141883735 = 30966054950 := by
        calc
          (3 : ZMod 72644472739) ^ 141883735 = (3 : ZMod 72644472739) ^ (70941867 + 70941867 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 70941867 * (3 : ZMod 72644472739) ^ 70941867) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 30966054950 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 72644472739) ^ 283767471 = 32572019826 := by
        calc
          (3 : ZMod 72644472739) ^ 283767471 = (3 : ZMod 72644472739) ^ (141883735 + 141883735 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 141883735 * (3 : ZMod 72644472739) ^ 141883735) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 32572019826 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 72644472739) ^ 567534943 = 57093014779 := by
        calc
          (3 : ZMod 72644472739) ^ 567534943 = (3 : ZMod 72644472739) ^ (283767471 + 283767471 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 283767471 * (3 : ZMod 72644472739) ^ 283767471) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 57093014779 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 72644472739) ^ 1135069886 = 68020765055 := by
        calc
          (3 : ZMod 72644472739) ^ 1135069886 = (3 : ZMod 72644472739) ^ (567534943 + 567534943) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 567534943 * (3 : ZMod 72644472739) ^ 567534943 := by rw [pow_add]
          _ = 68020765055 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 72644472739) ^ 2270139773 = 23430320012 := by
        calc
          (3 : ZMod 72644472739) ^ 2270139773 = (3 : ZMod 72644472739) ^ (1135069886 + 1135069886 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 1135069886 * (3 : ZMod 72644472739) ^ 1135069886) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 23430320012 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 72644472739) ^ 4540279546 = 31006428183 := by
        calc
          (3 : ZMod 72644472739) ^ 4540279546 = (3 : ZMod 72644472739) ^ (2270139773 + 2270139773) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 2270139773 * (3 : ZMod 72644472739) ^ 2270139773 := by rw [pow_add]
          _ = 31006428183 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 72644472739) ^ 9080559092 = 9850097729 := by
        calc
          (3 : ZMod 72644472739) ^ 9080559092 = (3 : ZMod 72644472739) ^ (4540279546 + 4540279546) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 4540279546 * (3 : ZMod 72644472739) ^ 4540279546 := by rw [pow_add]
          _ = 9850097729 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 72644472739) ^ 18161118184 = 13460481976 := by
        calc
          (3 : ZMod 72644472739) ^ 18161118184 = (3 : ZMod 72644472739) ^ (9080559092 + 9080559092) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 9080559092 * (3 : ZMod 72644472739) ^ 9080559092 := by rw [pow_add]
          _ = 13460481976 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 72644472739) ^ 36322236369 = 72644472738 := by
        calc
          (3 : ZMod 72644472739) ^ 36322236369 = (3 : ZMod 72644472739) ^ (18161118184 + 18161118184 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 18161118184 * (3 : ZMod 72644472739) ^ 18161118184) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 72644472738 := by rw [factor_0_34]; decide
      change (3 : ZMod 72644472739) ^ 36322236369 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (3 : ZMod 72644472739) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 72644472739) ^ 2 = 9 := by
        calc
          (3 : ZMod 72644472739) ^ 2 = (3 : ZMod 72644472739) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 1 * (3 : ZMod 72644472739) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 72644472739) ^ 5 = 243 := by
        calc
          (3 : ZMod 72644472739) ^ 5 = (3 : ZMod 72644472739) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 2 * (3 : ZMod 72644472739) ^ 2) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 72644472739) ^ 11 = 177147 := by
        calc
          (3 : ZMod 72644472739) ^ 11 = (3 : ZMod 72644472739) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 5 * (3 : ZMod 72644472739) ^ 5) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 72644472739) ^ 22 = 31381059609 := by
        calc
          (3 : ZMod 72644472739) ^ 22 = (3 : ZMod 72644472739) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 11 * (3 : ZMod 72644472739) ^ 11 := by rw [pow_add]
          _ = 31381059609 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 72644472739) ^ 45 = 54787067383 := by
        calc
          (3 : ZMod 72644472739) ^ 45 = (3 : ZMod 72644472739) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 22 * (3 : ZMod 72644472739) ^ 22) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 54787067383 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 72644472739) ^ 90 = 59799051853 := by
        calc
          (3 : ZMod 72644472739) ^ 90 = (3 : ZMod 72644472739) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 45 * (3 : ZMod 72644472739) ^ 45 := by rw [pow_add]
          _ = 59799051853 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 72644472739) ^ 180 = 21493850106 := by
        calc
          (3 : ZMod 72644472739) ^ 180 = (3 : ZMod 72644472739) ^ (90 + 90) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 90 * (3 : ZMod 72644472739) ^ 90 := by rw [pow_add]
          _ = 21493850106 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 72644472739) ^ 360 = 1508525049 := by
        calc
          (3 : ZMod 72644472739) ^ 360 = (3 : ZMod 72644472739) ^ (180 + 180) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 180 * (3 : ZMod 72644472739) ^ 180 := by rw [pow_add]
          _ = 1508525049 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 72644472739) ^ 721 = 3464057829 := by
        calc
          (3 : ZMod 72644472739) ^ 721 = (3 : ZMod 72644472739) ^ (360 + 360 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 360 * (3 : ZMod 72644472739) ^ 360) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 3464057829 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 72644472739) ^ 1443 = 598710115 := by
        calc
          (3 : ZMod 72644472739) ^ 1443 = (3 : ZMod 72644472739) ^ (721 + 721 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 721 * (3 : ZMod 72644472739) ^ 721) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 598710115 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 72644472739) ^ 2886 = 39232319402 := by
        calc
          (3 : ZMod 72644472739) ^ 2886 = (3 : ZMod 72644472739) ^ (1443 + 1443) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 1443 * (3 : ZMod 72644472739) ^ 1443 := by rw [pow_add]
          _ = 39232319402 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 72644472739) ^ 5773 = 32662396187 := by
        calc
          (3 : ZMod 72644472739) ^ 5773 = (3 : ZMod 72644472739) ^ (2886 + 2886 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 2886 * (3 : ZMod 72644472739) ^ 2886) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 32662396187 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 72644472739) ^ 11546 = 26669346926 := by
        calc
          (3 : ZMod 72644472739) ^ 11546 = (3 : ZMod 72644472739) ^ (5773 + 5773) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 5773 * (3 : ZMod 72644472739) ^ 5773 := by rw [pow_add]
          _ = 26669346926 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 72644472739) ^ 23093 = 27166061469 := by
        calc
          (3 : ZMod 72644472739) ^ 23093 = (3 : ZMod 72644472739) ^ (11546 + 11546 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 11546 * (3 : ZMod 72644472739) ^ 11546) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 27166061469 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 72644472739) ^ 46186 = 36792286852 := by
        calc
          (3 : ZMod 72644472739) ^ 46186 = (3 : ZMod 72644472739) ^ (23093 + 23093) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 23093 * (3 : ZMod 72644472739) ^ 23093 := by rw [pow_add]
          _ = 36792286852 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 72644472739) ^ 92372 = 36868659881 := by
        calc
          (3 : ZMod 72644472739) ^ 92372 = (3 : ZMod 72644472739) ^ (46186 + 46186) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 46186 * (3 : ZMod 72644472739) ^ 46186 := by rw [pow_add]
          _ = 36868659881 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 72644472739) ^ 184744 = 9475526313 := by
        calc
          (3 : ZMod 72644472739) ^ 184744 = (3 : ZMod 72644472739) ^ (92372 + 92372) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 92372 * (3 : ZMod 72644472739) ^ 92372 := by rw [pow_add]
          _ = 9475526313 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 72644472739) ^ 369488 = 18419053333 := by
        calc
          (3 : ZMod 72644472739) ^ 369488 = (3 : ZMod 72644472739) ^ (184744 + 184744) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 184744 * (3 : ZMod 72644472739) ^ 184744 := by rw [pow_add]
          _ = 18419053333 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 72644472739) ^ 738977 = 56983893520 := by
        calc
          (3 : ZMod 72644472739) ^ 738977 = (3 : ZMod 72644472739) ^ (369488 + 369488 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 369488 * (3 : ZMod 72644472739) ^ 369488) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 56983893520 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 72644472739) ^ 1477955 = 26430425167 := by
        calc
          (3 : ZMod 72644472739) ^ 1477955 = (3 : ZMod 72644472739) ^ (738977 + 738977 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 738977 * (3 : ZMod 72644472739) ^ 738977) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 26430425167 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 72644472739) ^ 2955911 = 71155101340 := by
        calc
          (3 : ZMod 72644472739) ^ 2955911 = (3 : ZMod 72644472739) ^ (1477955 + 1477955 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 1477955 * (3 : ZMod 72644472739) ^ 1477955) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 71155101340 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 72644472739) ^ 5911822 = 3018429469 := by
        calc
          (3 : ZMod 72644472739) ^ 5911822 = (3 : ZMod 72644472739) ^ (2955911 + 2955911) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 2955911 * (3 : ZMod 72644472739) ^ 2955911 := by rw [pow_add]
          _ = 3018429469 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 72644472739) ^ 11823644 = 40884193990 := by
        calc
          (3 : ZMod 72644472739) ^ 11823644 = (3 : ZMod 72644472739) ^ (5911822 + 5911822) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 5911822 * (3 : ZMod 72644472739) ^ 5911822 := by rw [pow_add]
          _ = 40884193990 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 72644472739) ^ 23647289 = 43743857715 := by
        calc
          (3 : ZMod 72644472739) ^ 23647289 = (3 : ZMod 72644472739) ^ (11823644 + 11823644 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 11823644 * (3 : ZMod 72644472739) ^ 11823644) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 43743857715 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 72644472739) ^ 47294578 = 61188973199 := by
        calc
          (3 : ZMod 72644472739) ^ 47294578 = (3 : ZMod 72644472739) ^ (23647289 + 23647289) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 23647289 * (3 : ZMod 72644472739) ^ 23647289 := by rw [pow_add]
          _ = 61188973199 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 72644472739) ^ 94589157 = 13504542578 := by
        calc
          (3 : ZMod 72644472739) ^ 94589157 = (3 : ZMod 72644472739) ^ (47294578 + 47294578 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 47294578 * (3 : ZMod 72644472739) ^ 47294578) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 13504542578 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 72644472739) ^ 189178314 = 45120065223 := by
        calc
          (3 : ZMod 72644472739) ^ 189178314 = (3 : ZMod 72644472739) ^ (94589157 + 94589157) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 94589157 * (3 : ZMod 72644472739) ^ 94589157 := by rw [pow_add]
          _ = 45120065223 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 72644472739) ^ 378356628 = 14026068652 := by
        calc
          (3 : ZMod 72644472739) ^ 378356628 = (3 : ZMod 72644472739) ^ (189178314 + 189178314) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 189178314 * (3 : ZMod 72644472739) ^ 189178314 := by rw [pow_add]
          _ = 14026068652 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 72644472739) ^ 756713257 = 53222608130 := by
        calc
          (3 : ZMod 72644472739) ^ 756713257 = (3 : ZMod 72644472739) ^ (378356628 + 378356628 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 378356628 * (3 : ZMod 72644472739) ^ 378356628) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 53222608130 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 72644472739) ^ 1513426515 = 59069778963 := by
        calc
          (3 : ZMod 72644472739) ^ 1513426515 = (3 : ZMod 72644472739) ^ (756713257 + 756713257 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 756713257 * (3 : ZMod 72644472739) ^ 756713257) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 59069778963 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 72644472739) ^ 3026853030 = 13135941989 := by
        calc
          (3 : ZMod 72644472739) ^ 3026853030 = (3 : ZMod 72644472739) ^ (1513426515 + 1513426515) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 1513426515 * (3 : ZMod 72644472739) ^ 1513426515 := by rw [pow_add]
          _ = 13135941989 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 72644472739) ^ 6053706061 = 43052477357 := by
        calc
          (3 : ZMod 72644472739) ^ 6053706061 = (3 : ZMod 72644472739) ^ (3026853030 + 3026853030 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 3026853030 * (3 : ZMod 72644472739) ^ 3026853030) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 43052477357 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 72644472739) ^ 12107412123 = 16131513406 := by
        calc
          (3 : ZMod 72644472739) ^ 12107412123 = (3 : ZMod 72644472739) ^ (6053706061 + 6053706061 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 6053706061 * (3 : ZMod 72644472739) ^ 6053706061) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 16131513406 := by rw [factor_1_32]; decide
      have factor_1_34 : (3 : ZMod 72644472739) ^ 24214824246 = 16131513405 := by
        calc
          (3 : ZMod 72644472739) ^ 24214824246 = (3 : ZMod 72644472739) ^ (12107412123 + 12107412123) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 12107412123 * (3 : ZMod 72644472739) ^ 12107412123 := by rw [pow_add]
          _ = 16131513405 := by rw [factor_1_33]; decide
      change (3 : ZMod 72644472739) ^ 24214824246 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (3 : ZMod 72644472739) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 72644472739) ^ 3 = 27 := by
        calc
          (3 : ZMod 72644472739) ^ 3 = (3 : ZMod 72644472739) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 1 * (3 : ZMod 72644472739) ^ 1) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 72644472739) ^ 7 = 2187 := by
        calc
          (3 : ZMod 72644472739) ^ 7 = (3 : ZMod 72644472739) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 3 * (3 : ZMod 72644472739) ^ 3) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 72644472739) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 72644472739) ^ 14 = (3 : ZMod 72644472739) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 7 * (3 : ZMod 72644472739) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 72644472739) ^ 28 = 66428014915 := by
        calc
          (3 : ZMod 72644472739) ^ 28 = (3 : ZMod 72644472739) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 14 * (3 : ZMod 72644472739) ^ 14 := by rw [pow_add]
          _ = 66428014915 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 72644472739) ^ 56 = 63067765901 := by
        calc
          (3 : ZMod 72644472739) ^ 56 = (3 : ZMod 72644472739) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 28 * (3 : ZMod 72644472739) ^ 28 := by rw [pow_add]
          _ = 63067765901 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 72644472739) ^ 113 = 18170008721 := by
        calc
          (3 : ZMod 72644472739) ^ 113 = (3 : ZMod 72644472739) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 56 * (3 : ZMod 72644472739) ^ 56) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 18170008721 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 72644472739) ^ 227 = 8805138050 := by
        calc
          (3 : ZMod 72644472739) ^ 227 = (3 : ZMod 72644472739) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 113 * (3 : ZMod 72644472739) ^ 113) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 8805138050 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 72644472739) ^ 455 = 25496028135 := by
        calc
          (3 : ZMod 72644472739) ^ 455 = (3 : ZMod 72644472739) ^ (227 + 227 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 227 * (3 : ZMod 72644472739) ^ 227) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 25496028135 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 72644472739) ^ 911 = 10236113726 := by
        calc
          (3 : ZMod 72644472739) ^ 911 = (3 : ZMod 72644472739) ^ (455 + 455 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 455 * (3 : ZMod 72644472739) ^ 455) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 10236113726 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 72644472739) ^ 1823 = 6158849638 := by
        calc
          (3 : ZMod 72644472739) ^ 1823 = (3 : ZMod 72644472739) ^ (911 + 911 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 911 * (3 : ZMod 72644472739) ^ 911) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 6158849638 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 72644472739) ^ 3646 = 29355934820 := by
        calc
          (3 : ZMod 72644472739) ^ 3646 = (3 : ZMod 72644472739) ^ (1823 + 1823) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 1823 * (3 : ZMod 72644472739) ^ 1823 := by rw [pow_add]
          _ = 29355934820 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 72644472739) ^ 7292 = 27632031860 := by
        calc
          (3 : ZMod 72644472739) ^ 7292 = (3 : ZMod 72644472739) ^ (3646 + 3646) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 3646 * (3 : ZMod 72644472739) ^ 3646 := by rw [pow_add]
          _ = 27632031860 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 72644472739) ^ 14585 = 26602470511 := by
        calc
          (3 : ZMod 72644472739) ^ 14585 = (3 : ZMod 72644472739) ^ (7292 + 7292 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 7292 * (3 : ZMod 72644472739) ^ 7292) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 26602470511 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 72644472739) ^ 29170 = 36355106776 := by
        calc
          (3 : ZMod 72644472739) ^ 29170 = (3 : ZMod 72644472739) ^ (14585 + 14585) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 14585 * (3 : ZMod 72644472739) ^ 14585 := by rw [pow_add]
          _ = 36355106776 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 72644472739) ^ 58340 = 40541546280 := by
        calc
          (3 : ZMod 72644472739) ^ 58340 = (3 : ZMod 72644472739) ^ (29170 + 29170) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 29170 * (3 : ZMod 72644472739) ^ 29170 := by rw [pow_add]
          _ = 40541546280 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 72644472739) ^ 116680 = 52504480642 := by
        calc
          (3 : ZMod 72644472739) ^ 116680 = (3 : ZMod 72644472739) ^ (58340 + 58340) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 58340 * (3 : ZMod 72644472739) ^ 58340 := by rw [pow_add]
          _ = 52504480642 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 72644472739) ^ 233361 = 19730086474 := by
        calc
          (3 : ZMod 72644472739) ^ 233361 = (3 : ZMod 72644472739) ^ (116680 + 116680 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 116680 * (3 : ZMod 72644472739) ^ 116680) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 19730086474 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 72644472739) ^ 466722 = 1916564952 := by
        calc
          (3 : ZMod 72644472739) ^ 466722 = (3 : ZMod 72644472739) ^ (233361 + 233361) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 233361 * (3 : ZMod 72644472739) ^ 233361 := by rw [pow_add]
          _ = 1916564952 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 72644472739) ^ 933445 = 48882759009 := by
        calc
          (3 : ZMod 72644472739) ^ 933445 = (3 : ZMod 72644472739) ^ (466722 + 466722 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 466722 * (3 : ZMod 72644472739) ^ 466722) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 48882759009 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 72644472739) ^ 1866891 = 46454342248 := by
        calc
          (3 : ZMod 72644472739) ^ 1866891 = (3 : ZMod 72644472739) ^ (933445 + 933445 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 933445 * (3 : ZMod 72644472739) ^ 933445) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 46454342248 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 72644472739) ^ 3733782 = 17252396771 := by
        calc
          (3 : ZMod 72644472739) ^ 3733782 = (3 : ZMod 72644472739) ^ (1866891 + 1866891) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 1866891 * (3 : ZMod 72644472739) ^ 1866891 := by rw [pow_add]
          _ = 17252396771 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 72644472739) ^ 7467565 = 48136974568 := by
        calc
          (3 : ZMod 72644472739) ^ 7467565 = (3 : ZMod 72644472739) ^ (3733782 + 3733782 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 3733782 * (3 : ZMod 72644472739) ^ 3733782) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 48136974568 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 72644472739) ^ 14935130 = 14522717133 := by
        calc
          (3 : ZMod 72644472739) ^ 14935130 = (3 : ZMod 72644472739) ^ (7467565 + 7467565) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 7467565 * (3 : ZMod 72644472739) ^ 7467565 := by rw [pow_add]
          _ = 14522717133 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 72644472739) ^ 29870260 = 68597885837 := by
        calc
          (3 : ZMod 72644472739) ^ 29870260 = (3 : ZMod 72644472739) ^ (14935130 + 14935130) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 14935130 * (3 : ZMod 72644472739) ^ 14935130 := by rw [pow_add]
          _ = 68597885837 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 72644472739) ^ 59740520 = 58888573695 := by
        calc
          (3 : ZMod 72644472739) ^ 59740520 = (3 : ZMod 72644472739) ^ (29870260 + 29870260) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 29870260 * (3 : ZMod 72644472739) ^ 29870260 := by rw [pow_add]
          _ = 58888573695 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 72644472739) ^ 119481040 = 51336479936 := by
        calc
          (3 : ZMod 72644472739) ^ 119481040 = (3 : ZMod 72644472739) ^ (59740520 + 59740520) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 59740520 * (3 : ZMod 72644472739) ^ 59740520 := by rw [pow_add]
          _ = 51336479936 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 72644472739) ^ 238962081 = 48630457229 := by
        calc
          (3 : ZMod 72644472739) ^ 238962081 = (3 : ZMod 72644472739) ^ (119481040 + 119481040 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 119481040 * (3 : ZMod 72644472739) ^ 119481040) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 48630457229 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 72644472739) ^ 477924162 = 17002787580 := by
        calc
          (3 : ZMod 72644472739) ^ 477924162 = (3 : ZMod 72644472739) ^ (238962081 + 238962081) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 238962081 * (3 : ZMod 72644472739) ^ 238962081 := by rw [pow_add]
          _ = 17002787580 := by rw [factor_2_27]; decide
      have factor_2_29 : (3 : ZMod 72644472739) ^ 955848325 = 65853621048 := by
        calc
          (3 : ZMod 72644472739) ^ 955848325 = (3 : ZMod 72644472739) ^ (477924162 + 477924162 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 477924162 * (3 : ZMod 72644472739) ^ 477924162) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 65853621048 := by rw [factor_2_28]; decide
      have factor_2_30 : (3 : ZMod 72644472739) ^ 1911696651 = 68293633937 := by
        calc
          (3 : ZMod 72644472739) ^ 1911696651 = (3 : ZMod 72644472739) ^ (955848325 + 955848325 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 955848325 * (3 : ZMod 72644472739) ^ 955848325) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 68293633937 := by rw [factor_2_29]; decide
      have factor_2_31 : (3 : ZMod 72644472739) ^ 3823393302 = 17687286082 := by
        calc
          (3 : ZMod 72644472739) ^ 3823393302 = (3 : ZMod 72644472739) ^ (1911696651 + 1911696651) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 1911696651 * (3 : ZMod 72644472739) ^ 1911696651 := by rw [pow_add]
          _ = 17687286082 := by rw [factor_2_30]; decide
      change (3 : ZMod 72644472739) ^ 3823393302 ≠ 1
      rw [factor_2_31]
      decide
    ·
      have factor_3_0 : (3 : ZMod 72644472739) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 72644472739) ^ 2 = 9 := by
        calc
          (3 : ZMod 72644472739) ^ 2 = (3 : ZMod 72644472739) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 1 * (3 : ZMod 72644472739) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 72644472739) ^ 4 = 81 := by
        calc
          (3 : ZMod 72644472739) ^ 4 = (3 : ZMod 72644472739) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 2 * (3 : ZMod 72644472739) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 72644472739) ^ 8 = 6561 := by
        calc
          (3 : ZMod 72644472739) ^ 8 = (3 : ZMod 72644472739) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 4 * (3 : ZMod 72644472739) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 72644472739) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 72644472739) ^ 16 = (3 : ZMod 72644472739) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 8 * (3 : ZMod 72644472739) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 72644472739) ^ 32 = 4978225429 := by
        calc
          (3 : ZMod 72644472739) ^ 32 = (3 : ZMod 72644472739) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 16 * (3 : ZMod 72644472739) ^ 16 := by rw [pow_add]
          _ = 4978225429 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 72644472739) ^ 64 = 4695355117 := by
        calc
          (3 : ZMod 72644472739) ^ 64 = (3 : ZMod 72644472739) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 32 * (3 : ZMod 72644472739) ^ 32 := by rw [pow_add]
          _ = 4695355117 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 72644472739) ^ 128 = 60267056249 := by
        calc
          (3 : ZMod 72644472739) ^ 128 = (3 : ZMod 72644472739) ^ (64 + 64) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 64 * (3 : ZMod 72644472739) ^ 64 := by rw [pow_add]
          _ = 60267056249 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 72644472739) ^ 257 = 22744067658 := by
        calc
          (3 : ZMod 72644472739) ^ 257 = (3 : ZMod 72644472739) ^ (128 + 128 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 128 * (3 : ZMod 72644472739) ^ 128) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 22744067658 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 72644472739) ^ 515 = 29837544328 := by
        calc
          (3 : ZMod 72644472739) ^ 515 = (3 : ZMod 72644472739) ^ (257 + 257 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 257 * (3 : ZMod 72644472739) ^ 257) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 29837544328 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 72644472739) ^ 1030 = 51681338967 := by
        calc
          (3 : ZMod 72644472739) ^ 1030 = (3 : ZMod 72644472739) ^ (515 + 515) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 515 * (3 : ZMod 72644472739) ^ 515 := by rw [pow_add]
          _ = 51681338967 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 72644472739) ^ 2060 = 1610241807 := by
        calc
          (3 : ZMod 72644472739) ^ 2060 = (3 : ZMod 72644472739) ^ (1030 + 1030) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 1030 * (3 : ZMod 72644472739) ^ 1030 := by rw [pow_add]
          _ = 1610241807 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 72644472739) ^ 4120 = 69923283386 := by
        calc
          (3 : ZMod 72644472739) ^ 4120 = (3 : ZMod 72644472739) ^ (2060 + 2060) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 2060 * (3 : ZMod 72644472739) ^ 2060 := by rw [pow_add]
          _ = 69923283386 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 72644472739) ^ 8241 = 28436468188 := by
        calc
          (3 : ZMod 72644472739) ^ 8241 = (3 : ZMod 72644472739) ^ (4120 + 4120 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 4120 * (3 : ZMod 72644472739) ^ 4120) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 28436468188 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 72644472739) ^ 16482 = 52484047171 := by
        calc
          (3 : ZMod 72644472739) ^ 16482 = (3 : ZMod 72644472739) ^ (8241 + 8241) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 8241 * (3 : ZMod 72644472739) ^ 8241 := by rw [pow_add]
          _ = 52484047171 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 72644472739) ^ 32965 = 59116270879 := by
        calc
          (3 : ZMod 72644472739) ^ 32965 = (3 : ZMod 72644472739) ^ (16482 + 16482 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 16482 * (3 : ZMod 72644472739) ^ 16482) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 59116270879 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 72644472739) ^ 65931 = 48017550811 := by
        calc
          (3 : ZMod 72644472739) ^ 65931 = (3 : ZMod 72644472739) ^ (32965 + 32965 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 32965 * (3 : ZMod 72644472739) ^ 32965) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 48017550811 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 72644472739) ^ 131862 = 20306781482 := by
        calc
          (3 : ZMod 72644472739) ^ 131862 = (3 : ZMod 72644472739) ^ (65931 + 65931) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 65931 * (3 : ZMod 72644472739) ^ 65931 := by rw [pow_add]
          _ = 20306781482 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 72644472739) ^ 263724 = 52100082877 := by
        calc
          (3 : ZMod 72644472739) ^ 263724 = (3 : ZMod 72644472739) ^ (131862 + 131862) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 131862 * (3 : ZMod 72644472739) ^ 131862 := by rw [pow_add]
          _ = 52100082877 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 72644472739) ^ 527448 = 14443957285 := by
        calc
          (3 : ZMod 72644472739) ^ 527448 = (3 : ZMod 72644472739) ^ (263724 + 263724) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 263724 * (3 : ZMod 72644472739) ^ 263724 := by rw [pow_add]
          _ = 14443957285 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 72644472739) ^ 1054897 = 71318969798 := by
        calc
          (3 : ZMod 72644472739) ^ 1054897 = (3 : ZMod 72644472739) ^ (527448 + 527448 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 527448 * (3 : ZMod 72644472739) ^ 527448) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 71318969798 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 72644472739) ^ 2109795 = 50716233068 := by
        calc
          (3 : ZMod 72644472739) ^ 2109795 = (3 : ZMod 72644472739) ^ (1054897 + 1054897 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 1054897 * (3 : ZMod 72644472739) ^ 1054897) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 50716233068 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 72644472739) ^ 4219590 = 68507121296 := by
        calc
          (3 : ZMod 72644472739) ^ 4219590 = (3 : ZMod 72644472739) ^ (2109795 + 2109795) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 2109795 * (3 : ZMod 72644472739) ^ 2109795 := by rw [pow_add]
          _ = 68507121296 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 72644472739) ^ 8439181 = 35673523137 := by
        calc
          (3 : ZMod 72644472739) ^ 8439181 = (3 : ZMod 72644472739) ^ (4219590 + 4219590 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 4219590 * (3 : ZMod 72644472739) ^ 4219590) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 35673523137 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 72644472739) ^ 16878362 = 26760472153 := by
        calc
          (3 : ZMod 72644472739) ^ 16878362 = (3 : ZMod 72644472739) ^ (8439181 + 8439181) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 8439181 * (3 : ZMod 72644472739) ^ 8439181 := by rw [pow_add]
          _ = 26760472153 := by rw [factor_3_23]; decide
      have factor_3_25 : (3 : ZMod 72644472739) ^ 33756725 = 29512583324 := by
        calc
          (3 : ZMod 72644472739) ^ 33756725 = (3 : ZMod 72644472739) ^ (16878362 + 16878362 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 16878362 * (3 : ZMod 72644472739) ^ 16878362) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 29512583324 := by rw [factor_3_24]; decide
      have factor_3_26 : (3 : ZMod 72644472739) ^ 67513450 = 13184854578 := by
        calc
          (3 : ZMod 72644472739) ^ 67513450 = (3 : ZMod 72644472739) ^ (33756725 + 33756725) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 33756725 * (3 : ZMod 72644472739) ^ 33756725 := by rw [pow_add]
          _ = 13184854578 := by rw [factor_3_25]; decide
      have factor_3_27 : (3 : ZMod 72644472739) ^ 135026901 = 54520733881 := by
        calc
          (3 : ZMod 72644472739) ^ 135026901 = (3 : ZMod 72644472739) ^ (67513450 + 67513450 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 67513450 * (3 : ZMod 72644472739) ^ 67513450) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 54520733881 := by rw [factor_3_26]; decide
      have factor_3_28 : (3 : ZMod 72644472739) ^ 270053802 = 29303255440 := by
        calc
          (3 : ZMod 72644472739) ^ 270053802 = (3 : ZMod 72644472739) ^ (135026901 + 135026901) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 135026901 * (3 : ZMod 72644472739) ^ 135026901 := by rw [pow_add]
          _ = 29303255440 := by rw [factor_3_27]; decide
      change (3 : ZMod 72644472739) ^ 270053802 ≠ 1
      rw [factor_3_28]
      decide
    ·
      have factor_4_0 : (3 : ZMod 72644472739) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 72644472739) ^ 2 = 9 := by
        calc
          (3 : ZMod 72644472739) ^ 2 = (3 : ZMod 72644472739) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 1 * (3 : ZMod 72644472739) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 72644472739) ^ 5 = 243 := by
        calc
          (3 : ZMod 72644472739) ^ 5 = (3 : ZMod 72644472739) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 2 * (3 : ZMod 72644472739) ^ 2) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 72644472739) ^ 11 = 177147 := by
        calc
          (3 : ZMod 72644472739) ^ 11 = (3 : ZMod 72644472739) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 5 * (3 : ZMod 72644472739) ^ 5) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 72644472739) ^ 22 = 31381059609 := by
        calc
          (3 : ZMod 72644472739) ^ 22 = (3 : ZMod 72644472739) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 11 * (3 : ZMod 72644472739) ^ 11 := by rw [pow_add]
          _ = 31381059609 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 72644472739) ^ 44 = 66692004287 := by
        calc
          (3 : ZMod 72644472739) ^ 44 = (3 : ZMod 72644472739) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 22 * (3 : ZMod 72644472739) ^ 22 := by rw [pow_add]
          _ = 66692004287 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 72644472739) ^ 89 = 68362665777 := by
        calc
          (3 : ZMod 72644472739) ^ 89 = (3 : ZMod 72644472739) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 44 * (3 : ZMod 72644472739) ^ 44) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 68362665777 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 72644472739) ^ 179 = 7164616702 := by
        calc
          (3 : ZMod 72644472739) ^ 179 = (3 : ZMod 72644472739) ^ (89 + 89 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 89 * (3 : ZMod 72644472739) ^ 89) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 7164616702 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 72644472739) ^ 359 = 502841683 := by
        calc
          (3 : ZMod 72644472739) ^ 359 = (3 : ZMod 72644472739) ^ (179 + 179 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 179 * (3 : ZMod 72644472739) ^ 179) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 502841683 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 72644472739) ^ 718 = 64701163095 := by
        calc
          (3 : ZMod 72644472739) ^ 718 = (3 : ZMod 72644472739) ^ (359 + 359) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 359 * (3 : ZMod 72644472739) ^ 359 := by rw [pow_add]
          _ = 64701163095 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 72644472739) ^ 1437 = 28600222752 := by
        calc
          (3 : ZMod 72644472739) ^ 1437 = (3 : ZMod 72644472739) ^ (718 + 718 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 718 * (3 : ZMod 72644472739) ^ 718) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 28600222752 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 72644472739) ^ 2874 = 20889284544 := by
        calc
          (3 : ZMod 72644472739) ^ 2874 = (3 : ZMod 72644472739) ^ (1437 + 1437) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 1437 * (3 : ZMod 72644472739) ^ 1437 := by rw [pow_add]
          _ = 20889284544 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 72644472739) ^ 5749 = 14625517947 := by
        calc
          (3 : ZMod 72644472739) ^ 5749 = (3 : ZMod 72644472739) ^ (2874 + 2874 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 2874 * (3 : ZMod 72644472739) ^ 2874) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 14625517947 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 72644472739) ^ 11499 = 1724968387 := by
        calc
          (3 : ZMod 72644472739) ^ 11499 = (3 : ZMod 72644472739) ^ (5749 + 5749 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 5749 * (3 : ZMod 72644472739) ^ 5749) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 1724968387 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 72644472739) ^ 22999 = 10748444298 := by
        calc
          (3 : ZMod 72644472739) ^ 22999 = (3 : ZMod 72644472739) ^ (11499 + 11499 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 11499 * (3 : ZMod 72644472739) ^ 11499) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 10748444298 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 72644472739) ^ 45999 = 28151621712 := by
        calc
          (3 : ZMod 72644472739) ^ 45999 = (3 : ZMod 72644472739) ^ (22999 + 22999 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = ((3 : ZMod 72644472739) ^ 22999 * (3 : ZMod 72644472739) ^ 22999) * (3 : ZMod 72644472739) := by rw [pow_succ, pow_add]
          _ = 28151621712 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 72644472739) ^ 91998 = 13090647370 := by
        calc
          (3 : ZMod 72644472739) ^ 91998 = (3 : ZMod 72644472739) ^ (45999 + 45999) :=
            congrArg (fun n : ℕ => (3 : ZMod 72644472739) ^ n) (by norm_num)
          _ = (3 : ZMod 72644472739) ^ 45999 * (3 : ZMod 72644472739) ^ 45999 := by rw [pow_add]
          _ = 13090647370 := by rw [factor_4_15]; decide
      change (3 : ZMod 72644472739) ^ 91998 ≠ 1
      rw [factor_4_16]
      decide

#print axioms prime_lucas_72644472739

end TotientTailPeriodKiller
end Erdos249257
