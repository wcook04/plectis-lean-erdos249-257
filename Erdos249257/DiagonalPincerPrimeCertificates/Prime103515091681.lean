import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_103515091681 : Nat.Prime 103515091681 := by
  apply lucas_primality 103515091681 (43 : ZMod 103515091681)
  ·
      have fermat_0 : (43 : ZMod 103515091681) ^ 1 = 43 := by norm_num
      have fermat_1 : (43 : ZMod 103515091681) ^ 3 = 79507 := by
        calc
          (43 : ZMod 103515091681) ^ 3 = (43 : ZMod 103515091681) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 1 * (43 : ZMod 103515091681) ^ 1) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 79507 := by rw [fermat_0]; decide
      have fermat_2 : (43 : ZMod 103515091681) ^ 6 = 6321363049 := by
        calc
          (43 : ZMod 103515091681) ^ 6 = (43 : ZMod 103515091681) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 3 * (43 : ZMod 103515091681) ^ 3 := by rw [pow_add]
          _ = 6321363049 := by rw [fermat_1]; decide
      have fermat_3 : (43 : ZMod 103515091681) ^ 12 = 45896929620 := by
        calc
          (43 : ZMod 103515091681) ^ 12 = (43 : ZMod 103515091681) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 6 * (43 : ZMod 103515091681) ^ 6 := by rw [pow_add]
          _ = 45896929620 := by rw [fermat_2]; decide
      have fermat_4 : (43 : ZMod 103515091681) ^ 24 = 50772018725 := by
        calc
          (43 : ZMod 103515091681) ^ 24 = (43 : ZMod 103515091681) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 12 * (43 : ZMod 103515091681) ^ 12 := by rw [pow_add]
          _ = 50772018725 := by rw [fermat_3]; decide
      have fermat_5 : (43 : ZMod 103515091681) ^ 48 = 93465565319 := by
        calc
          (43 : ZMod 103515091681) ^ 48 = (43 : ZMod 103515091681) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 24 * (43 : ZMod 103515091681) ^ 24 := by rw [pow_add]
          _ = 93465565319 := by rw [fermat_4]; decide
      have fermat_6 : (43 : ZMod 103515091681) ^ 96 = 89450815400 := by
        calc
          (43 : ZMod 103515091681) ^ 96 = (43 : ZMod 103515091681) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 48 * (43 : ZMod 103515091681) ^ 48 := by rw [pow_add]
          _ = 89450815400 := by rw [fermat_5]; decide
      have fermat_7 : (43 : ZMod 103515091681) ^ 192 = 9150839835 := by
        calc
          (43 : ZMod 103515091681) ^ 192 = (43 : ZMod 103515091681) ^ (96 + 96) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 96 * (43 : ZMod 103515091681) ^ 96 := by rw [pow_add]
          _ = 9150839835 := by rw [fermat_6]; decide
      have fermat_8 : (43 : ZMod 103515091681) ^ 385 = 87021364228 := by
        calc
          (43 : ZMod 103515091681) ^ 385 = (43 : ZMod 103515091681) ^ (192 + 192 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 192 * (43 : ZMod 103515091681) ^ 192) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 87021364228 := by rw [fermat_7]; decide
      have fermat_9 : (43 : ZMod 103515091681) ^ 771 = 78809797975 := by
        calc
          (43 : ZMod 103515091681) ^ 771 = (43 : ZMod 103515091681) ^ (385 + 385 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 385 * (43 : ZMod 103515091681) ^ 385) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 78809797975 := by rw [fermat_8]; decide
      have fermat_10 : (43 : ZMod 103515091681) ^ 1542 = 62321728929 := by
        calc
          (43 : ZMod 103515091681) ^ 1542 = (43 : ZMod 103515091681) ^ (771 + 771) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 771 * (43 : ZMod 103515091681) ^ 771 := by rw [pow_add]
          _ = 62321728929 := by rw [fermat_9]; decide
      have fermat_11 : (43 : ZMod 103515091681) ^ 3084 = 67963593029 := by
        calc
          (43 : ZMod 103515091681) ^ 3084 = (43 : ZMod 103515091681) ^ (1542 + 1542) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1542 * (43 : ZMod 103515091681) ^ 1542 := by rw [pow_add]
          _ = 67963593029 := by rw [fermat_10]; decide
      have fermat_12 : (43 : ZMod 103515091681) ^ 6169 = 41905302585 := by
        calc
          (43 : ZMod 103515091681) ^ 6169 = (43 : ZMod 103515091681) ^ (3084 + 3084 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 3084 * (43 : ZMod 103515091681) ^ 3084) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 41905302585 := by rw [fermat_11]; decide
      have fermat_13 : (43 : ZMod 103515091681) ^ 12339 = 52603363840 := by
        calc
          (43 : ZMod 103515091681) ^ 12339 = (43 : ZMod 103515091681) ^ (6169 + 6169 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 6169 * (43 : ZMod 103515091681) ^ 6169) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 52603363840 := by rw [fermat_12]; decide
      have fermat_14 : (43 : ZMod 103515091681) ^ 24679 = 57375519900 := by
        calc
          (43 : ZMod 103515091681) ^ 24679 = (43 : ZMod 103515091681) ^ (12339 + 12339 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 12339 * (43 : ZMod 103515091681) ^ 12339) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 57375519900 := by rw [fermat_13]; decide
      have fermat_15 : (43 : ZMod 103515091681) ^ 49359 = 97562224551 := by
        calc
          (43 : ZMod 103515091681) ^ 49359 = (43 : ZMod 103515091681) ^ (24679 + 24679 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 24679 * (43 : ZMod 103515091681) ^ 24679) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 97562224551 := by rw [fermat_14]; decide
      have fermat_16 : (43 : ZMod 103515091681) ^ 98719 = 71297909700 := by
        calc
          (43 : ZMod 103515091681) ^ 98719 = (43 : ZMod 103515091681) ^ (49359 + 49359 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 49359 * (43 : ZMod 103515091681) ^ 49359) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 71297909700 := by rw [fermat_15]; decide
      have fermat_17 : (43 : ZMod 103515091681) ^ 197439 = 88252929987 := by
        calc
          (43 : ZMod 103515091681) ^ 197439 = (43 : ZMod 103515091681) ^ (98719 + 98719 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 98719 * (43 : ZMod 103515091681) ^ 98719) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 88252929987 := by rw [fermat_16]; decide
      have fermat_18 : (43 : ZMod 103515091681) ^ 394878 = 53177698485 := by
        calc
          (43 : ZMod 103515091681) ^ 394878 = (43 : ZMod 103515091681) ^ (197439 + 197439) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 197439 * (43 : ZMod 103515091681) ^ 197439 := by rw [pow_add]
          _ = 53177698485 := by rw [fermat_17]; decide
      have fermat_19 : (43 : ZMod 103515091681) ^ 789757 = 81942682516 := by
        calc
          (43 : ZMod 103515091681) ^ 789757 = (43 : ZMod 103515091681) ^ (394878 + 394878 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 394878 * (43 : ZMod 103515091681) ^ 394878) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 81942682516 := by rw [fermat_18]; decide
      have fermat_20 : (43 : ZMod 103515091681) ^ 1579514 = 102827103966 := by
        calc
          (43 : ZMod 103515091681) ^ 1579514 = (43 : ZMod 103515091681) ^ (789757 + 789757) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 789757 * (43 : ZMod 103515091681) ^ 789757 := by rw [pow_add]
          _ = 102827103966 := by rw [fermat_19]; decide
      have fermat_21 : (43 : ZMod 103515091681) ^ 3159029 = 54825386013 := by
        calc
          (43 : ZMod 103515091681) ^ 3159029 = (43 : ZMod 103515091681) ^ (1579514 + 1579514 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 1579514 * (43 : ZMod 103515091681) ^ 1579514) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 54825386013 := by rw [fermat_20]; decide
      have fermat_22 : (43 : ZMod 103515091681) ^ 6318059 = 84321679336 := by
        calc
          (43 : ZMod 103515091681) ^ 6318059 = (43 : ZMod 103515091681) ^ (3159029 + 3159029 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 3159029 * (43 : ZMod 103515091681) ^ 3159029) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 84321679336 := by rw [fermat_21]; decide
      have fermat_23 : (43 : ZMod 103515091681) ^ 12636119 = 56311839678 := by
        calc
          (43 : ZMod 103515091681) ^ 12636119 = (43 : ZMod 103515091681) ^ (6318059 + 6318059 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 6318059 * (43 : ZMod 103515091681) ^ 6318059) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 56311839678 := by rw [fermat_22]; decide
      have fermat_24 : (43 : ZMod 103515091681) ^ 25272239 = 1920870323 := by
        calc
          (43 : ZMod 103515091681) ^ 25272239 = (43 : ZMod 103515091681) ^ (12636119 + 12636119 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 12636119 * (43 : ZMod 103515091681) ^ 12636119) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 1920870323 := by rw [fermat_23]; decide
      have fermat_25 : (43 : ZMod 103515091681) ^ 50544478 = 43994544958 := by
        calc
          (43 : ZMod 103515091681) ^ 50544478 = (43 : ZMod 103515091681) ^ (25272239 + 25272239) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 25272239 * (43 : ZMod 103515091681) ^ 25272239 := by rw [pow_add]
          _ = 43994544958 := by rw [fermat_24]; decide
      have fermat_26 : (43 : ZMod 103515091681) ^ 101088956 = 27504166541 := by
        calc
          (43 : ZMod 103515091681) ^ 101088956 = (43 : ZMod 103515091681) ^ (50544478 + 50544478) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 50544478 * (43 : ZMod 103515091681) ^ 50544478 := by rw [pow_add]
          _ = 27504166541 := by rw [fermat_25]; decide
      have fermat_27 : (43 : ZMod 103515091681) ^ 202177913 = 52840493163 := by
        calc
          (43 : ZMod 103515091681) ^ 202177913 = (43 : ZMod 103515091681) ^ (101088956 + 101088956 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 101088956 * (43 : ZMod 103515091681) ^ 101088956) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 52840493163 := by rw [fermat_26]; decide
      have fermat_28 : (43 : ZMod 103515091681) ^ 404355826 = 25140706500 := by
        calc
          (43 : ZMod 103515091681) ^ 404355826 = (43 : ZMod 103515091681) ^ (202177913 + 202177913) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 202177913 * (43 : ZMod 103515091681) ^ 202177913 := by rw [pow_add]
          _ = 25140706500 := by rw [fermat_27]; decide
      have fermat_29 : (43 : ZMod 103515091681) ^ 808711653 = 23135531709 := by
        calc
          (43 : ZMod 103515091681) ^ 808711653 = (43 : ZMod 103515091681) ^ (404355826 + 404355826 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 404355826 * (43 : ZMod 103515091681) ^ 404355826) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 23135531709 := by rw [fermat_28]; decide
      have fermat_30 : (43 : ZMod 103515091681) ^ 1617423307 = 102920664334 := by
        calc
          (43 : ZMod 103515091681) ^ 1617423307 = (43 : ZMod 103515091681) ^ (808711653 + 808711653 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 808711653 * (43 : ZMod 103515091681) ^ 808711653) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 102920664334 := by rw [fermat_29]; decide
      have fermat_31 : (43 : ZMod 103515091681) ^ 3234846615 = 82256170241 := by
        calc
          (43 : ZMod 103515091681) ^ 3234846615 = (43 : ZMod 103515091681) ^ (1617423307 + 1617423307 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 1617423307 * (43 : ZMod 103515091681) ^ 1617423307) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 82256170241 := by rw [fermat_30]; decide
      have fermat_32 : (43 : ZMod 103515091681) ^ 6469693230 = 78111528307 := by
        calc
          (43 : ZMod 103515091681) ^ 6469693230 = (43 : ZMod 103515091681) ^ (3234846615 + 3234846615) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 3234846615 * (43 : ZMod 103515091681) ^ 3234846615 := by rw [pow_add]
          _ = 78111528307 := by rw [fermat_31]; decide
      have fermat_33 : (43 : ZMod 103515091681) ^ 12939386460 = 33515110342 := by
        calc
          (43 : ZMod 103515091681) ^ 12939386460 = (43 : ZMod 103515091681) ^ (6469693230 + 6469693230) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 6469693230 * (43 : ZMod 103515091681) ^ 6469693230 := by rw [pow_add]
          _ = 33515110342 := by rw [fermat_32]; decide
      have fermat_34 : (43 : ZMod 103515091681) ^ 25878772920 = 90885795945 := by
        calc
          (43 : ZMod 103515091681) ^ 25878772920 = (43 : ZMod 103515091681) ^ (12939386460 + 12939386460) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 12939386460 * (43 : ZMod 103515091681) ^ 12939386460 := by rw [pow_add]
          _ = 90885795945 := by rw [fermat_33]; decide
      have fermat_35 : (43 : ZMod 103515091681) ^ 51757545840 = 103515091680 := by
        calc
          (43 : ZMod 103515091681) ^ 51757545840 = (43 : ZMod 103515091681) ^ (25878772920 + 25878772920) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 25878772920 * (43 : ZMod 103515091681) ^ 25878772920 := by rw [pow_add]
          _ = 103515091680 := by rw [fermat_34]; decide
      have fermat_36 : (43 : ZMod 103515091681) ^ 103515091680 = 1 := by
        calc
          (43 : ZMod 103515091681) ^ 103515091680 = (43 : ZMod 103515091681) ^ (51757545840 + 51757545840) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 51757545840 * (43 : ZMod 103515091681) ^ 51757545840 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod = 103515091681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (43 : ZMod 103515091681) ^ 1 = 43 := by norm_num
      have factor_0_1 : (43 : ZMod 103515091681) ^ 3 = 79507 := by
        calc
          (43 : ZMod 103515091681) ^ 3 = (43 : ZMod 103515091681) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 1 * (43 : ZMod 103515091681) ^ 1) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 79507 := by rw [factor_0_0]; decide
      have factor_0_2 : (43 : ZMod 103515091681) ^ 6 = 6321363049 := by
        calc
          (43 : ZMod 103515091681) ^ 6 = (43 : ZMod 103515091681) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 3 * (43 : ZMod 103515091681) ^ 3 := by rw [pow_add]
          _ = 6321363049 := by rw [factor_0_1]; decide
      have factor_0_3 : (43 : ZMod 103515091681) ^ 12 = 45896929620 := by
        calc
          (43 : ZMod 103515091681) ^ 12 = (43 : ZMod 103515091681) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 6 * (43 : ZMod 103515091681) ^ 6 := by rw [pow_add]
          _ = 45896929620 := by rw [factor_0_2]; decide
      have factor_0_4 : (43 : ZMod 103515091681) ^ 24 = 50772018725 := by
        calc
          (43 : ZMod 103515091681) ^ 24 = (43 : ZMod 103515091681) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 12 * (43 : ZMod 103515091681) ^ 12 := by rw [pow_add]
          _ = 50772018725 := by rw [factor_0_3]; decide
      have factor_0_5 : (43 : ZMod 103515091681) ^ 48 = 93465565319 := by
        calc
          (43 : ZMod 103515091681) ^ 48 = (43 : ZMod 103515091681) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 24 * (43 : ZMod 103515091681) ^ 24 := by rw [pow_add]
          _ = 93465565319 := by rw [factor_0_4]; decide
      have factor_0_6 : (43 : ZMod 103515091681) ^ 96 = 89450815400 := by
        calc
          (43 : ZMod 103515091681) ^ 96 = (43 : ZMod 103515091681) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 48 * (43 : ZMod 103515091681) ^ 48 := by rw [pow_add]
          _ = 89450815400 := by rw [factor_0_5]; decide
      have factor_0_7 : (43 : ZMod 103515091681) ^ 192 = 9150839835 := by
        calc
          (43 : ZMod 103515091681) ^ 192 = (43 : ZMod 103515091681) ^ (96 + 96) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 96 * (43 : ZMod 103515091681) ^ 96 := by rw [pow_add]
          _ = 9150839835 := by rw [factor_0_6]; decide
      have factor_0_8 : (43 : ZMod 103515091681) ^ 385 = 87021364228 := by
        calc
          (43 : ZMod 103515091681) ^ 385 = (43 : ZMod 103515091681) ^ (192 + 192 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 192 * (43 : ZMod 103515091681) ^ 192) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 87021364228 := by rw [factor_0_7]; decide
      have factor_0_9 : (43 : ZMod 103515091681) ^ 771 = 78809797975 := by
        calc
          (43 : ZMod 103515091681) ^ 771 = (43 : ZMod 103515091681) ^ (385 + 385 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 385 * (43 : ZMod 103515091681) ^ 385) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 78809797975 := by rw [factor_0_8]; decide
      have factor_0_10 : (43 : ZMod 103515091681) ^ 1542 = 62321728929 := by
        calc
          (43 : ZMod 103515091681) ^ 1542 = (43 : ZMod 103515091681) ^ (771 + 771) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 771 * (43 : ZMod 103515091681) ^ 771 := by rw [pow_add]
          _ = 62321728929 := by rw [factor_0_9]; decide
      have factor_0_11 : (43 : ZMod 103515091681) ^ 3084 = 67963593029 := by
        calc
          (43 : ZMod 103515091681) ^ 3084 = (43 : ZMod 103515091681) ^ (1542 + 1542) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1542 * (43 : ZMod 103515091681) ^ 1542 := by rw [pow_add]
          _ = 67963593029 := by rw [factor_0_10]; decide
      have factor_0_12 : (43 : ZMod 103515091681) ^ 6169 = 41905302585 := by
        calc
          (43 : ZMod 103515091681) ^ 6169 = (43 : ZMod 103515091681) ^ (3084 + 3084 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 3084 * (43 : ZMod 103515091681) ^ 3084) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 41905302585 := by rw [factor_0_11]; decide
      have factor_0_13 : (43 : ZMod 103515091681) ^ 12339 = 52603363840 := by
        calc
          (43 : ZMod 103515091681) ^ 12339 = (43 : ZMod 103515091681) ^ (6169 + 6169 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 6169 * (43 : ZMod 103515091681) ^ 6169) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 52603363840 := by rw [factor_0_12]; decide
      have factor_0_14 : (43 : ZMod 103515091681) ^ 24679 = 57375519900 := by
        calc
          (43 : ZMod 103515091681) ^ 24679 = (43 : ZMod 103515091681) ^ (12339 + 12339 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 12339 * (43 : ZMod 103515091681) ^ 12339) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 57375519900 := by rw [factor_0_13]; decide
      have factor_0_15 : (43 : ZMod 103515091681) ^ 49359 = 97562224551 := by
        calc
          (43 : ZMod 103515091681) ^ 49359 = (43 : ZMod 103515091681) ^ (24679 + 24679 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 24679 * (43 : ZMod 103515091681) ^ 24679) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 97562224551 := by rw [factor_0_14]; decide
      have factor_0_16 : (43 : ZMod 103515091681) ^ 98719 = 71297909700 := by
        calc
          (43 : ZMod 103515091681) ^ 98719 = (43 : ZMod 103515091681) ^ (49359 + 49359 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 49359 * (43 : ZMod 103515091681) ^ 49359) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 71297909700 := by rw [factor_0_15]; decide
      have factor_0_17 : (43 : ZMod 103515091681) ^ 197439 = 88252929987 := by
        calc
          (43 : ZMod 103515091681) ^ 197439 = (43 : ZMod 103515091681) ^ (98719 + 98719 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 98719 * (43 : ZMod 103515091681) ^ 98719) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 88252929987 := by rw [factor_0_16]; decide
      have factor_0_18 : (43 : ZMod 103515091681) ^ 394878 = 53177698485 := by
        calc
          (43 : ZMod 103515091681) ^ 394878 = (43 : ZMod 103515091681) ^ (197439 + 197439) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 197439 * (43 : ZMod 103515091681) ^ 197439 := by rw [pow_add]
          _ = 53177698485 := by rw [factor_0_17]; decide
      have factor_0_19 : (43 : ZMod 103515091681) ^ 789757 = 81942682516 := by
        calc
          (43 : ZMod 103515091681) ^ 789757 = (43 : ZMod 103515091681) ^ (394878 + 394878 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 394878 * (43 : ZMod 103515091681) ^ 394878) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 81942682516 := by rw [factor_0_18]; decide
      have factor_0_20 : (43 : ZMod 103515091681) ^ 1579514 = 102827103966 := by
        calc
          (43 : ZMod 103515091681) ^ 1579514 = (43 : ZMod 103515091681) ^ (789757 + 789757) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 789757 * (43 : ZMod 103515091681) ^ 789757 := by rw [pow_add]
          _ = 102827103966 := by rw [factor_0_19]; decide
      have factor_0_21 : (43 : ZMod 103515091681) ^ 3159029 = 54825386013 := by
        calc
          (43 : ZMod 103515091681) ^ 3159029 = (43 : ZMod 103515091681) ^ (1579514 + 1579514 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 1579514 * (43 : ZMod 103515091681) ^ 1579514) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 54825386013 := by rw [factor_0_20]; decide
      have factor_0_22 : (43 : ZMod 103515091681) ^ 6318059 = 84321679336 := by
        calc
          (43 : ZMod 103515091681) ^ 6318059 = (43 : ZMod 103515091681) ^ (3159029 + 3159029 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 3159029 * (43 : ZMod 103515091681) ^ 3159029) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 84321679336 := by rw [factor_0_21]; decide
      have factor_0_23 : (43 : ZMod 103515091681) ^ 12636119 = 56311839678 := by
        calc
          (43 : ZMod 103515091681) ^ 12636119 = (43 : ZMod 103515091681) ^ (6318059 + 6318059 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 6318059 * (43 : ZMod 103515091681) ^ 6318059) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 56311839678 := by rw [factor_0_22]; decide
      have factor_0_24 : (43 : ZMod 103515091681) ^ 25272239 = 1920870323 := by
        calc
          (43 : ZMod 103515091681) ^ 25272239 = (43 : ZMod 103515091681) ^ (12636119 + 12636119 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 12636119 * (43 : ZMod 103515091681) ^ 12636119) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 1920870323 := by rw [factor_0_23]; decide
      have factor_0_25 : (43 : ZMod 103515091681) ^ 50544478 = 43994544958 := by
        calc
          (43 : ZMod 103515091681) ^ 50544478 = (43 : ZMod 103515091681) ^ (25272239 + 25272239) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 25272239 * (43 : ZMod 103515091681) ^ 25272239 := by rw [pow_add]
          _ = 43994544958 := by rw [factor_0_24]; decide
      have factor_0_26 : (43 : ZMod 103515091681) ^ 101088956 = 27504166541 := by
        calc
          (43 : ZMod 103515091681) ^ 101088956 = (43 : ZMod 103515091681) ^ (50544478 + 50544478) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 50544478 * (43 : ZMod 103515091681) ^ 50544478 := by rw [pow_add]
          _ = 27504166541 := by rw [factor_0_25]; decide
      have factor_0_27 : (43 : ZMod 103515091681) ^ 202177913 = 52840493163 := by
        calc
          (43 : ZMod 103515091681) ^ 202177913 = (43 : ZMod 103515091681) ^ (101088956 + 101088956 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 101088956 * (43 : ZMod 103515091681) ^ 101088956) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 52840493163 := by rw [factor_0_26]; decide
      have factor_0_28 : (43 : ZMod 103515091681) ^ 404355826 = 25140706500 := by
        calc
          (43 : ZMod 103515091681) ^ 404355826 = (43 : ZMod 103515091681) ^ (202177913 + 202177913) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 202177913 * (43 : ZMod 103515091681) ^ 202177913 := by rw [pow_add]
          _ = 25140706500 := by rw [factor_0_27]; decide
      have factor_0_29 : (43 : ZMod 103515091681) ^ 808711653 = 23135531709 := by
        calc
          (43 : ZMod 103515091681) ^ 808711653 = (43 : ZMod 103515091681) ^ (404355826 + 404355826 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 404355826 * (43 : ZMod 103515091681) ^ 404355826) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 23135531709 := by rw [factor_0_28]; decide
      have factor_0_30 : (43 : ZMod 103515091681) ^ 1617423307 = 102920664334 := by
        calc
          (43 : ZMod 103515091681) ^ 1617423307 = (43 : ZMod 103515091681) ^ (808711653 + 808711653 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 808711653 * (43 : ZMod 103515091681) ^ 808711653) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 102920664334 := by rw [factor_0_29]; decide
      have factor_0_31 : (43 : ZMod 103515091681) ^ 3234846615 = 82256170241 := by
        calc
          (43 : ZMod 103515091681) ^ 3234846615 = (43 : ZMod 103515091681) ^ (1617423307 + 1617423307 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 1617423307 * (43 : ZMod 103515091681) ^ 1617423307) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 82256170241 := by rw [factor_0_30]; decide
      have factor_0_32 : (43 : ZMod 103515091681) ^ 6469693230 = 78111528307 := by
        calc
          (43 : ZMod 103515091681) ^ 6469693230 = (43 : ZMod 103515091681) ^ (3234846615 + 3234846615) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 3234846615 * (43 : ZMod 103515091681) ^ 3234846615 := by rw [pow_add]
          _ = 78111528307 := by rw [factor_0_31]; decide
      have factor_0_33 : (43 : ZMod 103515091681) ^ 12939386460 = 33515110342 := by
        calc
          (43 : ZMod 103515091681) ^ 12939386460 = (43 : ZMod 103515091681) ^ (6469693230 + 6469693230) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 6469693230 * (43 : ZMod 103515091681) ^ 6469693230 := by rw [pow_add]
          _ = 33515110342 := by rw [factor_0_32]; decide
      have factor_0_34 : (43 : ZMod 103515091681) ^ 25878772920 = 90885795945 := by
        calc
          (43 : ZMod 103515091681) ^ 25878772920 = (43 : ZMod 103515091681) ^ (12939386460 + 12939386460) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 12939386460 * (43 : ZMod 103515091681) ^ 12939386460 := by rw [pow_add]
          _ = 90885795945 := by rw [factor_0_33]; decide
      have factor_0_35 : (43 : ZMod 103515091681) ^ 51757545840 = 103515091680 := by
        calc
          (43 : ZMod 103515091681) ^ 51757545840 = (43 : ZMod 103515091681) ^ (25878772920 + 25878772920) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 25878772920 * (43 : ZMod 103515091681) ^ 25878772920 := by rw [pow_add]
          _ = 103515091680 := by rw [factor_0_34]; decide
      change (43 : ZMod 103515091681) ^ 51757545840 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (43 : ZMod 103515091681) ^ 1 = 43 := by norm_num
      have factor_1_1 : (43 : ZMod 103515091681) ^ 2 = 1849 := by
        calc
          (43 : ZMod 103515091681) ^ 2 = (43 : ZMod 103515091681) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1 * (43 : ZMod 103515091681) ^ 1 := by rw [pow_add]
          _ = 1849 := by rw [factor_1_0]; decide
      have factor_1_2 : (43 : ZMod 103515091681) ^ 4 = 3418801 := by
        calc
          (43 : ZMod 103515091681) ^ 4 = (43 : ZMod 103515091681) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 2 * (43 : ZMod 103515091681) ^ 2 := by rw [pow_add]
          _ = 3418801 := by rw [factor_1_1]; decide
      have factor_1_3 : (43 : ZMod 103515091681) ^ 8 = 94510009329 := by
        calc
          (43 : ZMod 103515091681) ^ 8 = (43 : ZMod 103515091681) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 4 * (43 : ZMod 103515091681) ^ 4 := by rw [pow_add]
          _ = 94510009329 := by rw [factor_1_2]; decide
      have factor_1_4 : (43 : ZMod 103515091681) ^ 16 = 48792966899 := by
        calc
          (43 : ZMod 103515091681) ^ 16 = (43 : ZMod 103515091681) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 8 * (43 : ZMod 103515091681) ^ 8 := by rw [pow_add]
          _ = 48792966899 := by rw [factor_1_3]; decide
      have factor_1_5 : (43 : ZMod 103515091681) ^ 32 = 5991554713 := by
        calc
          (43 : ZMod 103515091681) ^ 32 = (43 : ZMod 103515091681) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 16 * (43 : ZMod 103515091681) ^ 16 := by rw [pow_add]
          _ = 5991554713 := by rw [factor_1_4]; decide
      have factor_1_6 : (43 : ZMod 103515091681) ^ 64 = 74512721405 := by
        calc
          (43 : ZMod 103515091681) ^ 64 = (43 : ZMod 103515091681) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 32 * (43 : ZMod 103515091681) ^ 32 := by rw [pow_add]
          _ = 74512721405 := by rw [factor_1_5]; decide
      have factor_1_7 : (43 : ZMod 103515091681) ^ 128 = 24860795869 := by
        calc
          (43 : ZMod 103515091681) ^ 128 = (43 : ZMod 103515091681) ^ (64 + 64) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 64 * (43 : ZMod 103515091681) ^ 64 := by rw [pow_add]
          _ = 24860795869 := by rw [factor_1_6]; decide
      have factor_1_8 : (43 : ZMod 103515091681) ^ 257 = 97540312705 := by
        calc
          (43 : ZMod 103515091681) ^ 257 = (43 : ZMod 103515091681) ^ (128 + 128 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 128 * (43 : ZMod 103515091681) ^ 128) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 97540312705 := by rw [factor_1_7]; decide
      have factor_1_9 : (43 : ZMod 103515091681) ^ 514 = 30081305525 := by
        calc
          (43 : ZMod 103515091681) ^ 514 = (43 : ZMod 103515091681) ^ (257 + 257) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 257 * (43 : ZMod 103515091681) ^ 257 := by rw [pow_add]
          _ = 30081305525 := by rw [factor_1_8]; decide
      have factor_1_10 : (43 : ZMod 103515091681) ^ 1028 = 75909008342 := by
        calc
          (43 : ZMod 103515091681) ^ 1028 = (43 : ZMod 103515091681) ^ (514 + 514) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 514 * (43 : ZMod 103515091681) ^ 514 := by rw [pow_add]
          _ = 75909008342 := by rw [factor_1_9]; decide
      have factor_1_11 : (43 : ZMod 103515091681) ^ 2056 = 22056250259 := by
        calc
          (43 : ZMod 103515091681) ^ 2056 = (43 : ZMod 103515091681) ^ (1028 + 1028) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1028 * (43 : ZMod 103515091681) ^ 1028 := by rw [pow_add]
          _ = 22056250259 := by rw [factor_1_10]; decide
      have factor_1_12 : (43 : ZMod 103515091681) ^ 4113 = 26053443732 := by
        calc
          (43 : ZMod 103515091681) ^ 4113 = (43 : ZMod 103515091681) ^ (2056 + 2056 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 2056 * (43 : ZMod 103515091681) ^ 2056) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 26053443732 := by rw [factor_1_11]; decide
      have factor_1_13 : (43 : ZMod 103515091681) ^ 8226 = 54915836130 := by
        calc
          (43 : ZMod 103515091681) ^ 8226 = (43 : ZMod 103515091681) ^ (4113 + 4113) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 4113 * (43 : ZMod 103515091681) ^ 4113 := by rw [pow_add]
          _ = 54915836130 := by rw [factor_1_12]; decide
      have factor_1_14 : (43 : ZMod 103515091681) ^ 16453 = 58415547351 := by
        calc
          (43 : ZMod 103515091681) ^ 16453 = (43 : ZMod 103515091681) ^ (8226 + 8226 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 8226 * (43 : ZMod 103515091681) ^ 8226) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 58415547351 := by rw [factor_1_13]; decide
      have factor_1_15 : (43 : ZMod 103515091681) ^ 32906 = 52952446170 := by
        calc
          (43 : ZMod 103515091681) ^ 32906 = (43 : ZMod 103515091681) ^ (16453 + 16453) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 16453 * (43 : ZMod 103515091681) ^ 16453 := by rw [pow_add]
          _ = 52952446170 := by rw [factor_1_14]; decide
      have factor_1_16 : (43 : ZMod 103515091681) ^ 65813 = 74690862098 := by
        calc
          (43 : ZMod 103515091681) ^ 65813 = (43 : ZMod 103515091681) ^ (32906 + 32906 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 32906 * (43 : ZMod 103515091681) ^ 32906) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 74690862098 := by rw [factor_1_15]; decide
      have factor_1_17 : (43 : ZMod 103515091681) ^ 131626 = 54859660576 := by
        calc
          (43 : ZMod 103515091681) ^ 131626 = (43 : ZMod 103515091681) ^ (65813 + 65813) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 65813 * (43 : ZMod 103515091681) ^ 65813 := by rw [pow_add]
          _ = 54859660576 := by rw [factor_1_16]; decide
      have factor_1_18 : (43 : ZMod 103515091681) ^ 263252 = 714161511 := by
        calc
          (43 : ZMod 103515091681) ^ 263252 = (43 : ZMod 103515091681) ^ (131626 + 131626) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 131626 * (43 : ZMod 103515091681) ^ 131626 := by rw [pow_add]
          _ = 714161511 := by rw [factor_1_17]; decide
      have factor_1_19 : (43 : ZMod 103515091681) ^ 526504 = 43449640046 := by
        calc
          (43 : ZMod 103515091681) ^ 526504 = (43 : ZMod 103515091681) ^ (263252 + 263252) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 263252 * (43 : ZMod 103515091681) ^ 263252 := by rw [pow_add]
          _ = 43449640046 := by rw [factor_1_18]; decide
      have factor_1_20 : (43 : ZMod 103515091681) ^ 1053009 = 101556102967 := by
        calc
          (43 : ZMod 103515091681) ^ 1053009 = (43 : ZMod 103515091681) ^ (526504 + 526504 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 526504 * (43 : ZMod 103515091681) ^ 526504) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 101556102967 := by rw [factor_1_19]; decide
      have factor_1_21 : (43 : ZMod 103515091681) ^ 2106019 = 59075701178 := by
        calc
          (43 : ZMod 103515091681) ^ 2106019 = (43 : ZMod 103515091681) ^ (1053009 + 1053009 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 1053009 * (43 : ZMod 103515091681) ^ 1053009) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 59075701178 := by rw [factor_1_20]; decide
      have factor_1_22 : (43 : ZMod 103515091681) ^ 4212039 = 13860800748 := by
        calc
          (43 : ZMod 103515091681) ^ 4212039 = (43 : ZMod 103515091681) ^ (2106019 + 2106019 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 2106019 * (43 : ZMod 103515091681) ^ 2106019) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 13860800748 := by rw [factor_1_21]; decide
      have factor_1_23 : (43 : ZMod 103515091681) ^ 8424079 = 6895442019 := by
        calc
          (43 : ZMod 103515091681) ^ 8424079 = (43 : ZMod 103515091681) ^ (4212039 + 4212039 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 4212039 * (43 : ZMod 103515091681) ^ 4212039) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 6895442019 := by rw [factor_1_22]; decide
      have factor_1_24 : (43 : ZMod 103515091681) ^ 16848159 = 4997230635 := by
        calc
          (43 : ZMod 103515091681) ^ 16848159 = (43 : ZMod 103515091681) ^ (8424079 + 8424079 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 8424079 * (43 : ZMod 103515091681) ^ 8424079) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 4997230635 := by rw [factor_1_23]; decide
      have factor_1_25 : (43 : ZMod 103515091681) ^ 33696318 = 87177942086 := by
        calc
          (43 : ZMod 103515091681) ^ 33696318 = (43 : ZMod 103515091681) ^ (16848159 + 16848159) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 16848159 * (43 : ZMod 103515091681) ^ 16848159 := by rw [pow_add]
          _ = 87177942086 := by rw [factor_1_24]; decide
      have factor_1_26 : (43 : ZMod 103515091681) ^ 67392637 = 34276396769 := by
        calc
          (43 : ZMod 103515091681) ^ 67392637 = (43 : ZMod 103515091681) ^ (33696318 + 33696318 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 33696318 * (43 : ZMod 103515091681) ^ 33696318) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 34276396769 := by rw [factor_1_25]; decide
      have factor_1_27 : (43 : ZMod 103515091681) ^ 134785275 = 59577154861 := by
        calc
          (43 : ZMod 103515091681) ^ 134785275 = (43 : ZMod 103515091681) ^ (67392637 + 67392637 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 67392637 * (43 : ZMod 103515091681) ^ 67392637) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 59577154861 := by rw [factor_1_26]; decide
      have factor_1_28 : (43 : ZMod 103515091681) ^ 269570551 = 29069097543 := by
        calc
          (43 : ZMod 103515091681) ^ 269570551 = (43 : ZMod 103515091681) ^ (134785275 + 134785275 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 134785275 * (43 : ZMod 103515091681) ^ 134785275) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 29069097543 := by rw [factor_1_27]; decide
      have factor_1_29 : (43 : ZMod 103515091681) ^ 539141102 = 63519358867 := by
        calc
          (43 : ZMod 103515091681) ^ 539141102 = (43 : ZMod 103515091681) ^ (269570551 + 269570551) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 269570551 * (43 : ZMod 103515091681) ^ 269570551 := by rw [pow_add]
          _ = 63519358867 := by rw [factor_1_28]; decide
      have factor_1_30 : (43 : ZMod 103515091681) ^ 1078282205 = 10014548594 := by
        calc
          (43 : ZMod 103515091681) ^ 1078282205 = (43 : ZMod 103515091681) ^ (539141102 + 539141102 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 539141102 * (43 : ZMod 103515091681) ^ 539141102) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 10014548594 := by rw [factor_1_29]; decide
      have factor_1_31 : (43 : ZMod 103515091681) ^ 2156564410 = 35880695566 := by
        calc
          (43 : ZMod 103515091681) ^ 2156564410 = (43 : ZMod 103515091681) ^ (1078282205 + 1078282205) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1078282205 * (43 : ZMod 103515091681) ^ 1078282205 := by rw [pow_add]
          _ = 35880695566 := by rw [factor_1_30]; decide
      have factor_1_32 : (43 : ZMod 103515091681) ^ 4313128820 = 19974882943 := by
        calc
          (43 : ZMod 103515091681) ^ 4313128820 = (43 : ZMod 103515091681) ^ (2156564410 + 2156564410) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 2156564410 * (43 : ZMod 103515091681) ^ 2156564410 := by rw [pow_add]
          _ = 19974882943 := by rw [factor_1_31]; decide
      have factor_1_33 : (43 : ZMod 103515091681) ^ 8626257640 = 34480369483 := by
        calc
          (43 : ZMod 103515091681) ^ 8626257640 = (43 : ZMod 103515091681) ^ (4313128820 + 4313128820) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 4313128820 * (43 : ZMod 103515091681) ^ 4313128820 := by rw [pow_add]
          _ = 34480369483 := by rw [factor_1_32]; decide
      have factor_1_34 : (43 : ZMod 103515091681) ^ 17252515280 = 40574968479 := by
        calc
          (43 : ZMod 103515091681) ^ 17252515280 = (43 : ZMod 103515091681) ^ (8626257640 + 8626257640) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 8626257640 * (43 : ZMod 103515091681) ^ 8626257640 := by rw [pow_add]
          _ = 40574968479 := by rw [factor_1_33]; decide
      have factor_1_35 : (43 : ZMod 103515091681) ^ 34505030560 = 40574968478 := by
        calc
          (43 : ZMod 103515091681) ^ 34505030560 = (43 : ZMod 103515091681) ^ (17252515280 + 17252515280) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 17252515280 * (43 : ZMod 103515091681) ^ 17252515280 := by rw [pow_add]
          _ = 40574968478 := by rw [factor_1_34]; decide
      change (43 : ZMod 103515091681) ^ 34505030560 ≠ 1
      rw [factor_1_35]
      decide
    ·
      have factor_2_0 : (43 : ZMod 103515091681) ^ 1 = 43 := by norm_num
      have factor_2_1 : (43 : ZMod 103515091681) ^ 2 = 1849 := by
        calc
          (43 : ZMod 103515091681) ^ 2 = (43 : ZMod 103515091681) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1 * (43 : ZMod 103515091681) ^ 1 := by rw [pow_add]
          _ = 1849 := by rw [factor_2_0]; decide
      have factor_2_2 : (43 : ZMod 103515091681) ^ 4 = 3418801 := by
        calc
          (43 : ZMod 103515091681) ^ 4 = (43 : ZMod 103515091681) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 2 * (43 : ZMod 103515091681) ^ 2 := by rw [pow_add]
          _ = 3418801 := by rw [factor_2_1]; decide
      have factor_2_3 : (43 : ZMod 103515091681) ^ 9 = 26841825588 := by
        calc
          (43 : ZMod 103515091681) ^ 9 = (43 : ZMod 103515091681) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 4 * (43 : ZMod 103515091681) ^ 4) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 26841825588 := by rw [factor_2_2]; decide
      have factor_2_4 : (43 : ZMod 103515091681) ^ 19 = 50843401637 := by
        calc
          (43 : ZMod 103515091681) ^ 19 = (43 : ZMod 103515091681) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 9 * (43 : ZMod 103515091681) ^ 9) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 50843401637 := by rw [factor_2_3]; decide
      have factor_2_5 : (43 : ZMod 103515091681) ^ 38 = 68368932624 := by
        calc
          (43 : ZMod 103515091681) ^ 38 = (43 : ZMod 103515091681) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 19 * (43 : ZMod 103515091681) ^ 19 := by rw [pow_add]
          _ = 68368932624 := by rw [factor_2_4]; decide
      have factor_2_6 : (43 : ZMod 103515091681) ^ 77 = 38927055572 := by
        calc
          (43 : ZMod 103515091681) ^ 77 = (43 : ZMod 103515091681) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 38 * (43 : ZMod 103515091681) ^ 38) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 38927055572 := by rw [factor_2_5]; decide
      have factor_2_7 : (43 : ZMod 103515091681) ^ 154 = 39393464476 := by
        calc
          (43 : ZMod 103515091681) ^ 154 = (43 : ZMod 103515091681) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 77 * (43 : ZMod 103515091681) ^ 77 := by rw [pow_add]
          _ = 39393464476 := by rw [factor_2_6]; decide
      have factor_2_8 : (43 : ZMod 103515091681) ^ 308 = 45079839178 := by
        calc
          (43 : ZMod 103515091681) ^ 308 = (43 : ZMod 103515091681) ^ (154 + 154) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 154 * (43 : ZMod 103515091681) ^ 154 := by rw [pow_add]
          _ = 45079839178 := by rw [factor_2_7]; decide
      have factor_2_9 : (43 : ZMod 103515091681) ^ 616 = 39968767038 := by
        calc
          (43 : ZMod 103515091681) ^ 616 = (43 : ZMod 103515091681) ^ (308 + 308) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 308 * (43 : ZMod 103515091681) ^ 308 := by rw [pow_add]
          _ = 39968767038 := by rw [factor_2_8]; decide
      have factor_2_10 : (43 : ZMod 103515091681) ^ 1233 = 10017212386 := by
        calc
          (43 : ZMod 103515091681) ^ 1233 = (43 : ZMod 103515091681) ^ (616 + 616 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 616 * (43 : ZMod 103515091681) ^ 616) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 10017212386 := by rw [factor_2_9]; decide
      have factor_2_11 : (43 : ZMod 103515091681) ^ 2467 = 46552820282 := by
        calc
          (43 : ZMod 103515091681) ^ 2467 = (43 : ZMod 103515091681) ^ (1233 + 1233 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 1233 * (43 : ZMod 103515091681) ^ 1233) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 46552820282 := by rw [factor_2_10]; decide
      have factor_2_12 : (43 : ZMod 103515091681) ^ 4935 = 15850523420 := by
        calc
          (43 : ZMod 103515091681) ^ 4935 = (43 : ZMod 103515091681) ^ (2467 + 2467 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 2467 * (43 : ZMod 103515091681) ^ 2467) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 15850523420 := by rw [factor_2_11]; decide
      have factor_2_13 : (43 : ZMod 103515091681) ^ 9871 = 627403518 := by
        calc
          (43 : ZMod 103515091681) ^ 9871 = (43 : ZMod 103515091681) ^ (4935 + 4935 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 4935 * (43 : ZMod 103515091681) ^ 4935) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 627403518 := by rw [factor_2_12]; decide
      have factor_2_14 : (43 : ZMod 103515091681) ^ 19743 = 48771261084 := by
        calc
          (43 : ZMod 103515091681) ^ 19743 = (43 : ZMod 103515091681) ^ (9871 + 9871 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 9871 * (43 : ZMod 103515091681) ^ 9871) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 48771261084 := by rw [factor_2_13]; decide
      have factor_2_15 : (43 : ZMod 103515091681) ^ 39487 = 66858761787 := by
        calc
          (43 : ZMod 103515091681) ^ 39487 = (43 : ZMod 103515091681) ^ (19743 + 19743 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 19743 * (43 : ZMod 103515091681) ^ 19743) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 66858761787 := by rw [factor_2_14]; decide
      have factor_2_16 : (43 : ZMod 103515091681) ^ 78975 = 156251894 := by
        calc
          (43 : ZMod 103515091681) ^ 78975 = (43 : ZMod 103515091681) ^ (39487 + 39487 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 39487 * (43 : ZMod 103515091681) ^ 39487) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 156251894 := by rw [factor_2_15]; decide
      have factor_2_17 : (43 : ZMod 103515091681) ^ 157951 = 56863243581 := by
        calc
          (43 : ZMod 103515091681) ^ 157951 = (43 : ZMod 103515091681) ^ (78975 + 78975 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 78975 * (43 : ZMod 103515091681) ^ 78975) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 56863243581 := by rw [factor_2_16]; decide
      have factor_2_18 : (43 : ZMod 103515091681) ^ 315902 = 62136585203 := by
        calc
          (43 : ZMod 103515091681) ^ 315902 = (43 : ZMod 103515091681) ^ (157951 + 157951) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 157951 * (43 : ZMod 103515091681) ^ 157951 := by rw [pow_add]
          _ = 62136585203 := by rw [factor_2_17]; decide
      have factor_2_19 : (43 : ZMod 103515091681) ^ 631805 = 16788582059 := by
        calc
          (43 : ZMod 103515091681) ^ 631805 = (43 : ZMod 103515091681) ^ (315902 + 315902 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 315902 * (43 : ZMod 103515091681) ^ 315902) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 16788582059 := by rw [factor_2_18]; decide
      have factor_2_20 : (43 : ZMod 103515091681) ^ 1263611 = 17573940986 := by
        calc
          (43 : ZMod 103515091681) ^ 1263611 = (43 : ZMod 103515091681) ^ (631805 + 631805 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 631805 * (43 : ZMod 103515091681) ^ 631805) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 17573940986 := by rw [factor_2_19]; decide
      have factor_2_21 : (43 : ZMod 103515091681) ^ 2527223 = 19643688122 := by
        calc
          (43 : ZMod 103515091681) ^ 2527223 = (43 : ZMod 103515091681) ^ (1263611 + 1263611 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 1263611 * (43 : ZMod 103515091681) ^ 1263611) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 19643688122 := by rw [factor_2_20]; decide
      have factor_2_22 : (43 : ZMod 103515091681) ^ 5054447 = 94131323338 := by
        calc
          (43 : ZMod 103515091681) ^ 5054447 = (43 : ZMod 103515091681) ^ (2527223 + 2527223 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 2527223 * (43 : ZMod 103515091681) ^ 2527223) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 94131323338 := by rw [factor_2_21]; decide
      have factor_2_23 : (43 : ZMod 103515091681) ^ 10108895 = 56530082585 := by
        calc
          (43 : ZMod 103515091681) ^ 10108895 = (43 : ZMod 103515091681) ^ (5054447 + 5054447 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 5054447 * (43 : ZMod 103515091681) ^ 5054447) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 56530082585 := by rw [factor_2_22]; decide
      have factor_2_24 : (43 : ZMod 103515091681) ^ 20217791 = 1805748817 := by
        calc
          (43 : ZMod 103515091681) ^ 20217791 = (43 : ZMod 103515091681) ^ (10108895 + 10108895 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 10108895 * (43 : ZMod 103515091681) ^ 10108895) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 1805748817 := by rw [factor_2_23]; decide
      have factor_2_25 : (43 : ZMod 103515091681) ^ 40435582 = 89662465697 := by
        calc
          (43 : ZMod 103515091681) ^ 40435582 = (43 : ZMod 103515091681) ^ (20217791 + 20217791) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 20217791 * (43 : ZMod 103515091681) ^ 20217791 := by rw [pow_add]
          _ = 89662465697 := by rw [factor_2_24]; decide
      have factor_2_26 : (43 : ZMod 103515091681) ^ 80871165 = 74287602836 := by
        calc
          (43 : ZMod 103515091681) ^ 80871165 = (43 : ZMod 103515091681) ^ (40435582 + 40435582 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 40435582 * (43 : ZMod 103515091681) ^ 40435582) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 74287602836 := by rw [factor_2_25]; decide
      have factor_2_27 : (43 : ZMod 103515091681) ^ 161742330 = 24343288585 := by
        calc
          (43 : ZMod 103515091681) ^ 161742330 = (43 : ZMod 103515091681) ^ (80871165 + 80871165) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 80871165 * (43 : ZMod 103515091681) ^ 80871165 := by rw [pow_add]
          _ = 24343288585 := by rw [factor_2_26]; decide
      have factor_2_28 : (43 : ZMod 103515091681) ^ 323484661 = 20381920777 := by
        calc
          (43 : ZMod 103515091681) ^ 323484661 = (43 : ZMod 103515091681) ^ (161742330 + 161742330 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 161742330 * (43 : ZMod 103515091681) ^ 161742330) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 20381920777 := by rw [factor_2_27]; decide
      have factor_2_29 : (43 : ZMod 103515091681) ^ 646969323 = 79948449830 := by
        calc
          (43 : ZMod 103515091681) ^ 646969323 = (43 : ZMod 103515091681) ^ (323484661 + 323484661 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 323484661 * (43 : ZMod 103515091681) ^ 323484661) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 79948449830 := by rw [factor_2_28]; decide
      have factor_2_30 : (43 : ZMod 103515091681) ^ 1293938646 = 65975676265 := by
        calc
          (43 : ZMod 103515091681) ^ 1293938646 = (43 : ZMod 103515091681) ^ (646969323 + 646969323) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 646969323 * (43 : ZMod 103515091681) ^ 646969323 := by rw [pow_add]
          _ = 65975676265 := by rw [factor_2_29]; decide
      have factor_2_31 : (43 : ZMod 103515091681) ^ 2587877292 = 80438509466 := by
        calc
          (43 : ZMod 103515091681) ^ 2587877292 = (43 : ZMod 103515091681) ^ (1293938646 + 1293938646) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1293938646 * (43 : ZMod 103515091681) ^ 1293938646 := by rw [pow_add]
          _ = 80438509466 := by rw [factor_2_30]; decide
      have factor_2_32 : (43 : ZMod 103515091681) ^ 5175754584 = 13160079559 := by
        calc
          (43 : ZMod 103515091681) ^ 5175754584 = (43 : ZMod 103515091681) ^ (2587877292 + 2587877292) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 2587877292 * (43 : ZMod 103515091681) ^ 2587877292 := by rw [pow_add]
          _ = 13160079559 := by rw [factor_2_31]; decide
      have factor_2_33 : (43 : ZMod 103515091681) ^ 10351509168 = 64790114424 := by
        calc
          (43 : ZMod 103515091681) ^ 10351509168 = (43 : ZMod 103515091681) ^ (5175754584 + 5175754584) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 5175754584 * (43 : ZMod 103515091681) ^ 5175754584 := by rw [pow_add]
          _ = 64790114424 := by rw [factor_2_32]; decide
      have factor_2_34 : (43 : ZMod 103515091681) ^ 20703018336 = 73548434594 := by
        calc
          (43 : ZMod 103515091681) ^ 20703018336 = (43 : ZMod 103515091681) ^ (10351509168 + 10351509168) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 10351509168 * (43 : ZMod 103515091681) ^ 10351509168 := by rw [pow_add]
          _ = 73548434594 := by rw [factor_2_33]; decide
      change (43 : ZMod 103515091681) ^ 20703018336 ≠ 1
      rw [factor_2_34]
      decide
    ·
      have factor_3_0 : (43 : ZMod 103515091681) ^ 1 = 43 := by norm_num
      have factor_3_1 : (43 : ZMod 103515091681) ^ 3 = 79507 := by
        calc
          (43 : ZMod 103515091681) ^ 3 = (43 : ZMod 103515091681) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 1 * (43 : ZMod 103515091681) ^ 1) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 79507 := by rw [factor_3_0]; decide
      have factor_3_2 : (43 : ZMod 103515091681) ^ 6 = 6321363049 := by
        calc
          (43 : ZMod 103515091681) ^ 6 = (43 : ZMod 103515091681) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 3 * (43 : ZMod 103515091681) ^ 3 := by rw [pow_add]
          _ = 6321363049 := by rw [factor_3_1]; decide
      have factor_3_3 : (43 : ZMod 103515091681) ^ 13 = 6781231721 := by
        calc
          (43 : ZMod 103515091681) ^ 13 = (43 : ZMod 103515091681) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 6 * (43 : ZMod 103515091681) ^ 6) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 6781231721 := by rw [factor_3_2]; decide
      have factor_3_4 : (43 : ZMod 103515091681) ^ 27 = 56377576299 := by
        calc
          (43 : ZMod 103515091681) ^ 27 = (43 : ZMod 103515091681) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 13 * (43 : ZMod 103515091681) ^ 13) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 56377576299 := by rw [factor_3_3]; decide
      have factor_3_5 : (43 : ZMod 103515091681) ^ 55 = 42144885953 := by
        calc
          (43 : ZMod 103515091681) ^ 55 = (43 : ZMod 103515091681) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 27 * (43 : ZMod 103515091681) ^ 27) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 42144885953 := by rw [factor_3_4]; decide
      have factor_3_6 : (43 : ZMod 103515091681) ^ 110 = 82349939466 := by
        calc
          (43 : ZMod 103515091681) ^ 110 = (43 : ZMod 103515091681) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 55 * (43 : ZMod 103515091681) ^ 55 := by rw [pow_add]
          _ = 82349939466 := by rw [factor_3_5]; decide
      have factor_3_7 : (43 : ZMod 103515091681) ^ 220 = 18113997531 := by
        calc
          (43 : ZMod 103515091681) ^ 220 = (43 : ZMod 103515091681) ^ (110 + 110) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 110 * (43 : ZMod 103515091681) ^ 110 := by rw [pow_add]
          _ = 18113997531 := by rw [factor_3_6]; decide
      have factor_3_8 : (43 : ZMod 103515091681) ^ 440 = 77798395296 := by
        calc
          (43 : ZMod 103515091681) ^ 440 = (43 : ZMod 103515091681) ^ (220 + 220) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 220 * (43 : ZMod 103515091681) ^ 220 := by rw [pow_add]
          _ = 77798395296 := by rw [factor_3_7]; decide
      have factor_3_9 : (43 : ZMod 103515091681) ^ 881 = 81393002913 := by
        calc
          (43 : ZMod 103515091681) ^ 881 = (43 : ZMod 103515091681) ^ (440 + 440 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 440 * (43 : ZMod 103515091681) ^ 440) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 81393002913 := by rw [factor_3_8]; decide
      have factor_3_10 : (43 : ZMod 103515091681) ^ 1762 = 30875513794 := by
        calc
          (43 : ZMod 103515091681) ^ 1762 = (43 : ZMod 103515091681) ^ (881 + 881) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 881 * (43 : ZMod 103515091681) ^ 881 := by rw [pow_add]
          _ = 30875513794 := by rw [factor_3_9]; decide
      have factor_3_11 : (43 : ZMod 103515091681) ^ 3525 = 79296240891 := by
        calc
          (43 : ZMod 103515091681) ^ 3525 = (43 : ZMod 103515091681) ^ (1762 + 1762 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 1762 * (43 : ZMod 103515091681) ^ 1762) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 79296240891 := by rw [factor_3_10]; decide
      have factor_3_12 : (43 : ZMod 103515091681) ^ 7051 = 86038397979 := by
        calc
          (43 : ZMod 103515091681) ^ 7051 = (43 : ZMod 103515091681) ^ (3525 + 3525 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 3525 * (43 : ZMod 103515091681) ^ 3525) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 86038397979 := by rw [factor_3_11]; decide
      have factor_3_13 : (43 : ZMod 103515091681) ^ 14102 = 6019689316 := by
        calc
          (43 : ZMod 103515091681) ^ 14102 = (43 : ZMod 103515091681) ^ (7051 + 7051) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 7051 * (43 : ZMod 103515091681) ^ 7051 := by rw [pow_add]
          _ = 6019689316 := by rw [factor_3_12]; decide
      have factor_3_14 : (43 : ZMod 103515091681) ^ 28205 = 25898836658 := by
        calc
          (43 : ZMod 103515091681) ^ 28205 = (43 : ZMod 103515091681) ^ (14102 + 14102 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 14102 * (43 : ZMod 103515091681) ^ 14102) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 25898836658 := by rw [factor_3_13]; decide
      have factor_3_15 : (43 : ZMod 103515091681) ^ 56411 = 42335102658 := by
        calc
          (43 : ZMod 103515091681) ^ 56411 = (43 : ZMod 103515091681) ^ (28205 + 28205 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 28205 * (43 : ZMod 103515091681) ^ 28205) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 42335102658 := by rw [factor_3_14]; decide
      have factor_3_16 : (43 : ZMod 103515091681) ^ 112822 = 57225862498 := by
        calc
          (43 : ZMod 103515091681) ^ 112822 = (43 : ZMod 103515091681) ^ (56411 + 56411) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 56411 * (43 : ZMod 103515091681) ^ 56411 := by rw [pow_add]
          _ = 57225862498 := by rw [factor_3_15]; decide
      have factor_3_17 : (43 : ZMod 103515091681) ^ 225644 = 5394659629 := by
        calc
          (43 : ZMod 103515091681) ^ 225644 = (43 : ZMod 103515091681) ^ (112822 + 112822) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 112822 * (43 : ZMod 103515091681) ^ 112822 := by rw [pow_add]
          _ = 5394659629 := by rw [factor_3_16]; decide
      have factor_3_18 : (43 : ZMod 103515091681) ^ 451289 = 25830067906 := by
        calc
          (43 : ZMod 103515091681) ^ 451289 = (43 : ZMod 103515091681) ^ (225644 + 225644 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 225644 * (43 : ZMod 103515091681) ^ 225644) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 25830067906 := by rw [factor_3_17]; decide
      have factor_3_19 : (43 : ZMod 103515091681) ^ 902579 = 36284086663 := by
        calc
          (43 : ZMod 103515091681) ^ 902579 = (43 : ZMod 103515091681) ^ (451289 + 451289 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 451289 * (43 : ZMod 103515091681) ^ 451289) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 36284086663 := by rw [factor_3_18]; decide
      have factor_3_20 : (43 : ZMod 103515091681) ^ 1805159 = 78862808111 := by
        calc
          (43 : ZMod 103515091681) ^ 1805159 = (43 : ZMod 103515091681) ^ (902579 + 902579 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 902579 * (43 : ZMod 103515091681) ^ 902579) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 78862808111 := by rw [factor_3_19]; decide
      have factor_3_21 : (43 : ZMod 103515091681) ^ 3610319 = 4496079552 := by
        calc
          (43 : ZMod 103515091681) ^ 3610319 = (43 : ZMod 103515091681) ^ (1805159 + 1805159 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 1805159 * (43 : ZMod 103515091681) ^ 1805159) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 4496079552 := by rw [factor_3_20]; decide
      have factor_3_22 : (43 : ZMod 103515091681) ^ 7220639 = 50957688854 := by
        calc
          (43 : ZMod 103515091681) ^ 7220639 = (43 : ZMod 103515091681) ^ (3610319 + 3610319 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 3610319 * (43 : ZMod 103515091681) ^ 3610319) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 50957688854 := by rw [factor_3_21]; decide
      have factor_3_23 : (43 : ZMod 103515091681) ^ 14441279 = 24252403366 := by
        calc
          (43 : ZMod 103515091681) ^ 14441279 = (43 : ZMod 103515091681) ^ (7220639 + 7220639 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 7220639 * (43 : ZMod 103515091681) ^ 7220639) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 24252403366 := by rw [factor_3_22]; decide
      have factor_3_24 : (43 : ZMod 103515091681) ^ 28882559 = 66714419902 := by
        calc
          (43 : ZMod 103515091681) ^ 28882559 = (43 : ZMod 103515091681) ^ (14441279 + 14441279 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 14441279 * (43 : ZMod 103515091681) ^ 14441279) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 66714419902 := by rw [factor_3_23]; decide
      have factor_3_25 : (43 : ZMod 103515091681) ^ 57765118 = 24636483961 := by
        calc
          (43 : ZMod 103515091681) ^ 57765118 = (43 : ZMod 103515091681) ^ (28882559 + 28882559) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 28882559 * (43 : ZMod 103515091681) ^ 28882559 := by rw [pow_add]
          _ = 24636483961 := by rw [factor_3_24]; decide
      have factor_3_26 : (43 : ZMod 103515091681) ^ 115530236 = 38282091849 := by
        calc
          (43 : ZMod 103515091681) ^ 115530236 = (43 : ZMod 103515091681) ^ (57765118 + 57765118) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 57765118 * (43 : ZMod 103515091681) ^ 57765118 := by rw [pow_add]
          _ = 38282091849 := by rw [factor_3_25]; decide
      have factor_3_27 : (43 : ZMod 103515091681) ^ 231060472 = 59985733981 := by
        calc
          (43 : ZMod 103515091681) ^ 231060472 = (43 : ZMod 103515091681) ^ (115530236 + 115530236) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 115530236 * (43 : ZMod 103515091681) ^ 115530236 := by rw [pow_add]
          _ = 59985733981 := by rw [factor_3_26]; decide
      have factor_3_28 : (43 : ZMod 103515091681) ^ 462120945 = 61821616876 := by
        calc
          (43 : ZMod 103515091681) ^ 462120945 = (43 : ZMod 103515091681) ^ (231060472 + 231060472 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 231060472 * (43 : ZMod 103515091681) ^ 231060472) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 61821616876 := by rw [factor_3_27]; decide
      have factor_3_29 : (43 : ZMod 103515091681) ^ 924241890 = 10272897019 := by
        calc
          (43 : ZMod 103515091681) ^ 924241890 = (43 : ZMod 103515091681) ^ (462120945 + 462120945) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 462120945 * (43 : ZMod 103515091681) ^ 462120945 := by rw [pow_add]
          _ = 10272897019 := by rw [factor_3_28]; decide
      have factor_3_30 : (43 : ZMod 103515091681) ^ 1848483780 = 17977614014 := by
        calc
          (43 : ZMod 103515091681) ^ 1848483780 = (43 : ZMod 103515091681) ^ (924241890 + 924241890) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 924241890 * (43 : ZMod 103515091681) ^ 924241890 := by rw [pow_add]
          _ = 17977614014 := by rw [factor_3_29]; decide
      have factor_3_31 : (43 : ZMod 103515091681) ^ 3696967560 = 45100221780 := by
        calc
          (43 : ZMod 103515091681) ^ 3696967560 = (43 : ZMod 103515091681) ^ (1848483780 + 1848483780) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1848483780 * (43 : ZMod 103515091681) ^ 1848483780 := by rw [pow_add]
          _ = 45100221780 := by rw [factor_3_30]; decide
      have factor_3_32 : (43 : ZMod 103515091681) ^ 7393935120 = 97763637922 := by
        calc
          (43 : ZMod 103515091681) ^ 7393935120 = (43 : ZMod 103515091681) ^ (3696967560 + 3696967560) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 3696967560 * (43 : ZMod 103515091681) ^ 3696967560 := by rw [pow_add]
          _ = 97763637922 := by rw [factor_3_31]; decide
      have factor_3_33 : (43 : ZMod 103515091681) ^ 14787870240 = 63935153724 := by
        calc
          (43 : ZMod 103515091681) ^ 14787870240 = (43 : ZMod 103515091681) ^ (7393935120 + 7393935120) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 7393935120 * (43 : ZMod 103515091681) ^ 7393935120 := by rw [pow_add]
          _ = 63935153724 := by rw [factor_3_32]; decide
      change (43 : ZMod 103515091681) ^ 14787870240 ≠ 1
      rw [factor_3_33]
      decide
    ·
      have factor_4_0 : (43 : ZMod 103515091681) ^ 1 = 43 := by norm_num
      have factor_4_1 : (43 : ZMod 103515091681) ^ 2 = 1849 := by
        calc
          (43 : ZMod 103515091681) ^ 2 = (43 : ZMod 103515091681) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1 * (43 : ZMod 103515091681) ^ 1 := by rw [pow_add]
          _ = 1849 := by rw [factor_4_0]; decide
      have factor_4_2 : (43 : ZMod 103515091681) ^ 4 = 3418801 := by
        calc
          (43 : ZMod 103515091681) ^ 4 = (43 : ZMod 103515091681) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 2 * (43 : ZMod 103515091681) ^ 2 := by rw [pow_add]
          _ = 3418801 := by rw [factor_4_1]; decide
      have factor_4_3 : (43 : ZMod 103515091681) ^ 8 = 94510009329 := by
        calc
          (43 : ZMod 103515091681) ^ 8 = (43 : ZMod 103515091681) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 4 * (43 : ZMod 103515091681) ^ 4 := by rw [pow_add]
          _ = 94510009329 := by rw [factor_4_2]; decide
      have factor_4_4 : (43 : ZMod 103515091681) ^ 17 = 27795743037 := by
        calc
          (43 : ZMod 103515091681) ^ 17 = (43 : ZMod 103515091681) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 8 * (43 : ZMod 103515091681) ^ 8) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 27795743037 := by rw [factor_4_3]; decide
      have factor_4_5 : (43 : ZMod 103515091681) ^ 35 = 97603742210 := by
        calc
          (43 : ZMod 103515091681) ^ 35 = (43 : ZMod 103515091681) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 17 * (43 : ZMod 103515091681) ^ 17) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 97603742210 := by rw [factor_4_4]; decide
      have factor_4_6 : (43 : ZMod 103515091681) ^ 70 = 46531720728 := by
        calc
          (43 : ZMod 103515091681) ^ 70 = (43 : ZMod 103515091681) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 35 * (43 : ZMod 103515091681) ^ 35 := by rw [pow_add]
          _ = 46531720728 := by rw [factor_4_5]; decide
      have factor_4_7 : (43 : ZMod 103515091681) ^ 140 = 4852034055 := by
        calc
          (43 : ZMod 103515091681) ^ 140 = (43 : ZMod 103515091681) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 70 * (43 : ZMod 103515091681) ^ 70 := by rw [pow_add]
          _ = 4852034055 := by rw [factor_4_6]; decide
      have factor_4_8 : (43 : ZMod 103515091681) ^ 280 = 59449607785 := by
        calc
          (43 : ZMod 103515091681) ^ 280 = (43 : ZMod 103515091681) ^ (140 + 140) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 140 * (43 : ZMod 103515091681) ^ 140 := by rw [pow_add]
          _ = 59449607785 := by rw [factor_4_7]; decide
      have factor_4_9 : (43 : ZMod 103515091681) ^ 560 = 92290168337 := by
        calc
          (43 : ZMod 103515091681) ^ 560 = (43 : ZMod 103515091681) ^ (280 + 280) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 280 * (43 : ZMod 103515091681) ^ 280 := by rw [pow_add]
          _ = 92290168337 := by rw [factor_4_8]; decide
      have factor_4_10 : (43 : ZMod 103515091681) ^ 1121 = 35307995584 := by
        calc
          (43 : ZMod 103515091681) ^ 1121 = (43 : ZMod 103515091681) ^ (560 + 560 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 560 * (43 : ZMod 103515091681) ^ 560) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 35307995584 := by rw [factor_4_9]; decide
      have factor_4_11 : (43 : ZMod 103515091681) ^ 2243 = 68549352120 := by
        calc
          (43 : ZMod 103515091681) ^ 2243 = (43 : ZMod 103515091681) ^ (1121 + 1121 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 1121 * (43 : ZMod 103515091681) ^ 1121) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 68549352120 := by rw [factor_4_10]; decide
      have factor_4_12 : (43 : ZMod 103515091681) ^ 4487 = 3841104693 := by
        calc
          (43 : ZMod 103515091681) ^ 4487 = (43 : ZMod 103515091681) ^ (2243 + 2243 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 2243 * (43 : ZMod 103515091681) ^ 2243) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 3841104693 := by rw [factor_4_11]; decide
      have factor_4_13 : (43 : ZMod 103515091681) ^ 8974 = 56248558284 := by
        calc
          (43 : ZMod 103515091681) ^ 8974 = (43 : ZMod 103515091681) ^ (4487 + 4487) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 4487 * (43 : ZMod 103515091681) ^ 4487 := by rw [pow_add]
          _ = 56248558284 := by rw [factor_4_12]; decide
      have factor_4_14 : (43 : ZMod 103515091681) ^ 17949 = 4989334876 := by
        calc
          (43 : ZMod 103515091681) ^ 17949 = (43 : ZMod 103515091681) ^ (8974 + 8974 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 8974 * (43 : ZMod 103515091681) ^ 8974) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 4989334876 := by rw [factor_4_13]; decide
      have factor_4_15 : (43 : ZMod 103515091681) ^ 35898 = 55087367496 := by
        calc
          (43 : ZMod 103515091681) ^ 35898 = (43 : ZMod 103515091681) ^ (17949 + 17949) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 17949 * (43 : ZMod 103515091681) ^ 17949 := by rw [pow_add]
          _ = 55087367496 := by rw [factor_4_14]; decide
      have factor_4_16 : (43 : ZMod 103515091681) ^ 71796 = 4879415244 := by
        calc
          (43 : ZMod 103515091681) ^ 71796 = (43 : ZMod 103515091681) ^ (35898 + 35898) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 35898 * (43 : ZMod 103515091681) ^ 35898 := by rw [pow_add]
          _ = 4879415244 := by rw [factor_4_15]; decide
      have factor_4_17 : (43 : ZMod 103515091681) ^ 143592 = 100393015472 := by
        calc
          (43 : ZMod 103515091681) ^ 143592 = (43 : ZMod 103515091681) ^ (71796 + 71796) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 71796 * (43 : ZMod 103515091681) ^ 71796 := by rw [pow_add]
          _ = 100393015472 := by rw [factor_4_16]; decide
      have factor_4_18 : (43 : ZMod 103515091681) ^ 287184 = 60400390902 := by
        calc
          (43 : ZMod 103515091681) ^ 287184 = (43 : ZMod 103515091681) ^ (143592 + 143592) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 143592 * (43 : ZMod 103515091681) ^ 143592 := by rw [pow_add]
          _ = 60400390902 := by rw [factor_4_17]; decide
      have factor_4_19 : (43 : ZMod 103515091681) ^ 574369 = 82838703440 := by
        calc
          (43 : ZMod 103515091681) ^ 574369 = (43 : ZMod 103515091681) ^ (287184 + 287184 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 287184 * (43 : ZMod 103515091681) ^ 287184) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 82838703440 := by rw [factor_4_18]; decide
      have factor_4_20 : (43 : ZMod 103515091681) ^ 1148738 = 100154760882 := by
        calc
          (43 : ZMod 103515091681) ^ 1148738 = (43 : ZMod 103515091681) ^ (574369 + 574369) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 574369 * (43 : ZMod 103515091681) ^ 574369 := by rw [pow_add]
          _ = 100154760882 := by rw [factor_4_19]; decide
      have factor_4_21 : (43 : ZMod 103515091681) ^ 2297476 = 1282993447 := by
        calc
          (43 : ZMod 103515091681) ^ 2297476 = (43 : ZMod 103515091681) ^ (1148738 + 1148738) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1148738 * (43 : ZMod 103515091681) ^ 1148738 := by rw [pow_add]
          _ = 1282993447 := by rw [factor_4_20]; decide
      have factor_4_22 : (43 : ZMod 103515091681) ^ 4594952 = 40755683249 := by
        calc
          (43 : ZMod 103515091681) ^ 4594952 = (43 : ZMod 103515091681) ^ (2297476 + 2297476) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 2297476 * (43 : ZMod 103515091681) ^ 2297476 := by rw [pow_add]
          _ = 40755683249 := by rw [factor_4_21]; decide
      have factor_4_23 : (43 : ZMod 103515091681) ^ 9189905 = 3927403766 := by
        calc
          (43 : ZMod 103515091681) ^ 9189905 = (43 : ZMod 103515091681) ^ (4594952 + 4594952 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 4594952 * (43 : ZMod 103515091681) ^ 4594952) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 3927403766 := by rw [factor_4_22]; decide
      have factor_4_24 : (43 : ZMod 103515091681) ^ 18379810 = 57641287015 := by
        calc
          (43 : ZMod 103515091681) ^ 18379810 = (43 : ZMod 103515091681) ^ (9189905 + 9189905) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 9189905 * (43 : ZMod 103515091681) ^ 9189905 := by rw [pow_add]
          _ = 57641287015 := by rw [factor_4_23]; decide
      have factor_4_25 : (43 : ZMod 103515091681) ^ 36759620 = 94456822862 := by
        calc
          (43 : ZMod 103515091681) ^ 36759620 = (43 : ZMod 103515091681) ^ (18379810 + 18379810) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 18379810 * (43 : ZMod 103515091681) ^ 18379810 := by rw [pow_add]
          _ = 94456822862 := by rw [factor_4_24]; decide
      have factor_4_26 : (43 : ZMod 103515091681) ^ 73519241 = 18295471067 := by
        calc
          (43 : ZMod 103515091681) ^ 73519241 = (43 : ZMod 103515091681) ^ (36759620 + 36759620 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 36759620 * (43 : ZMod 103515091681) ^ 36759620) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 18295471067 := by rw [factor_4_25]; decide
      have factor_4_27 : (43 : ZMod 103515091681) ^ 147038482 = 36091922992 := by
        calc
          (43 : ZMod 103515091681) ^ 147038482 = (43 : ZMod 103515091681) ^ (73519241 + 73519241) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 73519241 * (43 : ZMod 103515091681) ^ 73519241 := by rw [pow_add]
          _ = 36091922992 := by rw [factor_4_26]; decide
      have factor_4_28 : (43 : ZMod 103515091681) ^ 294076965 = 100357965733 := by
        calc
          (43 : ZMod 103515091681) ^ 294076965 = (43 : ZMod 103515091681) ^ (147038482 + 147038482 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 147038482 * (43 : ZMod 103515091681) ^ 147038482) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 100357965733 := by rw [factor_4_27]; decide
      have factor_4_29 : (43 : ZMod 103515091681) ^ 588153930 = 89072678696 := by
        calc
          (43 : ZMod 103515091681) ^ 588153930 = (43 : ZMod 103515091681) ^ (294076965 + 294076965) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 294076965 * (43 : ZMod 103515091681) ^ 294076965 := by rw [pow_add]
          _ = 89072678696 := by rw [factor_4_28]; decide
      have factor_4_30 : (43 : ZMod 103515091681) ^ 1176307860 = 86242390525 := by
        calc
          (43 : ZMod 103515091681) ^ 1176307860 = (43 : ZMod 103515091681) ^ (588153930 + 588153930) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 588153930 * (43 : ZMod 103515091681) ^ 588153930 := by rw [pow_add]
          _ = 86242390525 := by rw [factor_4_29]; decide
      have factor_4_31 : (43 : ZMod 103515091681) ^ 2352615720 = 100316944242 := by
        calc
          (43 : ZMod 103515091681) ^ 2352615720 = (43 : ZMod 103515091681) ^ (1176307860 + 1176307860) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1176307860 * (43 : ZMod 103515091681) ^ 1176307860 := by rw [pow_add]
          _ = 100316944242 := by rw [factor_4_30]; decide
      have factor_4_32 : (43 : ZMod 103515091681) ^ 4705231440 = 17206348532 := by
        calc
          (43 : ZMod 103515091681) ^ 4705231440 = (43 : ZMod 103515091681) ^ (2352615720 + 2352615720) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 2352615720 * (43 : ZMod 103515091681) ^ 2352615720 := by rw [pow_add]
          _ = 17206348532 := by rw [factor_4_31]; decide
      have factor_4_33 : (43 : ZMod 103515091681) ^ 9410462880 = 24528183977 := by
        calc
          (43 : ZMod 103515091681) ^ 9410462880 = (43 : ZMod 103515091681) ^ (4705231440 + 4705231440) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 4705231440 * (43 : ZMod 103515091681) ^ 4705231440 := by rw [pow_add]
          _ = 24528183977 := by rw [factor_4_32]; decide
      change (43 : ZMod 103515091681) ^ 9410462880 ≠ 1
      rw [factor_4_33]
      decide
    ·
      have factor_5_0 : (43 : ZMod 103515091681) ^ 1 = 43 := by norm_num
      have factor_5_1 : (43 : ZMod 103515091681) ^ 3 = 79507 := by
        calc
          (43 : ZMod 103515091681) ^ 3 = (43 : ZMod 103515091681) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 1 * (43 : ZMod 103515091681) ^ 1) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 79507 := by rw [factor_5_0]; decide
      have factor_5_2 : (43 : ZMod 103515091681) ^ 7 = 64788427745 := by
        calc
          (43 : ZMod 103515091681) ^ 7 = (43 : ZMod 103515091681) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 3 * (43 : ZMod 103515091681) ^ 3) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 64788427745 := by rw [factor_5_1]; decide
      have factor_5_3 : (43 : ZMod 103515091681) ^ 14 = 84562780641 := by
        calc
          (43 : ZMod 103515091681) ^ 14 = (43 : ZMod 103515091681) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 7 * (43 : ZMod 103515091681) ^ 7 := by rw [pow_add]
          _ = 84562780641 := by rw [factor_5_2]; decide
      have factor_5_4 : (43 : ZMod 103515091681) ^ 29 = 2441254084 := by
        calc
          (43 : ZMod 103515091681) ^ 29 = (43 : ZMod 103515091681) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 14 * (43 : ZMod 103515091681) ^ 14) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 2441254084 := by rw [factor_5_3]; decide
      have factor_5_5 : (43 : ZMod 103515091681) ^ 59 = 44798201471 := by
        calc
          (43 : ZMod 103515091681) ^ 59 = (43 : ZMod 103515091681) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 29 * (43 : ZMod 103515091681) ^ 29) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 44798201471 := by rw [factor_5_4]; decide
      have factor_5_6 : (43 : ZMod 103515091681) ^ 118 = 5064272744 := by
        calc
          (43 : ZMod 103515091681) ^ 118 = (43 : ZMod 103515091681) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 59 * (43 : ZMod 103515091681) ^ 59 := by rw [pow_add]
          _ = 5064272744 := by rw [factor_5_5]; decide
      have factor_5_7 : (43 : ZMod 103515091681) ^ 237 = 77274053991 := by
        calc
          (43 : ZMod 103515091681) ^ 237 = (43 : ZMod 103515091681) ^ (118 + 118 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 118 * (43 : ZMod 103515091681) ^ 118) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 77274053991 := by rw [factor_5_6]; decide
      have factor_5_8 : (43 : ZMod 103515091681) ^ 474 = 48304797252 := by
        calc
          (43 : ZMod 103515091681) ^ 474 = (43 : ZMod 103515091681) ^ (237 + 237) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 237 * (43 : ZMod 103515091681) ^ 237 := by rw [pow_add]
          _ = 48304797252 := by rw [factor_5_7]; decide
      have factor_5_9 : (43 : ZMod 103515091681) ^ 949 = 94573111753 := by
        calc
          (43 : ZMod 103515091681) ^ 949 = (43 : ZMod 103515091681) ^ (474 + 474 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 474 * (43 : ZMod 103515091681) ^ 474) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 94573111753 := by rw [factor_5_8]; decide
      have factor_5_10 : (43 : ZMod 103515091681) ^ 1898 = 49238680163 := by
        calc
          (43 : ZMod 103515091681) ^ 1898 = (43 : ZMod 103515091681) ^ (949 + 949) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 949 * (43 : ZMod 103515091681) ^ 949 := by rw [pow_add]
          _ = 49238680163 := by rw [factor_5_9]; decide
      have factor_5_11 : (43 : ZMod 103515091681) ^ 3796 = 10663903926 := by
        calc
          (43 : ZMod 103515091681) ^ 3796 = (43 : ZMod 103515091681) ^ (1898 + 1898) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1898 * (43 : ZMod 103515091681) ^ 1898 := by rw [pow_add]
          _ = 10663903926 := by rw [factor_5_10]; decide
      have factor_5_12 : (43 : ZMod 103515091681) ^ 7593 = 75963345960 := by
        calc
          (43 : ZMod 103515091681) ^ 7593 = (43 : ZMod 103515091681) ^ (3796 + 3796 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 3796 * (43 : ZMod 103515091681) ^ 3796) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 75963345960 := by rw [factor_5_11]; decide
      have factor_5_13 : (43 : ZMod 103515091681) ^ 15187 = 1429466804 := by
        calc
          (43 : ZMod 103515091681) ^ 15187 = (43 : ZMod 103515091681) ^ (7593 + 7593 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 7593 * (43 : ZMod 103515091681) ^ 7593) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 1429466804 := by rw [factor_5_12]; decide
      have factor_5_14 : (43 : ZMod 103515091681) ^ 30375 = 8845054708 := by
        calc
          (43 : ZMod 103515091681) ^ 30375 = (43 : ZMod 103515091681) ^ (15187 + 15187 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 15187 * (43 : ZMod 103515091681) ^ 15187) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 8845054708 := by rw [factor_5_13]; decide
      have factor_5_15 : (43 : ZMod 103515091681) ^ 60750 = 83840852538 := by
        calc
          (43 : ZMod 103515091681) ^ 60750 = (43 : ZMod 103515091681) ^ (30375 + 30375) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 30375 * (43 : ZMod 103515091681) ^ 30375 := by rw [pow_add]
          _ = 83840852538 := by rw [factor_5_14]; decide
      have factor_5_16 : (43 : ZMod 103515091681) ^ 121501 = 93635691743 := by
        calc
          (43 : ZMod 103515091681) ^ 121501 = (43 : ZMod 103515091681) ^ (60750 + 60750 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 60750 * (43 : ZMod 103515091681) ^ 60750) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 93635691743 := by rw [factor_5_15]; decide
      have factor_5_17 : (43 : ZMod 103515091681) ^ 243002 = 64241383189 := by
        calc
          (43 : ZMod 103515091681) ^ 243002 = (43 : ZMod 103515091681) ^ (121501 + 121501) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 121501 * (43 : ZMod 103515091681) ^ 121501 := by rw [pow_add]
          _ = 64241383189 := by rw [factor_5_16]; decide
      have factor_5_18 : (43 : ZMod 103515091681) ^ 486004 = 44802827603 := by
        calc
          (43 : ZMod 103515091681) ^ 486004 = (43 : ZMod 103515091681) ^ (243002 + 243002) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 243002 * (43 : ZMod 103515091681) ^ 243002 := by rw [pow_add]
          _ = 44802827603 := by rw [factor_5_17]; decide
      have factor_5_19 : (43 : ZMod 103515091681) ^ 972009 = 48010821221 := by
        calc
          (43 : ZMod 103515091681) ^ 972009 = (43 : ZMod 103515091681) ^ (486004 + 486004 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 486004 * (43 : ZMod 103515091681) ^ 486004) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 48010821221 := by rw [factor_5_18]; decide
      have factor_5_20 : (43 : ZMod 103515091681) ^ 1944018 = 9174633672 := by
        calc
          (43 : ZMod 103515091681) ^ 1944018 = (43 : ZMod 103515091681) ^ (972009 + 972009) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 972009 * (43 : ZMod 103515091681) ^ 972009 := by rw [pow_add]
          _ = 9174633672 := by rw [factor_5_19]; decide
      have factor_5_21 : (43 : ZMod 103515091681) ^ 3888036 = 30614169648 := by
        calc
          (43 : ZMod 103515091681) ^ 3888036 = (43 : ZMod 103515091681) ^ (1944018 + 1944018) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1944018 * (43 : ZMod 103515091681) ^ 1944018 := by rw [pow_add]
          _ = 30614169648 := by rw [factor_5_20]; decide
      have factor_5_22 : (43 : ZMod 103515091681) ^ 7776073 = 48322509048 := by
        calc
          (43 : ZMod 103515091681) ^ 7776073 = (43 : ZMod 103515091681) ^ (3888036 + 3888036 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 3888036 * (43 : ZMod 103515091681) ^ 3888036) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 48322509048 := by rw [factor_5_21]; decide
      have factor_5_23 : (43 : ZMod 103515091681) ^ 15552147 = 61727008349 := by
        calc
          (43 : ZMod 103515091681) ^ 15552147 = (43 : ZMod 103515091681) ^ (7776073 + 7776073 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 7776073 * (43 : ZMod 103515091681) ^ 7776073) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 61727008349 := by rw [factor_5_22]; decide
      have factor_5_24 : (43 : ZMod 103515091681) ^ 31104294 = 21092941475 := by
        calc
          (43 : ZMod 103515091681) ^ 31104294 = (43 : ZMod 103515091681) ^ (15552147 + 15552147) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 15552147 * (43 : ZMod 103515091681) ^ 15552147 := by rw [pow_add]
          _ = 21092941475 := by rw [factor_5_23]; decide
      have factor_5_25 : (43 : ZMod 103515091681) ^ 62208588 = 64604628011 := by
        calc
          (43 : ZMod 103515091681) ^ 62208588 = (43 : ZMod 103515091681) ^ (31104294 + 31104294) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 31104294 * (43 : ZMod 103515091681) ^ 31104294 := by rw [pow_add]
          _ = 64604628011 := by rw [factor_5_24]; decide
      have factor_5_26 : (43 : ZMod 103515091681) ^ 124417177 = 5224330763 := by
        calc
          (43 : ZMod 103515091681) ^ 124417177 = (43 : ZMod 103515091681) ^ (62208588 + 62208588 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 62208588 * (43 : ZMod 103515091681) ^ 62208588) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 5224330763 := by rw [factor_5_25]; decide
      have factor_5_27 : (43 : ZMod 103515091681) ^ 248834355 = 97121116590 := by
        calc
          (43 : ZMod 103515091681) ^ 248834355 = (43 : ZMod 103515091681) ^ (124417177 + 124417177 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 124417177 * (43 : ZMod 103515091681) ^ 124417177) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 97121116590 := by rw [factor_5_26]; decide
      have factor_5_28 : (43 : ZMod 103515091681) ^ 497668710 = 1068434236 := by
        calc
          (43 : ZMod 103515091681) ^ 497668710 = (43 : ZMod 103515091681) ^ (248834355 + 248834355) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 248834355 * (43 : ZMod 103515091681) ^ 248834355 := by rw [pow_add]
          _ = 1068434236 := by rw [factor_5_27]; decide
      have factor_5_29 : (43 : ZMod 103515091681) ^ 995337420 = 17955112459 := by
        calc
          (43 : ZMod 103515091681) ^ 995337420 = (43 : ZMod 103515091681) ^ (497668710 + 497668710) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 497668710 * (43 : ZMod 103515091681) ^ 497668710 := by rw [pow_add]
          _ = 17955112459 := by rw [factor_5_28]; decide
      have factor_5_30 : (43 : ZMod 103515091681) ^ 1990674840 = 23620786968 := by
        calc
          (43 : ZMod 103515091681) ^ 1990674840 = (43 : ZMod 103515091681) ^ (995337420 + 995337420) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 995337420 * (43 : ZMod 103515091681) ^ 995337420 := by rw [pow_add]
          _ = 23620786968 := by rw [factor_5_29]; decide
      have factor_5_31 : (43 : ZMod 103515091681) ^ 3981349680 = 7565818117 := by
        calc
          (43 : ZMod 103515091681) ^ 3981349680 = (43 : ZMod 103515091681) ^ (1990674840 + 1990674840) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1990674840 * (43 : ZMod 103515091681) ^ 1990674840 := by rw [pow_add]
          _ = 7565818117 := by rw [factor_5_30]; decide
      have factor_5_32 : (43 : ZMod 103515091681) ^ 7962699360 = 9788052787 := by
        calc
          (43 : ZMod 103515091681) ^ 7962699360 = (43 : ZMod 103515091681) ^ (3981349680 + 3981349680) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 3981349680 * (43 : ZMod 103515091681) ^ 3981349680 := by rw [pow_add]
          _ = 9788052787 := by rw [factor_5_31]; decide
      change (43 : ZMod 103515091681) ^ 7962699360 ≠ 1
      rw [factor_5_32]
      decide
    ·
      have factor_6_0 : (43 : ZMod 103515091681) ^ 1 = 43 := by norm_num
      have factor_6_1 : (43 : ZMod 103515091681) ^ 2 = 1849 := by
        calc
          (43 : ZMod 103515091681) ^ 2 = (43 : ZMod 103515091681) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1 * (43 : ZMod 103515091681) ^ 1 := by rw [pow_add]
          _ = 1849 := by rw [factor_6_0]; decide
      have factor_6_2 : (43 : ZMod 103515091681) ^ 5 = 147008443 := by
        calc
          (43 : ZMod 103515091681) ^ 5 = (43 : ZMod 103515091681) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 2 * (43 : ZMod 103515091681) ^ 2) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 147008443 := by rw [factor_6_1]; decide
      have factor_6_3 : (43 : ZMod 103515091681) ^ 11 = 46806597013 := by
        calc
          (43 : ZMod 103515091681) ^ 11 = (43 : ZMod 103515091681) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 5 * (43 : ZMod 103515091681) ^ 5) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 46806597013 := by rw [factor_6_2]; decide
      have factor_6_4 : (43 : ZMod 103515091681) ^ 22 = 38488718228 := by
        calc
          (43 : ZMod 103515091681) ^ 22 = (43 : ZMod 103515091681) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 11 * (43 : ZMod 103515091681) ^ 11 := by rw [pow_add]
          _ = 38488718228 := by rw [factor_6_3]; decide
      have factor_6_5 : (43 : ZMod 103515091681) ^ 45 = 883905791 := by
        calc
          (43 : ZMod 103515091681) ^ 45 = (43 : ZMod 103515091681) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 22 * (43 : ZMod 103515091681) ^ 22) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 883905791 := by rw [factor_6_4]; decide
      have factor_6_6 : (43 : ZMod 103515091681) ^ 90 = 80057828572 := by
        calc
          (43 : ZMod 103515091681) ^ 90 = (43 : ZMod 103515091681) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 45 * (43 : ZMod 103515091681) ^ 45 := by rw [pow_add]
          _ = 80057828572 := by rw [factor_6_5]; decide
      have factor_6_7 : (43 : ZMod 103515091681) ^ 181 = 68531612354 := by
        calc
          (43 : ZMod 103515091681) ^ 181 = (43 : ZMod 103515091681) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 90 * (43 : ZMod 103515091681) ^ 90) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 68531612354 := by rw [factor_6_6]; decide
      have factor_6_8 : (43 : ZMod 103515091681) ^ 362 = 40594905872 := by
        calc
          (43 : ZMod 103515091681) ^ 362 = (43 : ZMod 103515091681) ^ (181 + 181) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 181 * (43 : ZMod 103515091681) ^ 181 := by rw [pow_add]
          _ = 40594905872 := by rw [factor_6_7]; decide
      have factor_6_9 : (43 : ZMod 103515091681) ^ 725 = 90894687955 := by
        calc
          (43 : ZMod 103515091681) ^ 725 = (43 : ZMod 103515091681) ^ (362 + 362 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 362 * (43 : ZMod 103515091681) ^ 362) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 90894687955 := by rw [factor_6_8]; decide
      have factor_6_10 : (43 : ZMod 103515091681) ^ 1451 = 78554506220 := by
        calc
          (43 : ZMod 103515091681) ^ 1451 = (43 : ZMod 103515091681) ^ (725 + 725 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 725 * (43 : ZMod 103515091681) ^ 725) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 78554506220 := by rw [factor_6_9]; decide
      have factor_6_11 : (43 : ZMod 103515091681) ^ 2903 = 30140925047 := by
        calc
          (43 : ZMod 103515091681) ^ 2903 = (43 : ZMod 103515091681) ^ (1451 + 1451 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 1451 * (43 : ZMod 103515091681) ^ 1451) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 30140925047 := by rw [factor_6_10]; decide
      have factor_6_12 : (43 : ZMod 103515091681) ^ 5807 = 29238481814 := by
        calc
          (43 : ZMod 103515091681) ^ 5807 = (43 : ZMod 103515091681) ^ (2903 + 2903 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 2903 * (43 : ZMod 103515091681) ^ 2903) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 29238481814 := by rw [factor_6_11]; decide
      have factor_6_13 : (43 : ZMod 103515091681) ^ 11614 = 85159699299 := by
        calc
          (43 : ZMod 103515091681) ^ 11614 = (43 : ZMod 103515091681) ^ (5807 + 5807) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 5807 * (43 : ZMod 103515091681) ^ 5807 := by rw [pow_add]
          _ = 85159699299 := by rw [factor_6_12]; decide
      have factor_6_14 : (43 : ZMod 103515091681) ^ 23228 = 65944676907 := by
        calc
          (43 : ZMod 103515091681) ^ 23228 = (43 : ZMod 103515091681) ^ (11614 + 11614) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 11614 * (43 : ZMod 103515091681) ^ 11614 := by rw [pow_add]
          _ = 65944676907 := by rw [factor_6_13]; decide
      have factor_6_15 : (43 : ZMod 103515091681) ^ 46456 = 23359220647 := by
        calc
          (43 : ZMod 103515091681) ^ 46456 = (43 : ZMod 103515091681) ^ (23228 + 23228) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 23228 * (43 : ZMod 103515091681) ^ 23228 := by rw [pow_add]
          _ = 23359220647 := by rw [factor_6_14]; decide
      have factor_6_16 : (43 : ZMod 103515091681) ^ 92912 = 67333350777 := by
        calc
          (43 : ZMod 103515091681) ^ 92912 = (43 : ZMod 103515091681) ^ (46456 + 46456) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 46456 * (43 : ZMod 103515091681) ^ 46456 := by rw [pow_add]
          _ = 67333350777 := by rw [factor_6_15]; decide
      have factor_6_17 : (43 : ZMod 103515091681) ^ 185825 = 73732513247 := by
        calc
          (43 : ZMod 103515091681) ^ 185825 = (43 : ZMod 103515091681) ^ (92912 + 92912 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 92912 * (43 : ZMod 103515091681) ^ 92912) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 73732513247 := by rw [factor_6_16]; decide
      have factor_6_18 : (43 : ZMod 103515091681) ^ 371650 = 951218062 := by
        calc
          (43 : ZMod 103515091681) ^ 371650 = (43 : ZMod 103515091681) ^ (185825 + 185825) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 185825 * (43 : ZMod 103515091681) ^ 185825 := by rw [pow_add]
          _ = 951218062 := by rw [factor_6_17]; decide
      have factor_6_19 : (43 : ZMod 103515091681) ^ 743301 = 101722103887 := by
        calc
          (43 : ZMod 103515091681) ^ 743301 = (43 : ZMod 103515091681) ^ (371650 + 371650 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 371650 * (43 : ZMod 103515091681) ^ 371650) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 101722103887 := by rw [factor_6_18]; decide
      have factor_6_20 : (43 : ZMod 103515091681) ^ 1486602 = 67787003165 := by
        calc
          (43 : ZMod 103515091681) ^ 1486602 = (43 : ZMod 103515091681) ^ (743301 + 743301) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 743301 * (43 : ZMod 103515091681) ^ 743301 := by rw [pow_add]
          _ = 67787003165 := by rw [factor_6_19]; decide
      have factor_6_21 : (43 : ZMod 103515091681) ^ 2973204 = 40308638362 := by
        calc
          (43 : ZMod 103515091681) ^ 2973204 = (43 : ZMod 103515091681) ^ (1486602 + 1486602) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1486602 * (43 : ZMod 103515091681) ^ 1486602 := by rw [pow_add]
          _ = 40308638362 := by rw [factor_6_20]; decide
      have factor_6_22 : (43 : ZMod 103515091681) ^ 5946409 = 7808616792 := by
        calc
          (43 : ZMod 103515091681) ^ 5946409 = (43 : ZMod 103515091681) ^ (2973204 + 2973204 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 2973204 * (43 : ZMod 103515091681) ^ 2973204) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 7808616792 := by rw [factor_6_21]; decide
      have factor_6_23 : (43 : ZMod 103515091681) ^ 11892818 = 35902744227 := by
        calc
          (43 : ZMod 103515091681) ^ 11892818 = (43 : ZMod 103515091681) ^ (5946409 + 5946409) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 5946409 * (43 : ZMod 103515091681) ^ 5946409 := by rw [pow_add]
          _ = 35902744227 := by rw [factor_6_22]; decide
      have factor_6_24 : (43 : ZMod 103515091681) ^ 23785636 = 77572287481 := by
        calc
          (43 : ZMod 103515091681) ^ 23785636 = (43 : ZMod 103515091681) ^ (11892818 + 11892818) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 11892818 * (43 : ZMod 103515091681) ^ 11892818 := by rw [pow_add]
          _ = 77572287481 := by rw [factor_6_23]; decide
      have factor_6_25 : (43 : ZMod 103515091681) ^ 47571273 = 62494524898 := by
        calc
          (43 : ZMod 103515091681) ^ 47571273 = (43 : ZMod 103515091681) ^ (23785636 + 23785636 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 23785636 * (43 : ZMod 103515091681) ^ 23785636) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 62494524898 := by rw [factor_6_24]; decide
      have factor_6_26 : (43 : ZMod 103515091681) ^ 95142547 = 84508831366 := by
        calc
          (43 : ZMod 103515091681) ^ 95142547 = (43 : ZMod 103515091681) ^ (47571273 + 47571273 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 47571273 * (43 : ZMod 103515091681) ^ 47571273) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 84508831366 := by rw [factor_6_25]; decide
      have factor_6_27 : (43 : ZMod 103515091681) ^ 190285095 = 95074499487 := by
        calc
          (43 : ZMod 103515091681) ^ 190285095 = (43 : ZMod 103515091681) ^ (95142547 + 95142547 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 95142547 * (43 : ZMod 103515091681) ^ 95142547) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 95074499487 := by rw [factor_6_26]; decide
      have factor_6_28 : (43 : ZMod 103515091681) ^ 380570190 = 27459717423 := by
        calc
          (43 : ZMod 103515091681) ^ 380570190 = (43 : ZMod 103515091681) ^ (190285095 + 190285095) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 190285095 * (43 : ZMod 103515091681) ^ 190285095 := by rw [pow_add]
          _ = 27459717423 := by rw [factor_6_27]; decide
      have factor_6_29 : (43 : ZMod 103515091681) ^ 761140380 = 13433450476 := by
        calc
          (43 : ZMod 103515091681) ^ 761140380 = (43 : ZMod 103515091681) ^ (380570190 + 380570190) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 380570190 * (43 : ZMod 103515091681) ^ 380570190 := by rw [pow_add]
          _ = 13433450476 := by rw [factor_6_28]; decide
      have factor_6_30 : (43 : ZMod 103515091681) ^ 1522280760 = 53684413642 := by
        calc
          (43 : ZMod 103515091681) ^ 1522280760 = (43 : ZMod 103515091681) ^ (761140380 + 761140380) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 761140380 * (43 : ZMod 103515091681) ^ 761140380 := by rw [pow_add]
          _ = 53684413642 := by rw [factor_6_29]; decide
      have factor_6_31 : (43 : ZMod 103515091681) ^ 3044561520 = 21887554100 := by
        calc
          (43 : ZMod 103515091681) ^ 3044561520 = (43 : ZMod 103515091681) ^ (1522280760 + 1522280760) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1522280760 * (43 : ZMod 103515091681) ^ 1522280760 := by rw [pow_add]
          _ = 21887554100 := by rw [factor_6_30]; decide
      have factor_6_32 : (43 : ZMod 103515091681) ^ 6089123040 = 35371292121 := by
        calc
          (43 : ZMod 103515091681) ^ 6089123040 = (43 : ZMod 103515091681) ^ (3044561520 + 3044561520) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 3044561520 * (43 : ZMod 103515091681) ^ 3044561520 := by rw [pow_add]
          _ = 35371292121 := by rw [factor_6_31]; decide
      change (43 : ZMod 103515091681) ^ 6089123040 ≠ 1
      rw [factor_6_32]
      decide
    ·
      have factor_7_0 : (43 : ZMod 103515091681) ^ 1 = 43 := by norm_num
      have factor_7_1 : (43 : ZMod 103515091681) ^ 2 = 1849 := by
        calc
          (43 : ZMod 103515091681) ^ 2 = (43 : ZMod 103515091681) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1 * (43 : ZMod 103515091681) ^ 1 := by rw [pow_add]
          _ = 1849 := by rw [factor_7_0]; decide
      have factor_7_2 : (43 : ZMod 103515091681) ^ 5 = 147008443 := by
        calc
          (43 : ZMod 103515091681) ^ 5 = (43 : ZMod 103515091681) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 2 * (43 : ZMod 103515091681) ^ 2) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 147008443 := by rw [factor_7_1]; decide
      have factor_7_3 : (43 : ZMod 103515091681) ^ 10 = 15532491793 := by
        calc
          (43 : ZMod 103515091681) ^ 10 = (43 : ZMod 103515091681) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 5 * (43 : ZMod 103515091681) ^ 5 := by rw [pow_add]
          _ = 15532491793 := by rw [factor_7_2]; decide
      have factor_7_4 : (43 : ZMod 103515091681) ^ 20 = 12449345090 := by
        calc
          (43 : ZMod 103515091681) ^ 20 = (43 : ZMod 103515091681) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 10 * (43 : ZMod 103515091681) ^ 10 := by rw [pow_add]
          _ = 12449345090 := by rw [factor_7_3]; decide
      have factor_7_5 : (43 : ZMod 103515091681) ^ 40 = 22229479275 := by
        calc
          (43 : ZMod 103515091681) ^ 40 = (43 : ZMod 103515091681) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 20 * (43 : ZMod 103515091681) ^ 20 := by rw [pow_add]
          _ = 22229479275 := by rw [factor_7_4]; decide
      have factor_7_6 : (43 : ZMod 103515091681) ^ 81 = 92957298246 := by
        calc
          (43 : ZMod 103515091681) ^ 81 = (43 : ZMod 103515091681) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 40 * (43 : ZMod 103515091681) ^ 40) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 92957298246 := by rw [factor_7_5]; decide
      have factor_7_7 : (43 : ZMod 103515091681) ^ 162 = 27519929013 := by
        calc
          (43 : ZMod 103515091681) ^ 162 = (43 : ZMod 103515091681) ^ (81 + 81) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 81 * (43 : ZMod 103515091681) ^ 81 := by rw [pow_add]
          _ = 27519929013 := by rw [factor_7_6]; decide
      have factor_7_8 : (43 : ZMod 103515091681) ^ 324 = 35630105483 := by
        calc
          (43 : ZMod 103515091681) ^ 324 = (43 : ZMod 103515091681) ^ (162 + 162) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 162 * (43 : ZMod 103515091681) ^ 162 := by rw [pow_add]
          _ = 35630105483 := by rw [factor_7_7]; decide
      have factor_7_9 : (43 : ZMod 103515091681) ^ 649 = 45932837800 := by
        calc
          (43 : ZMod 103515091681) ^ 649 = (43 : ZMod 103515091681) ^ (324 + 324 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 324 * (43 : ZMod 103515091681) ^ 324) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 45932837800 := by rw [factor_7_8]; decide
      have factor_7_10 : (43 : ZMod 103515091681) ^ 1298 = 58523872288 := by
        calc
          (43 : ZMod 103515091681) ^ 1298 = (43 : ZMod 103515091681) ^ (649 + 649) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 649 * (43 : ZMod 103515091681) ^ 649 := by rw [pow_add]
          _ = 58523872288 := by rw [factor_7_9]; decide
      have factor_7_11 : (43 : ZMod 103515091681) ^ 2597 = 83721523052 := by
        calc
          (43 : ZMod 103515091681) ^ 2597 = (43 : ZMod 103515091681) ^ (1298 + 1298 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 1298 * (43 : ZMod 103515091681) ^ 1298) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 83721523052 := by rw [factor_7_10]; decide
      have factor_7_12 : (43 : ZMod 103515091681) ^ 5195 = 51998971958 := by
        calc
          (43 : ZMod 103515091681) ^ 5195 = (43 : ZMod 103515091681) ^ (2597 + 2597 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 2597 * (43 : ZMod 103515091681) ^ 2597) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 51998971958 := by rw [factor_7_11]; decide
      have factor_7_13 : (43 : ZMod 103515091681) ^ 10391 = 31973339163 := by
        calc
          (43 : ZMod 103515091681) ^ 10391 = (43 : ZMod 103515091681) ^ (5195 + 5195 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 5195 * (43 : ZMod 103515091681) ^ 5195) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 31973339163 := by rw [factor_7_12]; decide
      have factor_7_14 : (43 : ZMod 103515091681) ^ 20783 = 55944857392 := by
        calc
          (43 : ZMod 103515091681) ^ 20783 = (43 : ZMod 103515091681) ^ (10391 + 10391 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 10391 * (43 : ZMod 103515091681) ^ 10391) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 55944857392 := by rw [factor_7_13]; decide
      have factor_7_15 : (43 : ZMod 103515091681) ^ 41566 = 64568991020 := by
        calc
          (43 : ZMod 103515091681) ^ 41566 = (43 : ZMod 103515091681) ^ (20783 + 20783) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 20783 * (43 : ZMod 103515091681) ^ 20783 := by rw [pow_add]
          _ = 64568991020 := by rw [factor_7_14]; decide
      have factor_7_16 : (43 : ZMod 103515091681) ^ 83132 = 37647319942 := by
        calc
          (43 : ZMod 103515091681) ^ 83132 = (43 : ZMod 103515091681) ^ (41566 + 41566) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 41566 * (43 : ZMod 103515091681) ^ 41566 := by rw [pow_add]
          _ = 37647319942 := by rw [factor_7_15]; decide
      have factor_7_17 : (43 : ZMod 103515091681) ^ 166264 = 21138065634 := by
        calc
          (43 : ZMod 103515091681) ^ 166264 = (43 : ZMod 103515091681) ^ (83132 + 83132) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 83132 * (43 : ZMod 103515091681) ^ 83132 := by rw [pow_add]
          _ = 21138065634 := by rw [factor_7_16]; decide
      have factor_7_18 : (43 : ZMod 103515091681) ^ 332529 = 60791616205 := by
        calc
          (43 : ZMod 103515091681) ^ 332529 = (43 : ZMod 103515091681) ^ (166264 + 166264 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 166264 * (43 : ZMod 103515091681) ^ 166264) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 60791616205 := by rw [factor_7_17]; decide
      have factor_7_19 : (43 : ZMod 103515091681) ^ 665058 = 92881748353 := by
        calc
          (43 : ZMod 103515091681) ^ 665058 = (43 : ZMod 103515091681) ^ (332529 + 332529) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 332529 * (43 : ZMod 103515091681) ^ 332529 := by rw [pow_add]
          _ = 92881748353 := by rw [factor_7_18]; decide
      have factor_7_20 : (43 : ZMod 103515091681) ^ 1330117 = 31418890017 := by
        calc
          (43 : ZMod 103515091681) ^ 1330117 = (43 : ZMod 103515091681) ^ (665058 + 665058 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 665058 * (43 : ZMod 103515091681) ^ 665058) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 31418890017 := by rw [factor_7_19]; decide
      have factor_7_21 : (43 : ZMod 103515091681) ^ 2660235 = 17270782330 := by
        calc
          (43 : ZMod 103515091681) ^ 2660235 = (43 : ZMod 103515091681) ^ (1330117 + 1330117 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 1330117 * (43 : ZMod 103515091681) ^ 1330117) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 17270782330 := by rw [factor_7_20]; decide
      have factor_7_22 : (43 : ZMod 103515091681) ^ 5320471 = 5697358519 := by
        calc
          (43 : ZMod 103515091681) ^ 5320471 = (43 : ZMod 103515091681) ^ (2660235 + 2660235 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 2660235 * (43 : ZMod 103515091681) ^ 2660235) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 5697358519 := by rw [factor_7_21]; decide
      have factor_7_23 : (43 : ZMod 103515091681) ^ 10640942 = 54905186040 := by
        calc
          (43 : ZMod 103515091681) ^ 10640942 = (43 : ZMod 103515091681) ^ (5320471 + 5320471) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 5320471 * (43 : ZMod 103515091681) ^ 5320471 := by rw [pow_add]
          _ = 54905186040 := by rw [factor_7_22]; decide
      have factor_7_24 : (43 : ZMod 103515091681) ^ 21281885 = 100099254227 := by
        calc
          (43 : ZMod 103515091681) ^ 21281885 = (43 : ZMod 103515091681) ^ (10640942 + 10640942 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 10640942 * (43 : ZMod 103515091681) ^ 10640942) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 100099254227 := by rw [factor_7_23]; decide
      have factor_7_25 : (43 : ZMod 103515091681) ^ 42563771 = 1667763721 := by
        calc
          (43 : ZMod 103515091681) ^ 42563771 = (43 : ZMod 103515091681) ^ (21281885 + 21281885 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 21281885 * (43 : ZMod 103515091681) ^ 21281885) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 1667763721 := by rw [factor_7_24]; decide
      have factor_7_26 : (43 : ZMod 103515091681) ^ 85127542 = 14758314543 := by
        calc
          (43 : ZMod 103515091681) ^ 85127542 = (43 : ZMod 103515091681) ^ (42563771 + 42563771) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 42563771 * (43 : ZMod 103515091681) ^ 42563771 := by rw [pow_add]
          _ = 14758314543 := by rw [factor_7_25]; decide
      have factor_7_27 : (43 : ZMod 103515091681) ^ 170255085 = 48098601519 := by
        calc
          (43 : ZMod 103515091681) ^ 170255085 = (43 : ZMod 103515091681) ^ (85127542 + 85127542 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 85127542 * (43 : ZMod 103515091681) ^ 85127542) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 48098601519 := by rw [factor_7_26]; decide
      have factor_7_28 : (43 : ZMod 103515091681) ^ 340510170 = 59978422186 := by
        calc
          (43 : ZMod 103515091681) ^ 340510170 = (43 : ZMod 103515091681) ^ (170255085 + 170255085) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 170255085 * (43 : ZMod 103515091681) ^ 170255085 := by rw [pow_add]
          _ = 59978422186 := by rw [factor_7_27]; decide
      have factor_7_29 : (43 : ZMod 103515091681) ^ 681020340 = 58692316460 := by
        calc
          (43 : ZMod 103515091681) ^ 681020340 = (43 : ZMod 103515091681) ^ (340510170 + 340510170) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 340510170 * (43 : ZMod 103515091681) ^ 340510170 := by rw [pow_add]
          _ = 58692316460 := by rw [factor_7_28]; decide
      have factor_7_30 : (43 : ZMod 103515091681) ^ 1362040680 = 52225735559 := by
        calc
          (43 : ZMod 103515091681) ^ 1362040680 = (43 : ZMod 103515091681) ^ (681020340 + 681020340) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 681020340 * (43 : ZMod 103515091681) ^ 681020340 := by rw [pow_add]
          _ = 52225735559 := by rw [factor_7_29]; decide
      have factor_7_31 : (43 : ZMod 103515091681) ^ 2724081360 = 98788484342 := by
        calc
          (43 : ZMod 103515091681) ^ 2724081360 = (43 : ZMod 103515091681) ^ (1362040680 + 1362040680) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1362040680 * (43 : ZMod 103515091681) ^ 1362040680 := by rw [pow_add]
          _ = 98788484342 := by rw [factor_7_30]; decide
      have factor_7_32 : (43 : ZMod 103515091681) ^ 5448162720 = 3817097967 := by
        calc
          (43 : ZMod 103515091681) ^ 5448162720 = (43 : ZMod 103515091681) ^ (2724081360 + 2724081360) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 2724081360 * (43 : ZMod 103515091681) ^ 2724081360 := by rw [pow_add]
          _ = 3817097967 := by rw [factor_7_31]; decide
      change (43 : ZMod 103515091681) ^ 5448162720 ≠ 1
      rw [factor_7_32]
      decide
    ·
      have factor_8_0 : (43 : ZMod 103515091681) ^ 1 = 43 := by norm_num
      have factor_8_1 : (43 : ZMod 103515091681) ^ 2 = 1849 := by
        calc
          (43 : ZMod 103515091681) ^ 2 = (43 : ZMod 103515091681) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1 * (43 : ZMod 103515091681) ^ 1 := by rw [pow_add]
          _ = 1849 := by rw [factor_8_0]; decide
      have factor_8_2 : (43 : ZMod 103515091681) ^ 4 = 3418801 := by
        calc
          (43 : ZMod 103515091681) ^ 4 = (43 : ZMod 103515091681) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 2 * (43 : ZMod 103515091681) ^ 2 := by rw [pow_add]
          _ = 3418801 := by rw [factor_8_1]; decide
      have factor_8_3 : (43 : ZMod 103515091681) ^ 8 = 94510009329 := by
        calc
          (43 : ZMod 103515091681) ^ 8 = (43 : ZMod 103515091681) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 4 * (43 : ZMod 103515091681) ^ 4 := by rw [pow_add]
          _ = 94510009329 := by rw [factor_8_2]; decide
      have factor_8_4 : (43 : ZMod 103515091681) ^ 16 = 48792966899 := by
        calc
          (43 : ZMod 103515091681) ^ 16 = (43 : ZMod 103515091681) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 8 * (43 : ZMod 103515091681) ^ 8 := by rw [pow_add]
          _ = 48792966899 := by rw [factor_8_3]; decide
      have factor_8_5 : (43 : ZMod 103515091681) ^ 33 = 50606669297 := by
        calc
          (43 : ZMod 103515091681) ^ 33 = (43 : ZMod 103515091681) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 16 * (43 : ZMod 103515091681) ^ 16) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 50606669297 := by rw [factor_8_4]; decide
      have factor_8_6 : (43 : ZMod 103515091681) ^ 67 = 10728752024 := by
        calc
          (43 : ZMod 103515091681) ^ 67 = (43 : ZMod 103515091681) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 33 * (43 : ZMod 103515091681) ^ 33) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 10728752024 := by rw [factor_8_5]; decide
      have factor_8_7 : (43 : ZMod 103515091681) ^ 134 = 37309765172 := by
        calc
          (43 : ZMod 103515091681) ^ 134 = (43 : ZMod 103515091681) ^ (67 + 67) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 67 * (43 : ZMod 103515091681) ^ 67 := by rw [pow_add]
          _ = 37309765172 := by rw [factor_8_6]; decide
      have factor_8_8 : (43 : ZMod 103515091681) ^ 268 = 1664208516 := by
        calc
          (43 : ZMod 103515091681) ^ 268 = (43 : ZMod 103515091681) ^ (134 + 134) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 134 * (43 : ZMod 103515091681) ^ 134 := by rw [pow_add]
          _ = 1664208516 := by rw [factor_8_7]; decide
      have factor_8_9 : (43 : ZMod 103515091681) ^ 536 = 23433077874 := by
        calc
          (43 : ZMod 103515091681) ^ 536 = (43 : ZMod 103515091681) ^ (268 + 268) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 268 * (43 : ZMod 103515091681) ^ 268 := by rw [pow_add]
          _ = 23433077874 := by rw [factor_8_8]; decide
      have factor_8_10 : (43 : ZMod 103515091681) ^ 1073 = 40285620203 := by
        calc
          (43 : ZMod 103515091681) ^ 1073 = (43 : ZMod 103515091681) ^ (536 + 536 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 536 * (43 : ZMod 103515091681) ^ 536) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 40285620203 := by rw [factor_8_9]; decide
      have factor_8_11 : (43 : ZMod 103515091681) ^ 2146 = 3818963702 := by
        calc
          (43 : ZMod 103515091681) ^ 2146 = (43 : ZMod 103515091681) ^ (1073 + 1073) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1073 * (43 : ZMod 103515091681) ^ 1073 := by rw [pow_add]
          _ = 3818963702 := by rw [factor_8_10]; decide
      have factor_8_12 : (43 : ZMod 103515091681) ^ 4292 = 57912737902 := by
        calc
          (43 : ZMod 103515091681) ^ 4292 = (43 : ZMod 103515091681) ^ (2146 + 2146) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 2146 * (43 : ZMod 103515091681) ^ 2146 := by rw [pow_add]
          _ = 57912737902 := by rw [factor_8_11]; decide
      have factor_8_13 : (43 : ZMod 103515091681) ^ 8584 = 95416848800 := by
        calc
          (43 : ZMod 103515091681) ^ 8584 = (43 : ZMod 103515091681) ^ (4292 + 4292) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 4292 * (43 : ZMod 103515091681) ^ 4292 := by rw [pow_add]
          _ = 95416848800 := by rw [factor_8_12]; decide
      have factor_8_14 : (43 : ZMod 103515091681) ^ 17168 = 59576975615 := by
        calc
          (43 : ZMod 103515091681) ^ 17168 = (43 : ZMod 103515091681) ^ (8584 + 8584) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 8584 * (43 : ZMod 103515091681) ^ 8584 := by rw [pow_add]
          _ = 59576975615 := by rw [factor_8_13]; decide
      have factor_8_15 : (43 : ZMod 103515091681) ^ 34337 = 101370466293 := by
        calc
          (43 : ZMod 103515091681) ^ 34337 = (43 : ZMod 103515091681) ^ (17168 + 17168 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 17168 * (43 : ZMod 103515091681) ^ 17168) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 101370466293 := by rw [factor_8_14]; decide
      have factor_8_16 : (43 : ZMod 103515091681) ^ 68674 = 99122603642 := by
        calc
          (43 : ZMod 103515091681) ^ 68674 = (43 : ZMod 103515091681) ^ (34337 + 34337) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 34337 * (43 : ZMod 103515091681) ^ 34337 := by rw [pow_add]
          _ = 99122603642 := by rw [factor_8_15]; decide
      have factor_8_17 : (43 : ZMod 103515091681) ^ 137349 = 94589705922 := by
        calc
          (43 : ZMod 103515091681) ^ 137349 = (43 : ZMod 103515091681) ^ (68674 + 68674 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 68674 * (43 : ZMod 103515091681) ^ 68674) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 94589705922 := by rw [factor_8_16]; decide
      have factor_8_18 : (43 : ZMod 103515091681) ^ 274698 = 99942022120 := by
        calc
          (43 : ZMod 103515091681) ^ 274698 = (43 : ZMod 103515091681) ^ (137349 + 137349) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 137349 * (43 : ZMod 103515091681) ^ 137349 := by rw [pow_add]
          _ = 99942022120 := by rw [factor_8_17]; decide
      have factor_8_19 : (43 : ZMod 103515091681) ^ 549396 = 10057601488 := by
        calc
          (43 : ZMod 103515091681) ^ 549396 = (43 : ZMod 103515091681) ^ (274698 + 274698) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 274698 * (43 : ZMod 103515091681) ^ 274698 := by rw [pow_add]
          _ = 10057601488 := by rw [factor_8_18]; decide
      have factor_8_20 : (43 : ZMod 103515091681) ^ 1098793 = 20351934311 := by
        calc
          (43 : ZMod 103515091681) ^ 1098793 = (43 : ZMod 103515091681) ^ (549396 + 549396 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 549396 * (43 : ZMod 103515091681) ^ 549396) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 20351934311 := by rw [factor_8_19]; decide
      have factor_8_21 : (43 : ZMod 103515091681) ^ 2197586 = 34984448240 := by
        calc
          (43 : ZMod 103515091681) ^ 2197586 = (43 : ZMod 103515091681) ^ (1098793 + 1098793) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1098793 * (43 : ZMod 103515091681) ^ 1098793 := by rw [pow_add]
          _ = 34984448240 := by rw [factor_8_20]; decide
      have factor_8_22 : (43 : ZMod 103515091681) ^ 4395172 = 13535010195 := by
        calc
          (43 : ZMod 103515091681) ^ 4395172 = (43 : ZMod 103515091681) ^ (2197586 + 2197586) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 2197586 * (43 : ZMod 103515091681) ^ 2197586 := by rw [pow_add]
          _ = 13535010195 := by rw [factor_8_21]; decide
      have factor_8_23 : (43 : ZMod 103515091681) ^ 8790344 = 10993028937 := by
        calc
          (43 : ZMod 103515091681) ^ 8790344 = (43 : ZMod 103515091681) ^ (4395172 + 4395172) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 4395172 * (43 : ZMod 103515091681) ^ 4395172 := by rw [pow_add]
          _ = 10993028937 := by rw [factor_8_22]; decide
      have factor_8_24 : (43 : ZMod 103515091681) ^ 17580688 = 33574878093 := by
        calc
          (43 : ZMod 103515091681) ^ 17580688 = (43 : ZMod 103515091681) ^ (8790344 + 8790344) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 8790344 * (43 : ZMod 103515091681) ^ 8790344 := by rw [pow_add]
          _ = 33574878093 := by rw [factor_8_23]; decide
      have factor_8_25 : (43 : ZMod 103515091681) ^ 35161376 = 82575931718 := by
        calc
          (43 : ZMod 103515091681) ^ 35161376 = (43 : ZMod 103515091681) ^ (17580688 + 17580688) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 17580688 * (43 : ZMod 103515091681) ^ 17580688 := by rw [pow_add]
          _ = 82575931718 := by rw [factor_8_24]; decide
      have factor_8_26 : (43 : ZMod 103515091681) ^ 70322752 = 8484233878 := by
        calc
          (43 : ZMod 103515091681) ^ 70322752 = (43 : ZMod 103515091681) ^ (35161376 + 35161376) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 35161376 * (43 : ZMod 103515091681) ^ 35161376 := by rw [pow_add]
          _ = 8484233878 := by rw [factor_8_25]; decide
      have factor_8_27 : (43 : ZMod 103515091681) ^ 140645505 = 22809750494 := by
        calc
          (43 : ZMod 103515091681) ^ 140645505 = (43 : ZMod 103515091681) ^ (70322752 + 70322752 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 70322752 * (43 : ZMod 103515091681) ^ 70322752) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 22809750494 := by rw [factor_8_26]; decide
      have factor_8_28 : (43 : ZMod 103515091681) ^ 281291010 = 1488011755 := by
        calc
          (43 : ZMod 103515091681) ^ 281291010 = (43 : ZMod 103515091681) ^ (140645505 + 140645505) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 140645505 * (43 : ZMod 103515091681) ^ 140645505 := by rw [pow_add]
          _ = 1488011755 := by rw [factor_8_27]; decide
      have factor_8_29 : (43 : ZMod 103515091681) ^ 562582020 = 74259474591 := by
        calc
          (43 : ZMod 103515091681) ^ 562582020 = (43 : ZMod 103515091681) ^ (281291010 + 281291010) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 281291010 * (43 : ZMod 103515091681) ^ 281291010 := by rw [pow_add]
          _ = 74259474591 := by rw [factor_8_28]; decide
      have factor_8_30 : (43 : ZMod 103515091681) ^ 1125164040 = 100520275476 := by
        calc
          (43 : ZMod 103515091681) ^ 1125164040 = (43 : ZMod 103515091681) ^ (562582020 + 562582020) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 562582020 * (43 : ZMod 103515091681) ^ 562582020 := by rw [pow_add]
          _ = 100520275476 := by rw [factor_8_29]; decide
      have factor_8_31 : (43 : ZMod 103515091681) ^ 2250328080 = 74100318228 := by
        calc
          (43 : ZMod 103515091681) ^ 2250328080 = (43 : ZMod 103515091681) ^ (1125164040 + 1125164040) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1125164040 * (43 : ZMod 103515091681) ^ 1125164040 := by rw [pow_add]
          _ = 74100318228 := by rw [factor_8_30]; decide
      have factor_8_32 : (43 : ZMod 103515091681) ^ 4500656160 = 74763386337 := by
        calc
          (43 : ZMod 103515091681) ^ 4500656160 = (43 : ZMod 103515091681) ^ (2250328080 + 2250328080) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 2250328080 * (43 : ZMod 103515091681) ^ 2250328080 := by rw [pow_add]
          _ = 74763386337 := by rw [factor_8_31]; decide
      change (43 : ZMod 103515091681) ^ 4500656160 ≠ 1
      rw [factor_8_32]
      decide
    ·
      have factor_9_0 : (43 : ZMod 103515091681) ^ 1 = 43 := by norm_num
      have factor_9_1 : (43 : ZMod 103515091681) ^ 3 = 79507 := by
        calc
          (43 : ZMod 103515091681) ^ 3 = (43 : ZMod 103515091681) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 1 * (43 : ZMod 103515091681) ^ 1) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 79507 := by rw [factor_9_0]; decide
      have factor_9_2 : (43 : ZMod 103515091681) ^ 6 = 6321363049 := by
        calc
          (43 : ZMod 103515091681) ^ 6 = (43 : ZMod 103515091681) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 3 * (43 : ZMod 103515091681) ^ 3 := by rw [pow_add]
          _ = 6321363049 := by rw [factor_9_1]; decide
      have factor_9_3 : (43 : ZMod 103515091681) ^ 13 = 6781231721 := by
        calc
          (43 : ZMod 103515091681) ^ 13 = (43 : ZMod 103515091681) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 6 * (43 : ZMod 103515091681) ^ 6) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 6781231721 := by rw [factor_9_2]; decide
      have factor_9_4 : (43 : ZMod 103515091681) ^ 26 = 92789559539 := by
        calc
          (43 : ZMod 103515091681) ^ 26 = (43 : ZMod 103515091681) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 13 * (43 : ZMod 103515091681) ^ 13 := by rw [pow_add]
          _ = 92789559539 := by rw [factor_9_3]; decide
      have factor_9_5 : (43 : ZMod 103515091681) ^ 53 = 94804324014 := by
        calc
          (43 : ZMod 103515091681) ^ 53 = (43 : ZMod 103515091681) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 26 * (43 : ZMod 103515091681) ^ 26) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 94804324014 := by rw [factor_9_4]; decide
      have factor_9_6 : (43 : ZMod 103515091681) ^ 106 = 6442646727 := by
        calc
          (43 : ZMod 103515091681) ^ 106 = (43 : ZMod 103515091681) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 53 * (43 : ZMod 103515091681) ^ 53 := by rw [pow_add]
          _ = 6442646727 := by rw [factor_9_5]; decide
      have factor_9_7 : (43 : ZMod 103515091681) ^ 212 = 75285736049 := by
        calc
          (43 : ZMod 103515091681) ^ 212 = (43 : ZMod 103515091681) ^ (106 + 106) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 106 * (43 : ZMod 103515091681) ^ 106 := by rw [pow_add]
          _ = 75285736049 := by rw [factor_9_6]; decide
      have factor_9_8 : (43 : ZMod 103515091681) ^ 425 = 5970906266 := by
        calc
          (43 : ZMod 103515091681) ^ 425 = (43 : ZMod 103515091681) ^ (212 + 212 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 212 * (43 : ZMod 103515091681) ^ 212) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 5970906266 := by rw [factor_9_7]; decide
      have factor_9_9 : (43 : ZMod 103515091681) ^ 851 = 71827614135 := by
        calc
          (43 : ZMod 103515091681) ^ 851 = (43 : ZMod 103515091681) ^ (425 + 425 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 425 * (43 : ZMod 103515091681) ^ 425) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 71827614135 := by rw [factor_9_8]; decide
      have factor_9_10 : (43 : ZMod 103515091681) ^ 1702 = 23312437064 := by
        calc
          (43 : ZMod 103515091681) ^ 1702 = (43 : ZMod 103515091681) ^ (851 + 851) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 851 * (43 : ZMod 103515091681) ^ 851 := by rw [pow_add]
          _ = 23312437064 := by rw [factor_9_9]; decide
      have factor_9_11 : (43 : ZMod 103515091681) ^ 3404 = 21816336851 := by
        calc
          (43 : ZMod 103515091681) ^ 3404 = (43 : ZMod 103515091681) ^ (1702 + 1702) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1702 * (43 : ZMod 103515091681) ^ 1702 := by rw [pow_add]
          _ = 21816336851 := by rw [factor_9_10]; decide
      have factor_9_12 : (43 : ZMod 103515091681) ^ 6808 = 17860866760 := by
        calc
          (43 : ZMod 103515091681) ^ 6808 = (43 : ZMod 103515091681) ^ (3404 + 3404) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 3404 * (43 : ZMod 103515091681) ^ 3404 := by rw [pow_add]
          _ = 17860866760 := by rw [factor_9_11]; decide
      have factor_9_13 : (43 : ZMod 103515091681) ^ 13616 = 16728225558 := by
        calc
          (43 : ZMod 103515091681) ^ 13616 = (43 : ZMod 103515091681) ^ (6808 + 6808) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 6808 * (43 : ZMod 103515091681) ^ 6808 := by rw [pow_add]
          _ = 16728225558 := by rw [factor_9_12]; decide
      have factor_9_14 : (43 : ZMod 103515091681) ^ 27233 = 16658103485 := by
        calc
          (43 : ZMod 103515091681) ^ 27233 = (43 : ZMod 103515091681) ^ (13616 + 13616 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 13616 * (43 : ZMod 103515091681) ^ 13616) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 16658103485 := by rw [factor_9_13]; decide
      have factor_9_15 : (43 : ZMod 103515091681) ^ 54466 = 42820497043 := by
        calc
          (43 : ZMod 103515091681) ^ 54466 = (43 : ZMod 103515091681) ^ (27233 + 27233) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 27233 * (43 : ZMod 103515091681) ^ 27233 := by rw [pow_add]
          _ = 42820497043 := by rw [factor_9_14]; decide
      have factor_9_16 : (43 : ZMod 103515091681) ^ 108932 = 3085925765 := by
        calc
          (43 : ZMod 103515091681) ^ 108932 = (43 : ZMod 103515091681) ^ (54466 + 54466) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 54466 * (43 : ZMod 103515091681) ^ 54466 := by rw [pow_add]
          _ = 3085925765 := by rw [factor_9_15]; decide
      have factor_9_17 : (43 : ZMod 103515091681) ^ 217864 = 97148014299 := by
        calc
          (43 : ZMod 103515091681) ^ 217864 = (43 : ZMod 103515091681) ^ (108932 + 108932) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 108932 * (43 : ZMod 103515091681) ^ 108932 := by rw [pow_add]
          _ = 97148014299 := by rw [factor_9_16]; decide
      have factor_9_18 : (43 : ZMod 103515091681) ^ 435728 = 29743685754 := by
        calc
          (43 : ZMod 103515091681) ^ 435728 = (43 : ZMod 103515091681) ^ (217864 + 217864) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 217864 * (43 : ZMod 103515091681) ^ 217864 := by rw [pow_add]
          _ = 29743685754 := by rw [factor_9_17]; decide
      have factor_9_19 : (43 : ZMod 103515091681) ^ 871456 = 95301050465 := by
        calc
          (43 : ZMod 103515091681) ^ 871456 = (43 : ZMod 103515091681) ^ (435728 + 435728) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 435728 * (43 : ZMod 103515091681) ^ 435728 := by rw [pow_add]
          _ = 95301050465 := by rw [factor_9_18]; decide
      have factor_9_20 : (43 : ZMod 103515091681) ^ 1742913 = 94786207012 := by
        calc
          (43 : ZMod 103515091681) ^ 1742913 = (43 : ZMod 103515091681) ^ (871456 + 871456 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 871456 * (43 : ZMod 103515091681) ^ 871456) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 94786207012 := by rw [factor_9_19]; decide
      have factor_9_21 : (43 : ZMod 103515091681) ^ 3485826 = 77079747787 := by
        calc
          (43 : ZMod 103515091681) ^ 3485826 = (43 : ZMod 103515091681) ^ (1742913 + 1742913) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1742913 * (43 : ZMod 103515091681) ^ 1742913 := by rw [pow_add]
          _ = 77079747787 := by rw [factor_9_20]; decide
      have factor_9_22 : (43 : ZMod 103515091681) ^ 6971652 = 53163920477 := by
        calc
          (43 : ZMod 103515091681) ^ 6971652 = (43 : ZMod 103515091681) ^ (3485826 + 3485826) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 3485826 * (43 : ZMod 103515091681) ^ 3485826 := by rw [pow_add]
          _ = 53163920477 := by rw [factor_9_21]; decide
      have factor_9_23 : (43 : ZMod 103515091681) ^ 13943304 = 28669213514 := by
        calc
          (43 : ZMod 103515091681) ^ 13943304 = (43 : ZMod 103515091681) ^ (6971652 + 6971652) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 6971652 * (43 : ZMod 103515091681) ^ 6971652 := by rw [pow_add]
          _ = 28669213514 := by rw [factor_9_22]; decide
      have factor_9_24 : (43 : ZMod 103515091681) ^ 27886608 = 95167468067 := by
        calc
          (43 : ZMod 103515091681) ^ 27886608 = (43 : ZMod 103515091681) ^ (13943304 + 13943304) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 13943304 * (43 : ZMod 103515091681) ^ 13943304 := by rw [pow_add]
          _ = 95167468067 := by rw [factor_9_23]; decide
      have factor_9_25 : (43 : ZMod 103515091681) ^ 55773217 = 68249695142 := by
        calc
          (43 : ZMod 103515091681) ^ 55773217 = (43 : ZMod 103515091681) ^ (27886608 + 27886608 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 27886608 * (43 : ZMod 103515091681) ^ 27886608) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 68249695142 := by rw [factor_9_24]; decide
      have factor_9_26 : (43 : ZMod 103515091681) ^ 111546435 = 35509491937 := by
        calc
          (43 : ZMod 103515091681) ^ 111546435 = (43 : ZMod 103515091681) ^ (55773217 + 55773217 + 1) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = ((43 : ZMod 103515091681) ^ 55773217 * (43 : ZMod 103515091681) ^ 55773217) * (43 : ZMod 103515091681) := by rw [pow_succ, pow_add]
          _ = 35509491937 := by rw [factor_9_25]; decide
      have factor_9_27 : (43 : ZMod 103515091681) ^ 223092870 = 24865519541 := by
        calc
          (43 : ZMod 103515091681) ^ 223092870 = (43 : ZMod 103515091681) ^ (111546435 + 111546435) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 111546435 * (43 : ZMod 103515091681) ^ 111546435 := by rw [pow_add]
          _ = 24865519541 := by rw [factor_9_26]; decide
      have factor_9_28 : (43 : ZMod 103515091681) ^ 446185740 = 5174727870 := by
        calc
          (43 : ZMod 103515091681) ^ 446185740 = (43 : ZMod 103515091681) ^ (223092870 + 223092870) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 223092870 * (43 : ZMod 103515091681) ^ 223092870 := by rw [pow_add]
          _ = 5174727870 := by rw [factor_9_27]; decide
      have factor_9_29 : (43 : ZMod 103515091681) ^ 892371480 = 101544109273 := by
        calc
          (43 : ZMod 103515091681) ^ 892371480 = (43 : ZMod 103515091681) ^ (446185740 + 446185740) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 446185740 * (43 : ZMod 103515091681) ^ 446185740 := by rw [pow_add]
          _ = 101544109273 := by rw [factor_9_28]; decide
      have factor_9_30 : (43 : ZMod 103515091681) ^ 1784742960 = 48195210871 := by
        calc
          (43 : ZMod 103515091681) ^ 1784742960 = (43 : ZMod 103515091681) ^ (892371480 + 892371480) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 892371480 * (43 : ZMod 103515091681) ^ 892371480 := by rw [pow_add]
          _ = 48195210871 := by rw [factor_9_29]; decide
      have factor_9_31 : (43 : ZMod 103515091681) ^ 3569485920 = 12900742684 := by
        calc
          (43 : ZMod 103515091681) ^ 3569485920 = (43 : ZMod 103515091681) ^ (1784742960 + 1784742960) :=
            congrArg (fun n : ℕ => (43 : ZMod 103515091681) ^ n) (by norm_num)
          _ = (43 : ZMod 103515091681) ^ 1784742960 * (43 : ZMod 103515091681) ^ 1784742960 := by rw [pow_add]
          _ = 12900742684 := by rw [factor_9_30]; decide
      change (43 : ZMod 103515091681) ^ 3569485920 ≠ 1
      rw [factor_9_31]
      decide

#print axioms prime_lucas_103515091681

end TotientTailPeriodKiller
end Erdos249257
