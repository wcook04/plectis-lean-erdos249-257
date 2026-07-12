import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_75691781281 : Nat.Prime 75691781281 := by
  apply lucas_primality 75691781281 (11 : ZMod 75691781281)
  ·
      have fermat_0 : (11 : ZMod 75691781281) ^ 1 = 11 := by norm_num
      have fermat_1 : (11 : ZMod 75691781281) ^ 2 = 121 := by
        calc
          (11 : ZMod 75691781281) ^ 2 = (11 : ZMod 75691781281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 1 * (11 : ZMod 75691781281) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [fermat_0]; decide
      have fermat_2 : (11 : ZMod 75691781281) ^ 4 = 14641 := by
        calc
          (11 : ZMod 75691781281) ^ 4 = (11 : ZMod 75691781281) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 2 * (11 : ZMod 75691781281) ^ 2 := by rw [pow_add]
          _ = 14641 := by rw [fermat_1]; decide
      have fermat_3 : (11 : ZMod 75691781281) ^ 8 = 214358881 := by
        calc
          (11 : ZMod 75691781281) ^ 8 = (11 : ZMod 75691781281) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 4 * (11 : ZMod 75691781281) ^ 4 := by rw [pow_add]
          _ = 214358881 := by rw [fermat_2]; decide
      have fermat_4 : (11 : ZMod 75691781281) ^ 17 = 20639160071 := by
        calc
          (11 : ZMod 75691781281) ^ 17 = (11 : ZMod 75691781281) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 8 * (11 : ZMod 75691781281) ^ 8) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 20639160071 := by rw [fermat_3]; decide
      have fermat_5 : (11 : ZMod 75691781281) ^ 35 = 26000725628 := by
        calc
          (11 : ZMod 75691781281) ^ 35 = (11 : ZMod 75691781281) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 17 * (11 : ZMod 75691781281) ^ 17) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 26000725628 := by rw [fermat_4]; decide
      have fermat_6 : (11 : ZMod 75691781281) ^ 70 = 24175047773 := by
        calc
          (11 : ZMod 75691781281) ^ 70 = (11 : ZMod 75691781281) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 35 * (11 : ZMod 75691781281) ^ 35 := by rw [pow_add]
          _ = 24175047773 := by rw [fermat_5]; decide
      have fermat_7 : (11 : ZMod 75691781281) ^ 140 = 4623173409 := by
        calc
          (11 : ZMod 75691781281) ^ 140 = (11 : ZMod 75691781281) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 70 * (11 : ZMod 75691781281) ^ 70 := by rw [pow_add]
          _ = 4623173409 := by rw [fermat_6]; decide
      have fermat_8 : (11 : ZMod 75691781281) ^ 281 = 5252578648 := by
        calc
          (11 : ZMod 75691781281) ^ 281 = (11 : ZMod 75691781281) ^ (140 + 140 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 140 * (11 : ZMod 75691781281) ^ 140) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 5252578648 := by rw [fermat_7]; decide
      have fermat_9 : (11 : ZMod 75691781281) ^ 563 = 12324098022 := by
        calc
          (11 : ZMod 75691781281) ^ 563 = (11 : ZMod 75691781281) ^ (281 + 281 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 281 * (11 : ZMod 75691781281) ^ 281) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 12324098022 := by rw [fermat_8]; decide
      have fermat_10 : (11 : ZMod 75691781281) ^ 1127 = 72605680437 := by
        calc
          (11 : ZMod 75691781281) ^ 1127 = (11 : ZMod 75691781281) ^ (563 + 563 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 563 * (11 : ZMod 75691781281) ^ 563) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 72605680437 := by rw [fermat_9]; decide
      have fermat_11 : (11 : ZMod 75691781281) ^ 2255 = 29096297518 := by
        calc
          (11 : ZMod 75691781281) ^ 2255 = (11 : ZMod 75691781281) ^ (1127 + 1127 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 1127 * (11 : ZMod 75691781281) ^ 1127) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 29096297518 := by rw [fermat_10]; decide
      have fermat_12 : (11 : ZMod 75691781281) ^ 4511 = 55448136765 := by
        calc
          (11 : ZMod 75691781281) ^ 4511 = (11 : ZMod 75691781281) ^ (2255 + 2255 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 2255 * (11 : ZMod 75691781281) ^ 2255) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 55448136765 := by rw [fermat_11]; decide
      have fermat_13 : (11 : ZMod 75691781281) ^ 9023 = 61539820329 := by
        calc
          (11 : ZMod 75691781281) ^ 9023 = (11 : ZMod 75691781281) ^ (4511 + 4511 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 4511 * (11 : ZMod 75691781281) ^ 4511) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 61539820329 := by rw [fermat_12]; decide
      have fermat_14 : (11 : ZMod 75691781281) ^ 18046 = 50490126572 := by
        calc
          (11 : ZMod 75691781281) ^ 18046 = (11 : ZMod 75691781281) ^ (9023 + 9023) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 9023 * (11 : ZMod 75691781281) ^ 9023 := by rw [pow_add]
          _ = 50490126572 := by rw [fermat_13]; decide
      have fermat_15 : (11 : ZMod 75691781281) ^ 36092 = 31644376158 := by
        calc
          (11 : ZMod 75691781281) ^ 36092 = (11 : ZMod 75691781281) ^ (18046 + 18046) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 18046 * (11 : ZMod 75691781281) ^ 18046 := by rw [pow_add]
          _ = 31644376158 := by rw [fermat_14]; decide
      have fermat_16 : (11 : ZMod 75691781281) ^ 72185 = 11974878386 := by
        calc
          (11 : ZMod 75691781281) ^ 72185 = (11 : ZMod 75691781281) ^ (36092 + 36092 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 36092 * (11 : ZMod 75691781281) ^ 36092) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 11974878386 := by rw [fermat_15]; decide
      have fermat_17 : (11 : ZMod 75691781281) ^ 144370 = 54850021689 := by
        calc
          (11 : ZMod 75691781281) ^ 144370 = (11 : ZMod 75691781281) ^ (72185 + 72185) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 72185 * (11 : ZMod 75691781281) ^ 72185 := by rw [pow_add]
          _ = 54850021689 := by rw [fermat_16]; decide
      have fermat_18 : (11 : ZMod 75691781281) ^ 288741 = 68089727119 := by
        calc
          (11 : ZMod 75691781281) ^ 288741 = (11 : ZMod 75691781281) ^ (144370 + 144370 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 144370 * (11 : ZMod 75691781281) ^ 144370) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 68089727119 := by rw [fermat_17]; decide
      have fermat_19 : (11 : ZMod 75691781281) ^ 577482 = 75318233506 := by
        calc
          (11 : ZMod 75691781281) ^ 577482 = (11 : ZMod 75691781281) ^ (288741 + 288741) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 288741 * (11 : ZMod 75691781281) ^ 288741 := by rw [pow_add]
          _ = 75318233506 := by rw [fermat_18]; decide
      have fermat_20 : (11 : ZMod 75691781281) ^ 1154964 = 65724145844 := by
        calc
          (11 : ZMod 75691781281) ^ 1154964 = (11 : ZMod 75691781281) ^ (577482 + 577482) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 577482 * (11 : ZMod 75691781281) ^ 577482 := by rw [pow_add]
          _ = 65724145844 := by rw [fermat_19]; decide
      have fermat_21 : (11 : ZMod 75691781281) ^ 2309929 = 4329191029 := by
        calc
          (11 : ZMod 75691781281) ^ 2309929 = (11 : ZMod 75691781281) ^ (1154964 + 1154964 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 1154964 * (11 : ZMod 75691781281) ^ 1154964) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 4329191029 := by rw [fermat_20]; decide
      have fermat_22 : (11 : ZMod 75691781281) ^ 4619859 = 31965863254 := by
        calc
          (11 : ZMod 75691781281) ^ 4619859 = (11 : ZMod 75691781281) ^ (2309929 + 2309929 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 2309929 * (11 : ZMod 75691781281) ^ 2309929) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 31965863254 := by rw [fermat_21]; decide
      have fermat_23 : (11 : ZMod 75691781281) ^ 9239719 = 11691652389 := by
        calc
          (11 : ZMod 75691781281) ^ 9239719 = (11 : ZMod 75691781281) ^ (4619859 + 4619859 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 4619859 * (11 : ZMod 75691781281) ^ 4619859) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 11691652389 := by rw [fermat_22]; decide
      have fermat_24 : (11 : ZMod 75691781281) ^ 18479438 = 29121300057 := by
        calc
          (11 : ZMod 75691781281) ^ 18479438 = (11 : ZMod 75691781281) ^ (9239719 + 9239719) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 9239719 * (11 : ZMod 75691781281) ^ 9239719 := by rw [pow_add]
          _ = 29121300057 := by rw [fermat_23]; decide
      have fermat_25 : (11 : ZMod 75691781281) ^ 36958877 = 4456159642 := by
        calc
          (11 : ZMod 75691781281) ^ 36958877 = (11 : ZMod 75691781281) ^ (18479438 + 18479438 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 18479438 * (11 : ZMod 75691781281) ^ 18479438) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 4456159642 := by rw [fermat_24]; decide
      have fermat_26 : (11 : ZMod 75691781281) ^ 73917755 = 54958674558 := by
        calc
          (11 : ZMod 75691781281) ^ 73917755 = (11 : ZMod 75691781281) ^ (36958877 + 36958877 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 36958877 * (11 : ZMod 75691781281) ^ 36958877) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 54958674558 := by rw [fermat_25]; decide
      have fermat_27 : (11 : ZMod 75691781281) ^ 147835510 = 68761111069 := by
        calc
          (11 : ZMod 75691781281) ^ 147835510 = (11 : ZMod 75691781281) ^ (73917755 + 73917755) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 73917755 * (11 : ZMod 75691781281) ^ 73917755 := by rw [pow_add]
          _ = 68761111069 := by rw [fermat_26]; decide
      have fermat_28 : (11 : ZMod 75691781281) ^ 295671020 = 44484511618 := by
        calc
          (11 : ZMod 75691781281) ^ 295671020 = (11 : ZMod 75691781281) ^ (147835510 + 147835510) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 147835510 * (11 : ZMod 75691781281) ^ 147835510 := by rw [pow_add]
          _ = 44484511618 := by rw [fermat_27]; decide
      have fermat_29 : (11 : ZMod 75691781281) ^ 591342041 = 72772124951 := by
        calc
          (11 : ZMod 75691781281) ^ 591342041 = (11 : ZMod 75691781281) ^ (295671020 + 295671020 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 295671020 * (11 : ZMod 75691781281) ^ 295671020) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 72772124951 := by rw [fermat_28]; decide
      have fermat_30 : (11 : ZMod 75691781281) ^ 1182684082 = 42874448943 := by
        calc
          (11 : ZMod 75691781281) ^ 1182684082 = (11 : ZMod 75691781281) ^ (591342041 + 591342041) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 591342041 * (11 : ZMod 75691781281) ^ 591342041 := by rw [pow_add]
          _ = 42874448943 := by rw [fermat_29]; decide
      have fermat_31 : (11 : ZMod 75691781281) ^ 2365368165 = 16922711876 := by
        calc
          (11 : ZMod 75691781281) ^ 2365368165 = (11 : ZMod 75691781281) ^ (1182684082 + 1182684082 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 1182684082 * (11 : ZMod 75691781281) ^ 1182684082) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 16922711876 := by rw [fermat_30]; decide
      have fermat_32 : (11 : ZMod 75691781281) ^ 4730736330 = 15629345055 := by
        calc
          (11 : ZMod 75691781281) ^ 4730736330 = (11 : ZMod 75691781281) ^ (2365368165 + 2365368165) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 2365368165 * (11 : ZMod 75691781281) ^ 2365368165 := by rw [pow_add]
          _ = 15629345055 := by rw [fermat_31]; decide
      have fermat_33 : (11 : ZMod 75691781281) ^ 9461472660 = 60788776565 := by
        calc
          (11 : ZMod 75691781281) ^ 9461472660 = (11 : ZMod 75691781281) ^ (4730736330 + 4730736330) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 4730736330 * (11 : ZMod 75691781281) ^ 4730736330 := by rw [pow_add]
          _ = 60788776565 := by rw [fermat_32]; decide
      have fermat_34 : (11 : ZMod 75691781281) ^ 18922945320 = 22345136793 := by
        calc
          (11 : ZMod 75691781281) ^ 18922945320 = (11 : ZMod 75691781281) ^ (9461472660 + 9461472660) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 9461472660 * (11 : ZMod 75691781281) ^ 9461472660 := by rw [pow_add]
          _ = 22345136793 := by rw [fermat_33]; decide
      have fermat_35 : (11 : ZMod 75691781281) ^ 37845890640 = 75691781280 := by
        calc
          (11 : ZMod 75691781281) ^ 37845890640 = (11 : ZMod 75691781281) ^ (18922945320 + 18922945320) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 18922945320 * (11 : ZMod 75691781281) ^ 18922945320 := by rw [pow_add]
          _ = 75691781280 := by rw [fermat_34]; decide
      have fermat_36 : (11 : ZMod 75691781281) ^ 75691781280 = 1 := by
        calc
          (11 : ZMod 75691781281) ^ 75691781280 = (11 : ZMod 75691781281) ^ (37845890640 + 37845890640) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 37845890640 * (11 : ZMod 75691781281) ^ 37845890640 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 2), (5, 1), (197, 1), (266821, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 2), (5, 1), (197, 1), (266821, 1)] : List FactorBlock).map factorBlockValue).prod = 75691781281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (11 : ZMod 75691781281) ^ 1 = 11 := by norm_num
      have factor_0_1 : (11 : ZMod 75691781281) ^ 2 = 121 := by
        calc
          (11 : ZMod 75691781281) ^ 2 = (11 : ZMod 75691781281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 1 * (11 : ZMod 75691781281) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_0_0]; decide
      have factor_0_2 : (11 : ZMod 75691781281) ^ 4 = 14641 := by
        calc
          (11 : ZMod 75691781281) ^ 4 = (11 : ZMod 75691781281) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 2 * (11 : ZMod 75691781281) ^ 2 := by rw [pow_add]
          _ = 14641 := by rw [factor_0_1]; decide
      have factor_0_3 : (11 : ZMod 75691781281) ^ 8 = 214358881 := by
        calc
          (11 : ZMod 75691781281) ^ 8 = (11 : ZMod 75691781281) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 4 * (11 : ZMod 75691781281) ^ 4 := by rw [pow_add]
          _ = 214358881 := by rw [factor_0_2]; decide
      have factor_0_4 : (11 : ZMod 75691781281) ^ 17 = 20639160071 := by
        calc
          (11 : ZMod 75691781281) ^ 17 = (11 : ZMod 75691781281) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 8 * (11 : ZMod 75691781281) ^ 8) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 20639160071 := by rw [factor_0_3]; decide
      have factor_0_5 : (11 : ZMod 75691781281) ^ 35 = 26000725628 := by
        calc
          (11 : ZMod 75691781281) ^ 35 = (11 : ZMod 75691781281) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 17 * (11 : ZMod 75691781281) ^ 17) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 26000725628 := by rw [factor_0_4]; decide
      have factor_0_6 : (11 : ZMod 75691781281) ^ 70 = 24175047773 := by
        calc
          (11 : ZMod 75691781281) ^ 70 = (11 : ZMod 75691781281) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 35 * (11 : ZMod 75691781281) ^ 35 := by rw [pow_add]
          _ = 24175047773 := by rw [factor_0_5]; decide
      have factor_0_7 : (11 : ZMod 75691781281) ^ 140 = 4623173409 := by
        calc
          (11 : ZMod 75691781281) ^ 140 = (11 : ZMod 75691781281) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 70 * (11 : ZMod 75691781281) ^ 70 := by rw [pow_add]
          _ = 4623173409 := by rw [factor_0_6]; decide
      have factor_0_8 : (11 : ZMod 75691781281) ^ 281 = 5252578648 := by
        calc
          (11 : ZMod 75691781281) ^ 281 = (11 : ZMod 75691781281) ^ (140 + 140 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 140 * (11 : ZMod 75691781281) ^ 140) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 5252578648 := by rw [factor_0_7]; decide
      have factor_0_9 : (11 : ZMod 75691781281) ^ 563 = 12324098022 := by
        calc
          (11 : ZMod 75691781281) ^ 563 = (11 : ZMod 75691781281) ^ (281 + 281 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 281 * (11 : ZMod 75691781281) ^ 281) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 12324098022 := by rw [factor_0_8]; decide
      have factor_0_10 : (11 : ZMod 75691781281) ^ 1127 = 72605680437 := by
        calc
          (11 : ZMod 75691781281) ^ 1127 = (11 : ZMod 75691781281) ^ (563 + 563 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 563 * (11 : ZMod 75691781281) ^ 563) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 72605680437 := by rw [factor_0_9]; decide
      have factor_0_11 : (11 : ZMod 75691781281) ^ 2255 = 29096297518 := by
        calc
          (11 : ZMod 75691781281) ^ 2255 = (11 : ZMod 75691781281) ^ (1127 + 1127 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 1127 * (11 : ZMod 75691781281) ^ 1127) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 29096297518 := by rw [factor_0_10]; decide
      have factor_0_12 : (11 : ZMod 75691781281) ^ 4511 = 55448136765 := by
        calc
          (11 : ZMod 75691781281) ^ 4511 = (11 : ZMod 75691781281) ^ (2255 + 2255 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 2255 * (11 : ZMod 75691781281) ^ 2255) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 55448136765 := by rw [factor_0_11]; decide
      have factor_0_13 : (11 : ZMod 75691781281) ^ 9023 = 61539820329 := by
        calc
          (11 : ZMod 75691781281) ^ 9023 = (11 : ZMod 75691781281) ^ (4511 + 4511 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 4511 * (11 : ZMod 75691781281) ^ 4511) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 61539820329 := by rw [factor_0_12]; decide
      have factor_0_14 : (11 : ZMod 75691781281) ^ 18046 = 50490126572 := by
        calc
          (11 : ZMod 75691781281) ^ 18046 = (11 : ZMod 75691781281) ^ (9023 + 9023) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 9023 * (11 : ZMod 75691781281) ^ 9023 := by rw [pow_add]
          _ = 50490126572 := by rw [factor_0_13]; decide
      have factor_0_15 : (11 : ZMod 75691781281) ^ 36092 = 31644376158 := by
        calc
          (11 : ZMod 75691781281) ^ 36092 = (11 : ZMod 75691781281) ^ (18046 + 18046) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 18046 * (11 : ZMod 75691781281) ^ 18046 := by rw [pow_add]
          _ = 31644376158 := by rw [factor_0_14]; decide
      have factor_0_16 : (11 : ZMod 75691781281) ^ 72185 = 11974878386 := by
        calc
          (11 : ZMod 75691781281) ^ 72185 = (11 : ZMod 75691781281) ^ (36092 + 36092 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 36092 * (11 : ZMod 75691781281) ^ 36092) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 11974878386 := by rw [factor_0_15]; decide
      have factor_0_17 : (11 : ZMod 75691781281) ^ 144370 = 54850021689 := by
        calc
          (11 : ZMod 75691781281) ^ 144370 = (11 : ZMod 75691781281) ^ (72185 + 72185) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 72185 * (11 : ZMod 75691781281) ^ 72185 := by rw [pow_add]
          _ = 54850021689 := by rw [factor_0_16]; decide
      have factor_0_18 : (11 : ZMod 75691781281) ^ 288741 = 68089727119 := by
        calc
          (11 : ZMod 75691781281) ^ 288741 = (11 : ZMod 75691781281) ^ (144370 + 144370 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 144370 * (11 : ZMod 75691781281) ^ 144370) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 68089727119 := by rw [factor_0_17]; decide
      have factor_0_19 : (11 : ZMod 75691781281) ^ 577482 = 75318233506 := by
        calc
          (11 : ZMod 75691781281) ^ 577482 = (11 : ZMod 75691781281) ^ (288741 + 288741) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 288741 * (11 : ZMod 75691781281) ^ 288741 := by rw [pow_add]
          _ = 75318233506 := by rw [factor_0_18]; decide
      have factor_0_20 : (11 : ZMod 75691781281) ^ 1154964 = 65724145844 := by
        calc
          (11 : ZMod 75691781281) ^ 1154964 = (11 : ZMod 75691781281) ^ (577482 + 577482) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 577482 * (11 : ZMod 75691781281) ^ 577482 := by rw [pow_add]
          _ = 65724145844 := by rw [factor_0_19]; decide
      have factor_0_21 : (11 : ZMod 75691781281) ^ 2309929 = 4329191029 := by
        calc
          (11 : ZMod 75691781281) ^ 2309929 = (11 : ZMod 75691781281) ^ (1154964 + 1154964 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 1154964 * (11 : ZMod 75691781281) ^ 1154964) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 4329191029 := by rw [factor_0_20]; decide
      have factor_0_22 : (11 : ZMod 75691781281) ^ 4619859 = 31965863254 := by
        calc
          (11 : ZMod 75691781281) ^ 4619859 = (11 : ZMod 75691781281) ^ (2309929 + 2309929 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 2309929 * (11 : ZMod 75691781281) ^ 2309929) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 31965863254 := by rw [factor_0_21]; decide
      have factor_0_23 : (11 : ZMod 75691781281) ^ 9239719 = 11691652389 := by
        calc
          (11 : ZMod 75691781281) ^ 9239719 = (11 : ZMod 75691781281) ^ (4619859 + 4619859 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 4619859 * (11 : ZMod 75691781281) ^ 4619859) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 11691652389 := by rw [factor_0_22]; decide
      have factor_0_24 : (11 : ZMod 75691781281) ^ 18479438 = 29121300057 := by
        calc
          (11 : ZMod 75691781281) ^ 18479438 = (11 : ZMod 75691781281) ^ (9239719 + 9239719) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 9239719 * (11 : ZMod 75691781281) ^ 9239719 := by rw [pow_add]
          _ = 29121300057 := by rw [factor_0_23]; decide
      have factor_0_25 : (11 : ZMod 75691781281) ^ 36958877 = 4456159642 := by
        calc
          (11 : ZMod 75691781281) ^ 36958877 = (11 : ZMod 75691781281) ^ (18479438 + 18479438 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 18479438 * (11 : ZMod 75691781281) ^ 18479438) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 4456159642 := by rw [factor_0_24]; decide
      have factor_0_26 : (11 : ZMod 75691781281) ^ 73917755 = 54958674558 := by
        calc
          (11 : ZMod 75691781281) ^ 73917755 = (11 : ZMod 75691781281) ^ (36958877 + 36958877 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 36958877 * (11 : ZMod 75691781281) ^ 36958877) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 54958674558 := by rw [factor_0_25]; decide
      have factor_0_27 : (11 : ZMod 75691781281) ^ 147835510 = 68761111069 := by
        calc
          (11 : ZMod 75691781281) ^ 147835510 = (11 : ZMod 75691781281) ^ (73917755 + 73917755) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 73917755 * (11 : ZMod 75691781281) ^ 73917755 := by rw [pow_add]
          _ = 68761111069 := by rw [factor_0_26]; decide
      have factor_0_28 : (11 : ZMod 75691781281) ^ 295671020 = 44484511618 := by
        calc
          (11 : ZMod 75691781281) ^ 295671020 = (11 : ZMod 75691781281) ^ (147835510 + 147835510) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 147835510 * (11 : ZMod 75691781281) ^ 147835510 := by rw [pow_add]
          _ = 44484511618 := by rw [factor_0_27]; decide
      have factor_0_29 : (11 : ZMod 75691781281) ^ 591342041 = 72772124951 := by
        calc
          (11 : ZMod 75691781281) ^ 591342041 = (11 : ZMod 75691781281) ^ (295671020 + 295671020 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 295671020 * (11 : ZMod 75691781281) ^ 295671020) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 72772124951 := by rw [factor_0_28]; decide
      have factor_0_30 : (11 : ZMod 75691781281) ^ 1182684082 = 42874448943 := by
        calc
          (11 : ZMod 75691781281) ^ 1182684082 = (11 : ZMod 75691781281) ^ (591342041 + 591342041) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 591342041 * (11 : ZMod 75691781281) ^ 591342041 := by rw [pow_add]
          _ = 42874448943 := by rw [factor_0_29]; decide
      have factor_0_31 : (11 : ZMod 75691781281) ^ 2365368165 = 16922711876 := by
        calc
          (11 : ZMod 75691781281) ^ 2365368165 = (11 : ZMod 75691781281) ^ (1182684082 + 1182684082 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 1182684082 * (11 : ZMod 75691781281) ^ 1182684082) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 16922711876 := by rw [factor_0_30]; decide
      have factor_0_32 : (11 : ZMod 75691781281) ^ 4730736330 = 15629345055 := by
        calc
          (11 : ZMod 75691781281) ^ 4730736330 = (11 : ZMod 75691781281) ^ (2365368165 + 2365368165) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 2365368165 * (11 : ZMod 75691781281) ^ 2365368165 := by rw [pow_add]
          _ = 15629345055 := by rw [factor_0_31]; decide
      have factor_0_33 : (11 : ZMod 75691781281) ^ 9461472660 = 60788776565 := by
        calc
          (11 : ZMod 75691781281) ^ 9461472660 = (11 : ZMod 75691781281) ^ (4730736330 + 4730736330) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 4730736330 * (11 : ZMod 75691781281) ^ 4730736330 := by rw [pow_add]
          _ = 60788776565 := by rw [factor_0_32]; decide
      have factor_0_34 : (11 : ZMod 75691781281) ^ 18922945320 = 22345136793 := by
        calc
          (11 : ZMod 75691781281) ^ 18922945320 = (11 : ZMod 75691781281) ^ (9461472660 + 9461472660) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 9461472660 * (11 : ZMod 75691781281) ^ 9461472660 := by rw [pow_add]
          _ = 22345136793 := by rw [factor_0_33]; decide
      have factor_0_35 : (11 : ZMod 75691781281) ^ 37845890640 = 75691781280 := by
        calc
          (11 : ZMod 75691781281) ^ 37845890640 = (11 : ZMod 75691781281) ^ (18922945320 + 18922945320) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 18922945320 * (11 : ZMod 75691781281) ^ 18922945320 := by rw [pow_add]
          _ = 75691781280 := by rw [factor_0_34]; decide
      change (11 : ZMod 75691781281) ^ 37845890640 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (11 : ZMod 75691781281) ^ 1 = 11 := by norm_num
      have factor_1_1 : (11 : ZMod 75691781281) ^ 2 = 121 := by
        calc
          (11 : ZMod 75691781281) ^ 2 = (11 : ZMod 75691781281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 1 * (11 : ZMod 75691781281) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_1_0]; decide
      have factor_1_2 : (11 : ZMod 75691781281) ^ 5 = 161051 := by
        calc
          (11 : ZMod 75691781281) ^ 5 = (11 : ZMod 75691781281) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 2 * (11 : ZMod 75691781281) ^ 2) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 161051 := by rw [factor_1_1]; decide
      have factor_1_3 : (11 : ZMod 75691781281) ^ 11 = 58236326768 := by
        calc
          (11 : ZMod 75691781281) ^ 11 = (11 : ZMod 75691781281) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 5 * (11 : ZMod 75691781281) ^ 5) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 58236326768 := by rw [factor_1_2]; decide
      have factor_1_4 : (11 : ZMod 75691781281) ^ 23 = 10572503533 := by
        calc
          (11 : ZMod 75691781281) ^ 23 = (11 : ZMod 75691781281) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 11 * (11 : ZMod 75691781281) ^ 11) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 10572503533 := by rw [factor_1_3]; decide
      have factor_1_5 : (11 : ZMod 75691781281) ^ 46 = 63608172503 := by
        calc
          (11 : ZMod 75691781281) ^ 46 = (11 : ZMod 75691781281) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 23 * (11 : ZMod 75691781281) ^ 23 := by rw [pow_add]
          _ = 63608172503 := by rw [factor_1_4]; decide
      have factor_1_6 : (11 : ZMod 75691781281) ^ 93 = 51823498613 := by
        calc
          (11 : ZMod 75691781281) ^ 93 = (11 : ZMod 75691781281) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 46 * (11 : ZMod 75691781281) ^ 46) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 51823498613 := by rw [factor_1_5]; decide
      have factor_1_7 : (11 : ZMod 75691781281) ^ 187 = 31108661080 := by
        calc
          (11 : ZMod 75691781281) ^ 187 = (11 : ZMod 75691781281) ^ (93 + 93 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 93 * (11 : ZMod 75691781281) ^ 93) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 31108661080 := by rw [factor_1_6]; decide
      have factor_1_8 : (11 : ZMod 75691781281) ^ 375 = 31438831695 := by
        calc
          (11 : ZMod 75691781281) ^ 375 = (11 : ZMod 75691781281) ^ (187 + 187 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 187 * (11 : ZMod 75691781281) ^ 187) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 31438831695 := by rw [factor_1_7]; decide
      have factor_1_9 : (11 : ZMod 75691781281) ^ 751 = 32389979391 := by
        calc
          (11 : ZMod 75691781281) ^ 751 = (11 : ZMod 75691781281) ^ (375 + 375 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 375 * (11 : ZMod 75691781281) ^ 375) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 32389979391 := by rw [factor_1_8]; decide
      have factor_1_10 : (11 : ZMod 75691781281) ^ 1503 = 44966817497 := by
        calc
          (11 : ZMod 75691781281) ^ 1503 = (11 : ZMod 75691781281) ^ (751 + 751 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 751 * (11 : ZMod 75691781281) ^ 751) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 44966817497 := by rw [factor_1_9]; decide
      have factor_1_11 : (11 : ZMod 75691781281) ^ 3007 = 68739967972 := by
        calc
          (11 : ZMod 75691781281) ^ 3007 = (11 : ZMod 75691781281) ^ (1503 + 1503 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 1503 * (11 : ZMod 75691781281) ^ 1503) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 68739967972 := by rw [factor_1_10]; decide
      have factor_1_12 : (11 : ZMod 75691781281) ^ 6015 = 17375523978 := by
        calc
          (11 : ZMod 75691781281) ^ 6015 = (11 : ZMod 75691781281) ^ (3007 + 3007 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 3007 * (11 : ZMod 75691781281) ^ 3007) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 17375523978 := by rw [factor_1_11]; decide
      have factor_1_13 : (11 : ZMod 75691781281) ^ 12030 = 50149025222 := by
        calc
          (11 : ZMod 75691781281) ^ 12030 = (11 : ZMod 75691781281) ^ (6015 + 6015) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 6015 * (11 : ZMod 75691781281) ^ 6015 := by rw [pow_add]
          _ = 50149025222 := by rw [factor_1_12]; decide
      have factor_1_14 : (11 : ZMod 75691781281) ^ 24061 = 4752062583 := by
        calc
          (11 : ZMod 75691781281) ^ 24061 = (11 : ZMod 75691781281) ^ (12030 + 12030 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 12030 * (11 : ZMod 75691781281) ^ 12030) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 4752062583 := by rw [factor_1_13]; decide
      have factor_1_15 : (11 : ZMod 75691781281) ^ 48123 = 29248802259 := by
        calc
          (11 : ZMod 75691781281) ^ 48123 = (11 : ZMod 75691781281) ^ (24061 + 24061 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 24061 * (11 : ZMod 75691781281) ^ 24061) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 29248802259 := by rw [factor_1_14]; decide
      have factor_1_16 : (11 : ZMod 75691781281) ^ 96247 = 2621389623 := by
        calc
          (11 : ZMod 75691781281) ^ 96247 = (11 : ZMod 75691781281) ^ (48123 + 48123 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 48123 * (11 : ZMod 75691781281) ^ 48123) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 2621389623 := by rw [factor_1_15]; decide
      have factor_1_17 : (11 : ZMod 75691781281) ^ 192494 = 44935370021 := by
        calc
          (11 : ZMod 75691781281) ^ 192494 = (11 : ZMod 75691781281) ^ (96247 + 96247) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 96247 * (11 : ZMod 75691781281) ^ 96247 := by rw [pow_add]
          _ = 44935370021 := by rw [factor_1_16]; decide
      have factor_1_18 : (11 : ZMod 75691781281) ^ 384988 = 4437186533 := by
        calc
          (11 : ZMod 75691781281) ^ 384988 = (11 : ZMod 75691781281) ^ (192494 + 192494) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 192494 * (11 : ZMod 75691781281) ^ 192494 := by rw [pow_add]
          _ = 4437186533 := by rw [factor_1_17]; decide
      have factor_1_19 : (11 : ZMod 75691781281) ^ 769976 = 23276846901 := by
        calc
          (11 : ZMod 75691781281) ^ 769976 = (11 : ZMod 75691781281) ^ (384988 + 384988) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 384988 * (11 : ZMod 75691781281) ^ 384988 := by rw [pow_add]
          _ = 23276846901 := by rw [factor_1_18]; decide
      have factor_1_20 : (11 : ZMod 75691781281) ^ 1539953 = 26636269714 := by
        calc
          (11 : ZMod 75691781281) ^ 1539953 = (11 : ZMod 75691781281) ^ (769976 + 769976 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 769976 * (11 : ZMod 75691781281) ^ 769976) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 26636269714 := by rw [factor_1_19]; decide
      have factor_1_21 : (11 : ZMod 75691781281) ^ 3079906 = 61440931134 := by
        calc
          (11 : ZMod 75691781281) ^ 3079906 = (11 : ZMod 75691781281) ^ (1539953 + 1539953) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 1539953 * (11 : ZMod 75691781281) ^ 1539953 := by rw [pow_add]
          _ = 61440931134 := by rw [factor_1_20]; decide
      have factor_1_22 : (11 : ZMod 75691781281) ^ 6159812 = 67141782559 := by
        calc
          (11 : ZMod 75691781281) ^ 6159812 = (11 : ZMod 75691781281) ^ (3079906 + 3079906) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 3079906 * (11 : ZMod 75691781281) ^ 3079906 := by rw [pow_add]
          _ = 67141782559 := by rw [factor_1_21]; decide
      have factor_1_23 : (11 : ZMod 75691781281) ^ 12319625 = 51077255906 := by
        calc
          (11 : ZMod 75691781281) ^ 12319625 = (11 : ZMod 75691781281) ^ (6159812 + 6159812 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 6159812 * (11 : ZMod 75691781281) ^ 6159812) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 51077255906 := by rw [factor_1_22]; decide
      have factor_1_24 : (11 : ZMod 75691781281) ^ 24639251 = 60620470392 := by
        calc
          (11 : ZMod 75691781281) ^ 24639251 = (11 : ZMod 75691781281) ^ (12319625 + 12319625 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 12319625 * (11 : ZMod 75691781281) ^ 12319625) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 60620470392 := by rw [factor_1_23]; decide
      have factor_1_25 : (11 : ZMod 75691781281) ^ 49278503 = 7667982850 := by
        calc
          (11 : ZMod 75691781281) ^ 49278503 = (11 : ZMod 75691781281) ^ (24639251 + 24639251 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 24639251 * (11 : ZMod 75691781281) ^ 24639251) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 7667982850 := by rw [factor_1_24]; decide
      have factor_1_26 : (11 : ZMod 75691781281) ^ 98557006 = 39960457808 := by
        calc
          (11 : ZMod 75691781281) ^ 98557006 = (11 : ZMod 75691781281) ^ (49278503 + 49278503) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 49278503 * (11 : ZMod 75691781281) ^ 49278503 := by rw [pow_add]
          _ = 39960457808 := by rw [factor_1_25]; decide
      have factor_1_27 : (11 : ZMod 75691781281) ^ 197114013 = 57391107734 := by
        calc
          (11 : ZMod 75691781281) ^ 197114013 = (11 : ZMod 75691781281) ^ (98557006 + 98557006 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 98557006 * (11 : ZMod 75691781281) ^ 98557006) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 57391107734 := by rw [factor_1_26]; decide
      have factor_1_28 : (11 : ZMod 75691781281) ^ 394228027 = 18758692651 := by
        calc
          (11 : ZMod 75691781281) ^ 394228027 = (11 : ZMod 75691781281) ^ (197114013 + 197114013 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 197114013 * (11 : ZMod 75691781281) ^ 197114013) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 18758692651 := by rw [factor_1_27]; decide
      have factor_1_29 : (11 : ZMod 75691781281) ^ 788456055 = 70030684235 := by
        calc
          (11 : ZMod 75691781281) ^ 788456055 = (11 : ZMod 75691781281) ^ (394228027 + 394228027 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 394228027 * (11 : ZMod 75691781281) ^ 394228027) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 70030684235 := by rw [factor_1_28]; decide
      have factor_1_30 : (11 : ZMod 75691781281) ^ 1576912110 = 52531883417 := by
        calc
          (11 : ZMod 75691781281) ^ 1576912110 = (11 : ZMod 75691781281) ^ (788456055 + 788456055) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 788456055 * (11 : ZMod 75691781281) ^ 788456055 := by rw [pow_add]
          _ = 52531883417 := by rw [factor_1_29]; decide
      have factor_1_31 : (11 : ZMod 75691781281) ^ 3153824220 = 71090986034 := by
        calc
          (11 : ZMod 75691781281) ^ 3153824220 = (11 : ZMod 75691781281) ^ (1576912110 + 1576912110) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 1576912110 * (11 : ZMod 75691781281) ^ 1576912110 := by rw [pow_add]
          _ = 71090986034 := by rw [factor_1_30]; decide
      have factor_1_32 : (11 : ZMod 75691781281) ^ 6307648440 = 62352595873 := by
        calc
          (11 : ZMod 75691781281) ^ 6307648440 = (11 : ZMod 75691781281) ^ (3153824220 + 3153824220) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 3153824220 * (11 : ZMod 75691781281) ^ 3153824220 := by rw [pow_add]
          _ = 62352595873 := by rw [factor_1_31]; decide
      have factor_1_33 : (11 : ZMod 75691781281) ^ 12615296880 = 18358891723 := by
        calc
          (11 : ZMod 75691781281) ^ 12615296880 = (11 : ZMod 75691781281) ^ (6307648440 + 6307648440) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 6307648440 * (11 : ZMod 75691781281) ^ 6307648440 := by rw [pow_add]
          _ = 18358891723 := by rw [factor_1_32]; decide
      have factor_1_34 : (11 : ZMod 75691781281) ^ 25230593760 = 18358891722 := by
        calc
          (11 : ZMod 75691781281) ^ 25230593760 = (11 : ZMod 75691781281) ^ (12615296880 + 12615296880) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 12615296880 * (11 : ZMod 75691781281) ^ 12615296880 := by rw [pow_add]
          _ = 18358891722 := by rw [factor_1_33]; decide
      change (11 : ZMod 75691781281) ^ 25230593760 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (11 : ZMod 75691781281) ^ 1 = 11 := by norm_num
      have factor_2_1 : (11 : ZMod 75691781281) ^ 3 = 1331 := by
        calc
          (11 : ZMod 75691781281) ^ 3 = (11 : ZMod 75691781281) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 1 * (11 : ZMod 75691781281) ^ 1) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 1331 := by rw [factor_2_0]; decide
      have factor_2_2 : (11 : ZMod 75691781281) ^ 7 = 19487171 := by
        calc
          (11 : ZMod 75691781281) ^ 7 = (11 : ZMod 75691781281) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 3 * (11 : ZMod 75691781281) ^ 3) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 19487171 := by rw [factor_2_1]; decide
      have factor_2_3 : (11 : ZMod 75691781281) ^ 14 = 4166896464 := by
        calc
          (11 : ZMod 75691781281) ^ 14 = (11 : ZMod 75691781281) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 7 * (11 : ZMod 75691781281) ^ 7 := by rw [pow_add]
          _ = 4166896464 := by rw [factor_2_2]; decide
      have factor_2_4 : (11 : ZMod 75691781281) ^ 28 = 25646577088 := by
        calc
          (11 : ZMod 75691781281) ^ 28 = (11 : ZMod 75691781281) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 14 * (11 : ZMod 75691781281) ^ 14 := by rw [pow_add]
          _ = 25646577088 := by rw [factor_2_3]; decide
      have factor_2_5 : (11 : ZMod 75691781281) ^ 56 = 10706315064 := by
        calc
          (11 : ZMod 75691781281) ^ 56 = (11 : ZMod 75691781281) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 28 * (11 : ZMod 75691781281) ^ 28 := by rw [pow_add]
          _ = 10706315064 := by rw [factor_2_4]; decide
      have factor_2_6 : (11 : ZMod 75691781281) ^ 112 = 31715490562 := by
        calc
          (11 : ZMod 75691781281) ^ 112 = (11 : ZMod 75691781281) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 56 * (11 : ZMod 75691781281) ^ 56 := by rw [pow_add]
          _ = 31715490562 := by rw [factor_2_5]; decide
      have factor_2_7 : (11 : ZMod 75691781281) ^ 225 = 57413954374 := by
        calc
          (11 : ZMod 75691781281) ^ 225 = (11 : ZMod 75691781281) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 112 * (11 : ZMod 75691781281) ^ 112) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 57413954374 := by rw [factor_2_6]; decide
      have factor_2_8 : (11 : ZMod 75691781281) ^ 451 = 2537695082 := by
        calc
          (11 : ZMod 75691781281) ^ 451 = (11 : ZMod 75691781281) ^ (225 + 225 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 225 * (11 : ZMod 75691781281) ^ 225) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 2537695082 := by rw [factor_2_7]; decide
      have factor_2_9 : (11 : ZMod 75691781281) ^ 902 = 66709678042 := by
        calc
          (11 : ZMod 75691781281) ^ 902 = (11 : ZMod 75691781281) ^ (451 + 451) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 451 * (11 : ZMod 75691781281) ^ 451 := by rw [pow_add]
          _ = 66709678042 := by rw [factor_2_8]; decide
      have factor_2_10 : (11 : ZMod 75691781281) ^ 1804 = 34413771223 := by
        calc
          (11 : ZMod 75691781281) ^ 1804 = (11 : ZMod 75691781281) ^ (902 + 902) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 902 * (11 : ZMod 75691781281) ^ 902 := by rw [pow_add]
          _ = 34413771223 := by rw [factor_2_9]; decide
      have factor_2_11 : (11 : ZMod 75691781281) ^ 3609 = 69275594615 := by
        calc
          (11 : ZMod 75691781281) ^ 3609 = (11 : ZMod 75691781281) ^ (1804 + 1804 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 1804 * (11 : ZMod 75691781281) ^ 1804) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 69275594615 := by rw [factor_2_10]; decide
      have factor_2_12 : (11 : ZMod 75691781281) ^ 7218 = 53735081484 := by
        calc
          (11 : ZMod 75691781281) ^ 7218 = (11 : ZMod 75691781281) ^ (3609 + 3609) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 3609 * (11 : ZMod 75691781281) ^ 3609 := by rw [pow_add]
          _ = 53735081484 := by rw [factor_2_11]; decide
      have factor_2_13 : (11 : ZMod 75691781281) ^ 14437 = 52634629760 := by
        calc
          (11 : ZMod 75691781281) ^ 14437 = (11 : ZMod 75691781281) ^ (7218 + 7218 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 7218 * (11 : ZMod 75691781281) ^ 7218) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 52634629760 := by rw [factor_2_12]; decide
      have factor_2_14 : (11 : ZMod 75691781281) ^ 28874 = 5976854057 := by
        calc
          (11 : ZMod 75691781281) ^ 28874 = (11 : ZMod 75691781281) ^ (14437 + 14437) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 14437 * (11 : ZMod 75691781281) ^ 14437 := by rw [pow_add]
          _ = 5976854057 := by rw [factor_2_13]; decide
      have factor_2_15 : (11 : ZMod 75691781281) ^ 57748 = 27444733252 := by
        calc
          (11 : ZMod 75691781281) ^ 57748 = (11 : ZMod 75691781281) ^ (28874 + 28874) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 28874 * (11 : ZMod 75691781281) ^ 28874 := by rw [pow_add]
          _ = 27444733252 := by rw [factor_2_14]; decide
      have factor_2_16 : (11 : ZMod 75691781281) ^ 115496 = 38813384479 := by
        calc
          (11 : ZMod 75691781281) ^ 115496 = (11 : ZMod 75691781281) ^ (57748 + 57748) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 57748 * (11 : ZMod 75691781281) ^ 57748 := by rw [pow_add]
          _ = 38813384479 := by rw [factor_2_15]; decide
      have factor_2_17 : (11 : ZMod 75691781281) ^ 230992 = 3106500237 := by
        calc
          (11 : ZMod 75691781281) ^ 230992 = (11 : ZMod 75691781281) ^ (115496 + 115496) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 115496 * (11 : ZMod 75691781281) ^ 115496 := by rw [pow_add]
          _ = 3106500237 := by rw [factor_2_16]; decide
      have factor_2_18 : (11 : ZMod 75691781281) ^ 461985 = 31425357463 := by
        calc
          (11 : ZMod 75691781281) ^ 461985 = (11 : ZMod 75691781281) ^ (230992 + 230992 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 230992 * (11 : ZMod 75691781281) ^ 230992) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 31425357463 := by rw [factor_2_17]; decide
      have factor_2_19 : (11 : ZMod 75691781281) ^ 923971 = 72737164341 := by
        calc
          (11 : ZMod 75691781281) ^ 923971 = (11 : ZMod 75691781281) ^ (461985 + 461985 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 461985 * (11 : ZMod 75691781281) ^ 461985) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 72737164341 := by rw [factor_2_18]; decide
      have factor_2_20 : (11 : ZMod 75691781281) ^ 1847943 = 63036541888 := by
        calc
          (11 : ZMod 75691781281) ^ 1847943 = (11 : ZMod 75691781281) ^ (923971 + 923971 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 923971 * (11 : ZMod 75691781281) ^ 923971) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 63036541888 := by rw [factor_2_19]; decide
      have factor_2_21 : (11 : ZMod 75691781281) ^ 3695887 = 57952463005 := by
        calc
          (11 : ZMod 75691781281) ^ 3695887 = (11 : ZMod 75691781281) ^ (1847943 + 1847943 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 1847943 * (11 : ZMod 75691781281) ^ 1847943) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 57952463005 := by rw [factor_2_20]; decide
      have factor_2_22 : (11 : ZMod 75691781281) ^ 7391775 = 23598202870 := by
        calc
          (11 : ZMod 75691781281) ^ 7391775 = (11 : ZMod 75691781281) ^ (3695887 + 3695887 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 3695887 * (11 : ZMod 75691781281) ^ 3695887) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 23598202870 := by rw [factor_2_21]; decide
      have factor_2_23 : (11 : ZMod 75691781281) ^ 14783551 = 10406047583 := by
        calc
          (11 : ZMod 75691781281) ^ 14783551 = (11 : ZMod 75691781281) ^ (7391775 + 7391775 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 7391775 * (11 : ZMod 75691781281) ^ 7391775) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 10406047583 := by rw [factor_2_22]; decide
      have factor_2_24 : (11 : ZMod 75691781281) ^ 29567102 = 10849002671 := by
        calc
          (11 : ZMod 75691781281) ^ 29567102 = (11 : ZMod 75691781281) ^ (14783551 + 14783551) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 14783551 * (11 : ZMod 75691781281) ^ 14783551 := by rw [pow_add]
          _ = 10849002671 := by rw [factor_2_23]; decide
      have factor_2_25 : (11 : ZMod 75691781281) ^ 59134204 = 17607921044 := by
        calc
          (11 : ZMod 75691781281) ^ 59134204 = (11 : ZMod 75691781281) ^ (29567102 + 29567102) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 29567102 * (11 : ZMod 75691781281) ^ 29567102 := by rw [pow_add]
          _ = 17607921044 := by rw [factor_2_24]; decide
      have factor_2_26 : (11 : ZMod 75691781281) ^ 118268408 = 43181672410 := by
        calc
          (11 : ZMod 75691781281) ^ 118268408 = (11 : ZMod 75691781281) ^ (59134204 + 59134204) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 59134204 * (11 : ZMod 75691781281) ^ 59134204 := by rw [pow_add]
          _ = 43181672410 := by rw [factor_2_25]; decide
      have factor_2_27 : (11 : ZMod 75691781281) ^ 236536816 = 37414947974 := by
        calc
          (11 : ZMod 75691781281) ^ 236536816 = (11 : ZMod 75691781281) ^ (118268408 + 118268408) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 118268408 * (11 : ZMod 75691781281) ^ 118268408 := by rw [pow_add]
          _ = 37414947974 := by rw [factor_2_26]; decide
      have factor_2_28 : (11 : ZMod 75691781281) ^ 473073633 = 24177194924 := by
        calc
          (11 : ZMod 75691781281) ^ 473073633 = (11 : ZMod 75691781281) ^ (236536816 + 236536816 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 236536816 * (11 : ZMod 75691781281) ^ 236536816) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 24177194924 := by rw [factor_2_27]; decide
      have factor_2_29 : (11 : ZMod 75691781281) ^ 946147266 = 42451228527 := by
        calc
          (11 : ZMod 75691781281) ^ 946147266 = (11 : ZMod 75691781281) ^ (473073633 + 473073633) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 473073633 * (11 : ZMod 75691781281) ^ 473073633 := by rw [pow_add]
          _ = 42451228527 := by rw [factor_2_28]; decide
      have factor_2_30 : (11 : ZMod 75691781281) ^ 1892294532 = 24135706240 := by
        calc
          (11 : ZMod 75691781281) ^ 1892294532 = (11 : ZMod 75691781281) ^ (946147266 + 946147266) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 946147266 * (11 : ZMod 75691781281) ^ 946147266 := by rw [pow_add]
          _ = 24135706240 := by rw [factor_2_29]; decide
      have factor_2_31 : (11 : ZMod 75691781281) ^ 3784589064 = 71187917141 := by
        calc
          (11 : ZMod 75691781281) ^ 3784589064 = (11 : ZMod 75691781281) ^ (1892294532 + 1892294532) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 1892294532 * (11 : ZMod 75691781281) ^ 1892294532 := by rw [pow_add]
          _ = 71187917141 := by rw [factor_2_30]; decide
      have factor_2_32 : (11 : ZMod 75691781281) ^ 7569178128 = 39753062476 := by
        calc
          (11 : ZMod 75691781281) ^ 7569178128 = (11 : ZMod 75691781281) ^ (3784589064 + 3784589064) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 3784589064 * (11 : ZMod 75691781281) ^ 3784589064 := by rw [pow_add]
          _ = 39753062476 := by rw [factor_2_31]; decide
      have factor_2_33 : (11 : ZMod 75691781281) ^ 15138356256 = 28373565028 := by
        calc
          (11 : ZMod 75691781281) ^ 15138356256 = (11 : ZMod 75691781281) ^ (7569178128 + 7569178128) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 7569178128 * (11 : ZMod 75691781281) ^ 7569178128 := by rw [pow_add]
          _ = 28373565028 := by rw [factor_2_32]; decide
      change (11 : ZMod 75691781281) ^ 15138356256 ≠ 1
      rw [factor_2_33]
      decide
    ·
      have factor_3_0 : (11 : ZMod 75691781281) ^ 1 = 11 := by norm_num
      have factor_3_1 : (11 : ZMod 75691781281) ^ 2 = 121 := by
        calc
          (11 : ZMod 75691781281) ^ 2 = (11 : ZMod 75691781281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 1 * (11 : ZMod 75691781281) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_3_0]; decide
      have factor_3_2 : (11 : ZMod 75691781281) ^ 5 = 161051 := by
        calc
          (11 : ZMod 75691781281) ^ 5 = (11 : ZMod 75691781281) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 2 * (11 : ZMod 75691781281) ^ 2) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 161051 := by rw [factor_3_1]; decide
      have factor_3_3 : (11 : ZMod 75691781281) ^ 11 = 58236326768 := by
        calc
          (11 : ZMod 75691781281) ^ 11 = (11 : ZMod 75691781281) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 5 * (11 : ZMod 75691781281) ^ 5) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 58236326768 := by rw [factor_3_2]; decide
      have factor_3_4 : (11 : ZMod 75691781281) ^ 22 = 28485420787 := by
        calc
          (11 : ZMod 75691781281) ^ 22 = (11 : ZMod 75691781281) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 11 * (11 : ZMod 75691781281) ^ 11 := by rw [pow_add]
          _ = 28485420787 := by rw [factor_3_3]; decide
      have factor_3_5 : (11 : ZMod 75691781281) ^ 45 = 60831129341 := by
        calc
          (11 : ZMod 75691781281) ^ 45 = (11 : ZMod 75691781281) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 22 * (11 : ZMod 75691781281) ^ 22) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 60831129341 := by rw [factor_3_4]; decide
      have factor_3_6 : (11 : ZMod 75691781281) ^ 91 = 39838063796 := by
        calc
          (11 : ZMod 75691781281) ^ 91 = (11 : ZMod 75691781281) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 45 * (11 : ZMod 75691781281) ^ 45) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 39838063796 := by rw [factor_3_5]; decide
      have factor_3_7 : (11 : ZMod 75691781281) ^ 183 = 68905892328 := by
        calc
          (11 : ZMod 75691781281) ^ 183 = (11 : ZMod 75691781281) ^ (91 + 91 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 91 * (11 : ZMod 75691781281) ^ 91) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 68905892328 := by rw [factor_3_6]; decide
      have factor_3_8 : (11 : ZMod 75691781281) ^ 366 = 5068503558 := by
        calc
          (11 : ZMod 75691781281) ^ 366 = (11 : ZMod 75691781281) ^ (183 + 183) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 183 * (11 : ZMod 75691781281) ^ 183 := by rw [pow_add]
          _ = 5068503558 := by rw [factor_3_7]; decide
      have factor_3_9 : (11 : ZMod 75691781281) ^ 732 = 45023253627 := by
        calc
          (11 : ZMod 75691781281) ^ 732 = (11 : ZMod 75691781281) ^ (366 + 366) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 366 * (11 : ZMod 75691781281) ^ 366 := by rw [pow_add]
          _ = 45023253627 := by rw [factor_3_8]; decide
      have factor_3_10 : (11 : ZMod 75691781281) ^ 1465 = 72997490226 := by
        calc
          (11 : ZMod 75691781281) ^ 1465 = (11 : ZMod 75691781281) ^ (732 + 732 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 732 * (11 : ZMod 75691781281) ^ 732) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 72997490226 := by rw [factor_3_9]; decide
      have factor_3_11 : (11 : ZMod 75691781281) ^ 2931 = 41677266600 := by
        calc
          (11 : ZMod 75691781281) ^ 2931 = (11 : ZMod 75691781281) ^ (1465 + 1465 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 1465 * (11 : ZMod 75691781281) ^ 1465) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 41677266600 := by rw [factor_3_10]; decide
      have factor_3_12 : (11 : ZMod 75691781281) ^ 5862 = 44927863898 := by
        calc
          (11 : ZMod 75691781281) ^ 5862 = (11 : ZMod 75691781281) ^ (2931 + 2931) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 2931 * (11 : ZMod 75691781281) ^ 2931 := by rw [pow_add]
          _ = 44927863898 := by rw [factor_3_11]; decide
      have factor_3_13 : (11 : ZMod 75691781281) ^ 11725 = 56209026746 := by
        calc
          (11 : ZMod 75691781281) ^ 11725 = (11 : ZMod 75691781281) ^ (5862 + 5862 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 5862 * (11 : ZMod 75691781281) ^ 5862) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 56209026746 := by rw [factor_3_12]; decide
      have factor_3_14 : (11 : ZMod 75691781281) ^ 23451 = 42707452991 := by
        calc
          (11 : ZMod 75691781281) ^ 23451 = (11 : ZMod 75691781281) ^ (11725 + 11725 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 11725 * (11 : ZMod 75691781281) ^ 11725) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 42707452991 := by rw [factor_3_13]; decide
      have factor_3_15 : (11 : ZMod 75691781281) ^ 46902 = 17013846097 := by
        calc
          (11 : ZMod 75691781281) ^ 46902 = (11 : ZMod 75691781281) ^ (23451 + 23451) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 23451 * (11 : ZMod 75691781281) ^ 23451 := by rw [pow_add]
          _ = 17013846097 := by rw [factor_3_14]; decide
      have factor_3_16 : (11 : ZMod 75691781281) ^ 93804 = 14271435202 := by
        calc
          (11 : ZMod 75691781281) ^ 93804 = (11 : ZMod 75691781281) ^ (46902 + 46902) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 46902 * (11 : ZMod 75691781281) ^ 46902 := by rw [pow_add]
          _ = 14271435202 := by rw [factor_3_15]; decide
      have factor_3_17 : (11 : ZMod 75691781281) ^ 187608 = 58475865664 := by
        calc
          (11 : ZMod 75691781281) ^ 187608 = (11 : ZMod 75691781281) ^ (93804 + 93804) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 93804 * (11 : ZMod 75691781281) ^ 93804 := by rw [pow_add]
          _ = 58475865664 := by rw [factor_3_16]; decide
      have factor_3_18 : (11 : ZMod 75691781281) ^ 375217 = 14077604896 := by
        calc
          (11 : ZMod 75691781281) ^ 375217 = (11 : ZMod 75691781281) ^ (187608 + 187608 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 187608 * (11 : ZMod 75691781281) ^ 187608) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 14077604896 := by rw [factor_3_17]; decide
      have factor_3_19 : (11 : ZMod 75691781281) ^ 750434 = 10548255765 := by
        calc
          (11 : ZMod 75691781281) ^ 750434 = (11 : ZMod 75691781281) ^ (375217 + 375217) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 375217 * (11 : ZMod 75691781281) ^ 375217 := by rw [pow_add]
          _ = 10548255765 := by rw [factor_3_18]; decide
      have factor_3_20 : (11 : ZMod 75691781281) ^ 1500868 = 65539703168 := by
        calc
          (11 : ZMod 75691781281) ^ 1500868 = (11 : ZMod 75691781281) ^ (750434 + 750434) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 750434 * (11 : ZMod 75691781281) ^ 750434 := by rw [pow_add]
          _ = 65539703168 := by rw [factor_3_19]; decide
      have factor_3_21 : (11 : ZMod 75691781281) ^ 3001736 = 65288941418 := by
        calc
          (11 : ZMod 75691781281) ^ 3001736 = (11 : ZMod 75691781281) ^ (1500868 + 1500868) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 1500868 * (11 : ZMod 75691781281) ^ 1500868 := by rw [pow_add]
          _ = 65288941418 := by rw [factor_3_20]; decide
      have factor_3_22 : (11 : ZMod 75691781281) ^ 6003472 = 26500494525 := by
        calc
          (11 : ZMod 75691781281) ^ 6003472 = (11 : ZMod 75691781281) ^ (3001736 + 3001736) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 3001736 * (11 : ZMod 75691781281) ^ 3001736 := by rw [pow_add]
          _ = 26500494525 := by rw [factor_3_21]; decide
      have factor_3_23 : (11 : ZMod 75691781281) ^ 12006945 = 5747869125 := by
        calc
          (11 : ZMod 75691781281) ^ 12006945 = (11 : ZMod 75691781281) ^ (6003472 + 6003472 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 6003472 * (11 : ZMod 75691781281) ^ 6003472) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 5747869125 := by rw [factor_3_22]; decide
      have factor_3_24 : (11 : ZMod 75691781281) ^ 24013890 = 71103927355 := by
        calc
          (11 : ZMod 75691781281) ^ 24013890 = (11 : ZMod 75691781281) ^ (12006945 + 12006945) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 12006945 * (11 : ZMod 75691781281) ^ 12006945 := by rw [pow_add]
          _ = 71103927355 := by rw [factor_3_23]; decide
      have factor_3_25 : (11 : ZMod 75691781281) ^ 48027780 = 30384713679 := by
        calc
          (11 : ZMod 75691781281) ^ 48027780 = (11 : ZMod 75691781281) ^ (24013890 + 24013890) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 24013890 * (11 : ZMod 75691781281) ^ 24013890 := by rw [pow_add]
          _ = 30384713679 := by rw [factor_3_24]; decide
      have factor_3_26 : (11 : ZMod 75691781281) ^ 96055560 = 15274023801 := by
        calc
          (11 : ZMod 75691781281) ^ 96055560 = (11 : ZMod 75691781281) ^ (48027780 + 48027780) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 48027780 * (11 : ZMod 75691781281) ^ 48027780 := by rw [pow_add]
          _ = 15274023801 := by rw [factor_3_25]; decide
      have factor_3_27 : (11 : ZMod 75691781281) ^ 192111120 = 27135769366 := by
        calc
          (11 : ZMod 75691781281) ^ 192111120 = (11 : ZMod 75691781281) ^ (96055560 + 96055560) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 96055560 * (11 : ZMod 75691781281) ^ 96055560 := by rw [pow_add]
          _ = 27135769366 := by rw [factor_3_26]; decide
      have factor_3_28 : (11 : ZMod 75691781281) ^ 384222240 = 46415746637 := by
        calc
          (11 : ZMod 75691781281) ^ 384222240 = (11 : ZMod 75691781281) ^ (192111120 + 192111120) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 192111120 * (11 : ZMod 75691781281) ^ 192111120 := by rw [pow_add]
          _ = 46415746637 := by rw [factor_3_27]; decide
      change (11 : ZMod 75691781281) ^ 384222240 ≠ 1
      rw [factor_3_28]
      decide
    ·
      have factor_4_0 : (11 : ZMod 75691781281) ^ 1 = 11 := by norm_num
      have factor_4_1 : (11 : ZMod 75691781281) ^ 2 = 121 := by
        calc
          (11 : ZMod 75691781281) ^ 2 = (11 : ZMod 75691781281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 1 * (11 : ZMod 75691781281) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_4_0]; decide
      have factor_4_2 : (11 : ZMod 75691781281) ^ 4 = 14641 := by
        calc
          (11 : ZMod 75691781281) ^ 4 = (11 : ZMod 75691781281) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 2 * (11 : ZMod 75691781281) ^ 2 := by rw [pow_add]
          _ = 14641 := by rw [factor_4_1]; decide
      have factor_4_3 : (11 : ZMod 75691781281) ^ 8 = 214358881 := by
        calc
          (11 : ZMod 75691781281) ^ 8 = (11 : ZMod 75691781281) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 4 * (11 : ZMod 75691781281) ^ 4 := by rw [pow_add]
          _ = 214358881 := by rw [factor_4_2]; decide
      have factor_4_4 : (11 : ZMod 75691781281) ^ 17 = 20639160071 := by
        calc
          (11 : ZMod 75691781281) ^ 17 = (11 : ZMod 75691781281) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 8 * (11 : ZMod 75691781281) ^ 8) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 20639160071 := by rw [factor_4_3]; decide
      have factor_4_5 : (11 : ZMod 75691781281) ^ 34 = 29887986432 := by
        calc
          (11 : ZMod 75691781281) ^ 34 = (11 : ZMod 75691781281) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 17 * (11 : ZMod 75691781281) ^ 17 := by rw [pow_add]
          _ = 29887986432 := by rw [factor_4_4]; decide
      have factor_4_6 : (11 : ZMod 75691781281) ^ 69 = 43484157769 := by
        calc
          (11 : ZMod 75691781281) ^ 69 = (11 : ZMod 75691781281) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 34 * (11 : ZMod 75691781281) ^ 34) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 43484157769 := by rw [factor_4_5]; decide
      have factor_4_7 : (11 : ZMod 75691781281) ^ 138 = 51959016692 := by
        calc
          (11 : ZMod 75691781281) ^ 138 = (11 : ZMod 75691781281) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 69 * (11 : ZMod 75691781281) ^ 69 := by rw [pow_add]
          _ = 51959016692 := by rw [factor_4_6]; decide
      have factor_4_8 : (11 : ZMod 75691781281) ^ 277 = 55012738009 := by
        calc
          (11 : ZMod 75691781281) ^ 277 = (11 : ZMod 75691781281) ^ (138 + 138 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 138 * (11 : ZMod 75691781281) ^ 138) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 55012738009 := by rw [factor_4_7]; decide
      have factor_4_9 : (11 : ZMod 75691781281) ^ 554 = 43390538398 := by
        calc
          (11 : ZMod 75691781281) ^ 554 = (11 : ZMod 75691781281) ^ (277 + 277) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 277 * (11 : ZMod 75691781281) ^ 277 := by rw [pow_add]
          _ = 43390538398 := by rw [factor_4_8]; decide
      have factor_4_10 : (11 : ZMod 75691781281) ^ 1108 = 52358282933 := by
        calc
          (11 : ZMod 75691781281) ^ 1108 = (11 : ZMod 75691781281) ^ (554 + 554) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 554 * (11 : ZMod 75691781281) ^ 554 := by rw [pow_add]
          _ = 52358282933 := by rw [factor_4_9]; decide
      have factor_4_11 : (11 : ZMod 75691781281) ^ 2216 = 3200596787 := by
        calc
          (11 : ZMod 75691781281) ^ 2216 = (11 : ZMod 75691781281) ^ (1108 + 1108) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 1108 * (11 : ZMod 75691781281) ^ 1108 := by rw [pow_add]
          _ = 3200596787 := by rw [factor_4_10]; decide
      have factor_4_12 : (11 : ZMod 75691781281) ^ 4432 = 60564121171 := by
        calc
          (11 : ZMod 75691781281) ^ 4432 = (11 : ZMod 75691781281) ^ (2216 + 2216) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 2216 * (11 : ZMod 75691781281) ^ 2216 := by rw [pow_add]
          _ = 60564121171 := by rw [factor_4_11]; decide
      have factor_4_13 : (11 : ZMod 75691781281) ^ 8865 = 58672312874 := by
        calc
          (11 : ZMod 75691781281) ^ 8865 = (11 : ZMod 75691781281) ^ (4432 + 4432 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = ((11 : ZMod 75691781281) ^ 4432 * (11 : ZMod 75691781281) ^ 4432) * (11 : ZMod 75691781281) := by rw [pow_succ, pow_add]
          _ = 58672312874 := by rw [factor_4_12]; decide
      have factor_4_14 : (11 : ZMod 75691781281) ^ 17730 = 63333302682 := by
        calc
          (11 : ZMod 75691781281) ^ 17730 = (11 : ZMod 75691781281) ^ (8865 + 8865) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 8865 * (11 : ZMod 75691781281) ^ 8865 := by rw [pow_add]
          _ = 63333302682 := by rw [factor_4_13]; decide
      have factor_4_15 : (11 : ZMod 75691781281) ^ 35460 = 29522839084 := by
        calc
          (11 : ZMod 75691781281) ^ 35460 = (11 : ZMod 75691781281) ^ (17730 + 17730) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 17730 * (11 : ZMod 75691781281) ^ 17730 := by rw [pow_add]
          _ = 29522839084 := by rw [factor_4_14]; decide
      have factor_4_16 : (11 : ZMod 75691781281) ^ 70920 = 9650180381 := by
        calc
          (11 : ZMod 75691781281) ^ 70920 = (11 : ZMod 75691781281) ^ (35460 + 35460) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 35460 * (11 : ZMod 75691781281) ^ 35460 := by rw [pow_add]
          _ = 9650180381 := by rw [factor_4_15]; decide
      have factor_4_17 : (11 : ZMod 75691781281) ^ 141840 = 22856498000 := by
        calc
          (11 : ZMod 75691781281) ^ 141840 = (11 : ZMod 75691781281) ^ (70920 + 70920) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 70920 * (11 : ZMod 75691781281) ^ 70920 := by rw [pow_add]
          _ = 22856498000 := by rw [factor_4_16]; decide
      have factor_4_18 : (11 : ZMod 75691781281) ^ 283680 = 31484337631 := by
        calc
          (11 : ZMod 75691781281) ^ 283680 = (11 : ZMod 75691781281) ^ (141840 + 141840) :=
            congrArg (fun n : ℕ => (11 : ZMod 75691781281) ^ n) (by norm_num)
          _ = (11 : ZMod 75691781281) ^ 141840 * (11 : ZMod 75691781281) ^ 141840 := by rw [pow_add]
          _ = 31484337631 := by rw [factor_4_17]; decide
      change (11 : ZMod 75691781281) ^ 283680 ≠ 1
      rw [factor_4_18]
      decide

#print axioms prime_lucas_75691781281

end TotientTailPeriodKiller
end Erdos249257
