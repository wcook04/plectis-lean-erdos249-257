import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_823412819 : Nat.Prime 823412819 := by
  apply lucas_primality 823412819 (2 : ZMod 823412819)
  ·
      have fermat_0 : (2 : ZMod 823412819) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 823412819) ^ 3 = 8 := by
        calc
          (2 : ZMod 823412819) ^ 3 = (2 : ZMod 823412819) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 1 * (2 : ZMod 823412819) ^ 1) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 823412819) ^ 6 = 64 := by
        calc
          (2 : ZMod 823412819) ^ 6 = (2 : ZMod 823412819) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 3 * (2 : ZMod 823412819) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 823412819) ^ 12 = 4096 := by
        calc
          (2 : ZMod 823412819) ^ 12 = (2 : ZMod 823412819) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 6 * (2 : ZMod 823412819) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 823412819) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 823412819) ^ 24 = (2 : ZMod 823412819) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 12 * (2 : ZMod 823412819) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 823412819) ^ 49 = 724153030 := by
        calc
          (2 : ZMod 823412819) ^ 49 = (2 : ZMod 823412819) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 24 * (2 : ZMod 823412819) ^ 24) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 724153030 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 823412819) ^ 98 = 797220971 := by
        calc
          (2 : ZMod 823412819) ^ 98 = (2 : ZMod 823412819) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 49 * (2 : ZMod 823412819) ^ 49 := by rw [pow_add]
          _ = 797220971 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 823412819) ^ 196 = 509523177 := by
        calc
          (2 : ZMod 823412819) ^ 196 = (2 : ZMod 823412819) ^ (98 + 98) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 98 * (2 : ZMod 823412819) ^ 98 := by rw [pow_add]
          _ = 509523177 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 823412819) ^ 392 = 673848017 := by
        calc
          (2 : ZMod 823412819) ^ 392 = (2 : ZMod 823412819) ^ (196 + 196) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 196 * (2 : ZMod 823412819) ^ 196 := by rw [pow_add]
          _ = 673848017 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 823412819) ^ 785 = 585472824 := by
        calc
          (2 : ZMod 823412819) ^ 785 = (2 : ZMod 823412819) ^ (392 + 392 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 392 * (2 : ZMod 823412819) ^ 392) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 585472824 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 823412819) ^ 1570 = 736911980 := by
        calc
          (2 : ZMod 823412819) ^ 1570 = (2 : ZMod 823412819) ^ (785 + 785) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 785 * (2 : ZMod 823412819) ^ 785 := by rw [pow_add]
          _ = 736911980 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 823412819) ^ 3141 = 87968666 := by
        calc
          (2 : ZMod 823412819) ^ 3141 = (2 : ZMod 823412819) ^ (1570 + 1570 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 1570 * (2 : ZMod 823412819) ^ 1570) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 87968666 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 823412819) ^ 6282 = 649849959 := by
        calc
          (2 : ZMod 823412819) ^ 6282 = (2 : ZMod 823412819) ^ (3141 + 3141) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 3141 * (2 : ZMod 823412819) ^ 3141 := by rw [pow_add]
          _ = 649849959 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 823412819) ^ 12564 = 789130362 := by
        calc
          (2 : ZMod 823412819) ^ 12564 = (2 : ZMod 823412819) ^ (6282 + 6282) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 6282 * (2 : ZMod 823412819) ^ 6282 := by rw [pow_add]
          _ = 789130362 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 823412819) ^ 25128 = 98536665 := by
        calc
          (2 : ZMod 823412819) ^ 25128 = (2 : ZMod 823412819) ^ (12564 + 12564) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 12564 * (2 : ZMod 823412819) ^ 12564 := by rw [pow_add]
          _ = 98536665 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 823412819) ^ 50257 = 715886140 := by
        calc
          (2 : ZMod 823412819) ^ 50257 = (2 : ZMod 823412819) ^ (25128 + 25128 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 25128 * (2 : ZMod 823412819) ^ 25128) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 715886140 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 823412819) ^ 100514 = 192029324 := by
        calc
          (2 : ZMod 823412819) ^ 100514 = (2 : ZMod 823412819) ^ (50257 + 50257) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 50257 * (2 : ZMod 823412819) ^ 50257 := by rw [pow_add]
          _ = 192029324 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 823412819) ^ 201028 = 230741159 := by
        calc
          (2 : ZMod 823412819) ^ 201028 = (2 : ZMod 823412819) ^ (100514 + 100514) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 100514 * (2 : ZMod 823412819) ^ 100514 := by rw [pow_add]
          _ = 230741159 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 823412819) ^ 402057 = 579011793 := by
        calc
          (2 : ZMod 823412819) ^ 402057 = (2 : ZMod 823412819) ^ (201028 + 201028 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 201028 * (2 : ZMod 823412819) ^ 201028) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 579011793 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 823412819) ^ 804114 = 301913372 := by
        calc
          (2 : ZMod 823412819) ^ 804114 = (2 : ZMod 823412819) ^ (402057 + 402057) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 402057 * (2 : ZMod 823412819) ^ 402057 := by rw [pow_add]
          _ = 301913372 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 823412819) ^ 1608228 = 406905044 := by
        calc
          (2 : ZMod 823412819) ^ 1608228 = (2 : ZMod 823412819) ^ (804114 + 804114) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 804114 * (2 : ZMod 823412819) ^ 804114 := by rw [pow_add]
          _ = 406905044 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 823412819) ^ 3216456 = 227824252 := by
        calc
          (2 : ZMod 823412819) ^ 3216456 = (2 : ZMod 823412819) ^ (1608228 + 1608228) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 1608228 * (2 : ZMod 823412819) ^ 1608228 := by rw [pow_add]
          _ = 227824252 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 823412819) ^ 6432912 = 174320260 := by
        calc
          (2 : ZMod 823412819) ^ 6432912 = (2 : ZMod 823412819) ^ (3216456 + 3216456) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 3216456 * (2 : ZMod 823412819) ^ 3216456 := by rw [pow_add]
          _ = 174320260 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 823412819) ^ 12865825 = 605230552 := by
        calc
          (2 : ZMod 823412819) ^ 12865825 = (2 : ZMod 823412819) ^ (6432912 + 6432912 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 6432912 * (2 : ZMod 823412819) ^ 6432912) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 605230552 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 823412819) ^ 25731650 = 733242205 := by
        calc
          (2 : ZMod 823412819) ^ 25731650 = (2 : ZMod 823412819) ^ (12865825 + 12865825) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 12865825 * (2 : ZMod 823412819) ^ 12865825 := by rw [pow_add]
          _ = 733242205 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 823412819) ^ 51463301 = 775619729 := by
        calc
          (2 : ZMod 823412819) ^ 51463301 = (2 : ZMod 823412819) ^ (25731650 + 25731650 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 25731650 * (2 : ZMod 823412819) ^ 25731650) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 775619729 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 823412819) ^ 102926602 = 178742159 := by
        calc
          (2 : ZMod 823412819) ^ 102926602 = (2 : ZMod 823412819) ^ (51463301 + 51463301) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 51463301 * (2 : ZMod 823412819) ^ 51463301 := by rw [pow_add]
          _ = 178742159 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 823412819) ^ 205853204 = 310461396 := by
        calc
          (2 : ZMod 823412819) ^ 205853204 = (2 : ZMod 823412819) ^ (102926602 + 102926602) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 102926602 * (2 : ZMod 823412819) ^ 102926602 := by rw [pow_add]
          _ = 310461396 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 823412819) ^ 411706409 = 823412818 := by
        calc
          (2 : ZMod 823412819) ^ 411706409 = (2 : ZMod 823412819) ^ (205853204 + 205853204 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 205853204 * (2 : ZMod 823412819) ^ 205853204) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 823412818 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 823412819) ^ 823412818 = 1 := by
        calc
          (2 : ZMod 823412819) ^ 823412818 = (2 : ZMod 823412819) ^ (411706409 + 411706409) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 411706409 * (2 : ZMod 823412819) ^ 411706409 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2887, 1), (142607, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2887, 1), (142607, 1)] : List FactorBlock).map factorBlockValue).prod = 823412819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 823412819) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 823412819) ^ 3 = 8 := by
        calc
          (2 : ZMod 823412819) ^ 3 = (2 : ZMod 823412819) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 1 * (2 : ZMod 823412819) ^ 1) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 823412819) ^ 6 = 64 := by
        calc
          (2 : ZMod 823412819) ^ 6 = (2 : ZMod 823412819) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 3 * (2 : ZMod 823412819) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 823412819) ^ 12 = 4096 := by
        calc
          (2 : ZMod 823412819) ^ 12 = (2 : ZMod 823412819) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 6 * (2 : ZMod 823412819) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 823412819) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 823412819) ^ 24 = (2 : ZMod 823412819) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 12 * (2 : ZMod 823412819) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 823412819) ^ 49 = 724153030 := by
        calc
          (2 : ZMod 823412819) ^ 49 = (2 : ZMod 823412819) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 24 * (2 : ZMod 823412819) ^ 24) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 724153030 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 823412819) ^ 98 = 797220971 := by
        calc
          (2 : ZMod 823412819) ^ 98 = (2 : ZMod 823412819) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 49 * (2 : ZMod 823412819) ^ 49 := by rw [pow_add]
          _ = 797220971 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 823412819) ^ 196 = 509523177 := by
        calc
          (2 : ZMod 823412819) ^ 196 = (2 : ZMod 823412819) ^ (98 + 98) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 98 * (2 : ZMod 823412819) ^ 98 := by rw [pow_add]
          _ = 509523177 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 823412819) ^ 392 = 673848017 := by
        calc
          (2 : ZMod 823412819) ^ 392 = (2 : ZMod 823412819) ^ (196 + 196) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 196 * (2 : ZMod 823412819) ^ 196 := by rw [pow_add]
          _ = 673848017 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 823412819) ^ 785 = 585472824 := by
        calc
          (2 : ZMod 823412819) ^ 785 = (2 : ZMod 823412819) ^ (392 + 392 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 392 * (2 : ZMod 823412819) ^ 392) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 585472824 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 823412819) ^ 1570 = 736911980 := by
        calc
          (2 : ZMod 823412819) ^ 1570 = (2 : ZMod 823412819) ^ (785 + 785) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 785 * (2 : ZMod 823412819) ^ 785 := by rw [pow_add]
          _ = 736911980 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 823412819) ^ 3141 = 87968666 := by
        calc
          (2 : ZMod 823412819) ^ 3141 = (2 : ZMod 823412819) ^ (1570 + 1570 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 1570 * (2 : ZMod 823412819) ^ 1570) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 87968666 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 823412819) ^ 6282 = 649849959 := by
        calc
          (2 : ZMod 823412819) ^ 6282 = (2 : ZMod 823412819) ^ (3141 + 3141) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 3141 * (2 : ZMod 823412819) ^ 3141 := by rw [pow_add]
          _ = 649849959 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 823412819) ^ 12564 = 789130362 := by
        calc
          (2 : ZMod 823412819) ^ 12564 = (2 : ZMod 823412819) ^ (6282 + 6282) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 6282 * (2 : ZMod 823412819) ^ 6282 := by rw [pow_add]
          _ = 789130362 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 823412819) ^ 25128 = 98536665 := by
        calc
          (2 : ZMod 823412819) ^ 25128 = (2 : ZMod 823412819) ^ (12564 + 12564) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 12564 * (2 : ZMod 823412819) ^ 12564 := by rw [pow_add]
          _ = 98536665 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 823412819) ^ 50257 = 715886140 := by
        calc
          (2 : ZMod 823412819) ^ 50257 = (2 : ZMod 823412819) ^ (25128 + 25128 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 25128 * (2 : ZMod 823412819) ^ 25128) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 715886140 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 823412819) ^ 100514 = 192029324 := by
        calc
          (2 : ZMod 823412819) ^ 100514 = (2 : ZMod 823412819) ^ (50257 + 50257) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 50257 * (2 : ZMod 823412819) ^ 50257 := by rw [pow_add]
          _ = 192029324 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 823412819) ^ 201028 = 230741159 := by
        calc
          (2 : ZMod 823412819) ^ 201028 = (2 : ZMod 823412819) ^ (100514 + 100514) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 100514 * (2 : ZMod 823412819) ^ 100514 := by rw [pow_add]
          _ = 230741159 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 823412819) ^ 402057 = 579011793 := by
        calc
          (2 : ZMod 823412819) ^ 402057 = (2 : ZMod 823412819) ^ (201028 + 201028 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 201028 * (2 : ZMod 823412819) ^ 201028) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 579011793 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 823412819) ^ 804114 = 301913372 := by
        calc
          (2 : ZMod 823412819) ^ 804114 = (2 : ZMod 823412819) ^ (402057 + 402057) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 402057 * (2 : ZMod 823412819) ^ 402057 := by rw [pow_add]
          _ = 301913372 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 823412819) ^ 1608228 = 406905044 := by
        calc
          (2 : ZMod 823412819) ^ 1608228 = (2 : ZMod 823412819) ^ (804114 + 804114) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 804114 * (2 : ZMod 823412819) ^ 804114 := by rw [pow_add]
          _ = 406905044 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 823412819) ^ 3216456 = 227824252 := by
        calc
          (2 : ZMod 823412819) ^ 3216456 = (2 : ZMod 823412819) ^ (1608228 + 1608228) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 1608228 * (2 : ZMod 823412819) ^ 1608228 := by rw [pow_add]
          _ = 227824252 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 823412819) ^ 6432912 = 174320260 := by
        calc
          (2 : ZMod 823412819) ^ 6432912 = (2 : ZMod 823412819) ^ (3216456 + 3216456) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 3216456 * (2 : ZMod 823412819) ^ 3216456 := by rw [pow_add]
          _ = 174320260 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 823412819) ^ 12865825 = 605230552 := by
        calc
          (2 : ZMod 823412819) ^ 12865825 = (2 : ZMod 823412819) ^ (6432912 + 6432912 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 6432912 * (2 : ZMod 823412819) ^ 6432912) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 605230552 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 823412819) ^ 25731650 = 733242205 := by
        calc
          (2 : ZMod 823412819) ^ 25731650 = (2 : ZMod 823412819) ^ (12865825 + 12865825) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 12865825 * (2 : ZMod 823412819) ^ 12865825 := by rw [pow_add]
          _ = 733242205 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 823412819) ^ 51463301 = 775619729 := by
        calc
          (2 : ZMod 823412819) ^ 51463301 = (2 : ZMod 823412819) ^ (25731650 + 25731650 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 25731650 * (2 : ZMod 823412819) ^ 25731650) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 775619729 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 823412819) ^ 102926602 = 178742159 := by
        calc
          (2 : ZMod 823412819) ^ 102926602 = (2 : ZMod 823412819) ^ (51463301 + 51463301) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 51463301 * (2 : ZMod 823412819) ^ 51463301 := by rw [pow_add]
          _ = 178742159 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 823412819) ^ 205853204 = 310461396 := by
        calc
          (2 : ZMod 823412819) ^ 205853204 = (2 : ZMod 823412819) ^ (102926602 + 102926602) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 102926602 * (2 : ZMod 823412819) ^ 102926602 := by rw [pow_add]
          _ = 310461396 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 823412819) ^ 411706409 = 823412818 := by
        calc
          (2 : ZMod 823412819) ^ 411706409 = (2 : ZMod 823412819) ^ (205853204 + 205853204 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 205853204 * (2 : ZMod 823412819) ^ 205853204) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 823412818 := by rw [factor_0_27]; decide
      change (2 : ZMod 823412819) ^ 411706409 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (2 : ZMod 823412819) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 823412819) ^ 2 = 4 := by
        calc
          (2 : ZMod 823412819) ^ 2 = (2 : ZMod 823412819) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 1 * (2 : ZMod 823412819) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 823412819) ^ 4 = 16 := by
        calc
          (2 : ZMod 823412819) ^ 4 = (2 : ZMod 823412819) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 2 * (2 : ZMod 823412819) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 823412819) ^ 8 = 256 := by
        calc
          (2 : ZMod 823412819) ^ 8 = (2 : ZMod 823412819) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 4 * (2 : ZMod 823412819) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 823412819) ^ 17 = 131072 := by
        calc
          (2 : ZMod 823412819) ^ 17 = (2 : ZMod 823412819) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 8 * (2 : ZMod 823412819) ^ 8) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 823412819) ^ 34 = 711612804 := by
        calc
          (2 : ZMod 823412819) ^ 34 = (2 : ZMod 823412819) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 17 * (2 : ZMod 823412819) ^ 17 := by rw [pow_add]
          _ = 711612804 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 823412819) ^ 69 = 418049593 := by
        calc
          (2 : ZMod 823412819) ^ 69 = (2 : ZMod 823412819) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 34 * (2 : ZMod 823412819) ^ 34) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 418049593 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 823412819) ^ 139 = 230734884 := by
        calc
          (2 : ZMod 823412819) ^ 139 = (2 : ZMod 823412819) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 69 * (2 : ZMod 823412819) ^ 69) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 230734884 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 823412819) ^ 278 = 58514085 := by
        calc
          (2 : ZMod 823412819) ^ 278 = (2 : ZMod 823412819) ^ (139 + 139) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 139 * (2 : ZMod 823412819) ^ 139 := by rw [pow_add]
          _ = 58514085 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 823412819) ^ 557 = 502181248 := by
        calc
          (2 : ZMod 823412819) ^ 557 = (2 : ZMod 823412819) ^ (278 + 278 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 278 * (2 : ZMod 823412819) ^ 278) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 502181248 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 823412819) ^ 1114 = 736055048 := by
        calc
          (2 : ZMod 823412819) ^ 1114 = (2 : ZMod 823412819) ^ (557 + 557) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 557 * (2 : ZMod 823412819) ^ 557 := by rw [pow_add]
          _ = 736055048 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 823412819) ^ 2228 = 28550269 := by
        calc
          (2 : ZMod 823412819) ^ 2228 = (2 : ZMod 823412819) ^ (1114 + 1114) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 1114 * (2 : ZMod 823412819) ^ 1114 := by rw [pow_add]
          _ = 28550269 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 823412819) ^ 4456 = 101710967 := by
        calc
          (2 : ZMod 823412819) ^ 4456 = (2 : ZMod 823412819) ^ (2228 + 2228) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 2228 * (2 : ZMod 823412819) ^ 2228 := by rw [pow_add]
          _ = 101710967 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 823412819) ^ 8912 = 116463780 := by
        calc
          (2 : ZMod 823412819) ^ 8912 = (2 : ZMod 823412819) ^ (4456 + 4456) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 4456 * (2 : ZMod 823412819) ^ 4456 := by rw [pow_add]
          _ = 116463780 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 823412819) ^ 17825 = 587335150 := by
        calc
          (2 : ZMod 823412819) ^ 17825 = (2 : ZMod 823412819) ^ (8912 + 8912 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 8912 * (2 : ZMod 823412819) ^ 8912) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 587335150 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 823412819) ^ 35651 = 48878547 := by
        calc
          (2 : ZMod 823412819) ^ 35651 = (2 : ZMod 823412819) ^ (17825 + 17825 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 17825 * (2 : ZMod 823412819) ^ 17825) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 48878547 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 823412819) ^ 71303 = 472233549 := by
        calc
          (2 : ZMod 823412819) ^ 71303 = (2 : ZMod 823412819) ^ (35651 + 35651 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 35651 * (2 : ZMod 823412819) ^ 35651) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 472233549 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 823412819) ^ 142607 = 664029445 := by
        calc
          (2 : ZMod 823412819) ^ 142607 = (2 : ZMod 823412819) ^ (71303 + 71303 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 71303 * (2 : ZMod 823412819) ^ 71303) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 664029445 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 823412819) ^ 285214 = 433424016 := by
        calc
          (2 : ZMod 823412819) ^ 285214 = (2 : ZMod 823412819) ^ (142607 + 142607) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 142607 * (2 : ZMod 823412819) ^ 142607 := by rw [pow_add]
          _ = 433424016 := by rw [factor_1_17]; decide
      change (2 : ZMod 823412819) ^ 285214 ≠ 1
      rw [factor_1_18]
      decide
    ·
      have factor_2_0 : (2 : ZMod 823412819) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 823412819) ^ 2 = 4 := by
        calc
          (2 : ZMod 823412819) ^ 2 = (2 : ZMod 823412819) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 1 * (2 : ZMod 823412819) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 823412819) ^ 5 = 32 := by
        calc
          (2 : ZMod 823412819) ^ 5 = (2 : ZMod 823412819) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 2 * (2 : ZMod 823412819) ^ 2) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 823412819) ^ 11 = 2048 := by
        calc
          (2 : ZMod 823412819) ^ 11 = (2 : ZMod 823412819) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 5 * (2 : ZMod 823412819) ^ 5) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 823412819) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 823412819) ^ 22 = (2 : ZMod 823412819) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 11 * (2 : ZMod 823412819) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 823412819) ^ 45 = 765745781 := by
        calc
          (2 : ZMod 823412819) ^ 45 = (2 : ZMod 823412819) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 22 * (2 : ZMod 823412819) ^ 22) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 765745781 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 823412819) ^ 90 = 385872447 := by
        calc
          (2 : ZMod 823412819) ^ 90 = (2 : ZMod 823412819) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 45 * (2 : ZMod 823412819) ^ 45 := by rw [pow_add]
          _ = 385872447 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 823412819) ^ 180 = 442835912 := by
        calc
          (2 : ZMod 823412819) ^ 180 = (2 : ZMod 823412819) ^ (90 + 90) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 90 * (2 : ZMod 823412819) ^ 90 := by rw [pow_add]
          _ = 442835912 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 823412819) ^ 360 = 404518276 := by
        calc
          (2 : ZMod 823412819) ^ 360 = (2 : ZMod 823412819) ^ (180 + 180) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 180 * (2 : ZMod 823412819) ^ 180 := by rw [pow_add]
          _ = 404518276 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 823412819) ^ 721 = 629349554 := by
        calc
          (2 : ZMod 823412819) ^ 721 = (2 : ZMod 823412819) ^ (360 + 360 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 360 * (2 : ZMod 823412819) ^ 360) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 629349554 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 823412819) ^ 1443 = 296822578 := by
        calc
          (2 : ZMod 823412819) ^ 1443 = (2 : ZMod 823412819) ^ (721 + 721 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 721 * (2 : ZMod 823412819) ^ 721) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 296822578 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 823412819) ^ 2887 = 510341934 := by
        calc
          (2 : ZMod 823412819) ^ 2887 = (2 : ZMod 823412819) ^ (1443 + 1443 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = ((2 : ZMod 823412819) ^ 1443 * (2 : ZMod 823412819) ^ 1443) * (2 : ZMod 823412819) := by rw [pow_succ, pow_add]
          _ = 510341934 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 823412819) ^ 5774 = 256199963 := by
        calc
          (2 : ZMod 823412819) ^ 5774 = (2 : ZMod 823412819) ^ (2887 + 2887) :=
            congrArg (fun n : ℕ => (2 : ZMod 823412819) ^ n) (by norm_num)
          _ = (2 : ZMod 823412819) ^ 2887 * (2 : ZMod 823412819) ^ 2887 := by rw [pow_add]
          _ = 256199963 := by rw [factor_2_11]; decide
      change (2 : ZMod 823412819) ^ 5774 ≠ 1
      rw [factor_2_12]
      decide

#print axioms prime_lucas_823412819

end TotientTailPeriodKiller
end Erdos249257
