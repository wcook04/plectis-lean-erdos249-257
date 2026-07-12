import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2641630853 : Nat.Prime 2641630853 := by
  apply lucas_primality 2641630853 (3 : ZMod 2641630853)
  ·
      have fermat_0 : (3 : ZMod 2641630853) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 2641630853) ^ 2 = 9 := by
        calc
          (3 : ZMod 2641630853) ^ 2 = (3 : ZMod 2641630853) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 1 * (3 : ZMod 2641630853) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 2641630853) ^ 4 = 81 := by
        calc
          (3 : ZMod 2641630853) ^ 4 = (3 : ZMod 2641630853) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 2 * (3 : ZMod 2641630853) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 2641630853) ^ 9 = 19683 := by
        calc
          (3 : ZMod 2641630853) ^ 9 = (3 : ZMod 2641630853) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 4 * (3 : ZMod 2641630853) ^ 4) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 2641630853) ^ 19 = 1162261467 := by
        calc
          (3 : ZMod 2641630853) ^ 19 = (3 : ZMod 2641630853) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 9 * (3 : ZMod 2641630853) ^ 9) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1162261467 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 2641630853) ^ 39 = 86717586 := by
        calc
          (3 : ZMod 2641630853) ^ 39 = (3 : ZMod 2641630853) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 19 * (3 : ZMod 2641630853) ^ 19) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 86717586 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 2641630853) ^ 78 = 1247539737 := by
        calc
          (3 : ZMod 2641630853) ^ 78 = (3 : ZMod 2641630853) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 39 * (3 : ZMod 2641630853) ^ 39 := by rw [pow_add]
          _ = 1247539737 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 2641630853) ^ 157 = 2557936724 := by
        calc
          (3 : ZMod 2641630853) ^ 157 = (3 : ZMod 2641630853) ^ (78 + 78 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 78 * (3 : ZMod 2641630853) ^ 78) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 2557936724 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 2641630853) ^ 314 = 361402661 := by
        calc
          (3 : ZMod 2641630853) ^ 314 = (3 : ZMod 2641630853) ^ (157 + 157) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 157 * (3 : ZMod 2641630853) ^ 157 := by rw [pow_add]
          _ = 361402661 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 2641630853) ^ 629 = 1817641324 := by
        calc
          (3 : ZMod 2641630853) ^ 629 = (3 : ZMod 2641630853) ^ (314 + 314 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 314 * (3 : ZMod 2641630853) ^ 314) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1817641324 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 2641630853) ^ 1259 = 349915717 := by
        calc
          (3 : ZMod 2641630853) ^ 1259 = (3 : ZMod 2641630853) ^ (629 + 629 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 629 * (3 : ZMod 2641630853) ^ 629) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 349915717 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 2641630853) ^ 2519 = 1233918084 := by
        calc
          (3 : ZMod 2641630853) ^ 2519 = (3 : ZMod 2641630853) ^ (1259 + 1259 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 1259 * (3 : ZMod 2641630853) ^ 1259) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1233918084 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 2641630853) ^ 5038 = 772129592 := by
        calc
          (3 : ZMod 2641630853) ^ 5038 = (3 : ZMod 2641630853) ^ (2519 + 2519) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 2519 * (3 : ZMod 2641630853) ^ 2519 := by rw [pow_add]
          _ = 772129592 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 2641630853) ^ 10077 = 784386087 := by
        calc
          (3 : ZMod 2641630853) ^ 10077 = (3 : ZMod 2641630853) ^ (5038 + 5038 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 5038 * (3 : ZMod 2641630853) ^ 5038) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 784386087 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 2641630853) ^ 20154 = 2105641026 := by
        calc
          (3 : ZMod 2641630853) ^ 20154 = (3 : ZMod 2641630853) ^ (10077 + 10077) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 10077 * (3 : ZMod 2641630853) ^ 10077 := by rw [pow_add]
          _ = 2105641026 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 2641630853) ^ 40308 = 2046971492 := by
        calc
          (3 : ZMod 2641630853) ^ 40308 = (3 : ZMod 2641630853) ^ (20154 + 20154) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 20154 * (3 : ZMod 2641630853) ^ 20154 := by rw [pow_add]
          _ = 2046971492 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 2641630853) ^ 80616 = 2342121075 := by
        calc
          (3 : ZMod 2641630853) ^ 80616 = (3 : ZMod 2641630853) ^ (40308 + 40308) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 40308 * (3 : ZMod 2641630853) ^ 40308 := by rw [pow_add]
          _ = 2342121075 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 2641630853) ^ 161232 = 499876660 := by
        calc
          (3 : ZMod 2641630853) ^ 161232 = (3 : ZMod 2641630853) ^ (80616 + 80616) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 80616 * (3 : ZMod 2641630853) ^ 80616 := by rw [pow_add]
          _ = 499876660 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 2641630853) ^ 322464 = 2417702287 := by
        calc
          (3 : ZMod 2641630853) ^ 322464 = (3 : ZMod 2641630853) ^ (161232 + 161232) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 161232 * (3 : ZMod 2641630853) ^ 161232 := by rw [pow_add]
          _ = 2417702287 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 2641630853) ^ 644929 = 1530503442 := by
        calc
          (3 : ZMod 2641630853) ^ 644929 = (3 : ZMod 2641630853) ^ (322464 + 322464 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 322464 * (3 : ZMod 2641630853) ^ 322464) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1530503442 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 2641630853) ^ 1289858 = 2582071282 := by
        calc
          (3 : ZMod 2641630853) ^ 1289858 = (3 : ZMod 2641630853) ^ (644929 + 644929) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 644929 * (3 : ZMod 2641630853) ^ 644929 := by rw [pow_add]
          _ = 2582071282 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 2641630853) ^ 2579717 = 988071677 := by
        calc
          (3 : ZMod 2641630853) ^ 2579717 = (3 : ZMod 2641630853) ^ (1289858 + 1289858 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 1289858 * (3 : ZMod 2641630853) ^ 1289858) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 988071677 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 2641630853) ^ 5159435 = 951299688 := by
        calc
          (3 : ZMod 2641630853) ^ 5159435 = (3 : ZMod 2641630853) ^ (2579717 + 2579717 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 2579717 * (3 : ZMod 2641630853) ^ 2579717) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 951299688 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 2641630853) ^ 10318870 = 2109380935 := by
        calc
          (3 : ZMod 2641630853) ^ 10318870 = (3 : ZMod 2641630853) ^ (5159435 + 5159435) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 5159435 * (3 : ZMod 2641630853) ^ 5159435 := by rw [pow_add]
          _ = 2109380935 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 2641630853) ^ 20637741 = 1741134573 := by
        calc
          (3 : ZMod 2641630853) ^ 20637741 = (3 : ZMod 2641630853) ^ (10318870 + 10318870 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 10318870 * (3 : ZMod 2641630853) ^ 10318870) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1741134573 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 2641630853) ^ 41275482 = 2050001193 := by
        calc
          (3 : ZMod 2641630853) ^ 41275482 = (3 : ZMod 2641630853) ^ (20637741 + 20637741) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 20637741 * (3 : ZMod 2641630853) ^ 20637741 := by rw [pow_add]
          _ = 2050001193 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 2641630853) ^ 82550964 = 1223896887 := by
        calc
          (3 : ZMod 2641630853) ^ 82550964 = (3 : ZMod 2641630853) ^ (41275482 + 41275482) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 41275482 * (3 : ZMod 2641630853) ^ 41275482 := by rw [pow_add]
          _ = 1223896887 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 2641630853) ^ 165101928 = 1835858945 := by
        calc
          (3 : ZMod 2641630853) ^ 165101928 = (3 : ZMod 2641630853) ^ (82550964 + 82550964) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 82550964 * (3 : ZMod 2641630853) ^ 82550964 := by rw [pow_add]
          _ = 1835858945 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 2641630853) ^ 330203856 = 2326279249 := by
        calc
          (3 : ZMod 2641630853) ^ 330203856 = (3 : ZMod 2641630853) ^ (165101928 + 165101928) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 165101928 * (3 : ZMod 2641630853) ^ 165101928 := by rw [pow_add]
          _ = 2326279249 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 2641630853) ^ 660407713 = 2093469785 := by
        calc
          (3 : ZMod 2641630853) ^ 660407713 = (3 : ZMod 2641630853) ^ (330203856 + 330203856 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 330203856 * (3 : ZMod 2641630853) ^ 330203856) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 2093469785 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 2641630853) ^ 1320815426 = 2641630852 := by
        calc
          (3 : ZMod 2641630853) ^ 1320815426 = (3 : ZMod 2641630853) ^ (660407713 + 660407713) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 660407713 * (3 : ZMod 2641630853) ^ 660407713 := by rw [pow_add]
          _ = 2641630852 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 2641630853) ^ 2641630852 = 1 := by
        calc
          (3 : ZMod 2641630853) ^ 2641630852 = (3 : ZMod 2641630853) ^ (1320815426 + 1320815426) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 1320815426 * (3 : ZMod 2641630853) ^ 1320815426 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (73, 1), (1292383, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (73, 1), (1292383, 1)] : List FactorBlock).map factorBlockValue).prod = 2641630853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 2641630853) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 2641630853) ^ 2 = 9 := by
        calc
          (3 : ZMod 2641630853) ^ 2 = (3 : ZMod 2641630853) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 1 * (3 : ZMod 2641630853) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 2641630853) ^ 4 = 81 := by
        calc
          (3 : ZMod 2641630853) ^ 4 = (3 : ZMod 2641630853) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 2 * (3 : ZMod 2641630853) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 2641630853) ^ 9 = 19683 := by
        calc
          (3 : ZMod 2641630853) ^ 9 = (3 : ZMod 2641630853) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 4 * (3 : ZMod 2641630853) ^ 4) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 2641630853) ^ 19 = 1162261467 := by
        calc
          (3 : ZMod 2641630853) ^ 19 = (3 : ZMod 2641630853) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 9 * (3 : ZMod 2641630853) ^ 9) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1162261467 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 2641630853) ^ 39 = 86717586 := by
        calc
          (3 : ZMod 2641630853) ^ 39 = (3 : ZMod 2641630853) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 19 * (3 : ZMod 2641630853) ^ 19) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 86717586 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 2641630853) ^ 78 = 1247539737 := by
        calc
          (3 : ZMod 2641630853) ^ 78 = (3 : ZMod 2641630853) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 39 * (3 : ZMod 2641630853) ^ 39 := by rw [pow_add]
          _ = 1247539737 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 2641630853) ^ 157 = 2557936724 := by
        calc
          (3 : ZMod 2641630853) ^ 157 = (3 : ZMod 2641630853) ^ (78 + 78 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 78 * (3 : ZMod 2641630853) ^ 78) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 2557936724 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 2641630853) ^ 314 = 361402661 := by
        calc
          (3 : ZMod 2641630853) ^ 314 = (3 : ZMod 2641630853) ^ (157 + 157) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 157 * (3 : ZMod 2641630853) ^ 157 := by rw [pow_add]
          _ = 361402661 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 2641630853) ^ 629 = 1817641324 := by
        calc
          (3 : ZMod 2641630853) ^ 629 = (3 : ZMod 2641630853) ^ (314 + 314 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 314 * (3 : ZMod 2641630853) ^ 314) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1817641324 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 2641630853) ^ 1259 = 349915717 := by
        calc
          (3 : ZMod 2641630853) ^ 1259 = (3 : ZMod 2641630853) ^ (629 + 629 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 629 * (3 : ZMod 2641630853) ^ 629) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 349915717 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 2641630853) ^ 2519 = 1233918084 := by
        calc
          (3 : ZMod 2641630853) ^ 2519 = (3 : ZMod 2641630853) ^ (1259 + 1259 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 1259 * (3 : ZMod 2641630853) ^ 1259) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1233918084 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 2641630853) ^ 5038 = 772129592 := by
        calc
          (3 : ZMod 2641630853) ^ 5038 = (3 : ZMod 2641630853) ^ (2519 + 2519) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 2519 * (3 : ZMod 2641630853) ^ 2519 := by rw [pow_add]
          _ = 772129592 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 2641630853) ^ 10077 = 784386087 := by
        calc
          (3 : ZMod 2641630853) ^ 10077 = (3 : ZMod 2641630853) ^ (5038 + 5038 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 5038 * (3 : ZMod 2641630853) ^ 5038) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 784386087 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 2641630853) ^ 20154 = 2105641026 := by
        calc
          (3 : ZMod 2641630853) ^ 20154 = (3 : ZMod 2641630853) ^ (10077 + 10077) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 10077 * (3 : ZMod 2641630853) ^ 10077 := by rw [pow_add]
          _ = 2105641026 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 2641630853) ^ 40308 = 2046971492 := by
        calc
          (3 : ZMod 2641630853) ^ 40308 = (3 : ZMod 2641630853) ^ (20154 + 20154) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 20154 * (3 : ZMod 2641630853) ^ 20154 := by rw [pow_add]
          _ = 2046971492 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 2641630853) ^ 80616 = 2342121075 := by
        calc
          (3 : ZMod 2641630853) ^ 80616 = (3 : ZMod 2641630853) ^ (40308 + 40308) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 40308 * (3 : ZMod 2641630853) ^ 40308 := by rw [pow_add]
          _ = 2342121075 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 2641630853) ^ 161232 = 499876660 := by
        calc
          (3 : ZMod 2641630853) ^ 161232 = (3 : ZMod 2641630853) ^ (80616 + 80616) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 80616 * (3 : ZMod 2641630853) ^ 80616 := by rw [pow_add]
          _ = 499876660 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 2641630853) ^ 322464 = 2417702287 := by
        calc
          (3 : ZMod 2641630853) ^ 322464 = (3 : ZMod 2641630853) ^ (161232 + 161232) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 161232 * (3 : ZMod 2641630853) ^ 161232 := by rw [pow_add]
          _ = 2417702287 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 2641630853) ^ 644929 = 1530503442 := by
        calc
          (3 : ZMod 2641630853) ^ 644929 = (3 : ZMod 2641630853) ^ (322464 + 322464 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 322464 * (3 : ZMod 2641630853) ^ 322464) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1530503442 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 2641630853) ^ 1289858 = 2582071282 := by
        calc
          (3 : ZMod 2641630853) ^ 1289858 = (3 : ZMod 2641630853) ^ (644929 + 644929) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 644929 * (3 : ZMod 2641630853) ^ 644929 := by rw [pow_add]
          _ = 2582071282 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 2641630853) ^ 2579717 = 988071677 := by
        calc
          (3 : ZMod 2641630853) ^ 2579717 = (3 : ZMod 2641630853) ^ (1289858 + 1289858 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 1289858 * (3 : ZMod 2641630853) ^ 1289858) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 988071677 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 2641630853) ^ 5159435 = 951299688 := by
        calc
          (3 : ZMod 2641630853) ^ 5159435 = (3 : ZMod 2641630853) ^ (2579717 + 2579717 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 2579717 * (3 : ZMod 2641630853) ^ 2579717) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 951299688 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 2641630853) ^ 10318870 = 2109380935 := by
        calc
          (3 : ZMod 2641630853) ^ 10318870 = (3 : ZMod 2641630853) ^ (5159435 + 5159435) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 5159435 * (3 : ZMod 2641630853) ^ 5159435 := by rw [pow_add]
          _ = 2109380935 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 2641630853) ^ 20637741 = 1741134573 := by
        calc
          (3 : ZMod 2641630853) ^ 20637741 = (3 : ZMod 2641630853) ^ (10318870 + 10318870 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 10318870 * (3 : ZMod 2641630853) ^ 10318870) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1741134573 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 2641630853) ^ 41275482 = 2050001193 := by
        calc
          (3 : ZMod 2641630853) ^ 41275482 = (3 : ZMod 2641630853) ^ (20637741 + 20637741) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 20637741 * (3 : ZMod 2641630853) ^ 20637741 := by rw [pow_add]
          _ = 2050001193 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 2641630853) ^ 82550964 = 1223896887 := by
        calc
          (3 : ZMod 2641630853) ^ 82550964 = (3 : ZMod 2641630853) ^ (41275482 + 41275482) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 41275482 * (3 : ZMod 2641630853) ^ 41275482 := by rw [pow_add]
          _ = 1223896887 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 2641630853) ^ 165101928 = 1835858945 := by
        calc
          (3 : ZMod 2641630853) ^ 165101928 = (3 : ZMod 2641630853) ^ (82550964 + 82550964) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 82550964 * (3 : ZMod 2641630853) ^ 82550964 := by rw [pow_add]
          _ = 1835858945 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 2641630853) ^ 330203856 = 2326279249 := by
        calc
          (3 : ZMod 2641630853) ^ 330203856 = (3 : ZMod 2641630853) ^ (165101928 + 165101928) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 165101928 * (3 : ZMod 2641630853) ^ 165101928 := by rw [pow_add]
          _ = 2326279249 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 2641630853) ^ 660407713 = 2093469785 := by
        calc
          (3 : ZMod 2641630853) ^ 660407713 = (3 : ZMod 2641630853) ^ (330203856 + 330203856 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 330203856 * (3 : ZMod 2641630853) ^ 330203856) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 2093469785 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 2641630853) ^ 1320815426 = 2641630852 := by
        calc
          (3 : ZMod 2641630853) ^ 1320815426 = (3 : ZMod 2641630853) ^ (660407713 + 660407713) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 660407713 * (3 : ZMod 2641630853) ^ 660407713 := by rw [pow_add]
          _ = 2641630852 := by rw [factor_0_29]; decide
      change (3 : ZMod 2641630853) ^ 1320815426 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (3 : ZMod 2641630853) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 2641630853) ^ 2 = 9 := by
        calc
          (3 : ZMod 2641630853) ^ 2 = (3 : ZMod 2641630853) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 1 * (3 : ZMod 2641630853) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 2641630853) ^ 5 = 243 := by
        calc
          (3 : ZMod 2641630853) ^ 5 = (3 : ZMod 2641630853) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 2 * (3 : ZMod 2641630853) ^ 2) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 2641630853) ^ 11 = 177147 := by
        calc
          (3 : ZMod 2641630853) ^ 11 = (3 : ZMod 2641630853) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 5 * (3 : ZMod 2641630853) ^ 5) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 2641630853) ^ 22 = 2323120226 := by
        calc
          (3 : ZMod 2641630853) ^ 22 = (3 : ZMod 2641630853) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 11 * (3 : ZMod 2641630853) ^ 11 := by rw [pow_add]
          _ = 2323120226 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 2641630853) ^ 44 = 2580957427 := by
        calc
          (3 : ZMod 2641630853) ^ 44 = (3 : ZMod 2641630853) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 22 * (3 : ZMod 2641630853) ^ 22 := by rw [pow_add]
          _ = 2580957427 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 2641630853) ^ 89 = 1726259212 := by
        calc
          (3 : ZMod 2641630853) ^ 89 = (3 : ZMod 2641630853) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 44 * (3 : ZMod 2641630853) ^ 44) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1726259212 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 2641630853) ^ 179 = 1210176807 := by
        calc
          (3 : ZMod 2641630853) ^ 179 = (3 : ZMod 2641630853) ^ (89 + 89 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 89 * (3 : ZMod 2641630853) ^ 89) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1210176807 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 2641630853) ^ 359 = 2483099964 := by
        calc
          (3 : ZMod 2641630853) ^ 359 = (3 : ZMod 2641630853) ^ (179 + 179 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 179 * (3 : ZMod 2641630853) ^ 179) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 2483099964 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 2641630853) ^ 719 = 177444639 := by
        calc
          (3 : ZMod 2641630853) ^ 719 = (3 : ZMod 2641630853) ^ (359 + 359 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 359 * (3 : ZMod 2641630853) ^ 359) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 177444639 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 2641630853) ^ 1439 = 1784520102 := by
        calc
          (3 : ZMod 2641630853) ^ 1439 = (3 : ZMod 2641630853) ^ (719 + 719 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 719 * (3 : ZMod 2641630853) ^ 719) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1784520102 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 2641630853) ^ 2879 = 1375943828 := by
        calc
          (3 : ZMod 2641630853) ^ 2879 = (3 : ZMod 2641630853) ^ (1439 + 1439 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 1439 * (3 : ZMod 2641630853) ^ 1439) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1375943828 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 2641630853) ^ 5758 = 1811039755 := by
        calc
          (3 : ZMod 2641630853) ^ 5758 = (3 : ZMod 2641630853) ^ (2879 + 2879) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 2879 * (3 : ZMod 2641630853) ^ 2879 := by rw [pow_add]
          _ = 1811039755 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 2641630853) ^ 11516 = 2590933313 := by
        calc
          (3 : ZMod 2641630853) ^ 11516 = (3 : ZMod 2641630853) ^ (5758 + 5758) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 5758 * (3 : ZMod 2641630853) ^ 5758 := by rw [pow_add]
          _ = 2590933313 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 2641630853) ^ 23033 = 1990192628 := by
        calc
          (3 : ZMod 2641630853) ^ 23033 = (3 : ZMod 2641630853) ^ (11516 + 11516 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 11516 * (3 : ZMod 2641630853) ^ 11516) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1990192628 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 2641630853) ^ 46066 = 1347144558 := by
        calc
          (3 : ZMod 2641630853) ^ 46066 = (3 : ZMod 2641630853) ^ (23033 + 23033) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 23033 * (3 : ZMod 2641630853) ^ 23033 := by rw [pow_add]
          _ = 1347144558 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 2641630853) ^ 92132 = 453430613 := by
        calc
          (3 : ZMod 2641630853) ^ 92132 = (3 : ZMod 2641630853) ^ (46066 + 46066) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 46066 * (3 : ZMod 2641630853) ^ 46066 := by rw [pow_add]
          _ = 453430613 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 2641630853) ^ 184265 = 423153198 := by
        calc
          (3 : ZMod 2641630853) ^ 184265 = (3 : ZMod 2641630853) ^ (92132 + 92132 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 92132 * (3 : ZMod 2641630853) ^ 92132) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 423153198 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 2641630853) ^ 368531 = 2020400577 := by
        calc
          (3 : ZMod 2641630853) ^ 368531 = (3 : ZMod 2641630853) ^ (184265 + 184265 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 184265 * (3 : ZMod 2641630853) ^ 184265) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 2020400577 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 2641630853) ^ 737062 = 1347818603 := by
        calc
          (3 : ZMod 2641630853) ^ 737062 = (3 : ZMod 2641630853) ^ (368531 + 368531) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 368531 * (3 : ZMod 2641630853) ^ 368531 := by rw [pow_add]
          _ = 1347818603 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 2641630853) ^ 1474124 = 1516328849 := by
        calc
          (3 : ZMod 2641630853) ^ 1474124 = (3 : ZMod 2641630853) ^ (737062 + 737062) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 737062 * (3 : ZMod 2641630853) ^ 737062 := by rw [pow_add]
          _ = 1516328849 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 2641630853) ^ 2948248 = 355910945 := by
        calc
          (3 : ZMod 2641630853) ^ 2948248 = (3 : ZMod 2641630853) ^ (1474124 + 1474124) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 1474124 * (3 : ZMod 2641630853) ^ 1474124 := by rw [pow_add]
          _ = 355910945 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 2641630853) ^ 5896497 = 2093658618 := by
        calc
          (3 : ZMod 2641630853) ^ 5896497 = (3 : ZMod 2641630853) ^ (2948248 + 2948248 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 2948248 * (3 : ZMod 2641630853) ^ 2948248) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 2093658618 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 2641630853) ^ 11792994 = 1487112268 := by
        calc
          (3 : ZMod 2641630853) ^ 11792994 = (3 : ZMod 2641630853) ^ (5896497 + 5896497) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 5896497 * (3 : ZMod 2641630853) ^ 5896497 := by rw [pow_add]
          _ = 1487112268 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 2641630853) ^ 23585989 = 2039690855 := by
        calc
          (3 : ZMod 2641630853) ^ 23585989 = (3 : ZMod 2641630853) ^ (11792994 + 11792994 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 11792994 * (3 : ZMod 2641630853) ^ 11792994) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 2039690855 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 2641630853) ^ 47171979 = 156694133 := by
        calc
          (3 : ZMod 2641630853) ^ 47171979 = (3 : ZMod 2641630853) ^ (23585989 + 23585989 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 23585989 * (3 : ZMod 2641630853) ^ 23585989) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 156694133 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 2641630853) ^ 94343959 = 1135369510 := by
        calc
          (3 : ZMod 2641630853) ^ 94343959 = (3 : ZMod 2641630853) ^ (47171979 + 47171979 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 47171979 * (3 : ZMod 2641630853) ^ 47171979) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1135369510 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 2641630853) ^ 188687918 = 2436210080 := by
        calc
          (3 : ZMod 2641630853) ^ 188687918 = (3 : ZMod 2641630853) ^ (94343959 + 94343959) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 94343959 * (3 : ZMod 2641630853) ^ 94343959 := by rw [pow_add]
          _ = 2436210080 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 2641630853) ^ 377375836 = 79594258 := by
        calc
          (3 : ZMod 2641630853) ^ 377375836 = (3 : ZMod 2641630853) ^ (188687918 + 188687918) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 188687918 * (3 : ZMod 2641630853) ^ 188687918 := by rw [pow_add]
          _ = 79594258 := by rw [factor_1_27]; decide
      change (3 : ZMod 2641630853) ^ 377375836 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (3 : ZMod 2641630853) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 2641630853) ^ 2 = 9 := by
        calc
          (3 : ZMod 2641630853) ^ 2 = (3 : ZMod 2641630853) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 1 * (3 : ZMod 2641630853) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 2641630853) ^ 4 = 81 := by
        calc
          (3 : ZMod 2641630853) ^ 4 = (3 : ZMod 2641630853) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 2 * (3 : ZMod 2641630853) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 2641630853) ^ 8 = 6561 := by
        calc
          (3 : ZMod 2641630853) ^ 8 = (3 : ZMod 2641630853) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 4 * (3 : ZMod 2641630853) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 2641630853) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 2641630853) ^ 17 = (3 : ZMod 2641630853) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 8 * (3 : ZMod 2641630853) ^ 8) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 2641630853) ^ 34 = 815675027 := by
        calc
          (3 : ZMod 2641630853) ^ 34 = (3 : ZMod 2641630853) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 17 * (3 : ZMod 2641630853) ^ 17 := by rw [pow_add]
          _ = 815675027 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 2641630853) ^ 69 = 1300143556 := by
        calc
          (3 : ZMod 2641630853) ^ 69 = (3 : ZMod 2641630853) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 34 * (3 : ZMod 2641630853) ^ 34) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1300143556 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 2641630853) ^ 138 = 2154625512 := by
        calc
          (3 : ZMod 2641630853) ^ 138 = (3 : ZMod 2641630853) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 69 * (3 : ZMod 2641630853) ^ 69 := by rw [pow_add]
          _ = 2154625512 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 2641630853) ^ 276 = 1521544884 := by
        calc
          (3 : ZMod 2641630853) ^ 276 = (3 : ZMod 2641630853) ^ (138 + 138) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 138 * (3 : ZMod 2641630853) ^ 138 := by rw [pow_add]
          _ = 1521544884 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 2641630853) ^ 552 = 2465473692 := by
        calc
          (3 : ZMod 2641630853) ^ 552 = (3 : ZMod 2641630853) ^ (276 + 276) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 276 * (3 : ZMod 2641630853) ^ 276 := by rw [pow_add]
          _ = 2465473692 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 2641630853) ^ 1104 = 2076154801 := by
        calc
          (3 : ZMod 2641630853) ^ 1104 = (3 : ZMod 2641630853) ^ (552 + 552) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 552 * (3 : ZMod 2641630853) ^ 552 := by rw [pow_add]
          _ = 2076154801 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 2641630853) ^ 2208 = 728454902 := by
        calc
          (3 : ZMod 2641630853) ^ 2208 = (3 : ZMod 2641630853) ^ (1104 + 1104) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 1104 * (3 : ZMod 2641630853) ^ 1104 := by rw [pow_add]
          _ = 728454902 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 2641630853) ^ 4417 = 984897332 := by
        calc
          (3 : ZMod 2641630853) ^ 4417 = (3 : ZMod 2641630853) ^ (2208 + 2208 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 2208 * (3 : ZMod 2641630853) ^ 2208) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 984897332 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 2641630853) ^ 8834 = 99752311 := by
        calc
          (3 : ZMod 2641630853) ^ 8834 = (3 : ZMod 2641630853) ^ (4417 + 4417) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 4417 * (3 : ZMod 2641630853) ^ 4417 := by rw [pow_add]
          _ = 99752311 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 2641630853) ^ 17669 = 826093667 := by
        calc
          (3 : ZMod 2641630853) ^ 17669 = (3 : ZMod 2641630853) ^ (8834 + 8834 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 8834 * (3 : ZMod 2641630853) ^ 8834) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 826093667 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 2641630853) ^ 35338 = 16084365 := by
        calc
          (3 : ZMod 2641630853) ^ 35338 = (3 : ZMod 2641630853) ^ (17669 + 17669) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 17669 * (3 : ZMod 2641630853) ^ 17669 := by rw [pow_add]
          _ = 16084365 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 2641630853) ^ 70677 = 1322855716 := by
        calc
          (3 : ZMod 2641630853) ^ 70677 = (3 : ZMod 2641630853) ^ (35338 + 35338 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 35338 * (3 : ZMod 2641630853) ^ 35338) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1322855716 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 2641630853) ^ 141354 = 1552242622 := by
        calc
          (3 : ZMod 2641630853) ^ 141354 = (3 : ZMod 2641630853) ^ (70677 + 70677) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 70677 * (3 : ZMod 2641630853) ^ 70677 := by rw [pow_add]
          _ = 1552242622 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 2641630853) ^ 282708 = 1013290548 := by
        calc
          (3 : ZMod 2641630853) ^ 282708 = (3 : ZMod 2641630853) ^ (141354 + 141354) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 141354 * (3 : ZMod 2641630853) ^ 141354 := by rw [pow_add]
          _ = 1013290548 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 2641630853) ^ 565417 = 2218277628 := by
        calc
          (3 : ZMod 2641630853) ^ 565417 = (3 : ZMod 2641630853) ^ (282708 + 282708 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 282708 * (3 : ZMod 2641630853) ^ 282708) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 2218277628 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 2641630853) ^ 1130835 = 2036343205 := by
        calc
          (3 : ZMod 2641630853) ^ 1130835 = (3 : ZMod 2641630853) ^ (565417 + 565417 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 565417 * (3 : ZMod 2641630853) ^ 565417) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 2036343205 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 2641630853) ^ 2261670 = 1874693726 := by
        calc
          (3 : ZMod 2641630853) ^ 2261670 = (3 : ZMod 2641630853) ^ (1130835 + 1130835) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 1130835 * (3 : ZMod 2641630853) ^ 1130835 := by rw [pow_add]
          _ = 1874693726 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 2641630853) ^ 4523340 = 1662334296 := by
        calc
          (3 : ZMod 2641630853) ^ 4523340 = (3 : ZMod 2641630853) ^ (2261670 + 2261670) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 2261670 * (3 : ZMod 2641630853) ^ 2261670 := by rw [pow_add]
          _ = 1662334296 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 2641630853) ^ 9046681 = 1077799092 := by
        calc
          (3 : ZMod 2641630853) ^ 9046681 = (3 : ZMod 2641630853) ^ (4523340 + 4523340 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 4523340 * (3 : ZMod 2641630853) ^ 4523340) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1077799092 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 2641630853) ^ 18093362 = 2190704604 := by
        calc
          (3 : ZMod 2641630853) ^ 18093362 = (3 : ZMod 2641630853) ^ (9046681 + 9046681) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 9046681 * (3 : ZMod 2641630853) ^ 9046681 := by rw [pow_add]
          _ = 2190704604 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 2641630853) ^ 36186724 = 567356790 := by
        calc
          (3 : ZMod 2641630853) ^ 36186724 = (3 : ZMod 2641630853) ^ (18093362 + 18093362) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 18093362 * (3 : ZMod 2641630853) ^ 18093362 := by rw [pow_add]
          _ = 567356790 := by rw [factor_2_24]; decide
      change (3 : ZMod 2641630853) ^ 36186724 ≠ 1
      rw [factor_2_25]
      decide
    ·
      have factor_3_0 : (3 : ZMod 2641630853) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 2641630853) ^ 3 = 27 := by
        calc
          (3 : ZMod 2641630853) ^ 3 = (3 : ZMod 2641630853) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 1 * (3 : ZMod 2641630853) ^ 1) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 2641630853) ^ 7 = 2187 := by
        calc
          (3 : ZMod 2641630853) ^ 7 = (3 : ZMod 2641630853) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 3 * (3 : ZMod 2641630853) ^ 3) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 2641630853) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 2641630853) ^ 15 = (3 : ZMod 2641630853) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 7 * (3 : ZMod 2641630853) ^ 7) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 2641630853) ^ 31 = 1986973781 := by
        calc
          (3 : ZMod 2641630853) ^ 31 = (3 : ZMod 2641630853) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 15 * (3 : ZMod 2641630853) ^ 15) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1986973781 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 2641630853) ^ 63 = 701145265 := by
        calc
          (3 : ZMod 2641630853) ^ 63 = (3 : ZMod 2641630853) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 31 * (3 : ZMod 2641630853) ^ 31) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 701145265 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 2641630853) ^ 127 = 1167851981 := by
        calc
          (3 : ZMod 2641630853) ^ 127 = (3 : ZMod 2641630853) ^ (63 + 63 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 63 * (3 : ZMod 2641630853) ^ 63) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 1167851981 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 2641630853) ^ 255 = 912615888 := by
        calc
          (3 : ZMod 2641630853) ^ 255 = (3 : ZMod 2641630853) ^ (127 + 127 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 127 * (3 : ZMod 2641630853) ^ 127) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 912615888 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 2641630853) ^ 511 = 48581877 := by
        calc
          (3 : ZMod 2641630853) ^ 511 = (3 : ZMod 2641630853) ^ (255 + 255 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = ((3 : ZMod 2641630853) ^ 255 * (3 : ZMod 2641630853) ^ 255) * (3 : ZMod 2641630853) := by rw [pow_succ, pow_add]
          _ = 48581877 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 2641630853) ^ 1022 = 1987660043 := by
        calc
          (3 : ZMod 2641630853) ^ 1022 = (3 : ZMod 2641630853) ^ (511 + 511) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 511 * (3 : ZMod 2641630853) ^ 511 := by rw [pow_add]
          _ = 1987660043 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 2641630853) ^ 2044 = 1559641767 := by
        calc
          (3 : ZMod 2641630853) ^ 2044 = (3 : ZMod 2641630853) ^ (1022 + 1022) :=
            congrArg (fun n : ℕ => (3 : ZMod 2641630853) ^ n) (by norm_num)
          _ = (3 : ZMod 2641630853) ^ 1022 * (3 : ZMod 2641630853) ^ 1022 := by rw [pow_add]
          _ = 1559641767 := by rw [factor_3_9]; decide
      change (3 : ZMod 2641630853) ^ 2044 ≠ 1
      rw [factor_3_10]
      decide

#print axioms prime_lucas_2641630853

end TotientTailPeriodKiller
end Erdos249257
