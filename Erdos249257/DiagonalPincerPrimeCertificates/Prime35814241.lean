import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=19 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000

theorem prime_lucas_35814241 : Nat.Prime 35814241 := by
  apply lucas_primality 35814241 (26 : ZMod 35814241)
  ·
      have fermat_0 : (26 : ZMod 35814241) ^ 1 = 26 := by norm_num
      have fermat_1 : (26 : ZMod 35814241) ^ 2 = 676 := by
        calc
          (26 : ZMod 35814241) ^ 2 = (26 : ZMod 35814241) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 1 * (26 : ZMod 35814241) ^ 1 := by rw [pow_add]
          _ = 676 := by rw [fermat_0]; decide
      have fermat_2 : (26 : ZMod 35814241) ^ 4 = 456976 := by
        calc
          (26 : ZMod 35814241) ^ 4 = (26 : ZMod 35814241) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 2 * (26 : ZMod 35814241) ^ 2 := by rw [pow_add]
          _ = 456976 := by rw [fermat_1]; decide
      have fermat_3 : (26 : ZMod 35814241) ^ 8 = 30039546 := by
        calc
          (26 : ZMod 35814241) ^ 8 = (26 : ZMod 35814241) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 4 * (26 : ZMod 35814241) ^ 4 := by rw [pow_add]
          _ = 30039546 := by rw [fermat_2]; decide
      have fermat_4 : (26 : ZMod 35814241) ^ 17 = 28475315 := by
        calc
          (26 : ZMod 35814241) ^ 17 = (26 : ZMod 35814241) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 8 * (26 : ZMod 35814241) ^ 8) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 28475315 := by rw [fermat_3]; decide
      have fermat_5 : (26 : ZMod 35814241) ^ 34 = 15477770 := by
        calc
          (26 : ZMod 35814241) ^ 34 = (26 : ZMod 35814241) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 17 * (26 : ZMod 35814241) ^ 17 := by rw [pow_add]
          _ = 15477770 := by rw [fermat_4]; decide
      have fermat_6 : (26 : ZMod 35814241) ^ 68 = 13566623 := by
        calc
          (26 : ZMod 35814241) ^ 68 = (26 : ZMod 35814241) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 34 * (26 : ZMod 35814241) ^ 34 := by rw [pow_add]
          _ = 13566623 := by rw [fermat_5]; decide
      have fermat_7 : (26 : ZMod 35814241) ^ 136 = 7187101 := by
        calc
          (26 : ZMod 35814241) ^ 136 = (26 : ZMod 35814241) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 68 * (26 : ZMod 35814241) ^ 68 := by rw [pow_add]
          _ = 7187101 := by rw [fermat_6]; decide
      have fermat_8 : (26 : ZMod 35814241) ^ 273 = 27693920 := by
        calc
          (26 : ZMod 35814241) ^ 273 = (26 : ZMod 35814241) ^ (136 + 136 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 136 * (26 : ZMod 35814241) ^ 136) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 27693920 := by rw [fermat_7]; decide
      have fermat_9 : (26 : ZMod 35814241) ^ 546 = 8440445 := by
        calc
          (26 : ZMod 35814241) ^ 546 = (26 : ZMod 35814241) ^ (273 + 273) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 273 * (26 : ZMod 35814241) ^ 273 := by rw [pow_add]
          _ = 8440445 := by rw [fermat_8]; decide
      have fermat_10 : (26 : ZMod 35814241) ^ 1092 = 32442922 := by
        calc
          (26 : ZMod 35814241) ^ 1092 = (26 : ZMod 35814241) ^ (546 + 546) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 546 * (26 : ZMod 35814241) ^ 546 := by rw [pow_add]
          _ = 32442922 := by rw [fermat_9]; decide
      have fermat_11 : (26 : ZMod 35814241) ^ 2185 = 14011863 := by
        calc
          (26 : ZMod 35814241) ^ 2185 = (26 : ZMod 35814241) ^ (1092 + 1092 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 1092 * (26 : ZMod 35814241) ^ 1092) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 14011863 := by rw [fermat_10]; decide
      have fermat_12 : (26 : ZMod 35814241) ^ 4371 = 16700825 := by
        calc
          (26 : ZMod 35814241) ^ 4371 = (26 : ZMod 35814241) ^ (2185 + 2185 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 2185 * (26 : ZMod 35814241) ^ 2185) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 16700825 := by rw [fermat_11]; decide
      have fermat_13 : (26 : ZMod 35814241) ^ 8743 = 9894975 := by
        calc
          (26 : ZMod 35814241) ^ 8743 = (26 : ZMod 35814241) ^ (4371 + 4371 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 4371 * (26 : ZMod 35814241) ^ 4371) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 9894975 := by rw [fermat_12]; decide
      have fermat_14 : (26 : ZMod 35814241) ^ 17487 = 7418879 := by
        calc
          (26 : ZMod 35814241) ^ 17487 = (26 : ZMod 35814241) ^ (8743 + 8743 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 8743 * (26 : ZMod 35814241) ^ 8743) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 7418879 := by rw [fermat_13]; decide
      have fermat_15 : (26 : ZMod 35814241) ^ 34974 = 10276949 := by
        calc
          (26 : ZMod 35814241) ^ 34974 = (26 : ZMod 35814241) ^ (17487 + 17487) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 17487 * (26 : ZMod 35814241) ^ 17487 := by rw [pow_add]
          _ = 10276949 := by rw [fermat_14]; decide
      have fermat_16 : (26 : ZMod 35814241) ^ 69949 = 15370001 := by
        calc
          (26 : ZMod 35814241) ^ 69949 = (26 : ZMod 35814241) ^ (34974 + 34974 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 34974 * (26 : ZMod 35814241) ^ 34974) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 15370001 := by rw [fermat_15]; decide
      have fermat_17 : (26 : ZMod 35814241) ^ 139899 = 32248008 := by
        calc
          (26 : ZMod 35814241) ^ 139899 = (26 : ZMod 35814241) ^ (69949 + 69949 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 69949 * (26 : ZMod 35814241) ^ 69949) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 32248008 := by rw [fermat_16]; decide
      have fermat_18 : (26 : ZMod 35814241) ^ 279798 = 22688779 := by
        calc
          (26 : ZMod 35814241) ^ 279798 = (26 : ZMod 35814241) ^ (139899 + 139899) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 139899 * (26 : ZMod 35814241) ^ 139899 := by rw [pow_add]
          _ = 22688779 := by rw [fermat_17]; decide
      have fermat_19 : (26 : ZMod 35814241) ^ 559597 = 24554815 := by
        calc
          (26 : ZMod 35814241) ^ 559597 = (26 : ZMod 35814241) ^ (279798 + 279798 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 279798 * (26 : ZMod 35814241) ^ 279798) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 24554815 := by rw [fermat_18]; decide
      have fermat_20 : (26 : ZMod 35814241) ^ 1119195 = 18666555 := by
        calc
          (26 : ZMod 35814241) ^ 1119195 = (26 : ZMod 35814241) ^ (559597 + 559597 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 559597 * (26 : ZMod 35814241) ^ 559597) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 18666555 := by rw [fermat_19]; decide
      have fermat_21 : (26 : ZMod 35814241) ^ 2238390 = 15083407 := by
        calc
          (26 : ZMod 35814241) ^ 2238390 = (26 : ZMod 35814241) ^ (1119195 + 1119195) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 1119195 * (26 : ZMod 35814241) ^ 1119195 := by rw [pow_add]
          _ = 15083407 := by rw [fermat_20]; decide
      have fermat_22 : (26 : ZMod 35814241) ^ 4476780 = 24502692 := by
        calc
          (26 : ZMod 35814241) ^ 4476780 = (26 : ZMod 35814241) ^ (2238390 + 2238390) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 2238390 * (26 : ZMod 35814241) ^ 2238390 := by rw [pow_add]
          _ = 24502692 := by rw [fermat_21]; decide
      have fermat_23 : (26 : ZMod 35814241) ^ 8953560 = 1512848 := by
        calc
          (26 : ZMod 35814241) ^ 8953560 = (26 : ZMod 35814241) ^ (4476780 + 4476780) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 4476780 * (26 : ZMod 35814241) ^ 4476780 := by rw [pow_add]
          _ = 1512848 := by rw [fermat_22]; decide
      have fermat_24 : (26 : ZMod 35814241) ^ 17907120 = 35814240 := by
        calc
          (26 : ZMod 35814241) ^ 17907120 = (26 : ZMod 35814241) ^ (8953560 + 8953560) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 8953560 * (26 : ZMod 35814241) ^ 8953560 := by rw [pow_add]
          _ = 35814240 := by rw [fermat_23]; decide
      have fermat_25 : (26 : ZMod 35814241) ^ 35814240 = 1 := by
        calc
          (26 : ZMod 35814241) ^ 35814240 = (26 : ZMod 35814241) ^ (17907120 + 17907120) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 17907120 * (26 : ZMod 35814241) ^ 17907120 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 2), (5, 1), (7, 1), (11, 1), (17, 1), (19, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 2), (5, 1), (7, 1), (11, 1), (17, 1), (19, 1)] : List FactorBlock).map factorBlockValue).prod = 35814241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (26 : ZMod 35814241) ^ 1 = 26 := by norm_num
      have factor_0_1 : (26 : ZMod 35814241) ^ 2 = 676 := by
        calc
          (26 : ZMod 35814241) ^ 2 = (26 : ZMod 35814241) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 1 * (26 : ZMod 35814241) ^ 1 := by rw [pow_add]
          _ = 676 := by rw [factor_0_0]; decide
      have factor_0_2 : (26 : ZMod 35814241) ^ 4 = 456976 := by
        calc
          (26 : ZMod 35814241) ^ 4 = (26 : ZMod 35814241) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 2 * (26 : ZMod 35814241) ^ 2 := by rw [pow_add]
          _ = 456976 := by rw [factor_0_1]; decide
      have factor_0_3 : (26 : ZMod 35814241) ^ 8 = 30039546 := by
        calc
          (26 : ZMod 35814241) ^ 8 = (26 : ZMod 35814241) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 4 * (26 : ZMod 35814241) ^ 4 := by rw [pow_add]
          _ = 30039546 := by rw [factor_0_2]; decide
      have factor_0_4 : (26 : ZMod 35814241) ^ 17 = 28475315 := by
        calc
          (26 : ZMod 35814241) ^ 17 = (26 : ZMod 35814241) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 8 * (26 : ZMod 35814241) ^ 8) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 28475315 := by rw [factor_0_3]; decide
      have factor_0_5 : (26 : ZMod 35814241) ^ 34 = 15477770 := by
        calc
          (26 : ZMod 35814241) ^ 34 = (26 : ZMod 35814241) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 17 * (26 : ZMod 35814241) ^ 17 := by rw [pow_add]
          _ = 15477770 := by rw [factor_0_4]; decide
      have factor_0_6 : (26 : ZMod 35814241) ^ 68 = 13566623 := by
        calc
          (26 : ZMod 35814241) ^ 68 = (26 : ZMod 35814241) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 34 * (26 : ZMod 35814241) ^ 34 := by rw [pow_add]
          _ = 13566623 := by rw [factor_0_5]; decide
      have factor_0_7 : (26 : ZMod 35814241) ^ 136 = 7187101 := by
        calc
          (26 : ZMod 35814241) ^ 136 = (26 : ZMod 35814241) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 68 * (26 : ZMod 35814241) ^ 68 := by rw [pow_add]
          _ = 7187101 := by rw [factor_0_6]; decide
      have factor_0_8 : (26 : ZMod 35814241) ^ 273 = 27693920 := by
        calc
          (26 : ZMod 35814241) ^ 273 = (26 : ZMod 35814241) ^ (136 + 136 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 136 * (26 : ZMod 35814241) ^ 136) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 27693920 := by rw [factor_0_7]; decide
      have factor_0_9 : (26 : ZMod 35814241) ^ 546 = 8440445 := by
        calc
          (26 : ZMod 35814241) ^ 546 = (26 : ZMod 35814241) ^ (273 + 273) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 273 * (26 : ZMod 35814241) ^ 273 := by rw [pow_add]
          _ = 8440445 := by rw [factor_0_8]; decide
      have factor_0_10 : (26 : ZMod 35814241) ^ 1092 = 32442922 := by
        calc
          (26 : ZMod 35814241) ^ 1092 = (26 : ZMod 35814241) ^ (546 + 546) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 546 * (26 : ZMod 35814241) ^ 546 := by rw [pow_add]
          _ = 32442922 := by rw [factor_0_9]; decide
      have factor_0_11 : (26 : ZMod 35814241) ^ 2185 = 14011863 := by
        calc
          (26 : ZMod 35814241) ^ 2185 = (26 : ZMod 35814241) ^ (1092 + 1092 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 1092 * (26 : ZMod 35814241) ^ 1092) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 14011863 := by rw [factor_0_10]; decide
      have factor_0_12 : (26 : ZMod 35814241) ^ 4371 = 16700825 := by
        calc
          (26 : ZMod 35814241) ^ 4371 = (26 : ZMod 35814241) ^ (2185 + 2185 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 2185 * (26 : ZMod 35814241) ^ 2185) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 16700825 := by rw [factor_0_11]; decide
      have factor_0_13 : (26 : ZMod 35814241) ^ 8743 = 9894975 := by
        calc
          (26 : ZMod 35814241) ^ 8743 = (26 : ZMod 35814241) ^ (4371 + 4371 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 4371 * (26 : ZMod 35814241) ^ 4371) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 9894975 := by rw [factor_0_12]; decide
      have factor_0_14 : (26 : ZMod 35814241) ^ 17487 = 7418879 := by
        calc
          (26 : ZMod 35814241) ^ 17487 = (26 : ZMod 35814241) ^ (8743 + 8743 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 8743 * (26 : ZMod 35814241) ^ 8743) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 7418879 := by rw [factor_0_13]; decide
      have factor_0_15 : (26 : ZMod 35814241) ^ 34974 = 10276949 := by
        calc
          (26 : ZMod 35814241) ^ 34974 = (26 : ZMod 35814241) ^ (17487 + 17487) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 17487 * (26 : ZMod 35814241) ^ 17487 := by rw [pow_add]
          _ = 10276949 := by rw [factor_0_14]; decide
      have factor_0_16 : (26 : ZMod 35814241) ^ 69949 = 15370001 := by
        calc
          (26 : ZMod 35814241) ^ 69949 = (26 : ZMod 35814241) ^ (34974 + 34974 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 34974 * (26 : ZMod 35814241) ^ 34974) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 15370001 := by rw [factor_0_15]; decide
      have factor_0_17 : (26 : ZMod 35814241) ^ 139899 = 32248008 := by
        calc
          (26 : ZMod 35814241) ^ 139899 = (26 : ZMod 35814241) ^ (69949 + 69949 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 69949 * (26 : ZMod 35814241) ^ 69949) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 32248008 := by rw [factor_0_16]; decide
      have factor_0_18 : (26 : ZMod 35814241) ^ 279798 = 22688779 := by
        calc
          (26 : ZMod 35814241) ^ 279798 = (26 : ZMod 35814241) ^ (139899 + 139899) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 139899 * (26 : ZMod 35814241) ^ 139899 := by rw [pow_add]
          _ = 22688779 := by rw [factor_0_17]; decide
      have factor_0_19 : (26 : ZMod 35814241) ^ 559597 = 24554815 := by
        calc
          (26 : ZMod 35814241) ^ 559597 = (26 : ZMod 35814241) ^ (279798 + 279798 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 279798 * (26 : ZMod 35814241) ^ 279798) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 24554815 := by rw [factor_0_18]; decide
      have factor_0_20 : (26 : ZMod 35814241) ^ 1119195 = 18666555 := by
        calc
          (26 : ZMod 35814241) ^ 1119195 = (26 : ZMod 35814241) ^ (559597 + 559597 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 559597 * (26 : ZMod 35814241) ^ 559597) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 18666555 := by rw [factor_0_19]; decide
      have factor_0_21 : (26 : ZMod 35814241) ^ 2238390 = 15083407 := by
        calc
          (26 : ZMod 35814241) ^ 2238390 = (26 : ZMod 35814241) ^ (1119195 + 1119195) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 1119195 * (26 : ZMod 35814241) ^ 1119195 := by rw [pow_add]
          _ = 15083407 := by rw [factor_0_20]; decide
      have factor_0_22 : (26 : ZMod 35814241) ^ 4476780 = 24502692 := by
        calc
          (26 : ZMod 35814241) ^ 4476780 = (26 : ZMod 35814241) ^ (2238390 + 2238390) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 2238390 * (26 : ZMod 35814241) ^ 2238390 := by rw [pow_add]
          _ = 24502692 := by rw [factor_0_21]; decide
      have factor_0_23 : (26 : ZMod 35814241) ^ 8953560 = 1512848 := by
        calc
          (26 : ZMod 35814241) ^ 8953560 = (26 : ZMod 35814241) ^ (4476780 + 4476780) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 4476780 * (26 : ZMod 35814241) ^ 4476780 := by rw [pow_add]
          _ = 1512848 := by rw [factor_0_22]; decide
      have factor_0_24 : (26 : ZMod 35814241) ^ 17907120 = 35814240 := by
        calc
          (26 : ZMod 35814241) ^ 17907120 = (26 : ZMod 35814241) ^ (8953560 + 8953560) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 8953560 * (26 : ZMod 35814241) ^ 8953560 := by rw [pow_add]
          _ = 35814240 := by rw [factor_0_23]; decide
      change (26 : ZMod 35814241) ^ 17907120 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (26 : ZMod 35814241) ^ 1 = 26 := by norm_num
      have factor_1_1 : (26 : ZMod 35814241) ^ 2 = 676 := by
        calc
          (26 : ZMod 35814241) ^ 2 = (26 : ZMod 35814241) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 1 * (26 : ZMod 35814241) ^ 1 := by rw [pow_add]
          _ = 676 := by rw [factor_1_0]; decide
      have factor_1_2 : (26 : ZMod 35814241) ^ 5 = 11881376 := by
        calc
          (26 : ZMod 35814241) ^ 5 = (26 : ZMod 35814241) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 2 * (26 : ZMod 35814241) ^ 2) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 11881376 := by rw [factor_1_1]; decide
      have factor_1_3 : (26 : ZMod 35814241) ^ 11 = 1519674 := by
        calc
          (26 : ZMod 35814241) ^ 11 = (26 : ZMod 35814241) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 5 * (26 : ZMod 35814241) ^ 5) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 1519674 := by rw [factor_1_2]; decide
      have factor_1_4 : (26 : ZMod 35814241) ^ 22 = 35178114 := by
        calc
          (26 : ZMod 35814241) ^ 22 = (26 : ZMod 35814241) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 11 * (26 : ZMod 35814241) ^ 11 := by rw [pow_add]
          _ = 35178114 := by rw [factor_1_3]; decide
      have factor_1_5 : (26 : ZMod 35814241) ^ 45 = 18613266 := by
        calc
          (26 : ZMod 35814241) ^ 45 = (26 : ZMod 35814241) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 22 * (26 : ZMod 35814241) ^ 22) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 18613266 := by rw [factor_1_4]; decide
      have factor_1_6 : (26 : ZMod 35814241) ^ 91 = 12440029 := by
        calc
          (26 : ZMod 35814241) ^ 91 = (26 : ZMod 35814241) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 45 * (26 : ZMod 35814241) ^ 45) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 12440029 := by rw [factor_1_5]; decide
      have factor_1_7 : (26 : ZMod 35814241) ^ 182 = 19175334 := by
        calc
          (26 : ZMod 35814241) ^ 182 = (26 : ZMod 35814241) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 91 * (26 : ZMod 35814241) ^ 91 := by rw [pow_add]
          _ = 19175334 := by rw [factor_1_6]; decide
      have factor_1_8 : (26 : ZMod 35814241) ^ 364 = 10593194 := by
        calc
          (26 : ZMod 35814241) ^ 364 = (26 : ZMod 35814241) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 182 * (26 : ZMod 35814241) ^ 182 := by rw [pow_add]
          _ = 10593194 := by rw [factor_1_7]; decide
      have factor_1_9 : (26 : ZMod 35814241) ^ 728 = 595084 := by
        calc
          (26 : ZMod 35814241) ^ 728 = (26 : ZMod 35814241) ^ (364 + 364) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 364 * (26 : ZMod 35814241) ^ 364 := by rw [pow_add]
          _ = 595084 := by rw [factor_1_8]; decide
      have factor_1_10 : (26 : ZMod 35814241) ^ 1457 = 16624453 := by
        calc
          (26 : ZMod 35814241) ^ 1457 = (26 : ZMod 35814241) ^ (728 + 728 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 728 * (26 : ZMod 35814241) ^ 728) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 16624453 := by rw [factor_1_9]; decide
      have factor_1_11 : (26 : ZMod 35814241) ^ 2914 = 28173179 := by
        calc
          (26 : ZMod 35814241) ^ 2914 = (26 : ZMod 35814241) ^ (1457 + 1457) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 1457 * (26 : ZMod 35814241) ^ 1457 := by rw [pow_add]
          _ = 28173179 := by rw [factor_1_10]; decide
      have factor_1_12 : (26 : ZMod 35814241) ^ 5829 = 24840730 := by
        calc
          (26 : ZMod 35814241) ^ 5829 = (26 : ZMod 35814241) ^ (2914 + 2914 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 2914 * (26 : ZMod 35814241) ^ 2914) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 24840730 := by rw [factor_1_11]; decide
      have factor_1_13 : (26 : ZMod 35814241) ^ 11658 = 7666749 := by
        calc
          (26 : ZMod 35814241) ^ 11658 = (26 : ZMod 35814241) ^ (5829 + 5829) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 5829 * (26 : ZMod 35814241) ^ 5829 := by rw [pow_add]
          _ = 7666749 := by rw [factor_1_12]; decide
      have factor_1_14 : (26 : ZMod 35814241) ^ 23316 = 27429222 := by
        calc
          (26 : ZMod 35814241) ^ 23316 = (26 : ZMod 35814241) ^ (11658 + 11658) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 11658 * (26 : ZMod 35814241) ^ 11658 := by rw [pow_add]
          _ = 27429222 := by rw [factor_1_13]; decide
      have factor_1_15 : (26 : ZMod 35814241) ^ 46633 = 25799780 := by
        calc
          (26 : ZMod 35814241) ^ 46633 = (26 : ZMod 35814241) ^ (23316 + 23316 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 23316 * (26 : ZMod 35814241) ^ 23316) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 25799780 := by rw [factor_1_14]; decide
      have factor_1_16 : (26 : ZMod 35814241) ^ 93266 = 27732415 := by
        calc
          (26 : ZMod 35814241) ^ 93266 = (26 : ZMod 35814241) ^ (46633 + 46633) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 46633 * (26 : ZMod 35814241) ^ 46633 := by rw [pow_add]
          _ = 27732415 := by rw [factor_1_15]; decide
      have factor_1_17 : (26 : ZMod 35814241) ^ 186532 = 11798695 := by
        calc
          (26 : ZMod 35814241) ^ 186532 = (26 : ZMod 35814241) ^ (93266 + 93266) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 93266 * (26 : ZMod 35814241) ^ 93266 := by rw [pow_add]
          _ = 11798695 := by rw [factor_1_16]; decide
      have factor_1_18 : (26 : ZMod 35814241) ^ 373065 = 26912236 := by
        calc
          (26 : ZMod 35814241) ^ 373065 = (26 : ZMod 35814241) ^ (186532 + 186532 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 186532 * (26 : ZMod 35814241) ^ 186532) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 26912236 := by rw [factor_1_17]; decide
      have factor_1_19 : (26 : ZMod 35814241) ^ 746130 = 23358699 := by
        calc
          (26 : ZMod 35814241) ^ 746130 = (26 : ZMod 35814241) ^ (373065 + 373065) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 373065 * (26 : ZMod 35814241) ^ 373065 := by rw [pow_add]
          _ = 23358699 := by rw [factor_1_18]; decide
      have factor_1_20 : (26 : ZMod 35814241) ^ 1492260 = 3393313 := by
        calc
          (26 : ZMod 35814241) ^ 1492260 = (26 : ZMod 35814241) ^ (746130 + 746130) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 746130 * (26 : ZMod 35814241) ^ 746130 := by rw [pow_add]
          _ = 3393313 := by rw [factor_1_19]; decide
      have factor_1_21 : (26 : ZMod 35814241) ^ 2984520 = 8120541 := by
        calc
          (26 : ZMod 35814241) ^ 2984520 = (26 : ZMod 35814241) ^ (1492260 + 1492260) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 1492260 * (26 : ZMod 35814241) ^ 1492260 := by rw [pow_add]
          _ = 8120541 := by rw [factor_1_20]; decide
      have factor_1_22 : (26 : ZMod 35814241) ^ 5969040 = 5985 := by
        calc
          (26 : ZMod 35814241) ^ 5969040 = (26 : ZMod 35814241) ^ (2984520 + 2984520) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 2984520 * (26 : ZMod 35814241) ^ 2984520 := by rw [pow_add]
          _ = 5985 := by rw [factor_1_21]; decide
      have factor_1_23 : (26 : ZMod 35814241) ^ 11938080 = 5984 := by
        calc
          (26 : ZMod 35814241) ^ 11938080 = (26 : ZMod 35814241) ^ (5969040 + 5969040) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 5969040 * (26 : ZMod 35814241) ^ 5969040 := by rw [pow_add]
          _ = 5984 := by rw [factor_1_22]; decide
      change (26 : ZMod 35814241) ^ 11938080 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (26 : ZMod 35814241) ^ 1 = 26 := by norm_num
      have factor_2_1 : (26 : ZMod 35814241) ^ 3 = 17576 := by
        calc
          (26 : ZMod 35814241) ^ 3 = (26 : ZMod 35814241) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 1 * (26 : ZMod 35814241) ^ 1) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 17576 := by rw [factor_2_0]; decide
      have factor_2_2 : (26 : ZMod 35814241) ^ 6 = 22401848 := by
        calc
          (26 : ZMod 35814241) ^ 6 = (26 : ZMod 35814241) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 3 * (26 : ZMod 35814241) ^ 3 := by rw [pow_add]
          _ = 22401848 := by rw [factor_2_1]; decide
      have factor_2_3 : (26 : ZMod 35814241) ^ 13 = 24500876 := by
        calc
          (26 : ZMod 35814241) ^ 13 = (26 : ZMod 35814241) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 6 * (26 : ZMod 35814241) ^ 6) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 24500876 := by rw [factor_2_2]; decide
      have factor_2_4 : (26 : ZMod 35814241) ^ 27 = 30092924 := by
        calc
          (26 : ZMod 35814241) ^ 27 = (26 : ZMod 35814241) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 13 * (26 : ZMod 35814241) ^ 13) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 30092924 := by rw [factor_2_3]; decide
      have factor_2_5 : (26 : ZMod 35814241) ^ 54 = 4039550 := by
        calc
          (26 : ZMod 35814241) ^ 54 = (26 : ZMod 35814241) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 27 * (26 : ZMod 35814241) ^ 27 := by rw [pow_add]
          _ = 4039550 := by rw [factor_2_4]; decide
      have factor_2_6 : (26 : ZMod 35814241) ^ 109 = 2379157 := by
        calc
          (26 : ZMod 35814241) ^ 109 = (26 : ZMod 35814241) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 54 * (26 : ZMod 35814241) ^ 54) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 2379157 := by rw [factor_2_5]; decide
      have factor_2_7 : (26 : ZMod 35814241) ^ 218 = 18869081 := by
        calc
          (26 : ZMod 35814241) ^ 218 = (26 : ZMod 35814241) ^ (109 + 109) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 109 * (26 : ZMod 35814241) ^ 109 := by rw [pow_add]
          _ = 18869081 := by rw [factor_2_6]; decide
      have factor_2_8 : (26 : ZMod 35814241) ^ 437 = 8666779 := by
        calc
          (26 : ZMod 35814241) ^ 437 = (26 : ZMod 35814241) ^ (218 + 218 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 218 * (26 : ZMod 35814241) ^ 218) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 8666779 := by rw [factor_2_7]; decide
      have factor_2_9 : (26 : ZMod 35814241) ^ 874 = 29656746 := by
        calc
          (26 : ZMod 35814241) ^ 874 = (26 : ZMod 35814241) ^ (437 + 437) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 437 * (26 : ZMod 35814241) ^ 437 := by rw [pow_add]
          _ = 29656746 := by rw [factor_2_8]; decide
      have factor_2_10 : (26 : ZMod 35814241) ^ 1748 = 34254616 := by
        calc
          (26 : ZMod 35814241) ^ 1748 = (26 : ZMod 35814241) ^ (874 + 874) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 874 * (26 : ZMod 35814241) ^ 874 := by rw [pow_add]
          _ = 34254616 := by rw [factor_2_9]; decide
      have factor_2_11 : (26 : ZMod 35814241) ^ 3497 = 33158544 := by
        calc
          (26 : ZMod 35814241) ^ 3497 = (26 : ZMod 35814241) ^ (1748 + 1748 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 1748 * (26 : ZMod 35814241) ^ 1748) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 33158544 := by rw [factor_2_10]; decide
      have factor_2_12 : (26 : ZMod 35814241) ^ 6994 = 7146884 := by
        calc
          (26 : ZMod 35814241) ^ 6994 = (26 : ZMod 35814241) ^ (3497 + 3497) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 3497 * (26 : ZMod 35814241) ^ 3497 := by rw [pow_add]
          _ = 7146884 := by rw [factor_2_11]; decide
      have factor_2_13 : (26 : ZMod 35814241) ^ 13989 = 34994809 := by
        calc
          (26 : ZMod 35814241) ^ 13989 = (26 : ZMod 35814241) ^ (6994 + 6994 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 6994 * (26 : ZMod 35814241) ^ 6994) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 34994809 := by rw [factor_2_12]; decide
      have factor_2_14 : (26 : ZMod 35814241) ^ 27979 = 35693400 := by
        calc
          (26 : ZMod 35814241) ^ 27979 = (26 : ZMod 35814241) ^ (13989 + 13989 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 13989 * (26 : ZMod 35814241) ^ 13989) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 35693400 := by rw [factor_2_13]; decide
      have factor_2_15 : (26 : ZMod 35814241) ^ 55959 = 35274706 := by
        calc
          (26 : ZMod 35814241) ^ 55959 = (26 : ZMod 35814241) ^ (27979 + 27979 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 27979 * (26 : ZMod 35814241) ^ 27979) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 35274706 := by rw [factor_2_14]; decide
      have factor_2_16 : (26 : ZMod 35814241) ^ 111919 = 32314043 := by
        calc
          (26 : ZMod 35814241) ^ 111919 = (26 : ZMod 35814241) ^ (55959 + 55959 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 55959 * (26 : ZMod 35814241) ^ 55959) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 32314043 := by rw [factor_2_15]; decide
      have factor_2_17 : (26 : ZMod 35814241) ^ 223839 = 23113348 := by
        calc
          (26 : ZMod 35814241) ^ 223839 = (26 : ZMod 35814241) ^ (111919 + 111919 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 111919 * (26 : ZMod 35814241) ^ 111919) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 23113348 := by rw [factor_2_16]; decide
      have factor_2_18 : (26 : ZMod 35814241) ^ 447678 = 5211540 := by
        calc
          (26 : ZMod 35814241) ^ 447678 = (26 : ZMod 35814241) ^ (223839 + 223839) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 223839 * (26 : ZMod 35814241) ^ 223839 := by rw [pow_add]
          _ = 5211540 := by rw [factor_2_17]; decide
      have factor_2_19 : (26 : ZMod 35814241) ^ 895356 = 25552599 := by
        calc
          (26 : ZMod 35814241) ^ 895356 = (26 : ZMod 35814241) ^ (447678 + 447678) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 447678 * (26 : ZMod 35814241) ^ 447678 := by rw [pow_add]
          _ = 25552599 := by rw [factor_2_18]; decide
      have factor_2_20 : (26 : ZMod 35814241) ^ 1790712 = 14448277 := by
        calc
          (26 : ZMod 35814241) ^ 1790712 = (26 : ZMod 35814241) ^ (895356 + 895356) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 895356 * (26 : ZMod 35814241) ^ 895356 := by rw [pow_add]
          _ = 14448277 := by rw [factor_2_19]; decide
      have factor_2_21 : (26 : ZMod 35814241) ^ 3581424 = 21269087 := by
        calc
          (26 : ZMod 35814241) ^ 3581424 = (26 : ZMod 35814241) ^ (1790712 + 1790712) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 1790712 * (26 : ZMod 35814241) ^ 1790712 := by rw [pow_add]
          _ = 21269087 := by rw [factor_2_20]; decide
      have factor_2_22 : (26 : ZMod 35814241) ^ 7162848 = 14405167 := by
        calc
          (26 : ZMod 35814241) ^ 7162848 = (26 : ZMod 35814241) ^ (3581424 + 3581424) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 3581424 * (26 : ZMod 35814241) ^ 3581424 := by rw [pow_add]
          _ = 14405167 := by rw [factor_2_21]; decide
      change (26 : ZMod 35814241) ^ 7162848 ≠ 1
      rw [factor_2_22]
      decide
    ·
      have factor_3_0 : (26 : ZMod 35814241) ^ 1 = 26 := by norm_num
      have factor_3_1 : (26 : ZMod 35814241) ^ 2 = 676 := by
        calc
          (26 : ZMod 35814241) ^ 2 = (26 : ZMod 35814241) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 1 * (26 : ZMod 35814241) ^ 1 := by rw [pow_add]
          _ = 676 := by rw [factor_3_0]; decide
      have factor_3_2 : (26 : ZMod 35814241) ^ 4 = 456976 := by
        calc
          (26 : ZMod 35814241) ^ 4 = (26 : ZMod 35814241) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 2 * (26 : ZMod 35814241) ^ 2 := by rw [pow_add]
          _ = 456976 := by rw [factor_3_1]; decide
      have factor_3_3 : (26 : ZMod 35814241) ^ 9 = 28929135 := by
        calc
          (26 : ZMod 35814241) ^ 9 = (26 : ZMod 35814241) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 4 * (26 : ZMod 35814241) ^ 4) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 28929135 := by rw [factor_3_2]; decide
      have factor_3_4 : (26 : ZMod 35814241) ^ 19 = 17065523 := by
        calc
          (26 : ZMod 35814241) ^ 19 = (26 : ZMod 35814241) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 9 * (26 : ZMod 35814241) ^ 9) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 17065523 := by rw [factor_3_3]; decide
      have factor_3_5 : (26 : ZMod 35814241) ^ 39 = 31036770 := by
        calc
          (26 : ZMod 35814241) ^ 39 = (26 : ZMod 35814241) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 19 * (26 : ZMod 35814241) ^ 19) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 31036770 := by rw [factor_3_4]; decide
      have factor_3_6 : (26 : ZMod 35814241) ^ 78 = 28251987 := by
        calc
          (26 : ZMod 35814241) ^ 78 = (26 : ZMod 35814241) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 39 * (26 : ZMod 35814241) ^ 39 := by rw [pow_add]
          _ = 28251987 := by rw [factor_3_5]; decide
      have factor_3_7 : (26 : ZMod 35814241) ^ 156 = 6931090 := by
        calc
          (26 : ZMod 35814241) ^ 156 = (26 : ZMod 35814241) ^ (78 + 78) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 78 * (26 : ZMod 35814241) ^ 78 := by rw [pow_add]
          _ = 6931090 := by rw [factor_3_6]; decide
      have factor_3_8 : (26 : ZMod 35814241) ^ 312 = 3394894 := by
        calc
          (26 : ZMod 35814241) ^ 312 = (26 : ZMod 35814241) ^ (156 + 156) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 156 * (26 : ZMod 35814241) ^ 156 := by rw [pow_add]
          _ = 3394894 := by rw [factor_3_7]; decide
      have factor_3_9 : (26 : ZMod 35814241) ^ 624 = 31817749 := by
        calc
          (26 : ZMod 35814241) ^ 624 = (26 : ZMod 35814241) ^ (312 + 312) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 312 * (26 : ZMod 35814241) ^ 312 := by rw [pow_add]
          _ = 31817749 := by rw [factor_3_8]; decide
      have factor_3_10 : (26 : ZMod 35814241) ^ 1249 = 18968298 := by
        calc
          (26 : ZMod 35814241) ^ 1249 = (26 : ZMod 35814241) ^ (624 + 624 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 624 * (26 : ZMod 35814241) ^ 624) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 18968298 := by rw [factor_3_9]; decide
      have factor_3_11 : (26 : ZMod 35814241) ^ 2498 = 17367424 := by
        calc
          (26 : ZMod 35814241) ^ 2498 = (26 : ZMod 35814241) ^ (1249 + 1249) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 1249 * (26 : ZMod 35814241) ^ 1249 := by rw [pow_add]
          _ = 17367424 := by rw [factor_3_10]; decide
      have factor_3_12 : (26 : ZMod 35814241) ^ 4996 = 21950740 := by
        calc
          (26 : ZMod 35814241) ^ 4996 = (26 : ZMod 35814241) ^ (2498 + 2498) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 2498 * (26 : ZMod 35814241) ^ 2498 := by rw [pow_add]
          _ = 21950740 := by rw [factor_3_11]; decide
      have factor_3_13 : (26 : ZMod 35814241) ^ 9992 = 1235634 := by
        calc
          (26 : ZMod 35814241) ^ 9992 = (26 : ZMod 35814241) ^ (4996 + 4996) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 4996 * (26 : ZMod 35814241) ^ 4996 := by rw [pow_add]
          _ = 1235634 := by rw [factor_3_12]; decide
      have factor_3_14 : (26 : ZMod 35814241) ^ 19985 = 35392215 := by
        calc
          (26 : ZMod 35814241) ^ 19985 = (26 : ZMod 35814241) ^ (9992 + 9992 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 9992 * (26 : ZMod 35814241) ^ 9992) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 35392215 := by rw [factor_3_13]; decide
      have factor_3_15 : (26 : ZMod 35814241) ^ 39971 = 9014517 := by
        calc
          (26 : ZMod 35814241) ^ 39971 = (26 : ZMod 35814241) ^ (19985 + 19985 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 19985 * (26 : ZMod 35814241) ^ 19985) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 9014517 := by rw [factor_3_14]; decide
      have factor_3_16 : (26 : ZMod 35814241) ^ 79942 = 6713037 := by
        calc
          (26 : ZMod 35814241) ^ 79942 = (26 : ZMod 35814241) ^ (39971 + 39971) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 39971 * (26 : ZMod 35814241) ^ 39971 := by rw [pow_add]
          _ = 6713037 := by rw [factor_3_15]; decide
      have factor_3_17 : (26 : ZMod 35814241) ^ 159885 = 13947775 := by
        calc
          (26 : ZMod 35814241) ^ 159885 = (26 : ZMod 35814241) ^ (79942 + 79942 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 79942 * (26 : ZMod 35814241) ^ 79942) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 13947775 := by rw [factor_3_16]; decide
      have factor_3_18 : (26 : ZMod 35814241) ^ 319770 = 13149736 := by
        calc
          (26 : ZMod 35814241) ^ 319770 = (26 : ZMod 35814241) ^ (159885 + 159885) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 159885 * (26 : ZMod 35814241) ^ 159885 := by rw [pow_add]
          _ = 13149736 := by rw [factor_3_17]; decide
      have factor_3_19 : (26 : ZMod 35814241) ^ 639540 = 31984294 := by
        calc
          (26 : ZMod 35814241) ^ 639540 = (26 : ZMod 35814241) ^ (319770 + 319770) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 319770 * (26 : ZMod 35814241) ^ 319770 := by rw [pow_add]
          _ = 31984294 := by rw [factor_3_18]; decide
      have factor_3_20 : (26 : ZMod 35814241) ^ 1279080 = 19522198 := by
        calc
          (26 : ZMod 35814241) ^ 1279080 = (26 : ZMod 35814241) ^ (639540 + 639540) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 639540 * (26 : ZMod 35814241) ^ 639540 := by rw [pow_add]
          _ = 19522198 := by rw [factor_3_19]; decide
      have factor_3_21 : (26 : ZMod 35814241) ^ 2558160 = 7762693 := by
        calc
          (26 : ZMod 35814241) ^ 2558160 = (26 : ZMod 35814241) ^ (1279080 + 1279080) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 1279080 * (26 : ZMod 35814241) ^ 1279080 := by rw [pow_add]
          _ = 7762693 := by rw [factor_3_20]; decide
      have factor_3_22 : (26 : ZMod 35814241) ^ 5116320 = 8160735 := by
        calc
          (26 : ZMod 35814241) ^ 5116320 = (26 : ZMod 35814241) ^ (2558160 + 2558160) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 2558160 * (26 : ZMod 35814241) ^ 2558160 := by rw [pow_add]
          _ = 8160735 := by rw [factor_3_21]; decide
      change (26 : ZMod 35814241) ^ 5116320 ≠ 1
      rw [factor_3_22]
      decide
    ·
      have factor_4_0 : (26 : ZMod 35814241) ^ 1 = 26 := by norm_num
      have factor_4_1 : (26 : ZMod 35814241) ^ 3 = 17576 := by
        calc
          (26 : ZMod 35814241) ^ 3 = (26 : ZMod 35814241) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 1 * (26 : ZMod 35814241) ^ 1) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 17576 := by rw [factor_4_0]; decide
      have factor_4_2 : (26 : ZMod 35814241) ^ 6 = 22401848 := by
        calc
          (26 : ZMod 35814241) ^ 6 = (26 : ZMod 35814241) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 3 * (26 : ZMod 35814241) ^ 3 := by rw [pow_add]
          _ = 22401848 := by rw [factor_4_1]; decide
      have factor_4_3 : (26 : ZMod 35814241) ^ 12 = 3697283 := by
        calc
          (26 : ZMod 35814241) ^ 12 = (26 : ZMod 35814241) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 6 * (26 : ZMod 35814241) ^ 6 := by rw [pow_add]
          _ = 3697283 := by rw [factor_4_2]; decide
      have factor_4_4 : (26 : ZMod 35814241) ^ 24 = 35563281 := by
        calc
          (26 : ZMod 35814241) ^ 24 = (26 : ZMod 35814241) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 12 * (26 : ZMod 35814241) ^ 12 := by rw [pow_add]
          _ = 35563281 := by rw [factor_4_3]; decide
      have factor_4_5 : (26 : ZMod 35814241) ^ 49 = 5234598 := by
        calc
          (26 : ZMod 35814241) ^ 49 = (26 : ZMod 35814241) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 24 * (26 : ZMod 35814241) ^ 24) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 5234598 := by rw [factor_4_4]; decide
      have factor_4_6 : (26 : ZMod 35814241) ^ 99 = 13201598 := by
        calc
          (26 : ZMod 35814241) ^ 99 = (26 : ZMod 35814241) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 49 * (26 : ZMod 35814241) ^ 49) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 13201598 := by rw [factor_4_5]; decide
      have factor_4_7 : (26 : ZMod 35814241) ^ 198 = 29245883 := by
        calc
          (26 : ZMod 35814241) ^ 198 = (26 : ZMod 35814241) ^ (99 + 99) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 99 * (26 : ZMod 35814241) ^ 99 := by rw [pow_add]
          _ = 29245883 := by rw [factor_4_6]; decide
      have factor_4_8 : (26 : ZMod 35814241) ^ 397 = 7973661 := by
        calc
          (26 : ZMod 35814241) ^ 397 = (26 : ZMod 35814241) ^ (198 + 198 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 198 * (26 : ZMod 35814241) ^ 198) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 7973661 := by rw [factor_4_7]; decide
      have factor_4_9 : (26 : ZMod 35814241) ^ 794 = 2593430 := by
        calc
          (26 : ZMod 35814241) ^ 794 = (26 : ZMod 35814241) ^ (397 + 397) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 397 * (26 : ZMod 35814241) ^ 397 := by rw [pow_add]
          _ = 2593430 := by rw [factor_4_8]; decide
      have factor_4_10 : (26 : ZMod 35814241) ^ 1589 = 13502866 := by
        calc
          (26 : ZMod 35814241) ^ 1589 = (26 : ZMod 35814241) ^ (794 + 794 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 794 * (26 : ZMod 35814241) ^ 794) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 13502866 := by rw [factor_4_9]; decide
      have factor_4_11 : (26 : ZMod 35814241) ^ 3179 = 32662330 := by
        calc
          (26 : ZMod 35814241) ^ 3179 = (26 : ZMod 35814241) ^ (1589 + 1589 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 1589 * (26 : ZMod 35814241) ^ 1589) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 32662330 := by rw [factor_4_10]; decide
      have factor_4_12 : (26 : ZMod 35814241) ^ 6359 = 8750904 := by
        calc
          (26 : ZMod 35814241) ^ 6359 = (26 : ZMod 35814241) ^ (3179 + 3179 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 3179 * (26 : ZMod 35814241) ^ 3179) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 8750904 := by rw [factor_4_11]; decide
      have factor_4_13 : (26 : ZMod 35814241) ^ 12718 = 24197088 := by
        calc
          (26 : ZMod 35814241) ^ 12718 = (26 : ZMod 35814241) ^ (6359 + 6359) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 6359 * (26 : ZMod 35814241) ^ 6359 := by rw [pow_add]
          _ = 24197088 := by rw [factor_4_12]; decide
      have factor_4_14 : (26 : ZMod 35814241) ^ 25436 = 12492965 := by
        calc
          (26 : ZMod 35814241) ^ 25436 = (26 : ZMod 35814241) ^ (12718 + 12718) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 12718 * (26 : ZMod 35814241) ^ 12718 := by rw [pow_add]
          _ = 12492965 := by rw [factor_4_13]; decide
      have factor_4_15 : (26 : ZMod 35814241) ^ 50872 = 9922145 := by
        calc
          (26 : ZMod 35814241) ^ 50872 = (26 : ZMod 35814241) ^ (25436 + 25436) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 25436 * (26 : ZMod 35814241) ^ 25436 := by rw [pow_add]
          _ = 9922145 := by rw [factor_4_14]; decide
      have factor_4_16 : (26 : ZMod 35814241) ^ 101745 = 3550235 := by
        calc
          (26 : ZMod 35814241) ^ 101745 = (26 : ZMod 35814241) ^ (50872 + 50872 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 50872 * (26 : ZMod 35814241) ^ 50872) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 3550235 := by rw [factor_4_15]; decide
      have factor_4_17 : (26 : ZMod 35814241) ^ 203490 = 26905854 := by
        calc
          (26 : ZMod 35814241) ^ 203490 = (26 : ZMod 35814241) ^ (101745 + 101745) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 101745 * (26 : ZMod 35814241) ^ 101745 := by rw [pow_add]
          _ = 26905854 := by rw [factor_4_16]; decide
      have factor_4_18 : (26 : ZMod 35814241) ^ 406980 = 14879509 := by
        calc
          (26 : ZMod 35814241) ^ 406980 = (26 : ZMod 35814241) ^ (203490 + 203490) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 203490 * (26 : ZMod 35814241) ^ 203490 := by rw [pow_add]
          _ = 14879509 := by rw [factor_4_17]; decide
      have factor_4_19 : (26 : ZMod 35814241) ^ 813960 = 18157109 := by
        calc
          (26 : ZMod 35814241) ^ 813960 = (26 : ZMod 35814241) ^ (406980 + 406980) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 406980 * (26 : ZMod 35814241) ^ 406980 := by rw [pow_add]
          _ = 18157109 := by rw [factor_4_18]; decide
      have factor_4_20 : (26 : ZMod 35814241) ^ 1627920 = 25260268 := by
        calc
          (26 : ZMod 35814241) ^ 1627920 = (26 : ZMod 35814241) ^ (813960 + 813960) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 813960 * (26 : ZMod 35814241) ^ 813960 := by rw [pow_add]
          _ = 25260268 := by rw [factor_4_19]; decide
      have factor_4_21 : (26 : ZMod 35814241) ^ 3255840 = 9565496 := by
        calc
          (26 : ZMod 35814241) ^ 3255840 = (26 : ZMod 35814241) ^ (1627920 + 1627920) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 1627920 * (26 : ZMod 35814241) ^ 1627920 := by rw [pow_add]
          _ = 9565496 := by rw [factor_4_20]; decide
      change (26 : ZMod 35814241) ^ 3255840 ≠ 1
      rw [factor_4_21]
      decide
    ·
      have factor_5_0 : (26 : ZMod 35814241) ^ 1 = 26 := by norm_num
      have factor_5_1 : (26 : ZMod 35814241) ^ 2 = 676 := by
        calc
          (26 : ZMod 35814241) ^ 2 = (26 : ZMod 35814241) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 1 * (26 : ZMod 35814241) ^ 1 := by rw [pow_add]
          _ = 676 := by rw [factor_5_0]; decide
      have factor_5_2 : (26 : ZMod 35814241) ^ 4 = 456976 := by
        calc
          (26 : ZMod 35814241) ^ 4 = (26 : ZMod 35814241) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 2 * (26 : ZMod 35814241) ^ 2 := by rw [pow_add]
          _ = 456976 := by rw [factor_5_1]; decide
      have factor_5_3 : (26 : ZMod 35814241) ^ 8 = 30039546 := by
        calc
          (26 : ZMod 35814241) ^ 8 = (26 : ZMod 35814241) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 4 * (26 : ZMod 35814241) ^ 4 := by rw [pow_add]
          _ = 30039546 := by rw [factor_5_2]; decide
      have factor_5_4 : (26 : ZMod 35814241) ^ 16 = 32777033 := by
        calc
          (26 : ZMod 35814241) ^ 16 = (26 : ZMod 35814241) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 8 * (26 : ZMod 35814241) ^ 8 := by rw [pow_add]
          _ = 32777033 := by rw [factor_5_3]; decide
      have factor_5_5 : (26 : ZMod 35814241) ^ 32 = 30009376 := by
        calc
          (26 : ZMod 35814241) ^ 32 = (26 : ZMod 35814241) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 16 * (26 : ZMod 35814241) ^ 16 := by rw [pow_add]
          _ = 30009376 := by rw [factor_5_4]; decide
      have factor_5_6 : (26 : ZMod 35814241) ^ 64 = 20181278 := by
        calc
          (26 : ZMod 35814241) ^ 64 = (26 : ZMod 35814241) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 32 * (26 : ZMod 35814241) ^ 32 := by rw [pow_add]
          _ = 20181278 := by rw [factor_5_5]; decide
      have factor_5_7 : (26 : ZMod 35814241) ^ 128 = 27909641 := by
        calc
          (26 : ZMod 35814241) ^ 128 = (26 : ZMod 35814241) ^ (64 + 64) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 64 * (26 : ZMod 35814241) ^ 64 := by rw [pow_add]
          _ = 27909641 := by rw [factor_5_6]; decide
      have factor_5_8 : (26 : ZMod 35814241) ^ 257 = 34548827 := by
        calc
          (26 : ZMod 35814241) ^ 257 = (26 : ZMod 35814241) ^ (128 + 128 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 128 * (26 : ZMod 35814241) ^ 128) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 34548827 := by rw [factor_5_7]; decide
      have factor_5_9 : (26 : ZMod 35814241) ^ 514 = 17876286 := by
        calc
          (26 : ZMod 35814241) ^ 514 = (26 : ZMod 35814241) ^ (257 + 257) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 257 * (26 : ZMod 35814241) ^ 257 := by rw [pow_add]
          _ = 17876286 := by rw [factor_5_8]; decide
      have factor_5_10 : (26 : ZMod 35814241) ^ 1028 = 10642564 := by
        calc
          (26 : ZMod 35814241) ^ 1028 = (26 : ZMod 35814241) ^ (514 + 514) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 514 * (26 : ZMod 35814241) ^ 514 := by rw [pow_add]
          _ = 10642564 := by rw [factor_5_9]; decide
      have factor_5_11 : (26 : ZMod 35814241) ^ 2057 = 10560152 := by
        calc
          (26 : ZMod 35814241) ^ 2057 = (26 : ZMod 35814241) ^ (1028 + 1028 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 1028 * (26 : ZMod 35814241) ^ 1028) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 10560152 := by rw [factor_5_10]; decide
      have factor_5_12 : (26 : ZMod 35814241) ^ 4114 = 2463908 := by
        calc
          (26 : ZMod 35814241) ^ 4114 = (26 : ZMod 35814241) ^ (2057 + 2057) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 2057 * (26 : ZMod 35814241) ^ 2057 := by rw [pow_add]
          _ = 2463908 := by rw [factor_5_11]; decide
      have factor_5_13 : (26 : ZMod 35814241) ^ 8229 = 24567706 := by
        calc
          (26 : ZMod 35814241) ^ 8229 = (26 : ZMod 35814241) ^ (4114 + 4114 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 4114 * (26 : ZMod 35814241) ^ 4114) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 24567706 := by rw [factor_5_12]; decide
      have factor_5_14 : (26 : ZMod 35814241) ^ 16458 = 3408622 := by
        calc
          (26 : ZMod 35814241) ^ 16458 = (26 : ZMod 35814241) ^ (8229 + 8229) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 8229 * (26 : ZMod 35814241) ^ 8229 := by rw [pow_add]
          _ = 3408622 := by rw [factor_5_13]; decide
      have factor_5_15 : (26 : ZMod 35814241) ^ 32917 = 20096015 := by
        calc
          (26 : ZMod 35814241) ^ 32917 = (26 : ZMod 35814241) ^ (16458 + 16458 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 16458 * (26 : ZMod 35814241) ^ 16458) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 20096015 := by rw [factor_5_14]; decide
      have factor_5_16 : (26 : ZMod 35814241) ^ 65835 = 9243725 := by
        calc
          (26 : ZMod 35814241) ^ 65835 = (26 : ZMod 35814241) ^ (32917 + 32917 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 32917 * (26 : ZMod 35814241) ^ 32917) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 9243725 := by rw [factor_5_15]; decide
      have factor_5_17 : (26 : ZMod 35814241) ^ 131670 = 11970282 := by
        calc
          (26 : ZMod 35814241) ^ 131670 = (26 : ZMod 35814241) ^ (65835 + 65835) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 65835 * (26 : ZMod 35814241) ^ 65835 := by rw [pow_add]
          _ = 11970282 := by rw [factor_5_16]; decide
      have factor_5_18 : (26 : ZMod 35814241) ^ 263340 = 30169228 := by
        calc
          (26 : ZMod 35814241) ^ 263340 = (26 : ZMod 35814241) ^ (131670 + 131670) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 131670 * (26 : ZMod 35814241) ^ 131670 := by rw [pow_add]
          _ = 30169228 := by rw [factor_5_17]; decide
      have factor_5_19 : (26 : ZMod 35814241) ^ 526680 = 21069527 := by
        calc
          (26 : ZMod 35814241) ^ 526680 = (26 : ZMod 35814241) ^ (263340 + 263340) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 263340 * (26 : ZMod 35814241) ^ 263340 := by rw [pow_add]
          _ = 21069527 := by rw [factor_5_18]; decide
      have factor_5_20 : (26 : ZMod 35814241) ^ 1053360 = 1446601 := by
        calc
          (26 : ZMod 35814241) ^ 1053360 = (26 : ZMod 35814241) ^ (526680 + 526680) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 526680 * (26 : ZMod 35814241) ^ 526680 := by rw [pow_add]
          _ = 1446601 := by rw [factor_5_19]; decide
      have factor_5_21 : (26 : ZMod 35814241) ^ 2106720 = 28351571 := by
        calc
          (26 : ZMod 35814241) ^ 2106720 = (26 : ZMod 35814241) ^ (1053360 + 1053360) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 1053360 * (26 : ZMod 35814241) ^ 1053360 := by rw [pow_add]
          _ = 28351571 := by rw [factor_5_20]; decide
      change (26 : ZMod 35814241) ^ 2106720 ≠ 1
      rw [factor_5_21]
      decide
    ·
      have factor_6_0 : (26 : ZMod 35814241) ^ 1 = 26 := by norm_num
      have factor_6_1 : (26 : ZMod 35814241) ^ 3 = 17576 := by
        calc
          (26 : ZMod 35814241) ^ 3 = (26 : ZMod 35814241) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 1 * (26 : ZMod 35814241) ^ 1) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 17576 := by rw [factor_6_0]; decide
      have factor_6_2 : (26 : ZMod 35814241) ^ 7 = 9420192 := by
        calc
          (26 : ZMod 35814241) ^ 7 = (26 : ZMod 35814241) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 3 * (26 : ZMod 35814241) ^ 3) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 9420192 := by rw [factor_6_1]; decide
      have factor_6_3 : (26 : ZMod 35814241) ^ 14 = 28180679 := by
        calc
          (26 : ZMod 35814241) ^ 14 = (26 : ZMod 35814241) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 7 * (26 : ZMod 35814241) ^ 7 := by rw [pow_add]
          _ = 28180679 := by rw [factor_6_2]; decide
      have factor_6_4 : (26 : ZMod 35814241) ^ 28 = 30316963 := by
        calc
          (26 : ZMod 35814241) ^ 28 = (26 : ZMod 35814241) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 14 * (26 : ZMod 35814241) ^ 14 := by rw [pow_add]
          _ = 30316963 := by rw [factor_6_3]; decide
      have factor_6_5 : (26 : ZMod 35814241) ^ 57 = 15305138 := by
        calc
          (26 : ZMod 35814241) ^ 57 = (26 : ZMod 35814241) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 28 * (26 : ZMod 35814241) ^ 28) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 15305138 := by rw [factor_6_4]; decide
      have factor_6_6 : (26 : ZMod 35814241) ^ 115 = 13524371 := by
        calc
          (26 : ZMod 35814241) ^ 115 = (26 : ZMod 35814241) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 57 * (26 : ZMod 35814241) ^ 57) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 13524371 := by rw [factor_6_5]; decide
      have factor_6_7 : (26 : ZMod 35814241) ^ 230 = 17465214 := by
        calc
          (26 : ZMod 35814241) ^ 230 = (26 : ZMod 35814241) ^ (115 + 115) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 115 * (26 : ZMod 35814241) ^ 115 := by rw [pow_add]
          _ = 17465214 := by rw [factor_6_6]; decide
      have factor_6_8 : (26 : ZMod 35814241) ^ 460 = 13159250 := by
        calc
          (26 : ZMod 35814241) ^ 460 = (26 : ZMod 35814241) ^ (230 + 230) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 230 * (26 : ZMod 35814241) ^ 230 := by rw [pow_add]
          _ = 13159250 := by rw [factor_6_7]; decide
      have factor_6_9 : (26 : ZMod 35814241) ^ 920 = 29946749 := by
        calc
          (26 : ZMod 35814241) ^ 920 = (26 : ZMod 35814241) ^ (460 + 460) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 460 * (26 : ZMod 35814241) ^ 460 := by rw [pow_add]
          _ = 29946749 := by rw [factor_6_8]; decide
      have factor_6_10 : (26 : ZMod 35814241) ^ 1840 = 20410066 := by
        calc
          (26 : ZMod 35814241) ^ 1840 = (26 : ZMod 35814241) ^ (920 + 920) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 920 * (26 : ZMod 35814241) ^ 920 := by rw [pow_add]
          _ = 20410066 := by rw [factor_6_9]; decide
      have factor_6_11 : (26 : ZMod 35814241) ^ 3681 = 26228588 := by
        calc
          (26 : ZMod 35814241) ^ 3681 = (26 : ZMod 35814241) ^ (1840 + 1840 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 1840 * (26 : ZMod 35814241) ^ 1840) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 26228588 := by rw [factor_6_10]; decide
      have factor_6_12 : (26 : ZMod 35814241) ^ 7363 = 21930993 := by
        calc
          (26 : ZMod 35814241) ^ 7363 = (26 : ZMod 35814241) ^ (3681 + 3681 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 3681 * (26 : ZMod 35814241) ^ 3681) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 21930993 := by rw [factor_6_11]; decide
      have factor_6_13 : (26 : ZMod 35814241) ^ 14726 = 30029319 := by
        calc
          (26 : ZMod 35814241) ^ 14726 = (26 : ZMod 35814241) ^ (7363 + 7363) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 7363 * (26 : ZMod 35814241) ^ 7363 := by rw [pow_add]
          _ = 30029319 := by rw [factor_6_12]; decide
      have factor_6_14 : (26 : ZMod 35814241) ^ 29452 = 30170551 := by
        calc
          (26 : ZMod 35814241) ^ 29452 = (26 : ZMod 35814241) ^ (14726 + 14726) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 14726 * (26 : ZMod 35814241) ^ 14726 := by rw [pow_add]
          _ = 30170551 := by rw [factor_6_13]; decide
      have factor_6_15 : (26 : ZMod 35814241) ^ 58905 = 35603456 := by
        calc
          (26 : ZMod 35814241) ^ 58905 = (26 : ZMod 35814241) ^ (29452 + 29452 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = ((26 : ZMod 35814241) ^ 29452 * (26 : ZMod 35814241) ^ 29452) * (26 : ZMod 35814241) := by rw [pow_succ, pow_add]
          _ = 35603456 := by rw [factor_6_14]; decide
      have factor_6_16 : (26 : ZMod 35814241) ^ 117810 = 20657385 := by
        calc
          (26 : ZMod 35814241) ^ 117810 = (26 : ZMod 35814241) ^ (58905 + 58905) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 58905 * (26 : ZMod 35814241) ^ 58905 := by rw [pow_add]
          _ = 20657385 := by rw [factor_6_15]; decide
      have factor_6_17 : (26 : ZMod 35814241) ^ 235620 = 13981441 := by
        calc
          (26 : ZMod 35814241) ^ 235620 = (26 : ZMod 35814241) ^ (117810 + 117810) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 117810 * (26 : ZMod 35814241) ^ 117810 := by rw [pow_add]
          _ = 13981441 := by rw [factor_6_16]; decide
      have factor_6_18 : (26 : ZMod 35814241) ^ 471240 = 11052378 := by
        calc
          (26 : ZMod 35814241) ^ 471240 = (26 : ZMod 35814241) ^ (235620 + 235620) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 235620 * (26 : ZMod 35814241) ^ 235620 := by rw [pow_add]
          _ = 11052378 := by rw [factor_6_17]; decide
      have factor_6_19 : (26 : ZMod 35814241) ^ 942480 = 25323289 := by
        calc
          (26 : ZMod 35814241) ^ 942480 = (26 : ZMod 35814241) ^ (471240 + 471240) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 471240 * (26 : ZMod 35814241) ^ 471240 := by rw [pow_add]
          _ = 25323289 := by rw [factor_6_18]; decide
      have factor_6_20 : (26 : ZMod 35814241) ^ 1884960 = 10319783 := by
        calc
          (26 : ZMod 35814241) ^ 1884960 = (26 : ZMod 35814241) ^ (942480 + 942480) :=
            congrArg (fun n : ℕ => (26 : ZMod 35814241) ^ n) (by norm_num)
          _ = (26 : ZMod 35814241) ^ 942480 * (26 : ZMod 35814241) ^ 942480 := by rw [pow_add]
          _ = 10319783 := by rw [factor_6_19]; decide
      change (26 : ZMod 35814241) ^ 1884960 ≠ 1
      rw [factor_6_20]
      decide

#print axioms prime_lucas_35814241

end TotientTailPeriodKiller
end Erdos249257
