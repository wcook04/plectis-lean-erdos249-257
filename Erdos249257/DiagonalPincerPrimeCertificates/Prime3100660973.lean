import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_3100660973 : Nat.Prime 3100660973 := by
  apply lucas_primality 3100660973 (2 : ZMod 3100660973)
  ·
      have fermat_0 : (2 : ZMod 3100660973) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 3100660973) ^ 2 = 4 := by
        calc
          (2 : ZMod 3100660973) ^ 2 = (2 : ZMod 3100660973) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 1 * (2 : ZMod 3100660973) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 3100660973) ^ 5 = 32 := by
        calc
          (2 : ZMod 3100660973) ^ 5 = (2 : ZMod 3100660973) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 2 * (2 : ZMod 3100660973) ^ 2) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 3100660973) ^ 11 = 2048 := by
        calc
          (2 : ZMod 3100660973) ^ 11 = (2 : ZMod 3100660973) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 5 * (2 : ZMod 3100660973) ^ 5) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 3100660973) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 3100660973) ^ 23 = (2 : ZMod 3100660973) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 11 * (2 : ZMod 3100660973) ^ 11) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 3100660973) ^ 46 = 2344056402 := by
        calc
          (2 : ZMod 3100660973) ^ 46 = (2 : ZMod 3100660973) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 23 * (2 : ZMod 3100660973) ^ 23 := by rw [pow_add]
          _ = 2344056402 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 3100660973) ^ 92 = 1748671174 := by
        calc
          (2 : ZMod 3100660973) ^ 92 = (2 : ZMod 3100660973) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 46 * (2 : ZMod 3100660973) ^ 46 := by rw [pow_add]
          _ = 1748671174 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 3100660973) ^ 184 = 2278081594 := by
        calc
          (2 : ZMod 3100660973) ^ 184 = (2 : ZMod 3100660973) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 92 * (2 : ZMod 3100660973) ^ 92 := by rw [pow_add]
          _ = 2278081594 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 3100660973) ^ 369 = 1438180827 := by
        calc
          (2 : ZMod 3100660973) ^ 369 = (2 : ZMod 3100660973) ^ (184 + 184 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 184 * (2 : ZMod 3100660973) ^ 184) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 1438180827 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 3100660973) ^ 739 = 1849932399 := by
        calc
          (2 : ZMod 3100660973) ^ 739 = (2 : ZMod 3100660973) ^ (369 + 369 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 369 * (2 : ZMod 3100660973) ^ 369) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 1849932399 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 3100660973) ^ 1478 = 933610762 := by
        calc
          (2 : ZMod 3100660973) ^ 1478 = (2 : ZMod 3100660973) ^ (739 + 739) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 739 * (2 : ZMod 3100660973) ^ 739 := by rw [pow_add]
          _ = 933610762 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 3100660973) ^ 2957 = 1645970438 := by
        calc
          (2 : ZMod 3100660973) ^ 2957 = (2 : ZMod 3100660973) ^ (1478 + 1478 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 1478 * (2 : ZMod 3100660973) ^ 1478) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 1645970438 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 3100660973) ^ 5914 = 66831541 := by
        calc
          (2 : ZMod 3100660973) ^ 5914 = (2 : ZMod 3100660973) ^ (2957 + 2957) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 2957 * (2 : ZMod 3100660973) ^ 2957 := by rw [pow_add]
          _ = 66831541 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 3100660973) ^ 11828 = 2351403749 := by
        calc
          (2 : ZMod 3100660973) ^ 11828 = (2 : ZMod 3100660973) ^ (5914 + 5914) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 5914 * (2 : ZMod 3100660973) ^ 5914 := by rw [pow_add]
          _ = 2351403749 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 3100660973) ^ 23656 = 1156719209 := by
        calc
          (2 : ZMod 3100660973) ^ 23656 = (2 : ZMod 3100660973) ^ (11828 + 11828) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 11828 * (2 : ZMod 3100660973) ^ 11828 := by rw [pow_add]
          _ = 1156719209 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 3100660973) ^ 47312 = 51825014 := by
        calc
          (2 : ZMod 3100660973) ^ 47312 = (2 : ZMod 3100660973) ^ (23656 + 23656) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 23656 * (2 : ZMod 3100660973) ^ 23656 := by rw [pow_add]
          _ = 51825014 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 3100660973) ^ 94624 = 2333355920 := by
        calc
          (2 : ZMod 3100660973) ^ 94624 = (2 : ZMod 3100660973) ^ (47312 + 47312) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 47312 * (2 : ZMod 3100660973) ^ 47312 := by rw [pow_add]
          _ = 2333355920 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 3100660973) ^ 189249 = 1903845232 := by
        calc
          (2 : ZMod 3100660973) ^ 189249 = (2 : ZMod 3100660973) ^ (94624 + 94624 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 94624 * (2 : ZMod 3100660973) ^ 94624) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 1903845232 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 3100660973) ^ 378498 = 680312171 := by
        calc
          (2 : ZMod 3100660973) ^ 378498 = (2 : ZMod 3100660973) ^ (189249 + 189249) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 189249 * (2 : ZMod 3100660973) ^ 189249 := by rw [pow_add]
          _ = 680312171 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 3100660973) ^ 756997 = 237598674 := by
        calc
          (2 : ZMod 3100660973) ^ 756997 = (2 : ZMod 3100660973) ^ (378498 + 378498 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 378498 * (2 : ZMod 3100660973) ^ 378498) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 237598674 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 3100660973) ^ 1513994 = 180037011 := by
        calc
          (2 : ZMod 3100660973) ^ 1513994 = (2 : ZMod 3100660973) ^ (756997 + 756997) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 756997 * (2 : ZMod 3100660973) ^ 756997 := by rw [pow_add]
          _ = 180037011 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 3100660973) ^ 3027989 = 3056523070 := by
        calc
          (2 : ZMod 3100660973) ^ 3027989 = (2 : ZMod 3100660973) ^ (1513994 + 1513994 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 1513994 * (2 : ZMod 3100660973) ^ 1513994) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 3056523070 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 3100660973) ^ 6055978 = 2990579563 := by
        calc
          (2 : ZMod 3100660973) ^ 6055978 = (2 : ZMod 3100660973) ^ (3027989 + 3027989) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 3027989 * (2 : ZMod 3100660973) ^ 3027989 := by rw [pow_add]
          _ = 2990579563 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 3100660973) ^ 12111956 = 431416744 := by
        calc
          (2 : ZMod 3100660973) ^ 12111956 = (2 : ZMod 3100660973) ^ (6055978 + 6055978) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 6055978 * (2 : ZMod 3100660973) ^ 6055978 := by rw [pow_add]
          _ = 431416744 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 3100660973) ^ 24223913 = 2421005340 := by
        calc
          (2 : ZMod 3100660973) ^ 24223913 = (2 : ZMod 3100660973) ^ (12111956 + 12111956 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 12111956 * (2 : ZMod 3100660973) ^ 12111956) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 2421005340 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 3100660973) ^ 48447827 = 1122946649 := by
        calc
          (2 : ZMod 3100660973) ^ 48447827 = (2 : ZMod 3100660973) ^ (24223913 + 24223913 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 24223913 * (2 : ZMod 3100660973) ^ 24223913) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 1122946649 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 3100660973) ^ 96895655 = 2200262162 := by
        calc
          (2 : ZMod 3100660973) ^ 96895655 = (2 : ZMod 3100660973) ^ (48447827 + 48447827 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 48447827 * (2 : ZMod 3100660973) ^ 48447827) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 2200262162 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 3100660973) ^ 193791310 = 1556888905 := by
        calc
          (2 : ZMod 3100660973) ^ 193791310 = (2 : ZMod 3100660973) ^ (96895655 + 96895655) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 96895655 * (2 : ZMod 3100660973) ^ 96895655 := by rw [pow_add]
          _ = 1556888905 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 3100660973) ^ 387582621 = 2518737859 := by
        calc
          (2 : ZMod 3100660973) ^ 387582621 = (2 : ZMod 3100660973) ^ (193791310 + 193791310 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 193791310 * (2 : ZMod 3100660973) ^ 193791310) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 2518737859 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 3100660973) ^ 775165243 = 1163846227 := by
        calc
          (2 : ZMod 3100660973) ^ 775165243 = (2 : ZMod 3100660973) ^ (387582621 + 387582621 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 387582621 * (2 : ZMod 3100660973) ^ 387582621) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 1163846227 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 3100660973) ^ 1550330486 = 3100660972 := by
        calc
          (2 : ZMod 3100660973) ^ 1550330486 = (2 : ZMod 3100660973) ^ (775165243 + 775165243) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 775165243 * (2 : ZMod 3100660973) ^ 775165243 := by rw [pow_add]
          _ = 3100660972 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 3100660973) ^ 3100660972 = 1 := by
        calc
          (2 : ZMod 3100660973) ^ 3100660972 = (2 : ZMod 3100660973) ^ (1550330486 + 1550330486) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 1550330486 * (2 : ZMod 3100660973) ^ 1550330486 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (373, 1), (2078191, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (373, 1), (2078191, 1)] : List FactorBlock).map factorBlockValue).prod = 3100660973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 3100660973) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 3100660973) ^ 2 = 4 := by
        calc
          (2 : ZMod 3100660973) ^ 2 = (2 : ZMod 3100660973) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 1 * (2 : ZMod 3100660973) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 3100660973) ^ 5 = 32 := by
        calc
          (2 : ZMod 3100660973) ^ 5 = (2 : ZMod 3100660973) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 2 * (2 : ZMod 3100660973) ^ 2) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 3100660973) ^ 11 = 2048 := by
        calc
          (2 : ZMod 3100660973) ^ 11 = (2 : ZMod 3100660973) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 5 * (2 : ZMod 3100660973) ^ 5) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 3100660973) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 3100660973) ^ 23 = (2 : ZMod 3100660973) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 11 * (2 : ZMod 3100660973) ^ 11) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 3100660973) ^ 46 = 2344056402 := by
        calc
          (2 : ZMod 3100660973) ^ 46 = (2 : ZMod 3100660973) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 23 * (2 : ZMod 3100660973) ^ 23 := by rw [pow_add]
          _ = 2344056402 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 3100660973) ^ 92 = 1748671174 := by
        calc
          (2 : ZMod 3100660973) ^ 92 = (2 : ZMod 3100660973) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 46 * (2 : ZMod 3100660973) ^ 46 := by rw [pow_add]
          _ = 1748671174 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 3100660973) ^ 184 = 2278081594 := by
        calc
          (2 : ZMod 3100660973) ^ 184 = (2 : ZMod 3100660973) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 92 * (2 : ZMod 3100660973) ^ 92 := by rw [pow_add]
          _ = 2278081594 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 3100660973) ^ 369 = 1438180827 := by
        calc
          (2 : ZMod 3100660973) ^ 369 = (2 : ZMod 3100660973) ^ (184 + 184 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 184 * (2 : ZMod 3100660973) ^ 184) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 1438180827 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 3100660973) ^ 739 = 1849932399 := by
        calc
          (2 : ZMod 3100660973) ^ 739 = (2 : ZMod 3100660973) ^ (369 + 369 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 369 * (2 : ZMod 3100660973) ^ 369) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 1849932399 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 3100660973) ^ 1478 = 933610762 := by
        calc
          (2 : ZMod 3100660973) ^ 1478 = (2 : ZMod 3100660973) ^ (739 + 739) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 739 * (2 : ZMod 3100660973) ^ 739 := by rw [pow_add]
          _ = 933610762 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 3100660973) ^ 2957 = 1645970438 := by
        calc
          (2 : ZMod 3100660973) ^ 2957 = (2 : ZMod 3100660973) ^ (1478 + 1478 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 1478 * (2 : ZMod 3100660973) ^ 1478) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 1645970438 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 3100660973) ^ 5914 = 66831541 := by
        calc
          (2 : ZMod 3100660973) ^ 5914 = (2 : ZMod 3100660973) ^ (2957 + 2957) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 2957 * (2 : ZMod 3100660973) ^ 2957 := by rw [pow_add]
          _ = 66831541 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 3100660973) ^ 11828 = 2351403749 := by
        calc
          (2 : ZMod 3100660973) ^ 11828 = (2 : ZMod 3100660973) ^ (5914 + 5914) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 5914 * (2 : ZMod 3100660973) ^ 5914 := by rw [pow_add]
          _ = 2351403749 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 3100660973) ^ 23656 = 1156719209 := by
        calc
          (2 : ZMod 3100660973) ^ 23656 = (2 : ZMod 3100660973) ^ (11828 + 11828) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 11828 * (2 : ZMod 3100660973) ^ 11828 := by rw [pow_add]
          _ = 1156719209 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 3100660973) ^ 47312 = 51825014 := by
        calc
          (2 : ZMod 3100660973) ^ 47312 = (2 : ZMod 3100660973) ^ (23656 + 23656) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 23656 * (2 : ZMod 3100660973) ^ 23656 := by rw [pow_add]
          _ = 51825014 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 3100660973) ^ 94624 = 2333355920 := by
        calc
          (2 : ZMod 3100660973) ^ 94624 = (2 : ZMod 3100660973) ^ (47312 + 47312) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 47312 * (2 : ZMod 3100660973) ^ 47312 := by rw [pow_add]
          _ = 2333355920 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 3100660973) ^ 189249 = 1903845232 := by
        calc
          (2 : ZMod 3100660973) ^ 189249 = (2 : ZMod 3100660973) ^ (94624 + 94624 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 94624 * (2 : ZMod 3100660973) ^ 94624) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 1903845232 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 3100660973) ^ 378498 = 680312171 := by
        calc
          (2 : ZMod 3100660973) ^ 378498 = (2 : ZMod 3100660973) ^ (189249 + 189249) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 189249 * (2 : ZMod 3100660973) ^ 189249 := by rw [pow_add]
          _ = 680312171 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 3100660973) ^ 756997 = 237598674 := by
        calc
          (2 : ZMod 3100660973) ^ 756997 = (2 : ZMod 3100660973) ^ (378498 + 378498 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 378498 * (2 : ZMod 3100660973) ^ 378498) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 237598674 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 3100660973) ^ 1513994 = 180037011 := by
        calc
          (2 : ZMod 3100660973) ^ 1513994 = (2 : ZMod 3100660973) ^ (756997 + 756997) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 756997 * (2 : ZMod 3100660973) ^ 756997 := by rw [pow_add]
          _ = 180037011 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 3100660973) ^ 3027989 = 3056523070 := by
        calc
          (2 : ZMod 3100660973) ^ 3027989 = (2 : ZMod 3100660973) ^ (1513994 + 1513994 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 1513994 * (2 : ZMod 3100660973) ^ 1513994) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 3056523070 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 3100660973) ^ 6055978 = 2990579563 := by
        calc
          (2 : ZMod 3100660973) ^ 6055978 = (2 : ZMod 3100660973) ^ (3027989 + 3027989) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 3027989 * (2 : ZMod 3100660973) ^ 3027989 := by rw [pow_add]
          _ = 2990579563 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 3100660973) ^ 12111956 = 431416744 := by
        calc
          (2 : ZMod 3100660973) ^ 12111956 = (2 : ZMod 3100660973) ^ (6055978 + 6055978) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 6055978 * (2 : ZMod 3100660973) ^ 6055978 := by rw [pow_add]
          _ = 431416744 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 3100660973) ^ 24223913 = 2421005340 := by
        calc
          (2 : ZMod 3100660973) ^ 24223913 = (2 : ZMod 3100660973) ^ (12111956 + 12111956 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 12111956 * (2 : ZMod 3100660973) ^ 12111956) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 2421005340 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 3100660973) ^ 48447827 = 1122946649 := by
        calc
          (2 : ZMod 3100660973) ^ 48447827 = (2 : ZMod 3100660973) ^ (24223913 + 24223913 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 24223913 * (2 : ZMod 3100660973) ^ 24223913) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 1122946649 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 3100660973) ^ 96895655 = 2200262162 := by
        calc
          (2 : ZMod 3100660973) ^ 96895655 = (2 : ZMod 3100660973) ^ (48447827 + 48447827 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 48447827 * (2 : ZMod 3100660973) ^ 48447827) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 2200262162 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 3100660973) ^ 193791310 = 1556888905 := by
        calc
          (2 : ZMod 3100660973) ^ 193791310 = (2 : ZMod 3100660973) ^ (96895655 + 96895655) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 96895655 * (2 : ZMod 3100660973) ^ 96895655 := by rw [pow_add]
          _ = 1556888905 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 3100660973) ^ 387582621 = 2518737859 := by
        calc
          (2 : ZMod 3100660973) ^ 387582621 = (2 : ZMod 3100660973) ^ (193791310 + 193791310 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 193791310 * (2 : ZMod 3100660973) ^ 193791310) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 2518737859 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 3100660973) ^ 775165243 = 1163846227 := by
        calc
          (2 : ZMod 3100660973) ^ 775165243 = (2 : ZMod 3100660973) ^ (387582621 + 387582621 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 387582621 * (2 : ZMod 3100660973) ^ 387582621) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 1163846227 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 3100660973) ^ 1550330486 = 3100660972 := by
        calc
          (2 : ZMod 3100660973) ^ 1550330486 = (2 : ZMod 3100660973) ^ (775165243 + 775165243) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 775165243 * (2 : ZMod 3100660973) ^ 775165243 := by rw [pow_add]
          _ = 3100660972 := by rw [factor_0_29]; decide
      change (2 : ZMod 3100660973) ^ 1550330486 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (2 : ZMod 3100660973) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 3100660973) ^ 3 = 8 := by
        calc
          (2 : ZMod 3100660973) ^ 3 = (2 : ZMod 3100660973) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 1 * (2 : ZMod 3100660973) ^ 1) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 3100660973) ^ 7 = 128 := by
        calc
          (2 : ZMod 3100660973) ^ 7 = (2 : ZMod 3100660973) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 3 * (2 : ZMod 3100660973) ^ 3) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 3100660973) ^ 15 = 32768 := by
        calc
          (2 : ZMod 3100660973) ^ 15 = (2 : ZMod 3100660973) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 7 * (2 : ZMod 3100660973) ^ 7) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 3100660973) ^ 31 = 2147483648 := by
        calc
          (2 : ZMod 3100660973) ^ 31 = (2 : ZMod 3100660973) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 15 * (2 : ZMod 3100660973) ^ 15) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 2147483648 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 3100660973) ^ 63 = 1866230320 := by
        calc
          (2 : ZMod 3100660973) ^ 63 = (2 : ZMod 3100660973) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 31 * (2 : ZMod 3100660973) ^ 31) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 1866230320 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 3100660973) ^ 126 = 1855687443 := by
        calc
          (2 : ZMod 3100660973) ^ 126 = (2 : ZMod 3100660973) ^ (63 + 63) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 63 * (2 : ZMod 3100660973) ^ 63 := by rw [pow_add]
          _ = 1855687443 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 3100660973) ^ 253 = 2144013680 := by
        calc
          (2 : ZMod 3100660973) ^ 253 = (2 : ZMod 3100660973) ^ (126 + 126 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 126 * (2 : ZMod 3100660973) ^ 126) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 2144013680 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 3100660973) ^ 507 = 1896476752 := by
        calc
          (2 : ZMod 3100660973) ^ 507 = (2 : ZMod 3100660973) ^ (253 + 253 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 253 * (2 : ZMod 3100660973) ^ 253) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 1896476752 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 3100660973) ^ 1014 = 507176261 := by
        calc
          (2 : ZMod 3100660973) ^ 1014 = (2 : ZMod 3100660973) ^ (507 + 507) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 507 * (2 : ZMod 3100660973) ^ 507 := by rw [pow_add]
          _ = 507176261 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 3100660973) ^ 2029 = 2515090674 := by
        calc
          (2 : ZMod 3100660973) ^ 2029 = (2 : ZMod 3100660973) ^ (1014 + 1014 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 1014 * (2 : ZMod 3100660973) ^ 1014) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 2515090674 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 3100660973) ^ 4058 = 196727484 := by
        calc
          (2 : ZMod 3100660973) ^ 4058 = (2 : ZMod 3100660973) ^ (2029 + 2029) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 2029 * (2 : ZMod 3100660973) ^ 2029 := by rw [pow_add]
          _ = 196727484 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 3100660973) ^ 8117 = 3011218471 := by
        calc
          (2 : ZMod 3100660973) ^ 8117 = (2 : ZMod 3100660973) ^ (4058 + 4058 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 4058 * (2 : ZMod 3100660973) ^ 4058) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 3011218471 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 3100660973) ^ 16235 = 98299463 := by
        calc
          (2 : ZMod 3100660973) ^ 16235 = (2 : ZMod 3100660973) ^ (8117 + 8117 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 8117 * (2 : ZMod 3100660973) ^ 8117) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 98299463 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 3100660973) ^ 32471 = 1689235313 := by
        calc
          (2 : ZMod 3100660973) ^ 32471 = (2 : ZMod 3100660973) ^ (16235 + 16235 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 16235 * (2 : ZMod 3100660973) ^ 16235) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 1689235313 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 3100660973) ^ 64943 = 697863679 := by
        calc
          (2 : ZMod 3100660973) ^ 64943 = (2 : ZMod 3100660973) ^ (32471 + 32471 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 32471 * (2 : ZMod 3100660973) ^ 32471) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 697863679 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 3100660973) ^ 129886 = 2153255157 := by
        calc
          (2 : ZMod 3100660973) ^ 129886 = (2 : ZMod 3100660973) ^ (64943 + 64943) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 64943 * (2 : ZMod 3100660973) ^ 64943 := by rw [pow_add]
          _ = 2153255157 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 3100660973) ^ 259773 = 2718110550 := by
        calc
          (2 : ZMod 3100660973) ^ 259773 = (2 : ZMod 3100660973) ^ (129886 + 129886 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 129886 * (2 : ZMod 3100660973) ^ 129886) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 2718110550 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 3100660973) ^ 519547 = 140356888 := by
        calc
          (2 : ZMod 3100660973) ^ 519547 = (2 : ZMod 3100660973) ^ (259773 + 259773 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 259773 * (2 : ZMod 3100660973) ^ 259773) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 140356888 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 3100660973) ^ 1039095 = 631534196 := by
        calc
          (2 : ZMod 3100660973) ^ 1039095 = (2 : ZMod 3100660973) ^ (519547 + 519547 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 519547 * (2 : ZMod 3100660973) ^ 519547) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 631534196 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 3100660973) ^ 2078191 = 2121272877 := by
        calc
          (2 : ZMod 3100660973) ^ 2078191 = (2 : ZMod 3100660973) ^ (1039095 + 1039095 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 1039095 * (2 : ZMod 3100660973) ^ 1039095) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 2121272877 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 3100660973) ^ 4156382 = 2022864953 := by
        calc
          (2 : ZMod 3100660973) ^ 4156382 = (2 : ZMod 3100660973) ^ (2078191 + 2078191) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 2078191 * (2 : ZMod 3100660973) ^ 2078191 := by rw [pow_add]
          _ = 2022864953 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 3100660973) ^ 8312764 = 1710316398 := by
        calc
          (2 : ZMod 3100660973) ^ 8312764 = (2 : ZMod 3100660973) ^ (4156382 + 4156382) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 4156382 * (2 : ZMod 3100660973) ^ 4156382 := by rw [pow_add]
          _ = 1710316398 := by rw [factor_1_21]; decide
      change (2 : ZMod 3100660973) ^ 8312764 ≠ 1
      rw [factor_1_22]
      decide
    ·
      have factor_2_0 : (2 : ZMod 3100660973) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 3100660973) ^ 2 = 4 := by
        calc
          (2 : ZMod 3100660973) ^ 2 = (2 : ZMod 3100660973) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 1 * (2 : ZMod 3100660973) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 3100660973) ^ 5 = 32 := by
        calc
          (2 : ZMod 3100660973) ^ 5 = (2 : ZMod 3100660973) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 2 * (2 : ZMod 3100660973) ^ 2) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 3100660973) ^ 11 = 2048 := by
        calc
          (2 : ZMod 3100660973) ^ 11 = (2 : ZMod 3100660973) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 5 * (2 : ZMod 3100660973) ^ 5) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 3100660973) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 3100660973) ^ 23 = (2 : ZMod 3100660973) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 11 * (2 : ZMod 3100660973) ^ 11) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 3100660973) ^ 46 = 2344056402 := by
        calc
          (2 : ZMod 3100660973) ^ 46 = (2 : ZMod 3100660973) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 23 * (2 : ZMod 3100660973) ^ 23 := by rw [pow_add]
          _ = 2344056402 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 3100660973) ^ 93 = 396681375 := by
        calc
          (2 : ZMod 3100660973) ^ 93 = (2 : ZMod 3100660973) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 46 * (2 : ZMod 3100660973) ^ 46) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 396681375 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 3100660973) ^ 186 = 2911004430 := by
        calc
          (2 : ZMod 3100660973) ^ 186 = (2 : ZMod 3100660973) ^ (93 + 93) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 93 * (2 : ZMod 3100660973) ^ 93 := by rw [pow_add]
          _ = 2911004430 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 3100660973) ^ 373 = 1306266421 := by
        calc
          (2 : ZMod 3100660973) ^ 373 = (2 : ZMod 3100660973) ^ (186 + 186 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = ((2 : ZMod 3100660973) ^ 186 * (2 : ZMod 3100660973) ^ 186) * (2 : ZMod 3100660973) := by rw [pow_succ, pow_add]
          _ = 1306266421 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 3100660973) ^ 746 = 1141113124 := by
        calc
          (2 : ZMod 3100660973) ^ 746 = (2 : ZMod 3100660973) ^ (373 + 373) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 373 * (2 : ZMod 3100660973) ^ 373 := by rw [pow_add]
          _ = 1141113124 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 3100660973) ^ 1492 = 718144799 := by
        calc
          (2 : ZMod 3100660973) ^ 1492 = (2 : ZMod 3100660973) ^ (746 + 746) :=
            congrArg (fun n : ℕ => (2 : ZMod 3100660973) ^ n) (by norm_num)
          _ = (2 : ZMod 3100660973) ^ 746 * (2 : ZMod 3100660973) ^ 746 := by rw [pow_add]
          _ = 718144799 := by rw [factor_2_9]; decide
      change (2 : ZMod 3100660973) ^ 1492 ≠ 1
      rw [factor_2_10]
      decide

#print axioms prime_lucas_3100660973

end TotientTailPeriodKiller
end Erdos249257
