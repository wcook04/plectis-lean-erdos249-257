import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_689125061 : Nat.Prime 689125061 := by
  apply lucas_primality 689125061 (2 : ZMod 689125061)
  ·
      have fermat_0 : (2 : ZMod 689125061) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 689125061) ^ 2 = 4 := by
        calc
          (2 : ZMod 689125061) ^ 2 = (2 : ZMod 689125061) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 1 * (2 : ZMod 689125061) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 689125061) ^ 5 = 32 := by
        calc
          (2 : ZMod 689125061) ^ 5 = (2 : ZMod 689125061) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 2 * (2 : ZMod 689125061) ^ 2) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 689125061) ^ 10 = 1024 := by
        calc
          (2 : ZMod 689125061) ^ 10 = (2 : ZMod 689125061) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 5 * (2 : ZMod 689125061) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 689125061) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 689125061) ^ 20 = (2 : ZMod 689125061) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 10 * (2 : ZMod 689125061) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 689125061) ^ 41 = 25185901 := by
        calc
          (2 : ZMod 689125061) ^ 41 = (2 : ZMod 689125061) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 20 * (2 : ZMod 689125061) ^ 20) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 25185901 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 689125061) ^ 82 = 327407216 := by
        calc
          (2 : ZMod 689125061) ^ 82 = (2 : ZMod 689125061) ^ (41 + 41) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 41 * (2 : ZMod 689125061) ^ 41 := by rw [pow_add]
          _ = 327407216 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 689125061) ^ 164 = 3511375 := by
        calc
          (2 : ZMod 689125061) ^ 164 = (2 : ZMod 689125061) ^ (82 + 82) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 82 * (2 : ZMod 689125061) ^ 82 := by rw [pow_add]
          _ = 3511375 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 689125061) ^ 328 = 617924274 := by
        calc
          (2 : ZMod 689125061) ^ 328 = (2 : ZMod 689125061) ^ (164 + 164) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 164 * (2 : ZMod 689125061) ^ 164 := by rw [pow_add]
          _ = 617924274 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 689125061) ^ 657 = 225095128 := by
        calc
          (2 : ZMod 689125061) ^ 657 = (2 : ZMod 689125061) ^ (328 + 328 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 328 * (2 : ZMod 689125061) ^ 328) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 225095128 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 689125061) ^ 1314 = 597195595 := by
        calc
          (2 : ZMod 689125061) ^ 1314 = (2 : ZMod 689125061) ^ (657 + 657) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 657 * (2 : ZMod 689125061) ^ 657 := by rw [pow_add]
          _ = 597195595 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 689125061) ^ 2628 = 109101841 := by
        calc
          (2 : ZMod 689125061) ^ 2628 = (2 : ZMod 689125061) ^ (1314 + 1314) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 1314 * (2 : ZMod 689125061) ^ 1314 := by rw [pow_add]
          _ = 109101841 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 689125061) ^ 5257 = 26380614 := by
        calc
          (2 : ZMod 689125061) ^ 5257 = (2 : ZMod 689125061) ^ (2628 + 2628 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 2628 * (2 : ZMod 689125061) ^ 2628) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 26380614 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 689125061) ^ 10515 = 154703083 := by
        calc
          (2 : ZMod 689125061) ^ 10515 = (2 : ZMod 689125061) ^ (5257 + 5257 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 5257 * (2 : ZMod 689125061) ^ 5257) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 154703083 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 689125061) ^ 21030 = 658198801 := by
        calc
          (2 : ZMod 689125061) ^ 21030 = (2 : ZMod 689125061) ^ (10515 + 10515) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 10515 * (2 : ZMod 689125061) ^ 10515 := by rw [pow_add]
          _ = 658198801 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 689125061) ^ 42060 = 331051005 := by
        calc
          (2 : ZMod 689125061) ^ 42060 = (2 : ZMod 689125061) ^ (21030 + 21030) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 21030 * (2 : ZMod 689125061) ^ 21030 := by rw [pow_add]
          _ = 331051005 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 689125061) ^ 84121 = 410541896 := by
        calc
          (2 : ZMod 689125061) ^ 84121 = (2 : ZMod 689125061) ^ (42060 + 42060 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 42060 * (2 : ZMod 689125061) ^ 42060) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 410541896 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 689125061) ^ 168243 = 194690657 := by
        calc
          (2 : ZMod 689125061) ^ 168243 = (2 : ZMod 689125061) ^ (84121 + 84121 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 84121 * (2 : ZMod 689125061) ^ 84121) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 194690657 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 689125061) ^ 336486 = 375113875 := by
        calc
          (2 : ZMod 689125061) ^ 336486 = (2 : ZMod 689125061) ^ (168243 + 168243) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 168243 * (2 : ZMod 689125061) ^ 168243 := by rw [pow_add]
          _ = 375113875 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 689125061) ^ 672973 = 146585113 := by
        calc
          (2 : ZMod 689125061) ^ 672973 = (2 : ZMod 689125061) ^ (336486 + 336486 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 336486 * (2 : ZMod 689125061) ^ 336486) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 146585113 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 689125061) ^ 1345947 = 602436738 := by
        calc
          (2 : ZMod 689125061) ^ 1345947 = (2 : ZMod 689125061) ^ (672973 + 672973 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 672973 * (2 : ZMod 689125061) ^ 672973) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 602436738 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 689125061) ^ 2691894 = 658351233 := by
        calc
          (2 : ZMod 689125061) ^ 2691894 = (2 : ZMod 689125061) ^ (1345947 + 1345947) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 1345947 * (2 : ZMod 689125061) ^ 1345947 := by rw [pow_add]
          _ = 658351233 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 689125061) ^ 5383789 = 195013973 := by
        calc
          (2 : ZMod 689125061) ^ 5383789 = (2 : ZMod 689125061) ^ (2691894 + 2691894 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 2691894 * (2 : ZMod 689125061) ^ 2691894) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 195013973 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 689125061) ^ 10767579 = 427852735 := by
        calc
          (2 : ZMod 689125061) ^ 10767579 = (2 : ZMod 689125061) ^ (5383789 + 5383789 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 5383789 * (2 : ZMod 689125061) ^ 5383789) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 427852735 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 689125061) ^ 21535158 = 16048073 := by
        calc
          (2 : ZMod 689125061) ^ 21535158 = (2 : ZMod 689125061) ^ (10767579 + 10767579) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 10767579 * (2 : ZMod 689125061) ^ 10767579 := by rw [pow_add]
          _ = 16048073 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 689125061) ^ 43070316 = 140091348 := by
        calc
          (2 : ZMod 689125061) ^ 43070316 = (2 : ZMod 689125061) ^ (21535158 + 21535158) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 21535158 * (2 : ZMod 689125061) ^ 21535158 := by rw [pow_add]
          _ = 140091348 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 689125061) ^ 86140632 = 63488714 := by
        calc
          (2 : ZMod 689125061) ^ 86140632 = (2 : ZMod 689125061) ^ (43070316 + 43070316) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 43070316 * (2 : ZMod 689125061) ^ 43070316 := by rw [pow_add]
          _ = 63488714 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 689125061) ^ 172281265 = 562147632 := by
        calc
          (2 : ZMod 689125061) ^ 172281265 = (2 : ZMod 689125061) ^ (86140632 + 86140632 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 86140632 * (2 : ZMod 689125061) ^ 86140632) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 562147632 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 689125061) ^ 344562530 = 689125060 := by
        calc
          (2 : ZMod 689125061) ^ 344562530 = (2 : ZMod 689125061) ^ (172281265 + 172281265) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 172281265 * (2 : ZMod 689125061) ^ 172281265 := by rw [pow_add]
          _ = 689125060 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 689125061) ^ 689125060 = 1 := by
        calc
          (2 : ZMod 689125061) ^ 689125060 = (2 : ZMod 689125061) ^ (344562530 + 344562530) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 344562530 * (2 : ZMod 689125061) ^ 344562530 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (13, 1), (19, 1), (199, 1), (701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (13, 1), (19, 1), (199, 1), (701, 1)] : List FactorBlock).map factorBlockValue).prod = 689125061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 689125061) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 689125061) ^ 2 = 4 := by
        calc
          (2 : ZMod 689125061) ^ 2 = (2 : ZMod 689125061) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 1 * (2 : ZMod 689125061) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 689125061) ^ 5 = 32 := by
        calc
          (2 : ZMod 689125061) ^ 5 = (2 : ZMod 689125061) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 2 * (2 : ZMod 689125061) ^ 2) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 689125061) ^ 10 = 1024 := by
        calc
          (2 : ZMod 689125061) ^ 10 = (2 : ZMod 689125061) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 5 * (2 : ZMod 689125061) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 689125061) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 689125061) ^ 20 = (2 : ZMod 689125061) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 10 * (2 : ZMod 689125061) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 689125061) ^ 41 = 25185901 := by
        calc
          (2 : ZMod 689125061) ^ 41 = (2 : ZMod 689125061) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 20 * (2 : ZMod 689125061) ^ 20) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 25185901 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 689125061) ^ 82 = 327407216 := by
        calc
          (2 : ZMod 689125061) ^ 82 = (2 : ZMod 689125061) ^ (41 + 41) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 41 * (2 : ZMod 689125061) ^ 41 := by rw [pow_add]
          _ = 327407216 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 689125061) ^ 164 = 3511375 := by
        calc
          (2 : ZMod 689125061) ^ 164 = (2 : ZMod 689125061) ^ (82 + 82) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 82 * (2 : ZMod 689125061) ^ 82 := by rw [pow_add]
          _ = 3511375 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 689125061) ^ 328 = 617924274 := by
        calc
          (2 : ZMod 689125061) ^ 328 = (2 : ZMod 689125061) ^ (164 + 164) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 164 * (2 : ZMod 689125061) ^ 164 := by rw [pow_add]
          _ = 617924274 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 689125061) ^ 657 = 225095128 := by
        calc
          (2 : ZMod 689125061) ^ 657 = (2 : ZMod 689125061) ^ (328 + 328 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 328 * (2 : ZMod 689125061) ^ 328) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 225095128 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 689125061) ^ 1314 = 597195595 := by
        calc
          (2 : ZMod 689125061) ^ 1314 = (2 : ZMod 689125061) ^ (657 + 657) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 657 * (2 : ZMod 689125061) ^ 657 := by rw [pow_add]
          _ = 597195595 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 689125061) ^ 2628 = 109101841 := by
        calc
          (2 : ZMod 689125061) ^ 2628 = (2 : ZMod 689125061) ^ (1314 + 1314) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 1314 * (2 : ZMod 689125061) ^ 1314 := by rw [pow_add]
          _ = 109101841 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 689125061) ^ 5257 = 26380614 := by
        calc
          (2 : ZMod 689125061) ^ 5257 = (2 : ZMod 689125061) ^ (2628 + 2628 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 2628 * (2 : ZMod 689125061) ^ 2628) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 26380614 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 689125061) ^ 10515 = 154703083 := by
        calc
          (2 : ZMod 689125061) ^ 10515 = (2 : ZMod 689125061) ^ (5257 + 5257 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 5257 * (2 : ZMod 689125061) ^ 5257) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 154703083 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 689125061) ^ 21030 = 658198801 := by
        calc
          (2 : ZMod 689125061) ^ 21030 = (2 : ZMod 689125061) ^ (10515 + 10515) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 10515 * (2 : ZMod 689125061) ^ 10515 := by rw [pow_add]
          _ = 658198801 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 689125061) ^ 42060 = 331051005 := by
        calc
          (2 : ZMod 689125061) ^ 42060 = (2 : ZMod 689125061) ^ (21030 + 21030) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 21030 * (2 : ZMod 689125061) ^ 21030 := by rw [pow_add]
          _ = 331051005 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 689125061) ^ 84121 = 410541896 := by
        calc
          (2 : ZMod 689125061) ^ 84121 = (2 : ZMod 689125061) ^ (42060 + 42060 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 42060 * (2 : ZMod 689125061) ^ 42060) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 410541896 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 689125061) ^ 168243 = 194690657 := by
        calc
          (2 : ZMod 689125061) ^ 168243 = (2 : ZMod 689125061) ^ (84121 + 84121 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 84121 * (2 : ZMod 689125061) ^ 84121) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 194690657 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 689125061) ^ 336486 = 375113875 := by
        calc
          (2 : ZMod 689125061) ^ 336486 = (2 : ZMod 689125061) ^ (168243 + 168243) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 168243 * (2 : ZMod 689125061) ^ 168243 := by rw [pow_add]
          _ = 375113875 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 689125061) ^ 672973 = 146585113 := by
        calc
          (2 : ZMod 689125061) ^ 672973 = (2 : ZMod 689125061) ^ (336486 + 336486 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 336486 * (2 : ZMod 689125061) ^ 336486) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 146585113 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 689125061) ^ 1345947 = 602436738 := by
        calc
          (2 : ZMod 689125061) ^ 1345947 = (2 : ZMod 689125061) ^ (672973 + 672973 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 672973 * (2 : ZMod 689125061) ^ 672973) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 602436738 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 689125061) ^ 2691894 = 658351233 := by
        calc
          (2 : ZMod 689125061) ^ 2691894 = (2 : ZMod 689125061) ^ (1345947 + 1345947) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 1345947 * (2 : ZMod 689125061) ^ 1345947 := by rw [pow_add]
          _ = 658351233 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 689125061) ^ 5383789 = 195013973 := by
        calc
          (2 : ZMod 689125061) ^ 5383789 = (2 : ZMod 689125061) ^ (2691894 + 2691894 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 2691894 * (2 : ZMod 689125061) ^ 2691894) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 195013973 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 689125061) ^ 10767579 = 427852735 := by
        calc
          (2 : ZMod 689125061) ^ 10767579 = (2 : ZMod 689125061) ^ (5383789 + 5383789 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 5383789 * (2 : ZMod 689125061) ^ 5383789) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 427852735 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 689125061) ^ 21535158 = 16048073 := by
        calc
          (2 : ZMod 689125061) ^ 21535158 = (2 : ZMod 689125061) ^ (10767579 + 10767579) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 10767579 * (2 : ZMod 689125061) ^ 10767579 := by rw [pow_add]
          _ = 16048073 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 689125061) ^ 43070316 = 140091348 := by
        calc
          (2 : ZMod 689125061) ^ 43070316 = (2 : ZMod 689125061) ^ (21535158 + 21535158) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 21535158 * (2 : ZMod 689125061) ^ 21535158 := by rw [pow_add]
          _ = 140091348 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 689125061) ^ 86140632 = 63488714 := by
        calc
          (2 : ZMod 689125061) ^ 86140632 = (2 : ZMod 689125061) ^ (43070316 + 43070316) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 43070316 * (2 : ZMod 689125061) ^ 43070316 := by rw [pow_add]
          _ = 63488714 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 689125061) ^ 172281265 = 562147632 := by
        calc
          (2 : ZMod 689125061) ^ 172281265 = (2 : ZMod 689125061) ^ (86140632 + 86140632 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 86140632 * (2 : ZMod 689125061) ^ 86140632) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 562147632 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 689125061) ^ 344562530 = 689125060 := by
        calc
          (2 : ZMod 689125061) ^ 344562530 = (2 : ZMod 689125061) ^ (172281265 + 172281265) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 172281265 * (2 : ZMod 689125061) ^ 172281265 := by rw [pow_add]
          _ = 689125060 := by rw [factor_0_27]; decide
      change (2 : ZMod 689125061) ^ 344562530 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (2 : ZMod 689125061) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 689125061) ^ 2 = 4 := by
        calc
          (2 : ZMod 689125061) ^ 2 = (2 : ZMod 689125061) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 1 * (2 : ZMod 689125061) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 689125061) ^ 4 = 16 := by
        calc
          (2 : ZMod 689125061) ^ 4 = (2 : ZMod 689125061) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 2 * (2 : ZMod 689125061) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 689125061) ^ 8 = 256 := by
        calc
          (2 : ZMod 689125061) ^ 8 = (2 : ZMod 689125061) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 4 * (2 : ZMod 689125061) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 689125061) ^ 16 = 65536 := by
        calc
          (2 : ZMod 689125061) ^ 16 = (2 : ZMod 689125061) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 8 * (2 : ZMod 689125061) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 689125061) ^ 32 = 160216930 := by
        calc
          (2 : ZMod 689125061) ^ 32 = (2 : ZMod 689125061) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 16 * (2 : ZMod 689125061) ^ 16 := by rw [pow_add]
          _ = 160216930 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 689125061) ^ 65 = 554953429 := by
        calc
          (2 : ZMod 689125061) ^ 65 = (2 : ZMod 689125061) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 32 * (2 : ZMod 689125061) ^ 32) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 554953429 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 689125061) ^ 131 = 232453591 := by
        calc
          (2 : ZMod 689125061) ^ 131 = (2 : ZMod 689125061) ^ (65 + 65 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 65 * (2 : ZMod 689125061) ^ 65) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 232453591 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 689125061) ^ 262 = 362627036 := by
        calc
          (2 : ZMod 689125061) ^ 262 = (2 : ZMod 689125061) ^ (131 + 131) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 131 * (2 : ZMod 689125061) ^ 131 := by rw [pow_add]
          _ = 362627036 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 689125061) ^ 525 = 634460077 := by
        calc
          (2 : ZMod 689125061) ^ 525 = (2 : ZMod 689125061) ^ (262 + 262 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 262 * (2 : ZMod 689125061) ^ 262) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 634460077 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 689125061) ^ 1051 = 475785631 := by
        calc
          (2 : ZMod 689125061) ^ 1051 = (2 : ZMod 689125061) ^ (525 + 525 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 525 * (2 : ZMod 689125061) ^ 525) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 475785631 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 689125061) ^ 2103 = 304505561 := by
        calc
          (2 : ZMod 689125061) ^ 2103 = (2 : ZMod 689125061) ^ (1051 + 1051 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 1051 * (2 : ZMod 689125061) ^ 1051) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 304505561 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 689125061) ^ 4206 = 462960143 := by
        calc
          (2 : ZMod 689125061) ^ 4206 = (2 : ZMod 689125061) ^ (2103 + 2103) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 2103 * (2 : ZMod 689125061) ^ 2103 := by rw [pow_add]
          _ = 462960143 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 689125061) ^ 8412 = 613698544 := by
        calc
          (2 : ZMod 689125061) ^ 8412 = (2 : ZMod 689125061) ^ (4206 + 4206) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 4206 * (2 : ZMod 689125061) ^ 4206 := by rw [pow_add]
          _ = 613698544 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 689125061) ^ 16824 = 6783042 := by
        calc
          (2 : ZMod 689125061) ^ 16824 = (2 : ZMod 689125061) ^ (8412 + 8412) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 8412 * (2 : ZMod 689125061) ^ 8412 := by rw [pow_add]
          _ = 6783042 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 689125061) ^ 33648 = 224076099 := by
        calc
          (2 : ZMod 689125061) ^ 33648 = (2 : ZMod 689125061) ^ (16824 + 16824) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 16824 * (2 : ZMod 689125061) ^ 16824 := by rw [pow_add]
          _ = 224076099 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 689125061) ^ 67297 = 669366668 := by
        calc
          (2 : ZMod 689125061) ^ 67297 = (2 : ZMod 689125061) ^ (33648 + 33648 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 33648 * (2 : ZMod 689125061) ^ 33648) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 669366668 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 689125061) ^ 134594 = 612135583 := by
        calc
          (2 : ZMod 689125061) ^ 134594 = (2 : ZMod 689125061) ^ (67297 + 67297) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 67297 * (2 : ZMod 689125061) ^ 67297 := by rw [pow_add]
          _ = 612135583 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 689125061) ^ 269189 = 132064904 := by
        calc
          (2 : ZMod 689125061) ^ 269189 = (2 : ZMod 689125061) ^ (134594 + 134594 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 134594 * (2 : ZMod 689125061) ^ 134594) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 132064904 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 689125061) ^ 538378 = 341548811 := by
        calc
          (2 : ZMod 689125061) ^ 538378 = (2 : ZMod 689125061) ^ (269189 + 269189) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 269189 * (2 : ZMod 689125061) ^ 269189 := by rw [pow_add]
          _ = 341548811 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 689125061) ^ 1076757 = 18403931 := by
        calc
          (2 : ZMod 689125061) ^ 1076757 = (2 : ZMod 689125061) ^ (538378 + 538378 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 538378 * (2 : ZMod 689125061) ^ 538378) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 18403931 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 689125061) ^ 2153515 = 106667583 := by
        calc
          (2 : ZMod 689125061) ^ 2153515 = (2 : ZMod 689125061) ^ (1076757 + 1076757 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 1076757 * (2 : ZMod 689125061) ^ 1076757) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 106667583 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 689125061) ^ 4307031 = 567812034 := by
        calc
          (2 : ZMod 689125061) ^ 4307031 = (2 : ZMod 689125061) ^ (2153515 + 2153515 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 2153515 * (2 : ZMod 689125061) ^ 2153515) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 567812034 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 689125061) ^ 8614063 = 239266941 := by
        calc
          (2 : ZMod 689125061) ^ 8614063 = (2 : ZMod 689125061) ^ (4307031 + 4307031 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 4307031 * (2 : ZMod 689125061) ^ 4307031) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 239266941 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 689125061) ^ 17228126 = 170707495 := by
        calc
          (2 : ZMod 689125061) ^ 17228126 = (2 : ZMod 689125061) ^ (8614063 + 8614063) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 8614063 * (2 : ZMod 689125061) ^ 8614063 := by rw [pow_add]
          _ = 170707495 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 689125061) ^ 34456253 = 333083000 := by
        calc
          (2 : ZMod 689125061) ^ 34456253 = (2 : ZMod 689125061) ^ (17228126 + 17228126 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 17228126 * (2 : ZMod 689125061) ^ 17228126) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 333083000 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 689125061) ^ 68912506 = 130179318 := by
        calc
          (2 : ZMod 689125061) ^ 68912506 = (2 : ZMod 689125061) ^ (34456253 + 34456253) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 34456253 * (2 : ZMod 689125061) ^ 34456253 := by rw [pow_add]
          _ = 130179318 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 689125061) ^ 137825012 = 62860452 := by
        calc
          (2 : ZMod 689125061) ^ 137825012 = (2 : ZMod 689125061) ^ (68912506 + 68912506) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 68912506 * (2 : ZMod 689125061) ^ 68912506 := by rw [pow_add]
          _ = 62860452 := by rw [factor_1_26]; decide
      change (2 : ZMod 689125061) ^ 137825012 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (2 : ZMod 689125061) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 689125061) ^ 3 = 8 := by
        calc
          (2 : ZMod 689125061) ^ 3 = (2 : ZMod 689125061) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 1 * (2 : ZMod 689125061) ^ 1) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 689125061) ^ 6 = 64 := by
        calc
          (2 : ZMod 689125061) ^ 6 = (2 : ZMod 689125061) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 3 * (2 : ZMod 689125061) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 689125061) ^ 12 = 4096 := by
        calc
          (2 : ZMod 689125061) ^ 12 = (2 : ZMod 689125061) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 6 * (2 : ZMod 689125061) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 689125061) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 689125061) ^ 25 = (2 : ZMod 689125061) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 12 * (2 : ZMod 689125061) ^ 12) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 689125061) ^ 50 = 490930214 := by
        calc
          (2 : ZMod 689125061) ^ 50 = (2 : ZMod 689125061) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 25 * (2 : ZMod 689125061) ^ 25 := by rw [pow_add]
          _ = 490930214 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 689125061) ^ 101 = 134767596 := by
        calc
          (2 : ZMod 689125061) ^ 101 = (2 : ZMod 689125061) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 50 * (2 : ZMod 689125061) ^ 50) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 134767596 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 689125061) ^ 202 = 473927616 := by
        calc
          (2 : ZMod 689125061) ^ 202 = (2 : ZMod 689125061) ^ (101 + 101) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 101 * (2 : ZMod 689125061) ^ 101 := by rw [pow_add]
          _ = 473927616 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 689125061) ^ 404 = 249762877 := by
        calc
          (2 : ZMod 689125061) ^ 404 = (2 : ZMod 689125061) ^ (202 + 202) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 202 * (2 : ZMod 689125061) ^ 202 := by rw [pow_add]
          _ = 249762877 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 689125061) ^ 808 = 489929501 := by
        calc
          (2 : ZMod 689125061) ^ 808 = (2 : ZMod 689125061) ^ (404 + 404) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 404 * (2 : ZMod 689125061) ^ 404 := by rw [pow_add]
          _ = 489929501 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 689125061) ^ 1617 = 140460377 := by
        calc
          (2 : ZMod 689125061) ^ 1617 = (2 : ZMod 689125061) ^ (808 + 808 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 808 * (2 : ZMod 689125061) ^ 808) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 140460377 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 689125061) ^ 3235 = 97573625 := by
        calc
          (2 : ZMod 689125061) ^ 3235 = (2 : ZMod 689125061) ^ (1617 + 1617 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 1617 * (2 : ZMod 689125061) ^ 1617) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 97573625 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 689125061) ^ 6470 = 191519698 := by
        calc
          (2 : ZMod 689125061) ^ 6470 = (2 : ZMod 689125061) ^ (3235 + 3235) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 3235 * (2 : ZMod 689125061) ^ 3235 := by rw [pow_add]
          _ = 191519698 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 689125061) ^ 12941 = 137500317 := by
        calc
          (2 : ZMod 689125061) ^ 12941 = (2 : ZMod 689125061) ^ (6470 + 6470 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 6470 * (2 : ZMod 689125061) ^ 6470) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 137500317 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 689125061) ^ 25883 = 477847184 := by
        calc
          (2 : ZMod 689125061) ^ 25883 = (2 : ZMod 689125061) ^ (12941 + 12941 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 12941 * (2 : ZMod 689125061) ^ 12941) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 477847184 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 689125061) ^ 51767 = 340407288 := by
        calc
          (2 : ZMod 689125061) ^ 51767 = (2 : ZMod 689125061) ^ (25883 + 25883 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 25883 * (2 : ZMod 689125061) ^ 25883) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 340407288 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 689125061) ^ 103534 = 528674247 := by
        calc
          (2 : ZMod 689125061) ^ 103534 = (2 : ZMod 689125061) ^ (51767 + 51767) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 51767 * (2 : ZMod 689125061) ^ 51767 := by rw [pow_add]
          _ = 528674247 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 689125061) ^ 207068 = 128913128 := by
        calc
          (2 : ZMod 689125061) ^ 207068 = (2 : ZMod 689125061) ^ (103534 + 103534) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 103534 * (2 : ZMod 689125061) ^ 103534 := by rw [pow_add]
          _ = 128913128 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 689125061) ^ 414137 = 391772951 := by
        calc
          (2 : ZMod 689125061) ^ 414137 = (2 : ZMod 689125061) ^ (207068 + 207068 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 207068 * (2 : ZMod 689125061) ^ 207068) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 391772951 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 689125061) ^ 828275 = 458428950 := by
        calc
          (2 : ZMod 689125061) ^ 828275 = (2 : ZMod 689125061) ^ (414137 + 414137 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 414137 * (2 : ZMod 689125061) ^ 414137) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 458428950 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 689125061) ^ 1656550 = 629157690 := by
        calc
          (2 : ZMod 689125061) ^ 1656550 = (2 : ZMod 689125061) ^ (828275 + 828275) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 828275 * (2 : ZMod 689125061) ^ 828275 := by rw [pow_add]
          _ = 629157690 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 689125061) ^ 3313101 = 318916412 := by
        calc
          (2 : ZMod 689125061) ^ 3313101 = (2 : ZMod 689125061) ^ (1656550 + 1656550 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 1656550 * (2 : ZMod 689125061) ^ 1656550) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 318916412 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 689125061) ^ 6626202 = 211614425 := by
        calc
          (2 : ZMod 689125061) ^ 6626202 = (2 : ZMod 689125061) ^ (3313101 + 3313101) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 3313101 * (2 : ZMod 689125061) ^ 3313101 := by rw [pow_add]
          _ = 211614425 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 689125061) ^ 13252405 = 216117864 := by
        calc
          (2 : ZMod 689125061) ^ 13252405 = (2 : ZMod 689125061) ^ (6626202 + 6626202 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 6626202 * (2 : ZMod 689125061) ^ 6626202) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 216117864 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 689125061) ^ 26504810 = 579141529 := by
        calc
          (2 : ZMod 689125061) ^ 26504810 = (2 : ZMod 689125061) ^ (13252405 + 13252405) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 13252405 * (2 : ZMod 689125061) ^ 13252405 := by rw [pow_add]
          _ = 579141529 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 689125061) ^ 53009620 = 414572445 := by
        calc
          (2 : ZMod 689125061) ^ 53009620 = (2 : ZMod 689125061) ^ (26504810 + 26504810) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 26504810 * (2 : ZMod 689125061) ^ 26504810 := by rw [pow_add]
          _ = 414572445 := by rw [factor_2_24]; decide
      change (2 : ZMod 689125061) ^ 53009620 ≠ 1
      rw [factor_2_25]
      decide
    ·
      have factor_3_0 : (2 : ZMod 689125061) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 689125061) ^ 2 = 4 := by
        calc
          (2 : ZMod 689125061) ^ 2 = (2 : ZMod 689125061) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 1 * (2 : ZMod 689125061) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 689125061) ^ 4 = 16 := by
        calc
          (2 : ZMod 689125061) ^ 4 = (2 : ZMod 689125061) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 2 * (2 : ZMod 689125061) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 689125061) ^ 8 = 256 := by
        calc
          (2 : ZMod 689125061) ^ 8 = (2 : ZMod 689125061) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 4 * (2 : ZMod 689125061) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 689125061) ^ 17 = 131072 := by
        calc
          (2 : ZMod 689125061) ^ 17 = (2 : ZMod 689125061) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 8 * (2 : ZMod 689125061) ^ 8) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 689125061) ^ 34 = 640867720 := by
        calc
          (2 : ZMod 689125061) ^ 34 = (2 : ZMod 689125061) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 17 * (2 : ZMod 689125061) ^ 17 := by rw [pow_add]
          _ = 640867720 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 689125061) ^ 69 = 609754132 := by
        calc
          (2 : ZMod 689125061) ^ 69 = (2 : ZMod 689125061) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 34 * (2 : ZMod 689125061) ^ 34) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 609754132 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 689125061) ^ 138 = 121682025 := by
        calc
          (2 : ZMod 689125061) ^ 138 = (2 : ZMod 689125061) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 69 * (2 : ZMod 689125061) ^ 69 := by rw [pow_add]
          _ = 121682025 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 689125061) ^ 276 = 334206943 := by
        calc
          (2 : ZMod 689125061) ^ 276 = (2 : ZMod 689125061) ^ (138 + 138) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 138 * (2 : ZMod 689125061) ^ 138 := by rw [pow_add]
          _ = 334206943 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 689125061) ^ 553 = 336767813 := by
        calc
          (2 : ZMod 689125061) ^ 553 = (2 : ZMod 689125061) ^ (276 + 276 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 276 * (2 : ZMod 689125061) ^ 276) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 336767813 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 689125061) ^ 1106 = 48495415 := by
        calc
          (2 : ZMod 689125061) ^ 1106 = (2 : ZMod 689125061) ^ (553 + 553) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 553 * (2 : ZMod 689125061) ^ 553 := by rw [pow_add]
          _ = 48495415 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 689125061) ^ 2213 = 541565109 := by
        calc
          (2 : ZMod 689125061) ^ 2213 = (2 : ZMod 689125061) ^ (1106 + 1106 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 1106 * (2 : ZMod 689125061) ^ 1106) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 541565109 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 689125061) ^ 4427 = 266961730 := by
        calc
          (2 : ZMod 689125061) ^ 4427 = (2 : ZMod 689125061) ^ (2213 + 2213 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 2213 * (2 : ZMod 689125061) ^ 2213) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 266961730 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 689125061) ^ 8854 = 554914207 := by
        calc
          (2 : ZMod 689125061) ^ 8854 = (2 : ZMod 689125061) ^ (4427 + 4427) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 4427 * (2 : ZMod 689125061) ^ 4427 := by rw [pow_add]
          _ = 554914207 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 689125061) ^ 17709 = 457571825 := by
        calc
          (2 : ZMod 689125061) ^ 17709 = (2 : ZMod 689125061) ^ (8854 + 8854 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 8854 * (2 : ZMod 689125061) ^ 8854) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 457571825 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 689125061) ^ 35419 = 387142389 := by
        calc
          (2 : ZMod 689125061) ^ 35419 = (2 : ZMod 689125061) ^ (17709 + 17709 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 17709 * (2 : ZMod 689125061) ^ 17709) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 387142389 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 689125061) ^ 70839 = 492223322 := by
        calc
          (2 : ZMod 689125061) ^ 70839 = (2 : ZMod 689125061) ^ (35419 + 35419 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 35419 * (2 : ZMod 689125061) ^ 35419) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 492223322 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 689125061) ^ 141678 = 359853629 := by
        calc
          (2 : ZMod 689125061) ^ 141678 = (2 : ZMod 689125061) ^ (70839 + 70839) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 70839 * (2 : ZMod 689125061) ^ 70839 := by rw [pow_add]
          _ = 359853629 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 689125061) ^ 283357 = 288716762 := by
        calc
          (2 : ZMod 689125061) ^ 283357 = (2 : ZMod 689125061) ^ (141678 + 141678 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 141678 * (2 : ZMod 689125061) ^ 141678) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 288716762 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 689125061) ^ 566714 = 517883762 := by
        calc
          (2 : ZMod 689125061) ^ 566714 = (2 : ZMod 689125061) ^ (283357 + 283357) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 283357 * (2 : ZMod 689125061) ^ 283357 := by rw [pow_add]
          _ = 517883762 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 689125061) ^ 1133429 = 154457697 := by
        calc
          (2 : ZMod 689125061) ^ 1133429 = (2 : ZMod 689125061) ^ (566714 + 566714 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 566714 * (2 : ZMod 689125061) ^ 566714) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 154457697 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 689125061) ^ 2266858 = 641628028 := by
        calc
          (2 : ZMod 689125061) ^ 2266858 = (2 : ZMod 689125061) ^ (1133429 + 1133429) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 1133429 * (2 : ZMod 689125061) ^ 1133429 := by rw [pow_add]
          _ = 641628028 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 689125061) ^ 4533717 = 210718438 := by
        calc
          (2 : ZMod 689125061) ^ 4533717 = (2 : ZMod 689125061) ^ (2266858 + 2266858 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 2266858 * (2 : ZMod 689125061) ^ 2266858) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 210718438 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 689125061) ^ 9067435 = 252517600 := by
        calc
          (2 : ZMod 689125061) ^ 9067435 = (2 : ZMod 689125061) ^ (4533717 + 4533717 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 4533717 * (2 : ZMod 689125061) ^ 4533717) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 252517600 := by rw [factor_3_22]; decide
      have factor_3_24 : (2 : ZMod 689125061) ^ 18134870 = 168519925 := by
        calc
          (2 : ZMod 689125061) ^ 18134870 = (2 : ZMod 689125061) ^ (9067435 + 9067435) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 9067435 * (2 : ZMod 689125061) ^ 9067435 := by rw [pow_add]
          _ = 168519925 := by rw [factor_3_23]; decide
      have factor_3_25 : (2 : ZMod 689125061) ^ 36269740 = 72184889 := by
        calc
          (2 : ZMod 689125061) ^ 36269740 = (2 : ZMod 689125061) ^ (18134870 + 18134870) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 18134870 * (2 : ZMod 689125061) ^ 18134870 := by rw [pow_add]
          _ = 72184889 := by rw [factor_3_24]; decide
      change (2 : ZMod 689125061) ^ 36269740 ≠ 1
      rw [factor_3_25]
      decide
    ·
      have factor_4_0 : (2 : ZMod 689125061) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 689125061) ^ 3 = 8 := by
        calc
          (2 : ZMod 689125061) ^ 3 = (2 : ZMod 689125061) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 1 * (2 : ZMod 689125061) ^ 1) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 689125061) ^ 6 = 64 := by
        calc
          (2 : ZMod 689125061) ^ 6 = (2 : ZMod 689125061) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 3 * (2 : ZMod 689125061) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 689125061) ^ 13 = 8192 := by
        calc
          (2 : ZMod 689125061) ^ 13 = (2 : ZMod 689125061) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 6 * (2 : ZMod 689125061) ^ 6) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 689125061) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 689125061) ^ 26 = (2 : ZMod 689125061) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 13 * (2 : ZMod 689125061) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 689125061) ^ 52 = 585470734 := by
        calc
          (2 : ZMod 689125061) ^ 52 = (2 : ZMod 689125061) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 26 * (2 : ZMod 689125061) ^ 26 := by rw [pow_add]
          _ = 585470734 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 689125061) ^ 105 = 88906353 := by
        calc
          (2 : ZMod 689125061) ^ 105 = (2 : ZMod 689125061) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 52 * (2 : ZMod 689125061) ^ 52) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 88906353 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 689125061) ^ 211 = 78917920 := by
        calc
          (2 : ZMod 689125061) ^ 211 = (2 : ZMod 689125061) ^ (105 + 105 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 105 * (2 : ZMod 689125061) ^ 105) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 78917920 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 689125061) ^ 422 = 67582678 := by
        calc
          (2 : ZMod 689125061) ^ 422 = (2 : ZMod 689125061) ^ (211 + 211) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 211 * (2 : ZMod 689125061) ^ 211 := by rw [pow_add]
          _ = 67582678 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 689125061) ^ 845 = 281955546 := by
        calc
          (2 : ZMod 689125061) ^ 845 = (2 : ZMod 689125061) ^ (422 + 422 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 422 * (2 : ZMod 689125061) ^ 422) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 281955546 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 689125061) ^ 1690 = 559818674 := by
        calc
          (2 : ZMod 689125061) ^ 1690 = (2 : ZMod 689125061) ^ (845 + 845) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 845 * (2 : ZMod 689125061) ^ 845 := by rw [pow_add]
          _ = 559818674 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 689125061) ^ 3381 = 574169228 := by
        calc
          (2 : ZMod 689125061) ^ 3381 = (2 : ZMod 689125061) ^ (1690 + 1690 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 1690 * (2 : ZMod 689125061) ^ 1690) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 574169228 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 689125061) ^ 6763 = 262193692 := by
        calc
          (2 : ZMod 689125061) ^ 6763 = (2 : ZMod 689125061) ^ (3381 + 3381 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 3381 * (2 : ZMod 689125061) ^ 3381) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 262193692 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 689125061) ^ 13527 = 675492206 := by
        calc
          (2 : ZMod 689125061) ^ 13527 = (2 : ZMod 689125061) ^ (6763 + 6763 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 6763 * (2 : ZMod 689125061) ^ 6763) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 675492206 := by rw [factor_4_12]; decide
      have factor_4_14 : (2 : ZMod 689125061) ^ 27054 = 462999569 := by
        calc
          (2 : ZMod 689125061) ^ 27054 = (2 : ZMod 689125061) ^ (13527 + 13527) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 13527 * (2 : ZMod 689125061) ^ 13527 := by rw [pow_add]
          _ = 462999569 := by rw [factor_4_13]; decide
      have factor_4_15 : (2 : ZMod 689125061) ^ 54108 = 412072320 := by
        calc
          (2 : ZMod 689125061) ^ 54108 = (2 : ZMod 689125061) ^ (27054 + 27054) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 27054 * (2 : ZMod 689125061) ^ 27054 := by rw [pow_add]
          _ = 412072320 := by rw [factor_4_14]; decide
      have factor_4_16 : (2 : ZMod 689125061) ^ 108216 = 189375763 := by
        calc
          (2 : ZMod 689125061) ^ 108216 = (2 : ZMod 689125061) ^ (54108 + 54108) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 54108 * (2 : ZMod 689125061) ^ 54108 := by rw [pow_add]
          _ = 189375763 := by rw [factor_4_15]; decide
      have factor_4_17 : (2 : ZMod 689125061) ^ 216433 = 446462613 := by
        calc
          (2 : ZMod 689125061) ^ 216433 = (2 : ZMod 689125061) ^ (108216 + 108216 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 108216 * (2 : ZMod 689125061) ^ 108216) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 446462613 := by rw [factor_4_16]; decide
      have factor_4_18 : (2 : ZMod 689125061) ^ 432867 = 275049541 := by
        calc
          (2 : ZMod 689125061) ^ 432867 = (2 : ZMod 689125061) ^ (216433 + 216433 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 216433 * (2 : ZMod 689125061) ^ 216433) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 275049541 := by rw [factor_4_17]; decide
      have factor_4_19 : (2 : ZMod 689125061) ^ 865735 = 390943550 := by
        calc
          (2 : ZMod 689125061) ^ 865735 = (2 : ZMod 689125061) ^ (432867 + 432867 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 432867 * (2 : ZMod 689125061) ^ 432867) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 390943550 := by rw [factor_4_18]; decide
      have factor_4_20 : (2 : ZMod 689125061) ^ 1731470 = 509533258 := by
        calc
          (2 : ZMod 689125061) ^ 1731470 = (2 : ZMod 689125061) ^ (865735 + 865735) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 865735 * (2 : ZMod 689125061) ^ 865735 := by rw [pow_add]
          _ = 509533258 := by rw [factor_4_19]; decide
      have factor_4_21 : (2 : ZMod 689125061) ^ 3462940 = 375549391 := by
        calc
          (2 : ZMod 689125061) ^ 3462940 = (2 : ZMod 689125061) ^ (1731470 + 1731470) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 1731470 * (2 : ZMod 689125061) ^ 1731470 := by rw [pow_add]
          _ = 375549391 := by rw [factor_4_20]; decide
      change (2 : ZMod 689125061) ^ 3462940 ≠ 1
      rw [factor_4_21]
      decide
    ·
      have factor_5_0 : (2 : ZMod 689125061) ^ 1 = 2 := by norm_num
      have factor_5_1 : (2 : ZMod 689125061) ^ 3 = 8 := by
        calc
          (2 : ZMod 689125061) ^ 3 = (2 : ZMod 689125061) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 1 * (2 : ZMod 689125061) ^ 1) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_5_0]; decide
      have factor_5_2 : (2 : ZMod 689125061) ^ 7 = 128 := by
        calc
          (2 : ZMod 689125061) ^ 7 = (2 : ZMod 689125061) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 3 * (2 : ZMod 689125061) ^ 3) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_5_1]; decide
      have factor_5_3 : (2 : ZMod 689125061) ^ 15 = 32768 := by
        calc
          (2 : ZMod 689125061) ^ 15 = (2 : ZMod 689125061) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 7 * (2 : ZMod 689125061) ^ 7) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_5_2]; decide
      have factor_5_4 : (2 : ZMod 689125061) ^ 30 = 384616763 := by
        calc
          (2 : ZMod 689125061) ^ 30 = (2 : ZMod 689125061) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 15 * (2 : ZMod 689125061) ^ 15 := by rw [pow_add]
          _ = 384616763 := by rw [factor_5_3]; decide
      have factor_5_5 : (2 : ZMod 689125061) ^ 60 = 340369667 := by
        calc
          (2 : ZMod 689125061) ^ 60 = (2 : ZMod 689125061) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 30 * (2 : ZMod 689125061) ^ 30 := by rw [pow_add]
          _ = 340369667 := by rw [factor_5_4]; decide
      have factor_5_6 : (2 : ZMod 689125061) ^ 120 = 351742257 := by
        calc
          (2 : ZMod 689125061) ^ 120 = (2 : ZMod 689125061) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 60 * (2 : ZMod 689125061) ^ 60 := by rw [pow_add]
          _ = 351742257 := by rw [factor_5_5]; decide
      have factor_5_7 : (2 : ZMod 689125061) ^ 240 = 367520615 := by
        calc
          (2 : ZMod 689125061) ^ 240 = (2 : ZMod 689125061) ^ (120 + 120) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 120 * (2 : ZMod 689125061) ^ 120 := by rw [pow_add]
          _ = 367520615 := by rw [factor_5_6]; decide
      have factor_5_8 : (2 : ZMod 689125061) ^ 480 = 303472391 := by
        calc
          (2 : ZMod 689125061) ^ 480 = (2 : ZMod 689125061) ^ (240 + 240) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 240 * (2 : ZMod 689125061) ^ 240 := by rw [pow_add]
          _ = 303472391 := by rw [factor_5_7]; decide
      have factor_5_9 : (2 : ZMod 689125061) ^ 960 = 266644413 := by
        calc
          (2 : ZMod 689125061) ^ 960 = (2 : ZMod 689125061) ^ (480 + 480) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 480 * (2 : ZMod 689125061) ^ 480 := by rw [pow_add]
          _ = 266644413 := by rw [factor_5_8]; decide
      have factor_5_10 : (2 : ZMod 689125061) ^ 1920 = 416673942 := by
        calc
          (2 : ZMod 689125061) ^ 1920 = (2 : ZMod 689125061) ^ (960 + 960) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 960 * (2 : ZMod 689125061) ^ 960 := by rw [pow_add]
          _ = 416673942 := by rw [factor_5_9]; decide
      have factor_5_11 : (2 : ZMod 689125061) ^ 3840 = 480942387 := by
        calc
          (2 : ZMod 689125061) ^ 3840 = (2 : ZMod 689125061) ^ (1920 + 1920) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 1920 * (2 : ZMod 689125061) ^ 1920 := by rw [pow_add]
          _ = 480942387 := by rw [factor_5_10]; decide
      have factor_5_12 : (2 : ZMod 689125061) ^ 7680 = 364041157 := by
        calc
          (2 : ZMod 689125061) ^ 7680 = (2 : ZMod 689125061) ^ (3840 + 3840) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 3840 * (2 : ZMod 689125061) ^ 3840 := by rw [pow_add]
          _ = 364041157 := by rw [factor_5_11]; decide
      have factor_5_13 : (2 : ZMod 689125061) ^ 15360 = 309335040 := by
        calc
          (2 : ZMod 689125061) ^ 15360 = (2 : ZMod 689125061) ^ (7680 + 7680) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 7680 * (2 : ZMod 689125061) ^ 7680 := by rw [pow_add]
          _ = 309335040 := by rw [factor_5_12]; decide
      have factor_5_14 : (2 : ZMod 689125061) ^ 30720 = 193922586 := by
        calc
          (2 : ZMod 689125061) ^ 30720 = (2 : ZMod 689125061) ^ (15360 + 15360) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 15360 * (2 : ZMod 689125061) ^ 15360 := by rw [pow_add]
          _ = 193922586 := by rw [factor_5_13]; decide
      have factor_5_15 : (2 : ZMod 689125061) ^ 61441 = 546866409 := by
        calc
          (2 : ZMod 689125061) ^ 61441 = (2 : ZMod 689125061) ^ (30720 + 30720 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 30720 * (2 : ZMod 689125061) ^ 30720) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 546866409 := by rw [factor_5_14]; decide
      have factor_5_16 : (2 : ZMod 689125061) ^ 122882 = 117596141 := by
        calc
          (2 : ZMod 689125061) ^ 122882 = (2 : ZMod 689125061) ^ (61441 + 61441) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 61441 * (2 : ZMod 689125061) ^ 61441 := by rw [pow_add]
          _ = 117596141 := by rw [factor_5_15]; decide
      have factor_5_17 : (2 : ZMod 689125061) ^ 245765 = 523852981 := by
        calc
          (2 : ZMod 689125061) ^ 245765 = (2 : ZMod 689125061) ^ (122882 + 122882 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = ((2 : ZMod 689125061) ^ 122882 * (2 : ZMod 689125061) ^ 122882) * (2 : ZMod 689125061) := by rw [pow_succ, pow_add]
          _ = 523852981 := by rw [factor_5_16]; decide
      have factor_5_18 : (2 : ZMod 689125061) ^ 491530 = 47793485 := by
        calc
          (2 : ZMod 689125061) ^ 491530 = (2 : ZMod 689125061) ^ (245765 + 245765) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 245765 * (2 : ZMod 689125061) ^ 245765 := by rw [pow_add]
          _ = 47793485 := by rw [factor_5_17]; decide
      have factor_5_19 : (2 : ZMod 689125061) ^ 983060 = 555500843 := by
        calc
          (2 : ZMod 689125061) ^ 983060 = (2 : ZMod 689125061) ^ (491530 + 491530) :=
            congrArg (fun n : ℕ => (2 : ZMod 689125061) ^ n) (by norm_num)
          _ = (2 : ZMod 689125061) ^ 491530 * (2 : ZMod 689125061) ^ 491530 := by rw [pow_add]
          _ = 555500843 := by rw [factor_5_18]; decide
      change (2 : ZMod 689125061) ^ 983060 ≠ 1
      rw [factor_5_19]
      decide

#print axioms prime_lucas_689125061

end TotientTailPeriodKiller
end Erdos249257
