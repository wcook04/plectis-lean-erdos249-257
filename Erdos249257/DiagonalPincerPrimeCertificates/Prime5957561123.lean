import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_5957561123 : Nat.Prime 5957561123 := by
  apply lucas_primality 5957561123 (2 : ZMod 5957561123)
  ·
      have fermat_0 : (2 : ZMod 5957561123) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 5957561123) ^ 2 = 4 := by
        calc
          (2 : ZMod 5957561123) ^ 2 = (2 : ZMod 5957561123) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 1 * (2 : ZMod 5957561123) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 5957561123) ^ 5 = 32 := by
        calc
          (2 : ZMod 5957561123) ^ 5 = (2 : ZMod 5957561123) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 2 * (2 : ZMod 5957561123) ^ 2) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 5957561123) ^ 11 = 2048 := by
        calc
          (2 : ZMod 5957561123) ^ 11 = (2 : ZMod 5957561123) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 5 * (2 : ZMod 5957561123) ^ 5) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 5957561123) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 5957561123) ^ 22 = (2 : ZMod 5957561123) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 11 * (2 : ZMod 5957561123) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 5957561123) ^ 44 = 5465609320 := by
        calc
          (2 : ZMod 5957561123) ^ 44 = (2 : ZMod 5957561123) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 22 * (2 : ZMod 5957561123) ^ 22 := by rw [pow_add]
          _ = 5465609320 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 5957561123) ^ 88 = 3266477796 := by
        calc
          (2 : ZMod 5957561123) ^ 88 = (2 : ZMod 5957561123) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 44 * (2 : ZMod 5957561123) ^ 44 := by rw [pow_add]
          _ = 3266477796 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 5957561123) ^ 177 = 3638787791 := by
        calc
          (2 : ZMod 5957561123) ^ 177 = (2 : ZMod 5957561123) ^ (88 + 88 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 88 * (2 : ZMod 5957561123) ^ 88) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 3638787791 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 5957561123) ^ 355 = 5936154482 := by
        calc
          (2 : ZMod 5957561123) ^ 355 = (2 : ZMod 5957561123) ^ (177 + 177 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 177 * (2 : ZMod 5957561123) ^ 177) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 5936154482 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 5957561123) ^ 710 = 592443967 := by
        calc
          (2 : ZMod 5957561123) ^ 710 = (2 : ZMod 5957561123) ^ (355 + 355) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 355 * (2 : ZMod 5957561123) ^ 355 := by rw [pow_add]
          _ = 592443967 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 5957561123) ^ 1420 = 3449246260 := by
        calc
          (2 : ZMod 5957561123) ^ 1420 = (2 : ZMod 5957561123) ^ (710 + 710) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 710 * (2 : ZMod 5957561123) ^ 710 := by rw [pow_add]
          _ = 3449246260 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 5957561123) ^ 2840 = 1082965202 := by
        calc
          (2 : ZMod 5957561123) ^ 2840 = (2 : ZMod 5957561123) ^ (1420 + 1420) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 1420 * (2 : ZMod 5957561123) ^ 1420 := by rw [pow_add]
          _ = 1082965202 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 5957561123) ^ 5681 = 4166131326 := by
        calc
          (2 : ZMod 5957561123) ^ 5681 = (2 : ZMod 5957561123) ^ (2840 + 2840 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 2840 * (2 : ZMod 5957561123) ^ 2840) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 4166131326 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 5957561123) ^ 11363 = 5746485677 := by
        calc
          (2 : ZMod 5957561123) ^ 11363 = (2 : ZMod 5957561123) ^ (5681 + 5681 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 5681 * (2 : ZMod 5957561123) ^ 5681) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 5746485677 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 5957561123) ^ 22726 = 3486250529 := by
        calc
          (2 : ZMod 5957561123) ^ 22726 = (2 : ZMod 5957561123) ^ (11363 + 11363) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 11363 * (2 : ZMod 5957561123) ^ 11363 := by rw [pow_add]
          _ = 3486250529 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 5957561123) ^ 45452 = 2432646007 := by
        calc
          (2 : ZMod 5957561123) ^ 45452 = (2 : ZMod 5957561123) ^ (22726 + 22726) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 22726 * (2 : ZMod 5957561123) ^ 22726 := by rw [pow_add]
          _ = 2432646007 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 5957561123) ^ 90905 = 5528782426 := by
        calc
          (2 : ZMod 5957561123) ^ 90905 = (2 : ZMod 5957561123) ^ (45452 + 45452 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 45452 * (2 : ZMod 5957561123) ^ 45452) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 5528782426 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 5957561123) ^ 181810 = 686680589 := by
        calc
          (2 : ZMod 5957561123) ^ 181810 = (2 : ZMod 5957561123) ^ (90905 + 90905) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 90905 * (2 : ZMod 5957561123) ^ 90905 := by rw [pow_add]
          _ = 686680589 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 5957561123) ^ 363620 = 3949080567 := by
        calc
          (2 : ZMod 5957561123) ^ 363620 = (2 : ZMod 5957561123) ^ (181810 + 181810) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 181810 * (2 : ZMod 5957561123) ^ 181810 := by rw [pow_add]
          _ = 3949080567 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 5957561123) ^ 727241 = 3966154724 := by
        calc
          (2 : ZMod 5957561123) ^ 727241 = (2 : ZMod 5957561123) ^ (363620 + 363620 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 363620 * (2 : ZMod 5957561123) ^ 363620) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 3966154724 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 5957561123) ^ 1454482 = 2664182986 := by
        calc
          (2 : ZMod 5957561123) ^ 1454482 = (2 : ZMod 5957561123) ^ (727241 + 727241) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 727241 * (2 : ZMod 5957561123) ^ 727241 := by rw [pow_add]
          _ = 2664182986 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 5957561123) ^ 2908965 = 3199199820 := by
        calc
          (2 : ZMod 5957561123) ^ 2908965 = (2 : ZMod 5957561123) ^ (1454482 + 1454482 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 1454482 * (2 : ZMod 5957561123) ^ 1454482) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 3199199820 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 5957561123) ^ 5817930 = 1311435851 := by
        calc
          (2 : ZMod 5957561123) ^ 5817930 = (2 : ZMod 5957561123) ^ (2908965 + 2908965) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 2908965 * (2 : ZMod 5957561123) ^ 2908965 := by rw [pow_add]
          _ = 1311435851 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 5957561123) ^ 11635861 = 2737701066 := by
        calc
          (2 : ZMod 5957561123) ^ 11635861 = (2 : ZMod 5957561123) ^ (5817930 + 5817930 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 5817930 * (2 : ZMod 5957561123) ^ 5817930) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 2737701066 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 5957561123) ^ 23271723 = 1004589703 := by
        calc
          (2 : ZMod 5957561123) ^ 23271723 = (2 : ZMod 5957561123) ^ (11635861 + 11635861 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 11635861 * (2 : ZMod 5957561123) ^ 11635861) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 1004589703 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 5957561123) ^ 46543446 = 1166465598 := by
        calc
          (2 : ZMod 5957561123) ^ 46543446 = (2 : ZMod 5957561123) ^ (23271723 + 23271723) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 23271723 * (2 : ZMod 5957561123) ^ 23271723 := by rw [pow_add]
          _ = 1166465598 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 5957561123) ^ 93086892 = 3985905042 := by
        calc
          (2 : ZMod 5957561123) ^ 93086892 = (2 : ZMod 5957561123) ^ (46543446 + 46543446) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 46543446 * (2 : ZMod 5957561123) ^ 46543446 := by rw [pow_add]
          _ = 3985905042 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 5957561123) ^ 186173785 = 2340348566 := by
        calc
          (2 : ZMod 5957561123) ^ 186173785 = (2 : ZMod 5957561123) ^ (93086892 + 93086892 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 93086892 * (2 : ZMod 5957561123) ^ 93086892) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 2340348566 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 5957561123) ^ 372347570 = 5286506277 := by
        calc
          (2 : ZMod 5957561123) ^ 372347570 = (2 : ZMod 5957561123) ^ (186173785 + 186173785) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 186173785 * (2 : ZMod 5957561123) ^ 186173785 := by rw [pow_add]
          _ = 5286506277 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 5957561123) ^ 744695140 = 4791481860 := by
        calc
          (2 : ZMod 5957561123) ^ 744695140 = (2 : ZMod 5957561123) ^ (372347570 + 372347570) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 372347570 * (2 : ZMod 5957561123) ^ 372347570 := by rw [pow_add]
          _ = 4791481860 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 5957561123) ^ 1489390280 = 962495587 := by
        calc
          (2 : ZMod 5957561123) ^ 1489390280 = (2 : ZMod 5957561123) ^ (744695140 + 744695140) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 744695140 * (2 : ZMod 5957561123) ^ 744695140 := by rw [pow_add]
          _ = 962495587 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 5957561123) ^ 2978780561 = 5957561122 := by
        calc
          (2 : ZMod 5957561123) ^ 2978780561 = (2 : ZMod 5957561123) ^ (1489390280 + 1489390280 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 1489390280 * (2 : ZMod 5957561123) ^ 1489390280) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 5957561122 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 5957561123) ^ 5957561122 = 1 := by
        calc
          (2 : ZMod 5957561123) ^ 5957561122 = (2 : ZMod 5957561123) ^ (2978780561 + 2978780561) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 2978780561 * (2 : ZMod 5957561123) ^ 2978780561 := by rw [pow_add]
          _ = 1 := by rw [fermat_31]; decide
      simpa using fermat_32
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23887, 1), (124703, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23887, 1), (124703, 1)] : List FactorBlock).map factorBlockValue).prod = 5957561123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 5957561123) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 5957561123) ^ 2 = 4 := by
        calc
          (2 : ZMod 5957561123) ^ 2 = (2 : ZMod 5957561123) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 1 * (2 : ZMod 5957561123) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 5957561123) ^ 5 = 32 := by
        calc
          (2 : ZMod 5957561123) ^ 5 = (2 : ZMod 5957561123) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 2 * (2 : ZMod 5957561123) ^ 2) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 5957561123) ^ 11 = 2048 := by
        calc
          (2 : ZMod 5957561123) ^ 11 = (2 : ZMod 5957561123) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 5 * (2 : ZMod 5957561123) ^ 5) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 5957561123) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 5957561123) ^ 22 = (2 : ZMod 5957561123) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 11 * (2 : ZMod 5957561123) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 5957561123) ^ 44 = 5465609320 := by
        calc
          (2 : ZMod 5957561123) ^ 44 = (2 : ZMod 5957561123) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 22 * (2 : ZMod 5957561123) ^ 22 := by rw [pow_add]
          _ = 5465609320 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 5957561123) ^ 88 = 3266477796 := by
        calc
          (2 : ZMod 5957561123) ^ 88 = (2 : ZMod 5957561123) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 44 * (2 : ZMod 5957561123) ^ 44 := by rw [pow_add]
          _ = 3266477796 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 5957561123) ^ 177 = 3638787791 := by
        calc
          (2 : ZMod 5957561123) ^ 177 = (2 : ZMod 5957561123) ^ (88 + 88 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 88 * (2 : ZMod 5957561123) ^ 88) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 3638787791 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 5957561123) ^ 355 = 5936154482 := by
        calc
          (2 : ZMod 5957561123) ^ 355 = (2 : ZMod 5957561123) ^ (177 + 177 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 177 * (2 : ZMod 5957561123) ^ 177) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 5936154482 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 5957561123) ^ 710 = 592443967 := by
        calc
          (2 : ZMod 5957561123) ^ 710 = (2 : ZMod 5957561123) ^ (355 + 355) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 355 * (2 : ZMod 5957561123) ^ 355 := by rw [pow_add]
          _ = 592443967 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 5957561123) ^ 1420 = 3449246260 := by
        calc
          (2 : ZMod 5957561123) ^ 1420 = (2 : ZMod 5957561123) ^ (710 + 710) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 710 * (2 : ZMod 5957561123) ^ 710 := by rw [pow_add]
          _ = 3449246260 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 5957561123) ^ 2840 = 1082965202 := by
        calc
          (2 : ZMod 5957561123) ^ 2840 = (2 : ZMod 5957561123) ^ (1420 + 1420) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 1420 * (2 : ZMod 5957561123) ^ 1420 := by rw [pow_add]
          _ = 1082965202 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 5957561123) ^ 5681 = 4166131326 := by
        calc
          (2 : ZMod 5957561123) ^ 5681 = (2 : ZMod 5957561123) ^ (2840 + 2840 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 2840 * (2 : ZMod 5957561123) ^ 2840) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 4166131326 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 5957561123) ^ 11363 = 5746485677 := by
        calc
          (2 : ZMod 5957561123) ^ 11363 = (2 : ZMod 5957561123) ^ (5681 + 5681 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 5681 * (2 : ZMod 5957561123) ^ 5681) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 5746485677 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 5957561123) ^ 22726 = 3486250529 := by
        calc
          (2 : ZMod 5957561123) ^ 22726 = (2 : ZMod 5957561123) ^ (11363 + 11363) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 11363 * (2 : ZMod 5957561123) ^ 11363 := by rw [pow_add]
          _ = 3486250529 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 5957561123) ^ 45452 = 2432646007 := by
        calc
          (2 : ZMod 5957561123) ^ 45452 = (2 : ZMod 5957561123) ^ (22726 + 22726) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 22726 * (2 : ZMod 5957561123) ^ 22726 := by rw [pow_add]
          _ = 2432646007 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 5957561123) ^ 90905 = 5528782426 := by
        calc
          (2 : ZMod 5957561123) ^ 90905 = (2 : ZMod 5957561123) ^ (45452 + 45452 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 45452 * (2 : ZMod 5957561123) ^ 45452) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 5528782426 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 5957561123) ^ 181810 = 686680589 := by
        calc
          (2 : ZMod 5957561123) ^ 181810 = (2 : ZMod 5957561123) ^ (90905 + 90905) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 90905 * (2 : ZMod 5957561123) ^ 90905 := by rw [pow_add]
          _ = 686680589 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 5957561123) ^ 363620 = 3949080567 := by
        calc
          (2 : ZMod 5957561123) ^ 363620 = (2 : ZMod 5957561123) ^ (181810 + 181810) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 181810 * (2 : ZMod 5957561123) ^ 181810 := by rw [pow_add]
          _ = 3949080567 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 5957561123) ^ 727241 = 3966154724 := by
        calc
          (2 : ZMod 5957561123) ^ 727241 = (2 : ZMod 5957561123) ^ (363620 + 363620 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 363620 * (2 : ZMod 5957561123) ^ 363620) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 3966154724 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 5957561123) ^ 1454482 = 2664182986 := by
        calc
          (2 : ZMod 5957561123) ^ 1454482 = (2 : ZMod 5957561123) ^ (727241 + 727241) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 727241 * (2 : ZMod 5957561123) ^ 727241 := by rw [pow_add]
          _ = 2664182986 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 5957561123) ^ 2908965 = 3199199820 := by
        calc
          (2 : ZMod 5957561123) ^ 2908965 = (2 : ZMod 5957561123) ^ (1454482 + 1454482 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 1454482 * (2 : ZMod 5957561123) ^ 1454482) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 3199199820 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 5957561123) ^ 5817930 = 1311435851 := by
        calc
          (2 : ZMod 5957561123) ^ 5817930 = (2 : ZMod 5957561123) ^ (2908965 + 2908965) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 2908965 * (2 : ZMod 5957561123) ^ 2908965 := by rw [pow_add]
          _ = 1311435851 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 5957561123) ^ 11635861 = 2737701066 := by
        calc
          (2 : ZMod 5957561123) ^ 11635861 = (2 : ZMod 5957561123) ^ (5817930 + 5817930 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 5817930 * (2 : ZMod 5957561123) ^ 5817930) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 2737701066 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 5957561123) ^ 23271723 = 1004589703 := by
        calc
          (2 : ZMod 5957561123) ^ 23271723 = (2 : ZMod 5957561123) ^ (11635861 + 11635861 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 11635861 * (2 : ZMod 5957561123) ^ 11635861) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 1004589703 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 5957561123) ^ 46543446 = 1166465598 := by
        calc
          (2 : ZMod 5957561123) ^ 46543446 = (2 : ZMod 5957561123) ^ (23271723 + 23271723) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 23271723 * (2 : ZMod 5957561123) ^ 23271723 := by rw [pow_add]
          _ = 1166465598 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 5957561123) ^ 93086892 = 3985905042 := by
        calc
          (2 : ZMod 5957561123) ^ 93086892 = (2 : ZMod 5957561123) ^ (46543446 + 46543446) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 46543446 * (2 : ZMod 5957561123) ^ 46543446 := by rw [pow_add]
          _ = 3985905042 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 5957561123) ^ 186173785 = 2340348566 := by
        calc
          (2 : ZMod 5957561123) ^ 186173785 = (2 : ZMod 5957561123) ^ (93086892 + 93086892 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 93086892 * (2 : ZMod 5957561123) ^ 93086892) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 2340348566 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 5957561123) ^ 372347570 = 5286506277 := by
        calc
          (2 : ZMod 5957561123) ^ 372347570 = (2 : ZMod 5957561123) ^ (186173785 + 186173785) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 186173785 * (2 : ZMod 5957561123) ^ 186173785 := by rw [pow_add]
          _ = 5286506277 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 5957561123) ^ 744695140 = 4791481860 := by
        calc
          (2 : ZMod 5957561123) ^ 744695140 = (2 : ZMod 5957561123) ^ (372347570 + 372347570) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 372347570 * (2 : ZMod 5957561123) ^ 372347570 := by rw [pow_add]
          _ = 4791481860 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 5957561123) ^ 1489390280 = 962495587 := by
        calc
          (2 : ZMod 5957561123) ^ 1489390280 = (2 : ZMod 5957561123) ^ (744695140 + 744695140) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 744695140 * (2 : ZMod 5957561123) ^ 744695140 := by rw [pow_add]
          _ = 962495587 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 5957561123) ^ 2978780561 = 5957561122 := by
        calc
          (2 : ZMod 5957561123) ^ 2978780561 = (2 : ZMod 5957561123) ^ (1489390280 + 1489390280 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 1489390280 * (2 : ZMod 5957561123) ^ 1489390280) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 5957561122 := by rw [factor_0_30]; decide
      change (2 : ZMod 5957561123) ^ 2978780561 ≠ 1
      rw [factor_0_31]
      decide
    ·
      have factor_1_0 : (2 : ZMod 5957561123) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 5957561123) ^ 3 = 8 := by
        calc
          (2 : ZMod 5957561123) ^ 3 = (2 : ZMod 5957561123) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 1 * (2 : ZMod 5957561123) ^ 1) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 5957561123) ^ 7 = 128 := by
        calc
          (2 : ZMod 5957561123) ^ 7 = (2 : ZMod 5957561123) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 3 * (2 : ZMod 5957561123) ^ 3) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 5957561123) ^ 15 = 32768 := by
        calc
          (2 : ZMod 5957561123) ^ 15 = (2 : ZMod 5957561123) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 7 * (2 : ZMod 5957561123) ^ 7) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 5957561123) ^ 30 = 1073741824 := by
        calc
          (2 : ZMod 5957561123) ^ 30 = (2 : ZMod 5957561123) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 15 * (2 : ZMod 5957561123) ^ 15 := by rw [pow_add]
          _ = 1073741824 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 5957561123) ^ 60 = 1767436268 := by
        calc
          (2 : ZMod 5957561123) ^ 60 = (2 : ZMod 5957561123) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 30 * (2 : ZMod 5957561123) ^ 30 := by rw [pow_add]
          _ = 1767436268 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 5957561123) ^ 121 = 198628137 := by
        calc
          (2 : ZMod 5957561123) ^ 121 = (2 : ZMod 5957561123) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 60 * (2 : ZMod 5957561123) ^ 60) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 198628137 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 5957561123) ^ 243 = 2956233117 := by
        calc
          (2 : ZMod 5957561123) ^ 243 = (2 : ZMod 5957561123) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 121 * (2 : ZMod 5957561123) ^ 121) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 2956233117 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 5957561123) ^ 487 = 528879312 := by
        calc
          (2 : ZMod 5957561123) ^ 487 = (2 : ZMod 5957561123) ^ (243 + 243 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 243 * (2 : ZMod 5957561123) ^ 243) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 528879312 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 5957561123) ^ 974 = 5441965050 := by
        calc
          (2 : ZMod 5957561123) ^ 974 = (2 : ZMod 5957561123) ^ (487 + 487) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 487 * (2 : ZMod 5957561123) ^ 487 := by rw [pow_add]
          _ = 5441965050 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 5957561123) ^ 1948 = 5277124419 := by
        calc
          (2 : ZMod 5957561123) ^ 1948 = (2 : ZMod 5957561123) ^ (974 + 974) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 974 * (2 : ZMod 5957561123) ^ 974 := by rw [pow_add]
          _ = 5277124419 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 5957561123) ^ 3896 = 5433456368 := by
        calc
          (2 : ZMod 5957561123) ^ 3896 = (2 : ZMod 5957561123) ^ (1948 + 1948) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 1948 * (2 : ZMod 5957561123) ^ 1948 := by rw [pow_add]
          _ = 5433456368 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 5957561123) ^ 7793 = 4457701525 := by
        calc
          (2 : ZMod 5957561123) ^ 7793 = (2 : ZMod 5957561123) ^ (3896 + 3896 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 3896 * (2 : ZMod 5957561123) ^ 3896) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 4457701525 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 5957561123) ^ 15587 = 2511756089 := by
        calc
          (2 : ZMod 5957561123) ^ 15587 = (2 : ZMod 5957561123) ^ (7793 + 7793 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 7793 * (2 : ZMod 5957561123) ^ 7793) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 2511756089 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 5957561123) ^ 31175 = 401716048 := by
        calc
          (2 : ZMod 5957561123) ^ 31175 = (2 : ZMod 5957561123) ^ (15587 + 15587 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 15587 * (2 : ZMod 5957561123) ^ 15587) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 401716048 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 5957561123) ^ 62351 = 1525861340 := by
        calc
          (2 : ZMod 5957561123) ^ 62351 = (2 : ZMod 5957561123) ^ (31175 + 31175 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 31175 * (2 : ZMod 5957561123) ^ 31175) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 1525861340 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 5957561123) ^ 124703 = 2620367549 := by
        calc
          (2 : ZMod 5957561123) ^ 124703 = (2 : ZMod 5957561123) ^ (62351 + 62351 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 62351 * (2 : ZMod 5957561123) ^ 62351) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 2620367549 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 5957561123) ^ 249406 = 1134272429 := by
        calc
          (2 : ZMod 5957561123) ^ 249406 = (2 : ZMod 5957561123) ^ (124703 + 124703) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 124703 * (2 : ZMod 5957561123) ^ 124703 := by rw [pow_add]
          _ = 1134272429 := by rw [factor_1_16]; decide
      change (2 : ZMod 5957561123) ^ 249406 ≠ 1
      rw [factor_1_17]
      decide
    ·
      have factor_2_0 : (2 : ZMod 5957561123) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 5957561123) ^ 2 = 4 := by
        calc
          (2 : ZMod 5957561123) ^ 2 = (2 : ZMod 5957561123) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 1 * (2 : ZMod 5957561123) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 5957561123) ^ 5 = 32 := by
        calc
          (2 : ZMod 5957561123) ^ 5 = (2 : ZMod 5957561123) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 2 * (2 : ZMod 5957561123) ^ 2) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 5957561123) ^ 11 = 2048 := by
        calc
          (2 : ZMod 5957561123) ^ 11 = (2 : ZMod 5957561123) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 5 * (2 : ZMod 5957561123) ^ 5) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 5957561123) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 5957561123) ^ 23 = (2 : ZMod 5957561123) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 11 * (2 : ZMod 5957561123) ^ 11) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 5957561123) ^ 46 = 3989753911 := by
        calc
          (2 : ZMod 5957561123) ^ 46 = (2 : ZMod 5957561123) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 23 * (2 : ZMod 5957561123) ^ 23 := by rw [pow_add]
          _ = 3989753911 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 5957561123) ^ 93 = 3248750381 := by
        calc
          (2 : ZMod 5957561123) ^ 93 = (2 : ZMod 5957561123) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 46 * (2 : ZMod 5957561123) ^ 46) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 3248750381 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 5957561123) ^ 186 = 4300278616 := by
        calc
          (2 : ZMod 5957561123) ^ 186 = (2 : ZMod 5957561123) ^ (93 + 93) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 93 * (2 : ZMod 5957561123) ^ 93 := by rw [pow_add]
          _ = 4300278616 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 5957561123) ^ 373 = 400079562 := by
        calc
          (2 : ZMod 5957561123) ^ 373 = (2 : ZMod 5957561123) ^ (186 + 186 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 186 * (2 : ZMod 5957561123) ^ 186) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 400079562 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 5957561123) ^ 746 = 2479400468 := by
        calc
          (2 : ZMod 5957561123) ^ 746 = (2 : ZMod 5957561123) ^ (373 + 373) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 373 * (2 : ZMod 5957561123) ^ 373 := by rw [pow_add]
          _ = 2479400468 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 5957561123) ^ 1492 = 3063290630 := by
        calc
          (2 : ZMod 5957561123) ^ 1492 = (2 : ZMod 5957561123) ^ (746 + 746) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 746 * (2 : ZMod 5957561123) ^ 746 := by rw [pow_add]
          _ = 3063290630 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 5957561123) ^ 2985 = 4167975039 := by
        calc
          (2 : ZMod 5957561123) ^ 2985 = (2 : ZMod 5957561123) ^ (1492 + 1492 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 1492 * (2 : ZMod 5957561123) ^ 1492) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 4167975039 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 5957561123) ^ 5971 = 394963566 := by
        calc
          (2 : ZMod 5957561123) ^ 5971 = (2 : ZMod 5957561123) ^ (2985 + 2985 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 2985 * (2 : ZMod 5957561123) ^ 2985) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 394963566 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 5957561123) ^ 11943 = 1020072770 := by
        calc
          (2 : ZMod 5957561123) ^ 11943 = (2 : ZMod 5957561123) ^ (5971 + 5971 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 5971 * (2 : ZMod 5957561123) ^ 5971) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 1020072770 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 5957561123) ^ 23887 = 4502593606 := by
        calc
          (2 : ZMod 5957561123) ^ 23887 = (2 : ZMod 5957561123) ^ (11943 + 11943 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = ((2 : ZMod 5957561123) ^ 11943 * (2 : ZMod 5957561123) ^ 11943) * (2 : ZMod 5957561123) := by rw [pow_succ, pow_add]
          _ = 4502593606 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 5957561123) ^ 47774 = 5363928203 := by
        calc
          (2 : ZMod 5957561123) ^ 47774 = (2 : ZMod 5957561123) ^ (23887 + 23887) :=
            congrArg (fun n : ℕ => (2 : ZMod 5957561123) ^ n) (by norm_num)
          _ = (2 : ZMod 5957561123) ^ 23887 * (2 : ZMod 5957561123) ^ 23887 := by rw [pow_add]
          _ = 5363928203 := by rw [factor_2_14]; decide
      change (2 : ZMod 5957561123) ^ 47774 ≠ 1
      rw [factor_2_15]
      decide

#print axioms prime_lucas_5957561123

end TotientTailPeriodKiller
end Erdos249257
