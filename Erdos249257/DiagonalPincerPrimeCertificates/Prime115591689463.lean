import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_115591689463 : Nat.Prime 115591689463 := by
  apply lucas_primality 115591689463 (3 : ZMod 115591689463)
  ·
      have fermat_0 : (3 : ZMod 115591689463) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 115591689463) ^ 3 = 27 := by
        calc
          (3 : ZMod 115591689463) ^ 3 = (3 : ZMod 115591689463) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 1 * (3 : ZMod 115591689463) ^ 1) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 115591689463) ^ 6 = 729 := by
        calc
          (3 : ZMod 115591689463) ^ 6 = (3 : ZMod 115591689463) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 3 * (3 : ZMod 115591689463) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 115591689463) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 115591689463) ^ 13 = (3 : ZMod 115591689463) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 6 * (3 : ZMod 115591689463) ^ 6) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 115591689463) ^ 26 = 114440349606 := by
        calc
          (3 : ZMod 115591689463) ^ 26 = (3 : ZMod 115591689463) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 13 * (3 : ZMod 115591689463) ^ 13 := by rw [pow_add]
          _ = 114440349606 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 115591689463) ^ 53 = 33111662183 := by
        calc
          (3 : ZMod 115591689463) ^ 53 = (3 : ZMod 115591689463) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 26 * (3 : ZMod 115591689463) ^ 26) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 33111662183 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 115591689463) ^ 107 = 6798063127 := by
        calc
          (3 : ZMod 115591689463) ^ 107 = (3 : ZMod 115591689463) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 53 * (3 : ZMod 115591689463) ^ 53) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 6798063127 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 115591689463) ^ 215 = 84713515027 := by
        calc
          (3 : ZMod 115591689463) ^ 215 = (3 : ZMod 115591689463) ^ (107 + 107 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 107 * (3 : ZMod 115591689463) ^ 107) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 84713515027 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 115591689463) ^ 430 = 81735619811 := by
        calc
          (3 : ZMod 115591689463) ^ 430 = (3 : ZMod 115591689463) ^ (215 + 215) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 215 * (3 : ZMod 115591689463) ^ 215 := by rw [pow_add]
          _ = 81735619811 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 115591689463) ^ 861 = 71740932237 := by
        calc
          (3 : ZMod 115591689463) ^ 861 = (3 : ZMod 115591689463) ^ (430 + 430 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 430 * (3 : ZMod 115591689463) ^ 430) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 71740932237 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 115591689463) ^ 1722 = 63539144131 := by
        calc
          (3 : ZMod 115591689463) ^ 1722 = (3 : ZMod 115591689463) ^ (861 + 861) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 861 * (3 : ZMod 115591689463) ^ 861 := by rw [pow_add]
          _ = 63539144131 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 115591689463) ^ 3444 = 79935293888 := by
        calc
          (3 : ZMod 115591689463) ^ 3444 = (3 : ZMod 115591689463) ^ (1722 + 1722) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 1722 * (3 : ZMod 115591689463) ^ 1722 := by rw [pow_add]
          _ = 79935293888 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 115591689463) ^ 6889 = 95991893725 := by
        calc
          (3 : ZMod 115591689463) ^ 6889 = (3 : ZMod 115591689463) ^ (3444 + 3444 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 3444 * (3 : ZMod 115591689463) ^ 3444) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 95991893725 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 115591689463) ^ 13779 = 31260946742 := by
        calc
          (3 : ZMod 115591689463) ^ 13779 = (3 : ZMod 115591689463) ^ (6889 + 6889 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 6889 * (3 : ZMod 115591689463) ^ 6889) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 31260946742 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 115591689463) ^ 27559 = 93492398794 := by
        calc
          (3 : ZMod 115591689463) ^ 27559 = (3 : ZMod 115591689463) ^ (13779 + 13779 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 13779 * (3 : ZMod 115591689463) ^ 13779) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 93492398794 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 115591689463) ^ 55118 = 9708925634 := by
        calc
          (3 : ZMod 115591689463) ^ 55118 = (3 : ZMod 115591689463) ^ (27559 + 27559) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 27559 * (3 : ZMod 115591689463) ^ 27559 := by rw [pow_add]
          _ = 9708925634 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 115591689463) ^ 110236 = 101068005306 := by
        calc
          (3 : ZMod 115591689463) ^ 110236 = (3 : ZMod 115591689463) ^ (55118 + 55118) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 55118 * (3 : ZMod 115591689463) ^ 55118 := by rw [pow_add]
          _ = 101068005306 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 115591689463) ^ 220473 = 81141805092 := by
        calc
          (3 : ZMod 115591689463) ^ 220473 = (3 : ZMod 115591689463) ^ (110236 + 110236 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 110236 * (3 : ZMod 115591689463) ^ 110236) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 81141805092 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 115591689463) ^ 440947 = 25766887630 := by
        calc
          (3 : ZMod 115591689463) ^ 440947 = (3 : ZMod 115591689463) ^ (220473 + 220473 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 220473 * (3 : ZMod 115591689463) ^ 220473) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 25766887630 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 115591689463) ^ 881894 = 5543687821 := by
        calc
          (3 : ZMod 115591689463) ^ 881894 = (3 : ZMod 115591689463) ^ (440947 + 440947) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 440947 * (3 : ZMod 115591689463) ^ 440947 := by rw [pow_add]
          _ = 5543687821 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 115591689463) ^ 1763789 = 50119727330 := by
        calc
          (3 : ZMod 115591689463) ^ 1763789 = (3 : ZMod 115591689463) ^ (881894 + 881894 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 881894 * (3 : ZMod 115591689463) ^ 881894) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 50119727330 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 115591689463) ^ 3527578 = 109003297725 := by
        calc
          (3 : ZMod 115591689463) ^ 3527578 = (3 : ZMod 115591689463) ^ (1763789 + 1763789) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 1763789 * (3 : ZMod 115591689463) ^ 1763789 := by rw [pow_add]
          _ = 109003297725 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 115591689463) ^ 7055156 = 4051103264 := by
        calc
          (3 : ZMod 115591689463) ^ 7055156 = (3 : ZMod 115591689463) ^ (3527578 + 3527578) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 3527578 * (3 : ZMod 115591689463) ^ 3527578 := by rw [pow_add]
          _ = 4051103264 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 115591689463) ^ 14110313 = 94972481885 := by
        calc
          (3 : ZMod 115591689463) ^ 14110313 = (3 : ZMod 115591689463) ^ (7055156 + 7055156 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 7055156 * (3 : ZMod 115591689463) ^ 7055156) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 94972481885 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 115591689463) ^ 28220627 = 24352694570 := by
        calc
          (3 : ZMod 115591689463) ^ 28220627 = (3 : ZMod 115591689463) ^ (14110313 + 14110313 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 14110313 * (3 : ZMod 115591689463) ^ 14110313) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 24352694570 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 115591689463) ^ 56441254 = 94518109254 := by
        calc
          (3 : ZMod 115591689463) ^ 56441254 = (3 : ZMod 115591689463) ^ (28220627 + 28220627) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 28220627 * (3 : ZMod 115591689463) ^ 28220627 := by rw [pow_add]
          _ = 94518109254 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 115591689463) ^ 112882509 = 45045069389 := by
        calc
          (3 : ZMod 115591689463) ^ 112882509 = (3 : ZMod 115591689463) ^ (56441254 + 56441254 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 56441254 * (3 : ZMod 115591689463) ^ 56441254) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 45045069389 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 115591689463) ^ 225765018 = 46989430296 := by
        calc
          (3 : ZMod 115591689463) ^ 225765018 = (3 : ZMod 115591689463) ^ (112882509 + 112882509) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 112882509 * (3 : ZMod 115591689463) ^ 112882509 := by rw [pow_add]
          _ = 46989430296 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 115591689463) ^ 451530036 = 74448049079 := by
        calc
          (3 : ZMod 115591689463) ^ 451530036 = (3 : ZMod 115591689463) ^ (225765018 + 225765018) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 225765018 * (3 : ZMod 115591689463) ^ 225765018 := by rw [pow_add]
          _ = 74448049079 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 115591689463) ^ 903060073 = 113320360736 := by
        calc
          (3 : ZMod 115591689463) ^ 903060073 = (3 : ZMod 115591689463) ^ (451530036 + 451530036 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 451530036 * (3 : ZMod 115591689463) ^ 451530036) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 113320360736 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 115591689463) ^ 1806120147 = 72706325587 := by
        calc
          (3 : ZMod 115591689463) ^ 1806120147 = (3 : ZMod 115591689463) ^ (903060073 + 903060073 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 903060073 * (3 : ZMod 115591689463) ^ 903060073) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 72706325587 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 115591689463) ^ 3612240295 = 54168273394 := by
        calc
          (3 : ZMod 115591689463) ^ 3612240295 = (3 : ZMod 115591689463) ^ (1806120147 + 1806120147 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 1806120147 * (3 : ZMod 115591689463) ^ 1806120147) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 54168273394 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 115591689463) ^ 7224480591 = 106574406142 := by
        calc
          (3 : ZMod 115591689463) ^ 7224480591 = (3 : ZMod 115591689463) ^ (3612240295 + 3612240295 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 3612240295 * (3 : ZMod 115591689463) ^ 3612240295) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 106574406142 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 115591689463) ^ 14448961182 = 53164819731 := by
        calc
          (3 : ZMod 115591689463) ^ 14448961182 = (3 : ZMod 115591689463) ^ (7224480591 + 7224480591) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 7224480591 * (3 : ZMod 115591689463) ^ 7224480591 := by rw [pow_add]
          _ = 53164819731 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 115591689463) ^ 28897922365 = 40389720050 := by
        calc
          (3 : ZMod 115591689463) ^ 28897922365 = (3 : ZMod 115591689463) ^ (14448961182 + 14448961182 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 14448961182 * (3 : ZMod 115591689463) ^ 14448961182) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 40389720050 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 115591689463) ^ 57795844731 = 115591689462 := by
        calc
          (3 : ZMod 115591689463) ^ 57795844731 = (3 : ZMod 115591689463) ^ (28897922365 + 28897922365 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 28897922365 * (3 : ZMod 115591689463) ^ 28897922365) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 115591689462 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 115591689463) ^ 115591689462 = 1 := by
        calc
          (3 : ZMod 115591689463) ^ 115591689462 = (3 : ZMod 115591689463) ^ (57795844731 + 57795844731) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 57795844731 * (3 : ZMod 115591689463) ^ 57795844731 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (601, 1), (32055377, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (601, 1), (32055377, 1)] : List FactorBlock).map factorBlockValue).prod = 115591689463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 115591689463) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 115591689463) ^ 3 = 27 := by
        calc
          (3 : ZMod 115591689463) ^ 3 = (3 : ZMod 115591689463) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 1 * (3 : ZMod 115591689463) ^ 1) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 115591689463) ^ 6 = 729 := by
        calc
          (3 : ZMod 115591689463) ^ 6 = (3 : ZMod 115591689463) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 3 * (3 : ZMod 115591689463) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 115591689463) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 115591689463) ^ 13 = (3 : ZMod 115591689463) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 6 * (3 : ZMod 115591689463) ^ 6) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 115591689463) ^ 26 = 114440349606 := by
        calc
          (3 : ZMod 115591689463) ^ 26 = (3 : ZMod 115591689463) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 13 * (3 : ZMod 115591689463) ^ 13 := by rw [pow_add]
          _ = 114440349606 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 115591689463) ^ 53 = 33111662183 := by
        calc
          (3 : ZMod 115591689463) ^ 53 = (3 : ZMod 115591689463) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 26 * (3 : ZMod 115591689463) ^ 26) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 33111662183 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 115591689463) ^ 107 = 6798063127 := by
        calc
          (3 : ZMod 115591689463) ^ 107 = (3 : ZMod 115591689463) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 53 * (3 : ZMod 115591689463) ^ 53) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 6798063127 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 115591689463) ^ 215 = 84713515027 := by
        calc
          (3 : ZMod 115591689463) ^ 215 = (3 : ZMod 115591689463) ^ (107 + 107 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 107 * (3 : ZMod 115591689463) ^ 107) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 84713515027 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 115591689463) ^ 430 = 81735619811 := by
        calc
          (3 : ZMod 115591689463) ^ 430 = (3 : ZMod 115591689463) ^ (215 + 215) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 215 * (3 : ZMod 115591689463) ^ 215 := by rw [pow_add]
          _ = 81735619811 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 115591689463) ^ 861 = 71740932237 := by
        calc
          (3 : ZMod 115591689463) ^ 861 = (3 : ZMod 115591689463) ^ (430 + 430 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 430 * (3 : ZMod 115591689463) ^ 430) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 71740932237 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 115591689463) ^ 1722 = 63539144131 := by
        calc
          (3 : ZMod 115591689463) ^ 1722 = (3 : ZMod 115591689463) ^ (861 + 861) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 861 * (3 : ZMod 115591689463) ^ 861 := by rw [pow_add]
          _ = 63539144131 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 115591689463) ^ 3444 = 79935293888 := by
        calc
          (3 : ZMod 115591689463) ^ 3444 = (3 : ZMod 115591689463) ^ (1722 + 1722) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 1722 * (3 : ZMod 115591689463) ^ 1722 := by rw [pow_add]
          _ = 79935293888 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 115591689463) ^ 6889 = 95991893725 := by
        calc
          (3 : ZMod 115591689463) ^ 6889 = (3 : ZMod 115591689463) ^ (3444 + 3444 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 3444 * (3 : ZMod 115591689463) ^ 3444) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 95991893725 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 115591689463) ^ 13779 = 31260946742 := by
        calc
          (3 : ZMod 115591689463) ^ 13779 = (3 : ZMod 115591689463) ^ (6889 + 6889 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 6889 * (3 : ZMod 115591689463) ^ 6889) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 31260946742 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 115591689463) ^ 27559 = 93492398794 := by
        calc
          (3 : ZMod 115591689463) ^ 27559 = (3 : ZMod 115591689463) ^ (13779 + 13779 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 13779 * (3 : ZMod 115591689463) ^ 13779) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 93492398794 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 115591689463) ^ 55118 = 9708925634 := by
        calc
          (3 : ZMod 115591689463) ^ 55118 = (3 : ZMod 115591689463) ^ (27559 + 27559) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 27559 * (3 : ZMod 115591689463) ^ 27559 := by rw [pow_add]
          _ = 9708925634 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 115591689463) ^ 110236 = 101068005306 := by
        calc
          (3 : ZMod 115591689463) ^ 110236 = (3 : ZMod 115591689463) ^ (55118 + 55118) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 55118 * (3 : ZMod 115591689463) ^ 55118 := by rw [pow_add]
          _ = 101068005306 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 115591689463) ^ 220473 = 81141805092 := by
        calc
          (3 : ZMod 115591689463) ^ 220473 = (3 : ZMod 115591689463) ^ (110236 + 110236 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 110236 * (3 : ZMod 115591689463) ^ 110236) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 81141805092 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 115591689463) ^ 440947 = 25766887630 := by
        calc
          (3 : ZMod 115591689463) ^ 440947 = (3 : ZMod 115591689463) ^ (220473 + 220473 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 220473 * (3 : ZMod 115591689463) ^ 220473) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 25766887630 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 115591689463) ^ 881894 = 5543687821 := by
        calc
          (3 : ZMod 115591689463) ^ 881894 = (3 : ZMod 115591689463) ^ (440947 + 440947) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 440947 * (3 : ZMod 115591689463) ^ 440947 := by rw [pow_add]
          _ = 5543687821 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 115591689463) ^ 1763789 = 50119727330 := by
        calc
          (3 : ZMod 115591689463) ^ 1763789 = (3 : ZMod 115591689463) ^ (881894 + 881894 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 881894 * (3 : ZMod 115591689463) ^ 881894) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 50119727330 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 115591689463) ^ 3527578 = 109003297725 := by
        calc
          (3 : ZMod 115591689463) ^ 3527578 = (3 : ZMod 115591689463) ^ (1763789 + 1763789) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 1763789 * (3 : ZMod 115591689463) ^ 1763789 := by rw [pow_add]
          _ = 109003297725 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 115591689463) ^ 7055156 = 4051103264 := by
        calc
          (3 : ZMod 115591689463) ^ 7055156 = (3 : ZMod 115591689463) ^ (3527578 + 3527578) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 3527578 * (3 : ZMod 115591689463) ^ 3527578 := by rw [pow_add]
          _ = 4051103264 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 115591689463) ^ 14110313 = 94972481885 := by
        calc
          (3 : ZMod 115591689463) ^ 14110313 = (3 : ZMod 115591689463) ^ (7055156 + 7055156 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 7055156 * (3 : ZMod 115591689463) ^ 7055156) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 94972481885 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 115591689463) ^ 28220627 = 24352694570 := by
        calc
          (3 : ZMod 115591689463) ^ 28220627 = (3 : ZMod 115591689463) ^ (14110313 + 14110313 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 14110313 * (3 : ZMod 115591689463) ^ 14110313) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 24352694570 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 115591689463) ^ 56441254 = 94518109254 := by
        calc
          (3 : ZMod 115591689463) ^ 56441254 = (3 : ZMod 115591689463) ^ (28220627 + 28220627) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 28220627 * (3 : ZMod 115591689463) ^ 28220627 := by rw [pow_add]
          _ = 94518109254 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 115591689463) ^ 112882509 = 45045069389 := by
        calc
          (3 : ZMod 115591689463) ^ 112882509 = (3 : ZMod 115591689463) ^ (56441254 + 56441254 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 56441254 * (3 : ZMod 115591689463) ^ 56441254) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 45045069389 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 115591689463) ^ 225765018 = 46989430296 := by
        calc
          (3 : ZMod 115591689463) ^ 225765018 = (3 : ZMod 115591689463) ^ (112882509 + 112882509) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 112882509 * (3 : ZMod 115591689463) ^ 112882509 := by rw [pow_add]
          _ = 46989430296 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 115591689463) ^ 451530036 = 74448049079 := by
        calc
          (3 : ZMod 115591689463) ^ 451530036 = (3 : ZMod 115591689463) ^ (225765018 + 225765018) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 225765018 * (3 : ZMod 115591689463) ^ 225765018 := by rw [pow_add]
          _ = 74448049079 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 115591689463) ^ 903060073 = 113320360736 := by
        calc
          (3 : ZMod 115591689463) ^ 903060073 = (3 : ZMod 115591689463) ^ (451530036 + 451530036 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 451530036 * (3 : ZMod 115591689463) ^ 451530036) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 113320360736 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 115591689463) ^ 1806120147 = 72706325587 := by
        calc
          (3 : ZMod 115591689463) ^ 1806120147 = (3 : ZMod 115591689463) ^ (903060073 + 903060073 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 903060073 * (3 : ZMod 115591689463) ^ 903060073) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 72706325587 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 115591689463) ^ 3612240295 = 54168273394 := by
        calc
          (3 : ZMod 115591689463) ^ 3612240295 = (3 : ZMod 115591689463) ^ (1806120147 + 1806120147 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 1806120147 * (3 : ZMod 115591689463) ^ 1806120147) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 54168273394 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 115591689463) ^ 7224480591 = 106574406142 := by
        calc
          (3 : ZMod 115591689463) ^ 7224480591 = (3 : ZMod 115591689463) ^ (3612240295 + 3612240295 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 3612240295 * (3 : ZMod 115591689463) ^ 3612240295) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 106574406142 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 115591689463) ^ 14448961182 = 53164819731 := by
        calc
          (3 : ZMod 115591689463) ^ 14448961182 = (3 : ZMod 115591689463) ^ (7224480591 + 7224480591) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 7224480591 * (3 : ZMod 115591689463) ^ 7224480591 := by rw [pow_add]
          _ = 53164819731 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 115591689463) ^ 28897922365 = 40389720050 := by
        calc
          (3 : ZMod 115591689463) ^ 28897922365 = (3 : ZMod 115591689463) ^ (14448961182 + 14448961182 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 14448961182 * (3 : ZMod 115591689463) ^ 14448961182) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 40389720050 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 115591689463) ^ 57795844731 = 115591689462 := by
        calc
          (3 : ZMod 115591689463) ^ 57795844731 = (3 : ZMod 115591689463) ^ (28897922365 + 28897922365 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 28897922365 * (3 : ZMod 115591689463) ^ 28897922365) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 115591689462 := by rw [factor_0_34]; decide
      change (3 : ZMod 115591689463) ^ 57795844731 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (3 : ZMod 115591689463) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 115591689463) ^ 2 = 9 := by
        calc
          (3 : ZMod 115591689463) ^ 2 = (3 : ZMod 115591689463) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 1 * (3 : ZMod 115591689463) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 115591689463) ^ 4 = 81 := by
        calc
          (3 : ZMod 115591689463) ^ 4 = (3 : ZMod 115591689463) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 2 * (3 : ZMod 115591689463) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 115591689463) ^ 8 = 6561 := by
        calc
          (3 : ZMod 115591689463) ^ 8 = (3 : ZMod 115591689463) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 4 * (3 : ZMod 115591689463) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 115591689463) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 115591689463) ^ 17 = (3 : ZMod 115591689463) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 8 * (3 : ZMod 115591689463) ^ 8) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 115591689463) ^ 35 = 109740418880 := by
        calc
          (3 : ZMod 115591689463) ^ 35 = (3 : ZMod 115591689463) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 17 * (3 : ZMod 115591689463) ^ 17) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 109740418880 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 115591689463) ^ 71 = 107440511542 := by
        calc
          (3 : ZMod 115591689463) ^ 71 = (3 : ZMod 115591689463) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 35 * (3 : ZMod 115591689463) ^ 35) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 107440511542 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 115591689463) ^ 143 = 1575719572 := by
        calc
          (3 : ZMod 115591689463) ^ 143 = (3 : ZMod 115591689463) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 71 * (3 : ZMod 115591689463) ^ 71) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 1575719572 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 115591689463) ^ 287 = 56016127902 := by
        calc
          (3 : ZMod 115591689463) ^ 287 = (3 : ZMod 115591689463) ^ (143 + 143 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 143 * (3 : ZMod 115591689463) ^ 143) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 56016127902 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 115591689463) ^ 574 = 101331828934 := by
        calc
          (3 : ZMod 115591689463) ^ 574 = (3 : ZMod 115591689463) ^ (287 + 287) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 287 * (3 : ZMod 115591689463) ^ 287 := by rw [pow_add]
          _ = 101331828934 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 115591689463) ^ 1148 = 4171750958 := by
        calc
          (3 : ZMod 115591689463) ^ 1148 = (3 : ZMod 115591689463) ^ (574 + 574) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 574 * (3 : ZMod 115591689463) ^ 574 := by rw [pow_add]
          _ = 4171750958 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 115591689463) ^ 2296 = 21153776572 := by
        calc
          (3 : ZMod 115591689463) ^ 2296 = (3 : ZMod 115591689463) ^ (1148 + 1148) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 1148 * (3 : ZMod 115591689463) ^ 1148 := by rw [pow_add]
          _ = 21153776572 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 115591689463) ^ 4593 = 22868459481 := by
        calc
          (3 : ZMod 115591689463) ^ 4593 = (3 : ZMod 115591689463) ^ (2296 + 2296 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 2296 * (3 : ZMod 115591689463) ^ 2296) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 22868459481 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 115591689463) ^ 9186 = 43815507569 := by
        calc
          (3 : ZMod 115591689463) ^ 9186 = (3 : ZMod 115591689463) ^ (4593 + 4593) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 4593 * (3 : ZMod 115591689463) ^ 4593 := by rw [pow_add]
          _ = 43815507569 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 115591689463) ^ 18372 = 100360304994 := by
        calc
          (3 : ZMod 115591689463) ^ 18372 = (3 : ZMod 115591689463) ^ (9186 + 9186) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 9186 * (3 : ZMod 115591689463) ^ 9186 := by rw [pow_add]
          _ = 100360304994 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 115591689463) ^ 36745 = 55208654078 := by
        calc
          (3 : ZMod 115591689463) ^ 36745 = (3 : ZMod 115591689463) ^ (18372 + 18372 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 18372 * (3 : ZMod 115591689463) ^ 18372) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 55208654078 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 115591689463) ^ 73491 = 85872601296 := by
        calc
          (3 : ZMod 115591689463) ^ 73491 = (3 : ZMod 115591689463) ^ (36745 + 36745 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 36745 * (3 : ZMod 115591689463) ^ 36745) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 85872601296 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 115591689463) ^ 146982 = 28141157016 := by
        calc
          (3 : ZMod 115591689463) ^ 146982 = (3 : ZMod 115591689463) ^ (73491 + 73491) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 73491 * (3 : ZMod 115591689463) ^ 73491 := by rw [pow_add]
          _ = 28141157016 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 115591689463) ^ 293964 = 35784157483 := by
        calc
          (3 : ZMod 115591689463) ^ 293964 = (3 : ZMod 115591689463) ^ (146982 + 146982) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 146982 * (3 : ZMod 115591689463) ^ 146982 := by rw [pow_add]
          _ = 35784157483 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 115591689463) ^ 587929 = 45812633410 := by
        calc
          (3 : ZMod 115591689463) ^ 587929 = (3 : ZMod 115591689463) ^ (293964 + 293964 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 293964 * (3 : ZMod 115591689463) ^ 293964) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 45812633410 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 115591689463) ^ 1175859 = 112819343412 := by
        calc
          (3 : ZMod 115591689463) ^ 1175859 = (3 : ZMod 115591689463) ^ (587929 + 587929 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 587929 * (3 : ZMod 115591689463) ^ 587929) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 112819343412 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 115591689463) ^ 2351718 = 8083775700 := by
        calc
          (3 : ZMod 115591689463) ^ 2351718 = (3 : ZMod 115591689463) ^ (1175859 + 1175859) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 1175859 * (3 : ZMod 115591689463) ^ 1175859 := by rw [pow_add]
          _ = 8083775700 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 115591689463) ^ 4703437 = 92606757538 := by
        calc
          (3 : ZMod 115591689463) ^ 4703437 = (3 : ZMod 115591689463) ^ (2351718 + 2351718 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 2351718 * (3 : ZMod 115591689463) ^ 2351718) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 92606757538 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 115591689463) ^ 9406875 = 52846328802 := by
        calc
          (3 : ZMod 115591689463) ^ 9406875 = (3 : ZMod 115591689463) ^ (4703437 + 4703437 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 4703437 * (3 : ZMod 115591689463) ^ 4703437) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 52846328802 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 115591689463) ^ 18813751 = 95638717846 := by
        calc
          (3 : ZMod 115591689463) ^ 18813751 = (3 : ZMod 115591689463) ^ (9406875 + 9406875 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 9406875 * (3 : ZMod 115591689463) ^ 9406875) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 95638717846 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 115591689463) ^ 37627503 = 74939465413 := by
        calc
          (3 : ZMod 115591689463) ^ 37627503 = (3 : ZMod 115591689463) ^ (18813751 + 18813751 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 18813751 * (3 : ZMod 115591689463) ^ 18813751) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 74939465413 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 115591689463) ^ 75255006 = 48627732471 := by
        calc
          (3 : ZMod 115591689463) ^ 75255006 = (3 : ZMod 115591689463) ^ (37627503 + 37627503) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 37627503 * (3 : ZMod 115591689463) ^ 37627503 := by rw [pow_add]
          _ = 48627732471 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 115591689463) ^ 150510012 = 27772446728 := by
        calc
          (3 : ZMod 115591689463) ^ 150510012 = (3 : ZMod 115591689463) ^ (75255006 + 75255006) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 75255006 * (3 : ZMod 115591689463) ^ 75255006 := by rw [pow_add]
          _ = 27772446728 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 115591689463) ^ 301020024 = 14453644405 := by
        calc
          (3 : ZMod 115591689463) ^ 301020024 = (3 : ZMod 115591689463) ^ (150510012 + 150510012) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 150510012 * (3 : ZMod 115591689463) ^ 150510012 := by rw [pow_add]
          _ = 14453644405 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 115591689463) ^ 602040049 = 45904433448 := by
        calc
          (3 : ZMod 115591689463) ^ 602040049 = (3 : ZMod 115591689463) ^ (301020024 + 301020024 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 301020024 * (3 : ZMod 115591689463) ^ 301020024) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 45904433448 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 115591689463) ^ 1204080098 = 30214630504 := by
        calc
          (3 : ZMod 115591689463) ^ 1204080098 = (3 : ZMod 115591689463) ^ (602040049 + 602040049) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 602040049 * (3 : ZMod 115591689463) ^ 602040049 := by rw [pow_add]
          _ = 30214630504 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 115591689463) ^ 2408160197 = 43002339494 := by
        calc
          (3 : ZMod 115591689463) ^ 2408160197 = (3 : ZMod 115591689463) ^ (1204080098 + 1204080098 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 1204080098 * (3 : ZMod 115591689463) ^ 1204080098) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 43002339494 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 115591689463) ^ 4816320394 = 109649231563 := by
        calc
          (3 : ZMod 115591689463) ^ 4816320394 = (3 : ZMod 115591689463) ^ (2408160197 + 2408160197) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 2408160197 * (3 : ZMod 115591689463) ^ 2408160197 := by rw [pow_add]
          _ = 109649231563 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 115591689463) ^ 9632640788 = 77990704757 := by
        calc
          (3 : ZMod 115591689463) ^ 9632640788 = (3 : ZMod 115591689463) ^ (4816320394 + 4816320394) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 4816320394 * (3 : ZMod 115591689463) ^ 4816320394 := by rw [pow_add]
          _ = 77990704757 := by rw [factor_1_32]; decide
      have factor_1_34 : (3 : ZMod 115591689463) ^ 19265281577 = 2788735344 := by
        calc
          (3 : ZMod 115591689463) ^ 19265281577 = (3 : ZMod 115591689463) ^ (9632640788 + 9632640788 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 9632640788 * (3 : ZMod 115591689463) ^ 9632640788) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 2788735344 := by rw [factor_1_33]; decide
      have factor_1_35 : (3 : ZMod 115591689463) ^ 38530563154 = 2788735343 := by
        calc
          (3 : ZMod 115591689463) ^ 38530563154 = (3 : ZMod 115591689463) ^ (19265281577 + 19265281577) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 19265281577 * (3 : ZMod 115591689463) ^ 19265281577 := by rw [pow_add]
          _ = 2788735343 := by rw [factor_1_34]; decide
      change (3 : ZMod 115591689463) ^ 38530563154 ≠ 1
      rw [factor_1_35]
      decide
    ·
      have factor_2_0 : (3 : ZMod 115591689463) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 115591689463) ^ 2 = 9 := by
        calc
          (3 : ZMod 115591689463) ^ 2 = (3 : ZMod 115591689463) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 1 * (3 : ZMod 115591689463) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 115591689463) ^ 5 = 243 := by
        calc
          (3 : ZMod 115591689463) ^ 5 = (3 : ZMod 115591689463) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 2 * (3 : ZMod 115591689463) ^ 2) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 115591689463) ^ 11 = 177147 := by
        calc
          (3 : ZMod 115591689463) ^ 11 = (3 : ZMod 115591689463) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 5 * (3 : ZMod 115591689463) ^ 5) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 115591689463) ^ 22 = 31381059609 := by
        calc
          (3 : ZMod 115591689463) ^ 22 = (3 : ZMod 115591689463) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 11 * (3 : ZMod 115591689463) ^ 11 := by rw [pow_add]
          _ = 31381059609 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 115591689463) ^ 45 = 107474838803 := by
        calc
          (3 : ZMod 115591689463) ^ 45 = (3 : ZMod 115591689463) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 22 * (3 : ZMod 115591689463) ^ 22) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 107474838803 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 115591689463) ^ 91 = 109296261236 := by
        calc
          (3 : ZMod 115591689463) ^ 91 = (3 : ZMod 115591689463) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 45 * (3 : ZMod 115591689463) ^ 45) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 109296261236 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 115591689463) ^ 183 = 51046378166 := by
        calc
          (3 : ZMod 115591689463) ^ 183 = (3 : ZMod 115591689463) ^ (91 + 91 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 91 * (3 : ZMod 115591689463) ^ 91) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 51046378166 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 115591689463) ^ 366 = 107277560700 := by
        calc
          (3 : ZMod 115591689463) ^ 366 = (3 : ZMod 115591689463) ^ (183 + 183) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 183 * (3 : ZMod 115591689463) ^ 183 := by rw [pow_add]
          _ = 107277560700 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 115591689463) ^ 733 = 31789908265 := by
        calc
          (3 : ZMod 115591689463) ^ 733 = (3 : ZMod 115591689463) ^ (366 + 366 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 366 * (3 : ZMod 115591689463) ^ 366) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 31789908265 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 115591689463) ^ 1467 = 25868604130 := by
        calc
          (3 : ZMod 115591689463) ^ 1467 = (3 : ZMod 115591689463) ^ (733 + 733 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 733 * (3 : ZMod 115591689463) ^ 733) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 25868604130 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 115591689463) ^ 2934 = 64827811215 := by
        calc
          (3 : ZMod 115591689463) ^ 2934 = (3 : ZMod 115591689463) ^ (1467 + 1467) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 1467 * (3 : ZMod 115591689463) ^ 1467 := by rw [pow_add]
          _ = 64827811215 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 115591689463) ^ 5869 = 77195103740 := by
        calc
          (3 : ZMod 115591689463) ^ 5869 = (3 : ZMod 115591689463) ^ (2934 + 2934 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 2934 * (3 : ZMod 115591689463) ^ 2934) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 77195103740 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 115591689463) ^ 11739 = 42152858885 := by
        calc
          (3 : ZMod 115591689463) ^ 11739 = (3 : ZMod 115591689463) ^ (5869 + 5869 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 5869 * (3 : ZMod 115591689463) ^ 5869) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 42152858885 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 115591689463) ^ 23478 = 63175181865 := by
        calc
          (3 : ZMod 115591689463) ^ 23478 = (3 : ZMod 115591689463) ^ (11739 + 11739) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 11739 * (3 : ZMod 115591689463) ^ 11739 := by rw [pow_add]
          _ = 63175181865 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 115591689463) ^ 46956 = 97373745396 := by
        calc
          (3 : ZMod 115591689463) ^ 46956 = (3 : ZMod 115591689463) ^ (23478 + 23478) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 23478 * (3 : ZMod 115591689463) ^ 23478 := by rw [pow_add]
          _ = 97373745396 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 115591689463) ^ 93912 = 23842918310 := by
        calc
          (3 : ZMod 115591689463) ^ 93912 = (3 : ZMod 115591689463) ^ (46956 + 46956) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 46956 * (3 : ZMod 115591689463) ^ 46956 := by rw [pow_add]
          _ = 23842918310 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 115591689463) ^ 187824 = 76772759943 := by
        calc
          (3 : ZMod 115591689463) ^ 187824 = (3 : ZMod 115591689463) ^ (93912 + 93912) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 93912 * (3 : ZMod 115591689463) ^ 93912 := by rw [pow_add]
          _ = 76772759943 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 115591689463) ^ 375648 = 27827124634 := by
        calc
          (3 : ZMod 115591689463) ^ 375648 = (3 : ZMod 115591689463) ^ (187824 + 187824) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 187824 * (3 : ZMod 115591689463) ^ 187824 := by rw [pow_add]
          _ = 27827124634 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 115591689463) ^ 751297 = 41491450569 := by
        calc
          (3 : ZMod 115591689463) ^ 751297 = (3 : ZMod 115591689463) ^ (375648 + 375648 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 375648 * (3 : ZMod 115591689463) ^ 375648) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 41491450569 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 115591689463) ^ 1502595 = 38316912103 := by
        calc
          (3 : ZMod 115591689463) ^ 1502595 = (3 : ZMod 115591689463) ^ (751297 + 751297 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 751297 * (3 : ZMod 115591689463) ^ 751297) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 38316912103 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 115591689463) ^ 3005191 = 73678720744 := by
        calc
          (3 : ZMod 115591689463) ^ 3005191 = (3 : ZMod 115591689463) ^ (1502595 + 1502595 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 1502595 * (3 : ZMod 115591689463) ^ 1502595) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 73678720744 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 115591689463) ^ 6010383 = 2602468614 := by
        calc
          (3 : ZMod 115591689463) ^ 6010383 = (3 : ZMod 115591689463) ^ (3005191 + 3005191 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 3005191 * (3 : ZMod 115591689463) ^ 3005191) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 2602468614 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 115591689463) ^ 12020766 = 63837004262 := by
        calc
          (3 : ZMod 115591689463) ^ 12020766 = (3 : ZMod 115591689463) ^ (6010383 + 6010383) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 6010383 * (3 : ZMod 115591689463) ^ 6010383 := by rw [pow_add]
          _ = 63837004262 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 115591689463) ^ 24041532 = 89701619457 := by
        calc
          (3 : ZMod 115591689463) ^ 24041532 = (3 : ZMod 115591689463) ^ (12020766 + 12020766) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 12020766 * (3 : ZMod 115591689463) ^ 12020766 := by rw [pow_add]
          _ = 89701619457 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 115591689463) ^ 48083065 = 82766398426 := by
        calc
          (3 : ZMod 115591689463) ^ 48083065 = (3 : ZMod 115591689463) ^ (24041532 + 24041532 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 24041532 * (3 : ZMod 115591689463) ^ 24041532) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 82766398426 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 115591689463) ^ 96166131 = 18738709266 := by
        calc
          (3 : ZMod 115591689463) ^ 96166131 = (3 : ZMod 115591689463) ^ (48083065 + 48083065 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 48083065 * (3 : ZMod 115591689463) ^ 48083065) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 18738709266 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 115591689463) ^ 192332262 = 75641887777 := by
        calc
          (3 : ZMod 115591689463) ^ 192332262 = (3 : ZMod 115591689463) ^ (96166131 + 96166131) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 96166131 * (3 : ZMod 115591689463) ^ 96166131 := by rw [pow_add]
          _ = 75641887777 := by rw [factor_2_26]; decide
      change (3 : ZMod 115591689463) ^ 192332262 ≠ 1
      rw [factor_2_27]
      decide
    ·
      have factor_3_0 : (3 : ZMod 115591689463) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 115591689463) ^ 3 = 27 := by
        calc
          (3 : ZMod 115591689463) ^ 3 = (3 : ZMod 115591689463) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 1 * (3 : ZMod 115591689463) ^ 1) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 115591689463) ^ 7 = 2187 := by
        calc
          (3 : ZMod 115591689463) ^ 7 = (3 : ZMod 115591689463) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 3 * (3 : ZMod 115591689463) ^ 3) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 115591689463) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 115591689463) ^ 14 = (3 : ZMod 115591689463) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 7 * (3 : ZMod 115591689463) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 115591689463) ^ 28 = 105229630750 := by
        calc
          (3 : ZMod 115591689463) ^ 28 = (3 : ZMod 115591689463) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 14 * (3 : ZMod 115591689463) ^ 14 := by rw [pow_add]
          _ = 105229630750 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 115591689463) ^ 56 = 84873052700 := by
        calc
          (3 : ZMod 115591689463) ^ 56 = (3 : ZMod 115591689463) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 28 * (3 : ZMod 115591689463) ^ 28 := by rw [pow_add]
          _ = 84873052700 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 115591689463) ^ 112 = 33645687379 := by
        calc
          (3 : ZMod 115591689463) ^ 112 = (3 : ZMod 115591689463) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 56 * (3 : ZMod 115591689463) ^ 56 := by rw [pow_add]
          _ = 33645687379 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 115591689463) ^ 225 = 17987317998 := by
        calc
          (3 : ZMod 115591689463) ^ 225 = (3 : ZMod 115591689463) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 112 * (3 : ZMod 115591689463) ^ 112) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 17987317998 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 115591689463) ^ 450 = 106608972083 := by
        calc
          (3 : ZMod 115591689463) ^ 450 = (3 : ZMod 115591689463) ^ (225 + 225) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 225 * (3 : ZMod 115591689463) ^ 225 := by rw [pow_add]
          _ = 106608972083 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 115591689463) ^ 901 = 3248073710 := by
        calc
          (3 : ZMod 115591689463) ^ 901 = (3 : ZMod 115591689463) ^ (450 + 450 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 450 * (3 : ZMod 115591689463) ^ 450) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 3248073710 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 115591689463) ^ 1803 = 95665626905 := by
        calc
          (3 : ZMod 115591689463) ^ 1803 = (3 : ZMod 115591689463) ^ (901 + 901 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = ((3 : ZMod 115591689463) ^ 901 * (3 : ZMod 115591689463) ^ 901) * (3 : ZMod 115591689463) := by rw [pow_succ, pow_add]
          _ = 95665626905 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 115591689463) ^ 3606 = 58044942514 := by
        calc
          (3 : ZMod 115591689463) ^ 3606 = (3 : ZMod 115591689463) ^ (1803 + 1803) :=
            congrArg (fun n : ℕ => (3 : ZMod 115591689463) ^ n) (by norm_num)
          _ = (3 : ZMod 115591689463) ^ 1803 * (3 : ZMod 115591689463) ^ 1803 := by rw [pow_add]
          _ = 58044942514 := by rw [factor_3_10]; decide
      change (3 : ZMod 115591689463) ^ 3606 ≠ 1
      rw [factor_3_11]
      decide

#print axioms prime_lucas_115591689463

end TotientTailPeriodKiller
end Erdos249257
