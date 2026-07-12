import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_89580367801 : Nat.Prime 89580367801 := by
  apply lucas_primality 89580367801 (13 : ZMod 89580367801)
  ·
      have fermat_0 : (13 : ZMod 89580367801) ^ 1 = 13 := by norm_num
      have fermat_1 : (13 : ZMod 89580367801) ^ 2 = 169 := by
        calc
          (13 : ZMod 89580367801) ^ 2 = (13 : ZMod 89580367801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1 * (13 : ZMod 89580367801) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [fermat_0]; decide
      have fermat_2 : (13 : ZMod 89580367801) ^ 5 = 371293 := by
        calc
          (13 : ZMod 89580367801) ^ 5 = (13 : ZMod 89580367801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 2 * (13 : ZMod 89580367801) ^ 2) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 371293 := by rw [fermat_1]; decide
      have fermat_3 : (13 : ZMod 89580367801) ^ 10 = 48278124048 := by
        calc
          (13 : ZMod 89580367801) ^ 10 = (13 : ZMod 89580367801) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 5 * (13 : ZMod 89580367801) ^ 5 := by rw [pow_add]
          _ = 48278124048 := by rw [fermat_2]; decide
      have fermat_4 : (13 : ZMod 89580367801) ^ 20 = 70106308453 := by
        calc
          (13 : ZMod 89580367801) ^ 20 = (13 : ZMod 89580367801) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 10 * (13 : ZMod 89580367801) ^ 10 := by rw [pow_add]
          _ = 70106308453 := by rw [fermat_3]; decide
      have fermat_5 : (13 : ZMod 89580367801) ^ 41 = 13875565533 := by
        calc
          (13 : ZMod 89580367801) ^ 41 = (13 : ZMod 89580367801) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 20 * (13 : ZMod 89580367801) ^ 20) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 13875565533 := by rw [fermat_4]; decide
      have fermat_6 : (13 : ZMod 89580367801) ^ 83 = 17621982433 := by
        calc
          (13 : ZMod 89580367801) ^ 83 = (13 : ZMod 89580367801) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 41 * (13 : ZMod 89580367801) ^ 41) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 17621982433 := by rw [fermat_5]; decide
      have fermat_7 : (13 : ZMod 89580367801) ^ 166 = 29059863331 := by
        calc
          (13 : ZMod 89580367801) ^ 166 = (13 : ZMod 89580367801) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 83 * (13 : ZMod 89580367801) ^ 83 := by rw [pow_add]
          _ = 29059863331 := by rw [fermat_6]; decide
      have fermat_8 : (13 : ZMod 89580367801) ^ 333 = 78587614323 := by
        calc
          (13 : ZMod 89580367801) ^ 333 = (13 : ZMod 89580367801) ^ (166 + 166 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 166 * (13 : ZMod 89580367801) ^ 166) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 78587614323 := by rw [fermat_7]; decide
      have fermat_9 : (13 : ZMod 89580367801) ^ 667 = 30510468725 := by
        calc
          (13 : ZMod 89580367801) ^ 667 = (13 : ZMod 89580367801) ^ (333 + 333 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 333 * (13 : ZMod 89580367801) ^ 333) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 30510468725 := by rw [fermat_8]; decide
      have fermat_10 : (13 : ZMod 89580367801) ^ 1334 = 67998358283 := by
        calc
          (13 : ZMod 89580367801) ^ 1334 = (13 : ZMod 89580367801) ^ (667 + 667) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 667 * (13 : ZMod 89580367801) ^ 667 := by rw [pow_add]
          _ = 67998358283 := by rw [fermat_9]; decide
      have fermat_11 : (13 : ZMod 89580367801) ^ 2669 = 11798726794 := by
        calc
          (13 : ZMod 89580367801) ^ 2669 = (13 : ZMod 89580367801) ^ (1334 + 1334 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1334 * (13 : ZMod 89580367801) ^ 1334) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 11798726794 := by rw [fermat_10]; decide
      have fermat_12 : (13 : ZMod 89580367801) ^ 5339 = 21752003771 := by
        calc
          (13 : ZMod 89580367801) ^ 5339 = (13 : ZMod 89580367801) ^ (2669 + 2669 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 2669 * (13 : ZMod 89580367801) ^ 2669) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 21752003771 := by rw [fermat_11]; decide
      have fermat_13 : (13 : ZMod 89580367801) ^ 10678 = 31139039080 := by
        calc
          (13 : ZMod 89580367801) ^ 10678 = (13 : ZMod 89580367801) ^ (5339 + 5339) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 5339 * (13 : ZMod 89580367801) ^ 5339 := by rw [pow_add]
          _ = 31139039080 := by rw [fermat_12]; decide
      have fermat_14 : (13 : ZMod 89580367801) ^ 21357 = 48583767561 := by
        calc
          (13 : ZMod 89580367801) ^ 21357 = (13 : ZMod 89580367801) ^ (10678 + 10678 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 10678 * (13 : ZMod 89580367801) ^ 10678) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 48583767561 := by rw [fermat_13]; decide
      have fermat_15 : (13 : ZMod 89580367801) ^ 42715 = 58440797330 := by
        calc
          (13 : ZMod 89580367801) ^ 42715 = (13 : ZMod 89580367801) ^ (21357 + 21357 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 21357 * (13 : ZMod 89580367801) ^ 21357) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 58440797330 := by rw [fermat_14]; decide
      have fermat_16 : (13 : ZMod 89580367801) ^ 85430 = 69804603048 := by
        calc
          (13 : ZMod 89580367801) ^ 85430 = (13 : ZMod 89580367801) ^ (42715 + 42715) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 42715 * (13 : ZMod 89580367801) ^ 42715 := by rw [pow_add]
          _ = 69804603048 := by rw [fermat_15]; decide
      have fermat_17 : (13 : ZMod 89580367801) ^ 170860 = 50447059574 := by
        calc
          (13 : ZMod 89580367801) ^ 170860 = (13 : ZMod 89580367801) ^ (85430 + 85430) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 85430 * (13 : ZMod 89580367801) ^ 85430 := by rw [pow_add]
          _ = 50447059574 := by rw [fermat_16]; decide
      have fermat_18 : (13 : ZMod 89580367801) ^ 341721 = 23873074845 := by
        calc
          (13 : ZMod 89580367801) ^ 341721 = (13 : ZMod 89580367801) ^ (170860 + 170860 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 170860 * (13 : ZMod 89580367801) ^ 170860) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 23873074845 := by rw [fermat_17]; decide
      have fermat_19 : (13 : ZMod 89580367801) ^ 683443 = 49754117325 := by
        calc
          (13 : ZMod 89580367801) ^ 683443 = (13 : ZMod 89580367801) ^ (341721 + 341721 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 341721 * (13 : ZMod 89580367801) ^ 341721) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 49754117325 := by rw [fermat_18]; decide
      have fermat_20 : (13 : ZMod 89580367801) ^ 1366887 = 45154665008 := by
        calc
          (13 : ZMod 89580367801) ^ 1366887 = (13 : ZMod 89580367801) ^ (683443 + 683443 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 683443 * (13 : ZMod 89580367801) ^ 683443) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 45154665008 := by rw [fermat_19]; decide
      have fermat_21 : (13 : ZMod 89580367801) ^ 2733775 = 43331707257 := by
        calc
          (13 : ZMod 89580367801) ^ 2733775 = (13 : ZMod 89580367801) ^ (1366887 + 1366887 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1366887 * (13 : ZMod 89580367801) ^ 1366887) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 43331707257 := by rw [fermat_20]; decide
      have fermat_22 : (13 : ZMod 89580367801) ^ 5467551 = 46344022140 := by
        calc
          (13 : ZMod 89580367801) ^ 5467551 = (13 : ZMod 89580367801) ^ (2733775 + 2733775 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 2733775 * (13 : ZMod 89580367801) ^ 2733775) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 46344022140 := by rw [fermat_21]; decide
      have fermat_23 : (13 : ZMod 89580367801) ^ 10935103 = 18557959264 := by
        calc
          (13 : ZMod 89580367801) ^ 10935103 = (13 : ZMod 89580367801) ^ (5467551 + 5467551 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 5467551 * (13 : ZMod 89580367801) ^ 5467551) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 18557959264 := by rw [fermat_22]; decide
      have fermat_24 : (13 : ZMod 89580367801) ^ 21870206 = 19538390888 := by
        calc
          (13 : ZMod 89580367801) ^ 21870206 = (13 : ZMod 89580367801) ^ (10935103 + 10935103) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 10935103 * (13 : ZMod 89580367801) ^ 10935103 := by rw [pow_add]
          _ = 19538390888 := by rw [fermat_23]; decide
      have fermat_25 : (13 : ZMod 89580367801) ^ 43740413 = 52416283572 := by
        calc
          (13 : ZMod 89580367801) ^ 43740413 = (13 : ZMod 89580367801) ^ (21870206 + 21870206 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 21870206 * (13 : ZMod 89580367801) ^ 21870206) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 52416283572 := by rw [fermat_24]; decide
      have fermat_26 : (13 : ZMod 89580367801) ^ 87480827 = 59467243783 := by
        calc
          (13 : ZMod 89580367801) ^ 87480827 = (13 : ZMod 89580367801) ^ (43740413 + 43740413 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 43740413 * (13 : ZMod 89580367801) ^ 43740413) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 59467243783 := by rw [fermat_25]; decide
      have fermat_27 : (13 : ZMod 89580367801) ^ 174961655 = 5841994298 := by
        calc
          (13 : ZMod 89580367801) ^ 174961655 = (13 : ZMod 89580367801) ^ (87480827 + 87480827 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 87480827 * (13 : ZMod 89580367801) ^ 87480827) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 5841994298 := by rw [fermat_26]; decide
      have fermat_28 : (13 : ZMod 89580367801) ^ 349923311 = 50991218300 := by
        calc
          (13 : ZMod 89580367801) ^ 349923311 = (13 : ZMod 89580367801) ^ (174961655 + 174961655 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 174961655 * (13 : ZMod 89580367801) ^ 174961655) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 50991218300 := by rw [fermat_27]; decide
      have fermat_29 : (13 : ZMod 89580367801) ^ 699846623 = 77612967261 := by
        calc
          (13 : ZMod 89580367801) ^ 699846623 = (13 : ZMod 89580367801) ^ (349923311 + 349923311 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 349923311 * (13 : ZMod 89580367801) ^ 349923311) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 77612967261 := by rw [fermat_28]; decide
      have fermat_30 : (13 : ZMod 89580367801) ^ 1399693246 = 74974923575 := by
        calc
          (13 : ZMod 89580367801) ^ 1399693246 = (13 : ZMod 89580367801) ^ (699846623 + 699846623) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 699846623 * (13 : ZMod 89580367801) ^ 699846623 := by rw [pow_add]
          _ = 74974923575 := by rw [fermat_29]; decide
      have fermat_31 : (13 : ZMod 89580367801) ^ 2799386493 = 8069882911 := by
        calc
          (13 : ZMod 89580367801) ^ 2799386493 = (13 : ZMod 89580367801) ^ (1399693246 + 1399693246 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1399693246 * (13 : ZMod 89580367801) ^ 1399693246) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 8069882911 := by rw [fermat_30]; decide
      have fermat_32 : (13 : ZMod 89580367801) ^ 5598772987 = 64408641999 := by
        calc
          (13 : ZMod 89580367801) ^ 5598772987 = (13 : ZMod 89580367801) ^ (2799386493 + 2799386493 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 2799386493 * (13 : ZMod 89580367801) ^ 2799386493) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 64408641999 := by rw [fermat_31]; decide
      have fermat_33 : (13 : ZMod 89580367801) ^ 11197545975 = 72800645810 := by
        calc
          (13 : ZMod 89580367801) ^ 11197545975 = (13 : ZMod 89580367801) ^ (5598772987 + 5598772987 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 5598772987 * (13 : ZMod 89580367801) ^ 5598772987) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 72800645810 := by rw [fermat_32]; decide
      have fermat_34 : (13 : ZMod 89580367801) ^ 22395091950 = 10685830265 := by
        calc
          (13 : ZMod 89580367801) ^ 22395091950 = (13 : ZMod 89580367801) ^ (11197545975 + 11197545975) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 11197545975 * (13 : ZMod 89580367801) ^ 11197545975 := by rw [pow_add]
          _ = 10685830265 := by rw [fermat_33]; decide
      have fermat_35 : (13 : ZMod 89580367801) ^ 44790183900 = 89580367800 := by
        calc
          (13 : ZMod 89580367801) ^ 44790183900 = (13 : ZMod 89580367801) ^ (22395091950 + 22395091950) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 22395091950 * (13 : ZMod 89580367801) ^ 22395091950 := by rw [pow_add]
          _ = 89580367800 := by rw [fermat_34]; decide
      have fermat_36 : (13 : ZMod 89580367801) ^ 89580367800 = 1 := by
        calc
          (13 : ZMod 89580367801) ^ 89580367800 = (13 : ZMod 89580367801) ^ (44790183900 + 44790183900) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 44790183900 * (13 : ZMod 89580367801) ^ 44790183900 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 3), (5, 2), (7, 1), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 3), (5, 2), (7, 1), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod = 89580367801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (13 : ZMod 89580367801) ^ 1 = 13 := by norm_num
      have factor_0_1 : (13 : ZMod 89580367801) ^ 2 = 169 := by
        calc
          (13 : ZMod 89580367801) ^ 2 = (13 : ZMod 89580367801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1 * (13 : ZMod 89580367801) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_0_0]; decide
      have factor_0_2 : (13 : ZMod 89580367801) ^ 5 = 371293 := by
        calc
          (13 : ZMod 89580367801) ^ 5 = (13 : ZMod 89580367801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 2 * (13 : ZMod 89580367801) ^ 2) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 371293 := by rw [factor_0_1]; decide
      have factor_0_3 : (13 : ZMod 89580367801) ^ 10 = 48278124048 := by
        calc
          (13 : ZMod 89580367801) ^ 10 = (13 : ZMod 89580367801) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 5 * (13 : ZMod 89580367801) ^ 5 := by rw [pow_add]
          _ = 48278124048 := by rw [factor_0_2]; decide
      have factor_0_4 : (13 : ZMod 89580367801) ^ 20 = 70106308453 := by
        calc
          (13 : ZMod 89580367801) ^ 20 = (13 : ZMod 89580367801) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 10 * (13 : ZMod 89580367801) ^ 10 := by rw [pow_add]
          _ = 70106308453 := by rw [factor_0_3]; decide
      have factor_0_5 : (13 : ZMod 89580367801) ^ 41 = 13875565533 := by
        calc
          (13 : ZMod 89580367801) ^ 41 = (13 : ZMod 89580367801) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 20 * (13 : ZMod 89580367801) ^ 20) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 13875565533 := by rw [factor_0_4]; decide
      have factor_0_6 : (13 : ZMod 89580367801) ^ 83 = 17621982433 := by
        calc
          (13 : ZMod 89580367801) ^ 83 = (13 : ZMod 89580367801) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 41 * (13 : ZMod 89580367801) ^ 41) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 17621982433 := by rw [factor_0_5]; decide
      have factor_0_7 : (13 : ZMod 89580367801) ^ 166 = 29059863331 := by
        calc
          (13 : ZMod 89580367801) ^ 166 = (13 : ZMod 89580367801) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 83 * (13 : ZMod 89580367801) ^ 83 := by rw [pow_add]
          _ = 29059863331 := by rw [factor_0_6]; decide
      have factor_0_8 : (13 : ZMod 89580367801) ^ 333 = 78587614323 := by
        calc
          (13 : ZMod 89580367801) ^ 333 = (13 : ZMod 89580367801) ^ (166 + 166 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 166 * (13 : ZMod 89580367801) ^ 166) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 78587614323 := by rw [factor_0_7]; decide
      have factor_0_9 : (13 : ZMod 89580367801) ^ 667 = 30510468725 := by
        calc
          (13 : ZMod 89580367801) ^ 667 = (13 : ZMod 89580367801) ^ (333 + 333 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 333 * (13 : ZMod 89580367801) ^ 333) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 30510468725 := by rw [factor_0_8]; decide
      have factor_0_10 : (13 : ZMod 89580367801) ^ 1334 = 67998358283 := by
        calc
          (13 : ZMod 89580367801) ^ 1334 = (13 : ZMod 89580367801) ^ (667 + 667) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 667 * (13 : ZMod 89580367801) ^ 667 := by rw [pow_add]
          _ = 67998358283 := by rw [factor_0_9]; decide
      have factor_0_11 : (13 : ZMod 89580367801) ^ 2669 = 11798726794 := by
        calc
          (13 : ZMod 89580367801) ^ 2669 = (13 : ZMod 89580367801) ^ (1334 + 1334 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1334 * (13 : ZMod 89580367801) ^ 1334) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 11798726794 := by rw [factor_0_10]; decide
      have factor_0_12 : (13 : ZMod 89580367801) ^ 5339 = 21752003771 := by
        calc
          (13 : ZMod 89580367801) ^ 5339 = (13 : ZMod 89580367801) ^ (2669 + 2669 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 2669 * (13 : ZMod 89580367801) ^ 2669) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 21752003771 := by rw [factor_0_11]; decide
      have factor_0_13 : (13 : ZMod 89580367801) ^ 10678 = 31139039080 := by
        calc
          (13 : ZMod 89580367801) ^ 10678 = (13 : ZMod 89580367801) ^ (5339 + 5339) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 5339 * (13 : ZMod 89580367801) ^ 5339 := by rw [pow_add]
          _ = 31139039080 := by rw [factor_0_12]; decide
      have factor_0_14 : (13 : ZMod 89580367801) ^ 21357 = 48583767561 := by
        calc
          (13 : ZMod 89580367801) ^ 21357 = (13 : ZMod 89580367801) ^ (10678 + 10678 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 10678 * (13 : ZMod 89580367801) ^ 10678) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 48583767561 := by rw [factor_0_13]; decide
      have factor_0_15 : (13 : ZMod 89580367801) ^ 42715 = 58440797330 := by
        calc
          (13 : ZMod 89580367801) ^ 42715 = (13 : ZMod 89580367801) ^ (21357 + 21357 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 21357 * (13 : ZMod 89580367801) ^ 21357) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 58440797330 := by rw [factor_0_14]; decide
      have factor_0_16 : (13 : ZMod 89580367801) ^ 85430 = 69804603048 := by
        calc
          (13 : ZMod 89580367801) ^ 85430 = (13 : ZMod 89580367801) ^ (42715 + 42715) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 42715 * (13 : ZMod 89580367801) ^ 42715 := by rw [pow_add]
          _ = 69804603048 := by rw [factor_0_15]; decide
      have factor_0_17 : (13 : ZMod 89580367801) ^ 170860 = 50447059574 := by
        calc
          (13 : ZMod 89580367801) ^ 170860 = (13 : ZMod 89580367801) ^ (85430 + 85430) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 85430 * (13 : ZMod 89580367801) ^ 85430 := by rw [pow_add]
          _ = 50447059574 := by rw [factor_0_16]; decide
      have factor_0_18 : (13 : ZMod 89580367801) ^ 341721 = 23873074845 := by
        calc
          (13 : ZMod 89580367801) ^ 341721 = (13 : ZMod 89580367801) ^ (170860 + 170860 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 170860 * (13 : ZMod 89580367801) ^ 170860) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 23873074845 := by rw [factor_0_17]; decide
      have factor_0_19 : (13 : ZMod 89580367801) ^ 683443 = 49754117325 := by
        calc
          (13 : ZMod 89580367801) ^ 683443 = (13 : ZMod 89580367801) ^ (341721 + 341721 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 341721 * (13 : ZMod 89580367801) ^ 341721) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 49754117325 := by rw [factor_0_18]; decide
      have factor_0_20 : (13 : ZMod 89580367801) ^ 1366887 = 45154665008 := by
        calc
          (13 : ZMod 89580367801) ^ 1366887 = (13 : ZMod 89580367801) ^ (683443 + 683443 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 683443 * (13 : ZMod 89580367801) ^ 683443) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 45154665008 := by rw [factor_0_19]; decide
      have factor_0_21 : (13 : ZMod 89580367801) ^ 2733775 = 43331707257 := by
        calc
          (13 : ZMod 89580367801) ^ 2733775 = (13 : ZMod 89580367801) ^ (1366887 + 1366887 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1366887 * (13 : ZMod 89580367801) ^ 1366887) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 43331707257 := by rw [factor_0_20]; decide
      have factor_0_22 : (13 : ZMod 89580367801) ^ 5467551 = 46344022140 := by
        calc
          (13 : ZMod 89580367801) ^ 5467551 = (13 : ZMod 89580367801) ^ (2733775 + 2733775 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 2733775 * (13 : ZMod 89580367801) ^ 2733775) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 46344022140 := by rw [factor_0_21]; decide
      have factor_0_23 : (13 : ZMod 89580367801) ^ 10935103 = 18557959264 := by
        calc
          (13 : ZMod 89580367801) ^ 10935103 = (13 : ZMod 89580367801) ^ (5467551 + 5467551 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 5467551 * (13 : ZMod 89580367801) ^ 5467551) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 18557959264 := by rw [factor_0_22]; decide
      have factor_0_24 : (13 : ZMod 89580367801) ^ 21870206 = 19538390888 := by
        calc
          (13 : ZMod 89580367801) ^ 21870206 = (13 : ZMod 89580367801) ^ (10935103 + 10935103) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 10935103 * (13 : ZMod 89580367801) ^ 10935103 := by rw [pow_add]
          _ = 19538390888 := by rw [factor_0_23]; decide
      have factor_0_25 : (13 : ZMod 89580367801) ^ 43740413 = 52416283572 := by
        calc
          (13 : ZMod 89580367801) ^ 43740413 = (13 : ZMod 89580367801) ^ (21870206 + 21870206 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 21870206 * (13 : ZMod 89580367801) ^ 21870206) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 52416283572 := by rw [factor_0_24]; decide
      have factor_0_26 : (13 : ZMod 89580367801) ^ 87480827 = 59467243783 := by
        calc
          (13 : ZMod 89580367801) ^ 87480827 = (13 : ZMod 89580367801) ^ (43740413 + 43740413 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 43740413 * (13 : ZMod 89580367801) ^ 43740413) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 59467243783 := by rw [factor_0_25]; decide
      have factor_0_27 : (13 : ZMod 89580367801) ^ 174961655 = 5841994298 := by
        calc
          (13 : ZMod 89580367801) ^ 174961655 = (13 : ZMod 89580367801) ^ (87480827 + 87480827 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 87480827 * (13 : ZMod 89580367801) ^ 87480827) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 5841994298 := by rw [factor_0_26]; decide
      have factor_0_28 : (13 : ZMod 89580367801) ^ 349923311 = 50991218300 := by
        calc
          (13 : ZMod 89580367801) ^ 349923311 = (13 : ZMod 89580367801) ^ (174961655 + 174961655 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 174961655 * (13 : ZMod 89580367801) ^ 174961655) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 50991218300 := by rw [factor_0_27]; decide
      have factor_0_29 : (13 : ZMod 89580367801) ^ 699846623 = 77612967261 := by
        calc
          (13 : ZMod 89580367801) ^ 699846623 = (13 : ZMod 89580367801) ^ (349923311 + 349923311 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 349923311 * (13 : ZMod 89580367801) ^ 349923311) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 77612967261 := by rw [factor_0_28]; decide
      have factor_0_30 : (13 : ZMod 89580367801) ^ 1399693246 = 74974923575 := by
        calc
          (13 : ZMod 89580367801) ^ 1399693246 = (13 : ZMod 89580367801) ^ (699846623 + 699846623) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 699846623 * (13 : ZMod 89580367801) ^ 699846623 := by rw [pow_add]
          _ = 74974923575 := by rw [factor_0_29]; decide
      have factor_0_31 : (13 : ZMod 89580367801) ^ 2799386493 = 8069882911 := by
        calc
          (13 : ZMod 89580367801) ^ 2799386493 = (13 : ZMod 89580367801) ^ (1399693246 + 1399693246 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1399693246 * (13 : ZMod 89580367801) ^ 1399693246) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 8069882911 := by rw [factor_0_30]; decide
      have factor_0_32 : (13 : ZMod 89580367801) ^ 5598772987 = 64408641999 := by
        calc
          (13 : ZMod 89580367801) ^ 5598772987 = (13 : ZMod 89580367801) ^ (2799386493 + 2799386493 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 2799386493 * (13 : ZMod 89580367801) ^ 2799386493) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 64408641999 := by rw [factor_0_31]; decide
      have factor_0_33 : (13 : ZMod 89580367801) ^ 11197545975 = 72800645810 := by
        calc
          (13 : ZMod 89580367801) ^ 11197545975 = (13 : ZMod 89580367801) ^ (5598772987 + 5598772987 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 5598772987 * (13 : ZMod 89580367801) ^ 5598772987) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 72800645810 := by rw [factor_0_32]; decide
      have factor_0_34 : (13 : ZMod 89580367801) ^ 22395091950 = 10685830265 := by
        calc
          (13 : ZMod 89580367801) ^ 22395091950 = (13 : ZMod 89580367801) ^ (11197545975 + 11197545975) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 11197545975 * (13 : ZMod 89580367801) ^ 11197545975 := by rw [pow_add]
          _ = 10685830265 := by rw [factor_0_33]; decide
      have factor_0_35 : (13 : ZMod 89580367801) ^ 44790183900 = 89580367800 := by
        calc
          (13 : ZMod 89580367801) ^ 44790183900 = (13 : ZMod 89580367801) ^ (22395091950 + 22395091950) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 22395091950 * (13 : ZMod 89580367801) ^ 22395091950 := by rw [pow_add]
          _ = 89580367800 := by rw [factor_0_34]; decide
      change (13 : ZMod 89580367801) ^ 44790183900 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (13 : ZMod 89580367801) ^ 1 = 13 := by norm_num
      have factor_1_1 : (13 : ZMod 89580367801) ^ 3 = 2197 := by
        calc
          (13 : ZMod 89580367801) ^ 3 = (13 : ZMod 89580367801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1 * (13 : ZMod 89580367801) ^ 1) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_1_0]; decide
      have factor_1_2 : (13 : ZMod 89580367801) ^ 6 = 4826809 := by
        calc
          (13 : ZMod 89580367801) ^ 6 = (13 : ZMod 89580367801) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 3 * (13 : ZMod 89580367801) ^ 3 := by rw [pow_add]
          _ = 4826809 := by rw [factor_1_1]; decide
      have factor_1_3 : (13 : ZMod 89580367801) ^ 13 = 3883057072 := by
        calc
          (13 : ZMod 89580367801) ^ 13 = (13 : ZMod 89580367801) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 6 * (13 : ZMod 89580367801) ^ 6) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 3883057072 := by rw [factor_1_2]; decide
      have factor_1_4 : (13 : ZMod 89580367801) ^ 27 = 50947120313 := by
        calc
          (13 : ZMod 89580367801) ^ 27 = (13 : ZMod 89580367801) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 13 * (13 : ZMod 89580367801) ^ 13) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 50947120313 := by rw [factor_1_3]; decide
      have factor_1_5 : (13 : ZMod 89580367801) ^ 55 = 86869211312 := by
        calc
          (13 : ZMod 89580367801) ^ 55 = (13 : ZMod 89580367801) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 27 * (13 : ZMod 89580367801) ^ 27) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 86869211312 := by rw [factor_1_4]; decide
      have factor_1_6 : (13 : ZMod 89580367801) ^ 111 = 16321603789 := by
        calc
          (13 : ZMod 89580367801) ^ 111 = (13 : ZMod 89580367801) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 55 * (13 : ZMod 89580367801) ^ 55) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 16321603789 := by rw [factor_1_5]; decide
      have factor_1_7 : (13 : ZMod 89580367801) ^ 222 = 64666661838 := by
        calc
          (13 : ZMod 89580367801) ^ 222 = (13 : ZMod 89580367801) ^ (111 + 111) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 111 * (13 : ZMod 89580367801) ^ 111 := by rw [pow_add]
          _ = 64666661838 := by rw [factor_1_6]; decide
      have factor_1_8 : (13 : ZMod 89580367801) ^ 444 = 26185986600 := by
        calc
          (13 : ZMod 89580367801) ^ 444 = (13 : ZMod 89580367801) ^ (222 + 222) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 222 * (13 : ZMod 89580367801) ^ 222 := by rw [pow_add]
          _ = 26185986600 := by rw [factor_1_7]; decide
      have factor_1_9 : (13 : ZMod 89580367801) ^ 889 = 26262965542 := by
        calc
          (13 : ZMod 89580367801) ^ 889 = (13 : ZMod 89580367801) ^ (444 + 444 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 444 * (13 : ZMod 89580367801) ^ 444) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 26262965542 := by rw [factor_1_8]; decide
      have factor_1_10 : (13 : ZMod 89580367801) ^ 1779 = 51350889403 := by
        calc
          (13 : ZMod 89580367801) ^ 1779 = (13 : ZMod 89580367801) ^ (889 + 889 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 889 * (13 : ZMod 89580367801) ^ 889) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 51350889403 := by rw [factor_1_9]; decide
      have factor_1_11 : (13 : ZMod 89580367801) ^ 3559 = 45261410049 := by
        calc
          (13 : ZMod 89580367801) ^ 3559 = (13 : ZMod 89580367801) ^ (1779 + 1779 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1779 * (13 : ZMod 89580367801) ^ 1779) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 45261410049 := by rw [factor_1_10]; decide
      have factor_1_12 : (13 : ZMod 89580367801) ^ 7119 = 70469597601 := by
        calc
          (13 : ZMod 89580367801) ^ 7119 = (13 : ZMod 89580367801) ^ (3559 + 3559 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 3559 * (13 : ZMod 89580367801) ^ 3559) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 70469597601 := by rw [factor_1_11]; decide
      have factor_1_13 : (13 : ZMod 89580367801) ^ 14238 = 22507026853 := by
        calc
          (13 : ZMod 89580367801) ^ 14238 = (13 : ZMod 89580367801) ^ (7119 + 7119) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 7119 * (13 : ZMod 89580367801) ^ 7119 := by rw [pow_add]
          _ = 22507026853 := by rw [factor_1_12]; decide
      have factor_1_14 : (13 : ZMod 89580367801) ^ 28476 = 79551656503 := by
        calc
          (13 : ZMod 89580367801) ^ 28476 = (13 : ZMod 89580367801) ^ (14238 + 14238) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 14238 * (13 : ZMod 89580367801) ^ 14238 := by rw [pow_add]
          _ = 79551656503 := by rw [factor_1_13]; decide
      have factor_1_15 : (13 : ZMod 89580367801) ^ 56953 = 38018092620 := by
        calc
          (13 : ZMod 89580367801) ^ 56953 = (13 : ZMod 89580367801) ^ (28476 + 28476 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 28476 * (13 : ZMod 89580367801) ^ 28476) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 38018092620 := by rw [factor_1_14]; decide
      have factor_1_16 : (13 : ZMod 89580367801) ^ 113907 = 66782772530 := by
        calc
          (13 : ZMod 89580367801) ^ 113907 = (13 : ZMod 89580367801) ^ (56953 + 56953 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 56953 * (13 : ZMod 89580367801) ^ 56953) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 66782772530 := by rw [factor_1_15]; decide
      have factor_1_17 : (13 : ZMod 89580367801) ^ 227814 = 45456494062 := by
        calc
          (13 : ZMod 89580367801) ^ 227814 = (13 : ZMod 89580367801) ^ (113907 + 113907) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 113907 * (13 : ZMod 89580367801) ^ 113907 := by rw [pow_add]
          _ = 45456494062 := by rw [factor_1_16]; decide
      have factor_1_18 : (13 : ZMod 89580367801) ^ 455629 = 41481806824 := by
        calc
          (13 : ZMod 89580367801) ^ 455629 = (13 : ZMod 89580367801) ^ (227814 + 227814 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 227814 * (13 : ZMod 89580367801) ^ 227814) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 41481806824 := by rw [factor_1_17]; decide
      have factor_1_19 : (13 : ZMod 89580367801) ^ 911258 = 71706176908 := by
        calc
          (13 : ZMod 89580367801) ^ 911258 = (13 : ZMod 89580367801) ^ (455629 + 455629) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 455629 * (13 : ZMod 89580367801) ^ 455629 := by rw [pow_add]
          _ = 71706176908 := by rw [factor_1_18]; decide
      have factor_1_20 : (13 : ZMod 89580367801) ^ 1822517 = 32390385285 := by
        calc
          (13 : ZMod 89580367801) ^ 1822517 = (13 : ZMod 89580367801) ^ (911258 + 911258 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 911258 * (13 : ZMod 89580367801) ^ 911258) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 32390385285 := by rw [factor_1_19]; decide
      have factor_1_21 : (13 : ZMod 89580367801) ^ 3645034 = 83253066125 := by
        calc
          (13 : ZMod 89580367801) ^ 3645034 = (13 : ZMod 89580367801) ^ (1822517 + 1822517) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1822517 * (13 : ZMod 89580367801) ^ 1822517 := by rw [pow_add]
          _ = 83253066125 := by rw [factor_1_20]; decide
      have factor_1_22 : (13 : ZMod 89580367801) ^ 7290068 = 25389632686 := by
        calc
          (13 : ZMod 89580367801) ^ 7290068 = (13 : ZMod 89580367801) ^ (3645034 + 3645034) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 3645034 * (13 : ZMod 89580367801) ^ 3645034 := by rw [pow_add]
          _ = 25389632686 := by rw [factor_1_21]; decide
      have factor_1_23 : (13 : ZMod 89580367801) ^ 14580137 = 61831942981 := by
        calc
          (13 : ZMod 89580367801) ^ 14580137 = (13 : ZMod 89580367801) ^ (7290068 + 7290068 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 7290068 * (13 : ZMod 89580367801) ^ 7290068) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 61831942981 := by rw [factor_1_22]; decide
      have factor_1_24 : (13 : ZMod 89580367801) ^ 29160275 = 21814557630 := by
        calc
          (13 : ZMod 89580367801) ^ 29160275 = (13 : ZMod 89580367801) ^ (14580137 + 14580137 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 14580137 * (13 : ZMod 89580367801) ^ 14580137) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 21814557630 := by rw [factor_1_23]; decide
      have factor_1_25 : (13 : ZMod 89580367801) ^ 58320551 = 16995326822 := by
        calc
          (13 : ZMod 89580367801) ^ 58320551 = (13 : ZMod 89580367801) ^ (29160275 + 29160275 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 29160275 * (13 : ZMod 89580367801) ^ 29160275) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 16995326822 := by rw [factor_1_24]; decide
      have factor_1_26 : (13 : ZMod 89580367801) ^ 116641103 = 59104881513 := by
        calc
          (13 : ZMod 89580367801) ^ 116641103 = (13 : ZMod 89580367801) ^ (58320551 + 58320551 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 58320551 * (13 : ZMod 89580367801) ^ 58320551) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 59104881513 := by rw [factor_1_25]; decide
      have factor_1_27 : (13 : ZMod 89580367801) ^ 233282207 = 83650068153 := by
        calc
          (13 : ZMod 89580367801) ^ 233282207 = (13 : ZMod 89580367801) ^ (116641103 + 116641103 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 116641103 * (13 : ZMod 89580367801) ^ 116641103) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 83650068153 := by rw [factor_1_26]; decide
      have factor_1_28 : (13 : ZMod 89580367801) ^ 466564415 = 17431887229 := by
        calc
          (13 : ZMod 89580367801) ^ 466564415 = (13 : ZMod 89580367801) ^ (233282207 + 233282207 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 233282207 * (13 : ZMod 89580367801) ^ 233282207) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 17431887229 := by rw [factor_1_27]; decide
      have factor_1_29 : (13 : ZMod 89580367801) ^ 933128831 = 4352003534 := by
        calc
          (13 : ZMod 89580367801) ^ 933128831 = (13 : ZMod 89580367801) ^ (466564415 + 466564415 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 466564415 * (13 : ZMod 89580367801) ^ 466564415) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 4352003534 := by rw [factor_1_28]; decide
      have factor_1_30 : (13 : ZMod 89580367801) ^ 1866257662 = 56877396830 := by
        calc
          (13 : ZMod 89580367801) ^ 1866257662 = (13 : ZMod 89580367801) ^ (933128831 + 933128831) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 933128831 * (13 : ZMod 89580367801) ^ 933128831 := by rw [pow_add]
          _ = 56877396830 := by rw [factor_1_29]; decide
      have factor_1_31 : (13 : ZMod 89580367801) ^ 3732515325 = 19049282657 := by
        calc
          (13 : ZMod 89580367801) ^ 3732515325 = (13 : ZMod 89580367801) ^ (1866257662 + 1866257662 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1866257662 * (13 : ZMod 89580367801) ^ 1866257662) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 19049282657 := by rw [factor_1_30]; decide
      have factor_1_32 : (13 : ZMod 89580367801) ^ 7465030650 = 45327791183 := by
        calc
          (13 : ZMod 89580367801) ^ 7465030650 = (13 : ZMod 89580367801) ^ (3732515325 + 3732515325) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 3732515325 * (13 : ZMod 89580367801) ^ 3732515325 := by rw [pow_add]
          _ = 45327791183 := by rw [factor_1_31]; decide
      have factor_1_33 : (13 : ZMod 89580367801) ^ 14930061300 = 6611003262 := by
        calc
          (13 : ZMod 89580367801) ^ 14930061300 = (13 : ZMod 89580367801) ^ (7465030650 + 7465030650) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 7465030650 * (13 : ZMod 89580367801) ^ 7465030650 := by rw [pow_add]
          _ = 6611003262 := by rw [factor_1_32]; decide
      have factor_1_34 : (13 : ZMod 89580367801) ^ 29860122600 = 6611003261 := by
        calc
          (13 : ZMod 89580367801) ^ 29860122600 = (13 : ZMod 89580367801) ^ (14930061300 + 14930061300) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 14930061300 * (13 : ZMod 89580367801) ^ 14930061300 := by rw [pow_add]
          _ = 6611003261 := by rw [factor_1_33]; decide
      change (13 : ZMod 89580367801) ^ 29860122600 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (13 : ZMod 89580367801) ^ 1 = 13 := by norm_num
      have factor_2_1 : (13 : ZMod 89580367801) ^ 2 = 169 := by
        calc
          (13 : ZMod 89580367801) ^ 2 = (13 : ZMod 89580367801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1 * (13 : ZMod 89580367801) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_2_0]; decide
      have factor_2_2 : (13 : ZMod 89580367801) ^ 4 = 28561 := by
        calc
          (13 : ZMod 89580367801) ^ 4 = (13 : ZMod 89580367801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 2 * (13 : ZMod 89580367801) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_2_1]; decide
      have factor_2_3 : (13 : ZMod 89580367801) ^ 8 = 815730721 := by
        calc
          (13 : ZMod 89580367801) ^ 8 = (13 : ZMod 89580367801) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 4 * (13 : ZMod 89580367801) ^ 4 := by rw [pow_add]
          _ = 815730721 := by rw [factor_2_2]; decide
      have factor_2_4 : (13 : ZMod 89580367801) ^ 16 = 20941446089 := by
        calc
          (13 : ZMod 89580367801) ^ 16 = (13 : ZMod 89580367801) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 8 * (13 : ZMod 89580367801) ^ 8 := by rw [pow_add]
          _ = 20941446089 := by rw [factor_2_3]; decide
      have factor_2_5 : (13 : ZMod 89580367801) ^ 33 = 24280117062 := by
        calc
          (13 : ZMod 89580367801) ^ 33 = (13 : ZMod 89580367801) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 16 * (13 : ZMod 89580367801) ^ 16) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 24280117062 := by rw [factor_2_4]; decide
      have factor_2_6 : (13 : ZMod 89580367801) ^ 66 = 28163164024 := by
        calc
          (13 : ZMod 89580367801) ^ 66 = (13 : ZMod 89580367801) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 33 * (13 : ZMod 89580367801) ^ 33 := by rw [pow_add]
          _ = 28163164024 := by rw [factor_2_5]; decide
      have factor_2_7 : (13 : ZMod 89580367801) ^ 133 = 74095198817 := by
        calc
          (13 : ZMod 89580367801) ^ 133 = (13 : ZMod 89580367801) ^ (66 + 66 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 66 * (13 : ZMod 89580367801) ^ 66) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 74095198817 := by rw [factor_2_6]; decide
      have factor_2_8 : (13 : ZMod 89580367801) ^ 266 = 46836187145 := by
        calc
          (13 : ZMod 89580367801) ^ 266 = (13 : ZMod 89580367801) ^ (133 + 133) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 133 * (13 : ZMod 89580367801) ^ 133 := by rw [pow_add]
          _ = 46836187145 := by rw [factor_2_7]; decide
      have factor_2_9 : (13 : ZMod 89580367801) ^ 533 = 32549431379 := by
        calc
          (13 : ZMod 89580367801) ^ 533 = (13 : ZMod 89580367801) ^ (266 + 266 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 266 * (13 : ZMod 89580367801) ^ 266) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 32549431379 := by rw [factor_2_8]; decide
      have factor_2_10 : (13 : ZMod 89580367801) ^ 1067 = 55655758117 := by
        calc
          (13 : ZMod 89580367801) ^ 1067 = (13 : ZMod 89580367801) ^ (533 + 533 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 533 * (13 : ZMod 89580367801) ^ 533) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 55655758117 := by rw [factor_2_9]; decide
      have factor_2_11 : (13 : ZMod 89580367801) ^ 2135 = 74023821891 := by
        calc
          (13 : ZMod 89580367801) ^ 2135 = (13 : ZMod 89580367801) ^ (1067 + 1067 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1067 * (13 : ZMod 89580367801) ^ 1067) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 74023821891 := by rw [factor_2_10]; decide
      have factor_2_12 : (13 : ZMod 89580367801) ^ 4271 = 13381016154 := by
        calc
          (13 : ZMod 89580367801) ^ 4271 = (13 : ZMod 89580367801) ^ (2135 + 2135 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 2135 * (13 : ZMod 89580367801) ^ 2135) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 13381016154 := by rw [factor_2_11]; decide
      have factor_2_13 : (13 : ZMod 89580367801) ^ 8543 = 80300505556 := by
        calc
          (13 : ZMod 89580367801) ^ 8543 = (13 : ZMod 89580367801) ^ (4271 + 4271 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 4271 * (13 : ZMod 89580367801) ^ 4271) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 80300505556 := by rw [factor_2_12]; decide
      have factor_2_14 : (13 : ZMod 89580367801) ^ 17086 = 61835930468 := by
        calc
          (13 : ZMod 89580367801) ^ 17086 = (13 : ZMod 89580367801) ^ (8543 + 8543) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 8543 * (13 : ZMod 89580367801) ^ 8543 := by rw [pow_add]
          _ = 61835930468 := by rw [factor_2_13]; decide
      have factor_2_15 : (13 : ZMod 89580367801) ^ 34172 = 32371349043 := by
        calc
          (13 : ZMod 89580367801) ^ 34172 = (13 : ZMod 89580367801) ^ (17086 + 17086) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 17086 * (13 : ZMod 89580367801) ^ 17086 := by rw [pow_add]
          _ = 32371349043 := by rw [factor_2_14]; decide
      have factor_2_16 : (13 : ZMod 89580367801) ^ 68344 = 17844335516 := by
        calc
          (13 : ZMod 89580367801) ^ 68344 = (13 : ZMod 89580367801) ^ (34172 + 34172) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 34172 * (13 : ZMod 89580367801) ^ 34172 := by rw [pow_add]
          _ = 17844335516 := by rw [factor_2_15]; decide
      have factor_2_17 : (13 : ZMod 89580367801) ^ 136688 = 76684773913 := by
        calc
          (13 : ZMod 89580367801) ^ 136688 = (13 : ZMod 89580367801) ^ (68344 + 68344) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 68344 * (13 : ZMod 89580367801) ^ 68344 := by rw [pow_add]
          _ = 76684773913 := by rw [factor_2_16]; decide
      have factor_2_18 : (13 : ZMod 89580367801) ^ 273377 = 2839245 := by
        calc
          (13 : ZMod 89580367801) ^ 273377 = (13 : ZMod 89580367801) ^ (136688 + 136688 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 136688 * (13 : ZMod 89580367801) ^ 136688) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 2839245 := by rw [factor_2_17]; decide
      have factor_2_19 : (13 : ZMod 89580367801) ^ 546755 = 77608250956 := by
        calc
          (13 : ZMod 89580367801) ^ 546755 = (13 : ZMod 89580367801) ^ (273377 + 273377 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 273377 * (13 : ZMod 89580367801) ^ 273377) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 77608250956 := by rw [factor_2_18]; decide
      have factor_2_20 : (13 : ZMod 89580367801) ^ 1093510 = 30323051411 := by
        calc
          (13 : ZMod 89580367801) ^ 1093510 = (13 : ZMod 89580367801) ^ (546755 + 546755) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 546755 * (13 : ZMod 89580367801) ^ 546755 := by rw [pow_add]
          _ = 30323051411 := by rw [factor_2_19]; decide
      have factor_2_21 : (13 : ZMod 89580367801) ^ 2187020 = 79342038415 := by
        calc
          (13 : ZMod 89580367801) ^ 2187020 = (13 : ZMod 89580367801) ^ (1093510 + 1093510) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1093510 * (13 : ZMod 89580367801) ^ 1093510 := by rw [pow_add]
          _ = 79342038415 := by rw [factor_2_20]; decide
      have factor_2_22 : (13 : ZMod 89580367801) ^ 4374041 = 41211515258 := by
        calc
          (13 : ZMod 89580367801) ^ 4374041 = (13 : ZMod 89580367801) ^ (2187020 + 2187020 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 2187020 * (13 : ZMod 89580367801) ^ 2187020) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 41211515258 := by rw [factor_2_21]; decide
      have factor_2_23 : (13 : ZMod 89580367801) ^ 8748082 = 33558818323 := by
        calc
          (13 : ZMod 89580367801) ^ 8748082 = (13 : ZMod 89580367801) ^ (4374041 + 4374041) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 4374041 * (13 : ZMod 89580367801) ^ 4374041 := by rw [pow_add]
          _ = 33558818323 := by rw [factor_2_22]; decide
      have factor_2_24 : (13 : ZMod 89580367801) ^ 17496165 = 47992438930 := by
        calc
          (13 : ZMod 89580367801) ^ 17496165 = (13 : ZMod 89580367801) ^ (8748082 + 8748082 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 8748082 * (13 : ZMod 89580367801) ^ 8748082) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 47992438930 := by rw [factor_2_23]; decide
      have factor_2_25 : (13 : ZMod 89580367801) ^ 34992331 = 49562553920 := by
        calc
          (13 : ZMod 89580367801) ^ 34992331 = (13 : ZMod 89580367801) ^ (17496165 + 17496165 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 17496165 * (13 : ZMod 89580367801) ^ 17496165) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 49562553920 := by rw [factor_2_24]; decide
      have factor_2_26 : (13 : ZMod 89580367801) ^ 69984662 = 84606165501 := by
        calc
          (13 : ZMod 89580367801) ^ 69984662 = (13 : ZMod 89580367801) ^ (34992331 + 34992331) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 34992331 * (13 : ZMod 89580367801) ^ 34992331 := by rw [pow_add]
          _ = 84606165501 := by rw [factor_2_25]; decide
      have factor_2_27 : (13 : ZMod 89580367801) ^ 139969324 = 62583074604 := by
        calc
          (13 : ZMod 89580367801) ^ 139969324 = (13 : ZMod 89580367801) ^ (69984662 + 69984662) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 69984662 * (13 : ZMod 89580367801) ^ 69984662 := by rw [pow_add]
          _ = 62583074604 := by rw [factor_2_26]; decide
      have factor_2_28 : (13 : ZMod 89580367801) ^ 279938649 = 8398055638 := by
        calc
          (13 : ZMod 89580367801) ^ 279938649 = (13 : ZMod 89580367801) ^ (139969324 + 139969324 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 139969324 * (13 : ZMod 89580367801) ^ 139969324) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 8398055638 := by rw [factor_2_27]; decide
      have factor_2_29 : (13 : ZMod 89580367801) ^ 559877298 = 77881235064 := by
        calc
          (13 : ZMod 89580367801) ^ 559877298 = (13 : ZMod 89580367801) ^ (279938649 + 279938649) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 279938649 * (13 : ZMod 89580367801) ^ 279938649 := by rw [pow_add]
          _ = 77881235064 := by rw [factor_2_28]; decide
      have factor_2_30 : (13 : ZMod 89580367801) ^ 1119754597 = 39165191903 := by
        calc
          (13 : ZMod 89580367801) ^ 1119754597 = (13 : ZMod 89580367801) ^ (559877298 + 559877298 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 559877298 * (13 : ZMod 89580367801) ^ 559877298) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 39165191903 := by rw [factor_2_29]; decide
      have factor_2_31 : (13 : ZMod 89580367801) ^ 2239509195 = 73439388227 := by
        calc
          (13 : ZMod 89580367801) ^ 2239509195 = (13 : ZMod 89580367801) ^ (1119754597 + 1119754597 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1119754597 * (13 : ZMod 89580367801) ^ 1119754597) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 73439388227 := by rw [factor_2_30]; decide
      have factor_2_32 : (13 : ZMod 89580367801) ^ 4479018390 = 88254760303 := by
        calc
          (13 : ZMod 89580367801) ^ 4479018390 = (13 : ZMod 89580367801) ^ (2239509195 + 2239509195) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 2239509195 * (13 : ZMod 89580367801) ^ 2239509195 := by rw [pow_add]
          _ = 88254760303 := by rw [factor_2_31]; decide
      have factor_2_33 : (13 : ZMod 89580367801) ^ 8958036780 = 49019799306 := by
        calc
          (13 : ZMod 89580367801) ^ 8958036780 = (13 : ZMod 89580367801) ^ (4479018390 + 4479018390) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 4479018390 * (13 : ZMod 89580367801) ^ 4479018390 := by rw [pow_add]
          _ = 49019799306 := by rw [factor_2_32]; decide
      have factor_2_34 : (13 : ZMod 89580367801) ^ 17916073560 = 152810490 := by
        calc
          (13 : ZMod 89580367801) ^ 17916073560 = (13 : ZMod 89580367801) ^ (8958036780 + 8958036780) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 8958036780 * (13 : ZMod 89580367801) ^ 8958036780 := by rw [pow_add]
          _ = 152810490 := by rw [factor_2_33]; decide
      change (13 : ZMod 89580367801) ^ 17916073560 ≠ 1
      rw [factor_2_34]
      decide
    ·
      have factor_3_0 : (13 : ZMod 89580367801) ^ 1 = 13 := by norm_num
      have factor_3_1 : (13 : ZMod 89580367801) ^ 2 = 169 := by
        calc
          (13 : ZMod 89580367801) ^ 2 = (13 : ZMod 89580367801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1 * (13 : ZMod 89580367801) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_3_0]; decide
      have factor_3_2 : (13 : ZMod 89580367801) ^ 5 = 371293 := by
        calc
          (13 : ZMod 89580367801) ^ 5 = (13 : ZMod 89580367801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 2 * (13 : ZMod 89580367801) ^ 2) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 371293 := by rw [factor_3_1]; decide
      have factor_3_3 : (13 : ZMod 89580367801) ^ 11 = 553038017 := by
        calc
          (13 : ZMod 89580367801) ^ 11 = (13 : ZMod 89580367801) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 5 * (13 : ZMod 89580367801) ^ 5) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 553038017 := by rw [factor_3_2]; decide
      have factor_3_4 : (13 : ZMod 89580367801) ^ 23 = 34907421322 := by
        calc
          (13 : ZMod 89580367801) ^ 23 = (13 : ZMod 89580367801) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 11 * (13 : ZMod 89580367801) ^ 11) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 34907421322 := by rw [factor_3_3]; decide
      have factor_3_5 : (13 : ZMod 89580367801) ^ 47 = 32188724348 := by
        calc
          (13 : ZMod 89580367801) ^ 47 = (13 : ZMod 89580367801) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 23 * (13 : ZMod 89580367801) ^ 23) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 32188724348 := by rw [factor_3_4]; decide
      have factor_3_6 : (13 : ZMod 89580367801) ^ 95 = 54635714261 := by
        calc
          (13 : ZMod 89580367801) ^ 95 = (13 : ZMod 89580367801) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 47 * (13 : ZMod 89580367801) ^ 47) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 54635714261 := by rw [factor_3_5]; decide
      have factor_3_7 : (13 : ZMod 89580367801) ^ 190 = 51089440811 := by
        calc
          (13 : ZMod 89580367801) ^ 190 = (13 : ZMod 89580367801) ^ (95 + 95) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 95 * (13 : ZMod 89580367801) ^ 95 := by rw [pow_add]
          _ = 51089440811 := by rw [factor_3_6]; decide
      have factor_3_8 : (13 : ZMod 89580367801) ^ 381 = 1075418073 := by
        calc
          (13 : ZMod 89580367801) ^ 381 = (13 : ZMod 89580367801) ^ (190 + 190 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 190 * (13 : ZMod 89580367801) ^ 190) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 1075418073 := by rw [factor_3_7]; decide
      have factor_3_9 : (13 : ZMod 89580367801) ^ 762 = 7713831466 := by
        calc
          (13 : ZMod 89580367801) ^ 762 = (13 : ZMod 89580367801) ^ (381 + 381) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 381 * (13 : ZMod 89580367801) ^ 381 := by rw [pow_add]
          _ = 7713831466 := by rw [factor_3_8]; decide
      have factor_3_10 : (13 : ZMod 89580367801) ^ 1525 = 1260217793 := by
        calc
          (13 : ZMod 89580367801) ^ 1525 = (13 : ZMod 89580367801) ^ (762 + 762 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 762 * (13 : ZMod 89580367801) ^ 762) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 1260217793 := by rw [factor_3_9]; decide
      have factor_3_11 : (13 : ZMod 89580367801) ^ 3051 = 38913536351 := by
        calc
          (13 : ZMod 89580367801) ^ 3051 = (13 : ZMod 89580367801) ^ (1525 + 1525 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1525 * (13 : ZMod 89580367801) ^ 1525) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 38913536351 := by rw [factor_3_10]; decide
      have factor_3_12 : (13 : ZMod 89580367801) ^ 6102 = 699644813 := by
        calc
          (13 : ZMod 89580367801) ^ 6102 = (13 : ZMod 89580367801) ^ (3051 + 3051) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 3051 * (13 : ZMod 89580367801) ^ 3051 := by rw [pow_add]
          _ = 699644813 := by rw [factor_3_11]; decide
      have factor_3_13 : (13 : ZMod 89580367801) ^ 12204 = 81706756171 := by
        calc
          (13 : ZMod 89580367801) ^ 12204 = (13 : ZMod 89580367801) ^ (6102 + 6102) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 6102 * (13 : ZMod 89580367801) ^ 6102 := by rw [pow_add]
          _ = 81706756171 := by rw [factor_3_12]; decide
      have factor_3_14 : (13 : ZMod 89580367801) ^ 24408 = 71098530023 := by
        calc
          (13 : ZMod 89580367801) ^ 24408 = (13 : ZMod 89580367801) ^ (12204 + 12204) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 12204 * (13 : ZMod 89580367801) ^ 12204 := by rw [pow_add]
          _ = 71098530023 := by rw [factor_3_13]; decide
      have factor_3_15 : (13 : ZMod 89580367801) ^ 48817 = 21327598419 := by
        calc
          (13 : ZMod 89580367801) ^ 48817 = (13 : ZMod 89580367801) ^ (24408 + 24408 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 24408 * (13 : ZMod 89580367801) ^ 24408) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 21327598419 := by rw [factor_3_14]; decide
      have factor_3_16 : (13 : ZMod 89580367801) ^ 97634 = 70384287645 := by
        calc
          (13 : ZMod 89580367801) ^ 97634 = (13 : ZMod 89580367801) ^ (48817 + 48817) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 48817 * (13 : ZMod 89580367801) ^ 48817 := by rw [pow_add]
          _ = 70384287645 := by rw [factor_3_15]; decide
      have factor_3_17 : (13 : ZMod 89580367801) ^ 195269 = 57949663381 := by
        calc
          (13 : ZMod 89580367801) ^ 195269 = (13 : ZMod 89580367801) ^ (97634 + 97634 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 97634 * (13 : ZMod 89580367801) ^ 97634) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 57949663381 := by rw [factor_3_16]; decide
      have factor_3_18 : (13 : ZMod 89580367801) ^ 390539 = 31851314574 := by
        calc
          (13 : ZMod 89580367801) ^ 390539 = (13 : ZMod 89580367801) ^ (195269 + 195269 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 195269 * (13 : ZMod 89580367801) ^ 195269) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 31851314574 := by rw [factor_3_17]; decide
      have factor_3_19 : (13 : ZMod 89580367801) ^ 781078 = 23193521955 := by
        calc
          (13 : ZMod 89580367801) ^ 781078 = (13 : ZMod 89580367801) ^ (390539 + 390539) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 390539 * (13 : ZMod 89580367801) ^ 390539 := by rw [pow_add]
          _ = 23193521955 := by rw [factor_3_18]; decide
      have factor_3_20 : (13 : ZMod 89580367801) ^ 1562157 = 1975228548 := by
        calc
          (13 : ZMod 89580367801) ^ 1562157 = (13 : ZMod 89580367801) ^ (781078 + 781078 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 781078 * (13 : ZMod 89580367801) ^ 781078) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 1975228548 := by rw [factor_3_19]; decide
      have factor_3_21 : (13 : ZMod 89580367801) ^ 3124315 = 47786386410 := by
        calc
          (13 : ZMod 89580367801) ^ 3124315 = (13 : ZMod 89580367801) ^ (1562157 + 1562157 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1562157 * (13 : ZMod 89580367801) ^ 1562157) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 47786386410 := by rw [factor_3_20]; decide
      have factor_3_22 : (13 : ZMod 89580367801) ^ 6248630 = 81637641390 := by
        calc
          (13 : ZMod 89580367801) ^ 6248630 = (13 : ZMod 89580367801) ^ (3124315 + 3124315) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 3124315 * (13 : ZMod 89580367801) ^ 3124315 := by rw [pow_add]
          _ = 81637641390 := by rw [factor_3_21]; decide
      have factor_3_23 : (13 : ZMod 89580367801) ^ 12497261 = 64634734104 := by
        calc
          (13 : ZMod 89580367801) ^ 12497261 = (13 : ZMod 89580367801) ^ (6248630 + 6248630 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 6248630 * (13 : ZMod 89580367801) ^ 6248630) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 64634734104 := by rw [factor_3_22]; decide
      have factor_3_24 : (13 : ZMod 89580367801) ^ 24994522 = 40766447853 := by
        calc
          (13 : ZMod 89580367801) ^ 24994522 = (13 : ZMod 89580367801) ^ (12497261 + 12497261) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 12497261 * (13 : ZMod 89580367801) ^ 12497261 := by rw [pow_add]
          _ = 40766447853 := by rw [factor_3_23]; decide
      have factor_3_25 : (13 : ZMod 89580367801) ^ 49989044 = 27391039099 := by
        calc
          (13 : ZMod 89580367801) ^ 49989044 = (13 : ZMod 89580367801) ^ (24994522 + 24994522) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 24994522 * (13 : ZMod 89580367801) ^ 24994522 := by rw [pow_add]
          _ = 27391039099 := by rw [factor_3_24]; decide
      have factor_3_26 : (13 : ZMod 89580367801) ^ 99978089 = 73491872989 := by
        calc
          (13 : ZMod 89580367801) ^ 99978089 = (13 : ZMod 89580367801) ^ (49989044 + 49989044 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 49989044 * (13 : ZMod 89580367801) ^ 49989044) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 73491872989 := by rw [factor_3_25]; decide
      have factor_3_27 : (13 : ZMod 89580367801) ^ 199956178 = 3488298684 := by
        calc
          (13 : ZMod 89580367801) ^ 199956178 = (13 : ZMod 89580367801) ^ (99978089 + 99978089) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 99978089 * (13 : ZMod 89580367801) ^ 99978089 := by rw [pow_add]
          _ = 3488298684 := by rw [factor_3_26]; decide
      have factor_3_28 : (13 : ZMod 89580367801) ^ 399912356 = 65725470981 := by
        calc
          (13 : ZMod 89580367801) ^ 399912356 = (13 : ZMod 89580367801) ^ (199956178 + 199956178) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 199956178 * (13 : ZMod 89580367801) ^ 199956178 := by rw [pow_add]
          _ = 65725470981 := by rw [factor_3_27]; decide
      have factor_3_29 : (13 : ZMod 89580367801) ^ 799824712 = 60747466746 := by
        calc
          (13 : ZMod 89580367801) ^ 799824712 = (13 : ZMod 89580367801) ^ (399912356 + 399912356) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 399912356 * (13 : ZMod 89580367801) ^ 399912356 := by rw [pow_add]
          _ = 60747466746 := by rw [factor_3_28]; decide
      have factor_3_30 : (13 : ZMod 89580367801) ^ 1599649425 = 13499248990 := by
        calc
          (13 : ZMod 89580367801) ^ 1599649425 = (13 : ZMod 89580367801) ^ (799824712 + 799824712 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 799824712 * (13 : ZMod 89580367801) ^ 799824712) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 13499248990 := by rw [factor_3_29]; decide
      have factor_3_31 : (13 : ZMod 89580367801) ^ 3199298850 = 33720512699 := by
        calc
          (13 : ZMod 89580367801) ^ 3199298850 = (13 : ZMod 89580367801) ^ (1599649425 + 1599649425) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1599649425 * (13 : ZMod 89580367801) ^ 1599649425 := by rw [pow_add]
          _ = 33720512699 := by rw [factor_3_30]; decide
      have factor_3_32 : (13 : ZMod 89580367801) ^ 6398597700 = 67967016960 := by
        calc
          (13 : ZMod 89580367801) ^ 6398597700 = (13 : ZMod 89580367801) ^ (3199298850 + 3199298850) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 3199298850 * (13 : ZMod 89580367801) ^ 3199298850 := by rw [pow_add]
          _ = 67967016960 := by rw [factor_3_31]; decide
      have factor_3_33 : (13 : ZMod 89580367801) ^ 12797195400 = 5966501627 := by
        calc
          (13 : ZMod 89580367801) ^ 12797195400 = (13 : ZMod 89580367801) ^ (6398597700 + 6398597700) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 6398597700 * (13 : ZMod 89580367801) ^ 6398597700 := by rw [pow_add]
          _ = 5966501627 := by rw [factor_3_32]; decide
      change (13 : ZMod 89580367801) ^ 12797195400 ≠ 1
      rw [factor_3_33]
      decide
    ·
      have factor_4_0 : (13 : ZMod 89580367801) ^ 1 = 13 := by norm_num
      have factor_4_1 : (13 : ZMod 89580367801) ^ 3 = 2197 := by
        calc
          (13 : ZMod 89580367801) ^ 3 = (13 : ZMod 89580367801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1 * (13 : ZMod 89580367801) ^ 1) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_4_0]; decide
      have factor_4_2 : (13 : ZMod 89580367801) ^ 7 = 62748517 := by
        calc
          (13 : ZMod 89580367801) ^ 7 = (13 : ZMod 89580367801) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 3 * (13 : ZMod 89580367801) ^ 3) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 62748517 := by rw [factor_4_1]; decide
      have factor_4_3 : (13 : ZMod 89580367801) ^ 15 = 29174070561 := by
        calc
          (13 : ZMod 89580367801) ^ 15 = (13 : ZMod 89580367801) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 7 * (13 : ZMod 89580367801) ^ 7) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 29174070561 := by rw [factor_4_2]; decide
      have factor_4_4 : (13 : ZMod 89580367801) ^ 30 = 44943944212 := by
        calc
          (13 : ZMod 89580367801) ^ 30 = (13 : ZMod 89580367801) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 15 * (13 : ZMod 89580367801) ^ 15 := by rw [pow_add]
          _ = 44943944212 := by rw [factor_4_3]; decide
      have factor_4_5 : (13 : ZMod 89580367801) ^ 60 = 70747077361 := by
        calc
          (13 : ZMod 89580367801) ^ 60 = (13 : ZMod 89580367801) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 30 * (13 : ZMod 89580367801) ^ 30 := by rw [pow_add]
          _ = 70747077361 := by rw [factor_4_4]; decide
      have factor_4_6 : (13 : ZMod 89580367801) ^ 121 = 68254461917 := by
        calc
          (13 : ZMod 89580367801) ^ 121 = (13 : ZMod 89580367801) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 60 * (13 : ZMod 89580367801) ^ 60) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 68254461917 := by rw [factor_4_5]; decide
      have factor_4_7 : (13 : ZMod 89580367801) ^ 242 = 71148532037 := by
        calc
          (13 : ZMod 89580367801) ^ 242 = (13 : ZMod 89580367801) ^ (121 + 121) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 121 * (13 : ZMod 89580367801) ^ 121 := by rw [pow_add]
          _ = 71148532037 := by rw [factor_4_6]; decide
      have factor_4_8 : (13 : ZMod 89580367801) ^ 485 = 4555403578 := by
        calc
          (13 : ZMod 89580367801) ^ 485 = (13 : ZMod 89580367801) ^ (242 + 242 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 242 * (13 : ZMod 89580367801) ^ 242) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 4555403578 := by rw [factor_4_7]; decide
      have factor_4_9 : (13 : ZMod 89580367801) ^ 970 = 85492333713 := by
        calc
          (13 : ZMod 89580367801) ^ 970 = (13 : ZMod 89580367801) ^ (485 + 485) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 485 * (13 : ZMod 89580367801) ^ 485 := by rw [pow_add]
          _ = 85492333713 := by rw [factor_4_8]; decide
      have factor_4_10 : (13 : ZMod 89580367801) ^ 1941 = 65582712837 := by
        calc
          (13 : ZMod 89580367801) ^ 1941 = (13 : ZMod 89580367801) ^ (970 + 970 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 970 * (13 : ZMod 89580367801) ^ 970) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 65582712837 := by rw [factor_4_9]; decide
      have factor_4_11 : (13 : ZMod 89580367801) ^ 3883 = 17601164263 := by
        calc
          (13 : ZMod 89580367801) ^ 3883 = (13 : ZMod 89580367801) ^ (1941 + 1941 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1941 * (13 : ZMod 89580367801) ^ 1941) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 17601164263 := by rw [factor_4_10]; decide
      have factor_4_12 : (13 : ZMod 89580367801) ^ 7766 = 83550586950 := by
        calc
          (13 : ZMod 89580367801) ^ 7766 = (13 : ZMod 89580367801) ^ (3883 + 3883) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 3883 * (13 : ZMod 89580367801) ^ 3883 := by rw [pow_add]
          _ = 83550586950 := by rw [factor_4_11]; decide
      have factor_4_13 : (13 : ZMod 89580367801) ^ 15532 = 11572621151 := by
        calc
          (13 : ZMod 89580367801) ^ 15532 = (13 : ZMod 89580367801) ^ (7766 + 7766) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 7766 * (13 : ZMod 89580367801) ^ 7766 := by rw [pow_add]
          _ = 11572621151 := by rw [factor_4_12]; decide
      have factor_4_14 : (13 : ZMod 89580367801) ^ 31065 = 45381705247 := by
        calc
          (13 : ZMod 89580367801) ^ 31065 = (13 : ZMod 89580367801) ^ (15532 + 15532 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 15532 * (13 : ZMod 89580367801) ^ 15532) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 45381705247 := by rw [factor_4_13]; decide
      have factor_4_15 : (13 : ZMod 89580367801) ^ 62131 = 37015409155 := by
        calc
          (13 : ZMod 89580367801) ^ 62131 = (13 : ZMod 89580367801) ^ (31065 + 31065 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 31065 * (13 : ZMod 89580367801) ^ 31065) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 37015409155 := by rw [factor_4_14]; decide
      have factor_4_16 : (13 : ZMod 89580367801) ^ 124262 = 38815283308 := by
        calc
          (13 : ZMod 89580367801) ^ 124262 = (13 : ZMod 89580367801) ^ (62131 + 62131) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 62131 * (13 : ZMod 89580367801) ^ 62131 := by rw [pow_add]
          _ = 38815283308 := by rw [factor_4_15]; decide
      have factor_4_17 : (13 : ZMod 89580367801) ^ 248525 = 39152258005 := by
        calc
          (13 : ZMod 89580367801) ^ 248525 = (13 : ZMod 89580367801) ^ (124262 + 124262 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 124262 * (13 : ZMod 89580367801) ^ 124262) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 39152258005 := by rw [factor_4_16]; decide
      have factor_4_18 : (13 : ZMod 89580367801) ^ 497050 = 47796841833 := by
        calc
          (13 : ZMod 89580367801) ^ 497050 = (13 : ZMod 89580367801) ^ (248525 + 248525) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 248525 * (13 : ZMod 89580367801) ^ 248525 := by rw [pow_add]
          _ = 47796841833 := by rw [factor_4_17]; decide
      have factor_4_19 : (13 : ZMod 89580367801) ^ 994100 = 12837039328 := by
        calc
          (13 : ZMod 89580367801) ^ 994100 = (13 : ZMod 89580367801) ^ (497050 + 497050) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 497050 * (13 : ZMod 89580367801) ^ 497050 := by rw [pow_add]
          _ = 12837039328 := by rw [factor_4_18]; decide
      have factor_4_20 : (13 : ZMod 89580367801) ^ 1988200 = 70263917512 := by
        calc
          (13 : ZMod 89580367801) ^ 1988200 = (13 : ZMod 89580367801) ^ (994100 + 994100) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 994100 * (13 : ZMod 89580367801) ^ 994100 := by rw [pow_add]
          _ = 70263917512 := by rw [factor_4_19]; decide
      have factor_4_21 : (13 : ZMod 89580367801) ^ 3976401 = 33439986904 := by
        calc
          (13 : ZMod 89580367801) ^ 3976401 = (13 : ZMod 89580367801) ^ (1988200 + 1988200 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1988200 * (13 : ZMod 89580367801) ^ 1988200) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 33439986904 := by rw [factor_4_20]; decide
      have factor_4_22 : (13 : ZMod 89580367801) ^ 7952802 = 60592166733 := by
        calc
          (13 : ZMod 89580367801) ^ 7952802 = (13 : ZMod 89580367801) ^ (3976401 + 3976401) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 3976401 * (13 : ZMod 89580367801) ^ 3976401 := by rw [pow_add]
          _ = 60592166733 := by rw [factor_4_21]; decide
      have factor_4_23 : (13 : ZMod 89580367801) ^ 15905605 = 26522715300 := by
        calc
          (13 : ZMod 89580367801) ^ 15905605 = (13 : ZMod 89580367801) ^ (7952802 + 7952802 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 7952802 * (13 : ZMod 89580367801) ^ 7952802) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 26522715300 := by rw [factor_4_22]; decide
      have factor_4_24 : (13 : ZMod 89580367801) ^ 31811210 = 81084996913 := by
        calc
          (13 : ZMod 89580367801) ^ 31811210 = (13 : ZMod 89580367801) ^ (15905605 + 15905605) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 15905605 * (13 : ZMod 89580367801) ^ 15905605 := by rw [pow_add]
          _ = 81084996913 := by rw [factor_4_23]; decide
      have factor_4_25 : (13 : ZMod 89580367801) ^ 63622420 = 56534088862 := by
        calc
          (13 : ZMod 89580367801) ^ 63622420 = (13 : ZMod 89580367801) ^ (31811210 + 31811210) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 31811210 * (13 : ZMod 89580367801) ^ 31811210 := by rw [pow_add]
          _ = 56534088862 := by rw [factor_4_24]; decide
      have factor_4_26 : (13 : ZMod 89580367801) ^ 127244840 = 40847050645 := by
        calc
          (13 : ZMod 89580367801) ^ 127244840 = (13 : ZMod 89580367801) ^ (63622420 + 63622420) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 63622420 * (13 : ZMod 89580367801) ^ 63622420 := by rw [pow_add]
          _ = 40847050645 := by rw [factor_4_25]; decide
      have factor_4_27 : (13 : ZMod 89580367801) ^ 254489681 = 33865056976 := by
        calc
          (13 : ZMod 89580367801) ^ 254489681 = (13 : ZMod 89580367801) ^ (127244840 + 127244840 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 127244840 * (13 : ZMod 89580367801) ^ 127244840) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 33865056976 := by rw [factor_4_26]; decide
      have factor_4_28 : (13 : ZMod 89580367801) ^ 508979362 = 88262304825 := by
        calc
          (13 : ZMod 89580367801) ^ 508979362 = (13 : ZMod 89580367801) ^ (254489681 + 254489681) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 254489681 * (13 : ZMod 89580367801) ^ 254489681 := by rw [pow_add]
          _ = 88262304825 := by rw [factor_4_27]; decide
      have factor_4_29 : (13 : ZMod 89580367801) ^ 1017958725 = 65031283481 := by
        calc
          (13 : ZMod 89580367801) ^ 1017958725 = (13 : ZMod 89580367801) ^ (508979362 + 508979362 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 508979362 * (13 : ZMod 89580367801) ^ 508979362) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 65031283481 := by rw [factor_4_28]; decide
      have factor_4_30 : (13 : ZMod 89580367801) ^ 2035917450 = 59341975302 := by
        calc
          (13 : ZMod 89580367801) ^ 2035917450 = (13 : ZMod 89580367801) ^ (1017958725 + 1017958725) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1017958725 * (13 : ZMod 89580367801) ^ 1017958725 := by rw [pow_add]
          _ = 59341975302 := by rw [factor_4_29]; decide
      have factor_4_31 : (13 : ZMod 89580367801) ^ 4071834900 = 11229739153 := by
        calc
          (13 : ZMod 89580367801) ^ 4071834900 = (13 : ZMod 89580367801) ^ (2035917450 + 2035917450) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 2035917450 * (13 : ZMod 89580367801) ^ 2035917450 := by rw [pow_add]
          _ = 11229739153 := by rw [factor_4_30]; decide
      have factor_4_32 : (13 : ZMod 89580367801) ^ 8143669800 = 77619546299 := by
        calc
          (13 : ZMod 89580367801) ^ 8143669800 = (13 : ZMod 89580367801) ^ (4071834900 + 4071834900) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 4071834900 * (13 : ZMod 89580367801) ^ 4071834900 := by rw [pow_add]
          _ = 77619546299 := by rw [factor_4_31]; decide
      change (13 : ZMod 89580367801) ^ 8143669800 ≠ 1
      rw [factor_4_32]
      decide
    ·
      have factor_5_0 : (13 : ZMod 89580367801) ^ 1 = 13 := by norm_num
      have factor_5_1 : (13 : ZMod 89580367801) ^ 2 = 169 := by
        calc
          (13 : ZMod 89580367801) ^ 2 = (13 : ZMod 89580367801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1 * (13 : ZMod 89580367801) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_5_0]; decide
      have factor_5_2 : (13 : ZMod 89580367801) ^ 4 = 28561 := by
        calc
          (13 : ZMod 89580367801) ^ 4 = (13 : ZMod 89580367801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 2 * (13 : ZMod 89580367801) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_5_1]; decide
      have factor_5_3 : (13 : ZMod 89580367801) ^ 9 = 10604499373 := by
        calc
          (13 : ZMod 89580367801) ^ 9 = (13 : ZMod 89580367801) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 4 * (13 : ZMod 89580367801) ^ 4) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 10604499373 := by rw [factor_5_2]; decide
      have factor_5_4 : (13 : ZMod 89580367801) ^ 19 = 53628375620 := by
        calc
          (13 : ZMod 89580367801) ^ 19 = (13 : ZMod 89580367801) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 9 * (13 : ZMod 89580367801) ^ 9) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 53628375620 := by rw [factor_5_3]; decide
      have factor_5_5 : (13 : ZMod 89580367801) ^ 39 = 612165286 := by
        calc
          (13 : ZMod 89580367801) ^ 39 = (13 : ZMod 89580367801) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 19 * (13 : ZMod 89580367801) ^ 19) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 612165286 := by rw [factor_5_4]; decide
      have factor_5_6 : (13 : ZMod 89580367801) ^ 78 = 37002045043 := by
        calc
          (13 : ZMod 89580367801) ^ 78 = (13 : ZMod 89580367801) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 39 * (13 : ZMod 89580367801) ^ 39 := by rw [pow_add]
          _ = 37002045043 := by rw [factor_5_5]; decide
      have factor_5_7 : (13 : ZMod 89580367801) ^ 157 = 45440298828 := by
        calc
          (13 : ZMod 89580367801) ^ 157 = (13 : ZMod 89580367801) ^ (78 + 78 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 78 * (13 : ZMod 89580367801) ^ 78) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 45440298828 := by rw [factor_5_6]; decide
      have factor_5_8 : (13 : ZMod 89580367801) ^ 314 = 84080604604 := by
        calc
          (13 : ZMod 89580367801) ^ 314 = (13 : ZMod 89580367801) ^ (157 + 157) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 157 * (13 : ZMod 89580367801) ^ 157 := by rw [pow_add]
          _ = 84080604604 := by rw [factor_5_7]; decide
      have factor_5_9 : (13 : ZMod 89580367801) ^ 628 = 60650316090 := by
        calc
          (13 : ZMod 89580367801) ^ 628 = (13 : ZMod 89580367801) ^ (314 + 314) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 314 * (13 : ZMod 89580367801) ^ 314 := by rw [pow_add]
          _ = 60650316090 := by rw [factor_5_8]; decide
      have factor_5_10 : (13 : ZMod 89580367801) ^ 1256 = 72665857892 := by
        calc
          (13 : ZMod 89580367801) ^ 1256 = (13 : ZMod 89580367801) ^ (628 + 628) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 628 * (13 : ZMod 89580367801) ^ 628 := by rw [pow_add]
          _ = 72665857892 := by rw [factor_5_9]; decide
      have factor_5_11 : (13 : ZMod 89580367801) ^ 2512 = 60058438732 := by
        calc
          (13 : ZMod 89580367801) ^ 2512 = (13 : ZMod 89580367801) ^ (1256 + 1256) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1256 * (13 : ZMod 89580367801) ^ 1256 := by rw [pow_add]
          _ = 60058438732 := by rw [factor_5_10]; decide
      have factor_5_12 : (13 : ZMod 89580367801) ^ 5025 = 70875075693 := by
        calc
          (13 : ZMod 89580367801) ^ 5025 = (13 : ZMod 89580367801) ^ (2512 + 2512 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 2512 * (13 : ZMod 89580367801) ^ 2512) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 70875075693 := by rw [factor_5_11]; decide
      have factor_5_13 : (13 : ZMod 89580367801) ^ 10050 = 16988140981 := by
        calc
          (13 : ZMod 89580367801) ^ 10050 = (13 : ZMod 89580367801) ^ (5025 + 5025) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 5025 * (13 : ZMod 89580367801) ^ 5025 := by rw [pow_add]
          _ = 16988140981 := by rw [factor_5_12]; decide
      have factor_5_14 : (13 : ZMod 89580367801) ^ 20101 = 65662259053 := by
        calc
          (13 : ZMod 89580367801) ^ 20101 = (13 : ZMod 89580367801) ^ (10050 + 10050 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 10050 * (13 : ZMod 89580367801) ^ 10050) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 65662259053 := by rw [factor_5_13]; decide
      have factor_5_15 : (13 : ZMod 89580367801) ^ 40202 = 46537990473 := by
        calc
          (13 : ZMod 89580367801) ^ 40202 = (13 : ZMod 89580367801) ^ (20101 + 20101) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 20101 * (13 : ZMod 89580367801) ^ 20101 := by rw [pow_add]
          _ = 46537990473 := by rw [factor_5_14]; decide
      have factor_5_16 : (13 : ZMod 89580367801) ^ 80405 = 83859582961 := by
        calc
          (13 : ZMod 89580367801) ^ 80405 = (13 : ZMod 89580367801) ^ (40202 + 40202 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 40202 * (13 : ZMod 89580367801) ^ 40202) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 83859582961 := by rw [factor_5_15]; decide
      have factor_5_17 : (13 : ZMod 89580367801) ^ 160810 = 3556776222 := by
        calc
          (13 : ZMod 89580367801) ^ 160810 = (13 : ZMod 89580367801) ^ (80405 + 80405) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 80405 * (13 : ZMod 89580367801) ^ 80405 := by rw [pow_add]
          _ = 3556776222 := by rw [factor_5_16]; decide
      have factor_5_18 : (13 : ZMod 89580367801) ^ 321620 = 23084818372 := by
        calc
          (13 : ZMod 89580367801) ^ 321620 = (13 : ZMod 89580367801) ^ (160810 + 160810) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 160810 * (13 : ZMod 89580367801) ^ 160810 := by rw [pow_add]
          _ = 23084818372 := by rw [factor_5_17]; decide
      have factor_5_19 : (13 : ZMod 89580367801) ^ 643241 = 44153544843 := by
        calc
          (13 : ZMod 89580367801) ^ 643241 = (13 : ZMod 89580367801) ^ (321620 + 321620 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 321620 * (13 : ZMod 89580367801) ^ 321620) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 44153544843 := by rw [factor_5_18]; decide
      have factor_5_20 : (13 : ZMod 89580367801) ^ 1286482 = 26452002224 := by
        calc
          (13 : ZMod 89580367801) ^ 1286482 = (13 : ZMod 89580367801) ^ (643241 + 643241) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 643241 * (13 : ZMod 89580367801) ^ 643241 := by rw [pow_add]
          _ = 26452002224 := by rw [factor_5_19]; decide
      have factor_5_21 : (13 : ZMod 89580367801) ^ 2572965 = 1004081681 := by
        calc
          (13 : ZMod 89580367801) ^ 2572965 = (13 : ZMod 89580367801) ^ (1286482 + 1286482 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1286482 * (13 : ZMod 89580367801) ^ 1286482) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 1004081681 := by rw [factor_5_20]; decide
      have factor_5_22 : (13 : ZMod 89580367801) ^ 5145931 = 69183773917 := by
        calc
          (13 : ZMod 89580367801) ^ 5145931 = (13 : ZMod 89580367801) ^ (2572965 + 2572965 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 2572965 * (13 : ZMod 89580367801) ^ 2572965) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 69183773917 := by rw [factor_5_21]; decide
      have factor_5_23 : (13 : ZMod 89580367801) ^ 10291862 = 23787766901 := by
        calc
          (13 : ZMod 89580367801) ^ 10291862 = (13 : ZMod 89580367801) ^ (5145931 + 5145931) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 5145931 * (13 : ZMod 89580367801) ^ 5145931 := by rw [pow_add]
          _ = 23787766901 := by rw [factor_5_22]; decide
      have factor_5_24 : (13 : ZMod 89580367801) ^ 20583724 = 2128297503 := by
        calc
          (13 : ZMod 89580367801) ^ 20583724 = (13 : ZMod 89580367801) ^ (10291862 + 10291862) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 10291862 * (13 : ZMod 89580367801) ^ 10291862 := by rw [pow_add]
          _ = 2128297503 := by rw [factor_5_23]; decide
      have factor_5_25 : (13 : ZMod 89580367801) ^ 41167448 = 61960863998 := by
        calc
          (13 : ZMod 89580367801) ^ 41167448 = (13 : ZMod 89580367801) ^ (20583724 + 20583724) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 20583724 * (13 : ZMod 89580367801) ^ 20583724 := by rw [pow_add]
          _ = 61960863998 := by rw [factor_5_24]; decide
      have factor_5_26 : (13 : ZMod 89580367801) ^ 82334896 = 85776758851 := by
        calc
          (13 : ZMod 89580367801) ^ 82334896 = (13 : ZMod 89580367801) ^ (41167448 + 41167448) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 41167448 * (13 : ZMod 89580367801) ^ 41167448 := by rw [pow_add]
          _ = 85776758851 := by rw [factor_5_25]; decide
      have factor_5_27 : (13 : ZMod 89580367801) ^ 164669793 = 9145192586 := by
        calc
          (13 : ZMod 89580367801) ^ 164669793 = (13 : ZMod 89580367801) ^ (82334896 + 82334896 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 82334896 * (13 : ZMod 89580367801) ^ 82334896) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 9145192586 := by rw [factor_5_26]; decide
      have factor_5_28 : (13 : ZMod 89580367801) ^ 329339587 = 49944117640 := by
        calc
          (13 : ZMod 89580367801) ^ 329339587 = (13 : ZMod 89580367801) ^ (164669793 + 164669793 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 164669793 * (13 : ZMod 89580367801) ^ 164669793) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 49944117640 := by rw [factor_5_27]; decide
      have factor_5_29 : (13 : ZMod 89580367801) ^ 658679175 = 81844119516 := by
        calc
          (13 : ZMod 89580367801) ^ 658679175 = (13 : ZMod 89580367801) ^ (329339587 + 329339587 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 329339587 * (13 : ZMod 89580367801) ^ 329339587) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 81844119516 := by rw [factor_5_28]; decide
      have factor_5_30 : (13 : ZMod 89580367801) ^ 1317358350 = 55987790648 := by
        calc
          (13 : ZMod 89580367801) ^ 1317358350 = (13 : ZMod 89580367801) ^ (658679175 + 658679175) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 658679175 * (13 : ZMod 89580367801) ^ 658679175 := by rw [pow_add]
          _ = 55987790648 := by rw [factor_5_29]; decide
      have factor_5_31 : (13 : ZMod 89580367801) ^ 2634716700 = 69478864167 := by
        calc
          (13 : ZMod 89580367801) ^ 2634716700 = (13 : ZMod 89580367801) ^ (1317358350 + 1317358350) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1317358350 * (13 : ZMod 89580367801) ^ 1317358350 := by rw [pow_add]
          _ = 69478864167 := by rw [factor_5_30]; decide
      have factor_5_32 : (13 : ZMod 89580367801) ^ 5269433400 = 54621519194 := by
        calc
          (13 : ZMod 89580367801) ^ 5269433400 = (13 : ZMod 89580367801) ^ (2634716700 + 2634716700) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 2634716700 * (13 : ZMod 89580367801) ^ 2634716700 := by rw [pow_add]
          _ = 54621519194 := by rw [factor_5_31]; decide
      change (13 : ZMod 89580367801) ^ 5269433400 ≠ 1
      rw [factor_5_32]
      decide
    ·
      have factor_6_0 : (13 : ZMod 89580367801) ^ 1 = 13 := by norm_num
      have factor_6_1 : (13 : ZMod 89580367801) ^ 2 = 169 := by
        calc
          (13 : ZMod 89580367801) ^ 2 = (13 : ZMod 89580367801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1 * (13 : ZMod 89580367801) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_6_0]; decide
      have factor_6_2 : (13 : ZMod 89580367801) ^ 4 = 28561 := by
        calc
          (13 : ZMod 89580367801) ^ 4 = (13 : ZMod 89580367801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 2 * (13 : ZMod 89580367801) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_6_1]; decide
      have factor_6_3 : (13 : ZMod 89580367801) ^ 8 = 815730721 := by
        calc
          (13 : ZMod 89580367801) ^ 8 = (13 : ZMod 89580367801) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 4 * (13 : ZMod 89580367801) ^ 4 := by rw [pow_add]
          _ = 815730721 := by rw [factor_6_2]; decide
      have factor_6_4 : (13 : ZMod 89580367801) ^ 17 = 3497695754 := by
        calc
          (13 : ZMod 89580367801) ^ 17 = (13 : ZMod 89580367801) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 8 * (13 : ZMod 89580367801) ^ 8) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 3497695754 := by rw [factor_6_3]; decide
      have factor_6_5 : (13 : ZMod 89580367801) ^ 35 = 72223232433 := by
        calc
          (13 : ZMod 89580367801) ^ 35 = (13 : ZMod 89580367801) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 17 * (13 : ZMod 89580367801) ^ 17) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 72223232433 := by rw [factor_6_4]; decide
      have factor_6_6 : (13 : ZMod 89580367801) ^ 70 = 26005204285 := by
        calc
          (13 : ZMod 89580367801) ^ 70 = (13 : ZMod 89580367801) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 35 * (13 : ZMod 89580367801) ^ 35 := by rw [pow_add]
          _ = 26005204285 := by rw [factor_6_5]; decide
      have factor_6_7 : (13 : ZMod 89580367801) ^ 140 = 52189097396 := by
        calc
          (13 : ZMod 89580367801) ^ 140 = (13 : ZMod 89580367801) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 70 * (13 : ZMod 89580367801) ^ 70 := by rw [pow_add]
          _ = 52189097396 := by rw [factor_6_6]; decide
      have factor_6_8 : (13 : ZMod 89580367801) ^ 281 = 4544872917 := by
        calc
          (13 : ZMod 89580367801) ^ 281 = (13 : ZMod 89580367801) ^ (140 + 140 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 140 * (13 : ZMod 89580367801) ^ 140) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 4544872917 := by rw [factor_6_7]; decide
      have factor_6_9 : (13 : ZMod 89580367801) ^ 562 = 71645948905 := by
        calc
          (13 : ZMod 89580367801) ^ 562 = (13 : ZMod 89580367801) ^ (281 + 281) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 281 * (13 : ZMod 89580367801) ^ 281 := by rw [pow_add]
          _ = 71645948905 := by rw [factor_6_8]; decide
      have factor_6_10 : (13 : ZMod 89580367801) ^ 1124 = 30152718813 := by
        calc
          (13 : ZMod 89580367801) ^ 1124 = (13 : ZMod 89580367801) ^ (562 + 562) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 562 * (13 : ZMod 89580367801) ^ 562 := by rw [pow_add]
          _ = 30152718813 := by rw [factor_6_9]; decide
      have factor_6_11 : (13 : ZMod 89580367801) ^ 2248 = 38723880521 := by
        calc
          (13 : ZMod 89580367801) ^ 2248 = (13 : ZMod 89580367801) ^ (1124 + 1124) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1124 * (13 : ZMod 89580367801) ^ 1124 := by rw [pow_add]
          _ = 38723880521 := by rw [factor_6_10]; decide
      have factor_6_12 : (13 : ZMod 89580367801) ^ 4496 = 11876357564 := by
        calc
          (13 : ZMod 89580367801) ^ 4496 = (13 : ZMod 89580367801) ^ (2248 + 2248) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 2248 * (13 : ZMod 89580367801) ^ 2248 := by rw [pow_add]
          _ = 11876357564 := by rw [factor_6_11]; decide
      have factor_6_13 : (13 : ZMod 89580367801) ^ 8992 = 74647450534 := by
        calc
          (13 : ZMod 89580367801) ^ 8992 = (13 : ZMod 89580367801) ^ (4496 + 4496) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 4496 * (13 : ZMod 89580367801) ^ 4496 := by rw [pow_add]
          _ = 74647450534 := by rw [factor_6_12]; decide
      have factor_6_14 : (13 : ZMod 89580367801) ^ 17985 = 29181615567 := by
        calc
          (13 : ZMod 89580367801) ^ 17985 = (13 : ZMod 89580367801) ^ (8992 + 8992 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 8992 * (13 : ZMod 89580367801) ^ 8992) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 29181615567 := by rw [factor_6_13]; decide
      have factor_6_15 : (13 : ZMod 89580367801) ^ 35970 = 89385424308 := by
        calc
          (13 : ZMod 89580367801) ^ 35970 = (13 : ZMod 89580367801) ^ (17985 + 17985) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 17985 * (13 : ZMod 89580367801) ^ 17985 := by rw [pow_add]
          _ = 89385424308 := by rw [factor_6_14]; decide
      have factor_6_16 : (13 : ZMod 89580367801) ^ 71941 = 45605616806 := by
        calc
          (13 : ZMod 89580367801) ^ 71941 = (13 : ZMod 89580367801) ^ (35970 + 35970 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 35970 * (13 : ZMod 89580367801) ^ 35970) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 45605616806 := by rw [factor_6_15]; decide
      have factor_6_17 : (13 : ZMod 89580367801) ^ 143882 = 7069931051 := by
        calc
          (13 : ZMod 89580367801) ^ 143882 = (13 : ZMod 89580367801) ^ (71941 + 71941) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 71941 * (13 : ZMod 89580367801) ^ 71941 := by rw [pow_add]
          _ = 7069931051 := by rw [factor_6_16]; decide
      have factor_6_18 : (13 : ZMod 89580367801) ^ 287765 = 24717863070 := by
        calc
          (13 : ZMod 89580367801) ^ 287765 = (13 : ZMod 89580367801) ^ (143882 + 143882 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 143882 * (13 : ZMod 89580367801) ^ 143882) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 24717863070 := by rw [factor_6_17]; decide
      have factor_6_19 : (13 : ZMod 89580367801) ^ 575531 = 2875558785 := by
        calc
          (13 : ZMod 89580367801) ^ 575531 = (13 : ZMod 89580367801) ^ (287765 + 287765 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 287765 * (13 : ZMod 89580367801) ^ 287765) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 2875558785 := by rw [factor_6_18]; decide
      have factor_6_20 : (13 : ZMod 89580367801) ^ 1151063 = 77674898752 := by
        calc
          (13 : ZMod 89580367801) ^ 1151063 = (13 : ZMod 89580367801) ^ (575531 + 575531 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 575531 * (13 : ZMod 89580367801) ^ 575531) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 77674898752 := by rw [factor_6_19]; decide
      have factor_6_21 : (13 : ZMod 89580367801) ^ 2302127 = 42074064246 := by
        calc
          (13 : ZMod 89580367801) ^ 2302127 = (13 : ZMod 89580367801) ^ (1151063 + 1151063 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1151063 * (13 : ZMod 89580367801) ^ 1151063) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 42074064246 := by rw [factor_6_20]; decide
      have factor_6_22 : (13 : ZMod 89580367801) ^ 4604254 = 45424898972 := by
        calc
          (13 : ZMod 89580367801) ^ 4604254 = (13 : ZMod 89580367801) ^ (2302127 + 2302127) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 2302127 * (13 : ZMod 89580367801) ^ 2302127 := by rw [pow_add]
          _ = 45424898972 := by rw [factor_6_21]; decide
      have factor_6_23 : (13 : ZMod 89580367801) ^ 9208508 = 40429938136 := by
        calc
          (13 : ZMod 89580367801) ^ 9208508 = (13 : ZMod 89580367801) ^ (4604254 + 4604254) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 4604254 * (13 : ZMod 89580367801) ^ 4604254 := by rw [pow_add]
          _ = 40429938136 := by rw [factor_6_22]; decide
      have factor_6_24 : (13 : ZMod 89580367801) ^ 18417016 = 61901781176 := by
        calc
          (13 : ZMod 89580367801) ^ 18417016 = (13 : ZMod 89580367801) ^ (9208508 + 9208508) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 9208508 * (13 : ZMod 89580367801) ^ 9208508 := by rw [pow_add]
          _ = 61901781176 := by rw [factor_6_23]; decide
      have factor_6_25 : (13 : ZMod 89580367801) ^ 36834032 = 28108481155 := by
        calc
          (13 : ZMod 89580367801) ^ 36834032 = (13 : ZMod 89580367801) ^ (18417016 + 18417016) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 18417016 * (13 : ZMod 89580367801) ^ 18417016 := by rw [pow_add]
          _ = 28108481155 := by rw [factor_6_24]; decide
      have factor_6_26 : (13 : ZMod 89580367801) ^ 73668065 = 32760989213 := by
        calc
          (13 : ZMod 89580367801) ^ 73668065 = (13 : ZMod 89580367801) ^ (36834032 + 36834032 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 36834032 * (13 : ZMod 89580367801) ^ 36834032) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 32760989213 := by rw [factor_6_25]; decide
      have factor_6_27 : (13 : ZMod 89580367801) ^ 147336131 = 56291650372 := by
        calc
          (13 : ZMod 89580367801) ^ 147336131 = (13 : ZMod 89580367801) ^ (73668065 + 73668065 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 73668065 * (13 : ZMod 89580367801) ^ 73668065) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 56291650372 := by rw [factor_6_26]; decide
      have factor_6_28 : (13 : ZMod 89580367801) ^ 294672262 = 72957280877 := by
        calc
          (13 : ZMod 89580367801) ^ 294672262 = (13 : ZMod 89580367801) ^ (147336131 + 147336131) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 147336131 * (13 : ZMod 89580367801) ^ 147336131 := by rw [pow_add]
          _ = 72957280877 := by rw [factor_6_27]; decide
      have factor_6_29 : (13 : ZMod 89580367801) ^ 589344525 = 68184180818 := by
        calc
          (13 : ZMod 89580367801) ^ 589344525 = (13 : ZMod 89580367801) ^ (294672262 + 294672262 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 294672262 * (13 : ZMod 89580367801) ^ 294672262) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 68184180818 := by rw [factor_6_28]; decide
      have factor_6_30 : (13 : ZMod 89580367801) ^ 1178689050 = 45663756860 := by
        calc
          (13 : ZMod 89580367801) ^ 1178689050 = (13 : ZMod 89580367801) ^ (589344525 + 589344525) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 589344525 * (13 : ZMod 89580367801) ^ 589344525 := by rw [pow_add]
          _ = 45663756860 := by rw [factor_6_29]; decide
      have factor_6_31 : (13 : ZMod 89580367801) ^ 2357378100 = 4280213551 := by
        calc
          (13 : ZMod 89580367801) ^ 2357378100 = (13 : ZMod 89580367801) ^ (1178689050 + 1178689050) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1178689050 * (13 : ZMod 89580367801) ^ 1178689050 := by rw [pow_add]
          _ = 4280213551 := by rw [factor_6_30]; decide
      have factor_6_32 : (13 : ZMod 89580367801) ^ 4714756200 = 21797958160 := by
        calc
          (13 : ZMod 89580367801) ^ 4714756200 = (13 : ZMod 89580367801) ^ (2357378100 + 2357378100) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 2357378100 * (13 : ZMod 89580367801) ^ 2357378100 := by rw [pow_add]
          _ = 21797958160 := by rw [factor_6_31]; decide
      change (13 : ZMod 89580367801) ^ 4714756200 ≠ 1
      rw [factor_6_32]
      decide
    ·
      have factor_7_0 : (13 : ZMod 89580367801) ^ 1 = 13 := by norm_num
      have factor_7_1 : (13 : ZMod 89580367801) ^ 3 = 2197 := by
        calc
          (13 : ZMod 89580367801) ^ 3 = (13 : ZMod 89580367801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1 * (13 : ZMod 89580367801) ^ 1) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_7_0]; decide
      have factor_7_2 : (13 : ZMod 89580367801) ^ 7 = 62748517 := by
        calc
          (13 : ZMod 89580367801) ^ 7 = (13 : ZMod 89580367801) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 3 * (13 : ZMod 89580367801) ^ 3) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 62748517 := by rw [factor_7_1]; decide
      have factor_7_3 : (13 : ZMod 89580367801) ^ 14 = 50479741936 := by
        calc
          (13 : ZMod 89580367801) ^ 14 = (13 : ZMod 89580367801) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 7 * (13 : ZMod 89580367801) ^ 7 := by rw [pow_add]
          _ = 50479741936 := by rw [factor_7_2]; decide
      have factor_7_4 : (13 : ZMod 89580367801) ^ 29 = 10348024001 := by
        calc
          (13 : ZMod 89580367801) ^ 29 = (13 : ZMod 89580367801) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 14 * (13 : ZMod 89580367801) ^ 14) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 10348024001 := by rw [factor_7_3]; decide
      have factor_7_5 : (13 : ZMod 89580367801) ^ 58 = 45473836334 := by
        calc
          (13 : ZMod 89580367801) ^ 58 = (13 : ZMod 89580367801) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 29 * (13 : ZMod 89580367801) ^ 29 := by rw [pow_add]
          _ = 45473836334 := by rw [factor_7_4]; decide
      have factor_7_6 : (13 : ZMod 89580367801) ^ 116 = 74934259328 := by
        calc
          (13 : ZMod 89580367801) ^ 116 = (13 : ZMod 89580367801) ^ (58 + 58) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 58 * (13 : ZMod 89580367801) ^ 58 := by rw [pow_add]
          _ = 74934259328 := by rw [factor_7_5]; decide
      have factor_7_7 : (13 : ZMod 89580367801) ^ 232 = 36578623845 := by
        calc
          (13 : ZMod 89580367801) ^ 232 = (13 : ZMod 89580367801) ^ (116 + 116) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 116 * (13 : ZMod 89580367801) ^ 116 := by rw [pow_add]
          _ = 36578623845 := by rw [factor_7_6]; decide
      have factor_7_8 : (13 : ZMod 89580367801) ^ 464 = 64140356778 := by
        calc
          (13 : ZMod 89580367801) ^ 464 = (13 : ZMod 89580367801) ^ (232 + 232) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 232 * (13 : ZMod 89580367801) ^ 232 := by rw [pow_add]
          _ = 64140356778 := by rw [factor_7_7]; decide
      have factor_7_9 : (13 : ZMod 89580367801) ^ 928 = 8321935006 := by
        calc
          (13 : ZMod 89580367801) ^ 928 = (13 : ZMod 89580367801) ^ (464 + 464) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 464 * (13 : ZMod 89580367801) ^ 464 := by rw [pow_add]
          _ = 8321935006 := by rw [factor_7_8]; decide
      have factor_7_10 : (13 : ZMod 89580367801) ^ 1857 = 44234718981 := by
        calc
          (13 : ZMod 89580367801) ^ 1857 = (13 : ZMod 89580367801) ^ (928 + 928 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 928 * (13 : ZMod 89580367801) ^ 928) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 44234718981 := by rw [factor_7_9]; decide
      have factor_7_11 : (13 : ZMod 89580367801) ^ 3714 = 41484904235 := by
        calc
          (13 : ZMod 89580367801) ^ 3714 = (13 : ZMod 89580367801) ^ (1857 + 1857) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1857 * (13 : ZMod 89580367801) ^ 1857 := by rw [pow_add]
          _ = 41484904235 := by rw [factor_7_10]; decide
      have factor_7_12 : (13 : ZMod 89580367801) ^ 7428 = 7491646825 := by
        calc
          (13 : ZMod 89580367801) ^ 7428 = (13 : ZMod 89580367801) ^ (3714 + 3714) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 3714 * (13 : ZMod 89580367801) ^ 3714 := by rw [pow_add]
          _ = 7491646825 := by rw [factor_7_11]; decide
      have factor_7_13 : (13 : ZMod 89580367801) ^ 14857 = 32734141002 := by
        calc
          (13 : ZMod 89580367801) ^ 14857 = (13 : ZMod 89580367801) ^ (7428 + 7428 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 7428 * (13 : ZMod 89580367801) ^ 7428) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 32734141002 := by rw [factor_7_12]; decide
      have factor_7_14 : (13 : ZMod 89580367801) ^ 29714 = 88734907437 := by
        calc
          (13 : ZMod 89580367801) ^ 29714 = (13 : ZMod 89580367801) ^ (14857 + 14857) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 14857 * (13 : ZMod 89580367801) ^ 14857 := by rw [pow_add]
          _ = 88734907437 := by rw [factor_7_13]; decide
      have factor_7_15 : (13 : ZMod 89580367801) ^ 59429 = 46687409030 := by
        calc
          (13 : ZMod 89580367801) ^ 59429 = (13 : ZMod 89580367801) ^ (29714 + 29714 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 29714 * (13 : ZMod 89580367801) ^ 29714) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 46687409030 := by rw [factor_7_14]; decide
      have factor_7_16 : (13 : ZMod 89580367801) ^ 118859 = 68213414267 := by
        calc
          (13 : ZMod 89580367801) ^ 118859 = (13 : ZMod 89580367801) ^ (59429 + 59429 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 59429 * (13 : ZMod 89580367801) ^ 59429) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 68213414267 := by rw [factor_7_15]; decide
      have factor_7_17 : (13 : ZMod 89580367801) ^ 237719 = 23649157555 := by
        calc
          (13 : ZMod 89580367801) ^ 237719 = (13 : ZMod 89580367801) ^ (118859 + 118859 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 118859 * (13 : ZMod 89580367801) ^ 118859) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 23649157555 := by rw [factor_7_16]; decide
      have factor_7_18 : (13 : ZMod 89580367801) ^ 475439 = 60384788353 := by
        calc
          (13 : ZMod 89580367801) ^ 475439 = (13 : ZMod 89580367801) ^ (237719 + 237719 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 237719 * (13 : ZMod 89580367801) ^ 237719) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 60384788353 := by rw [factor_7_17]; decide
      have factor_7_19 : (13 : ZMod 89580367801) ^ 950878 = 83897093225 := by
        calc
          (13 : ZMod 89580367801) ^ 950878 = (13 : ZMod 89580367801) ^ (475439 + 475439) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 475439 * (13 : ZMod 89580367801) ^ 475439 := by rw [pow_add]
          _ = 83897093225 := by rw [factor_7_18]; decide
      have factor_7_20 : (13 : ZMod 89580367801) ^ 1901757 = 33737993315 := by
        calc
          (13 : ZMod 89580367801) ^ 1901757 = (13 : ZMod 89580367801) ^ (950878 + 950878 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 950878 * (13 : ZMod 89580367801) ^ 950878) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 33737993315 := by rw [factor_7_19]; decide
      have factor_7_21 : (13 : ZMod 89580367801) ^ 3803514 = 53479993804 := by
        calc
          (13 : ZMod 89580367801) ^ 3803514 = (13 : ZMod 89580367801) ^ (1901757 + 1901757) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1901757 * (13 : ZMod 89580367801) ^ 1901757 := by rw [pow_add]
          _ = 53479993804 := by rw [factor_7_20]; decide
      have factor_7_22 : (13 : ZMod 89580367801) ^ 7607028 = 30569890519 := by
        calc
          (13 : ZMod 89580367801) ^ 7607028 = (13 : ZMod 89580367801) ^ (3803514 + 3803514) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 3803514 * (13 : ZMod 89580367801) ^ 3803514 := by rw [pow_add]
          _ = 30569890519 := by rw [factor_7_21]; decide
      have factor_7_23 : (13 : ZMod 89580367801) ^ 15214057 = 52003580010 := by
        calc
          (13 : ZMod 89580367801) ^ 15214057 = (13 : ZMod 89580367801) ^ (7607028 + 7607028 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 7607028 * (13 : ZMod 89580367801) ^ 7607028) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 52003580010 := by rw [factor_7_22]; decide
      have factor_7_24 : (13 : ZMod 89580367801) ^ 30428114 = 73342423793 := by
        calc
          (13 : ZMod 89580367801) ^ 30428114 = (13 : ZMod 89580367801) ^ (15214057 + 15214057) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 15214057 * (13 : ZMod 89580367801) ^ 15214057 := by rw [pow_add]
          _ = 73342423793 := by rw [factor_7_23]; decide
      have factor_7_25 : (13 : ZMod 89580367801) ^ 60856228 = 45518871588 := by
        calc
          (13 : ZMod 89580367801) ^ 60856228 = (13 : ZMod 89580367801) ^ (30428114 + 30428114) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 30428114 * (13 : ZMod 89580367801) ^ 30428114 := by rw [pow_add]
          _ = 45518871588 := by rw [factor_7_24]; decide
      have factor_7_26 : (13 : ZMod 89580367801) ^ 121712456 = 64146669828 := by
        calc
          (13 : ZMod 89580367801) ^ 121712456 = (13 : ZMod 89580367801) ^ (60856228 + 60856228) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 60856228 * (13 : ZMod 89580367801) ^ 60856228 := by rw [pow_add]
          _ = 64146669828 := by rw [factor_7_25]; decide
      have factor_7_27 : (13 : ZMod 89580367801) ^ 243424912 = 22144375859 := by
        calc
          (13 : ZMod 89580367801) ^ 243424912 = (13 : ZMod 89580367801) ^ (121712456 + 121712456) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 121712456 * (13 : ZMod 89580367801) ^ 121712456 := by rw [pow_add]
          _ = 22144375859 := by rw [factor_7_26]; decide
      have factor_7_28 : (13 : ZMod 89580367801) ^ 486849825 = 23869899506 := by
        calc
          (13 : ZMod 89580367801) ^ 486849825 = (13 : ZMod 89580367801) ^ (243424912 + 243424912 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 243424912 * (13 : ZMod 89580367801) ^ 243424912) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 23869899506 := by rw [factor_7_27]; decide
      have factor_7_29 : (13 : ZMod 89580367801) ^ 973699650 = 80751738358 := by
        calc
          (13 : ZMod 89580367801) ^ 973699650 = (13 : ZMod 89580367801) ^ (486849825 + 486849825) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 486849825 * (13 : ZMod 89580367801) ^ 486849825 := by rw [pow_add]
          _ = 80751738358 := by rw [factor_7_28]; decide
      have factor_7_30 : (13 : ZMod 89580367801) ^ 1947399300 = 68210643298 := by
        calc
          (13 : ZMod 89580367801) ^ 1947399300 = (13 : ZMod 89580367801) ^ (973699650 + 973699650) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 973699650 * (13 : ZMod 89580367801) ^ 973699650 := by rw [pow_add]
          _ = 68210643298 := by rw [factor_7_29]; decide
      have factor_7_31 : (13 : ZMod 89580367801) ^ 3894798600 = 45609372840 := by
        calc
          (13 : ZMod 89580367801) ^ 3894798600 = (13 : ZMod 89580367801) ^ (1947399300 + 1947399300) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1947399300 * (13 : ZMod 89580367801) ^ 1947399300 := by rw [pow_add]
          _ = 45609372840 := by rw [factor_7_30]; decide
      change (13 : ZMod 89580367801) ^ 3894798600 ≠ 1
      rw [factor_7_31]
      decide
    ·
      have factor_8_0 : (13 : ZMod 89580367801) ^ 1 = 13 := by norm_num
      have factor_8_1 : (13 : ZMod 89580367801) ^ 2 = 169 := by
        calc
          (13 : ZMod 89580367801) ^ 2 = (13 : ZMod 89580367801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1 * (13 : ZMod 89580367801) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_8_0]; decide
      have factor_8_2 : (13 : ZMod 89580367801) ^ 5 = 371293 := by
        calc
          (13 : ZMod 89580367801) ^ 5 = (13 : ZMod 89580367801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 2 * (13 : ZMod 89580367801) ^ 2) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 371293 := by rw [factor_8_1]; decide
      have factor_8_3 : (13 : ZMod 89580367801) ^ 11 = 553038017 := by
        calc
          (13 : ZMod 89580367801) ^ 11 = (13 : ZMod 89580367801) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 5 * (13 : ZMod 89580367801) ^ 5) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 553038017 := by rw [factor_8_2]; decide
      have factor_8_4 : (13 : ZMod 89580367801) ^ 23 = 34907421322 := by
        calc
          (13 : ZMod 89580367801) ^ 23 = (13 : ZMod 89580367801) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 11 * (13 : ZMod 89580367801) ^ 11) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 34907421322 := by rw [factor_8_3]; decide
      have factor_8_5 : (13 : ZMod 89580367801) ^ 46 = 43820840858 := by
        calc
          (13 : ZMod 89580367801) ^ 46 = (13 : ZMod 89580367801) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 23 * (13 : ZMod 89580367801) ^ 23 := by rw [pow_add]
          _ = 43820840858 := by rw [factor_8_4]; decide
      have factor_8_6 : (13 : ZMod 89580367801) ^ 92 = 55192022462 := by
        calc
          (13 : ZMod 89580367801) ^ 92 = (13 : ZMod 89580367801) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 46 * (13 : ZMod 89580367801) ^ 46 := by rw [pow_add]
          _ = 55192022462 := by rw [factor_8_5]; decide
      have factor_8_7 : (13 : ZMod 89580367801) ^ 184 = 31851165181 := by
        calc
          (13 : ZMod 89580367801) ^ 184 = (13 : ZMod 89580367801) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 92 * (13 : ZMod 89580367801) ^ 92 := by rw [pow_add]
          _ = 31851165181 := by rw [factor_8_6]; decide
      have factor_8_8 : (13 : ZMod 89580367801) ^ 368 = 68169558077 := by
        calc
          (13 : ZMod 89580367801) ^ 368 = (13 : ZMod 89580367801) ^ (184 + 184) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 184 * (13 : ZMod 89580367801) ^ 184 := by rw [pow_add]
          _ = 68169558077 := by rw [factor_8_7]; decide
      have factor_8_9 : (13 : ZMod 89580367801) ^ 736 = 41495987704 := by
        calc
          (13 : ZMod 89580367801) ^ 736 = (13 : ZMod 89580367801) ^ (368 + 368) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 368 * (13 : ZMod 89580367801) ^ 368 := by rw [pow_add]
          _ = 41495987704 := by rw [factor_8_8]; decide
      have factor_8_10 : (13 : ZMod 89580367801) ^ 1472 = 68659839878 := by
        calc
          (13 : ZMod 89580367801) ^ 1472 = (13 : ZMod 89580367801) ^ (736 + 736) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 736 * (13 : ZMod 89580367801) ^ 736 := by rw [pow_add]
          _ = 68659839878 := by rw [factor_8_9]; decide
      have factor_8_11 : (13 : ZMod 89580367801) ^ 2945 = 11167580375 := by
        calc
          (13 : ZMod 89580367801) ^ 2945 = (13 : ZMod 89580367801) ^ (1472 + 1472 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 1472 * (13 : ZMod 89580367801) ^ 1472) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 11167580375 := by rw [factor_8_10]; decide
      have factor_8_12 : (13 : ZMod 89580367801) ^ 5891 = 70729913407 := by
        calc
          (13 : ZMod 89580367801) ^ 5891 = (13 : ZMod 89580367801) ^ (2945 + 2945 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 2945 * (13 : ZMod 89580367801) ^ 2945) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 70729913407 := by rw [factor_8_11]; decide
      have factor_8_13 : (13 : ZMod 89580367801) ^ 11783 = 60895509769 := by
        calc
          (13 : ZMod 89580367801) ^ 11783 = (13 : ZMod 89580367801) ^ (5891 + 5891 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 5891 * (13 : ZMod 89580367801) ^ 5891) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 60895509769 := by rw [factor_8_12]; decide
      have factor_8_14 : (13 : ZMod 89580367801) ^ 23567 = 1176457937 := by
        calc
          (13 : ZMod 89580367801) ^ 23567 = (13 : ZMod 89580367801) ^ (11783 + 11783 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 11783 * (13 : ZMod 89580367801) ^ 11783) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 1176457937 := by rw [factor_8_13]; decide
      have factor_8_15 : (13 : ZMod 89580367801) ^ 47134 = 46214783161 := by
        calc
          (13 : ZMod 89580367801) ^ 47134 = (13 : ZMod 89580367801) ^ (23567 + 23567) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 23567 * (13 : ZMod 89580367801) ^ 23567 := by rw [pow_add]
          _ = 46214783161 := by rw [factor_8_14]; decide
      have factor_8_16 : (13 : ZMod 89580367801) ^ 94268 = 24407096266 := by
        calc
          (13 : ZMod 89580367801) ^ 94268 = (13 : ZMod 89580367801) ^ (47134 + 47134) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 47134 * (13 : ZMod 89580367801) ^ 47134 := by rw [pow_add]
          _ = 24407096266 := by rw [factor_8_15]; decide
      have factor_8_17 : (13 : ZMod 89580367801) ^ 188536 = 39840069137 := by
        calc
          (13 : ZMod 89580367801) ^ 188536 = (13 : ZMod 89580367801) ^ (94268 + 94268) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 94268 * (13 : ZMod 89580367801) ^ 94268 := by rw [pow_add]
          _ = 39840069137 := by rw [factor_8_16]; decide
      have factor_8_18 : (13 : ZMod 89580367801) ^ 377072 = 68589746166 := by
        calc
          (13 : ZMod 89580367801) ^ 377072 = (13 : ZMod 89580367801) ^ (188536 + 188536) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 188536 * (13 : ZMod 89580367801) ^ 188536 := by rw [pow_add]
          _ = 68589746166 := by rw [factor_8_17]; decide
      have factor_8_19 : (13 : ZMod 89580367801) ^ 754145 = 62860598450 := by
        calc
          (13 : ZMod 89580367801) ^ 754145 = (13 : ZMod 89580367801) ^ (377072 + 377072 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 377072 * (13 : ZMod 89580367801) ^ 377072) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 62860598450 := by rw [factor_8_18]; decide
      have factor_8_20 : (13 : ZMod 89580367801) ^ 1508290 = 64838816174 := by
        calc
          (13 : ZMod 89580367801) ^ 1508290 = (13 : ZMod 89580367801) ^ (754145 + 754145) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 754145 * (13 : ZMod 89580367801) ^ 754145 := by rw [pow_add]
          _ = 64838816174 := by rw [factor_8_19]; decide
      have factor_8_21 : (13 : ZMod 89580367801) ^ 3016580 = 58523410961 := by
        calc
          (13 : ZMod 89580367801) ^ 3016580 = (13 : ZMod 89580367801) ^ (1508290 + 1508290) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1508290 * (13 : ZMod 89580367801) ^ 1508290 := by rw [pow_add]
          _ = 58523410961 := by rw [factor_8_20]; decide
      have factor_8_22 : (13 : ZMod 89580367801) ^ 6033160 = 9656399660 := by
        calc
          (13 : ZMod 89580367801) ^ 6033160 = (13 : ZMod 89580367801) ^ (3016580 + 3016580) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 3016580 * (13 : ZMod 89580367801) ^ 3016580 := by rw [pow_add]
          _ = 9656399660 := by rw [factor_8_21]; decide
      have factor_8_23 : (13 : ZMod 89580367801) ^ 12066321 = 57273071992 := by
        calc
          (13 : ZMod 89580367801) ^ 12066321 = (13 : ZMod 89580367801) ^ (6033160 + 6033160 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 6033160 * (13 : ZMod 89580367801) ^ 6033160) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 57273071992 := by rw [factor_8_22]; decide
      have factor_8_24 : (13 : ZMod 89580367801) ^ 24132642 = 35187237141 := by
        calc
          (13 : ZMod 89580367801) ^ 24132642 = (13 : ZMod 89580367801) ^ (12066321 + 12066321) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 12066321 * (13 : ZMod 89580367801) ^ 12066321 := by rw [pow_add]
          _ = 35187237141 := by rw [factor_8_23]; decide
      have factor_8_25 : (13 : ZMod 89580367801) ^ 48265284 = 11573328559 := by
        calc
          (13 : ZMod 89580367801) ^ 48265284 = (13 : ZMod 89580367801) ^ (24132642 + 24132642) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 24132642 * (13 : ZMod 89580367801) ^ 24132642 := by rw [pow_add]
          _ = 11573328559 := by rw [factor_8_24]; decide
      have factor_8_26 : (13 : ZMod 89580367801) ^ 96530568 = 16713127410 := by
        calc
          (13 : ZMod 89580367801) ^ 96530568 = (13 : ZMod 89580367801) ^ (48265284 + 48265284) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 48265284 * (13 : ZMod 89580367801) ^ 48265284 := by rw [pow_add]
          _ = 16713127410 := by rw [factor_8_25]; decide
      have factor_8_27 : (13 : ZMod 89580367801) ^ 193061137 = 16923086489 := by
        calc
          (13 : ZMod 89580367801) ^ 193061137 = (13 : ZMod 89580367801) ^ (96530568 + 96530568 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 96530568 * (13 : ZMod 89580367801) ^ 96530568) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 16923086489 := by rw [factor_8_26]; decide
      have factor_8_28 : (13 : ZMod 89580367801) ^ 386122275 = 86072468915 := by
        calc
          (13 : ZMod 89580367801) ^ 386122275 = (13 : ZMod 89580367801) ^ (193061137 + 193061137 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = ((13 : ZMod 89580367801) ^ 193061137 * (13 : ZMod 89580367801) ^ 193061137) * (13 : ZMod 89580367801) := by rw [pow_succ, pow_add]
          _ = 86072468915 := by rw [factor_8_27]; decide
      have factor_8_29 : (13 : ZMod 89580367801) ^ 772244550 = 11710643351 := by
        calc
          (13 : ZMod 89580367801) ^ 772244550 = (13 : ZMod 89580367801) ^ (386122275 + 386122275) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 386122275 * (13 : ZMod 89580367801) ^ 386122275 := by rw [pow_add]
          _ = 11710643351 := by rw [factor_8_28]; decide
      have factor_8_30 : (13 : ZMod 89580367801) ^ 1544489100 = 86637799298 := by
        calc
          (13 : ZMod 89580367801) ^ 1544489100 = (13 : ZMod 89580367801) ^ (772244550 + 772244550) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 772244550 * (13 : ZMod 89580367801) ^ 772244550 := by rw [pow_add]
          _ = 86637799298 := by rw [factor_8_29]; decide
      have factor_8_31 : (13 : ZMod 89580367801) ^ 3088978200 = 38932634449 := by
        calc
          (13 : ZMod 89580367801) ^ 3088978200 = (13 : ZMod 89580367801) ^ (1544489100 + 1544489100) :=
            congrArg (fun n : ℕ => (13 : ZMod 89580367801) ^ n) (by norm_num)
          _ = (13 : ZMod 89580367801) ^ 1544489100 * (13 : ZMod 89580367801) ^ 1544489100 := by rw [pow_add]
          _ = 38932634449 := by rw [factor_8_30]; decide
      change (13 : ZMod 89580367801) ^ 3088978200 ≠ 1
      rw [factor_8_31]
      decide

#print axioms prime_lucas_89580367801

end TotientTailPeriodKiller
end Erdos249257
