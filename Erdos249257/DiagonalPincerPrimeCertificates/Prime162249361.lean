import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=23 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_162249361 : Nat.Prime 162249361 := by
  apply lucas_primality 162249361 (31 : ZMod 162249361)
  ·
      have fermat_0 : (31 : ZMod 162249361) ^ 1 = 31 := by norm_num
      have fermat_1 : (31 : ZMod 162249361) ^ 2 = 961 := by
        calc
          (31 : ZMod 162249361) ^ 2 = (31 : ZMod 162249361) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 1 * (31 : ZMod 162249361) ^ 1 := by rw [pow_add]
          _ = 961 := by rw [fermat_0]; decide
      have fermat_2 : (31 : ZMod 162249361) ^ 4 = 923521 := by
        calc
          (31 : ZMod 162249361) ^ 4 = (31 : ZMod 162249361) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 2 * (31 : ZMod 162249361) ^ 2 := by rw [pow_add]
          _ = 923521 := by rw [fermat_1]; decide
      have fermat_3 : (31 : ZMod 162249361) ^ 9 = 115289555 := by
        calc
          (31 : ZMod 162249361) ^ 9 = (31 : ZMod 162249361) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 4 * (31 : ZMod 162249361) ^ 4) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 115289555 := by rw [fermat_2]; decide
      have fermat_4 : (31 : ZMod 162249361) ^ 19 = 148425759 := by
        calc
          (31 : ZMod 162249361) ^ 19 = (31 : ZMod 162249361) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 9 * (31 : ZMod 162249361) ^ 9) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 148425759 := by rw [fermat_3]; decide
      have fermat_5 : (31 : ZMod 162249361) ^ 38 = 29097517 := by
        calc
          (31 : ZMod 162249361) ^ 38 = (31 : ZMod 162249361) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 19 * (31 : ZMod 162249361) ^ 19 := by rw [pow_add]
          _ = 29097517 := by rw [fermat_4]; decide
      have fermat_6 : (31 : ZMod 162249361) ^ 77 = 15286485 := by
        calc
          (31 : ZMod 162249361) ^ 77 = (31 : ZMod 162249361) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 38 * (31 : ZMod 162249361) ^ 38) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 15286485 := by rw [fermat_5]; decide
      have fermat_7 : (31 : ZMod 162249361) ^ 154 = 64212834 := by
        calc
          (31 : ZMod 162249361) ^ 154 = (31 : ZMod 162249361) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 77 * (31 : ZMod 162249361) ^ 77 := by rw [pow_add]
          _ = 64212834 := by rw [fermat_6]; decide
      have fermat_8 : (31 : ZMod 162249361) ^ 309 = 60023831 := by
        calc
          (31 : ZMod 162249361) ^ 309 = (31 : ZMod 162249361) ^ (154 + 154 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 154 * (31 : ZMod 162249361) ^ 154) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 60023831 := by rw [fermat_7]; decide
      have fermat_9 : (31 : ZMod 162249361) ^ 618 = 139106944 := by
        calc
          (31 : ZMod 162249361) ^ 618 = (31 : ZMod 162249361) ^ (309 + 309) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 309 * (31 : ZMod 162249361) ^ 309 := by rw [pow_add]
          _ = 139106944 := by rw [fermat_8]; decide
      have fermat_10 : (31 : ZMod 162249361) ^ 1237 = 161997213 := by
        calc
          (31 : ZMod 162249361) ^ 1237 = (31 : ZMod 162249361) ^ (618 + 618 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 618 * (31 : ZMod 162249361) ^ 618) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 161997213 := by rw [fermat_9]; decide
      have fermat_11 : (31 : ZMod 162249361) ^ 2475 = 94042957 := by
        calc
          (31 : ZMod 162249361) ^ 2475 = (31 : ZMod 162249361) ^ (1237 + 1237 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 1237 * (31 : ZMod 162249361) ^ 1237) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 94042957 := by rw [fermat_10]; decide
      have fermat_12 : (31 : ZMod 162249361) ^ 4951 = 28538455 := by
        calc
          (31 : ZMod 162249361) ^ 4951 = (31 : ZMod 162249361) ^ (2475 + 2475 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 2475 * (31 : ZMod 162249361) ^ 2475) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 28538455 := by rw [fermat_11]; decide
      have fermat_13 : (31 : ZMod 162249361) ^ 9902 = 134125964 := by
        calc
          (31 : ZMod 162249361) ^ 9902 = (31 : ZMod 162249361) ^ (4951 + 4951) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 4951 * (31 : ZMod 162249361) ^ 4951 := by rw [pow_add]
          _ = 134125964 := by rw [fermat_12]; decide
      have fermat_14 : (31 : ZMod 162249361) ^ 19805 = 130627276 := by
        calc
          (31 : ZMod 162249361) ^ 19805 = (31 : ZMod 162249361) ^ (9902 + 9902 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 9902 * (31 : ZMod 162249361) ^ 9902) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 130627276 := by rw [fermat_13]; decide
      have fermat_15 : (31 : ZMod 162249361) ^ 39611 = 66422566 := by
        calc
          (31 : ZMod 162249361) ^ 39611 = (31 : ZMod 162249361) ^ (19805 + 19805 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 19805 * (31 : ZMod 162249361) ^ 19805) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 66422566 := by rw [fermat_14]; decide
      have fermat_16 : (31 : ZMod 162249361) ^ 79223 = 119952356 := by
        calc
          (31 : ZMod 162249361) ^ 79223 = (31 : ZMod 162249361) ^ (39611 + 39611 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 39611 * (31 : ZMod 162249361) ^ 39611) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 119952356 := by rw [fermat_15]; decide
      have fermat_17 : (31 : ZMod 162249361) ^ 158446 = 56129882 := by
        calc
          (31 : ZMod 162249361) ^ 158446 = (31 : ZMod 162249361) ^ (79223 + 79223) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 79223 * (31 : ZMod 162249361) ^ 79223 := by rw [pow_add]
          _ = 56129882 := by rw [fermat_16]; decide
      have fermat_18 : (31 : ZMod 162249361) ^ 316893 = 95692262 := by
        calc
          (31 : ZMod 162249361) ^ 316893 = (31 : ZMod 162249361) ^ (158446 + 158446 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 158446 * (31 : ZMod 162249361) ^ 158446) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 95692262 := by rw [fermat_17]; decide
      have fermat_19 : (31 : ZMod 162249361) ^ 633786 = 13978130 := by
        calc
          (31 : ZMod 162249361) ^ 633786 = (31 : ZMod 162249361) ^ (316893 + 316893) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 316893 * (31 : ZMod 162249361) ^ 316893 := by rw [pow_add]
          _ = 13978130 := by rw [fermat_18]; decide
      have fermat_20 : (31 : ZMod 162249361) ^ 1267573 = 14859719 := by
        calc
          (31 : ZMod 162249361) ^ 1267573 = (31 : ZMod 162249361) ^ (633786 + 633786 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 633786 * (31 : ZMod 162249361) ^ 633786) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 14859719 := by rw [fermat_19]; decide
      have fermat_21 : (31 : ZMod 162249361) ^ 2535146 = 90147704 := by
        calc
          (31 : ZMod 162249361) ^ 2535146 = (31 : ZMod 162249361) ^ (1267573 + 1267573) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 1267573 * (31 : ZMod 162249361) ^ 1267573 := by rw [pow_add]
          _ = 90147704 := by rw [fermat_20]; decide
      have fermat_22 : (31 : ZMod 162249361) ^ 5070292 = 130161744 := by
        calc
          (31 : ZMod 162249361) ^ 5070292 = (31 : ZMod 162249361) ^ (2535146 + 2535146) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 2535146 * (31 : ZMod 162249361) ^ 2535146 := by rw [pow_add]
          _ = 130161744 := by rw [fermat_21]; decide
      have fermat_23 : (31 : ZMod 162249361) ^ 10140585 = 41459283 := by
        calc
          (31 : ZMod 162249361) ^ 10140585 = (31 : ZMod 162249361) ^ (5070292 + 5070292 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 5070292 * (31 : ZMod 162249361) ^ 5070292) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 41459283 := by rw [fermat_22]; decide
      have fermat_24 : (31 : ZMod 162249361) ^ 20281170 = 144949035 := by
        calc
          (31 : ZMod 162249361) ^ 20281170 = (31 : ZMod 162249361) ^ (10140585 + 10140585) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 10140585 * (31 : ZMod 162249361) ^ 10140585 := by rw [pow_add]
          _ = 144949035 := by rw [fermat_23]; decide
      have fermat_25 : (31 : ZMod 162249361) ^ 40562340 = 45718937 := by
        calc
          (31 : ZMod 162249361) ^ 40562340 = (31 : ZMod 162249361) ^ (20281170 + 20281170) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 20281170 * (31 : ZMod 162249361) ^ 20281170 := by rw [pow_add]
          _ = 45718937 := by rw [fermat_24]; decide
      have fermat_26 : (31 : ZMod 162249361) ^ 81124680 = 162249360 := by
        calc
          (31 : ZMod 162249361) ^ 81124680 = (31 : ZMod 162249361) ^ (40562340 + 40562340) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 40562340 * (31 : ZMod 162249361) ^ 40562340 := by rw [pow_add]
          _ = 162249360 := by rw [fermat_25]; decide
      have fermat_27 : (31 : ZMod 162249361) ^ 162249360 = 1 := by
        calc
          (31 : ZMod 162249361) ^ 162249360 = (31 : ZMod 162249361) ^ (81124680 + 81124680) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 81124680 * (31 : ZMod 162249361) ^ 81124680 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (7, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (7, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 162249361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (31 : ZMod 162249361) ^ 1 = 31 := by norm_num
      have factor_0_1 : (31 : ZMod 162249361) ^ 2 = 961 := by
        calc
          (31 : ZMod 162249361) ^ 2 = (31 : ZMod 162249361) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 1 * (31 : ZMod 162249361) ^ 1 := by rw [pow_add]
          _ = 961 := by rw [factor_0_0]; decide
      have factor_0_2 : (31 : ZMod 162249361) ^ 4 = 923521 := by
        calc
          (31 : ZMod 162249361) ^ 4 = (31 : ZMod 162249361) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 2 * (31 : ZMod 162249361) ^ 2 := by rw [pow_add]
          _ = 923521 := by rw [factor_0_1]; decide
      have factor_0_3 : (31 : ZMod 162249361) ^ 9 = 115289555 := by
        calc
          (31 : ZMod 162249361) ^ 9 = (31 : ZMod 162249361) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 4 * (31 : ZMod 162249361) ^ 4) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 115289555 := by rw [factor_0_2]; decide
      have factor_0_4 : (31 : ZMod 162249361) ^ 19 = 148425759 := by
        calc
          (31 : ZMod 162249361) ^ 19 = (31 : ZMod 162249361) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 9 * (31 : ZMod 162249361) ^ 9) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 148425759 := by rw [factor_0_3]; decide
      have factor_0_5 : (31 : ZMod 162249361) ^ 38 = 29097517 := by
        calc
          (31 : ZMod 162249361) ^ 38 = (31 : ZMod 162249361) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 19 * (31 : ZMod 162249361) ^ 19 := by rw [pow_add]
          _ = 29097517 := by rw [factor_0_4]; decide
      have factor_0_6 : (31 : ZMod 162249361) ^ 77 = 15286485 := by
        calc
          (31 : ZMod 162249361) ^ 77 = (31 : ZMod 162249361) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 38 * (31 : ZMod 162249361) ^ 38) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 15286485 := by rw [factor_0_5]; decide
      have factor_0_7 : (31 : ZMod 162249361) ^ 154 = 64212834 := by
        calc
          (31 : ZMod 162249361) ^ 154 = (31 : ZMod 162249361) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 77 * (31 : ZMod 162249361) ^ 77 := by rw [pow_add]
          _ = 64212834 := by rw [factor_0_6]; decide
      have factor_0_8 : (31 : ZMod 162249361) ^ 309 = 60023831 := by
        calc
          (31 : ZMod 162249361) ^ 309 = (31 : ZMod 162249361) ^ (154 + 154 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 154 * (31 : ZMod 162249361) ^ 154) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 60023831 := by rw [factor_0_7]; decide
      have factor_0_9 : (31 : ZMod 162249361) ^ 618 = 139106944 := by
        calc
          (31 : ZMod 162249361) ^ 618 = (31 : ZMod 162249361) ^ (309 + 309) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 309 * (31 : ZMod 162249361) ^ 309 := by rw [pow_add]
          _ = 139106944 := by rw [factor_0_8]; decide
      have factor_0_10 : (31 : ZMod 162249361) ^ 1237 = 161997213 := by
        calc
          (31 : ZMod 162249361) ^ 1237 = (31 : ZMod 162249361) ^ (618 + 618 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 618 * (31 : ZMod 162249361) ^ 618) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 161997213 := by rw [factor_0_9]; decide
      have factor_0_11 : (31 : ZMod 162249361) ^ 2475 = 94042957 := by
        calc
          (31 : ZMod 162249361) ^ 2475 = (31 : ZMod 162249361) ^ (1237 + 1237 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 1237 * (31 : ZMod 162249361) ^ 1237) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 94042957 := by rw [factor_0_10]; decide
      have factor_0_12 : (31 : ZMod 162249361) ^ 4951 = 28538455 := by
        calc
          (31 : ZMod 162249361) ^ 4951 = (31 : ZMod 162249361) ^ (2475 + 2475 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 2475 * (31 : ZMod 162249361) ^ 2475) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 28538455 := by rw [factor_0_11]; decide
      have factor_0_13 : (31 : ZMod 162249361) ^ 9902 = 134125964 := by
        calc
          (31 : ZMod 162249361) ^ 9902 = (31 : ZMod 162249361) ^ (4951 + 4951) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 4951 * (31 : ZMod 162249361) ^ 4951 := by rw [pow_add]
          _ = 134125964 := by rw [factor_0_12]; decide
      have factor_0_14 : (31 : ZMod 162249361) ^ 19805 = 130627276 := by
        calc
          (31 : ZMod 162249361) ^ 19805 = (31 : ZMod 162249361) ^ (9902 + 9902 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 9902 * (31 : ZMod 162249361) ^ 9902) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 130627276 := by rw [factor_0_13]; decide
      have factor_0_15 : (31 : ZMod 162249361) ^ 39611 = 66422566 := by
        calc
          (31 : ZMod 162249361) ^ 39611 = (31 : ZMod 162249361) ^ (19805 + 19805 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 19805 * (31 : ZMod 162249361) ^ 19805) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 66422566 := by rw [factor_0_14]; decide
      have factor_0_16 : (31 : ZMod 162249361) ^ 79223 = 119952356 := by
        calc
          (31 : ZMod 162249361) ^ 79223 = (31 : ZMod 162249361) ^ (39611 + 39611 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 39611 * (31 : ZMod 162249361) ^ 39611) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 119952356 := by rw [factor_0_15]; decide
      have factor_0_17 : (31 : ZMod 162249361) ^ 158446 = 56129882 := by
        calc
          (31 : ZMod 162249361) ^ 158446 = (31 : ZMod 162249361) ^ (79223 + 79223) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 79223 * (31 : ZMod 162249361) ^ 79223 := by rw [pow_add]
          _ = 56129882 := by rw [factor_0_16]; decide
      have factor_0_18 : (31 : ZMod 162249361) ^ 316893 = 95692262 := by
        calc
          (31 : ZMod 162249361) ^ 316893 = (31 : ZMod 162249361) ^ (158446 + 158446 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 158446 * (31 : ZMod 162249361) ^ 158446) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 95692262 := by rw [factor_0_17]; decide
      have factor_0_19 : (31 : ZMod 162249361) ^ 633786 = 13978130 := by
        calc
          (31 : ZMod 162249361) ^ 633786 = (31 : ZMod 162249361) ^ (316893 + 316893) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 316893 * (31 : ZMod 162249361) ^ 316893 := by rw [pow_add]
          _ = 13978130 := by rw [factor_0_18]; decide
      have factor_0_20 : (31 : ZMod 162249361) ^ 1267573 = 14859719 := by
        calc
          (31 : ZMod 162249361) ^ 1267573 = (31 : ZMod 162249361) ^ (633786 + 633786 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 633786 * (31 : ZMod 162249361) ^ 633786) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 14859719 := by rw [factor_0_19]; decide
      have factor_0_21 : (31 : ZMod 162249361) ^ 2535146 = 90147704 := by
        calc
          (31 : ZMod 162249361) ^ 2535146 = (31 : ZMod 162249361) ^ (1267573 + 1267573) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 1267573 * (31 : ZMod 162249361) ^ 1267573 := by rw [pow_add]
          _ = 90147704 := by rw [factor_0_20]; decide
      have factor_0_22 : (31 : ZMod 162249361) ^ 5070292 = 130161744 := by
        calc
          (31 : ZMod 162249361) ^ 5070292 = (31 : ZMod 162249361) ^ (2535146 + 2535146) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 2535146 * (31 : ZMod 162249361) ^ 2535146 := by rw [pow_add]
          _ = 130161744 := by rw [factor_0_21]; decide
      have factor_0_23 : (31 : ZMod 162249361) ^ 10140585 = 41459283 := by
        calc
          (31 : ZMod 162249361) ^ 10140585 = (31 : ZMod 162249361) ^ (5070292 + 5070292 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 5070292 * (31 : ZMod 162249361) ^ 5070292) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 41459283 := by rw [factor_0_22]; decide
      have factor_0_24 : (31 : ZMod 162249361) ^ 20281170 = 144949035 := by
        calc
          (31 : ZMod 162249361) ^ 20281170 = (31 : ZMod 162249361) ^ (10140585 + 10140585) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 10140585 * (31 : ZMod 162249361) ^ 10140585 := by rw [pow_add]
          _ = 144949035 := by rw [factor_0_23]; decide
      have factor_0_25 : (31 : ZMod 162249361) ^ 40562340 = 45718937 := by
        calc
          (31 : ZMod 162249361) ^ 40562340 = (31 : ZMod 162249361) ^ (20281170 + 20281170) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 20281170 * (31 : ZMod 162249361) ^ 20281170 := by rw [pow_add]
          _ = 45718937 := by rw [factor_0_24]; decide
      have factor_0_26 : (31 : ZMod 162249361) ^ 81124680 = 162249360 := by
        calc
          (31 : ZMod 162249361) ^ 81124680 = (31 : ZMod 162249361) ^ (40562340 + 40562340) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 40562340 * (31 : ZMod 162249361) ^ 40562340 := by rw [pow_add]
          _ = 162249360 := by rw [factor_0_25]; decide
      change (31 : ZMod 162249361) ^ 81124680 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (31 : ZMod 162249361) ^ 1 = 31 := by norm_num
      have factor_1_1 : (31 : ZMod 162249361) ^ 3 = 29791 := by
        calc
          (31 : ZMod 162249361) ^ 3 = (31 : ZMod 162249361) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 1 * (31 : ZMod 162249361) ^ 1) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 29791 := by rw [factor_1_0]; decide
      have factor_1_2 : (31 : ZMod 162249361) ^ 6 = 76256876 := by
        calc
          (31 : ZMod 162249361) ^ 6 = (31 : ZMod 162249361) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 3 * (31 : ZMod 162249361) ^ 3 := by rw [pow_add]
          _ = 76256876 := by rw [factor_1_1]; decide
      have factor_1_3 : (31 : ZMod 162249361) ^ 12 = 96659357 := by
        calc
          (31 : ZMod 162249361) ^ 12 = (31 : ZMod 162249361) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 6 * (31 : ZMod 162249361) ^ 6 := by rw [pow_add]
          _ = 96659357 := by rw [factor_1_2]; decide
      have factor_1_4 : (31 : ZMod 162249361) ^ 25 = 103287474 := by
        calc
          (31 : ZMod 162249361) ^ 25 = (31 : ZMod 162249361) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 12 * (31 : ZMod 162249361) ^ 12) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 103287474 := by rw [factor_1_3]; decide
      have factor_1_5 : (31 : ZMod 162249361) ^ 51 = 116736592 := by
        calc
          (31 : ZMod 162249361) ^ 51 = (31 : ZMod 162249361) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 25 * (31 : ZMod 162249361) ^ 25) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 116736592 := by rw [factor_1_4]; decide
      have factor_1_6 : (31 : ZMod 162249361) ^ 103 = 73613734 := by
        calc
          (31 : ZMod 162249361) ^ 103 = (31 : ZMod 162249361) ^ (51 + 51 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 51 * (31 : ZMod 162249361) ^ 51) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 73613734 := by rw [factor_1_5]; decide
      have factor_1_7 : (31 : ZMod 162249361) ^ 206 = 11694461 := by
        calc
          (31 : ZMod 162249361) ^ 206 = (31 : ZMod 162249361) ^ (103 + 103) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 103 * (31 : ZMod 162249361) ^ 103 := by rw [pow_add]
          _ = 11694461 := by rw [factor_1_6]; decide
      have factor_1_8 : (31 : ZMod 162249361) ^ 412 = 107194899 := by
        calc
          (31 : ZMod 162249361) ^ 412 = (31 : ZMod 162249361) ^ (206 + 206) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 206 * (31 : ZMod 162249361) ^ 206 := by rw [pow_add]
          _ = 107194899 := by rw [factor_1_7]; decide
      have factor_1_9 : (31 : ZMod 162249361) ^ 825 = 41466550 := by
        calc
          (31 : ZMod 162249361) ^ 825 = (31 : ZMod 162249361) ^ (412 + 412 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 412 * (31 : ZMod 162249361) ^ 412) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 41466550 := by rw [factor_1_8]; decide
      have factor_1_10 : (31 : ZMod 162249361) ^ 1650 = 10601331 := by
        calc
          (31 : ZMod 162249361) ^ 1650 = (31 : ZMod 162249361) ^ (825 + 825) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 825 * (31 : ZMod 162249361) ^ 825 := by rw [pow_add]
          _ = 10601331 := by rw [factor_1_9]; decide
      have factor_1_11 : (31 : ZMod 162249361) ^ 3300 = 33599193 := by
        calc
          (31 : ZMod 162249361) ^ 3300 = (31 : ZMod 162249361) ^ (1650 + 1650) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 1650 * (31 : ZMod 162249361) ^ 1650 := by rw [pow_add]
          _ = 33599193 := by rw [factor_1_10]; decide
      have factor_1_12 : (31 : ZMod 162249361) ^ 6601 = 35473710 := by
        calc
          (31 : ZMod 162249361) ^ 6601 = (31 : ZMod 162249361) ^ (3300 + 3300 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 3300 * (31 : ZMod 162249361) ^ 3300) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 35473710 := by rw [factor_1_11]; decide
      have factor_1_13 : (31 : ZMod 162249361) ^ 13203 = 86261773 := by
        calc
          (31 : ZMod 162249361) ^ 13203 = (31 : ZMod 162249361) ^ (6601 + 6601 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 6601 * (31 : ZMod 162249361) ^ 6601) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 86261773 := by rw [factor_1_12]; decide
      have factor_1_14 : (31 : ZMod 162249361) ^ 26407 = 105689181 := by
        calc
          (31 : ZMod 162249361) ^ 26407 = (31 : ZMod 162249361) ^ (13203 + 13203 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 13203 * (31 : ZMod 162249361) ^ 13203) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 105689181 := by rw [factor_1_13]; decide
      have factor_1_15 : (31 : ZMod 162249361) ^ 52815 = 47869629 := by
        calc
          (31 : ZMod 162249361) ^ 52815 = (31 : ZMod 162249361) ^ (26407 + 26407 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 26407 * (31 : ZMod 162249361) ^ 26407) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 47869629 := by rw [factor_1_14]; decide
      have factor_1_16 : (31 : ZMod 162249361) ^ 105631 = 92834260 := by
        calc
          (31 : ZMod 162249361) ^ 105631 = (31 : ZMod 162249361) ^ (52815 + 52815 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 52815 * (31 : ZMod 162249361) ^ 52815) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 92834260 := by rw [factor_1_15]; decide
      have factor_1_17 : (31 : ZMod 162249361) ^ 211262 = 34762517 := by
        calc
          (31 : ZMod 162249361) ^ 211262 = (31 : ZMod 162249361) ^ (105631 + 105631) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 105631 * (31 : ZMod 162249361) ^ 105631 := by rw [pow_add]
          _ = 34762517 := by rw [factor_1_16]; decide
      have factor_1_18 : (31 : ZMod 162249361) ^ 422524 = 158694094 := by
        calc
          (31 : ZMod 162249361) ^ 422524 = (31 : ZMod 162249361) ^ (211262 + 211262) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 211262 * (31 : ZMod 162249361) ^ 211262 := by rw [pow_add]
          _ = 158694094 := by rw [factor_1_17]; decide
      have factor_1_19 : (31 : ZMod 162249361) ^ 845048 = 49221945 := by
        calc
          (31 : ZMod 162249361) ^ 845048 = (31 : ZMod 162249361) ^ (422524 + 422524) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 422524 * (31 : ZMod 162249361) ^ 422524 := by rw [pow_add]
          _ = 49221945 := by rw [factor_1_18]; decide
      have factor_1_20 : (31 : ZMod 162249361) ^ 1690097 = 70343959 := by
        calc
          (31 : ZMod 162249361) ^ 1690097 = (31 : ZMod 162249361) ^ (845048 + 845048 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 845048 * (31 : ZMod 162249361) ^ 845048) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 70343959 := by rw [factor_1_19]; decide
      have factor_1_21 : (31 : ZMod 162249361) ^ 3380195 = 106954765 := by
        calc
          (31 : ZMod 162249361) ^ 3380195 = (31 : ZMod 162249361) ^ (1690097 + 1690097 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 1690097 * (31 : ZMod 162249361) ^ 1690097) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 106954765 := by rw [factor_1_20]; decide
      have factor_1_22 : (31 : ZMod 162249361) ^ 6760390 = 1626733 := by
        calc
          (31 : ZMod 162249361) ^ 6760390 = (31 : ZMod 162249361) ^ (3380195 + 3380195) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 3380195 * (31 : ZMod 162249361) ^ 3380195 := by rw [pow_add]
          _ = 1626733 := by rw [factor_1_21]; decide
      have factor_1_23 : (31 : ZMod 162249361) ^ 13520780 = 135424740 := by
        calc
          (31 : ZMod 162249361) ^ 13520780 = (31 : ZMod 162249361) ^ (6760390 + 6760390) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 6760390 * (31 : ZMod 162249361) ^ 6760390 := by rw [pow_add]
          _ = 135424740 := by rw [factor_1_22]; decide
      have factor_1_24 : (31 : ZMod 162249361) ^ 27041560 = 113946658 := by
        calc
          (31 : ZMod 162249361) ^ 27041560 = (31 : ZMod 162249361) ^ (13520780 + 13520780) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 13520780 * (31 : ZMod 162249361) ^ 13520780 := by rw [pow_add]
          _ = 113946658 := by rw [factor_1_23]; decide
      have factor_1_25 : (31 : ZMod 162249361) ^ 54083120 = 113946657 := by
        calc
          (31 : ZMod 162249361) ^ 54083120 = (31 : ZMod 162249361) ^ (27041560 + 27041560) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 27041560 * (31 : ZMod 162249361) ^ 27041560 := by rw [pow_add]
          _ = 113946657 := by rw [factor_1_24]; decide
      change (31 : ZMod 162249361) ^ 54083120 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (31 : ZMod 162249361) ^ 1 = 31 := by norm_num
      have factor_2_1 : (31 : ZMod 162249361) ^ 3 = 29791 := by
        calc
          (31 : ZMod 162249361) ^ 3 = (31 : ZMod 162249361) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 1 * (31 : ZMod 162249361) ^ 1) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 29791 := by rw [factor_2_0]; decide
      have factor_2_2 : (31 : ZMod 162249361) ^ 7 = 92472102 := by
        calc
          (31 : ZMod 162249361) ^ 7 = (31 : ZMod 162249361) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 3 * (31 : ZMod 162249361) ^ 3) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 92472102 := by rw [factor_2_1]; decide
      have factor_2_3 : (31 : ZMod 162249361) ^ 15 = 139494720 := by
        calc
          (31 : ZMod 162249361) ^ 15 = (31 : ZMod 162249361) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 7 * (31 : ZMod 162249361) ^ 7) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 139494720 := by rw [factor_2_2]; decide
      have factor_2_4 : (31 : ZMod 162249361) ^ 30 = 118979100 := by
        calc
          (31 : ZMod 162249361) ^ 30 = (31 : ZMod 162249361) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 15 * (31 : ZMod 162249361) ^ 15 := by rw [pow_add]
          _ = 118979100 := by rw [factor_2_3]; decide
      have factor_2_5 : (31 : ZMod 162249361) ^ 61 = 124966523 := by
        calc
          (31 : ZMod 162249361) ^ 61 = (31 : ZMod 162249361) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 30 * (31 : ZMod 162249361) ^ 30) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 124966523 := by rw [factor_2_4]; decide
      have factor_2_6 : (31 : ZMod 162249361) ^ 123 = 62973594 := by
        calc
          (31 : ZMod 162249361) ^ 123 = (31 : ZMod 162249361) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 61 * (31 : ZMod 162249361) ^ 61) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 62973594 := by rw [factor_2_5]; decide
      have factor_2_7 : (31 : ZMod 162249361) ^ 247 = 62565878 := by
        calc
          (31 : ZMod 162249361) ^ 247 = (31 : ZMod 162249361) ^ (123 + 123 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 123 * (31 : ZMod 162249361) ^ 123) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 62565878 := by rw [factor_2_6]; decide
      have factor_2_8 : (31 : ZMod 162249361) ^ 495 = 20619588 := by
        calc
          (31 : ZMod 162249361) ^ 495 = (31 : ZMod 162249361) ^ (247 + 247 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 247 * (31 : ZMod 162249361) ^ 247) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 20619588 := by rw [factor_2_7]; decide
      have factor_2_9 : (31 : ZMod 162249361) ^ 990 = 97761128 := by
        calc
          (31 : ZMod 162249361) ^ 990 = (31 : ZMod 162249361) ^ (495 + 495) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 495 * (31 : ZMod 162249361) ^ 495 := by rw [pow_add]
          _ = 97761128 := by rw [factor_2_8]; decide
      have factor_2_10 : (31 : ZMod 162249361) ^ 1980 = 57139037 := by
        calc
          (31 : ZMod 162249361) ^ 1980 = (31 : ZMod 162249361) ^ (990 + 990) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 990 * (31 : ZMod 162249361) ^ 990 := by rw [pow_add]
          _ = 57139037 := by rw [factor_2_9]; decide
      have factor_2_11 : (31 : ZMod 162249361) ^ 3961 = 146588444 := by
        calc
          (31 : ZMod 162249361) ^ 3961 = (31 : ZMod 162249361) ^ (1980 + 1980 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 1980 * (31 : ZMod 162249361) ^ 1980) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 146588444 := by rw [factor_2_10]; decide
      have factor_2_12 : (31 : ZMod 162249361) ^ 7922 = 74725239 := by
        calc
          (31 : ZMod 162249361) ^ 7922 = (31 : ZMod 162249361) ^ (3961 + 3961) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 3961 * (31 : ZMod 162249361) ^ 3961 := by rw [pow_add]
          _ = 74725239 := by rw [factor_2_11]; decide
      have factor_2_13 : (31 : ZMod 162249361) ^ 15844 = 98737016 := by
        calc
          (31 : ZMod 162249361) ^ 15844 = (31 : ZMod 162249361) ^ (7922 + 7922) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 7922 * (31 : ZMod 162249361) ^ 7922 := by rw [pow_add]
          _ = 98737016 := by rw [factor_2_12]; decide
      have factor_2_14 : (31 : ZMod 162249361) ^ 31689 = 2596675 := by
        calc
          (31 : ZMod 162249361) ^ 31689 = (31 : ZMod 162249361) ^ (15844 + 15844 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 15844 * (31 : ZMod 162249361) ^ 15844) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 2596675 := by rw [factor_2_13]; decide
      have factor_2_15 : (31 : ZMod 162249361) ^ 63378 = 124360548 := by
        calc
          (31 : ZMod 162249361) ^ 63378 = (31 : ZMod 162249361) ^ (31689 + 31689) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 31689 * (31 : ZMod 162249361) ^ 31689 := by rw [pow_add]
          _ = 124360548 := by rw [factor_2_14]; decide
      have factor_2_16 : (31 : ZMod 162249361) ^ 126757 = 57334138 := by
        calc
          (31 : ZMod 162249361) ^ 126757 = (31 : ZMod 162249361) ^ (63378 + 63378 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 63378 * (31 : ZMod 162249361) ^ 63378) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 57334138 := by rw [factor_2_15]; decide
      have factor_2_17 : (31 : ZMod 162249361) ^ 253514 = 12216371 := by
        calc
          (31 : ZMod 162249361) ^ 253514 = (31 : ZMod 162249361) ^ (126757 + 126757) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 126757 * (31 : ZMod 162249361) ^ 126757 := by rw [pow_add]
          _ = 12216371 := by rw [factor_2_16]; decide
      have factor_2_18 : (31 : ZMod 162249361) ^ 507029 = 159853185 := by
        calc
          (31 : ZMod 162249361) ^ 507029 = (31 : ZMod 162249361) ^ (253514 + 253514 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 253514 * (31 : ZMod 162249361) ^ 253514) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 159853185 := by rw [factor_2_17]; decide
      have factor_2_19 : (31 : ZMod 162249361) ^ 1014058 = 141285269 := by
        calc
          (31 : ZMod 162249361) ^ 1014058 = (31 : ZMod 162249361) ^ (507029 + 507029) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 507029 * (31 : ZMod 162249361) ^ 507029 := by rw [pow_add]
          _ = 141285269 := by rw [factor_2_18]; decide
      have factor_2_20 : (31 : ZMod 162249361) ^ 2028117 = 96820777 := by
        calc
          (31 : ZMod 162249361) ^ 2028117 = (31 : ZMod 162249361) ^ (1014058 + 1014058 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 1014058 * (31 : ZMod 162249361) ^ 1014058) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 96820777 := by rw [factor_2_19]; decide
      have factor_2_21 : (31 : ZMod 162249361) ^ 4056234 = 24813883 := by
        calc
          (31 : ZMod 162249361) ^ 4056234 = (31 : ZMod 162249361) ^ (2028117 + 2028117) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 2028117 * (31 : ZMod 162249361) ^ 2028117 := by rw [pow_add]
          _ = 24813883 := by rw [factor_2_20]; decide
      have factor_2_22 : (31 : ZMod 162249361) ^ 8112468 = 90262656 := by
        calc
          (31 : ZMod 162249361) ^ 8112468 = (31 : ZMod 162249361) ^ (4056234 + 4056234) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 4056234 * (31 : ZMod 162249361) ^ 4056234 := by rw [pow_add]
          _ = 90262656 := by rw [factor_2_21]; decide
      have factor_2_23 : (31 : ZMod 162249361) ^ 16224936 = 110790805 := by
        calc
          (31 : ZMod 162249361) ^ 16224936 = (31 : ZMod 162249361) ^ (8112468 + 8112468) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 8112468 * (31 : ZMod 162249361) ^ 8112468 := by rw [pow_add]
          _ = 110790805 := by rw [factor_2_22]; decide
      have factor_2_24 : (31 : ZMod 162249361) ^ 32449872 = 77373964 := by
        calc
          (31 : ZMod 162249361) ^ 32449872 = (31 : ZMod 162249361) ^ (16224936 + 16224936) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 16224936 * (31 : ZMod 162249361) ^ 16224936 := by rw [pow_add]
          _ = 77373964 := by rw [factor_2_23]; decide
      change (31 : ZMod 162249361) ^ 32449872 ≠ 1
      rw [factor_2_24]
      decide
    ·
      have factor_3_0 : (31 : ZMod 162249361) ^ 1 = 31 := by norm_num
      have factor_3_1 : (31 : ZMod 162249361) ^ 2 = 961 := by
        calc
          (31 : ZMod 162249361) ^ 2 = (31 : ZMod 162249361) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 1 * (31 : ZMod 162249361) ^ 1 := by rw [pow_add]
          _ = 961 := by rw [factor_3_0]; decide
      have factor_3_2 : (31 : ZMod 162249361) ^ 5 = 28629151 := by
        calc
          (31 : ZMod 162249361) ^ 5 = (31 : ZMod 162249361) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 2 * (31 : ZMod 162249361) ^ 2) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 28629151 := by rw [factor_3_1]; decide
      have factor_3_3 : (31 : ZMod 162249361) ^ 11 = 139198153 := by
        calc
          (31 : ZMod 162249361) ^ 11 = (31 : ZMod 162249361) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 5 * (31 : ZMod 162249361) ^ 5) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 139198153 := by rw [factor_3_2]; decide
      have factor_3_4 : (31 : ZMod 162249361) ^ 22 = 132200397 := by
        calc
          (31 : ZMod 162249361) ^ 22 = (31 : ZMod 162249361) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 11 * (31 : ZMod 162249361) ^ 11 := by rw [pow_add]
          _ = 132200397 := by rw [factor_3_3]; decide
      have factor_3_5 : (31 : ZMod 162249361) ^ 44 = 153096478 := by
        calc
          (31 : ZMod 162249361) ^ 44 = (31 : ZMod 162249361) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 22 * (31 : ZMod 162249361) ^ 22 := by rw [pow_add]
          _ = 153096478 := by rw [factor_3_4]; decide
      have factor_3_6 : (31 : ZMod 162249361) ^ 88 = 81150393 := by
        calc
          (31 : ZMod 162249361) ^ 88 = (31 : ZMod 162249361) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 44 * (31 : ZMod 162249361) ^ 44 := by rw [pow_add]
          _ = 81150393 := by rw [factor_3_5]; decide
      have factor_3_7 : (31 : ZMod 162249361) ^ 176 = 133822233 := by
        calc
          (31 : ZMod 162249361) ^ 176 = (31 : ZMod 162249361) ^ (88 + 88) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 88 * (31 : ZMod 162249361) ^ 88 := by rw [pow_add]
          _ = 133822233 := by rw [factor_3_6]; decide
      have factor_3_8 : (31 : ZMod 162249361) ^ 353 = 160932439 := by
        calc
          (31 : ZMod 162249361) ^ 353 = (31 : ZMod 162249361) ^ (176 + 176 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 176 * (31 : ZMod 162249361) ^ 176) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 160932439 := by rw [factor_3_7]; decide
      have factor_3_9 : (31 : ZMod 162249361) ^ 707 = 4165005 := by
        calc
          (31 : ZMod 162249361) ^ 707 = (31 : ZMod 162249361) ^ (353 + 353 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 353 * (31 : ZMod 162249361) ^ 353) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 4165005 := by rw [factor_3_8]; decide
      have factor_3_10 : (31 : ZMod 162249361) ^ 1414 = 51719988 := by
        calc
          (31 : ZMod 162249361) ^ 1414 = (31 : ZMod 162249361) ^ (707 + 707) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 707 * (31 : ZMod 162249361) ^ 707 := by rw [pow_add]
          _ = 51719988 := by rw [factor_3_9]; decide
      have factor_3_11 : (31 : ZMod 162249361) ^ 2829 = 34940166 := by
        calc
          (31 : ZMod 162249361) ^ 2829 = (31 : ZMod 162249361) ^ (1414 + 1414 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 1414 * (31 : ZMod 162249361) ^ 1414) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 34940166 := by rw [factor_3_10]; decide
      have factor_3_12 : (31 : ZMod 162249361) ^ 5658 = 61644202 := by
        calc
          (31 : ZMod 162249361) ^ 5658 = (31 : ZMod 162249361) ^ (2829 + 2829) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 2829 * (31 : ZMod 162249361) ^ 2829 := by rw [pow_add]
          _ = 61644202 := by rw [factor_3_11]; decide
      have factor_3_13 : (31 : ZMod 162249361) ^ 11317 = 134079744 := by
        calc
          (31 : ZMod 162249361) ^ 11317 = (31 : ZMod 162249361) ^ (5658 + 5658 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 5658 * (31 : ZMod 162249361) ^ 5658) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 134079744 := by rw [factor_3_12]; decide
      have factor_3_14 : (31 : ZMod 162249361) ^ 22635 = 160107714 := by
        calc
          (31 : ZMod 162249361) ^ 22635 = (31 : ZMod 162249361) ^ (11317 + 11317 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 11317 * (31 : ZMod 162249361) ^ 11317) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 160107714 := by rw [factor_3_13]; decide
      have factor_3_15 : (31 : ZMod 162249361) ^ 45270 = 24686500 := by
        calc
          (31 : ZMod 162249361) ^ 45270 = (31 : ZMod 162249361) ^ (22635 + 22635) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 22635 * (31 : ZMod 162249361) ^ 22635 := by rw [pow_add]
          _ = 24686500 := by rw [factor_3_14]; decide
      have factor_3_16 : (31 : ZMod 162249361) ^ 90540 = 79891510 := by
        calc
          (31 : ZMod 162249361) ^ 90540 = (31 : ZMod 162249361) ^ (45270 + 45270) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 45270 * (31 : ZMod 162249361) ^ 45270 := by rw [pow_add]
          _ = 79891510 := by rw [factor_3_15]; decide
      have factor_3_17 : (31 : ZMod 162249361) ^ 181081 = 158169246 := by
        calc
          (31 : ZMod 162249361) ^ 181081 = (31 : ZMod 162249361) ^ (90540 + 90540 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 90540 * (31 : ZMod 162249361) ^ 90540) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 158169246 := by rw [factor_3_16]; decide
      have factor_3_18 : (31 : ZMod 162249361) ^ 362163 = 137030470 := by
        calc
          (31 : ZMod 162249361) ^ 362163 = (31 : ZMod 162249361) ^ (181081 + 181081 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 181081 * (31 : ZMod 162249361) ^ 181081) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 137030470 := by rw [factor_3_17]; decide
      have factor_3_19 : (31 : ZMod 162249361) ^ 724327 = 51339974 := by
        calc
          (31 : ZMod 162249361) ^ 724327 = (31 : ZMod 162249361) ^ (362163 + 362163 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 362163 * (31 : ZMod 162249361) ^ 362163) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 51339974 := by rw [factor_3_18]; decide
      have factor_3_20 : (31 : ZMod 162249361) ^ 1448655 = 155001450 := by
        calc
          (31 : ZMod 162249361) ^ 1448655 = (31 : ZMod 162249361) ^ (724327 + 724327 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 724327 * (31 : ZMod 162249361) ^ 724327) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 155001450 := by rw [factor_3_19]; decide
      have factor_3_21 : (31 : ZMod 162249361) ^ 2897310 = 89255507 := by
        calc
          (31 : ZMod 162249361) ^ 2897310 = (31 : ZMod 162249361) ^ (1448655 + 1448655) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 1448655 * (31 : ZMod 162249361) ^ 1448655 := by rw [pow_add]
          _ = 89255507 := by rw [factor_3_20]; decide
      have factor_3_22 : (31 : ZMod 162249361) ^ 5794620 = 12128341 := by
        calc
          (31 : ZMod 162249361) ^ 5794620 = (31 : ZMod 162249361) ^ (2897310 + 2897310) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 2897310 * (31 : ZMod 162249361) ^ 2897310 := by rw [pow_add]
          _ = 12128341 := by rw [factor_3_21]; decide
      have factor_3_23 : (31 : ZMod 162249361) ^ 11589240 = 86734793 := by
        calc
          (31 : ZMod 162249361) ^ 11589240 = (31 : ZMod 162249361) ^ (5794620 + 5794620) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 5794620 * (31 : ZMod 162249361) ^ 5794620 := by rw [pow_add]
          _ = 86734793 := by rw [factor_3_22]; decide
      have factor_3_24 : (31 : ZMod 162249361) ^ 23178480 = 28404175 := by
        calc
          (31 : ZMod 162249361) ^ 23178480 = (31 : ZMod 162249361) ^ (11589240 + 11589240) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 11589240 * (31 : ZMod 162249361) ^ 11589240 := by rw [pow_add]
          _ = 28404175 := by rw [factor_3_23]; decide
      change (31 : ZMod 162249361) ^ 23178480 ≠ 1
      rw [factor_3_24]
      decide
    ·
      have factor_4_0 : (31 : ZMod 162249361) ^ 1 = 31 := by norm_num
      have factor_4_1 : (31 : ZMod 162249361) ^ 2 = 961 := by
        calc
          (31 : ZMod 162249361) ^ 2 = (31 : ZMod 162249361) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 1 * (31 : ZMod 162249361) ^ 1 := by rw [pow_add]
          _ = 961 := by rw [factor_4_0]; decide
      have factor_4_2 : (31 : ZMod 162249361) ^ 5 = 28629151 := by
        calc
          (31 : ZMod 162249361) ^ 5 = (31 : ZMod 162249361) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 2 * (31 : ZMod 162249361) ^ 2) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 28629151 := by rw [factor_4_1]; decide
      have factor_4_3 : (31 : ZMod 162249361) ^ 11 = 139198153 := by
        calc
          (31 : ZMod 162249361) ^ 11 = (31 : ZMod 162249361) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 5 * (31 : ZMod 162249361) ^ 5) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 139198153 := by rw [factor_4_2]; decide
      have factor_4_4 : (31 : ZMod 162249361) ^ 23 = 41978282 := by
        calc
          (31 : ZMod 162249361) ^ 23 = (31 : ZMod 162249361) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 11 * (31 : ZMod 162249361) ^ 11) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 41978282 := by rw [factor_4_3]; decide
      have factor_4_5 : (31 : ZMod 162249361) ^ 47 = 67638388 := by
        calc
          (31 : ZMod 162249361) ^ 47 = (31 : ZMod 162249361) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 23 * (31 : ZMod 162249361) ^ 23) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 67638388 := by rw [factor_4_4]; decide
      have factor_4_6 : (31 : ZMod 162249361) ^ 95 = 86786581 := by
        calc
          (31 : ZMod 162249361) ^ 95 = (31 : ZMod 162249361) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 47 * (31 : ZMod 162249361) ^ 47) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 86786581 := by rw [factor_4_5]; decide
      have factor_4_7 : (31 : ZMod 162249361) ^ 190 = 10212541 := by
        calc
          (31 : ZMod 162249361) ^ 190 = (31 : ZMod 162249361) ^ (95 + 95) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 95 * (31 : ZMod 162249361) ^ 95 := by rw [pow_add]
          _ = 10212541 := by rw [factor_4_6]; decide
      have factor_4_8 : (31 : ZMod 162249361) ^ 380 = 157433549 := by
        calc
          (31 : ZMod 162249361) ^ 380 = (31 : ZMod 162249361) ^ (190 + 190) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 190 * (31 : ZMod 162249361) ^ 190 := by rw [pow_add]
          _ = 157433549 := by rw [factor_4_7]; decide
      have factor_4_9 : (31 : ZMod 162249361) ^ 761 = 36562821 := by
        calc
          (31 : ZMod 162249361) ^ 761 = (31 : ZMod 162249361) ^ (380 + 380 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 380 * (31 : ZMod 162249361) ^ 380) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 36562821 := by rw [factor_4_8]; decide
      have factor_4_10 : (31 : ZMod 162249361) ^ 1523 = 97398035 := by
        calc
          (31 : ZMod 162249361) ^ 1523 = (31 : ZMod 162249361) ^ (761 + 761 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 761 * (31 : ZMod 162249361) ^ 761) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 97398035 := by rw [factor_4_9]; decide
      have factor_4_11 : (31 : ZMod 162249361) ^ 3047 = 25811334 := by
        calc
          (31 : ZMod 162249361) ^ 3047 = (31 : ZMod 162249361) ^ (1523 + 1523 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 1523 * (31 : ZMod 162249361) ^ 1523) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 25811334 := by rw [factor_4_10]; decide
      have factor_4_12 : (31 : ZMod 162249361) ^ 6094 = 43957937 := by
        calc
          (31 : ZMod 162249361) ^ 6094 = (31 : ZMod 162249361) ^ (3047 + 3047) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 3047 * (31 : ZMod 162249361) ^ 3047 := by rw [pow_add]
          _ = 43957937 := by rw [factor_4_11]; decide
      have factor_4_13 : (31 : ZMod 162249361) ^ 12188 = 59682602 := by
        calc
          (31 : ZMod 162249361) ^ 12188 = (31 : ZMod 162249361) ^ (6094 + 6094) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 6094 * (31 : ZMod 162249361) ^ 6094 := by rw [pow_add]
          _ = 59682602 := by rw [factor_4_12]; decide
      have factor_4_14 : (31 : ZMod 162249361) ^ 24376 = 82808703 := by
        calc
          (31 : ZMod 162249361) ^ 24376 = (31 : ZMod 162249361) ^ (12188 + 12188) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 12188 * (31 : ZMod 162249361) ^ 12188 := by rw [pow_add]
          _ = 82808703 := by rw [factor_4_13]; decide
      have factor_4_15 : (31 : ZMod 162249361) ^ 48752 = 96886608 := by
        calc
          (31 : ZMod 162249361) ^ 48752 = (31 : ZMod 162249361) ^ (24376 + 24376) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 24376 * (31 : ZMod 162249361) ^ 24376 := by rw [pow_add]
          _ = 96886608 := by rw [factor_4_14]; decide
      have factor_4_16 : (31 : ZMod 162249361) ^ 97505 = 88336796 := by
        calc
          (31 : ZMod 162249361) ^ 97505 = (31 : ZMod 162249361) ^ (48752 + 48752 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 48752 * (31 : ZMod 162249361) ^ 48752) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 88336796 := by rw [factor_4_15]; decide
      have factor_4_17 : (31 : ZMod 162249361) ^ 195011 = 141813373 := by
        calc
          (31 : ZMod 162249361) ^ 195011 = (31 : ZMod 162249361) ^ (97505 + 97505 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 97505 * (31 : ZMod 162249361) ^ 97505) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 141813373 := by rw [factor_4_16]; decide
      have factor_4_18 : (31 : ZMod 162249361) ^ 390022 = 74820866 := by
        calc
          (31 : ZMod 162249361) ^ 390022 = (31 : ZMod 162249361) ^ (195011 + 195011) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 195011 * (31 : ZMod 162249361) ^ 195011 := by rw [pow_add]
          _ = 74820866 := by rw [factor_4_17]; decide
      have factor_4_19 : (31 : ZMod 162249361) ^ 780045 = 52690865 := by
        calc
          (31 : ZMod 162249361) ^ 780045 = (31 : ZMod 162249361) ^ (390022 + 390022 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 390022 * (31 : ZMod 162249361) ^ 390022) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 52690865 := by rw [factor_4_18]; decide
      have factor_4_20 : (31 : ZMod 162249361) ^ 1560090 = 71935862 := by
        calc
          (31 : ZMod 162249361) ^ 1560090 = (31 : ZMod 162249361) ^ (780045 + 780045) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 780045 * (31 : ZMod 162249361) ^ 780045 := by rw [pow_add]
          _ = 71935862 := by rw [factor_4_19]; decide
      have factor_4_21 : (31 : ZMod 162249361) ^ 3120180 = 101897924 := by
        calc
          (31 : ZMod 162249361) ^ 3120180 = (31 : ZMod 162249361) ^ (1560090 + 1560090) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 1560090 * (31 : ZMod 162249361) ^ 1560090 := by rw [pow_add]
          _ = 101897924 := by rw [factor_4_20]; decide
      have factor_4_22 : (31 : ZMod 162249361) ^ 6240360 = 118468136 := by
        calc
          (31 : ZMod 162249361) ^ 6240360 = (31 : ZMod 162249361) ^ (3120180 + 3120180) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 3120180 * (31 : ZMod 162249361) ^ 3120180 := by rw [pow_add]
          _ = 118468136 := by rw [factor_4_21]; decide
      have factor_4_23 : (31 : ZMod 162249361) ^ 12480720 = 45824418 := by
        calc
          (31 : ZMod 162249361) ^ 12480720 = (31 : ZMod 162249361) ^ (6240360 + 6240360) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 6240360 * (31 : ZMod 162249361) ^ 6240360 := by rw [pow_add]
          _ = 45824418 := by rw [factor_4_22]; decide
      change (31 : ZMod 162249361) ^ 12480720 ≠ 1
      rw [factor_4_23]
      decide
    ·
      have factor_5_0 : (31 : ZMod 162249361) ^ 1 = 31 := by norm_num
      have factor_5_1 : (31 : ZMod 162249361) ^ 2 = 961 := by
        calc
          (31 : ZMod 162249361) ^ 2 = (31 : ZMod 162249361) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 1 * (31 : ZMod 162249361) ^ 1 := by rw [pow_add]
          _ = 961 := by rw [factor_5_0]; decide
      have factor_5_2 : (31 : ZMod 162249361) ^ 4 = 923521 := by
        calc
          (31 : ZMod 162249361) ^ 4 = (31 : ZMod 162249361) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 2 * (31 : ZMod 162249361) ^ 2 := by rw [pow_add]
          _ = 923521 := by rw [factor_5_1]; decide
      have factor_5_3 : (31 : ZMod 162249361) ^ 9 = 115289555 := by
        calc
          (31 : ZMod 162249361) ^ 9 = (31 : ZMod 162249361) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 4 * (31 : ZMod 162249361) ^ 4) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 115289555 := by rw [factor_5_2]; decide
      have factor_5_4 : (31 : ZMod 162249361) ^ 18 = 156569588 := by
        calc
          (31 : ZMod 162249361) ^ 18 = (31 : ZMod 162249361) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 9 * (31 : ZMod 162249361) ^ 9 := by rw [pow_add]
          _ = 156569588 := by rw [factor_5_3]; decide
      have factor_5_5 : (31 : ZMod 162249361) ^ 36 = 105382621 := by
        calc
          (31 : ZMod 162249361) ^ 36 = (31 : ZMod 162249361) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 18 * (31 : ZMod 162249361) ^ 18 := by rw [pow_add]
          _ = 105382621 := by rw [factor_5_4]; decide
      have factor_5_6 : (31 : ZMod 162249361) ^ 72 = 31770790 := by
        calc
          (31 : ZMod 162249361) ^ 72 = (31 : ZMod 162249361) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 36 * (31 : ZMod 162249361) ^ 36 := by rw [pow_add]
          _ = 31770790 := by rw [factor_5_5]; decide
      have factor_5_7 : (31 : ZMod 162249361) ^ 145 = 161126483 := by
        calc
          (31 : ZMod 162249361) ^ 145 = (31 : ZMod 162249361) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 72 * (31 : ZMod 162249361) ^ 72) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 161126483 := by rw [factor_5_6]; decide
      have factor_5_8 : (31 : ZMod 162249361) ^ 291 = 147276421 := by
        calc
          (31 : ZMod 162249361) ^ 291 = (31 : ZMod 162249361) ^ (145 + 145 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 145 * (31 : ZMod 162249361) ^ 145) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 147276421 := by rw [factor_5_7]; decide
      have factor_5_9 : (31 : ZMod 162249361) ^ 582 = 66435045 := by
        calc
          (31 : ZMod 162249361) ^ 582 = (31 : ZMod 162249361) ^ (291 + 291) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 291 * (31 : ZMod 162249361) ^ 291 := by rw [pow_add]
          _ = 66435045 := by rw [factor_5_8]; decide
      have factor_5_10 : (31 : ZMod 162249361) ^ 1165 = 61576764 := by
        calc
          (31 : ZMod 162249361) ^ 1165 = (31 : ZMod 162249361) ^ (582 + 582 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 582 * (31 : ZMod 162249361) ^ 582) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 61576764 := by rw [factor_5_9]; decide
      have factor_5_11 : (31 : ZMod 162249361) ^ 2330 = 65366926 := by
        calc
          (31 : ZMod 162249361) ^ 2330 = (31 : ZMod 162249361) ^ (1165 + 1165) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 1165 * (31 : ZMod 162249361) ^ 1165 := by rw [pow_add]
          _ = 65366926 := by rw [factor_5_10]; decide
      have factor_5_12 : (31 : ZMod 162249361) ^ 4660 = 39746808 := by
        calc
          (31 : ZMod 162249361) ^ 4660 = (31 : ZMod 162249361) ^ (2330 + 2330) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 2330 * (31 : ZMod 162249361) ^ 2330 := by rw [pow_add]
          _ = 39746808 := by rw [factor_5_11]; decide
      have factor_5_13 : (31 : ZMod 162249361) ^ 9320 = 22579466 := by
        calc
          (31 : ZMod 162249361) ^ 9320 = (31 : ZMod 162249361) ^ (4660 + 4660) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 4660 * (31 : ZMod 162249361) ^ 4660 := by rw [pow_add]
          _ = 22579466 := by rw [factor_5_12]; decide
      have factor_5_14 : (31 : ZMod 162249361) ^ 18640 = 11759520 := by
        calc
          (31 : ZMod 162249361) ^ 18640 = (31 : ZMod 162249361) ^ (9320 + 9320) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 9320 * (31 : ZMod 162249361) ^ 9320 := by rw [pow_add]
          _ = 11759520 := by rw [factor_5_13]; decide
      have factor_5_15 : (31 : ZMod 162249361) ^ 37281 = 81646875 := by
        calc
          (31 : ZMod 162249361) ^ 37281 = (31 : ZMod 162249361) ^ (18640 + 18640 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 18640 * (31 : ZMod 162249361) ^ 18640) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 81646875 := by rw [factor_5_14]; decide
      have factor_5_16 : (31 : ZMod 162249361) ^ 74563 = 148824978 := by
        calc
          (31 : ZMod 162249361) ^ 74563 = (31 : ZMod 162249361) ^ (37281 + 37281 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 37281 * (31 : ZMod 162249361) ^ 37281) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 148824978 := by rw [factor_5_15]; decide
      have factor_5_17 : (31 : ZMod 162249361) ^ 149126 = 124182047 := by
        calc
          (31 : ZMod 162249361) ^ 149126 = (31 : ZMod 162249361) ^ (74563 + 74563) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 74563 * (31 : ZMod 162249361) ^ 74563 := by rw [pow_add]
          _ = 124182047 := by rw [factor_5_16]; decide
      have factor_5_18 : (31 : ZMod 162249361) ^ 298252 = 124614117 := by
        calc
          (31 : ZMod 162249361) ^ 298252 = (31 : ZMod 162249361) ^ (149126 + 149126) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 149126 * (31 : ZMod 162249361) ^ 149126 := by rw [pow_add]
          _ = 124614117 := by rw [factor_5_17]; decide
      have factor_5_19 : (31 : ZMod 162249361) ^ 596505 = 38602856 := by
        calc
          (31 : ZMod 162249361) ^ 596505 = (31 : ZMod 162249361) ^ (298252 + 298252 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 298252 * (31 : ZMod 162249361) ^ 298252) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 38602856 := by rw [factor_5_18]; decide
      have factor_5_20 : (31 : ZMod 162249361) ^ 1193010 = 99506709 := by
        calc
          (31 : ZMod 162249361) ^ 1193010 = (31 : ZMod 162249361) ^ (596505 + 596505) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 596505 * (31 : ZMod 162249361) ^ 596505 := by rw [pow_add]
          _ = 99506709 := by rw [factor_5_19]; decide
      have factor_5_21 : (31 : ZMod 162249361) ^ 2386020 = 34487482 := by
        calc
          (31 : ZMod 162249361) ^ 2386020 = (31 : ZMod 162249361) ^ (1193010 + 1193010) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 1193010 * (31 : ZMod 162249361) ^ 1193010 := by rw [pow_add]
          _ = 34487482 := by rw [factor_5_20]; decide
      have factor_5_22 : (31 : ZMod 162249361) ^ 4772040 = 113208197 := by
        calc
          (31 : ZMod 162249361) ^ 4772040 = (31 : ZMod 162249361) ^ (2386020 + 2386020) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 2386020 * (31 : ZMod 162249361) ^ 2386020 := by rw [pow_add]
          _ = 113208197 := by rw [factor_5_21]; decide
      have factor_5_23 : (31 : ZMod 162249361) ^ 9544080 = 21674933 := by
        calc
          (31 : ZMod 162249361) ^ 9544080 = (31 : ZMod 162249361) ^ (4772040 + 4772040) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 4772040 * (31 : ZMod 162249361) ^ 4772040 := by rw [pow_add]
          _ = 21674933 := by rw [factor_5_22]; decide
      change (31 : ZMod 162249361) ^ 9544080 ≠ 1
      rw [factor_5_23]
      decide
    ·
      have factor_6_0 : (31 : ZMod 162249361) ^ 1 = 31 := by norm_num
      have factor_6_1 : (31 : ZMod 162249361) ^ 2 = 961 := by
        calc
          (31 : ZMod 162249361) ^ 2 = (31 : ZMod 162249361) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 1 * (31 : ZMod 162249361) ^ 1 := by rw [pow_add]
          _ = 961 := by rw [factor_6_0]; decide
      have factor_6_2 : (31 : ZMod 162249361) ^ 4 = 923521 := by
        calc
          (31 : ZMod 162249361) ^ 4 = (31 : ZMod 162249361) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 2 * (31 : ZMod 162249361) ^ 2 := by rw [pow_add]
          _ = 923521 := by rw [factor_6_1]; decide
      have factor_6_3 : (31 : ZMod 162249361) ^ 8 = 108396025 := by
        calc
          (31 : ZMod 162249361) ^ 8 = (31 : ZMod 162249361) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 4 * (31 : ZMod 162249361) ^ 4 := by rw [pow_add]
          _ = 108396025 := by rw [factor_6_2]; decide
      have factor_6_4 : (31 : ZMod 162249361) ^ 16 = 105852934 := by
        calc
          (31 : ZMod 162249361) ^ 16 = (31 : ZMod 162249361) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 8 * (31 : ZMod 162249361) ^ 8 := by rw [pow_add]
          _ = 105852934 := by rw [factor_6_3]; decide
      have factor_6_5 : (31 : ZMod 162249361) ^ 32 = 115364956 := by
        calc
          (31 : ZMod 162249361) ^ 32 = (31 : ZMod 162249361) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 16 * (31 : ZMod 162249361) ^ 16 := by rw [pow_add]
          _ = 115364956 := by rw [factor_6_4]; decide
      have factor_6_6 : (31 : ZMod 162249361) ^ 65 = 102062656 := by
        calc
          (31 : ZMod 162249361) ^ 65 = (31 : ZMod 162249361) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 32 * (31 : ZMod 162249361) ^ 32) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 102062656 := by rw [factor_6_5]; decide
      have factor_6_7 : (31 : ZMod 162249361) ^ 130 = 30558094 := by
        calc
          (31 : ZMod 162249361) ^ 130 = (31 : ZMod 162249361) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 65 * (31 : ZMod 162249361) ^ 65 := by rw [pow_add]
          _ = 30558094 := by rw [factor_6_6]; decide
      have factor_6_8 : (31 : ZMod 162249361) ^ 260 = 116562316 := by
        calc
          (31 : ZMod 162249361) ^ 260 = (31 : ZMod 162249361) ^ (130 + 130) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 130 * (31 : ZMod 162249361) ^ 130 := by rw [pow_add]
          _ = 116562316 := by rw [factor_6_7]; decide
      have factor_6_9 : (31 : ZMod 162249361) ^ 521 = 130926680 := by
        calc
          (31 : ZMod 162249361) ^ 521 = (31 : ZMod 162249361) ^ (260 + 260 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 260 * (31 : ZMod 162249361) ^ 260) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 130926680 := by rw [factor_6_8]; decide
      have factor_6_10 : (31 : ZMod 162249361) ^ 1042 = 141014753 := by
        calc
          (31 : ZMod 162249361) ^ 1042 = (31 : ZMod 162249361) ^ (521 + 521) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 521 * (31 : ZMod 162249361) ^ 521 := by rw [pow_add]
          _ = 141014753 := by rw [factor_6_9]; decide
      have factor_6_11 : (31 : ZMod 162249361) ^ 2084 = 79763676 := by
        calc
          (31 : ZMod 162249361) ^ 2084 = (31 : ZMod 162249361) ^ (1042 + 1042) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 1042 * (31 : ZMod 162249361) ^ 1042 := by rw [pow_add]
          _ = 79763676 := by rw [factor_6_10]; decide
      have factor_6_12 : (31 : ZMod 162249361) ^ 4169 = 50933014 := by
        calc
          (31 : ZMod 162249361) ^ 4169 = (31 : ZMod 162249361) ^ (2084 + 2084 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 2084 * (31 : ZMod 162249361) ^ 2084) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 50933014 := by rw [factor_6_11]; decide
      have factor_6_13 : (31 : ZMod 162249361) ^ 8339 = 58907484 := by
        calc
          (31 : ZMod 162249361) ^ 8339 = (31 : ZMod 162249361) ^ (4169 + 4169 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 4169 * (31 : ZMod 162249361) ^ 4169) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 58907484 := by rw [factor_6_12]; decide
      have factor_6_14 : (31 : ZMod 162249361) ^ 16678 = 12257578 := by
        calc
          (31 : ZMod 162249361) ^ 16678 = (31 : ZMod 162249361) ^ (8339 + 8339) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 8339 * (31 : ZMod 162249361) ^ 8339 := by rw [pow_add]
          _ = 12257578 := by rw [factor_6_13]; decide
      have factor_6_15 : (31 : ZMod 162249361) ^ 33357 = 93490550 := by
        calc
          (31 : ZMod 162249361) ^ 33357 = (31 : ZMod 162249361) ^ (16678 + 16678 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 16678 * (31 : ZMod 162249361) ^ 16678) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 93490550 := by rw [factor_6_14]; decide
      have factor_6_16 : (31 : ZMod 162249361) ^ 66714 = 19415103 := by
        calc
          (31 : ZMod 162249361) ^ 66714 = (31 : ZMod 162249361) ^ (33357 + 33357) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 33357 * (31 : ZMod 162249361) ^ 33357 := by rw [pow_add]
          _ = 19415103 := by rw [factor_6_15]; decide
      have factor_6_17 : (31 : ZMod 162249361) ^ 133428 = 72058637 := by
        calc
          (31 : ZMod 162249361) ^ 133428 = (31 : ZMod 162249361) ^ (66714 + 66714) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 66714 * (31 : ZMod 162249361) ^ 66714 := by rw [pow_add]
          _ = 72058637 := by rw [factor_6_16]; decide
      have factor_6_18 : (31 : ZMod 162249361) ^ 266857 = 36321655 := by
        calc
          (31 : ZMod 162249361) ^ 266857 = (31 : ZMod 162249361) ^ (133428 + 133428 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 133428 * (31 : ZMod 162249361) ^ 133428) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 36321655 := by rw [factor_6_17]; decide
      have factor_6_19 : (31 : ZMod 162249361) ^ 533715 = 122683719 := by
        calc
          (31 : ZMod 162249361) ^ 533715 = (31 : ZMod 162249361) ^ (266857 + 266857 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 266857 * (31 : ZMod 162249361) ^ 266857) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 122683719 := by rw [factor_6_18]; decide
      have factor_6_20 : (31 : ZMod 162249361) ^ 1067430 = 106672926 := by
        calc
          (31 : ZMod 162249361) ^ 1067430 = (31 : ZMod 162249361) ^ (533715 + 533715) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 533715 * (31 : ZMod 162249361) ^ 533715 := by rw [pow_add]
          _ = 106672926 := by rw [factor_6_19]; decide
      have factor_6_21 : (31 : ZMod 162249361) ^ 2134860 = 15448391 := by
        calc
          (31 : ZMod 162249361) ^ 2134860 = (31 : ZMod 162249361) ^ (1067430 + 1067430) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 1067430 * (31 : ZMod 162249361) ^ 1067430 := by rw [pow_add]
          _ = 15448391 := by rw [factor_6_20]; decide
      have factor_6_22 : (31 : ZMod 162249361) ^ 4269720 = 37144620 := by
        calc
          (31 : ZMod 162249361) ^ 4269720 = (31 : ZMod 162249361) ^ (2134860 + 2134860) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 2134860 * (31 : ZMod 162249361) ^ 2134860 := by rw [pow_add]
          _ = 37144620 := by rw [factor_6_21]; decide
      have factor_6_23 : (31 : ZMod 162249361) ^ 8539440 = 145569563 := by
        calc
          (31 : ZMod 162249361) ^ 8539440 = (31 : ZMod 162249361) ^ (4269720 + 4269720) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 4269720 * (31 : ZMod 162249361) ^ 4269720 := by rw [pow_add]
          _ = 145569563 := by rw [factor_6_22]; decide
      change (31 : ZMod 162249361) ^ 8539440 ≠ 1
      rw [factor_6_23]
      decide
    ·
      have factor_7_0 : (31 : ZMod 162249361) ^ 1 = 31 := by norm_num
      have factor_7_1 : (31 : ZMod 162249361) ^ 3 = 29791 := by
        calc
          (31 : ZMod 162249361) ^ 3 = (31 : ZMod 162249361) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 1 * (31 : ZMod 162249361) ^ 1) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 29791 := by rw [factor_7_0]; decide
      have factor_7_2 : (31 : ZMod 162249361) ^ 6 = 76256876 := by
        calc
          (31 : ZMod 162249361) ^ 6 = (31 : ZMod 162249361) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 3 * (31 : ZMod 162249361) ^ 3 := by rw [pow_add]
          _ = 76256876 := by rw [factor_7_1]; decide
      have factor_7_3 : (31 : ZMod 162249361) ^ 13 = 75951569 := by
        calc
          (31 : ZMod 162249361) ^ 13 = (31 : ZMod 162249361) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 6 * (31 : ZMod 162249361) ^ 6) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 75951569 := by rw [factor_7_2]; decide
      have factor_7_4 : (31 : ZMod 162249361) ^ 26 = 119173835 := by
        calc
          (31 : ZMod 162249361) ^ 26 = (31 : ZMod 162249361) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 13 * (31 : ZMod 162249361) ^ 13 := by rw [pow_add]
          _ = 119173835 := by rw [factor_7_3]; decide
      have factor_7_5 : (31 : ZMod 162249361) ^ 53 = 69556461 := by
        calc
          (31 : ZMod 162249361) ^ 53 = (31 : ZMod 162249361) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 26 * (31 : ZMod 162249361) ^ 26) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 69556461 := by rw [factor_7_4]; decide
      have factor_7_6 : (31 : ZMod 162249361) ^ 107 = 48983526 := by
        calc
          (31 : ZMod 162249361) ^ 107 = (31 : ZMod 162249361) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 53 * (31 : ZMod 162249361) ^ 53) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 48983526 := by rw [factor_7_5]; decide
      have factor_7_7 : (31 : ZMod 162249361) ^ 215 = 10825520 := by
        calc
          (31 : ZMod 162249361) ^ 215 = (31 : ZMod 162249361) ^ (107 + 107 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 107 * (31 : ZMod 162249361) ^ 107) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 10825520 := by rw [factor_7_6]; decide
      have factor_7_8 : (31 : ZMod 162249361) ^ 430 = 143316266 := by
        calc
          (31 : ZMod 162249361) ^ 430 = (31 : ZMod 162249361) ^ (215 + 215) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 215 * (31 : ZMod 162249361) ^ 215 := by rw [pow_add]
          _ = 143316266 := by rw [factor_7_7]; decide
      have factor_7_9 : (31 : ZMod 162249361) ^ 861 = 119981322 := by
        calc
          (31 : ZMod 162249361) ^ 861 = (31 : ZMod 162249361) ^ (430 + 430 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 430 * (31 : ZMod 162249361) ^ 430) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 119981322 := by rw [factor_7_8]; decide
      have factor_7_10 : (31 : ZMod 162249361) ^ 1722 = 23668395 := by
        calc
          (31 : ZMod 162249361) ^ 1722 = (31 : ZMod 162249361) ^ (861 + 861) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 861 * (31 : ZMod 162249361) ^ 861 := by rw [pow_add]
          _ = 23668395 := by rw [factor_7_9]; decide
      have factor_7_11 : (31 : ZMod 162249361) ^ 3444 = 69629599 := by
        calc
          (31 : ZMod 162249361) ^ 3444 = (31 : ZMod 162249361) ^ (1722 + 1722) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 1722 * (31 : ZMod 162249361) ^ 1722 := by rw [pow_add]
          _ = 69629599 := by rw [factor_7_10]; decide
      have factor_7_12 : (31 : ZMod 162249361) ^ 6888 = 5034736 := by
        calc
          (31 : ZMod 162249361) ^ 6888 = (31 : ZMod 162249361) ^ (3444 + 3444) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 3444 * (31 : ZMod 162249361) ^ 3444 := by rw [pow_add]
          _ = 5034736 := by rw [factor_7_11]; decide
      have factor_7_13 : (31 : ZMod 162249361) ^ 13777 = 108082820 := by
        calc
          (31 : ZMod 162249361) ^ 13777 = (31 : ZMod 162249361) ^ (6888 + 6888 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 6888 * (31 : ZMod 162249361) ^ 6888) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 108082820 := by rw [factor_7_12]; decide
      have factor_7_14 : (31 : ZMod 162249361) ^ 27555 = 135891085 := by
        calc
          (31 : ZMod 162249361) ^ 27555 = (31 : ZMod 162249361) ^ (13777 + 13777 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 13777 * (31 : ZMod 162249361) ^ 13777) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 135891085 := by rw [factor_7_13]; decide
      have factor_7_15 : (31 : ZMod 162249361) ^ 55111 = 141693409 := by
        calc
          (31 : ZMod 162249361) ^ 55111 = (31 : ZMod 162249361) ^ (27555 + 27555 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 27555 * (31 : ZMod 162249361) ^ 27555) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 141693409 := by rw [factor_7_14]; decide
      have factor_7_16 : (31 : ZMod 162249361) ^ 110223 = 10134704 := by
        calc
          (31 : ZMod 162249361) ^ 110223 = (31 : ZMod 162249361) ^ (55111 + 55111 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 55111 * (31 : ZMod 162249361) ^ 55111) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 10134704 := by rw [factor_7_15]; decide
      have factor_7_17 : (31 : ZMod 162249361) ^ 220447 = 8066135 := by
        calc
          (31 : ZMod 162249361) ^ 220447 = (31 : ZMod 162249361) ^ (110223 + 110223 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 110223 * (31 : ZMod 162249361) ^ 110223) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 8066135 := by rw [factor_7_16]; decide
      have factor_7_18 : (31 : ZMod 162249361) ^ 440895 = 30709792 := by
        calc
          (31 : ZMod 162249361) ^ 440895 = (31 : ZMod 162249361) ^ (220447 + 220447 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = ((31 : ZMod 162249361) ^ 220447 * (31 : ZMod 162249361) ^ 220447) * (31 : ZMod 162249361) := by rw [pow_succ, pow_add]
          _ = 30709792 := by rw [factor_7_17]; decide
      have factor_7_19 : (31 : ZMod 162249361) ^ 881790 = 39937220 := by
        calc
          (31 : ZMod 162249361) ^ 881790 = (31 : ZMod 162249361) ^ (440895 + 440895) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 440895 * (31 : ZMod 162249361) ^ 440895 := by rw [pow_add]
          _ = 39937220 := by rw [factor_7_18]; decide
      have factor_7_20 : (31 : ZMod 162249361) ^ 1763580 = 68725087 := by
        calc
          (31 : ZMod 162249361) ^ 1763580 = (31 : ZMod 162249361) ^ (881790 + 881790) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 881790 * (31 : ZMod 162249361) ^ 881790 := by rw [pow_add]
          _ = 68725087 := by rw [factor_7_19]; decide
      have factor_7_21 : (31 : ZMod 162249361) ^ 3527160 = 112428248 := by
        calc
          (31 : ZMod 162249361) ^ 3527160 = (31 : ZMod 162249361) ^ (1763580 + 1763580) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 1763580 * (31 : ZMod 162249361) ^ 1763580 := by rw [pow_add]
          _ = 112428248 := by rw [factor_7_20]; decide
      have factor_7_22 : (31 : ZMod 162249361) ^ 7054320 = 7187805 := by
        calc
          (31 : ZMod 162249361) ^ 7054320 = (31 : ZMod 162249361) ^ (3527160 + 3527160) :=
            congrArg (fun n : ℕ => (31 : ZMod 162249361) ^ n) (by norm_num)
          _ = (31 : ZMod 162249361) ^ 3527160 * (31 : ZMod 162249361) ^ 3527160 := by rw [pow_add]
          _ = 7187805 := by rw [factor_7_21]; decide
      change (31 : ZMod 162249361) ^ 7054320 ≠ 1
      rw [factor_7_22]
      decide

#print axioms prime_lucas_162249361

end TotientTailPeriodKiller
end Erdos249257
