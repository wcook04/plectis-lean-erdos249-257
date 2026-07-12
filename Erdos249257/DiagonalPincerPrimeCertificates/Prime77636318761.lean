import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_77636318761 : Nat.Prime 77636318761 := by
  apply lucas_primality 77636318761 (31 : ZMod 77636318761)
  ·
      have fermat_0 : (31 : ZMod 77636318761) ^ 1 = 31 := by norm_num
      have fermat_1 : (31 : ZMod 77636318761) ^ 2 = 961 := by
        calc
          (31 : ZMod 77636318761) ^ 2 = (31 : ZMod 77636318761) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1 * (31 : ZMod 77636318761) ^ 1 := by rw [pow_add]
          _ = 961 := by rw [fermat_0]; decide
      have fermat_2 : (31 : ZMod 77636318761) ^ 4 = 923521 := by
        calc
          (31 : ZMod 77636318761) ^ 4 = (31 : ZMod 77636318761) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 2 * (31 : ZMod 77636318761) ^ 2 := by rw [pow_add]
          _ = 923521 := by rw [fermat_1]; decide
      have fermat_3 : (31 : ZMod 77636318761) ^ 9 = 43273781931 := by
        calc
          (31 : ZMod 77636318761) ^ 9 = (31 : ZMod 77636318761) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 4 * (31 : ZMod 77636318761) ^ 4) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 43273781931 := by rw [fermat_2]; decide
      have fermat_4 : (31 : ZMod 77636318761) ^ 18 = 23030914803 := by
        calc
          (31 : ZMod 77636318761) ^ 18 = (31 : ZMod 77636318761) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 9 * (31 : ZMod 77636318761) ^ 9 := by rw [pow_add]
          _ = 23030914803 := by rw [fermat_3]; decide
      have fermat_5 : (31 : ZMod 77636318761) ^ 36 = 29750238858 := by
        calc
          (31 : ZMod 77636318761) ^ 36 = (31 : ZMod 77636318761) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 18 * (31 : ZMod 77636318761) ^ 18 := by rw [pow_add]
          _ = 29750238858 := by rw [fermat_4]; decide
      have fermat_6 : (31 : ZMod 77636318761) ^ 72 = 42852505976 := by
        calc
          (31 : ZMod 77636318761) ^ 72 = (31 : ZMod 77636318761) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 36 * (31 : ZMod 77636318761) ^ 36 := by rw [pow_add]
          _ = 42852505976 := by rw [fermat_5]; decide
      have fermat_7 : (31 : ZMod 77636318761) ^ 144 = 46134182034 := by
        calc
          (31 : ZMod 77636318761) ^ 144 = (31 : ZMod 77636318761) ^ (72 + 72) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 72 * (31 : ZMod 77636318761) ^ 72 := by rw [pow_add]
          _ = 46134182034 := by rw [fermat_6]; decide
      have fermat_8 : (31 : ZMod 77636318761) ^ 289 = 62028259856 := by
        calc
          (31 : ZMod 77636318761) ^ 289 = (31 : ZMod 77636318761) ^ (144 + 144 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 144 * (31 : ZMod 77636318761) ^ 144) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 62028259856 := by rw [fermat_7]; decide
      have fermat_9 : (31 : ZMod 77636318761) ^ 578 = 5601932691 := by
        calc
          (31 : ZMod 77636318761) ^ 578 = (31 : ZMod 77636318761) ^ (289 + 289) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 289 * (31 : ZMod 77636318761) ^ 289 := by rw [pow_add]
          _ = 5601932691 := by rw [fermat_8]; decide
      have fermat_10 : (31 : ZMod 77636318761) ^ 1156 = 32996015239 := by
        calc
          (31 : ZMod 77636318761) ^ 1156 = (31 : ZMod 77636318761) ^ (578 + 578) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 578 * (31 : ZMod 77636318761) ^ 578 := by rw [pow_add]
          _ = 32996015239 := by rw [fermat_9]; decide
      have fermat_11 : (31 : ZMod 77636318761) ^ 2313 = 38103576992 := by
        calc
          (31 : ZMod 77636318761) ^ 2313 = (31 : ZMod 77636318761) ^ (1156 + 1156 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1156 * (31 : ZMod 77636318761) ^ 1156) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 38103576992 := by rw [fermat_10]; decide
      have fermat_12 : (31 : ZMod 77636318761) ^ 4627 = 4474393191 := by
        calc
          (31 : ZMod 77636318761) ^ 4627 = (31 : ZMod 77636318761) ^ (2313 + 2313 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 2313 * (31 : ZMod 77636318761) ^ 2313) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 4474393191 := by rw [fermat_11]; decide
      have fermat_13 : (31 : ZMod 77636318761) ^ 9254 = 66108357176 := by
        calc
          (31 : ZMod 77636318761) ^ 9254 = (31 : ZMod 77636318761) ^ (4627 + 4627) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 4627 * (31 : ZMod 77636318761) ^ 4627 := by rw [pow_add]
          _ = 66108357176 := by rw [fermat_12]; decide
      have fermat_14 : (31 : ZMod 77636318761) ^ 18509 = 64925231660 := by
        calc
          (31 : ZMod 77636318761) ^ 18509 = (31 : ZMod 77636318761) ^ (9254 + 9254 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 9254 * (31 : ZMod 77636318761) ^ 9254) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 64925231660 := by rw [fermat_13]; decide
      have fermat_15 : (31 : ZMod 77636318761) ^ 37019 = 8288651866 := by
        calc
          (31 : ZMod 77636318761) ^ 37019 = (31 : ZMod 77636318761) ^ (18509 + 18509 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 18509 * (31 : ZMod 77636318761) ^ 18509) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 8288651866 := by rw [fermat_14]; decide
      have fermat_16 : (31 : ZMod 77636318761) ^ 74039 = 41890255086 := by
        calc
          (31 : ZMod 77636318761) ^ 74039 = (31 : ZMod 77636318761) ^ (37019 + 37019 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 37019 * (31 : ZMod 77636318761) ^ 37019) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 41890255086 := by rw [fermat_15]; decide
      have fermat_17 : (31 : ZMod 77636318761) ^ 148079 = 64355034254 := by
        calc
          (31 : ZMod 77636318761) ^ 148079 = (31 : ZMod 77636318761) ^ (74039 + 74039 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 74039 * (31 : ZMod 77636318761) ^ 74039) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 64355034254 := by rw [fermat_16]; decide
      have fermat_18 : (31 : ZMod 77636318761) ^ 296159 = 33498142675 := by
        calc
          (31 : ZMod 77636318761) ^ 296159 = (31 : ZMod 77636318761) ^ (148079 + 148079 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 148079 * (31 : ZMod 77636318761) ^ 148079) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 33498142675 := by rw [fermat_17]; decide
      have fermat_19 : (31 : ZMod 77636318761) ^ 592318 = 48125476281 := by
        calc
          (31 : ZMod 77636318761) ^ 592318 = (31 : ZMod 77636318761) ^ (296159 + 296159) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 296159 * (31 : ZMod 77636318761) ^ 296159 := by rw [pow_add]
          _ = 48125476281 := by rw [fermat_18]; decide
      have fermat_20 : (31 : ZMod 77636318761) ^ 1184636 = 50226999412 := by
        calc
          (31 : ZMod 77636318761) ^ 1184636 = (31 : ZMod 77636318761) ^ (592318 + 592318) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 592318 * (31 : ZMod 77636318761) ^ 592318 := by rw [pow_add]
          _ = 50226999412 := by rw [fermat_19]; decide
      have fermat_21 : (31 : ZMod 77636318761) ^ 2369272 = 9914082289 := by
        calc
          (31 : ZMod 77636318761) ^ 2369272 = (31 : ZMod 77636318761) ^ (1184636 + 1184636) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1184636 * (31 : ZMod 77636318761) ^ 1184636 := by rw [pow_add]
          _ = 9914082289 := by rw [fermat_20]; decide
      have fermat_22 : (31 : ZMod 77636318761) ^ 4738544 = 9019949349 := by
        calc
          (31 : ZMod 77636318761) ^ 4738544 = (31 : ZMod 77636318761) ^ (2369272 + 2369272) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 2369272 * (31 : ZMod 77636318761) ^ 2369272 := by rw [pow_add]
          _ = 9019949349 := by rw [fermat_21]; decide
      have fermat_23 : (31 : ZMod 77636318761) ^ 9477089 = 60433446542 := by
        calc
          (31 : ZMod 77636318761) ^ 9477089 = (31 : ZMod 77636318761) ^ (4738544 + 4738544 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 4738544 * (31 : ZMod 77636318761) ^ 4738544) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 60433446542 := by rw [fermat_22]; decide
      have fermat_24 : (31 : ZMod 77636318761) ^ 18954179 = 8378616035 := by
        calc
          (31 : ZMod 77636318761) ^ 18954179 = (31 : ZMod 77636318761) ^ (9477089 + 9477089 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 9477089 * (31 : ZMod 77636318761) ^ 9477089) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 8378616035 := by rw [fermat_23]; decide
      have fermat_25 : (31 : ZMod 77636318761) ^ 37908358 = 63859255744 := by
        calc
          (31 : ZMod 77636318761) ^ 37908358 = (31 : ZMod 77636318761) ^ (18954179 + 18954179) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 18954179 * (31 : ZMod 77636318761) ^ 18954179 := by rw [pow_add]
          _ = 63859255744 := by rw [fermat_24]; decide
      have fermat_26 : (31 : ZMod 77636318761) ^ 75816717 = 44050565033 := by
        calc
          (31 : ZMod 77636318761) ^ 75816717 = (31 : ZMod 77636318761) ^ (37908358 + 37908358 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 37908358 * (31 : ZMod 77636318761) ^ 37908358) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 44050565033 := by rw [fermat_25]; decide
      have fermat_27 : (31 : ZMod 77636318761) ^ 151633435 = 67286029868 := by
        calc
          (31 : ZMod 77636318761) ^ 151633435 = (31 : ZMod 77636318761) ^ (75816717 + 75816717 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 75816717 * (31 : ZMod 77636318761) ^ 75816717) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 67286029868 := by rw [fermat_26]; decide
      have fermat_28 : (31 : ZMod 77636318761) ^ 303266870 = 69534443775 := by
        calc
          (31 : ZMod 77636318761) ^ 303266870 = (31 : ZMod 77636318761) ^ (151633435 + 151633435) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 151633435 * (31 : ZMod 77636318761) ^ 151633435 := by rw [pow_add]
          _ = 69534443775 := by rw [fermat_27]; decide
      have fermat_29 : (31 : ZMod 77636318761) ^ 606533740 = 74239697702 := by
        calc
          (31 : ZMod 77636318761) ^ 606533740 = (31 : ZMod 77636318761) ^ (303266870 + 303266870) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 303266870 * (31 : ZMod 77636318761) ^ 303266870 := by rw [pow_add]
          _ = 74239697702 := by rw [fermat_28]; decide
      have fermat_30 : (31 : ZMod 77636318761) ^ 1213067480 = 23081792145 := by
        calc
          (31 : ZMod 77636318761) ^ 1213067480 = (31 : ZMod 77636318761) ^ (606533740 + 606533740) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 606533740 * (31 : ZMod 77636318761) ^ 606533740 := by rw [pow_add]
          _ = 23081792145 := by rw [fermat_29]; decide
      have fermat_31 : (31 : ZMod 77636318761) ^ 2426134961 = 75120070225 := by
        calc
          (31 : ZMod 77636318761) ^ 2426134961 = (31 : ZMod 77636318761) ^ (1213067480 + 1213067480 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1213067480 * (31 : ZMod 77636318761) ^ 1213067480) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 75120070225 := by rw [fermat_30]; decide
      have fermat_32 : (31 : ZMod 77636318761) ^ 4852269922 = 4842980764 := by
        calc
          (31 : ZMod 77636318761) ^ 4852269922 = (31 : ZMod 77636318761) ^ (2426134961 + 2426134961) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 2426134961 * (31 : ZMod 77636318761) ^ 2426134961 := by rw [pow_add]
          _ = 4842980764 := by rw [fermat_31]; decide
      have fermat_33 : (31 : ZMod 77636318761) ^ 9704539845 = 24655428236 := by
        calc
          (31 : ZMod 77636318761) ^ 9704539845 = (31 : ZMod 77636318761) ^ (4852269922 + 4852269922 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 4852269922 * (31 : ZMod 77636318761) ^ 4852269922) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 24655428236 := by rw [fermat_32]; decide
      have fermat_34 : (31 : ZMod 77636318761) ^ 19409079690 = 52806332037 := by
        calc
          (31 : ZMod 77636318761) ^ 19409079690 = (31 : ZMod 77636318761) ^ (9704539845 + 9704539845) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 9704539845 * (31 : ZMod 77636318761) ^ 9704539845 := by rw [pow_add]
          _ = 52806332037 := by rw [fermat_33]; decide
      have fermat_35 : (31 : ZMod 77636318761) ^ 38818159380 = 77636318760 := by
        calc
          (31 : ZMod 77636318761) ^ 38818159380 = (31 : ZMod 77636318761) ^ (19409079690 + 19409079690) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 19409079690 * (31 : ZMod 77636318761) ^ 19409079690 := by rw [pow_add]
          _ = 77636318760 := by rw [fermat_34]; decide
      have fermat_36 : (31 : ZMod 77636318761) ^ 77636318760 = 1 := by
        calc
          (31 : ZMod 77636318761) ^ 77636318760 = (31 : ZMod 77636318761) ^ (38818159380 + 38818159380) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 38818159380 * (31 : ZMod 77636318761) ^ 38818159380 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod = 77636318761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (31 : ZMod 77636318761) ^ 1 = 31 := by norm_num
      have factor_0_1 : (31 : ZMod 77636318761) ^ 2 = 961 := by
        calc
          (31 : ZMod 77636318761) ^ 2 = (31 : ZMod 77636318761) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1 * (31 : ZMod 77636318761) ^ 1 := by rw [pow_add]
          _ = 961 := by rw [factor_0_0]; decide
      have factor_0_2 : (31 : ZMod 77636318761) ^ 4 = 923521 := by
        calc
          (31 : ZMod 77636318761) ^ 4 = (31 : ZMod 77636318761) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 2 * (31 : ZMod 77636318761) ^ 2 := by rw [pow_add]
          _ = 923521 := by rw [factor_0_1]; decide
      have factor_0_3 : (31 : ZMod 77636318761) ^ 9 = 43273781931 := by
        calc
          (31 : ZMod 77636318761) ^ 9 = (31 : ZMod 77636318761) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 4 * (31 : ZMod 77636318761) ^ 4) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 43273781931 := by rw [factor_0_2]; decide
      have factor_0_4 : (31 : ZMod 77636318761) ^ 18 = 23030914803 := by
        calc
          (31 : ZMod 77636318761) ^ 18 = (31 : ZMod 77636318761) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 9 * (31 : ZMod 77636318761) ^ 9 := by rw [pow_add]
          _ = 23030914803 := by rw [factor_0_3]; decide
      have factor_0_5 : (31 : ZMod 77636318761) ^ 36 = 29750238858 := by
        calc
          (31 : ZMod 77636318761) ^ 36 = (31 : ZMod 77636318761) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 18 * (31 : ZMod 77636318761) ^ 18 := by rw [pow_add]
          _ = 29750238858 := by rw [factor_0_4]; decide
      have factor_0_6 : (31 : ZMod 77636318761) ^ 72 = 42852505976 := by
        calc
          (31 : ZMod 77636318761) ^ 72 = (31 : ZMod 77636318761) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 36 * (31 : ZMod 77636318761) ^ 36 := by rw [pow_add]
          _ = 42852505976 := by rw [factor_0_5]; decide
      have factor_0_7 : (31 : ZMod 77636318761) ^ 144 = 46134182034 := by
        calc
          (31 : ZMod 77636318761) ^ 144 = (31 : ZMod 77636318761) ^ (72 + 72) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 72 * (31 : ZMod 77636318761) ^ 72 := by rw [pow_add]
          _ = 46134182034 := by rw [factor_0_6]; decide
      have factor_0_8 : (31 : ZMod 77636318761) ^ 289 = 62028259856 := by
        calc
          (31 : ZMod 77636318761) ^ 289 = (31 : ZMod 77636318761) ^ (144 + 144 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 144 * (31 : ZMod 77636318761) ^ 144) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 62028259856 := by rw [factor_0_7]; decide
      have factor_0_9 : (31 : ZMod 77636318761) ^ 578 = 5601932691 := by
        calc
          (31 : ZMod 77636318761) ^ 578 = (31 : ZMod 77636318761) ^ (289 + 289) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 289 * (31 : ZMod 77636318761) ^ 289 := by rw [pow_add]
          _ = 5601932691 := by rw [factor_0_8]; decide
      have factor_0_10 : (31 : ZMod 77636318761) ^ 1156 = 32996015239 := by
        calc
          (31 : ZMod 77636318761) ^ 1156 = (31 : ZMod 77636318761) ^ (578 + 578) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 578 * (31 : ZMod 77636318761) ^ 578 := by rw [pow_add]
          _ = 32996015239 := by rw [factor_0_9]; decide
      have factor_0_11 : (31 : ZMod 77636318761) ^ 2313 = 38103576992 := by
        calc
          (31 : ZMod 77636318761) ^ 2313 = (31 : ZMod 77636318761) ^ (1156 + 1156 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1156 * (31 : ZMod 77636318761) ^ 1156) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 38103576992 := by rw [factor_0_10]; decide
      have factor_0_12 : (31 : ZMod 77636318761) ^ 4627 = 4474393191 := by
        calc
          (31 : ZMod 77636318761) ^ 4627 = (31 : ZMod 77636318761) ^ (2313 + 2313 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 2313 * (31 : ZMod 77636318761) ^ 2313) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 4474393191 := by rw [factor_0_11]; decide
      have factor_0_13 : (31 : ZMod 77636318761) ^ 9254 = 66108357176 := by
        calc
          (31 : ZMod 77636318761) ^ 9254 = (31 : ZMod 77636318761) ^ (4627 + 4627) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 4627 * (31 : ZMod 77636318761) ^ 4627 := by rw [pow_add]
          _ = 66108357176 := by rw [factor_0_12]; decide
      have factor_0_14 : (31 : ZMod 77636318761) ^ 18509 = 64925231660 := by
        calc
          (31 : ZMod 77636318761) ^ 18509 = (31 : ZMod 77636318761) ^ (9254 + 9254 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 9254 * (31 : ZMod 77636318761) ^ 9254) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 64925231660 := by rw [factor_0_13]; decide
      have factor_0_15 : (31 : ZMod 77636318761) ^ 37019 = 8288651866 := by
        calc
          (31 : ZMod 77636318761) ^ 37019 = (31 : ZMod 77636318761) ^ (18509 + 18509 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 18509 * (31 : ZMod 77636318761) ^ 18509) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 8288651866 := by rw [factor_0_14]; decide
      have factor_0_16 : (31 : ZMod 77636318761) ^ 74039 = 41890255086 := by
        calc
          (31 : ZMod 77636318761) ^ 74039 = (31 : ZMod 77636318761) ^ (37019 + 37019 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 37019 * (31 : ZMod 77636318761) ^ 37019) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 41890255086 := by rw [factor_0_15]; decide
      have factor_0_17 : (31 : ZMod 77636318761) ^ 148079 = 64355034254 := by
        calc
          (31 : ZMod 77636318761) ^ 148079 = (31 : ZMod 77636318761) ^ (74039 + 74039 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 74039 * (31 : ZMod 77636318761) ^ 74039) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 64355034254 := by rw [factor_0_16]; decide
      have factor_0_18 : (31 : ZMod 77636318761) ^ 296159 = 33498142675 := by
        calc
          (31 : ZMod 77636318761) ^ 296159 = (31 : ZMod 77636318761) ^ (148079 + 148079 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 148079 * (31 : ZMod 77636318761) ^ 148079) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 33498142675 := by rw [factor_0_17]; decide
      have factor_0_19 : (31 : ZMod 77636318761) ^ 592318 = 48125476281 := by
        calc
          (31 : ZMod 77636318761) ^ 592318 = (31 : ZMod 77636318761) ^ (296159 + 296159) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 296159 * (31 : ZMod 77636318761) ^ 296159 := by rw [pow_add]
          _ = 48125476281 := by rw [factor_0_18]; decide
      have factor_0_20 : (31 : ZMod 77636318761) ^ 1184636 = 50226999412 := by
        calc
          (31 : ZMod 77636318761) ^ 1184636 = (31 : ZMod 77636318761) ^ (592318 + 592318) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 592318 * (31 : ZMod 77636318761) ^ 592318 := by rw [pow_add]
          _ = 50226999412 := by rw [factor_0_19]; decide
      have factor_0_21 : (31 : ZMod 77636318761) ^ 2369272 = 9914082289 := by
        calc
          (31 : ZMod 77636318761) ^ 2369272 = (31 : ZMod 77636318761) ^ (1184636 + 1184636) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1184636 * (31 : ZMod 77636318761) ^ 1184636 := by rw [pow_add]
          _ = 9914082289 := by rw [factor_0_20]; decide
      have factor_0_22 : (31 : ZMod 77636318761) ^ 4738544 = 9019949349 := by
        calc
          (31 : ZMod 77636318761) ^ 4738544 = (31 : ZMod 77636318761) ^ (2369272 + 2369272) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 2369272 * (31 : ZMod 77636318761) ^ 2369272 := by rw [pow_add]
          _ = 9019949349 := by rw [factor_0_21]; decide
      have factor_0_23 : (31 : ZMod 77636318761) ^ 9477089 = 60433446542 := by
        calc
          (31 : ZMod 77636318761) ^ 9477089 = (31 : ZMod 77636318761) ^ (4738544 + 4738544 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 4738544 * (31 : ZMod 77636318761) ^ 4738544) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 60433446542 := by rw [factor_0_22]; decide
      have factor_0_24 : (31 : ZMod 77636318761) ^ 18954179 = 8378616035 := by
        calc
          (31 : ZMod 77636318761) ^ 18954179 = (31 : ZMod 77636318761) ^ (9477089 + 9477089 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 9477089 * (31 : ZMod 77636318761) ^ 9477089) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 8378616035 := by rw [factor_0_23]; decide
      have factor_0_25 : (31 : ZMod 77636318761) ^ 37908358 = 63859255744 := by
        calc
          (31 : ZMod 77636318761) ^ 37908358 = (31 : ZMod 77636318761) ^ (18954179 + 18954179) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 18954179 * (31 : ZMod 77636318761) ^ 18954179 := by rw [pow_add]
          _ = 63859255744 := by rw [factor_0_24]; decide
      have factor_0_26 : (31 : ZMod 77636318761) ^ 75816717 = 44050565033 := by
        calc
          (31 : ZMod 77636318761) ^ 75816717 = (31 : ZMod 77636318761) ^ (37908358 + 37908358 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 37908358 * (31 : ZMod 77636318761) ^ 37908358) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 44050565033 := by rw [factor_0_25]; decide
      have factor_0_27 : (31 : ZMod 77636318761) ^ 151633435 = 67286029868 := by
        calc
          (31 : ZMod 77636318761) ^ 151633435 = (31 : ZMod 77636318761) ^ (75816717 + 75816717 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 75816717 * (31 : ZMod 77636318761) ^ 75816717) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 67286029868 := by rw [factor_0_26]; decide
      have factor_0_28 : (31 : ZMod 77636318761) ^ 303266870 = 69534443775 := by
        calc
          (31 : ZMod 77636318761) ^ 303266870 = (31 : ZMod 77636318761) ^ (151633435 + 151633435) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 151633435 * (31 : ZMod 77636318761) ^ 151633435 := by rw [pow_add]
          _ = 69534443775 := by rw [factor_0_27]; decide
      have factor_0_29 : (31 : ZMod 77636318761) ^ 606533740 = 74239697702 := by
        calc
          (31 : ZMod 77636318761) ^ 606533740 = (31 : ZMod 77636318761) ^ (303266870 + 303266870) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 303266870 * (31 : ZMod 77636318761) ^ 303266870 := by rw [pow_add]
          _ = 74239697702 := by rw [factor_0_28]; decide
      have factor_0_30 : (31 : ZMod 77636318761) ^ 1213067480 = 23081792145 := by
        calc
          (31 : ZMod 77636318761) ^ 1213067480 = (31 : ZMod 77636318761) ^ (606533740 + 606533740) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 606533740 * (31 : ZMod 77636318761) ^ 606533740 := by rw [pow_add]
          _ = 23081792145 := by rw [factor_0_29]; decide
      have factor_0_31 : (31 : ZMod 77636318761) ^ 2426134961 = 75120070225 := by
        calc
          (31 : ZMod 77636318761) ^ 2426134961 = (31 : ZMod 77636318761) ^ (1213067480 + 1213067480 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1213067480 * (31 : ZMod 77636318761) ^ 1213067480) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 75120070225 := by rw [factor_0_30]; decide
      have factor_0_32 : (31 : ZMod 77636318761) ^ 4852269922 = 4842980764 := by
        calc
          (31 : ZMod 77636318761) ^ 4852269922 = (31 : ZMod 77636318761) ^ (2426134961 + 2426134961) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 2426134961 * (31 : ZMod 77636318761) ^ 2426134961 := by rw [pow_add]
          _ = 4842980764 := by rw [factor_0_31]; decide
      have factor_0_33 : (31 : ZMod 77636318761) ^ 9704539845 = 24655428236 := by
        calc
          (31 : ZMod 77636318761) ^ 9704539845 = (31 : ZMod 77636318761) ^ (4852269922 + 4852269922 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 4852269922 * (31 : ZMod 77636318761) ^ 4852269922) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 24655428236 := by rw [factor_0_32]; decide
      have factor_0_34 : (31 : ZMod 77636318761) ^ 19409079690 = 52806332037 := by
        calc
          (31 : ZMod 77636318761) ^ 19409079690 = (31 : ZMod 77636318761) ^ (9704539845 + 9704539845) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 9704539845 * (31 : ZMod 77636318761) ^ 9704539845 := by rw [pow_add]
          _ = 52806332037 := by rw [factor_0_33]; decide
      have factor_0_35 : (31 : ZMod 77636318761) ^ 38818159380 = 77636318760 := by
        calc
          (31 : ZMod 77636318761) ^ 38818159380 = (31 : ZMod 77636318761) ^ (19409079690 + 19409079690) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 19409079690 * (31 : ZMod 77636318761) ^ 19409079690 := by rw [pow_add]
          _ = 77636318760 := by rw [factor_0_34]; decide
      change (31 : ZMod 77636318761) ^ 38818159380 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (31 : ZMod 77636318761) ^ 1 = 31 := by norm_num
      have factor_1_1 : (31 : ZMod 77636318761) ^ 3 = 29791 := by
        calc
          (31 : ZMod 77636318761) ^ 3 = (31 : ZMod 77636318761) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1 * (31 : ZMod 77636318761) ^ 1) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 29791 := by rw [factor_1_0]; decide
      have factor_1_2 : (31 : ZMod 77636318761) ^ 6 = 887503681 := by
        calc
          (31 : ZMod 77636318761) ^ 6 = (31 : ZMod 77636318761) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 3 * (31 : ZMod 77636318761) ^ 3 := by rw [pow_add]
          _ = 887503681 := by rw [factor_1_1]; decide
      have factor_1_3 : (31 : ZMod 77636318761) ^ 12 = 18164480016 := by
        calc
          (31 : ZMod 77636318761) ^ 12 = (31 : ZMod 77636318761) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 6 * (31 : ZMod 77636318761) ^ 6 := by rw [pow_add]
          _ = 18164480016 := by rw [factor_1_2]; decide
      have factor_1_4 : (31 : ZMod 77636318761) ^ 24 = 58660638284 := by
        calc
          (31 : ZMod 77636318761) ^ 24 = (31 : ZMod 77636318761) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 12 * (31 : ZMod 77636318761) ^ 12 := by rw [pow_add]
          _ = 58660638284 := by rw [factor_1_3]; decide
      have factor_1_5 : (31 : ZMod 77636318761) ^ 48 = 10856710433 := by
        calc
          (31 : ZMod 77636318761) ^ 48 = (31 : ZMod 77636318761) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 24 * (31 : ZMod 77636318761) ^ 24 := by rw [pow_add]
          _ = 10856710433 := by rw [factor_1_4]; decide
      have factor_1_6 : (31 : ZMod 77636318761) ^ 96 = 62557654244 := by
        calc
          (31 : ZMod 77636318761) ^ 96 = (31 : ZMod 77636318761) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 48 * (31 : ZMod 77636318761) ^ 48 := by rw [pow_add]
          _ = 62557654244 := by rw [factor_1_5]; decide
      have factor_1_7 : (31 : ZMod 77636318761) ^ 192 = 44638074051 := by
        calc
          (31 : ZMod 77636318761) ^ 192 = (31 : ZMod 77636318761) ^ (96 + 96) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 96 * (31 : ZMod 77636318761) ^ 96 := by rw [pow_add]
          _ = 44638074051 := by rw [factor_1_6]; decide
      have factor_1_8 : (31 : ZMod 77636318761) ^ 385 = 23826810483 := by
        calc
          (31 : ZMod 77636318761) ^ 385 = (31 : ZMod 77636318761) ^ (192 + 192 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 192 * (31 : ZMod 77636318761) ^ 192) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 23826810483 := by rw [factor_1_7]; decide
      have factor_1_9 : (31 : ZMod 77636318761) ^ 771 = 23986357983 := by
        calc
          (31 : ZMod 77636318761) ^ 771 = (31 : ZMod 77636318761) ^ (385 + 385 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 385 * (31 : ZMod 77636318761) ^ 385) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 23986357983 := by rw [factor_1_8]; decide
      have factor_1_10 : (31 : ZMod 77636318761) ^ 1542 = 11169235830 := by
        calc
          (31 : ZMod 77636318761) ^ 1542 = (31 : ZMod 77636318761) ^ (771 + 771) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 771 * (31 : ZMod 77636318761) ^ 771 := by rw [pow_add]
          _ = 11169235830 := by rw [factor_1_9]; decide
      have factor_1_11 : (31 : ZMod 77636318761) ^ 3084 = 61056143256 := by
        calc
          (31 : ZMod 77636318761) ^ 3084 = (31 : ZMod 77636318761) ^ (1542 + 1542) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1542 * (31 : ZMod 77636318761) ^ 1542 := by rw [pow_add]
          _ = 61056143256 := by rw [factor_1_10]; decide
      have factor_1_12 : (31 : ZMod 77636318761) ^ 6169 = 58760759150 := by
        calc
          (31 : ZMod 77636318761) ^ 6169 = (31 : ZMod 77636318761) ^ (3084 + 3084 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 3084 * (31 : ZMod 77636318761) ^ 3084) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 58760759150 := by rw [factor_1_11]; decide
      have factor_1_13 : (31 : ZMod 77636318761) ^ 12339 = 69672370309 := by
        calc
          (31 : ZMod 77636318761) ^ 12339 = (31 : ZMod 77636318761) ^ (6169 + 6169 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 6169 * (31 : ZMod 77636318761) ^ 6169) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 69672370309 := by rw [factor_1_12]; decide
      have factor_1_14 : (31 : ZMod 77636318761) ^ 24679 = 69956119129 := by
        calc
          (31 : ZMod 77636318761) ^ 24679 = (31 : ZMod 77636318761) ^ (12339 + 12339 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 12339 * (31 : ZMod 77636318761) ^ 12339) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 69956119129 := by rw [factor_1_13]; decide
      have factor_1_15 : (31 : ZMod 77636318761) ^ 49359 = 19340162115 := by
        calc
          (31 : ZMod 77636318761) ^ 49359 = (31 : ZMod 77636318761) ^ (24679 + 24679 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 24679 * (31 : ZMod 77636318761) ^ 24679) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 19340162115 := by rw [factor_1_14]; decide
      have factor_1_16 : (31 : ZMod 77636318761) ^ 98719 = 4033136275 := by
        calc
          (31 : ZMod 77636318761) ^ 98719 = (31 : ZMod 77636318761) ^ (49359 + 49359 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 49359 * (31 : ZMod 77636318761) ^ 49359) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 4033136275 := by rw [factor_1_15]; decide
      have factor_1_17 : (31 : ZMod 77636318761) ^ 197439 = 6113810531 := by
        calc
          (31 : ZMod 77636318761) ^ 197439 = (31 : ZMod 77636318761) ^ (98719 + 98719 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 98719 * (31 : ZMod 77636318761) ^ 98719) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 6113810531 := by rw [factor_1_16]; decide
      have factor_1_18 : (31 : ZMod 77636318761) ^ 394878 = 46417800286 := by
        calc
          (31 : ZMod 77636318761) ^ 394878 = (31 : ZMod 77636318761) ^ (197439 + 197439) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 197439 * (31 : ZMod 77636318761) ^ 197439 := by rw [pow_add]
          _ = 46417800286 := by rw [factor_1_17]; decide
      have factor_1_19 : (31 : ZMod 77636318761) ^ 789757 = 47816359403 := by
        calc
          (31 : ZMod 77636318761) ^ 789757 = (31 : ZMod 77636318761) ^ (394878 + 394878 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 394878 * (31 : ZMod 77636318761) ^ 394878) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 47816359403 := by rw [factor_1_18]; decide
      have factor_1_20 : (31 : ZMod 77636318761) ^ 1579514 = 18787261010 := by
        calc
          (31 : ZMod 77636318761) ^ 1579514 = (31 : ZMod 77636318761) ^ (789757 + 789757) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 789757 * (31 : ZMod 77636318761) ^ 789757 := by rw [pow_add]
          _ = 18787261010 := by rw [factor_1_19]; decide
      have factor_1_21 : (31 : ZMod 77636318761) ^ 3159029 = 18766579464 := by
        calc
          (31 : ZMod 77636318761) ^ 3159029 = (31 : ZMod 77636318761) ^ (1579514 + 1579514 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1579514 * (31 : ZMod 77636318761) ^ 1579514) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 18766579464 := by rw [factor_1_20]; decide
      have factor_1_22 : (31 : ZMod 77636318761) ^ 6318059 = 9085581640 := by
        calc
          (31 : ZMod 77636318761) ^ 6318059 = (31 : ZMod 77636318761) ^ (3159029 + 3159029 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 3159029 * (31 : ZMod 77636318761) ^ 3159029) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 9085581640 := by rw [factor_1_21]; decide
      have factor_1_23 : (31 : ZMod 77636318761) ^ 12636119 = 1966301521 := by
        calc
          (31 : ZMod 77636318761) ^ 12636119 = (31 : ZMod 77636318761) ^ (6318059 + 6318059 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 6318059 * (31 : ZMod 77636318761) ^ 6318059) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 1966301521 := by rw [factor_1_22]; decide
      have factor_1_24 : (31 : ZMod 77636318761) ^ 25272239 = 50721215150 := by
        calc
          (31 : ZMod 77636318761) ^ 25272239 = (31 : ZMod 77636318761) ^ (12636119 + 12636119 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 12636119 * (31 : ZMod 77636318761) ^ 12636119) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 50721215150 := by rw [factor_1_23]; decide
      have factor_1_25 : (31 : ZMod 77636318761) ^ 50544478 = 816740983 := by
        calc
          (31 : ZMod 77636318761) ^ 50544478 = (31 : ZMod 77636318761) ^ (25272239 + 25272239) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 25272239 * (31 : ZMod 77636318761) ^ 25272239 := by rw [pow_add]
          _ = 816740983 := by rw [factor_1_24]; decide
      have factor_1_26 : (31 : ZMod 77636318761) ^ 101088956 = 64525685982 := by
        calc
          (31 : ZMod 77636318761) ^ 101088956 = (31 : ZMod 77636318761) ^ (50544478 + 50544478) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 50544478 * (31 : ZMod 77636318761) ^ 50544478 := by rw [pow_add]
          _ = 64525685982 := by rw [factor_1_25]; decide
      have factor_1_27 : (31 : ZMod 77636318761) ^ 202177913 = 51991012502 := by
        calc
          (31 : ZMod 77636318761) ^ 202177913 = (31 : ZMod 77636318761) ^ (101088956 + 101088956 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 101088956 * (31 : ZMod 77636318761) ^ 101088956) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 51991012502 := by rw [factor_1_26]; decide
      have factor_1_28 : (31 : ZMod 77636318761) ^ 404355826 = 25439882045 := by
        calc
          (31 : ZMod 77636318761) ^ 404355826 = (31 : ZMod 77636318761) ^ (202177913 + 202177913) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 202177913 * (31 : ZMod 77636318761) ^ 202177913 := by rw [pow_add]
          _ = 25439882045 := by rw [factor_1_27]; decide
      have factor_1_29 : (31 : ZMod 77636318761) ^ 808711653 = 51475012965 := by
        calc
          (31 : ZMod 77636318761) ^ 808711653 = (31 : ZMod 77636318761) ^ (404355826 + 404355826 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 404355826 * (31 : ZMod 77636318761) ^ 404355826) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 51475012965 := by rw [factor_1_28]; decide
      have factor_1_30 : (31 : ZMod 77636318761) ^ 1617423307 = 74774193904 := by
        calc
          (31 : ZMod 77636318761) ^ 1617423307 = (31 : ZMod 77636318761) ^ (808711653 + 808711653 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 808711653 * (31 : ZMod 77636318761) ^ 808711653) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 74774193904 := by rw [factor_1_29]; decide
      have factor_1_31 : (31 : ZMod 77636318761) ^ 3234846615 = 40211277284 := by
        calc
          (31 : ZMod 77636318761) ^ 3234846615 = (31 : ZMod 77636318761) ^ (1617423307 + 1617423307 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1617423307 * (31 : ZMod 77636318761) ^ 1617423307) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 40211277284 := by rw [factor_1_30]; decide
      have factor_1_32 : (31 : ZMod 77636318761) ^ 6469693230 = 11269992863 := by
        calc
          (31 : ZMod 77636318761) ^ 6469693230 = (31 : ZMod 77636318761) ^ (3234846615 + 3234846615) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 3234846615 * (31 : ZMod 77636318761) ^ 3234846615 := by rw [pow_add]
          _ = 11269992863 := by rw [factor_1_31]; decide
      have factor_1_33 : (31 : ZMod 77636318761) ^ 12939386460 = 42914013715 := by
        calc
          (31 : ZMod 77636318761) ^ 12939386460 = (31 : ZMod 77636318761) ^ (6469693230 + 6469693230) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 6469693230 * (31 : ZMod 77636318761) ^ 6469693230 := by rw [pow_add]
          _ = 42914013715 := by rw [factor_1_32]; decide
      have factor_1_34 : (31 : ZMod 77636318761) ^ 25878772920 = 42914013714 := by
        calc
          (31 : ZMod 77636318761) ^ 25878772920 = (31 : ZMod 77636318761) ^ (12939386460 + 12939386460) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 12939386460 * (31 : ZMod 77636318761) ^ 12939386460 := by rw [pow_add]
          _ = 42914013714 := by rw [factor_1_33]; decide
      change (31 : ZMod 77636318761) ^ 25878772920 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (31 : ZMod 77636318761) ^ 1 = 31 := by norm_num
      have factor_2_1 : (31 : ZMod 77636318761) ^ 3 = 29791 := by
        calc
          (31 : ZMod 77636318761) ^ 3 = (31 : ZMod 77636318761) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1 * (31 : ZMod 77636318761) ^ 1) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 29791 := by rw [factor_2_0]; decide
      have factor_2_2 : (31 : ZMod 77636318761) ^ 7 = 27512614111 := by
        calc
          (31 : ZMod 77636318761) ^ 7 = (31 : ZMod 77636318761) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 3 * (31 : ZMod 77636318761) ^ 3) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 27512614111 := by rw [factor_2_1]; decide
      have factor_2_3 : (31 : ZMod 77636318761) ^ 14 = 65529892912 := by
        calc
          (31 : ZMod 77636318761) ^ 14 = (31 : ZMod 77636318761) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 7 * (31 : ZMod 77636318761) ^ 7 := by rw [pow_add]
          _ = 65529892912 := by rw [factor_2_2]; decide
      have factor_2_4 : (31 : ZMod 77636318761) ^ 28 = 18642527208 := by
        calc
          (31 : ZMod 77636318761) ^ 28 = (31 : ZMod 77636318761) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 14 * (31 : ZMod 77636318761) ^ 14 := by rw [pow_add]
          _ = 18642527208 := by rw [factor_2_3]; decide
      have factor_2_5 : (31 : ZMod 77636318761) ^ 57 = 60057169357 := by
        calc
          (31 : ZMod 77636318761) ^ 57 = (31 : ZMod 77636318761) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 28 * (31 : ZMod 77636318761) ^ 28) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 60057169357 := by rw [factor_2_4]; decide
      have factor_2_6 : (31 : ZMod 77636318761) ^ 115 = 44102503018 := by
        calc
          (31 : ZMod 77636318761) ^ 115 = (31 : ZMod 77636318761) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 57 * (31 : ZMod 77636318761) ^ 57) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 44102503018 := by rw [factor_2_5]; decide
      have factor_2_7 : (31 : ZMod 77636318761) ^ 231 = 33105568665 := by
        calc
          (31 : ZMod 77636318761) ^ 231 = (31 : ZMod 77636318761) ^ (115 + 115 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 115 * (31 : ZMod 77636318761) ^ 115) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 33105568665 := by rw [factor_2_6]; decide
      have factor_2_8 : (31 : ZMod 77636318761) ^ 462 = 45978938744 := by
        calc
          (31 : ZMod 77636318761) ^ 462 = (31 : ZMod 77636318761) ^ (231 + 231) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 231 * (31 : ZMod 77636318761) ^ 231 := by rw [pow_add]
          _ = 45978938744 := by rw [factor_2_7]; decide
      have factor_2_9 : (31 : ZMod 77636318761) ^ 925 = 50775878906 := by
        calc
          (31 : ZMod 77636318761) ^ 925 = (31 : ZMod 77636318761) ^ (462 + 462 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 462 * (31 : ZMod 77636318761) ^ 462) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 50775878906 := by rw [factor_2_8]; decide
      have factor_2_10 : (31 : ZMod 77636318761) ^ 1850 = 20163838584 := by
        calc
          (31 : ZMod 77636318761) ^ 1850 = (31 : ZMod 77636318761) ^ (925 + 925) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 925 * (31 : ZMod 77636318761) ^ 925 := by rw [pow_add]
          _ = 20163838584 := by rw [factor_2_9]; decide
      have factor_2_11 : (31 : ZMod 77636318761) ^ 3701 = 71204409508 := by
        calc
          (31 : ZMod 77636318761) ^ 3701 = (31 : ZMod 77636318761) ^ (1850 + 1850 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1850 * (31 : ZMod 77636318761) ^ 1850) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 71204409508 := by rw [factor_2_10]; decide
      have factor_2_12 : (31 : ZMod 77636318761) ^ 7403 = 51700804908 := by
        calc
          (31 : ZMod 77636318761) ^ 7403 = (31 : ZMod 77636318761) ^ (3701 + 3701 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 3701 * (31 : ZMod 77636318761) ^ 3701) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 51700804908 := by rw [factor_2_11]; decide
      have factor_2_13 : (31 : ZMod 77636318761) ^ 14807 = 29033053422 := by
        calc
          (31 : ZMod 77636318761) ^ 14807 = (31 : ZMod 77636318761) ^ (7403 + 7403 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 7403 * (31 : ZMod 77636318761) ^ 7403) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 29033053422 := by rw [factor_2_12]; decide
      have factor_2_14 : (31 : ZMod 77636318761) ^ 29615 = 28194181961 := by
        calc
          (31 : ZMod 77636318761) ^ 29615 = (31 : ZMod 77636318761) ^ (14807 + 14807 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 14807 * (31 : ZMod 77636318761) ^ 14807) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 28194181961 := by rw [factor_2_13]; decide
      have factor_2_15 : (31 : ZMod 77636318761) ^ 59231 = 25079037094 := by
        calc
          (31 : ZMod 77636318761) ^ 59231 = (31 : ZMod 77636318761) ^ (29615 + 29615 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 29615 * (31 : ZMod 77636318761) ^ 29615) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 25079037094 := by rw [factor_2_14]; decide
      have factor_2_16 : (31 : ZMod 77636318761) ^ 118463 = 62790710305 := by
        calc
          (31 : ZMod 77636318761) ^ 118463 = (31 : ZMod 77636318761) ^ (59231 + 59231 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 59231 * (31 : ZMod 77636318761) ^ 59231) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 62790710305 := by rw [factor_2_15]; decide
      have factor_2_17 : (31 : ZMod 77636318761) ^ 236927 = 29290953996 := by
        calc
          (31 : ZMod 77636318761) ^ 236927 = (31 : ZMod 77636318761) ^ (118463 + 118463 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 118463 * (31 : ZMod 77636318761) ^ 118463) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 29290953996 := by rw [factor_2_16]; decide
      have factor_2_18 : (31 : ZMod 77636318761) ^ 473854 = 6571203703 := by
        calc
          (31 : ZMod 77636318761) ^ 473854 = (31 : ZMod 77636318761) ^ (236927 + 236927) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 236927 * (31 : ZMod 77636318761) ^ 236927 := by rw [pow_add]
          _ = 6571203703 := by rw [factor_2_17]; decide
      have factor_2_19 : (31 : ZMod 77636318761) ^ 947708 = 69286297569 := by
        calc
          (31 : ZMod 77636318761) ^ 947708 = (31 : ZMod 77636318761) ^ (473854 + 473854) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 473854 * (31 : ZMod 77636318761) ^ 473854 := by rw [pow_add]
          _ = 69286297569 := by rw [factor_2_18]; decide
      have factor_2_20 : (31 : ZMod 77636318761) ^ 1895417 = 20893528061 := by
        calc
          (31 : ZMod 77636318761) ^ 1895417 = (31 : ZMod 77636318761) ^ (947708 + 947708 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 947708 * (31 : ZMod 77636318761) ^ 947708) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 20893528061 := by rw [factor_2_19]; decide
      have factor_2_21 : (31 : ZMod 77636318761) ^ 3790835 = 20198368618 := by
        calc
          (31 : ZMod 77636318761) ^ 3790835 = (31 : ZMod 77636318761) ^ (1895417 + 1895417 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1895417 * (31 : ZMod 77636318761) ^ 1895417) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 20198368618 := by rw [factor_2_20]; decide
      have factor_2_22 : (31 : ZMod 77636318761) ^ 7581671 = 13003604765 := by
        calc
          (31 : ZMod 77636318761) ^ 7581671 = (31 : ZMod 77636318761) ^ (3790835 + 3790835 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 3790835 * (31 : ZMod 77636318761) ^ 3790835) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 13003604765 := by rw [factor_2_21]; decide
      have factor_2_23 : (31 : ZMod 77636318761) ^ 15163343 = 47382303815 := by
        calc
          (31 : ZMod 77636318761) ^ 15163343 = (31 : ZMod 77636318761) ^ (7581671 + 7581671 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 7581671 * (31 : ZMod 77636318761) ^ 7581671) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 47382303815 := by rw [factor_2_22]; decide
      have factor_2_24 : (31 : ZMod 77636318761) ^ 30326687 = 41184354765 := by
        calc
          (31 : ZMod 77636318761) ^ 30326687 = (31 : ZMod 77636318761) ^ (15163343 + 15163343 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 15163343 * (31 : ZMod 77636318761) ^ 15163343) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 41184354765 := by rw [factor_2_23]; decide
      have factor_2_25 : (31 : ZMod 77636318761) ^ 60653374 = 34486301180 := by
        calc
          (31 : ZMod 77636318761) ^ 60653374 = (31 : ZMod 77636318761) ^ (30326687 + 30326687) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 30326687 * (31 : ZMod 77636318761) ^ 30326687 := by rw [pow_add]
          _ = 34486301180 := by rw [factor_2_24]; decide
      have factor_2_26 : (31 : ZMod 77636318761) ^ 121306748 = 13468101402 := by
        calc
          (31 : ZMod 77636318761) ^ 121306748 = (31 : ZMod 77636318761) ^ (60653374 + 60653374) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 60653374 * (31 : ZMod 77636318761) ^ 60653374 := by rw [pow_add]
          _ = 13468101402 := by rw [factor_2_25]; decide
      have factor_2_27 : (31 : ZMod 77636318761) ^ 242613496 = 62049797493 := by
        calc
          (31 : ZMod 77636318761) ^ 242613496 = (31 : ZMod 77636318761) ^ (121306748 + 121306748) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 121306748 * (31 : ZMod 77636318761) ^ 121306748 := by rw [pow_add]
          _ = 62049797493 := by rw [factor_2_26]; decide
      have factor_2_28 : (31 : ZMod 77636318761) ^ 485226992 = 21484829478 := by
        calc
          (31 : ZMod 77636318761) ^ 485226992 = (31 : ZMod 77636318761) ^ (242613496 + 242613496) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 242613496 * (31 : ZMod 77636318761) ^ 242613496 := by rw [pow_add]
          _ = 21484829478 := by rw [factor_2_27]; decide
      have factor_2_29 : (31 : ZMod 77636318761) ^ 970453984 = 14392826879 := by
        calc
          (31 : ZMod 77636318761) ^ 970453984 = (31 : ZMod 77636318761) ^ (485226992 + 485226992) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 485226992 * (31 : ZMod 77636318761) ^ 485226992 := by rw [pow_add]
          _ = 14392826879 := by rw [factor_2_28]; decide
      have factor_2_30 : (31 : ZMod 77636318761) ^ 1940907969 = 36222839789 := by
        calc
          (31 : ZMod 77636318761) ^ 1940907969 = (31 : ZMod 77636318761) ^ (970453984 + 970453984 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 970453984 * (31 : ZMod 77636318761) ^ 970453984) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 36222839789 := by rw [factor_2_29]; decide
      have factor_2_31 : (31 : ZMod 77636318761) ^ 3881815938 = 67976155820 := by
        calc
          (31 : ZMod 77636318761) ^ 3881815938 = (31 : ZMod 77636318761) ^ (1940907969 + 1940907969) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1940907969 * (31 : ZMod 77636318761) ^ 1940907969 := by rw [pow_add]
          _ = 67976155820 := by rw [factor_2_30]; decide
      have factor_2_32 : (31 : ZMod 77636318761) ^ 7763631876 = 34067659661 := by
        calc
          (31 : ZMod 77636318761) ^ 7763631876 = (31 : ZMod 77636318761) ^ (3881815938 + 3881815938) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 3881815938 * (31 : ZMod 77636318761) ^ 3881815938 := by rw [pow_add]
          _ = 34067659661 := by rw [factor_2_31]; decide
      have factor_2_33 : (31 : ZMod 77636318761) ^ 15527263752 = 64431779990 := by
        calc
          (31 : ZMod 77636318761) ^ 15527263752 = (31 : ZMod 77636318761) ^ (7763631876 + 7763631876) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 7763631876 * (31 : ZMod 77636318761) ^ 7763631876 := by rw [pow_add]
          _ = 64431779990 := by rw [factor_2_32]; decide
      change (31 : ZMod 77636318761) ^ 15527263752 ≠ 1
      rw [factor_2_33]
      decide
    ·
      have factor_3_0 : (31 : ZMod 77636318761) ^ 1 = 31 := by norm_num
      have factor_3_1 : (31 : ZMod 77636318761) ^ 2 = 961 := by
        calc
          (31 : ZMod 77636318761) ^ 2 = (31 : ZMod 77636318761) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1 * (31 : ZMod 77636318761) ^ 1 := by rw [pow_add]
          _ = 961 := by rw [factor_3_0]; decide
      have factor_3_2 : (31 : ZMod 77636318761) ^ 5 = 28629151 := by
        calc
          (31 : ZMod 77636318761) ^ 5 = (31 : ZMod 77636318761) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 2 * (31 : ZMod 77636318761) ^ 2) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 28629151 := by rw [factor_3_1]; decide
      have factor_3_3 : (31 : ZMod 77636318761) ^ 10 = 21669820924 := by
        calc
          (31 : ZMod 77636318761) ^ 10 = (31 : ZMod 77636318761) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 5 * (31 : ZMod 77636318761) ^ 5 := by rw [pow_add]
          _ = 21669820924 := by rw [factor_3_2]; decide
      have factor_3_4 : (31 : ZMod 77636318761) ^ 20 = 6358278798 := by
        calc
          (31 : ZMod 77636318761) ^ 20 = (31 : ZMod 77636318761) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 10 * (31 : ZMod 77636318761) ^ 10 := by rw [pow_add]
          _ = 6358278798 := by rw [factor_3_3]; decide
      have factor_3_5 : (31 : ZMod 77636318761) ^ 41 = 17047315707 := by
        calc
          (31 : ZMod 77636318761) ^ 41 = (31 : ZMod 77636318761) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 20 * (31 : ZMod 77636318761) ^ 20) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 17047315707 := by rw [factor_3_4]; decide
      have factor_3_6 : (31 : ZMod 77636318761) ^ 82 = 44425989175 := by
        calc
          (31 : ZMod 77636318761) ^ 82 = (31 : ZMod 77636318761) ^ (41 + 41) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 41 * (31 : ZMod 77636318761) ^ 41 := by rw [pow_add]
          _ = 44425989175 := by rw [factor_3_5]; decide
      have factor_3_7 : (31 : ZMod 77636318761) ^ 165 = 49099958330 := by
        calc
          (31 : ZMod 77636318761) ^ 165 = (31 : ZMod 77636318761) ^ (82 + 82 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 82 * (31 : ZMod 77636318761) ^ 82) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 49099958330 := by rw [factor_3_6]; decide
      have factor_3_8 : (31 : ZMod 77636318761) ^ 330 = 65801473957 := by
        calc
          (31 : ZMod 77636318761) ^ 330 = (31 : ZMod 77636318761) ^ (165 + 165) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 165 * (31 : ZMod 77636318761) ^ 165 := by rw [pow_add]
          _ = 65801473957 := by rw [factor_3_7]; decide
      have factor_3_9 : (31 : ZMod 77636318761) ^ 661 = 25248570661 := by
        calc
          (31 : ZMod 77636318761) ^ 661 = (31 : ZMod 77636318761) ^ (330 + 330 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 330 * (31 : ZMod 77636318761) ^ 330) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 25248570661 := by rw [factor_3_8]; decide
      have factor_3_10 : (31 : ZMod 77636318761) ^ 1322 = 53636410980 := by
        calc
          (31 : ZMod 77636318761) ^ 1322 = (31 : ZMod 77636318761) ^ (661 + 661) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 661 * (31 : ZMod 77636318761) ^ 661 := by rw [pow_add]
          _ = 53636410980 := by rw [factor_3_9]; decide
      have factor_3_11 : (31 : ZMod 77636318761) ^ 2644 = 49422376502 := by
        calc
          (31 : ZMod 77636318761) ^ 2644 = (31 : ZMod 77636318761) ^ (1322 + 1322) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1322 * (31 : ZMod 77636318761) ^ 1322 := by rw [pow_add]
          _ = 49422376502 := by rw [factor_3_10]; decide
      have factor_3_12 : (31 : ZMod 77636318761) ^ 5288 = 59818571453 := by
        calc
          (31 : ZMod 77636318761) ^ 5288 = (31 : ZMod 77636318761) ^ (2644 + 2644) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 2644 * (31 : ZMod 77636318761) ^ 2644 := by rw [pow_add]
          _ = 59818571453 := by rw [factor_3_11]; decide
      have factor_3_13 : (31 : ZMod 77636318761) ^ 10577 = 49335441706 := by
        calc
          (31 : ZMod 77636318761) ^ 10577 = (31 : ZMod 77636318761) ^ (5288 + 5288 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 5288 * (31 : ZMod 77636318761) ^ 5288) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 49335441706 := by rw [factor_3_12]; decide
      have factor_3_14 : (31 : ZMod 77636318761) ^ 21154 = 3368139495 := by
        calc
          (31 : ZMod 77636318761) ^ 21154 = (31 : ZMod 77636318761) ^ (10577 + 10577) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 10577 * (31 : ZMod 77636318761) ^ 10577 := by rw [pow_add]
          _ = 3368139495 := by rw [factor_3_13]; decide
      have factor_3_15 : (31 : ZMod 77636318761) ^ 42308 = 46323364521 := by
        calc
          (31 : ZMod 77636318761) ^ 42308 = (31 : ZMod 77636318761) ^ (21154 + 21154) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 21154 * (31 : ZMod 77636318761) ^ 21154 := by rw [pow_add]
          _ = 46323364521 := by rw [factor_3_14]; decide
      have factor_3_16 : (31 : ZMod 77636318761) ^ 84616 = 4544682629 := by
        calc
          (31 : ZMod 77636318761) ^ 84616 = (31 : ZMod 77636318761) ^ (42308 + 42308) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 42308 * (31 : ZMod 77636318761) ^ 42308 := by rw [pow_add]
          _ = 4544682629 := by rw [factor_3_15]; decide
      have factor_3_17 : (31 : ZMod 77636318761) ^ 169233 = 64026628731 := by
        calc
          (31 : ZMod 77636318761) ^ 169233 = (31 : ZMod 77636318761) ^ (84616 + 84616 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 84616 * (31 : ZMod 77636318761) ^ 84616) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 64026628731 := by rw [factor_3_16]; decide
      have factor_3_18 : (31 : ZMod 77636318761) ^ 338467 = 14567475146 := by
        calc
          (31 : ZMod 77636318761) ^ 338467 = (31 : ZMod 77636318761) ^ (169233 + 169233 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 169233 * (31 : ZMod 77636318761) ^ 169233) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 14567475146 := by rw [factor_3_17]; decide
      have factor_3_19 : (31 : ZMod 77636318761) ^ 676934 = 37045646623 := by
        calc
          (31 : ZMod 77636318761) ^ 676934 = (31 : ZMod 77636318761) ^ (338467 + 338467) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 338467 * (31 : ZMod 77636318761) ^ 338467 := by rw [pow_add]
          _ = 37045646623 := by rw [factor_3_18]; decide
      have factor_3_20 : (31 : ZMod 77636318761) ^ 1353869 = 71232544124 := by
        calc
          (31 : ZMod 77636318761) ^ 1353869 = (31 : ZMod 77636318761) ^ (676934 + 676934 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 676934 * (31 : ZMod 77636318761) ^ 676934) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 71232544124 := by rw [factor_3_19]; decide
      have factor_3_21 : (31 : ZMod 77636318761) ^ 2707739 = 47363156687 := by
        calc
          (31 : ZMod 77636318761) ^ 2707739 = (31 : ZMod 77636318761) ^ (1353869 + 1353869 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1353869 * (31 : ZMod 77636318761) ^ 1353869) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 47363156687 := by rw [factor_3_20]; decide
      have factor_3_22 : (31 : ZMod 77636318761) ^ 5415479 = 56494677406 := by
        calc
          (31 : ZMod 77636318761) ^ 5415479 = (31 : ZMod 77636318761) ^ (2707739 + 2707739 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 2707739 * (31 : ZMod 77636318761) ^ 2707739) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 56494677406 := by rw [factor_3_21]; decide
      have factor_3_23 : (31 : ZMod 77636318761) ^ 10830959 = 69812837763 := by
        calc
          (31 : ZMod 77636318761) ^ 10830959 = (31 : ZMod 77636318761) ^ (5415479 + 5415479 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 5415479 * (31 : ZMod 77636318761) ^ 5415479) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 69812837763 := by rw [factor_3_22]; decide
      have factor_3_24 : (31 : ZMod 77636318761) ^ 21661919 = 70183053782 := by
        calc
          (31 : ZMod 77636318761) ^ 21661919 = (31 : ZMod 77636318761) ^ (10830959 + 10830959 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 10830959 * (31 : ZMod 77636318761) ^ 10830959) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 70183053782 := by rw [factor_3_23]; decide
      have factor_3_25 : (31 : ZMod 77636318761) ^ 43323838 = 52518396759 := by
        calc
          (31 : ZMod 77636318761) ^ 43323838 = (31 : ZMod 77636318761) ^ (21661919 + 21661919) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 21661919 * (31 : ZMod 77636318761) ^ 21661919 := by rw [pow_add]
          _ = 52518396759 := by rw [factor_3_24]; decide
      have factor_3_26 : (31 : ZMod 77636318761) ^ 86647677 = 48393180329 := by
        calc
          (31 : ZMod 77636318761) ^ 86647677 = (31 : ZMod 77636318761) ^ (43323838 + 43323838 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 43323838 * (31 : ZMod 77636318761) ^ 43323838) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 48393180329 := by rw [factor_3_25]; decide
      have factor_3_27 : (31 : ZMod 77636318761) ^ 173295354 = 50475324093 := by
        calc
          (31 : ZMod 77636318761) ^ 173295354 = (31 : ZMod 77636318761) ^ (86647677 + 86647677) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 86647677 * (31 : ZMod 77636318761) ^ 86647677 := by rw [pow_add]
          _ = 50475324093 := by rw [factor_3_26]; decide
      have factor_3_28 : (31 : ZMod 77636318761) ^ 346590708 = 54003085117 := by
        calc
          (31 : ZMod 77636318761) ^ 346590708 = (31 : ZMod 77636318761) ^ (173295354 + 173295354) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 173295354 * (31 : ZMod 77636318761) ^ 173295354 := by rw [pow_add]
          _ = 54003085117 := by rw [factor_3_27]; decide
      have factor_3_29 : (31 : ZMod 77636318761) ^ 693181417 = 33078658566 := by
        calc
          (31 : ZMod 77636318761) ^ 693181417 = (31 : ZMod 77636318761) ^ (346590708 + 346590708 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 346590708 * (31 : ZMod 77636318761) ^ 346590708) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 33078658566 := by rw [factor_3_28]; decide
      have factor_3_30 : (31 : ZMod 77636318761) ^ 1386362835 = 37165471416 := by
        calc
          (31 : ZMod 77636318761) ^ 1386362835 = (31 : ZMod 77636318761) ^ (693181417 + 693181417 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 693181417 * (31 : ZMod 77636318761) ^ 693181417) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 37165471416 := by rw [factor_3_29]; decide
      have factor_3_31 : (31 : ZMod 77636318761) ^ 2772725670 = 45749156153 := by
        calc
          (31 : ZMod 77636318761) ^ 2772725670 = (31 : ZMod 77636318761) ^ (1386362835 + 1386362835) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1386362835 * (31 : ZMod 77636318761) ^ 1386362835 := by rw [pow_add]
          _ = 45749156153 := by rw [factor_3_30]; decide
      have factor_3_32 : (31 : ZMod 77636318761) ^ 5545451340 = 40892079563 := by
        calc
          (31 : ZMod 77636318761) ^ 5545451340 = (31 : ZMod 77636318761) ^ (2772725670 + 2772725670) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 2772725670 * (31 : ZMod 77636318761) ^ 2772725670 := by rw [pow_add]
          _ = 40892079563 := by rw [factor_3_31]; decide
      have factor_3_33 : (31 : ZMod 77636318761) ^ 11090902680 = 69211434221 := by
        calc
          (31 : ZMod 77636318761) ^ 11090902680 = (31 : ZMod 77636318761) ^ (5545451340 + 5545451340) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 5545451340 * (31 : ZMod 77636318761) ^ 5545451340 := by rw [pow_add]
          _ = 69211434221 := by rw [factor_3_32]; decide
      change (31 : ZMod 77636318761) ^ 11090902680 ≠ 1
      rw [factor_3_33]
      decide
    ·
      have factor_4_0 : (31 : ZMod 77636318761) ^ 1 = 31 := by norm_num
      have factor_4_1 : (31 : ZMod 77636318761) ^ 3 = 29791 := by
        calc
          (31 : ZMod 77636318761) ^ 3 = (31 : ZMod 77636318761) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1 * (31 : ZMod 77636318761) ^ 1) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 29791 := by rw [factor_4_0]; decide
      have factor_4_2 : (31 : ZMod 77636318761) ^ 6 = 887503681 := by
        calc
          (31 : ZMod 77636318761) ^ 6 = (31 : ZMod 77636318761) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 3 * (31 : ZMod 77636318761) ^ 3 := by rw [pow_add]
          _ = 887503681 := by rw [factor_4_1]; decide
      have factor_4_3 : (31 : ZMod 77636318761) ^ 13 = 19644649169 := by
        calc
          (31 : ZMod 77636318761) ^ 13 = (31 : ZMod 77636318761) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 6 * (31 : ZMod 77636318761) ^ 6) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 19644649169 := by rw [factor_4_2]; decide
      have factor_4_4 : (31 : ZMod 77636318761) ^ 26 = 8905970438 := by
        calc
          (31 : ZMod 77636318761) ^ 26 = (31 : ZMod 77636318761) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 13 * (31 : ZMod 77636318761) ^ 13 := by rw [pow_add]
          _ = 8905970438 := by rw [factor_4_3]; decide
      have factor_4_5 : (31 : ZMod 77636318761) ^ 52 = 57689405248 := by
        calc
          (31 : ZMod 77636318761) ^ 52 = (31 : ZMod 77636318761) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 26 * (31 : ZMod 77636318761) ^ 26 := by rw [pow_add]
          _ = 57689405248 := by rw [factor_4_4]; decide
      have factor_4_6 : (31 : ZMod 77636318761) ^ 105 = 27070943703 := by
        calc
          (31 : ZMod 77636318761) ^ 105 = (31 : ZMod 77636318761) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 52 * (31 : ZMod 77636318761) ^ 52) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 27070943703 := by rw [factor_4_5]; decide
      have factor_4_7 : (31 : ZMod 77636318761) ^ 210 = 3577657825 := by
        calc
          (31 : ZMod 77636318761) ^ 210 = (31 : ZMod 77636318761) ^ (105 + 105) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 105 * (31 : ZMod 77636318761) ^ 105 := by rw [pow_add]
          _ = 3577657825 := by rw [factor_4_6]; decide
      have factor_4_8 : (31 : ZMod 77636318761) ^ 420 = 67959360591 := by
        calc
          (31 : ZMod 77636318761) ^ 420 = (31 : ZMod 77636318761) ^ (210 + 210) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 210 * (31 : ZMod 77636318761) ^ 210 := by rw [pow_add]
          _ = 67959360591 := by rw [factor_4_7]; decide
      have factor_4_9 : (31 : ZMod 77636318761) ^ 841 = 66251063898 := by
        calc
          (31 : ZMod 77636318761) ^ 841 = (31 : ZMod 77636318761) ^ (420 + 420 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 420 * (31 : ZMod 77636318761) ^ 420) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 66251063898 := by rw [factor_4_8]; decide
      have factor_4_10 : (31 : ZMod 77636318761) ^ 1682 = 9504416903 := by
        calc
          (31 : ZMod 77636318761) ^ 1682 = (31 : ZMod 77636318761) ^ (841 + 841) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 841 * (31 : ZMod 77636318761) ^ 841 := by rw [pow_add]
          _ = 9504416903 := by rw [factor_4_9]; decide
      have factor_4_11 : (31 : ZMod 77636318761) ^ 3365 = 63224604073 := by
        calc
          (31 : ZMod 77636318761) ^ 3365 = (31 : ZMod 77636318761) ^ (1682 + 1682 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1682 * (31 : ZMod 77636318761) ^ 1682) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 63224604073 := by rw [factor_4_10]; decide
      have factor_4_12 : (31 : ZMod 77636318761) ^ 6730 = 62594582799 := by
        calc
          (31 : ZMod 77636318761) ^ 6730 = (31 : ZMod 77636318761) ^ (3365 + 3365) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 3365 * (31 : ZMod 77636318761) ^ 3365 := by rw [pow_add]
          _ = 62594582799 := by rw [factor_4_11]; decide
      have factor_4_13 : (31 : ZMod 77636318761) ^ 13461 = 18715396374 := by
        calc
          (31 : ZMod 77636318761) ^ 13461 = (31 : ZMod 77636318761) ^ (6730 + 6730 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 6730 * (31 : ZMod 77636318761) ^ 6730) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 18715396374 := by rw [factor_4_12]; decide
      have factor_4_14 : (31 : ZMod 77636318761) ^ 26923 = 56239898828 := by
        calc
          (31 : ZMod 77636318761) ^ 26923 = (31 : ZMod 77636318761) ^ (13461 + 13461 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 13461 * (31 : ZMod 77636318761) ^ 13461) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 56239898828 := by rw [factor_4_13]; decide
      have factor_4_15 : (31 : ZMod 77636318761) ^ 53847 = 40550836429 := by
        calc
          (31 : ZMod 77636318761) ^ 53847 = (31 : ZMod 77636318761) ^ (26923 + 26923 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 26923 * (31 : ZMod 77636318761) ^ 26923) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 40550836429 := by rw [factor_4_14]; decide
      have factor_4_16 : (31 : ZMod 77636318761) ^ 107694 = 73031694207 := by
        calc
          (31 : ZMod 77636318761) ^ 107694 = (31 : ZMod 77636318761) ^ (53847 + 53847) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 53847 * (31 : ZMod 77636318761) ^ 53847 := by rw [pow_add]
          _ = 73031694207 := by rw [factor_4_15]; decide
      have factor_4_17 : (31 : ZMod 77636318761) ^ 215388 = 46630892615 := by
        calc
          (31 : ZMod 77636318761) ^ 215388 = (31 : ZMod 77636318761) ^ (107694 + 107694) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 107694 * (31 : ZMod 77636318761) ^ 107694 := by rw [pow_add]
          _ = 46630892615 := by rw [factor_4_16]; decide
      have factor_4_18 : (31 : ZMod 77636318761) ^ 430776 = 28259373907 := by
        calc
          (31 : ZMod 77636318761) ^ 430776 = (31 : ZMod 77636318761) ^ (215388 + 215388) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 215388 * (31 : ZMod 77636318761) ^ 215388 := by rw [pow_add]
          _ = 28259373907 := by rw [factor_4_17]; decide
      have factor_4_19 : (31 : ZMod 77636318761) ^ 861553 = 6423244169 := by
        calc
          (31 : ZMod 77636318761) ^ 861553 = (31 : ZMod 77636318761) ^ (430776 + 430776 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 430776 * (31 : ZMod 77636318761) ^ 430776) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 6423244169 := by rw [factor_4_18]; decide
      have factor_4_20 : (31 : ZMod 77636318761) ^ 1723107 = 70457205019 := by
        calc
          (31 : ZMod 77636318761) ^ 1723107 = (31 : ZMod 77636318761) ^ (861553 + 861553 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 861553 * (31 : ZMod 77636318761) ^ 861553) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 70457205019 := by rw [factor_4_19]; decide
      have factor_4_21 : (31 : ZMod 77636318761) ^ 3446214 = 64638941170 := by
        calc
          (31 : ZMod 77636318761) ^ 3446214 = (31 : ZMod 77636318761) ^ (1723107 + 1723107) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1723107 * (31 : ZMod 77636318761) ^ 1723107 := by rw [pow_add]
          _ = 64638941170 := by rw [factor_4_20]; decide
      have factor_4_22 : (31 : ZMod 77636318761) ^ 6892428 = 74315312898 := by
        calc
          (31 : ZMod 77636318761) ^ 6892428 = (31 : ZMod 77636318761) ^ (3446214 + 3446214) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 3446214 * (31 : ZMod 77636318761) ^ 3446214 := by rw [pow_add]
          _ = 74315312898 := by rw [factor_4_21]; decide
      have factor_4_23 : (31 : ZMod 77636318761) ^ 13784857 = 19920787045 := by
        calc
          (31 : ZMod 77636318761) ^ 13784857 = (31 : ZMod 77636318761) ^ (6892428 + 6892428 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 6892428 * (31 : ZMod 77636318761) ^ 6892428) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 19920787045 := by rw [factor_4_22]; decide
      have factor_4_24 : (31 : ZMod 77636318761) ^ 27569715 = 48625496476 := by
        calc
          (31 : ZMod 77636318761) ^ 27569715 = (31 : ZMod 77636318761) ^ (13784857 + 13784857 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 13784857 * (31 : ZMod 77636318761) ^ 13784857) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 48625496476 := by rw [factor_4_23]; decide
      have factor_4_25 : (31 : ZMod 77636318761) ^ 55139430 = 38852395725 := by
        calc
          (31 : ZMod 77636318761) ^ 55139430 = (31 : ZMod 77636318761) ^ (27569715 + 27569715) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 27569715 * (31 : ZMod 77636318761) ^ 27569715 := by rw [pow_add]
          _ = 38852395725 := by rw [factor_4_24]; decide
      have factor_4_26 : (31 : ZMod 77636318761) ^ 110278861 = 71874728231 := by
        calc
          (31 : ZMod 77636318761) ^ 110278861 = (31 : ZMod 77636318761) ^ (55139430 + 55139430 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 55139430 * (31 : ZMod 77636318761) ^ 55139430) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 71874728231 := by rw [factor_4_25]; decide
      have factor_4_27 : (31 : ZMod 77636318761) ^ 220557723 = 46558744769 := by
        calc
          (31 : ZMod 77636318761) ^ 220557723 = (31 : ZMod 77636318761) ^ (110278861 + 110278861 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 110278861 * (31 : ZMod 77636318761) ^ 110278861) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 46558744769 := by rw [factor_4_26]; decide
      have factor_4_28 : (31 : ZMod 77636318761) ^ 441115447 = 18025269154 := by
        calc
          (31 : ZMod 77636318761) ^ 441115447 = (31 : ZMod 77636318761) ^ (220557723 + 220557723 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 220557723 * (31 : ZMod 77636318761) ^ 220557723) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 18025269154 := by rw [factor_4_27]; decide
      have factor_4_29 : (31 : ZMod 77636318761) ^ 882230895 = 33220995372 := by
        calc
          (31 : ZMod 77636318761) ^ 882230895 = (31 : ZMod 77636318761) ^ (441115447 + 441115447 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 441115447 * (31 : ZMod 77636318761) ^ 441115447) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 33220995372 := by rw [factor_4_28]; decide
      have factor_4_30 : (31 : ZMod 77636318761) ^ 1764461790 = 13907451386 := by
        calc
          (31 : ZMod 77636318761) ^ 1764461790 = (31 : ZMod 77636318761) ^ (882230895 + 882230895) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 882230895 * (31 : ZMod 77636318761) ^ 882230895 := by rw [pow_add]
          _ = 13907451386 := by rw [factor_4_29]; decide
      have factor_4_31 : (31 : ZMod 77636318761) ^ 3528923580 = 38466634856 := by
        calc
          (31 : ZMod 77636318761) ^ 3528923580 = (31 : ZMod 77636318761) ^ (1764461790 + 1764461790) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1764461790 * (31 : ZMod 77636318761) ^ 1764461790 := by rw [pow_add]
          _ = 38466634856 := by rw [factor_4_30]; decide
      have factor_4_32 : (31 : ZMod 77636318761) ^ 7057847160 = 13341519565 := by
        calc
          (31 : ZMod 77636318761) ^ 7057847160 = (31 : ZMod 77636318761) ^ (3528923580 + 3528923580) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 3528923580 * (31 : ZMod 77636318761) ^ 3528923580 := by rw [pow_add]
          _ = 13341519565 := by rw [factor_4_31]; decide
      change (31 : ZMod 77636318761) ^ 7057847160 ≠ 1
      rw [factor_4_32]
      decide
    ·
      have factor_5_0 : (31 : ZMod 77636318761) ^ 1 = 31 := by norm_num
      have factor_5_1 : (31 : ZMod 77636318761) ^ 2 = 961 := by
        calc
          (31 : ZMod 77636318761) ^ 2 = (31 : ZMod 77636318761) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1 * (31 : ZMod 77636318761) ^ 1 := by rw [pow_add]
          _ = 961 := by rw [factor_5_0]; decide
      have factor_5_2 : (31 : ZMod 77636318761) ^ 5 = 28629151 := by
        calc
          (31 : ZMod 77636318761) ^ 5 = (31 : ZMod 77636318761) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 2 * (31 : ZMod 77636318761) ^ 2) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 28629151 := by rw [factor_5_1]; decide
      have factor_5_3 : (31 : ZMod 77636318761) ^ 11 = 50673898556 := by
        calc
          (31 : ZMod 77636318761) ^ 11 = (31 : ZMod 77636318761) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 5 * (31 : ZMod 77636318761) ^ 5) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 50673898556 := by rw [factor_5_2]; decide
      have factor_5_4 : (31 : ZMod 77636318761) ^ 22 = 54673061520 := by
        calc
          (31 : ZMod 77636318761) ^ 22 = (31 : ZMod 77636318761) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 11 * (31 : ZMod 77636318761) ^ 11 := by rw [pow_add]
          _ = 54673061520 := by rw [factor_5_3]; decide
      have factor_5_5 : (31 : ZMod 77636318761) ^ 44 = 37421211536 := by
        calc
          (31 : ZMod 77636318761) ^ 44 = (31 : ZMod 77636318761) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 22 * (31 : ZMod 77636318761) ^ 22 := by rw [pow_add]
          _ = 37421211536 := by rw [factor_5_4]; decide
      have factor_5_6 : (31 : ZMod 77636318761) ^ 88 = 13193008452 := by
        calc
          (31 : ZMod 77636318761) ^ 88 = (31 : ZMod 77636318761) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 44 * (31 : ZMod 77636318761) ^ 44 := by rw [pow_add]
          _ = 13193008452 := by rw [factor_5_5]; decide
      have factor_5_7 : (31 : ZMod 77636318761) ^ 177 = 22914847303 := by
        calc
          (31 : ZMod 77636318761) ^ 177 = (31 : ZMod 77636318761) ^ (88 + 88 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 88 * (31 : ZMod 77636318761) ^ 88) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 22914847303 := by rw [factor_5_6]; decide
      have factor_5_8 : (31 : ZMod 77636318761) ^ 355 = 38698587130 := by
        calc
          (31 : ZMod 77636318761) ^ 355 = (31 : ZMod 77636318761) ^ (177 + 177 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 177 * (31 : ZMod 77636318761) ^ 177) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 38698587130 := by rw [factor_5_7]; decide
      have factor_5_9 : (31 : ZMod 77636318761) ^ 711 = 53379727061 := by
        calc
          (31 : ZMod 77636318761) ^ 711 = (31 : ZMod 77636318761) ^ (355 + 355 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 355 * (31 : ZMod 77636318761) ^ 355) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 53379727061 := by rw [factor_5_8]; decide
      have factor_5_10 : (31 : ZMod 77636318761) ^ 1423 = 44495877628 := by
        calc
          (31 : ZMod 77636318761) ^ 1423 = (31 : ZMod 77636318761) ^ (711 + 711 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 711 * (31 : ZMod 77636318761) ^ 711) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 44495877628 := by rw [factor_5_9]; decide
      have factor_5_11 : (31 : ZMod 77636318761) ^ 2847 = 57157428179 := by
        calc
          (31 : ZMod 77636318761) ^ 2847 = (31 : ZMod 77636318761) ^ (1423 + 1423 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1423 * (31 : ZMod 77636318761) ^ 1423) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 57157428179 := by rw [factor_5_10]; decide
      have factor_5_12 : (31 : ZMod 77636318761) ^ 5695 = 20770972436 := by
        calc
          (31 : ZMod 77636318761) ^ 5695 = (31 : ZMod 77636318761) ^ (2847 + 2847 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 2847 * (31 : ZMod 77636318761) ^ 2847) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 20770972436 := by rw [factor_5_11]; decide
      have factor_5_13 : (31 : ZMod 77636318761) ^ 11390 = 44249195741 := by
        calc
          (31 : ZMod 77636318761) ^ 11390 = (31 : ZMod 77636318761) ^ (5695 + 5695) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 5695 * (31 : ZMod 77636318761) ^ 5695 := by rw [pow_add]
          _ = 44249195741 := by rw [factor_5_12]; decide
      have factor_5_14 : (31 : ZMod 77636318761) ^ 22781 = 5668145885 := by
        calc
          (31 : ZMod 77636318761) ^ 22781 = (31 : ZMod 77636318761) ^ (11390 + 11390 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 11390 * (31 : ZMod 77636318761) ^ 11390) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 5668145885 := by rw [factor_5_13]; decide
      have factor_5_15 : (31 : ZMod 77636318761) ^ 45562 = 58024216743 := by
        calc
          (31 : ZMod 77636318761) ^ 45562 = (31 : ZMod 77636318761) ^ (22781 + 22781) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 22781 * (31 : ZMod 77636318761) ^ 22781 := by rw [pow_add]
          _ = 58024216743 := by rw [factor_5_14]; decide
      have factor_5_16 : (31 : ZMod 77636318761) ^ 91125 = 36757475528 := by
        calc
          (31 : ZMod 77636318761) ^ 91125 = (31 : ZMod 77636318761) ^ (45562 + 45562 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 45562 * (31 : ZMod 77636318761) ^ 45562) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 36757475528 := by rw [factor_5_15]; decide
      have factor_5_17 : (31 : ZMod 77636318761) ^ 182251 = 39244367170 := by
        calc
          (31 : ZMod 77636318761) ^ 182251 = (31 : ZMod 77636318761) ^ (91125 + 91125 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 91125 * (31 : ZMod 77636318761) ^ 91125) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 39244367170 := by rw [factor_5_16]; decide
      have factor_5_18 : (31 : ZMod 77636318761) ^ 364503 = 77127675180 := by
        calc
          (31 : ZMod 77636318761) ^ 364503 = (31 : ZMod 77636318761) ^ (182251 + 182251 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 182251 * (31 : ZMod 77636318761) ^ 182251) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 77127675180 := by rw [factor_5_17]; decide
      have factor_5_19 : (31 : ZMod 77636318761) ^ 729006 = 73673234243 := by
        calc
          (31 : ZMod 77636318761) ^ 729006 = (31 : ZMod 77636318761) ^ (364503 + 364503) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 364503 * (31 : ZMod 77636318761) ^ 364503 := by rw [pow_add]
          _ = 73673234243 := by rw [factor_5_18]; decide
      have factor_5_20 : (31 : ZMod 77636318761) ^ 1458013 = 74537051349 := by
        calc
          (31 : ZMod 77636318761) ^ 1458013 = (31 : ZMod 77636318761) ^ (729006 + 729006 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 729006 * (31 : ZMod 77636318761) ^ 729006) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 74537051349 := by rw [factor_5_19]; decide
      have factor_5_21 : (31 : ZMod 77636318761) ^ 2916027 = 54999971297 := by
        calc
          (31 : ZMod 77636318761) ^ 2916027 = (31 : ZMod 77636318761) ^ (1458013 + 1458013 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1458013 * (31 : ZMod 77636318761) ^ 1458013) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 54999971297 := by rw [factor_5_20]; decide
      have factor_5_22 : (31 : ZMod 77636318761) ^ 5832055 = 65738317798 := by
        calc
          (31 : ZMod 77636318761) ^ 5832055 = (31 : ZMod 77636318761) ^ (2916027 + 2916027 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 2916027 * (31 : ZMod 77636318761) ^ 2916027) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 65738317798 := by rw [factor_5_21]; decide
      have factor_5_23 : (31 : ZMod 77636318761) ^ 11664110 = 26406044650 := by
        calc
          (31 : ZMod 77636318761) ^ 11664110 = (31 : ZMod 77636318761) ^ (5832055 + 5832055) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 5832055 * (31 : ZMod 77636318761) ^ 5832055 := by rw [pow_add]
          _ = 26406044650 := by rw [factor_5_22]; decide
      have factor_5_24 : (31 : ZMod 77636318761) ^ 23328220 = 17826463136 := by
        calc
          (31 : ZMod 77636318761) ^ 23328220 = (31 : ZMod 77636318761) ^ (11664110 + 11664110) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 11664110 * (31 : ZMod 77636318761) ^ 11664110 := by rw [pow_add]
          _ = 17826463136 := by rw [factor_5_23]; decide
      have factor_5_25 : (31 : ZMod 77636318761) ^ 46656441 = 64109173212 := by
        calc
          (31 : ZMod 77636318761) ^ 46656441 = (31 : ZMod 77636318761) ^ (23328220 + 23328220 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 23328220 * (31 : ZMod 77636318761) ^ 23328220) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 64109173212 := by rw [factor_5_24]; decide
      have factor_5_26 : (31 : ZMod 77636318761) ^ 93312883 = 26354096110 := by
        calc
          (31 : ZMod 77636318761) ^ 93312883 = (31 : ZMod 77636318761) ^ (46656441 + 46656441 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 46656441 * (31 : ZMod 77636318761) ^ 46656441) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 26354096110 := by rw [factor_5_25]; decide
      have factor_5_27 : (31 : ZMod 77636318761) ^ 186625766 = 9268639439 := by
        calc
          (31 : ZMod 77636318761) ^ 186625766 = (31 : ZMod 77636318761) ^ (93312883 + 93312883) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 93312883 * (31 : ZMod 77636318761) ^ 93312883 := by rw [pow_add]
          _ = 9268639439 := by rw [factor_5_26]; decide
      have factor_5_28 : (31 : ZMod 77636318761) ^ 373251532 = 27471453116 := by
        calc
          (31 : ZMod 77636318761) ^ 373251532 = (31 : ZMod 77636318761) ^ (186625766 + 186625766) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 186625766 * (31 : ZMod 77636318761) ^ 186625766 := by rw [pow_add]
          _ = 27471453116 := by rw [factor_5_27]; decide
      have factor_5_29 : (31 : ZMod 77636318761) ^ 746503065 = 64220320891 := by
        calc
          (31 : ZMod 77636318761) ^ 746503065 = (31 : ZMod 77636318761) ^ (373251532 + 373251532 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 373251532 * (31 : ZMod 77636318761) ^ 373251532) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 64220320891 := by rw [factor_5_28]; decide
      have factor_5_30 : (31 : ZMod 77636318761) ^ 1493006130 = 77310699251 := by
        calc
          (31 : ZMod 77636318761) ^ 1493006130 = (31 : ZMod 77636318761) ^ (746503065 + 746503065) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 746503065 * (31 : ZMod 77636318761) ^ 746503065 := by rw [pow_add]
          _ = 77310699251 := by rw [factor_5_29]; decide
      have factor_5_31 : (31 : ZMod 77636318761) ^ 2986012260 = 67124423639 := by
        calc
          (31 : ZMod 77636318761) ^ 2986012260 = (31 : ZMod 77636318761) ^ (1493006130 + 1493006130) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1493006130 * (31 : ZMod 77636318761) ^ 1493006130 := by rw [pow_add]
          _ = 67124423639 := by rw [factor_5_30]; decide
      have factor_5_32 : (31 : ZMod 77636318761) ^ 5972024520 = 33492352539 := by
        calc
          (31 : ZMod 77636318761) ^ 5972024520 = (31 : ZMod 77636318761) ^ (2986012260 + 2986012260) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 2986012260 * (31 : ZMod 77636318761) ^ 2986012260 := by rw [pow_add]
          _ = 33492352539 := by rw [factor_5_31]; decide
      change (31 : ZMod 77636318761) ^ 5972024520 ≠ 1
      rw [factor_5_32]
      decide
    ·
      have factor_6_0 : (31 : ZMod 77636318761) ^ 1 = 31 := by norm_num
      have factor_6_1 : (31 : ZMod 77636318761) ^ 2 = 961 := by
        calc
          (31 : ZMod 77636318761) ^ 2 = (31 : ZMod 77636318761) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1 * (31 : ZMod 77636318761) ^ 1 := by rw [pow_add]
          _ = 961 := by rw [factor_6_0]; decide
      have factor_6_2 : (31 : ZMod 77636318761) ^ 4 = 923521 := by
        calc
          (31 : ZMod 77636318761) ^ 4 = (31 : ZMod 77636318761) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 2 * (31 : ZMod 77636318761) ^ 2 := by rw [pow_add]
          _ = 923521 := by rw [factor_6_1]; decide
      have factor_6_3 : (31 : ZMod 77636318761) ^ 8 = 76527849831 := by
        calc
          (31 : ZMod 77636318761) ^ 8 = (31 : ZMod 77636318761) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 4 * (31 : ZMod 77636318761) ^ 4 := by rw [pow_add]
          _ = 76527849831 := by rw [factor_6_2]; decide
      have factor_6_4 : (31 : ZMod 77636318761) ^ 17 = 35804496047 := by
        calc
          (31 : ZMod 77636318761) ^ 17 = (31 : ZMod 77636318761) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 8 * (31 : ZMod 77636318761) ^ 8) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 35804496047 := by rw [factor_6_3]; decide
      have factor_6_5 : (31 : ZMod 77636318761) ^ 34 = 2858503013 := by
        calc
          (31 : ZMod 77636318761) ^ 34 = (31 : ZMod 77636318761) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 17 * (31 : ZMod 77636318761) ^ 17 := by rw [pow_add]
          _ = 2858503013 := by rw [factor_6_4]; decide
      have factor_6_6 : (31 : ZMod 77636318761) ^ 68 = 69810785368 := by
        calc
          (31 : ZMod 77636318761) ^ 68 = (31 : ZMod 77636318761) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 34 * (31 : ZMod 77636318761) ^ 34 := by rw [pow_add]
          _ = 69810785368 := by rw [factor_6_5]; decide
      have factor_6_7 : (31 : ZMod 77636318761) ^ 136 = 56505708643 := by
        calc
          (31 : ZMod 77636318761) ^ 136 = (31 : ZMod 77636318761) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 68 * (31 : ZMod 77636318761) ^ 68 := by rw [pow_add]
          _ = 56505708643 := by rw [factor_6_6]; decide
      have factor_6_8 : (31 : ZMod 77636318761) ^ 272 = 31058145269 := by
        calc
          (31 : ZMod 77636318761) ^ 272 = (31 : ZMod 77636318761) ^ (136 + 136) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 136 * (31 : ZMod 77636318761) ^ 136 := by rw [pow_add]
          _ = 31058145269 := by rw [factor_6_7]; decide
      have factor_6_9 : (31 : ZMod 77636318761) ^ 544 = 1842810659 := by
        calc
          (31 : ZMod 77636318761) ^ 544 = (31 : ZMod 77636318761) ^ (272 + 272) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 272 * (31 : ZMod 77636318761) ^ 272 := by rw [pow_add]
          _ = 1842810659 := by rw [factor_6_8]; decide
      have factor_6_10 : (31 : ZMod 77636318761) ^ 1088 = 39125204657 := by
        calc
          (31 : ZMod 77636318761) ^ 1088 = (31 : ZMod 77636318761) ^ (544 + 544) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 544 * (31 : ZMod 77636318761) ^ 544 := by rw [pow_add]
          _ = 39125204657 := by rw [factor_6_9]; decide
      have factor_6_11 : (31 : ZMod 77636318761) ^ 2177 = 8442507644 := by
        calc
          (31 : ZMod 77636318761) ^ 2177 = (31 : ZMod 77636318761) ^ (1088 + 1088 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1088 * (31 : ZMod 77636318761) ^ 1088) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 8442507644 := by rw [factor_6_10]; decide
      have factor_6_12 : (31 : ZMod 77636318761) ^ 4355 = 52973600928 := by
        calc
          (31 : ZMod 77636318761) ^ 4355 = (31 : ZMod 77636318761) ^ (2177 + 2177 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 2177 * (31 : ZMod 77636318761) ^ 2177) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 52973600928 := by rw [factor_6_11]; decide
      have factor_6_13 : (31 : ZMod 77636318761) ^ 8710 = 48058376184 := by
        calc
          (31 : ZMod 77636318761) ^ 8710 = (31 : ZMod 77636318761) ^ (4355 + 4355) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 4355 * (31 : ZMod 77636318761) ^ 4355 := by rw [pow_add]
          _ = 48058376184 := by rw [factor_6_12]; decide
      have factor_6_14 : (31 : ZMod 77636318761) ^ 17421 = 42623331571 := by
        calc
          (31 : ZMod 77636318761) ^ 17421 = (31 : ZMod 77636318761) ^ (8710 + 8710 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 8710 * (31 : ZMod 77636318761) ^ 8710) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 42623331571 := by rw [factor_6_13]; decide
      have factor_6_15 : (31 : ZMod 77636318761) ^ 34842 = 59294371915 := by
        calc
          (31 : ZMod 77636318761) ^ 34842 = (31 : ZMod 77636318761) ^ (17421 + 17421) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 17421 * (31 : ZMod 77636318761) ^ 17421 := by rw [pow_add]
          _ = 59294371915 := by rw [factor_6_14]; decide
      have factor_6_16 : (31 : ZMod 77636318761) ^ 69684 = 67476523298 := by
        calc
          (31 : ZMod 77636318761) ^ 69684 = (31 : ZMod 77636318761) ^ (34842 + 34842) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 34842 * (31 : ZMod 77636318761) ^ 34842 := by rw [pow_add]
          _ = 67476523298 := by rw [factor_6_15]; decide
      have factor_6_17 : (31 : ZMod 77636318761) ^ 139368 = 2442811067 := by
        calc
          (31 : ZMod 77636318761) ^ 139368 = (31 : ZMod 77636318761) ^ (69684 + 69684) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 69684 * (31 : ZMod 77636318761) ^ 69684 := by rw [pow_add]
          _ = 2442811067 := by rw [factor_6_16]; decide
      have factor_6_18 : (31 : ZMod 77636318761) ^ 278737 = 19805151519 := by
        calc
          (31 : ZMod 77636318761) ^ 278737 = (31 : ZMod 77636318761) ^ (139368 + 139368 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 139368 * (31 : ZMod 77636318761) ^ 139368) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 19805151519 := by rw [factor_6_17]; decide
      have factor_6_19 : (31 : ZMod 77636318761) ^ 557475 = 41391452788 := by
        calc
          (31 : ZMod 77636318761) ^ 557475 = (31 : ZMod 77636318761) ^ (278737 + 278737 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 278737 * (31 : ZMod 77636318761) ^ 278737) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 41391452788 := by rw [factor_6_18]; decide
      have factor_6_20 : (31 : ZMod 77636318761) ^ 1114951 = 11064458747 := by
        calc
          (31 : ZMod 77636318761) ^ 1114951 = (31 : ZMod 77636318761) ^ (557475 + 557475 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 557475 * (31 : ZMod 77636318761) ^ 557475) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 11064458747 := by rw [factor_6_19]; decide
      have factor_6_21 : (31 : ZMod 77636318761) ^ 2229903 = 23197068985 := by
        calc
          (31 : ZMod 77636318761) ^ 2229903 = (31 : ZMod 77636318761) ^ (1114951 + 1114951 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1114951 * (31 : ZMod 77636318761) ^ 1114951) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 23197068985 := by rw [factor_6_20]; decide
      have factor_6_22 : (31 : ZMod 77636318761) ^ 4459806 = 63494201930 := by
        calc
          (31 : ZMod 77636318761) ^ 4459806 = (31 : ZMod 77636318761) ^ (2229903 + 2229903) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 2229903 * (31 : ZMod 77636318761) ^ 2229903 := by rw [pow_add]
          _ = 63494201930 := by rw [factor_6_21]; decide
      have factor_6_23 : (31 : ZMod 77636318761) ^ 8919613 = 69951422496 := by
        calc
          (31 : ZMod 77636318761) ^ 8919613 = (31 : ZMod 77636318761) ^ (4459806 + 4459806 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 4459806 * (31 : ZMod 77636318761) ^ 4459806) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 69951422496 := by rw [factor_6_22]; decide
      have factor_6_24 : (31 : ZMod 77636318761) ^ 17839227 = 48547768424 := by
        calc
          (31 : ZMod 77636318761) ^ 17839227 = (31 : ZMod 77636318761) ^ (8919613 + 8919613 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 8919613 * (31 : ZMod 77636318761) ^ 8919613) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 48547768424 := by rw [factor_6_23]; decide
      have factor_6_25 : (31 : ZMod 77636318761) ^ 35678455 = 77578184659 := by
        calc
          (31 : ZMod 77636318761) ^ 35678455 = (31 : ZMod 77636318761) ^ (17839227 + 17839227 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 17839227 * (31 : ZMod 77636318761) ^ 17839227) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 77578184659 := by rw [factor_6_24]; decide
      have factor_6_26 : (31 : ZMod 77636318761) ^ 71356910 = 64859680074 := by
        calc
          (31 : ZMod 77636318761) ^ 71356910 = (31 : ZMod 77636318761) ^ (35678455 + 35678455) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 35678455 * (31 : ZMod 77636318761) ^ 35678455 := by rw [pow_add]
          _ = 64859680074 := by rw [factor_6_25]; decide
      have factor_6_27 : (31 : ZMod 77636318761) ^ 142713821 = 49243154906 := by
        calc
          (31 : ZMod 77636318761) ^ 142713821 = (31 : ZMod 77636318761) ^ (71356910 + 71356910 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 71356910 * (31 : ZMod 77636318761) ^ 71356910) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 49243154906 := by rw [factor_6_26]; decide
      have factor_6_28 : (31 : ZMod 77636318761) ^ 285427642 = 27923890398 := by
        calc
          (31 : ZMod 77636318761) ^ 285427642 = (31 : ZMod 77636318761) ^ (142713821 + 142713821) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 142713821 * (31 : ZMod 77636318761) ^ 142713821 := by rw [pow_add]
          _ = 27923890398 := by rw [factor_6_27]; decide
      have factor_6_29 : (31 : ZMod 77636318761) ^ 570855285 = 32349586000 := by
        calc
          (31 : ZMod 77636318761) ^ 570855285 = (31 : ZMod 77636318761) ^ (285427642 + 285427642 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 285427642 * (31 : ZMod 77636318761) ^ 285427642) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 32349586000 := by rw [factor_6_28]; decide
      have factor_6_30 : (31 : ZMod 77636318761) ^ 1141710570 = 63100393854 := by
        calc
          (31 : ZMod 77636318761) ^ 1141710570 = (31 : ZMod 77636318761) ^ (570855285 + 570855285) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 570855285 * (31 : ZMod 77636318761) ^ 570855285 := by rw [pow_add]
          _ = 63100393854 := by rw [factor_6_29]; decide
      have factor_6_31 : (31 : ZMod 77636318761) ^ 2283421140 = 69638839263 := by
        calc
          (31 : ZMod 77636318761) ^ 2283421140 = (31 : ZMod 77636318761) ^ (1141710570 + 1141710570) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1141710570 * (31 : ZMod 77636318761) ^ 1141710570 := by rw [pow_add]
          _ = 69638839263 := by rw [factor_6_30]; decide
      have factor_6_32 : (31 : ZMod 77636318761) ^ 4566842280 = 15646236602 := by
        calc
          (31 : ZMod 77636318761) ^ 4566842280 = (31 : ZMod 77636318761) ^ (2283421140 + 2283421140) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 2283421140 * (31 : ZMod 77636318761) ^ 2283421140 := by rw [pow_add]
          _ = 15646236602 := by rw [factor_6_31]; decide
      change (31 : ZMod 77636318761) ^ 4566842280 ≠ 1
      rw [factor_6_32]
      decide
    ·
      have factor_7_0 : (31 : ZMod 77636318761) ^ 1 = 31 := by norm_num
      have factor_7_1 : (31 : ZMod 77636318761) ^ 3 = 29791 := by
        calc
          (31 : ZMod 77636318761) ^ 3 = (31 : ZMod 77636318761) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1 * (31 : ZMod 77636318761) ^ 1) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 29791 := by rw [factor_7_0]; decide
      have factor_7_2 : (31 : ZMod 77636318761) ^ 7 = 27512614111 := by
        calc
          (31 : ZMod 77636318761) ^ 7 = (31 : ZMod 77636318761) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 3 * (31 : ZMod 77636318761) ^ 3) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 27512614111 := by rw [factor_7_1]; decide
      have factor_7_3 : (31 : ZMod 77636318761) ^ 15 = 12882392486 := by
        calc
          (31 : ZMod 77636318761) ^ 15 = (31 : ZMod 77636318761) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 7 * (31 : ZMod 77636318761) ^ 7) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 12882392486 := by rw [factor_7_2]; decide
      have factor_7_4 : (31 : ZMod 77636318761) ^ 30 = 59115331858 := by
        calc
          (31 : ZMod 77636318761) ^ 30 = (31 : ZMod 77636318761) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 15 * (31 : ZMod 77636318761) ^ 15 := by rw [pow_add]
          _ = 59115331858 := by rw [factor_7_3]; decide
      have factor_7_5 : (31 : ZMod 77636318761) ^ 60 = 34166467142 := by
        calc
          (31 : ZMod 77636318761) ^ 60 = (31 : ZMod 77636318761) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 30 * (31 : ZMod 77636318761) ^ 30 := by rw [pow_add]
          _ = 34166467142 := by rw [factor_7_4]; decide
      have factor_7_6 : (31 : ZMod 77636318761) ^ 121 = 5428885724 := by
        calc
          (31 : ZMod 77636318761) ^ 121 = (31 : ZMod 77636318761) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 60 * (31 : ZMod 77636318761) ^ 60) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 5428885724 := by rw [factor_7_5]; decide
      have factor_7_7 : (31 : ZMod 77636318761) ^ 243 = 53726146978 := by
        calc
          (31 : ZMod 77636318761) ^ 243 = (31 : ZMod 77636318761) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 121 * (31 : ZMod 77636318761) ^ 121) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 53726146978 := by rw [factor_7_6]; decide
      have factor_7_8 : (31 : ZMod 77636318761) ^ 487 = 32567141348 := by
        calc
          (31 : ZMod 77636318761) ^ 487 = (31 : ZMod 77636318761) ^ (243 + 243 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 243 * (31 : ZMod 77636318761) ^ 243) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 32567141348 := by rw [factor_7_7]; decide
      have factor_7_9 : (31 : ZMod 77636318761) ^ 974 = 70775549757 := by
        calc
          (31 : ZMod 77636318761) ^ 974 = (31 : ZMod 77636318761) ^ (487 + 487) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 487 * (31 : ZMod 77636318761) ^ 487 := by rw [pow_add]
          _ = 70775549757 := by rw [factor_7_8]; decide
      have factor_7_10 : (31 : ZMod 77636318761) ^ 1948 = 63747301861 := by
        calc
          (31 : ZMod 77636318761) ^ 1948 = (31 : ZMod 77636318761) ^ (974 + 974) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 974 * (31 : ZMod 77636318761) ^ 974 := by rw [pow_add]
          _ = 63747301861 := by rw [factor_7_9]; decide
      have factor_7_11 : (31 : ZMod 77636318761) ^ 3896 = 33722582079 := by
        calc
          (31 : ZMod 77636318761) ^ 3896 = (31 : ZMod 77636318761) ^ (1948 + 1948) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1948 * (31 : ZMod 77636318761) ^ 1948 := by rw [pow_add]
          _ = 33722582079 := by rw [factor_7_10]; decide
      have factor_7_12 : (31 : ZMod 77636318761) ^ 7793 = 6254806697 := by
        calc
          (31 : ZMod 77636318761) ^ 7793 = (31 : ZMod 77636318761) ^ (3896 + 3896 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 3896 * (31 : ZMod 77636318761) ^ 3896) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 6254806697 := by rw [factor_7_11]; decide
      have factor_7_13 : (31 : ZMod 77636318761) ^ 15587 = 23697721212 := by
        calc
          (31 : ZMod 77636318761) ^ 15587 = (31 : ZMod 77636318761) ^ (7793 + 7793 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 7793 * (31 : ZMod 77636318761) ^ 7793) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 23697721212 := by rw [factor_7_12]; decide
      have factor_7_14 : (31 : ZMod 77636318761) ^ 31174 = 65431963201 := by
        calc
          (31 : ZMod 77636318761) ^ 31174 = (31 : ZMod 77636318761) ^ (15587 + 15587) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 15587 * (31 : ZMod 77636318761) ^ 15587 := by rw [pow_add]
          _ = 65431963201 := by rw [factor_7_13]; decide
      have factor_7_15 : (31 : ZMod 77636318761) ^ 62349 = 32608966758 := by
        calc
          (31 : ZMod 77636318761) ^ 62349 = (31 : ZMod 77636318761) ^ (31174 + 31174 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 31174 * (31 : ZMod 77636318761) ^ 31174) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 32608966758 := by rw [factor_7_14]; decide
      have factor_7_16 : (31 : ZMod 77636318761) ^ 124698 = 5479346479 := by
        calc
          (31 : ZMod 77636318761) ^ 124698 = (31 : ZMod 77636318761) ^ (62349 + 62349) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 62349 * (31 : ZMod 77636318761) ^ 62349 := by rw [pow_add]
          _ = 5479346479 := by rw [factor_7_15]; decide
      have factor_7_17 : (31 : ZMod 77636318761) ^ 249397 = 36761615177 := by
        calc
          (31 : ZMod 77636318761) ^ 249397 = (31 : ZMod 77636318761) ^ (124698 + 124698 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 124698 * (31 : ZMod 77636318761) ^ 124698) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 36761615177 := by rw [factor_7_16]; decide
      have factor_7_18 : (31 : ZMod 77636318761) ^ 498794 = 24022338016 := by
        calc
          (31 : ZMod 77636318761) ^ 498794 = (31 : ZMod 77636318761) ^ (249397 + 249397) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 249397 * (31 : ZMod 77636318761) ^ 249397 := by rw [pow_add]
          _ = 24022338016 := by rw [factor_7_17]; decide
      have factor_7_19 : (31 : ZMod 77636318761) ^ 997588 = 31764237648 := by
        calc
          (31 : ZMod 77636318761) ^ 997588 = (31 : ZMod 77636318761) ^ (498794 + 498794) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 498794 * (31 : ZMod 77636318761) ^ 498794 := by rw [pow_add]
          _ = 31764237648 := by rw [factor_7_18]; decide
      have factor_7_20 : (31 : ZMod 77636318761) ^ 1995176 = 16939954633 := by
        calc
          (31 : ZMod 77636318761) ^ 1995176 = (31 : ZMod 77636318761) ^ (997588 + 997588) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 997588 * (31 : ZMod 77636318761) ^ 997588 := by rw [pow_add]
          _ = 16939954633 := by rw [factor_7_19]; decide
      have factor_7_21 : (31 : ZMod 77636318761) ^ 3990353 = 3524489351 := by
        calc
          (31 : ZMod 77636318761) ^ 3990353 = (31 : ZMod 77636318761) ^ (1995176 + 1995176 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1995176 * (31 : ZMod 77636318761) ^ 1995176) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 3524489351 := by rw [factor_7_20]; decide
      have factor_7_22 : (31 : ZMod 77636318761) ^ 7980707 = 76871358989 := by
        calc
          (31 : ZMod 77636318761) ^ 7980707 = (31 : ZMod 77636318761) ^ (3990353 + 3990353 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 3990353 * (31 : ZMod 77636318761) ^ 3990353) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 76871358989 := by rw [factor_7_21]; decide
      have factor_7_23 : (31 : ZMod 77636318761) ^ 15961414 = 40832769866 := by
        calc
          (31 : ZMod 77636318761) ^ 15961414 = (31 : ZMod 77636318761) ^ (7980707 + 7980707) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 7980707 * (31 : ZMod 77636318761) ^ 7980707 := by rw [pow_add]
          _ = 40832769866 := by rw [factor_7_22]; decide
      have factor_7_24 : (31 : ZMod 77636318761) ^ 31922828 = 65044210308 := by
        calc
          (31 : ZMod 77636318761) ^ 31922828 = (31 : ZMod 77636318761) ^ (15961414 + 15961414) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 15961414 * (31 : ZMod 77636318761) ^ 15961414 := by rw [pow_add]
          _ = 65044210308 := by rw [factor_7_23]; decide
      have factor_7_25 : (31 : ZMod 77636318761) ^ 63845656 = 72421509753 := by
        calc
          (31 : ZMod 77636318761) ^ 63845656 = (31 : ZMod 77636318761) ^ (31922828 + 31922828) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 31922828 * (31 : ZMod 77636318761) ^ 31922828 := by rw [pow_add]
          _ = 72421509753 := by rw [factor_7_24]; decide
      have factor_7_26 : (31 : ZMod 77636318761) ^ 127691313 = 74240594251 := by
        calc
          (31 : ZMod 77636318761) ^ 127691313 = (31 : ZMod 77636318761) ^ (63845656 + 63845656 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 63845656 * (31 : ZMod 77636318761) ^ 63845656) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 74240594251 := by rw [factor_7_25]; decide
      have factor_7_27 : (31 : ZMod 77636318761) ^ 255382627 = 1327283586 := by
        calc
          (31 : ZMod 77636318761) ^ 255382627 = (31 : ZMod 77636318761) ^ (127691313 + 127691313 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 127691313 * (31 : ZMod 77636318761) ^ 127691313) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 1327283586 := by rw [factor_7_26]; decide
      have factor_7_28 : (31 : ZMod 77636318761) ^ 510765255 = 13443074618 := by
        calc
          (31 : ZMod 77636318761) ^ 510765255 = (31 : ZMod 77636318761) ^ (255382627 + 255382627 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 255382627 * (31 : ZMod 77636318761) ^ 255382627) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 13443074618 := by rw [factor_7_27]; decide
      have factor_7_29 : (31 : ZMod 77636318761) ^ 1021530510 = 61859991039 := by
        calc
          (31 : ZMod 77636318761) ^ 1021530510 = (31 : ZMod 77636318761) ^ (510765255 + 510765255) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 510765255 * (31 : ZMod 77636318761) ^ 510765255 := by rw [pow_add]
          _ = 61859991039 := by rw [factor_7_28]; decide
      have factor_7_30 : (31 : ZMod 77636318761) ^ 2043061020 = 72857833368 := by
        calc
          (31 : ZMod 77636318761) ^ 2043061020 = (31 : ZMod 77636318761) ^ (1021530510 + 1021530510) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1021530510 * (31 : ZMod 77636318761) ^ 1021530510 := by rw [pow_add]
          _ = 72857833368 := by rw [factor_7_29]; decide
      have factor_7_31 : (31 : ZMod 77636318761) ^ 4086122040 = 62492880002 := by
        calc
          (31 : ZMod 77636318761) ^ 4086122040 = (31 : ZMod 77636318761) ^ (2043061020 + 2043061020) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 2043061020 * (31 : ZMod 77636318761) ^ 2043061020 := by rw [pow_add]
          _ = 62492880002 := by rw [factor_7_30]; decide
      change (31 : ZMod 77636318761) ^ 4086122040 ≠ 1
      rw [factor_7_31]
      decide
    ·
      have factor_8_0 : (31 : ZMod 77636318761) ^ 1 = 31 := by norm_num
      have factor_8_1 : (31 : ZMod 77636318761) ^ 3 = 29791 := by
        calc
          (31 : ZMod 77636318761) ^ 3 = (31 : ZMod 77636318761) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1 * (31 : ZMod 77636318761) ^ 1) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 29791 := by rw [factor_8_0]; decide
      have factor_8_2 : (31 : ZMod 77636318761) ^ 6 = 887503681 := by
        calc
          (31 : ZMod 77636318761) ^ 6 = (31 : ZMod 77636318761) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 3 * (31 : ZMod 77636318761) ^ 3 := by rw [pow_add]
          _ = 887503681 := by rw [factor_8_1]; decide
      have factor_8_3 : (31 : ZMod 77636318761) ^ 12 = 18164480016 := by
        calc
          (31 : ZMod 77636318761) ^ 12 = (31 : ZMod 77636318761) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 6 * (31 : ZMod 77636318761) ^ 6 := by rw [pow_add]
          _ = 18164480016 := by rw [factor_8_2]; decide
      have factor_8_4 : (31 : ZMod 77636318761) ^ 25 = 32844455301 := by
        calc
          (31 : ZMod 77636318761) ^ 25 = (31 : ZMod 77636318761) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 12 * (31 : ZMod 77636318761) ^ 12) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 32844455301 := by rw [factor_8_3]; decide
      have factor_8_5 : (31 : ZMod 77636318761) ^ 50 = 30032012139 := by
        calc
          (31 : ZMod 77636318761) ^ 50 = (31 : ZMod 77636318761) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 25 * (31 : ZMod 77636318761) ^ 25 := by rw [pow_add]
          _ = 30032012139 := by rw [factor_8_4]; decide
      have factor_8_6 : (31 : ZMod 77636318761) ^ 100 = 7890118691 := by
        calc
          (31 : ZMod 77636318761) ^ 100 = (31 : ZMod 77636318761) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 50 * (31 : ZMod 77636318761) ^ 50 := by rw [pow_add]
          _ = 7890118691 := by rw [factor_8_5]; decide
      have factor_8_7 : (31 : ZMod 77636318761) ^ 201 = 20570344794 := by
        calc
          (31 : ZMod 77636318761) ^ 201 = (31 : ZMod 77636318761) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 100 * (31 : ZMod 77636318761) ^ 100) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 20570344794 := by rw [factor_8_6]; decide
      have factor_8_8 : (31 : ZMod 77636318761) ^ 402 = 29180318602 := by
        calc
          (31 : ZMod 77636318761) ^ 402 = (31 : ZMod 77636318761) ^ (201 + 201) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 201 * (31 : ZMod 77636318761) ^ 201 := by rw [pow_add]
          _ = 29180318602 := by rw [factor_8_7]; decide
      have factor_8_9 : (31 : ZMod 77636318761) ^ 804 = 28528856196 := by
        calc
          (31 : ZMod 77636318761) ^ 804 = (31 : ZMod 77636318761) ^ (402 + 402) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 402 * (31 : ZMod 77636318761) ^ 402 := by rw [pow_add]
          _ = 28528856196 := by rw [factor_8_8]; decide
      have factor_8_10 : (31 : ZMod 77636318761) ^ 1609 = 62705455019 := by
        calc
          (31 : ZMod 77636318761) ^ 1609 = (31 : ZMod 77636318761) ^ (804 + 804 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 804 * (31 : ZMod 77636318761) ^ 804) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 62705455019 := by rw [factor_8_9]; decide
      have factor_8_11 : (31 : ZMod 77636318761) ^ 3219 = 57115004418 := by
        calc
          (31 : ZMod 77636318761) ^ 3219 = (31 : ZMod 77636318761) ^ (1609 + 1609 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1609 * (31 : ZMod 77636318761) ^ 1609) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 57115004418 := by rw [factor_8_10]; decide
      have factor_8_12 : (31 : ZMod 77636318761) ^ 6438 = 41883849167 := by
        calc
          (31 : ZMod 77636318761) ^ 6438 = (31 : ZMod 77636318761) ^ (3219 + 3219) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 3219 * (31 : ZMod 77636318761) ^ 3219 := by rw [pow_add]
          _ = 41883849167 := by rw [factor_8_11]; decide
      have factor_8_13 : (31 : ZMod 77636318761) ^ 12876 = 2683341574 := by
        calc
          (31 : ZMod 77636318761) ^ 12876 = (31 : ZMod 77636318761) ^ (6438 + 6438) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 6438 * (31 : ZMod 77636318761) ^ 6438 := by rw [pow_add]
          _ = 2683341574 := by rw [factor_8_12]; decide
      have factor_8_14 : (31 : ZMod 77636318761) ^ 25752 = 1779560748 := by
        calc
          (31 : ZMod 77636318761) ^ 25752 = (31 : ZMod 77636318761) ^ (12876 + 12876) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 12876 * (31 : ZMod 77636318761) ^ 12876 := by rw [pow_add]
          _ = 1779560748 := by rw [factor_8_13]; decide
      have factor_8_15 : (31 : ZMod 77636318761) ^ 51505 = 46218171815 := by
        calc
          (31 : ZMod 77636318761) ^ 51505 = (31 : ZMod 77636318761) ^ (25752 + 25752 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 25752 * (31 : ZMod 77636318761) ^ 25752) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 46218171815 := by rw [factor_8_14]; decide
      have factor_8_16 : (31 : ZMod 77636318761) ^ 103011 = 7775494094 := by
        calc
          (31 : ZMod 77636318761) ^ 103011 = (31 : ZMod 77636318761) ^ (51505 + 51505 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 51505 * (31 : ZMod 77636318761) ^ 51505) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 7775494094 := by rw [factor_8_15]; decide
      have factor_8_17 : (31 : ZMod 77636318761) ^ 206023 = 73509137644 := by
        calc
          (31 : ZMod 77636318761) ^ 206023 = (31 : ZMod 77636318761) ^ (103011 + 103011 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 103011 * (31 : ZMod 77636318761) ^ 103011) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 73509137644 := by rw [factor_8_16]; decide
      have factor_8_18 : (31 : ZMod 77636318761) ^ 412047 = 7142719976 := by
        calc
          (31 : ZMod 77636318761) ^ 412047 = (31 : ZMod 77636318761) ^ (206023 + 206023 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 206023 * (31 : ZMod 77636318761) ^ 206023) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 7142719976 := by rw [factor_8_17]; decide
      have factor_8_19 : (31 : ZMod 77636318761) ^ 824094 = 154489662 := by
        calc
          (31 : ZMod 77636318761) ^ 824094 = (31 : ZMod 77636318761) ^ (412047 + 412047) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 412047 * (31 : ZMod 77636318761) ^ 412047 := by rw [pow_add]
          _ = 154489662 := by rw [factor_8_18]; decide
      have factor_8_20 : (31 : ZMod 77636318761) ^ 1648189 = 27275964665 := by
        calc
          (31 : ZMod 77636318761) ^ 1648189 = (31 : ZMod 77636318761) ^ (824094 + 824094 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 824094 * (31 : ZMod 77636318761) ^ 824094) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 27275964665 := by rw [factor_8_19]; decide
      have factor_8_21 : (31 : ZMod 77636318761) ^ 3296379 = 55070161967 := by
        calc
          (31 : ZMod 77636318761) ^ 3296379 = (31 : ZMod 77636318761) ^ (1648189 + 1648189 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1648189 * (31 : ZMod 77636318761) ^ 1648189) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 55070161967 := by rw [factor_8_20]; decide
      have factor_8_22 : (31 : ZMod 77636318761) ^ 6592758 = 30194633976 := by
        calc
          (31 : ZMod 77636318761) ^ 6592758 = (31 : ZMod 77636318761) ^ (3296379 + 3296379) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 3296379 * (31 : ZMod 77636318761) ^ 3296379 := by rw [pow_add]
          _ = 30194633976 := by rw [factor_8_21]; decide
      have factor_8_23 : (31 : ZMod 77636318761) ^ 13185516 = 43414826647 := by
        calc
          (31 : ZMod 77636318761) ^ 13185516 = (31 : ZMod 77636318761) ^ (6592758 + 6592758) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 6592758 * (31 : ZMod 77636318761) ^ 6592758 := by rw [pow_add]
          _ = 43414826647 := by rw [factor_8_22]; decide
      have factor_8_24 : (31 : ZMod 77636318761) ^ 26371032 = 39968138672 := by
        calc
          (31 : ZMod 77636318761) ^ 26371032 = (31 : ZMod 77636318761) ^ (13185516 + 13185516) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 13185516 * (31 : ZMod 77636318761) ^ 13185516 := by rw [pow_add]
          _ = 39968138672 := by rw [factor_8_23]; decide
      have factor_8_25 : (31 : ZMod 77636318761) ^ 52742064 = 33510332703 := by
        calc
          (31 : ZMod 77636318761) ^ 52742064 = (31 : ZMod 77636318761) ^ (26371032 + 26371032) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 26371032 * (31 : ZMod 77636318761) ^ 26371032 := by rw [pow_add]
          _ = 33510332703 := by rw [factor_8_24]; decide
      have factor_8_26 : (31 : ZMod 77636318761) ^ 105484128 = 5731541282 := by
        calc
          (31 : ZMod 77636318761) ^ 105484128 = (31 : ZMod 77636318761) ^ (52742064 + 52742064) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 52742064 * (31 : ZMod 77636318761) ^ 52742064 := by rw [pow_add]
          _ = 5731541282 := by rw [factor_8_25]; decide
      have factor_8_27 : (31 : ZMod 77636318761) ^ 210968257 = 23875080538 := by
        calc
          (31 : ZMod 77636318761) ^ 210968257 = (31 : ZMod 77636318761) ^ (105484128 + 105484128 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 105484128 * (31 : ZMod 77636318761) ^ 105484128) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 23875080538 := by rw [factor_8_26]; decide
      have factor_8_28 : (31 : ZMod 77636318761) ^ 421936515 = 23568537228 := by
        calc
          (31 : ZMod 77636318761) ^ 421936515 = (31 : ZMod 77636318761) ^ (210968257 + 210968257 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 210968257 * (31 : ZMod 77636318761) ^ 210968257) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 23568537228 := by rw [factor_8_27]; decide
      have factor_8_29 : (31 : ZMod 77636318761) ^ 843873030 = 13962393239 := by
        calc
          (31 : ZMod 77636318761) ^ 843873030 = (31 : ZMod 77636318761) ^ (421936515 + 421936515) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 421936515 * (31 : ZMod 77636318761) ^ 421936515 := by rw [pow_add]
          _ = 13962393239 := by rw [factor_8_28]; decide
      have factor_8_30 : (31 : ZMod 77636318761) ^ 1687746060 = 62971978264 := by
        calc
          (31 : ZMod 77636318761) ^ 1687746060 = (31 : ZMod 77636318761) ^ (843873030 + 843873030) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 843873030 * (31 : ZMod 77636318761) ^ 843873030 := by rw [pow_add]
          _ = 62971978264 := by rw [factor_8_29]; decide
      have factor_8_31 : (31 : ZMod 77636318761) ^ 3375492120 = 9819953058 := by
        calc
          (31 : ZMod 77636318761) ^ 3375492120 = (31 : ZMod 77636318761) ^ (1687746060 + 1687746060) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1687746060 * (31 : ZMod 77636318761) ^ 1687746060 := by rw [pow_add]
          _ = 9819953058 := by rw [factor_8_30]; decide
      change (31 : ZMod 77636318761) ^ 3375492120 ≠ 1
      rw [factor_8_31]
      decide
    ·
      have factor_9_0 : (31 : ZMod 77636318761) ^ 1 = 31 := by norm_num
      have factor_9_1 : (31 : ZMod 77636318761) ^ 2 = 961 := by
        calc
          (31 : ZMod 77636318761) ^ 2 = (31 : ZMod 77636318761) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1 * (31 : ZMod 77636318761) ^ 1 := by rw [pow_add]
          _ = 961 := by rw [factor_9_0]; decide
      have factor_9_2 : (31 : ZMod 77636318761) ^ 4 = 923521 := by
        calc
          (31 : ZMod 77636318761) ^ 4 = (31 : ZMod 77636318761) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 2 * (31 : ZMod 77636318761) ^ 2 := by rw [pow_add]
          _ = 923521 := by rw [factor_9_1]; decide
      have factor_9_3 : (31 : ZMod 77636318761) ^ 9 = 43273781931 := by
        calc
          (31 : ZMod 77636318761) ^ 9 = (31 : ZMod 77636318761) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 4 * (31 : ZMod 77636318761) ^ 4) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 43273781931 := by rw [factor_9_2]; decide
      have factor_9_4 : (31 : ZMod 77636318761) ^ 19 = 15231490044 := by
        calc
          (31 : ZMod 77636318761) ^ 19 = (31 : ZMod 77636318761) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 9 * (31 : ZMod 77636318761) ^ 9) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 15231490044 := by rw [factor_9_3]; decide
      have factor_9_5 : (31 : ZMod 77636318761) ^ 39 = 70787161863 := by
        calc
          (31 : ZMod 77636318761) ^ 39 = (31 : ZMod 77636318761) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 19 * (31 : ZMod 77636318761) ^ 19) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 70787161863 := by rw [factor_9_4]; decide
      have factor_9_6 : (31 : ZMod 77636318761) ^ 79 = 37163516885 := by
        calc
          (31 : ZMod 77636318761) ^ 79 = (31 : ZMod 77636318761) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 39 * (31 : ZMod 77636318761) ^ 39) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 37163516885 := by rw [factor_9_5]; decide
      have factor_9_7 : (31 : ZMod 77636318761) ^ 159 = 5851877213 := by
        calc
          (31 : ZMod 77636318761) ^ 159 = (31 : ZMod 77636318761) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 79 * (31 : ZMod 77636318761) ^ 79) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 5851877213 := by rw [factor_9_6]; decide
      have factor_9_8 : (31 : ZMod 77636318761) ^ 319 = 51642136114 := by
        calc
          (31 : ZMod 77636318761) ^ 319 = (31 : ZMod 77636318761) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 159 * (31 : ZMod 77636318761) ^ 159) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 51642136114 := by rw [factor_9_7]; decide
      have factor_9_9 : (31 : ZMod 77636318761) ^ 638 = 31900061150 := by
        calc
          (31 : ZMod 77636318761) ^ 638 = (31 : ZMod 77636318761) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 319 * (31 : ZMod 77636318761) ^ 319 := by rw [pow_add]
          _ = 31900061150 := by rw [factor_9_8]; decide
      have factor_9_10 : (31 : ZMod 77636318761) ^ 1276 = 2625803793 := by
        calc
          (31 : ZMod 77636318761) ^ 1276 = (31 : ZMod 77636318761) ^ (638 + 638) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 638 * (31 : ZMod 77636318761) ^ 638 := by rw [pow_add]
          _ = 2625803793 := by rw [factor_9_9]; decide
      have factor_9_11 : (31 : ZMod 77636318761) ^ 2553 = 22406796298 := by
        calc
          (31 : ZMod 77636318761) ^ 2553 = (31 : ZMod 77636318761) ^ (1276 + 1276 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1276 * (31 : ZMod 77636318761) ^ 1276) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 22406796298 := by rw [factor_9_10]; decide
      have factor_9_12 : (31 : ZMod 77636318761) ^ 5106 = 61703045854 := by
        calc
          (31 : ZMod 77636318761) ^ 5106 = (31 : ZMod 77636318761) ^ (2553 + 2553) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 2553 * (31 : ZMod 77636318761) ^ 2553 := by rw [pow_add]
          _ = 61703045854 := by rw [factor_9_11]; decide
      have factor_9_13 : (31 : ZMod 77636318761) ^ 10212 = 51740585320 := by
        calc
          (31 : ZMod 77636318761) ^ 10212 = (31 : ZMod 77636318761) ^ (5106 + 5106) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 5106 * (31 : ZMod 77636318761) ^ 5106 := by rw [pow_add]
          _ = 51740585320 := by rw [factor_9_12]; decide
      have factor_9_14 : (31 : ZMod 77636318761) ^ 20424 = 8074017282 := by
        calc
          (31 : ZMod 77636318761) ^ 20424 = (31 : ZMod 77636318761) ^ (10212 + 10212) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 10212 * (31 : ZMod 77636318761) ^ 10212 := by rw [pow_add]
          _ = 8074017282 := by rw [factor_9_13]; decide
      have factor_9_15 : (31 : ZMod 77636318761) ^ 40849 = 19645920095 := by
        calc
          (31 : ZMod 77636318761) ^ 40849 = (31 : ZMod 77636318761) ^ (20424 + 20424 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 20424 * (31 : ZMod 77636318761) ^ 20424) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 19645920095 := by rw [factor_9_14]; decide
      have factor_9_16 : (31 : ZMod 77636318761) ^ 81699 = 5500513428 := by
        calc
          (31 : ZMod 77636318761) ^ 81699 = (31 : ZMod 77636318761) ^ (40849 + 40849 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 40849 * (31 : ZMod 77636318761) ^ 40849) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 5500513428 := by rw [factor_9_15]; decide
      have factor_9_17 : (31 : ZMod 77636318761) ^ 163398 = 50530651448 := by
        calc
          (31 : ZMod 77636318761) ^ 163398 = (31 : ZMod 77636318761) ^ (81699 + 81699) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 81699 * (31 : ZMod 77636318761) ^ 81699 := by rw [pow_add]
          _ = 50530651448 := by rw [factor_9_16]; decide
      have factor_9_18 : (31 : ZMod 77636318761) ^ 326796 = 12449504321 := by
        calc
          (31 : ZMod 77636318761) ^ 326796 = (31 : ZMod 77636318761) ^ (163398 + 163398) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 163398 * (31 : ZMod 77636318761) ^ 163398 := by rw [pow_add]
          _ = 12449504321 := by rw [factor_9_17]; decide
      have factor_9_19 : (31 : ZMod 77636318761) ^ 653592 = 62409569541 := by
        calc
          (31 : ZMod 77636318761) ^ 653592 = (31 : ZMod 77636318761) ^ (326796 + 326796) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 326796 * (31 : ZMod 77636318761) ^ 326796 := by rw [pow_add]
          _ = 62409569541 := by rw [factor_9_18]; decide
      have factor_9_20 : (31 : ZMod 77636318761) ^ 1307184 = 54831046552 := by
        calc
          (31 : ZMod 77636318761) ^ 1307184 = (31 : ZMod 77636318761) ^ (653592 + 653592) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 653592 * (31 : ZMod 77636318761) ^ 653592 := by rw [pow_add]
          _ = 54831046552 := by rw [factor_9_19]; decide
      have factor_9_21 : (31 : ZMod 77636318761) ^ 2614369 = 14788578439 := by
        calc
          (31 : ZMod 77636318761) ^ 2614369 = (31 : ZMod 77636318761) ^ (1307184 + 1307184 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 1307184 * (31 : ZMod 77636318761) ^ 1307184) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 14788578439 := by rw [factor_9_20]; decide
      have factor_9_22 : (31 : ZMod 77636318761) ^ 5228739 = 62723427694 := by
        calc
          (31 : ZMod 77636318761) ^ 5228739 = (31 : ZMod 77636318761) ^ (2614369 + 2614369 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 2614369 * (31 : ZMod 77636318761) ^ 2614369) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 62723427694 := by rw [factor_9_21]; decide
      have factor_9_23 : (31 : ZMod 77636318761) ^ 10457478 = 16990328033 := by
        calc
          (31 : ZMod 77636318761) ^ 10457478 = (31 : ZMod 77636318761) ^ (5228739 + 5228739) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 5228739 * (31 : ZMod 77636318761) ^ 5228739 := by rw [pow_add]
          _ = 16990328033 := by rw [factor_9_22]; decide
      have factor_9_24 : (31 : ZMod 77636318761) ^ 20914956 = 10587229712 := by
        calc
          (31 : ZMod 77636318761) ^ 20914956 = (31 : ZMod 77636318761) ^ (10457478 + 10457478) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 10457478 * (31 : ZMod 77636318761) ^ 10457478 := by rw [pow_add]
          _ = 10587229712 := by rw [factor_9_23]; decide
      have factor_9_25 : (31 : ZMod 77636318761) ^ 41829913 = 20569154042 := by
        calc
          (31 : ZMod 77636318761) ^ 41829913 = (31 : ZMod 77636318761) ^ (20914956 + 20914956 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 20914956 * (31 : ZMod 77636318761) ^ 20914956) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 20569154042 := by rw [factor_9_24]; decide
      have factor_9_26 : (31 : ZMod 77636318761) ^ 83659826 = 53074169710 := by
        calc
          (31 : ZMod 77636318761) ^ 83659826 = (31 : ZMod 77636318761) ^ (41829913 + 41829913) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 41829913 * (31 : ZMod 77636318761) ^ 41829913 := by rw [pow_add]
          _ = 53074169710 := by rw [factor_9_25]; decide
      have factor_9_27 : (31 : ZMod 77636318761) ^ 167319652 = 53578245361 := by
        calc
          (31 : ZMod 77636318761) ^ 167319652 = (31 : ZMod 77636318761) ^ (83659826 + 83659826) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 83659826 * (31 : ZMod 77636318761) ^ 83659826 := by rw [pow_add]
          _ = 53578245361 := by rw [factor_9_26]; decide
      have factor_9_28 : (31 : ZMod 77636318761) ^ 334639305 = 46029940624 := by
        calc
          (31 : ZMod 77636318761) ^ 334639305 = (31 : ZMod 77636318761) ^ (167319652 + 167319652 + 1) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = ((31 : ZMod 77636318761) ^ 167319652 * (31 : ZMod 77636318761) ^ 167319652) * (31 : ZMod 77636318761) := by rw [pow_succ, pow_add]
          _ = 46029940624 := by rw [factor_9_27]; decide
      have factor_9_29 : (31 : ZMod 77636318761) ^ 669278610 = 11763516424 := by
        calc
          (31 : ZMod 77636318761) ^ 669278610 = (31 : ZMod 77636318761) ^ (334639305 + 334639305) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 334639305 * (31 : ZMod 77636318761) ^ 334639305 := by rw [pow_add]
          _ = 11763516424 := by rw [factor_9_28]; decide
      have factor_9_30 : (31 : ZMod 77636318761) ^ 1338557220 = 58160957344 := by
        calc
          (31 : ZMod 77636318761) ^ 1338557220 = (31 : ZMod 77636318761) ^ (669278610 + 669278610) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 669278610 * (31 : ZMod 77636318761) ^ 669278610 := by rw [pow_add]
          _ = 58160957344 := by rw [factor_9_29]; decide
      have factor_9_31 : (31 : ZMod 77636318761) ^ 2677114440 = 56078963036 := by
        calc
          (31 : ZMod 77636318761) ^ 2677114440 = (31 : ZMod 77636318761) ^ (1338557220 + 1338557220) :=
            congrArg (fun n : ℕ => (31 : ZMod 77636318761) ^ n) (by norm_num)
          _ = (31 : ZMod 77636318761) ^ 1338557220 * (31 : ZMod 77636318761) ^ 1338557220 := by rw [pow_add]
          _ = 56078963036 := by rw [factor_9_30]; decide
      change (31 : ZMod 77636318761) ^ 2677114440 ≠ 1
      rw [factor_9_31]
      decide

#print axioms prime_lucas_77636318761

end TotientTailPeriodKiller
end Erdos249257
