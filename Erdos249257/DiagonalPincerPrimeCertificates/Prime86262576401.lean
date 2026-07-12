import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_86262576401 : Nat.Prime 86262576401 := by
  apply lucas_primality 86262576401 (3 : ZMod 86262576401)
  ·
      have fermat_0 : (3 : ZMod 86262576401) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 86262576401) ^ 2 = 9 := by
        calc
          (3 : ZMod 86262576401) ^ 2 = (3 : ZMod 86262576401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1 * (3 : ZMod 86262576401) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 86262576401) ^ 5 = 243 := by
        calc
          (3 : ZMod 86262576401) ^ 5 = (3 : ZMod 86262576401) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 2 * (3 : ZMod 86262576401) ^ 2) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 86262576401) ^ 10 = 59049 := by
        calc
          (3 : ZMod 86262576401) ^ 10 = (3 : ZMod 86262576401) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 5 * (3 : ZMod 86262576401) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 86262576401) ^ 20 = 3486784401 := by
        calc
          (3 : ZMod 86262576401) ^ 20 = (3 : ZMod 86262576401) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 10 * (3 : ZMod 86262576401) ^ 10 := by rw [pow_add]
          _ = 3486784401 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 86262576401) ^ 40 = 41398771312 := by
        calc
          (3 : ZMod 86262576401) ^ 40 = (3 : ZMod 86262576401) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 20 * (3 : ZMod 86262576401) ^ 20 := by rw [pow_add]
          _ = 41398771312 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 86262576401) ^ 80 = 55703322676 := by
        calc
          (3 : ZMod 86262576401) ^ 80 = (3 : ZMod 86262576401) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 40 * (3 : ZMod 86262576401) ^ 40 := by rw [pow_add]
          _ = 55703322676 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 86262576401) ^ 160 = 63920220047 := by
        calc
          (3 : ZMod 86262576401) ^ 160 = (3 : ZMod 86262576401) ^ (80 + 80) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 80 * (3 : ZMod 86262576401) ^ 80 := by rw [pow_add]
          _ = 63920220047 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 86262576401) ^ 321 = 59271151833 := by
        calc
          (3 : ZMod 86262576401) ^ 321 = (3 : ZMod 86262576401) ^ (160 + 160 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 160 * (3 : ZMod 86262576401) ^ 160) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 59271151833 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 86262576401) ^ 642 = 8185211502 := by
        calc
          (3 : ZMod 86262576401) ^ 642 = (3 : ZMod 86262576401) ^ (321 + 321) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 321 * (3 : ZMod 86262576401) ^ 321 := by rw [pow_add]
          _ = 8185211502 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 86262576401) ^ 1285 = 67049291818 := by
        calc
          (3 : ZMod 86262576401) ^ 1285 = (3 : ZMod 86262576401) ^ (642 + 642 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 642 * (3 : ZMod 86262576401) ^ 642) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 67049291818 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 86262576401) ^ 2570 = 35481824750 := by
        calc
          (3 : ZMod 86262576401) ^ 2570 = (3 : ZMod 86262576401) ^ (1285 + 1285) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1285 * (3 : ZMod 86262576401) ^ 1285 := by rw [pow_add]
          _ = 35481824750 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 86262576401) ^ 5141 = 28913462189 := by
        calc
          (3 : ZMod 86262576401) ^ 5141 = (3 : ZMod 86262576401) ^ (2570 + 2570 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 2570 * (3 : ZMod 86262576401) ^ 2570) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 28913462189 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 86262576401) ^ 10283 = 35430879119 := by
        calc
          (3 : ZMod 86262576401) ^ 10283 = (3 : ZMod 86262576401) ^ (5141 + 5141 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 5141 * (3 : ZMod 86262576401) ^ 5141) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 35430879119 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 86262576401) ^ 20566 = 22086643640 := by
        calc
          (3 : ZMod 86262576401) ^ 20566 = (3 : ZMod 86262576401) ^ (10283 + 10283) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 10283 * (3 : ZMod 86262576401) ^ 10283 := by rw [pow_add]
          _ = 22086643640 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 86262576401) ^ 41133 = 63457017583 := by
        calc
          (3 : ZMod 86262576401) ^ 41133 = (3 : ZMod 86262576401) ^ (20566 + 20566 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 20566 * (3 : ZMod 86262576401) ^ 20566) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 63457017583 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 86262576401) ^ 82266 = 44080630945 := by
        calc
          (3 : ZMod 86262576401) ^ 82266 = (3 : ZMod 86262576401) ^ (41133 + 41133) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 41133 * (3 : ZMod 86262576401) ^ 41133 := by rw [pow_add]
          _ = 44080630945 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 86262576401) ^ 164532 = 67124072410 := by
        calc
          (3 : ZMod 86262576401) ^ 164532 = (3 : ZMod 86262576401) ^ (82266 + 82266) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 82266 * (3 : ZMod 86262576401) ^ 82266 := by rw [pow_add]
          _ = 67124072410 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 86262576401) ^ 329065 = 45470953741 := by
        calc
          (3 : ZMod 86262576401) ^ 329065 = (3 : ZMod 86262576401) ^ (164532 + 164532 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 164532 * (3 : ZMod 86262576401) ^ 164532) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 45470953741 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 86262576401) ^ 658131 = 11640432868 := by
        calc
          (3 : ZMod 86262576401) ^ 658131 = (3 : ZMod 86262576401) ^ (329065 + 329065 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 329065 * (3 : ZMod 86262576401) ^ 329065) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 11640432868 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 86262576401) ^ 1316262 = 86246279714 := by
        calc
          (3 : ZMod 86262576401) ^ 1316262 = (3 : ZMod 86262576401) ^ (658131 + 658131) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 658131 * (3 : ZMod 86262576401) ^ 658131 := by rw [pow_add]
          _ = 86246279714 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 86262576401) ^ 2632524 = 65797013691 := by
        calc
          (3 : ZMod 86262576401) ^ 2632524 = (3 : ZMod 86262576401) ^ (1316262 + 1316262) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1316262 * (3 : ZMod 86262576401) ^ 1316262 := by rw [pow_add]
          _ = 65797013691 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 86262576401) ^ 5265049 = 72018907463 := by
        calc
          (3 : ZMod 86262576401) ^ 5265049 = (3 : ZMod 86262576401) ^ (2632524 + 2632524 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 2632524 * (3 : ZMod 86262576401) ^ 2632524) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 72018907463 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 86262576401) ^ 10530099 = 7418194690 := by
        calc
          (3 : ZMod 86262576401) ^ 10530099 = (3 : ZMod 86262576401) ^ (5265049 + 5265049 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 5265049 * (3 : ZMod 86262576401) ^ 5265049) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 7418194690 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 86262576401) ^ 21060199 = 5175105880 := by
        calc
          (3 : ZMod 86262576401) ^ 21060199 = (3 : ZMod 86262576401) ^ (10530099 + 10530099 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 10530099 * (3 : ZMod 86262576401) ^ 10530099) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 5175105880 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 86262576401) ^ 42120398 = 37500572965 := by
        calc
          (3 : ZMod 86262576401) ^ 42120398 = (3 : ZMod 86262576401) ^ (21060199 + 21060199) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 21060199 * (3 : ZMod 86262576401) ^ 21060199 := by rw [pow_add]
          _ = 37500572965 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 86262576401) ^ 84240797 = 34727607647 := by
        calc
          (3 : ZMod 86262576401) ^ 84240797 = (3 : ZMod 86262576401) ^ (42120398 + 42120398 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 42120398 * (3 : ZMod 86262576401) ^ 42120398) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 34727607647 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 86262576401) ^ 168481594 = 86070359617 := by
        calc
          (3 : ZMod 86262576401) ^ 168481594 = (3 : ZMod 86262576401) ^ (84240797 + 84240797) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 84240797 * (3 : ZMod 86262576401) ^ 84240797 := by rw [pow_add]
          _ = 86070359617 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 86262576401) ^ 336963189 = 72546089033 := by
        calc
          (3 : ZMod 86262576401) ^ 336963189 = (3 : ZMod 86262576401) ^ (168481594 + 168481594 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 168481594 * (3 : ZMod 86262576401) ^ 168481594) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 72546089033 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 86262576401) ^ 673926378 = 29271090629 := by
        calc
          (3 : ZMod 86262576401) ^ 673926378 = (3 : ZMod 86262576401) ^ (336963189 + 336963189) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 336963189 * (3 : ZMod 86262576401) ^ 336963189 := by rw [pow_add]
          _ = 29271090629 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 86262576401) ^ 1347852756 = 53248179799 := by
        calc
          (3 : ZMod 86262576401) ^ 1347852756 = (3 : ZMod 86262576401) ^ (673926378 + 673926378) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 673926378 * (3 : ZMod 86262576401) ^ 673926378 := by rw [pow_add]
          _ = 53248179799 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 86262576401) ^ 2695705512 = 64895059305 := by
        calc
          (3 : ZMod 86262576401) ^ 2695705512 = (3 : ZMod 86262576401) ^ (1347852756 + 1347852756) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1347852756 * (3 : ZMod 86262576401) ^ 1347852756 := by rw [pow_add]
          _ = 64895059305 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 86262576401) ^ 5391411025 = 4364805111 := by
        calc
          (3 : ZMod 86262576401) ^ 5391411025 = (3 : ZMod 86262576401) ^ (2695705512 + 2695705512 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 2695705512 * (3 : ZMod 86262576401) ^ 2695705512) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 4364805111 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 86262576401) ^ 10782822050 = 16879304494 := by
        calc
          (3 : ZMod 86262576401) ^ 10782822050 = (3 : ZMod 86262576401) ^ (5391411025 + 5391411025) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 5391411025 * (3 : ZMod 86262576401) ^ 5391411025 := by rw [pow_add]
          _ = 16879304494 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 86262576401) ^ 21565644100 = 54905051017 := by
        calc
          (3 : ZMod 86262576401) ^ 21565644100 = (3 : ZMod 86262576401) ^ (10782822050 + 10782822050) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 10782822050 * (3 : ZMod 86262576401) ^ 10782822050 := by rw [pow_add]
          _ = 54905051017 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 86262576401) ^ 43131288200 = 86262576400 := by
        calc
          (3 : ZMod 86262576401) ^ 43131288200 = (3 : ZMod 86262576401) ^ (21565644100 + 21565644100) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 21565644100 * (3 : ZMod 86262576401) ^ 21565644100 := by rw [pow_add]
          _ = 86262576400 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 86262576401) ^ 86262576400 = 1 := by
        calc
          (3 : ZMod 86262576401) ^ 86262576400 = (3 : ZMod 86262576401) ^ (43131288200 + 43131288200) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 43131288200 * (3 : ZMod 86262576401) ^ 43131288200 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod = 86262576401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 86262576401) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 86262576401) ^ 2 = 9 := by
        calc
          (3 : ZMod 86262576401) ^ 2 = (3 : ZMod 86262576401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1 * (3 : ZMod 86262576401) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 86262576401) ^ 5 = 243 := by
        calc
          (3 : ZMod 86262576401) ^ 5 = (3 : ZMod 86262576401) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 2 * (3 : ZMod 86262576401) ^ 2) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 86262576401) ^ 10 = 59049 := by
        calc
          (3 : ZMod 86262576401) ^ 10 = (3 : ZMod 86262576401) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 5 * (3 : ZMod 86262576401) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 86262576401) ^ 20 = 3486784401 := by
        calc
          (3 : ZMod 86262576401) ^ 20 = (3 : ZMod 86262576401) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 10 * (3 : ZMod 86262576401) ^ 10 := by rw [pow_add]
          _ = 3486784401 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 86262576401) ^ 40 = 41398771312 := by
        calc
          (3 : ZMod 86262576401) ^ 40 = (3 : ZMod 86262576401) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 20 * (3 : ZMod 86262576401) ^ 20 := by rw [pow_add]
          _ = 41398771312 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 86262576401) ^ 80 = 55703322676 := by
        calc
          (3 : ZMod 86262576401) ^ 80 = (3 : ZMod 86262576401) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 40 * (3 : ZMod 86262576401) ^ 40 := by rw [pow_add]
          _ = 55703322676 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 86262576401) ^ 160 = 63920220047 := by
        calc
          (3 : ZMod 86262576401) ^ 160 = (3 : ZMod 86262576401) ^ (80 + 80) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 80 * (3 : ZMod 86262576401) ^ 80 := by rw [pow_add]
          _ = 63920220047 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 86262576401) ^ 321 = 59271151833 := by
        calc
          (3 : ZMod 86262576401) ^ 321 = (3 : ZMod 86262576401) ^ (160 + 160 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 160 * (3 : ZMod 86262576401) ^ 160) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 59271151833 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 86262576401) ^ 642 = 8185211502 := by
        calc
          (3 : ZMod 86262576401) ^ 642 = (3 : ZMod 86262576401) ^ (321 + 321) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 321 * (3 : ZMod 86262576401) ^ 321 := by rw [pow_add]
          _ = 8185211502 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 86262576401) ^ 1285 = 67049291818 := by
        calc
          (3 : ZMod 86262576401) ^ 1285 = (3 : ZMod 86262576401) ^ (642 + 642 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 642 * (3 : ZMod 86262576401) ^ 642) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 67049291818 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 86262576401) ^ 2570 = 35481824750 := by
        calc
          (3 : ZMod 86262576401) ^ 2570 = (3 : ZMod 86262576401) ^ (1285 + 1285) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1285 * (3 : ZMod 86262576401) ^ 1285 := by rw [pow_add]
          _ = 35481824750 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 86262576401) ^ 5141 = 28913462189 := by
        calc
          (3 : ZMod 86262576401) ^ 5141 = (3 : ZMod 86262576401) ^ (2570 + 2570 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 2570 * (3 : ZMod 86262576401) ^ 2570) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 28913462189 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 86262576401) ^ 10283 = 35430879119 := by
        calc
          (3 : ZMod 86262576401) ^ 10283 = (3 : ZMod 86262576401) ^ (5141 + 5141 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 5141 * (3 : ZMod 86262576401) ^ 5141) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 35430879119 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 86262576401) ^ 20566 = 22086643640 := by
        calc
          (3 : ZMod 86262576401) ^ 20566 = (3 : ZMod 86262576401) ^ (10283 + 10283) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 10283 * (3 : ZMod 86262576401) ^ 10283 := by rw [pow_add]
          _ = 22086643640 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 86262576401) ^ 41133 = 63457017583 := by
        calc
          (3 : ZMod 86262576401) ^ 41133 = (3 : ZMod 86262576401) ^ (20566 + 20566 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 20566 * (3 : ZMod 86262576401) ^ 20566) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 63457017583 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 86262576401) ^ 82266 = 44080630945 := by
        calc
          (3 : ZMod 86262576401) ^ 82266 = (3 : ZMod 86262576401) ^ (41133 + 41133) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 41133 * (3 : ZMod 86262576401) ^ 41133 := by rw [pow_add]
          _ = 44080630945 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 86262576401) ^ 164532 = 67124072410 := by
        calc
          (3 : ZMod 86262576401) ^ 164532 = (3 : ZMod 86262576401) ^ (82266 + 82266) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 82266 * (3 : ZMod 86262576401) ^ 82266 := by rw [pow_add]
          _ = 67124072410 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 86262576401) ^ 329065 = 45470953741 := by
        calc
          (3 : ZMod 86262576401) ^ 329065 = (3 : ZMod 86262576401) ^ (164532 + 164532 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 164532 * (3 : ZMod 86262576401) ^ 164532) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 45470953741 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 86262576401) ^ 658131 = 11640432868 := by
        calc
          (3 : ZMod 86262576401) ^ 658131 = (3 : ZMod 86262576401) ^ (329065 + 329065 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 329065 * (3 : ZMod 86262576401) ^ 329065) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 11640432868 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 86262576401) ^ 1316262 = 86246279714 := by
        calc
          (3 : ZMod 86262576401) ^ 1316262 = (3 : ZMod 86262576401) ^ (658131 + 658131) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 658131 * (3 : ZMod 86262576401) ^ 658131 := by rw [pow_add]
          _ = 86246279714 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 86262576401) ^ 2632524 = 65797013691 := by
        calc
          (3 : ZMod 86262576401) ^ 2632524 = (3 : ZMod 86262576401) ^ (1316262 + 1316262) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1316262 * (3 : ZMod 86262576401) ^ 1316262 := by rw [pow_add]
          _ = 65797013691 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 86262576401) ^ 5265049 = 72018907463 := by
        calc
          (3 : ZMod 86262576401) ^ 5265049 = (3 : ZMod 86262576401) ^ (2632524 + 2632524 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 2632524 * (3 : ZMod 86262576401) ^ 2632524) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 72018907463 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 86262576401) ^ 10530099 = 7418194690 := by
        calc
          (3 : ZMod 86262576401) ^ 10530099 = (3 : ZMod 86262576401) ^ (5265049 + 5265049 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 5265049 * (3 : ZMod 86262576401) ^ 5265049) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 7418194690 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 86262576401) ^ 21060199 = 5175105880 := by
        calc
          (3 : ZMod 86262576401) ^ 21060199 = (3 : ZMod 86262576401) ^ (10530099 + 10530099 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 10530099 * (3 : ZMod 86262576401) ^ 10530099) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 5175105880 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 86262576401) ^ 42120398 = 37500572965 := by
        calc
          (3 : ZMod 86262576401) ^ 42120398 = (3 : ZMod 86262576401) ^ (21060199 + 21060199) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 21060199 * (3 : ZMod 86262576401) ^ 21060199 := by rw [pow_add]
          _ = 37500572965 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 86262576401) ^ 84240797 = 34727607647 := by
        calc
          (3 : ZMod 86262576401) ^ 84240797 = (3 : ZMod 86262576401) ^ (42120398 + 42120398 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 42120398 * (3 : ZMod 86262576401) ^ 42120398) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 34727607647 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 86262576401) ^ 168481594 = 86070359617 := by
        calc
          (3 : ZMod 86262576401) ^ 168481594 = (3 : ZMod 86262576401) ^ (84240797 + 84240797) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 84240797 * (3 : ZMod 86262576401) ^ 84240797 := by rw [pow_add]
          _ = 86070359617 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 86262576401) ^ 336963189 = 72546089033 := by
        calc
          (3 : ZMod 86262576401) ^ 336963189 = (3 : ZMod 86262576401) ^ (168481594 + 168481594 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 168481594 * (3 : ZMod 86262576401) ^ 168481594) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 72546089033 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 86262576401) ^ 673926378 = 29271090629 := by
        calc
          (3 : ZMod 86262576401) ^ 673926378 = (3 : ZMod 86262576401) ^ (336963189 + 336963189) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 336963189 * (3 : ZMod 86262576401) ^ 336963189 := by rw [pow_add]
          _ = 29271090629 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 86262576401) ^ 1347852756 = 53248179799 := by
        calc
          (3 : ZMod 86262576401) ^ 1347852756 = (3 : ZMod 86262576401) ^ (673926378 + 673926378) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 673926378 * (3 : ZMod 86262576401) ^ 673926378 := by rw [pow_add]
          _ = 53248179799 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 86262576401) ^ 2695705512 = 64895059305 := by
        calc
          (3 : ZMod 86262576401) ^ 2695705512 = (3 : ZMod 86262576401) ^ (1347852756 + 1347852756) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1347852756 * (3 : ZMod 86262576401) ^ 1347852756 := by rw [pow_add]
          _ = 64895059305 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 86262576401) ^ 5391411025 = 4364805111 := by
        calc
          (3 : ZMod 86262576401) ^ 5391411025 = (3 : ZMod 86262576401) ^ (2695705512 + 2695705512 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 2695705512 * (3 : ZMod 86262576401) ^ 2695705512) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 4364805111 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 86262576401) ^ 10782822050 = 16879304494 := by
        calc
          (3 : ZMod 86262576401) ^ 10782822050 = (3 : ZMod 86262576401) ^ (5391411025 + 5391411025) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 5391411025 * (3 : ZMod 86262576401) ^ 5391411025 := by rw [pow_add]
          _ = 16879304494 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 86262576401) ^ 21565644100 = 54905051017 := by
        calc
          (3 : ZMod 86262576401) ^ 21565644100 = (3 : ZMod 86262576401) ^ (10782822050 + 10782822050) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 10782822050 * (3 : ZMod 86262576401) ^ 10782822050 := by rw [pow_add]
          _ = 54905051017 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 86262576401) ^ 43131288200 = 86262576400 := by
        calc
          (3 : ZMod 86262576401) ^ 43131288200 = (3 : ZMod 86262576401) ^ (21565644100 + 21565644100) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 21565644100 * (3 : ZMod 86262576401) ^ 21565644100 := by rw [pow_add]
          _ = 86262576400 := by rw [factor_0_34]; decide
      change (3 : ZMod 86262576401) ^ 43131288200 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (3 : ZMod 86262576401) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 86262576401) ^ 2 = 9 := by
        calc
          (3 : ZMod 86262576401) ^ 2 = (3 : ZMod 86262576401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1 * (3 : ZMod 86262576401) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 86262576401) ^ 4 = 81 := by
        calc
          (3 : ZMod 86262576401) ^ 4 = (3 : ZMod 86262576401) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 2 * (3 : ZMod 86262576401) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 86262576401) ^ 8 = 6561 := by
        calc
          (3 : ZMod 86262576401) ^ 8 = (3 : ZMod 86262576401) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 4 * (3 : ZMod 86262576401) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 86262576401) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 86262576401) ^ 16 = (3 : ZMod 86262576401) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 8 * (3 : ZMod 86262576401) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 86262576401) ^ 32 = 13785181960 := by
        calc
          (3 : ZMod 86262576401) ^ 32 = (3 : ZMod 86262576401) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 16 * (3 : ZMod 86262576401) ^ 16 := by rw [pow_add]
          _ = 13785181960 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 86262576401) ^ 64 = 337000045 := by
        calc
          (3 : ZMod 86262576401) ^ 64 = (3 : ZMod 86262576401) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 32 * (3 : ZMod 86262576401) ^ 32 := by rw [pow_add]
          _ = 337000045 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 86262576401) ^ 128 = 35369265475 := by
        calc
          (3 : ZMod 86262576401) ^ 128 = (3 : ZMod 86262576401) ^ (64 + 64) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 64 * (3 : ZMod 86262576401) ^ 64 := by rw [pow_add]
          _ = 35369265475 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 86262576401) ^ 257 = 45500095396 := by
        calc
          (3 : ZMod 86262576401) ^ 257 = (3 : ZMod 86262576401) ^ (128 + 128 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 128 * (3 : ZMod 86262576401) ^ 128) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 45500095396 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 86262576401) ^ 514 = 16157267863 := by
        calc
          (3 : ZMod 86262576401) ^ 514 = (3 : ZMod 86262576401) ^ (257 + 257) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 257 * (3 : ZMod 86262576401) ^ 257 := by rw [pow_add]
          _ = 16157267863 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 86262576401) ^ 1028 = 48828435486 := by
        calc
          (3 : ZMod 86262576401) ^ 1028 = (3 : ZMod 86262576401) ^ (514 + 514) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 514 * (3 : ZMod 86262576401) ^ 514 := by rw [pow_add]
          _ = 48828435486 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 86262576401) ^ 2056 = 47594227783 := by
        calc
          (3 : ZMod 86262576401) ^ 2056 = (3 : ZMod 86262576401) ^ (1028 + 1028) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1028 * (3 : ZMod 86262576401) ^ 1028 := by rw [pow_add]
          _ = 47594227783 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 86262576401) ^ 4113 = 40595496746 := by
        calc
          (3 : ZMod 86262576401) ^ 4113 = (3 : ZMod 86262576401) ^ (2056 + 2056 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 2056 * (3 : ZMod 86262576401) ^ 2056) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 40595496746 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 86262576401) ^ 8226 = 85056600053 := by
        calc
          (3 : ZMod 86262576401) ^ 8226 = (3 : ZMod 86262576401) ^ (4113 + 4113) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 4113 * (3 : ZMod 86262576401) ^ 4113 := by rw [pow_add]
          _ = 85056600053 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 86262576401) ^ 16453 = 67490216394 := by
        calc
          (3 : ZMod 86262576401) ^ 16453 = (3 : ZMod 86262576401) ^ (8226 + 8226 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 8226 * (3 : ZMod 86262576401) ^ 8226) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 67490216394 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 86262576401) ^ 32906 = 2410278833 := by
        calc
          (3 : ZMod 86262576401) ^ 32906 = (3 : ZMod 86262576401) ^ (16453 + 16453) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 16453 * (3 : ZMod 86262576401) ^ 16453 := by rw [pow_add]
          _ = 2410278833 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 86262576401) ^ 65813 = 31768639908 := by
        calc
          (3 : ZMod 86262576401) ^ 65813 = (3 : ZMod 86262576401) ^ (32906 + 32906 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 32906 * (3 : ZMod 86262576401) ^ 32906) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 31768639908 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 86262576401) ^ 131626 = 52586358355 := by
        calc
          (3 : ZMod 86262576401) ^ 131626 = (3 : ZMod 86262576401) ^ (65813 + 65813) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 65813 * (3 : ZMod 86262576401) ^ 65813 := by rw [pow_add]
          _ = 52586358355 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 86262576401) ^ 263252 = 36496565057 := by
        calc
          (3 : ZMod 86262576401) ^ 263252 = (3 : ZMod 86262576401) ^ (131626 + 131626) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 131626 * (3 : ZMod 86262576401) ^ 131626 := by rw [pow_add]
          _ = 36496565057 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 86262576401) ^ 526504 = 53375076693 := by
        calc
          (3 : ZMod 86262576401) ^ 526504 = (3 : ZMod 86262576401) ^ (263252 + 263252) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 263252 * (3 : ZMod 86262576401) ^ 263252 := by rw [pow_add]
          _ = 53375076693 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 86262576401) ^ 1053009 = 83614650606 := by
        calc
          (3 : ZMod 86262576401) ^ 1053009 = (3 : ZMod 86262576401) ^ (526504 + 526504 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 526504 * (3 : ZMod 86262576401) ^ 526504) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 83614650606 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 86262576401) ^ 2106019 = 39023379787 := by
        calc
          (3 : ZMod 86262576401) ^ 2106019 = (3 : ZMod 86262576401) ^ (1053009 + 1053009 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 1053009 * (3 : ZMod 86262576401) ^ 1053009) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 39023379787 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 86262576401) ^ 4212039 = 63248192776 := by
        calc
          (3 : ZMod 86262576401) ^ 4212039 = (3 : ZMod 86262576401) ^ (2106019 + 2106019 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 2106019 * (3 : ZMod 86262576401) ^ 2106019) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 63248192776 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 86262576401) ^ 8424079 = 39422620810 := by
        calc
          (3 : ZMod 86262576401) ^ 8424079 = (3 : ZMod 86262576401) ^ (4212039 + 4212039 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 4212039 * (3 : ZMod 86262576401) ^ 4212039) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 39422620810 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 86262576401) ^ 16848159 = 18799605282 := by
        calc
          (3 : ZMod 86262576401) ^ 16848159 = (3 : ZMod 86262576401) ^ (8424079 + 8424079 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 8424079 * (3 : ZMod 86262576401) ^ 8424079) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 18799605282 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 86262576401) ^ 33696318 = 30191137934 := by
        calc
          (3 : ZMod 86262576401) ^ 33696318 = (3 : ZMod 86262576401) ^ (16848159 + 16848159) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 16848159 * (3 : ZMod 86262576401) ^ 16848159 := by rw [pow_add]
          _ = 30191137934 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 86262576401) ^ 67392637 = 27752426614 := by
        calc
          (3 : ZMod 86262576401) ^ 67392637 = (3 : ZMod 86262576401) ^ (33696318 + 33696318 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 33696318 * (3 : ZMod 86262576401) ^ 33696318) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 27752426614 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 86262576401) ^ 134785275 = 22166721047 := by
        calc
          (3 : ZMod 86262576401) ^ 134785275 = (3 : ZMod 86262576401) ^ (67392637 + 67392637 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 67392637 * (3 : ZMod 86262576401) ^ 67392637) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 22166721047 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 86262576401) ^ 269570551 = 41004190034 := by
        calc
          (3 : ZMod 86262576401) ^ 269570551 = (3 : ZMod 86262576401) ^ (134785275 + 134785275 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 134785275 * (3 : ZMod 86262576401) ^ 134785275) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 41004190034 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 86262576401) ^ 539141102 = 11526133559 := by
        calc
          (3 : ZMod 86262576401) ^ 539141102 = (3 : ZMod 86262576401) ^ (269570551 + 269570551) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 269570551 * (3 : ZMod 86262576401) ^ 269570551 := by rw [pow_add]
          _ = 11526133559 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 86262576401) ^ 1078282205 = 27382567736 := by
        calc
          (3 : ZMod 86262576401) ^ 1078282205 = (3 : ZMod 86262576401) ^ (539141102 + 539141102 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 539141102 * (3 : ZMod 86262576401) ^ 539141102) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 27382567736 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 86262576401) ^ 2156564410 = 3907857636 := by
        calc
          (3 : ZMod 86262576401) ^ 2156564410 = (3 : ZMod 86262576401) ^ (1078282205 + 1078282205) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1078282205 * (3 : ZMod 86262576401) ^ 1078282205 := by rw [pow_add]
          _ = 3907857636 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 86262576401) ^ 4313128820 = 62332486765 := by
        calc
          (3 : ZMod 86262576401) ^ 4313128820 = (3 : ZMod 86262576401) ^ (2156564410 + 2156564410) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 2156564410 * (3 : ZMod 86262576401) ^ 2156564410 := by rw [pow_add]
          _ = 62332486765 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 86262576401) ^ 8626257640 = 71766775972 := by
        calc
          (3 : ZMod 86262576401) ^ 8626257640 = (3 : ZMod 86262576401) ^ (4313128820 + 4313128820) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 4313128820 * (3 : ZMod 86262576401) ^ 4313128820 := by rw [pow_add]
          _ = 71766775972 := by rw [factor_1_32]; decide
      have factor_1_34 : (3 : ZMod 86262576401) ^ 17252515280 = 38057491896 := by
        calc
          (3 : ZMod 86262576401) ^ 17252515280 = (3 : ZMod 86262576401) ^ (8626257640 + 8626257640) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 8626257640 * (3 : ZMod 86262576401) ^ 8626257640 := by rw [pow_add]
          _ = 38057491896 := by rw [factor_1_33]; decide
      change (3 : ZMod 86262576401) ^ 17252515280 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (3 : ZMod 86262576401) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 86262576401) ^ 2 = 9 := by
        calc
          (3 : ZMod 86262576401) ^ 2 = (3 : ZMod 86262576401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1 * (3 : ZMod 86262576401) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 86262576401) ^ 5 = 243 := by
        calc
          (3 : ZMod 86262576401) ^ 5 = (3 : ZMod 86262576401) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 2 * (3 : ZMod 86262576401) ^ 2) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 86262576401) ^ 11 = 177147 := by
        calc
          (3 : ZMod 86262576401) ^ 11 = (3 : ZMod 86262576401) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 5 * (3 : ZMod 86262576401) ^ 5) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 86262576401) ^ 22 = 31381059609 := by
        calc
          (3 : ZMod 86262576401) ^ 22 = (3 : ZMod 86262576401) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 11 * (3 : ZMod 86262576401) ^ 11 := by rw [pow_add]
          _ = 31381059609 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 86262576401) ^ 45 = 53442566300 := by
        calc
          (3 : ZMod 86262576401) ^ 45 = (3 : ZMod 86262576401) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 22 * (3 : ZMod 86262576401) ^ 22) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 53442566300 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 86262576401) ^ 91 = 14124998581 := by
        calc
          (3 : ZMod 86262576401) ^ 91 = (3 : ZMod 86262576401) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 45 * (3 : ZMod 86262576401) ^ 45) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 14124998581 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 86262576401) ^ 183 = 33272128314 := by
        calc
          (3 : ZMod 86262576401) ^ 183 = (3 : ZMod 86262576401) ^ (91 + 91 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 91 * (3 : ZMod 86262576401) ^ 91) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 33272128314 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 86262576401) ^ 367 = 80009910983 := by
        calc
          (3 : ZMod 86262576401) ^ 367 = (3 : ZMod 86262576401) ^ (183 + 183 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 183 * (3 : ZMod 86262576401) ^ 183) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 80009910983 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 86262576401) ^ 734 = 17580519884 := by
        calc
          (3 : ZMod 86262576401) ^ 734 = (3 : ZMod 86262576401) ^ (367 + 367) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 367 * (3 : ZMod 86262576401) ^ 367 := by rw [pow_add]
          _ = 17580519884 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 86262576401) ^ 1469 = 27987638464 := by
        calc
          (3 : ZMod 86262576401) ^ 1469 = (3 : ZMod 86262576401) ^ (734 + 734 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 734 * (3 : ZMod 86262576401) ^ 734) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 27987638464 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 86262576401) ^ 2938 = 27476530952 := by
        calc
          (3 : ZMod 86262576401) ^ 2938 = (3 : ZMod 86262576401) ^ (1469 + 1469) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1469 * (3 : ZMod 86262576401) ^ 1469 := by rw [pow_add]
          _ = 27476530952 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 86262576401) ^ 5876 = 32335787087 := by
        calc
          (3 : ZMod 86262576401) ^ 5876 = (3 : ZMod 86262576401) ^ (2938 + 2938) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 2938 * (3 : ZMod 86262576401) ^ 2938 := by rw [pow_add]
          _ = 32335787087 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 86262576401) ^ 11752 = 39337557397 := by
        calc
          (3 : ZMod 86262576401) ^ 11752 = (3 : ZMod 86262576401) ^ (5876 + 5876) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 5876 * (3 : ZMod 86262576401) ^ 5876 := by rw [pow_add]
          _ = 39337557397 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 86262576401) ^ 23504 = 4548091111 := by
        calc
          (3 : ZMod 86262576401) ^ 23504 = (3 : ZMod 86262576401) ^ (11752 + 11752) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 11752 * (3 : ZMod 86262576401) ^ 11752 := by rw [pow_add]
          _ = 4548091111 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 86262576401) ^ 47009 = 42136863780 := by
        calc
          (3 : ZMod 86262576401) ^ 47009 = (3 : ZMod 86262576401) ^ (23504 + 23504 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 23504 * (3 : ZMod 86262576401) ^ 23504) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 42136863780 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 86262576401) ^ 94018 = 63165460318 := by
        calc
          (3 : ZMod 86262576401) ^ 94018 = (3 : ZMod 86262576401) ^ (47009 + 47009) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 47009 * (3 : ZMod 86262576401) ^ 47009 := by rw [pow_add]
          _ = 63165460318 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 86262576401) ^ 188037 = 78716192558 := by
        calc
          (3 : ZMod 86262576401) ^ 188037 = (3 : ZMod 86262576401) ^ (94018 + 94018 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 94018 * (3 : ZMod 86262576401) ^ 94018) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 78716192558 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 86262576401) ^ 376074 = 27655362898 := by
        calc
          (3 : ZMod 86262576401) ^ 376074 = (3 : ZMod 86262576401) ^ (188037 + 188037) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 188037 * (3 : ZMod 86262576401) ^ 188037 := by rw [pow_add]
          _ = 27655362898 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 86262576401) ^ 752149 = 61894864658 := by
        calc
          (3 : ZMod 86262576401) ^ 752149 = (3 : ZMod 86262576401) ^ (376074 + 376074 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 376074 * (3 : ZMod 86262576401) ^ 376074) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 61894864658 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 86262576401) ^ 1504299 = 37061954882 := by
        calc
          (3 : ZMod 86262576401) ^ 1504299 = (3 : ZMod 86262576401) ^ (752149 + 752149 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 752149 * (3 : ZMod 86262576401) ^ 752149) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 37061954882 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 86262576401) ^ 3008599 = 69908401987 := by
        calc
          (3 : ZMod 86262576401) ^ 3008599 = (3 : ZMod 86262576401) ^ (1504299 + 1504299 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 1504299 * (3 : ZMod 86262576401) ^ 1504299) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 69908401987 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 86262576401) ^ 6017199 = 74539928820 := by
        calc
          (3 : ZMod 86262576401) ^ 6017199 = (3 : ZMod 86262576401) ^ (3008599 + 3008599 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 3008599 * (3 : ZMod 86262576401) ^ 3008599) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 74539928820 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 86262576401) ^ 12034399 = 16696964040 := by
        calc
          (3 : ZMod 86262576401) ^ 12034399 = (3 : ZMod 86262576401) ^ (6017199 + 6017199 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 6017199 * (3 : ZMod 86262576401) ^ 6017199) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 16696964040 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 86262576401) ^ 24068799 = 4288359079 := by
        calc
          (3 : ZMod 86262576401) ^ 24068799 = (3 : ZMod 86262576401) ^ (12034399 + 12034399 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 12034399 * (3 : ZMod 86262576401) ^ 12034399) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 4288359079 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 86262576401) ^ 48137598 = 31786406062 := by
        calc
          (3 : ZMod 86262576401) ^ 48137598 = (3 : ZMod 86262576401) ^ (24068799 + 24068799) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 24068799 * (3 : ZMod 86262576401) ^ 24068799 := by rw [pow_add]
          _ = 31786406062 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 86262576401) ^ 96275196 = 54982728696 := by
        calc
          (3 : ZMod 86262576401) ^ 96275196 = (3 : ZMod 86262576401) ^ (48137598 + 48137598) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 48137598 * (3 : ZMod 86262576401) ^ 48137598 := by rw [pow_add]
          _ = 54982728696 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 86262576401) ^ 192550393 = 52333328110 := by
        calc
          (3 : ZMod 86262576401) ^ 192550393 = (3 : ZMod 86262576401) ^ (96275196 + 96275196 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 96275196 * (3 : ZMod 86262576401) ^ 96275196) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 52333328110 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 86262576401) ^ 385100787 = 69614974787 := by
        calc
          (3 : ZMod 86262576401) ^ 385100787 = (3 : ZMod 86262576401) ^ (192550393 + 192550393 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 192550393 * (3 : ZMod 86262576401) ^ 192550393) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 69614974787 := by rw [factor_2_27]; decide
      have factor_2_29 : (3 : ZMod 86262576401) ^ 770201575 = 14360058804 := by
        calc
          (3 : ZMod 86262576401) ^ 770201575 = (3 : ZMod 86262576401) ^ (385100787 + 385100787 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 385100787 * (3 : ZMod 86262576401) ^ 385100787) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 14360058804 := by rw [factor_2_28]; decide
      have factor_2_30 : (3 : ZMod 86262576401) ^ 1540403150 = 11528541461 := by
        calc
          (3 : ZMod 86262576401) ^ 1540403150 = (3 : ZMod 86262576401) ^ (770201575 + 770201575) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 770201575 * (3 : ZMod 86262576401) ^ 770201575 := by rw [pow_add]
          _ = 11528541461 := by rw [factor_2_29]; decide
      have factor_2_31 : (3 : ZMod 86262576401) ^ 3080806300 = 46308815346 := by
        calc
          (3 : ZMod 86262576401) ^ 3080806300 = (3 : ZMod 86262576401) ^ (1540403150 + 1540403150) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1540403150 * (3 : ZMod 86262576401) ^ 1540403150 := by rw [pow_add]
          _ = 46308815346 := by rw [factor_2_30]; decide
      have factor_2_32 : (3 : ZMod 86262576401) ^ 6161612600 = 4214338195 := by
        calc
          (3 : ZMod 86262576401) ^ 6161612600 = (3 : ZMod 86262576401) ^ (3080806300 + 3080806300) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 3080806300 * (3 : ZMod 86262576401) ^ 3080806300 := by rw [pow_add]
          _ = 4214338195 := by rw [factor_2_31]; decide
      have factor_2_33 : (3 : ZMod 86262576401) ^ 12323225200 = 55144545109 := by
        calc
          (3 : ZMod 86262576401) ^ 12323225200 = (3 : ZMod 86262576401) ^ (6161612600 + 6161612600) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 6161612600 * (3 : ZMod 86262576401) ^ 6161612600 := by rw [pow_add]
          _ = 55144545109 := by rw [factor_2_32]; decide
      change (3 : ZMod 86262576401) ^ 12323225200 ≠ 1
      rw [factor_2_33]
      decide
    ·
      have factor_3_0 : (3 : ZMod 86262576401) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 86262576401) ^ 3 = 27 := by
        calc
          (3 : ZMod 86262576401) ^ 3 = (3 : ZMod 86262576401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 1 * (3 : ZMod 86262576401) ^ 1) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 86262576401) ^ 7 = 2187 := by
        calc
          (3 : ZMod 86262576401) ^ 7 = (3 : ZMod 86262576401) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 3 * (3 : ZMod 86262576401) ^ 3) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 86262576401) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 86262576401) ^ 14 = (3 : ZMod 86262576401) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 7 * (3 : ZMod 86262576401) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 86262576401) ^ 29 = 51629126088 := by
        calc
          (3 : ZMod 86262576401) ^ 29 = (3 : ZMod 86262576401) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 14 * (3 : ZMod 86262576401) ^ 14) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 51629126088 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 86262576401) ^ 58 = 60467096764 := by
        calc
          (3 : ZMod 86262576401) ^ 58 = (3 : ZMod 86262576401) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 29 * (3 : ZMod 86262576401) ^ 29 := by rw [pow_add]
          _ = 60467096764 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 86262576401) ^ 116 = 26562150637 := by
        calc
          (3 : ZMod 86262576401) ^ 116 = (3 : ZMod 86262576401) ^ (58 + 58) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 58 * (3 : ZMod 86262576401) ^ 58 := by rw [pow_add]
          _ = 26562150637 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 86262576401) ^ 233 = 78824898502 := by
        calc
          (3 : ZMod 86262576401) ^ 233 = (3 : ZMod 86262576401) ^ (116 + 116 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 116 * (3 : ZMod 86262576401) ^ 116) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 78824898502 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 86262576401) ^ 467 = 1295720970 := by
        calc
          (3 : ZMod 86262576401) ^ 467 = (3 : ZMod 86262576401) ^ (233 + 233 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 233 * (3 : ZMod 86262576401) ^ 233) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 1295720970 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 86262576401) ^ 934 = 20311707914 := by
        calc
          (3 : ZMod 86262576401) ^ 934 = (3 : ZMod 86262576401) ^ (467 + 467) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 467 * (3 : ZMod 86262576401) ^ 467 := by rw [pow_add]
          _ = 20311707914 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 86262576401) ^ 1869 = 35226833124 := by
        calc
          (3 : ZMod 86262576401) ^ 1869 = (3 : ZMod 86262576401) ^ (934 + 934 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 934 * (3 : ZMod 86262576401) ^ 934) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 35226833124 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 86262576401) ^ 3739 = 35245802243 := by
        calc
          (3 : ZMod 86262576401) ^ 3739 = (3 : ZMod 86262576401) ^ (1869 + 1869 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 1869 * (3 : ZMod 86262576401) ^ 1869) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 35245802243 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 86262576401) ^ 7478 = 61609913773 := by
        calc
          (3 : ZMod 86262576401) ^ 7478 = (3 : ZMod 86262576401) ^ (3739 + 3739) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 3739 * (3 : ZMod 86262576401) ^ 3739 := by rw [pow_add]
          _ = 61609913773 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 86262576401) ^ 14957 = 76079039763 := by
        calc
          (3 : ZMod 86262576401) ^ 14957 = (3 : ZMod 86262576401) ^ (7478 + 7478 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 7478 * (3 : ZMod 86262576401) ^ 7478) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 76079039763 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 86262576401) ^ 29915 = 8078973213 := by
        calc
          (3 : ZMod 86262576401) ^ 29915 = (3 : ZMod 86262576401) ^ (14957 + 14957 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 14957 * (3 : ZMod 86262576401) ^ 14957) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 8078973213 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 86262576401) ^ 59830 = 67362154299 := by
        calc
          (3 : ZMod 86262576401) ^ 59830 = (3 : ZMod 86262576401) ^ (29915 + 29915) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 29915 * (3 : ZMod 86262576401) ^ 29915 := by rw [pow_add]
          _ = 67362154299 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 86262576401) ^ 119660 = 72608402029 := by
        calc
          (3 : ZMod 86262576401) ^ 119660 = (3 : ZMod 86262576401) ^ (59830 + 59830) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 59830 * (3 : ZMod 86262576401) ^ 59830 := by rw [pow_add]
          _ = 72608402029 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 86262576401) ^ 239320 = 41643059575 := by
        calc
          (3 : ZMod 86262576401) ^ 239320 = (3 : ZMod 86262576401) ^ (119660 + 119660) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 119660 * (3 : ZMod 86262576401) ^ 119660 := by rw [pow_add]
          _ = 41643059575 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 86262576401) ^ 478640 = 77579844171 := by
        calc
          (3 : ZMod 86262576401) ^ 478640 = (3 : ZMod 86262576401) ^ (239320 + 239320) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 239320 * (3 : ZMod 86262576401) ^ 239320 := by rw [pow_add]
          _ = 77579844171 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 86262576401) ^ 957281 = 62875996136 := by
        calc
          (3 : ZMod 86262576401) ^ 957281 = (3 : ZMod 86262576401) ^ (478640 + 478640 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 478640 * (3 : ZMod 86262576401) ^ 478640) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 62875996136 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 86262576401) ^ 1914563 = 75571514898 := by
        calc
          (3 : ZMod 86262576401) ^ 1914563 = (3 : ZMod 86262576401) ^ (957281 + 957281 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 957281 * (3 : ZMod 86262576401) ^ 957281) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 75571514898 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 86262576401) ^ 3829127 = 21653992342 := by
        calc
          (3 : ZMod 86262576401) ^ 3829127 = (3 : ZMod 86262576401) ^ (1914563 + 1914563 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 1914563 * (3 : ZMod 86262576401) ^ 1914563) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 21653992342 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 86262576401) ^ 7658254 = 23465837334 := by
        calc
          (3 : ZMod 86262576401) ^ 7658254 = (3 : ZMod 86262576401) ^ (3829127 + 3829127) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 3829127 * (3 : ZMod 86262576401) ^ 3829127 := by rw [pow_add]
          _ = 23465837334 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 86262576401) ^ 15316508 = 81219388832 := by
        calc
          (3 : ZMod 86262576401) ^ 15316508 = (3 : ZMod 86262576401) ^ (7658254 + 7658254) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 7658254 * (3 : ZMod 86262576401) ^ 7658254 := by rw [pow_add]
          _ = 81219388832 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 86262576401) ^ 30633017 = 53915834403 := by
        calc
          (3 : ZMod 86262576401) ^ 30633017 = (3 : ZMod 86262576401) ^ (15316508 + 15316508 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 15316508 * (3 : ZMod 86262576401) ^ 15316508) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 53915834403 := by rw [factor_3_23]; decide
      have factor_3_25 : (3 : ZMod 86262576401) ^ 61266034 = 49208783878 := by
        calc
          (3 : ZMod 86262576401) ^ 61266034 = (3 : ZMod 86262576401) ^ (30633017 + 30633017) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 30633017 * (3 : ZMod 86262576401) ^ 30633017 := by rw [pow_add]
          _ = 49208783878 := by rw [factor_3_24]; decide
      have factor_3_26 : (3 : ZMod 86262576401) ^ 122532068 = 76221701000 := by
        calc
          (3 : ZMod 86262576401) ^ 122532068 = (3 : ZMod 86262576401) ^ (61266034 + 61266034) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 61266034 * (3 : ZMod 86262576401) ^ 61266034 := by rw [pow_add]
          _ = 76221701000 := by rw [factor_3_25]; decide
      have factor_3_27 : (3 : ZMod 86262576401) ^ 245064137 = 74915486415 := by
        calc
          (3 : ZMod 86262576401) ^ 245064137 = (3 : ZMod 86262576401) ^ (122532068 + 122532068 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 122532068 * (3 : ZMod 86262576401) ^ 122532068) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 74915486415 := by rw [factor_3_26]; decide
      have factor_3_28 : (3 : ZMod 86262576401) ^ 490128275 = 59914172659 := by
        calc
          (3 : ZMod 86262576401) ^ 490128275 = (3 : ZMod 86262576401) ^ (245064137 + 245064137 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 245064137 * (3 : ZMod 86262576401) ^ 245064137) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 59914172659 := by rw [factor_3_27]; decide
      have factor_3_29 : (3 : ZMod 86262576401) ^ 980256550 = 68290174231 := by
        calc
          (3 : ZMod 86262576401) ^ 980256550 = (3 : ZMod 86262576401) ^ (490128275 + 490128275) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 490128275 * (3 : ZMod 86262576401) ^ 490128275 := by rw [pow_add]
          _ = 68290174231 := by rw [factor_3_28]; decide
      have factor_3_30 : (3 : ZMod 86262576401) ^ 1960513100 = 38288418618 := by
        calc
          (3 : ZMod 86262576401) ^ 1960513100 = (3 : ZMod 86262576401) ^ (980256550 + 980256550) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 980256550 * (3 : ZMod 86262576401) ^ 980256550 := by rw [pow_add]
          _ = 38288418618 := by rw [factor_3_29]; decide
      have factor_3_31 : (3 : ZMod 86262576401) ^ 3921026200 = 2241384937 := by
        calc
          (3 : ZMod 86262576401) ^ 3921026200 = (3 : ZMod 86262576401) ^ (1960513100 + 1960513100) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1960513100 * (3 : ZMod 86262576401) ^ 1960513100 := by rw [pow_add]
          _ = 2241384937 := by rw [factor_3_30]; decide
      have factor_3_32 : (3 : ZMod 86262576401) ^ 7842052400 = 15840375830 := by
        calc
          (3 : ZMod 86262576401) ^ 7842052400 = (3 : ZMod 86262576401) ^ (3921026200 + 3921026200) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 3921026200 * (3 : ZMod 86262576401) ^ 3921026200 := by rw [pow_add]
          _ = 15840375830 := by rw [factor_3_31]; decide
      change (3 : ZMod 86262576401) ^ 7842052400 ≠ 1
      rw [factor_3_32]
      decide
    ·
      have factor_4_0 : (3 : ZMod 86262576401) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 86262576401) ^ 3 = 27 := by
        calc
          (3 : ZMod 86262576401) ^ 3 = (3 : ZMod 86262576401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 1 * (3 : ZMod 86262576401) ^ 1) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 86262576401) ^ 6 = 729 := by
        calc
          (3 : ZMod 86262576401) ^ 6 = (3 : ZMod 86262576401) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 3 * (3 : ZMod 86262576401) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 86262576401) ^ 12 = 531441 := by
        calc
          (3 : ZMod 86262576401) ^ 12 = (3 : ZMod 86262576401) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 6 * (3 : ZMod 86262576401) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 86262576401) ^ 24 = 23641807278 := by
        calc
          (3 : ZMod 86262576401) ^ 24 = (3 : ZMod 86262576401) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 12 * (3 : ZMod 86262576401) ^ 12 := by rw [pow_add]
          _ = 23641807278 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 86262576401) ^ 49 = 15719050250 := by
        calc
          (3 : ZMod 86262576401) ^ 49 = (3 : ZMod 86262576401) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 24 * (3 : ZMod 86262576401) ^ 24) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 15719050250 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 86262576401) ^ 98 = 9369545089 := by
        calc
          (3 : ZMod 86262576401) ^ 98 = (3 : ZMod 86262576401) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 49 * (3 : ZMod 86262576401) ^ 49 := by rw [pow_add]
          _ = 9369545089 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 86262576401) ^ 197 = 28255756639 := by
        calc
          (3 : ZMod 86262576401) ^ 197 = (3 : ZMod 86262576401) ^ (98 + 98 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 98 * (3 : ZMod 86262576401) ^ 98) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 28255756639 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 86262576401) ^ 395 = 19925782159 := by
        calc
          (3 : ZMod 86262576401) ^ 395 = (3 : ZMod 86262576401) ^ (197 + 197 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 197 * (3 : ZMod 86262576401) ^ 197) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 19925782159 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 86262576401) ^ 791 = 75657229763 := by
        calc
          (3 : ZMod 86262576401) ^ 791 = (3 : ZMod 86262576401) ^ (395 + 395 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 395 * (3 : ZMod 86262576401) ^ 395) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 75657229763 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 86262576401) ^ 1582 = 56292550806 := by
        calc
          (3 : ZMod 86262576401) ^ 1582 = (3 : ZMod 86262576401) ^ (791 + 791) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 791 * (3 : ZMod 86262576401) ^ 791 := by rw [pow_add]
          _ = 56292550806 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 86262576401) ^ 3164 = 39238363030 := by
        calc
          (3 : ZMod 86262576401) ^ 3164 = (3 : ZMod 86262576401) ^ (1582 + 1582) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1582 * (3 : ZMod 86262576401) ^ 1582 := by rw [pow_add]
          _ = 39238363030 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 86262576401) ^ 6328 = 49466607792 := by
        calc
          (3 : ZMod 86262576401) ^ 6328 = (3 : ZMod 86262576401) ^ (3164 + 3164) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 3164 * (3 : ZMod 86262576401) ^ 3164 := by rw [pow_add]
          _ = 49466607792 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 86262576401) ^ 12656 = 69963209309 := by
        calc
          (3 : ZMod 86262576401) ^ 12656 = (3 : ZMod 86262576401) ^ (6328 + 6328) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 6328 * (3 : ZMod 86262576401) ^ 6328 := by rw [pow_add]
          _ = 69963209309 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 86262576401) ^ 25312 = 44608665385 := by
        calc
          (3 : ZMod 86262576401) ^ 25312 = (3 : ZMod 86262576401) ^ (12656 + 12656) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 12656 * (3 : ZMod 86262576401) ^ 12656 := by rw [pow_add]
          _ = 44608665385 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 86262576401) ^ 50625 = 34778857860 := by
        calc
          (3 : ZMod 86262576401) ^ 50625 = (3 : ZMod 86262576401) ^ (25312 + 25312 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 25312 * (3 : ZMod 86262576401) ^ 25312) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 34778857860 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 86262576401) ^ 101250 = 47019785914 := by
        calc
          (3 : ZMod 86262576401) ^ 101250 = (3 : ZMod 86262576401) ^ (50625 + 50625) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 50625 * (3 : ZMod 86262576401) ^ 50625 := by rw [pow_add]
          _ = 47019785914 := by rw [factor_4_15]; decide
      have factor_4_17 : (3 : ZMod 86262576401) ^ 202501 = 81186656364 := by
        calc
          (3 : ZMod 86262576401) ^ 202501 = (3 : ZMod 86262576401) ^ (101250 + 101250 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 101250 * (3 : ZMod 86262576401) ^ 101250) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 81186656364 := by rw [factor_4_16]; decide
      have factor_4_18 : (3 : ZMod 86262576401) ^ 405003 = 61135908894 := by
        calc
          (3 : ZMod 86262576401) ^ 405003 = (3 : ZMod 86262576401) ^ (202501 + 202501 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 202501 * (3 : ZMod 86262576401) ^ 202501) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 61135908894 := by rw [factor_4_17]; decide
      have factor_4_19 : (3 : ZMod 86262576401) ^ 810007 = 5487352912 := by
        calc
          (3 : ZMod 86262576401) ^ 810007 = (3 : ZMod 86262576401) ^ (405003 + 405003 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 405003 * (3 : ZMod 86262576401) ^ 405003) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 5487352912 := by rw [factor_4_18]; decide
      have factor_4_20 : (3 : ZMod 86262576401) ^ 1620015 = 57602196936 := by
        calc
          (3 : ZMod 86262576401) ^ 1620015 = (3 : ZMod 86262576401) ^ (810007 + 810007 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 810007 * (3 : ZMod 86262576401) ^ 810007) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 57602196936 := by rw [factor_4_19]; decide
      have factor_4_21 : (3 : ZMod 86262576401) ^ 3240030 = 59554933270 := by
        calc
          (3 : ZMod 86262576401) ^ 3240030 = (3 : ZMod 86262576401) ^ (1620015 + 1620015) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1620015 * (3 : ZMod 86262576401) ^ 1620015 := by rw [pow_add]
          _ = 59554933270 := by rw [factor_4_20]; decide
      have factor_4_22 : (3 : ZMod 86262576401) ^ 6480061 = 6735040809 := by
        calc
          (3 : ZMod 86262576401) ^ 6480061 = (3 : ZMod 86262576401) ^ (3240030 + 3240030 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 3240030 * (3 : ZMod 86262576401) ^ 3240030) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 6735040809 := by rw [factor_4_21]; decide
      have factor_4_23 : (3 : ZMod 86262576401) ^ 12960122 = 19409789131 := by
        calc
          (3 : ZMod 86262576401) ^ 12960122 = (3 : ZMod 86262576401) ^ (6480061 + 6480061) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 6480061 * (3 : ZMod 86262576401) ^ 6480061 := by rw [pow_add]
          _ = 19409789131 := by rw [factor_4_22]; decide
      have factor_4_24 : (3 : ZMod 86262576401) ^ 25920245 = 38979969730 := by
        calc
          (3 : ZMod 86262576401) ^ 25920245 = (3 : ZMod 86262576401) ^ (12960122 + 12960122 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 12960122 * (3 : ZMod 86262576401) ^ 12960122) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 38979969730 := by rw [factor_4_23]; decide
      have factor_4_25 : (3 : ZMod 86262576401) ^ 51840490 = 68301513543 := by
        calc
          (3 : ZMod 86262576401) ^ 51840490 = (3 : ZMod 86262576401) ^ (25920245 + 25920245) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 25920245 * (3 : ZMod 86262576401) ^ 25920245 := by rw [pow_add]
          _ = 68301513543 := by rw [factor_4_24]; decide
      have factor_4_26 : (3 : ZMod 86262576401) ^ 103680981 = 1185932527 := by
        calc
          (3 : ZMod 86262576401) ^ 103680981 = (3 : ZMod 86262576401) ^ (51840490 + 51840490 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 51840490 * (3 : ZMod 86262576401) ^ 51840490) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 1185932527 := by rw [factor_4_25]; decide
      have factor_4_27 : (3 : ZMod 86262576401) ^ 207361962 = 43870075203 := by
        calc
          (3 : ZMod 86262576401) ^ 207361962 = (3 : ZMod 86262576401) ^ (103680981 + 103680981) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 103680981 * (3 : ZMod 86262576401) ^ 103680981 := by rw [pow_add]
          _ = 43870075203 := by rw [factor_4_26]; decide
      have factor_4_28 : (3 : ZMod 86262576401) ^ 414723925 = 12813676522 := by
        calc
          (3 : ZMod 86262576401) ^ 414723925 = (3 : ZMod 86262576401) ^ (207361962 + 207361962 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 207361962 * (3 : ZMod 86262576401) ^ 207361962) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 12813676522 := by rw [factor_4_27]; decide
      have factor_4_29 : (3 : ZMod 86262576401) ^ 829447850 = 79419957101 := by
        calc
          (3 : ZMod 86262576401) ^ 829447850 = (3 : ZMod 86262576401) ^ (414723925 + 414723925) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 414723925 * (3 : ZMod 86262576401) ^ 414723925 := by rw [pow_add]
          _ = 79419957101 := by rw [factor_4_28]; decide
      have factor_4_30 : (3 : ZMod 86262576401) ^ 1658895700 = 11966496682 := by
        calc
          (3 : ZMod 86262576401) ^ 1658895700 = (3 : ZMod 86262576401) ^ (829447850 + 829447850) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 829447850 * (3 : ZMod 86262576401) ^ 829447850 := by rw [pow_add]
          _ = 11966496682 := by rw [factor_4_29]; decide
      have factor_4_31 : (3 : ZMod 86262576401) ^ 3317791400 = 3411796807 := by
        calc
          (3 : ZMod 86262576401) ^ 3317791400 = (3 : ZMod 86262576401) ^ (1658895700 + 1658895700) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1658895700 * (3 : ZMod 86262576401) ^ 1658895700 := by rw [pow_add]
          _ = 3411796807 := by rw [factor_4_30]; decide
      have factor_4_32 : (3 : ZMod 86262576401) ^ 6635582800 = 79016394660 := by
        calc
          (3 : ZMod 86262576401) ^ 6635582800 = (3 : ZMod 86262576401) ^ (3317791400 + 3317791400) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 3317791400 * (3 : ZMod 86262576401) ^ 3317791400 := by rw [pow_add]
          _ = 79016394660 := by rw [factor_4_31]; decide
      change (3 : ZMod 86262576401) ^ 6635582800 ≠ 1
      rw [factor_4_32]
      decide
    ·
      have factor_5_0 : (3 : ZMod 86262576401) ^ 1 = 3 := by norm_num
      have factor_5_1 : (3 : ZMod 86262576401) ^ 2 = 9 := by
        calc
          (3 : ZMod 86262576401) ^ 2 = (3 : ZMod 86262576401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1 * (3 : ZMod 86262576401) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_5_0]; decide
      have factor_5_2 : (3 : ZMod 86262576401) ^ 4 = 81 := by
        calc
          (3 : ZMod 86262576401) ^ 4 = (3 : ZMod 86262576401) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 2 * (3 : ZMod 86262576401) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_5_1]; decide
      have factor_5_3 : (3 : ZMod 86262576401) ^ 9 = 19683 := by
        calc
          (3 : ZMod 86262576401) ^ 9 = (3 : ZMod 86262576401) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 4 * (3 : ZMod 86262576401) ^ 4) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_5_2]; decide
      have factor_5_4 : (3 : ZMod 86262576401) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 86262576401) ^ 18 = (3 : ZMod 86262576401) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 9 * (3 : ZMod 86262576401) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [factor_5_3]; decide
      have factor_5_5 : (3 : ZMod 86262576401) ^ 37 = 71821313042 := by
        calc
          (3 : ZMod 86262576401) ^ 37 = (3 : ZMod 86262576401) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 18 * (3 : ZMod 86262576401) ^ 18) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 71821313042 := by rw [factor_5_4]; decide
      have factor_5_6 : (3 : ZMod 86262576401) ^ 75 = 4844102123 := by
        calc
          (3 : ZMod 86262576401) ^ 75 = (3 : ZMod 86262576401) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 37 * (3 : ZMod 86262576401) ^ 37) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 4844102123 := by rw [factor_5_5]; decide
      have factor_5_7 : (3 : ZMod 86262576401) ^ 151 = 16670248350 := by
        calc
          (3 : ZMod 86262576401) ^ 151 = (3 : ZMod 86262576401) ^ (75 + 75 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 75 * (3 : ZMod 86262576401) ^ 75) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 16670248350 := by rw [factor_5_6]; decide
      have factor_5_8 : (3 : ZMod 86262576401) ^ 302 = 75977928752 := by
        calc
          (3 : ZMod 86262576401) ^ 302 = (3 : ZMod 86262576401) ^ (151 + 151) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 151 * (3 : ZMod 86262576401) ^ 151 := by rw [pow_add]
          _ = 75977928752 := by rw [factor_5_7]; decide
      have factor_5_9 : (3 : ZMod 86262576401) ^ 604 = 41494993442 := by
        calc
          (3 : ZMod 86262576401) ^ 604 = (3 : ZMod 86262576401) ^ (302 + 302) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 302 * (3 : ZMod 86262576401) ^ 302 := by rw [pow_add]
          _ = 41494993442 := by rw [factor_5_8]; decide
      have factor_5_10 : (3 : ZMod 86262576401) ^ 1209 = 78983270983 := by
        calc
          (3 : ZMod 86262576401) ^ 1209 = (3 : ZMod 86262576401) ^ (604 + 604 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 604 * (3 : ZMod 86262576401) ^ 604) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 78983270983 := by rw [factor_5_9]; decide
      have factor_5_11 : (3 : ZMod 86262576401) ^ 2419 = 72907214413 := by
        calc
          (3 : ZMod 86262576401) ^ 2419 = (3 : ZMod 86262576401) ^ (1209 + 1209 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 1209 * (3 : ZMod 86262576401) ^ 1209) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 72907214413 := by rw [factor_5_10]; decide
      have factor_5_12 : (3 : ZMod 86262576401) ^ 4839 = 52815202797 := by
        calc
          (3 : ZMod 86262576401) ^ 4839 = (3 : ZMod 86262576401) ^ (2419 + 2419 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 2419 * (3 : ZMod 86262576401) ^ 2419) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 52815202797 := by rw [factor_5_11]; decide
      have factor_5_13 : (3 : ZMod 86262576401) ^ 9678 = 73529363930 := by
        calc
          (3 : ZMod 86262576401) ^ 9678 = (3 : ZMod 86262576401) ^ (4839 + 4839) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 4839 * (3 : ZMod 86262576401) ^ 4839 := by rw [pow_add]
          _ = 73529363930 := by rw [factor_5_12]; decide
      have factor_5_14 : (3 : ZMod 86262576401) ^ 19356 = 41704192098 := by
        calc
          (3 : ZMod 86262576401) ^ 19356 = (3 : ZMod 86262576401) ^ (9678 + 9678) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 9678 * (3 : ZMod 86262576401) ^ 9678 := by rw [pow_add]
          _ = 41704192098 := by rw [factor_5_13]; decide
      have factor_5_15 : (3 : ZMod 86262576401) ^ 38713 = 63206596772 := by
        calc
          (3 : ZMod 86262576401) ^ 38713 = (3 : ZMod 86262576401) ^ (19356 + 19356 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 19356 * (3 : ZMod 86262576401) ^ 19356) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 63206596772 := by rw [factor_5_14]; decide
      have factor_5_16 : (3 : ZMod 86262576401) ^ 77427 = 70322193767 := by
        calc
          (3 : ZMod 86262576401) ^ 77427 = (3 : ZMod 86262576401) ^ (38713 + 38713 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 38713 * (3 : ZMod 86262576401) ^ 38713) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 70322193767 := by rw [factor_5_15]; decide
      have factor_5_17 : (3 : ZMod 86262576401) ^ 154854 = 54200891622 := by
        calc
          (3 : ZMod 86262576401) ^ 154854 = (3 : ZMod 86262576401) ^ (77427 + 77427) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 77427 * (3 : ZMod 86262576401) ^ 77427 := by rw [pow_add]
          _ = 54200891622 := by rw [factor_5_16]; decide
      have factor_5_18 : (3 : ZMod 86262576401) ^ 309708 = 26133149854 := by
        calc
          (3 : ZMod 86262576401) ^ 309708 = (3 : ZMod 86262576401) ^ (154854 + 154854) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 154854 * (3 : ZMod 86262576401) ^ 154854 := by rw [pow_add]
          _ = 26133149854 := by rw [factor_5_17]; decide
      have factor_5_19 : (3 : ZMod 86262576401) ^ 619417 = 66839367468 := by
        calc
          (3 : ZMod 86262576401) ^ 619417 = (3 : ZMod 86262576401) ^ (309708 + 309708 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 309708 * (3 : ZMod 86262576401) ^ 309708) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 66839367468 := by rw [factor_5_18]; decide
      have factor_5_20 : (3 : ZMod 86262576401) ^ 1238835 = 41345164856 := by
        calc
          (3 : ZMod 86262576401) ^ 1238835 = (3 : ZMod 86262576401) ^ (619417 + 619417 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 619417 * (3 : ZMod 86262576401) ^ 619417) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 41345164856 := by rw [factor_5_19]; decide
      have factor_5_21 : (3 : ZMod 86262576401) ^ 2477670 = 52712463923 := by
        calc
          (3 : ZMod 86262576401) ^ 2477670 = (3 : ZMod 86262576401) ^ (1238835 + 1238835) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1238835 * (3 : ZMod 86262576401) ^ 1238835 := by rw [pow_add]
          _ = 52712463923 := by rw [factor_5_20]; decide
      have factor_5_22 : (3 : ZMod 86262576401) ^ 4955341 = 30985036835 := by
        calc
          (3 : ZMod 86262576401) ^ 4955341 = (3 : ZMod 86262576401) ^ (2477670 + 2477670 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 2477670 * (3 : ZMod 86262576401) ^ 2477670) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 30985036835 := by rw [factor_5_21]; decide
      have factor_5_23 : (3 : ZMod 86262576401) ^ 9910682 = 28481101026 := by
        calc
          (3 : ZMod 86262576401) ^ 9910682 = (3 : ZMod 86262576401) ^ (4955341 + 4955341) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 4955341 * (3 : ZMod 86262576401) ^ 4955341 := by rw [pow_add]
          _ = 28481101026 := by rw [factor_5_22]; decide
      have factor_5_24 : (3 : ZMod 86262576401) ^ 19821364 = 78439355349 := by
        calc
          (3 : ZMod 86262576401) ^ 19821364 = (3 : ZMod 86262576401) ^ (9910682 + 9910682) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 9910682 * (3 : ZMod 86262576401) ^ 9910682 := by rw [pow_add]
          _ = 78439355349 := by rw [factor_5_23]; decide
      have factor_5_25 : (3 : ZMod 86262576401) ^ 39642728 = 1348475020 := by
        calc
          (3 : ZMod 86262576401) ^ 39642728 = (3 : ZMod 86262576401) ^ (19821364 + 19821364) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 19821364 * (3 : ZMod 86262576401) ^ 19821364 := by rw [pow_add]
          _ = 1348475020 := by rw [factor_5_24]; decide
      have factor_5_26 : (3 : ZMod 86262576401) ^ 79285456 = 47195237151 := by
        calc
          (3 : ZMod 86262576401) ^ 79285456 = (3 : ZMod 86262576401) ^ (39642728 + 39642728) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 39642728 * (3 : ZMod 86262576401) ^ 39642728 := by rw [pow_add]
          _ = 47195237151 := by rw [factor_5_25]; decide
      have factor_5_27 : (3 : ZMod 86262576401) ^ 158570912 = 81365989511 := by
        calc
          (3 : ZMod 86262576401) ^ 158570912 = (3 : ZMod 86262576401) ^ (79285456 + 79285456) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 79285456 * (3 : ZMod 86262576401) ^ 79285456 := by rw [pow_add]
          _ = 81365989511 := by rw [factor_5_26]; decide
      have factor_5_28 : (3 : ZMod 86262576401) ^ 317141825 = 69454511272 := by
        calc
          (3 : ZMod 86262576401) ^ 317141825 = (3 : ZMod 86262576401) ^ (158570912 + 158570912 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 158570912 * (3 : ZMod 86262576401) ^ 158570912) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 69454511272 := by rw [factor_5_27]; decide
      have factor_5_29 : (3 : ZMod 86262576401) ^ 634283650 = 33530192508 := by
        calc
          (3 : ZMod 86262576401) ^ 634283650 = (3 : ZMod 86262576401) ^ (317141825 + 317141825) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 317141825 * (3 : ZMod 86262576401) ^ 317141825 := by rw [pow_add]
          _ = 33530192508 := by rw [factor_5_28]; decide
      have factor_5_30 : (3 : ZMod 86262576401) ^ 1268567300 = 77803142611 := by
        calc
          (3 : ZMod 86262576401) ^ 1268567300 = (3 : ZMod 86262576401) ^ (634283650 + 634283650) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 634283650 * (3 : ZMod 86262576401) ^ 634283650 := by rw [pow_add]
          _ = 77803142611 := by rw [factor_5_29]; decide
      have factor_5_31 : (3 : ZMod 86262576401) ^ 2537134600 = 77438494485 := by
        calc
          (3 : ZMod 86262576401) ^ 2537134600 = (3 : ZMod 86262576401) ^ (1268567300 + 1268567300) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1268567300 * (3 : ZMod 86262576401) ^ 1268567300 := by rw [pow_add]
          _ = 77438494485 := by rw [factor_5_30]; decide
      have factor_5_32 : (3 : ZMod 86262576401) ^ 5074269200 = 62539712771 := by
        calc
          (3 : ZMod 86262576401) ^ 5074269200 = (3 : ZMod 86262576401) ^ (2537134600 + 2537134600) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 2537134600 * (3 : ZMod 86262576401) ^ 2537134600 := by rw [pow_add]
          _ = 62539712771 := by rw [factor_5_31]; decide
      change (3 : ZMod 86262576401) ^ 5074269200 ≠ 1
      rw [factor_5_32]
      decide
    ·
      have factor_6_0 : (3 : ZMod 86262576401) ^ 1 = 3 := by norm_num
      have factor_6_1 : (3 : ZMod 86262576401) ^ 2 = 9 := by
        calc
          (3 : ZMod 86262576401) ^ 2 = (3 : ZMod 86262576401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1 * (3 : ZMod 86262576401) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_6_0]; decide
      have factor_6_2 : (3 : ZMod 86262576401) ^ 4 = 81 := by
        calc
          (3 : ZMod 86262576401) ^ 4 = (3 : ZMod 86262576401) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 2 * (3 : ZMod 86262576401) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_6_1]; decide
      have factor_6_3 : (3 : ZMod 86262576401) ^ 8 = 6561 := by
        calc
          (3 : ZMod 86262576401) ^ 8 = (3 : ZMod 86262576401) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 4 * (3 : ZMod 86262576401) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_6_2]; decide
      have factor_6_4 : (3 : ZMod 86262576401) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 86262576401) ^ 16 = (3 : ZMod 86262576401) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 8 * (3 : ZMod 86262576401) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_6_3]; decide
      have factor_6_5 : (3 : ZMod 86262576401) ^ 33 = 41355545880 := by
        calc
          (3 : ZMod 86262576401) ^ 33 = (3 : ZMod 86262576401) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 16 * (3 : ZMod 86262576401) ^ 16) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 41355545880 := by rw [factor_6_4]; decide
      have factor_6_6 : (3 : ZMod 86262576401) ^ 67 = 9099001215 := by
        calc
          (3 : ZMod 86262576401) ^ 67 = (3 : ZMod 86262576401) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 33 * (3 : ZMod 86262576401) ^ 33) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 9099001215 := by rw [factor_6_5]; decide
      have factor_6_7 : (3 : ZMod 86262576401) ^ 135 = 61315138529 := by
        calc
          (3 : ZMod 86262576401) ^ 135 = (3 : ZMod 86262576401) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 67 * (3 : ZMod 86262576401) ^ 67) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 61315138529 := by rw [factor_6_6]; decide
      have factor_6_8 : (3 : ZMod 86262576401) ^ 270 = 25068227166 := by
        calc
          (3 : ZMod 86262576401) ^ 270 = (3 : ZMod 86262576401) ^ (135 + 135) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 135 * (3 : ZMod 86262576401) ^ 135 := by rw [pow_add]
          _ = 25068227166 := by rw [factor_6_7]; decide
      have factor_6_9 : (3 : ZMod 86262576401) ^ 541 = 80777465098 := by
        calc
          (3 : ZMod 86262576401) ^ 541 = (3 : ZMod 86262576401) ^ (270 + 270 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 270 * (3 : ZMod 86262576401) ^ 270) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 80777465098 := by rw [factor_6_8]; decide
      have factor_6_10 : (3 : ZMod 86262576401) ^ 1082 = 6810851106 := by
        calc
          (3 : ZMod 86262576401) ^ 1082 = (3 : ZMod 86262576401) ^ (541 + 541) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 541 * (3 : ZMod 86262576401) ^ 541 := by rw [pow_add]
          _ = 6810851106 := by rw [factor_6_9]; decide
      have factor_6_11 : (3 : ZMod 86262576401) ^ 2164 = 5832972925 := by
        calc
          (3 : ZMod 86262576401) ^ 2164 = (3 : ZMod 86262576401) ^ (1082 + 1082) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1082 * (3 : ZMod 86262576401) ^ 1082 := by rw [pow_add]
          _ = 5832972925 := by rw [factor_6_10]; decide
      have factor_6_12 : (3 : ZMod 86262576401) ^ 4329 = 48200176379 := by
        calc
          (3 : ZMod 86262576401) ^ 4329 = (3 : ZMod 86262576401) ^ (2164 + 2164 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 2164 * (3 : ZMod 86262576401) ^ 2164) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 48200176379 := by rw [factor_6_11]; decide
      have factor_6_13 : (3 : ZMod 86262576401) ^ 8659 = 66103221394 := by
        calc
          (3 : ZMod 86262576401) ^ 8659 = (3 : ZMod 86262576401) ^ (4329 + 4329 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 4329 * (3 : ZMod 86262576401) ^ 4329) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 66103221394 := by rw [factor_6_12]; decide
      have factor_6_14 : (3 : ZMod 86262576401) ^ 17319 = 32861405749 := by
        calc
          (3 : ZMod 86262576401) ^ 17319 = (3 : ZMod 86262576401) ^ (8659 + 8659 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 8659 * (3 : ZMod 86262576401) ^ 8659) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 32861405749 := by rw [factor_6_13]; decide
      have factor_6_15 : (3 : ZMod 86262576401) ^ 34638 = 80172215025 := by
        calc
          (3 : ZMod 86262576401) ^ 34638 = (3 : ZMod 86262576401) ^ (17319 + 17319) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 17319 * (3 : ZMod 86262576401) ^ 17319 := by rw [pow_add]
          _ = 80172215025 := by rw [factor_6_14]; decide
      have factor_6_16 : (3 : ZMod 86262576401) ^ 69276 = 48314885685 := by
        calc
          (3 : ZMod 86262576401) ^ 69276 = (3 : ZMod 86262576401) ^ (34638 + 34638) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 34638 * (3 : ZMod 86262576401) ^ 34638 := by rw [pow_add]
          _ = 48314885685 := by rw [factor_6_15]; decide
      have factor_6_17 : (3 : ZMod 86262576401) ^ 138553 = 64123794713 := by
        calc
          (3 : ZMod 86262576401) ^ 138553 = (3 : ZMod 86262576401) ^ (69276 + 69276 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 69276 * (3 : ZMod 86262576401) ^ 69276) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 64123794713 := by rw [factor_6_16]; decide
      have factor_6_18 : (3 : ZMod 86262576401) ^ 277107 = 17524618617 := by
        calc
          (3 : ZMod 86262576401) ^ 277107 = (3 : ZMod 86262576401) ^ (138553 + 138553 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 138553 * (3 : ZMod 86262576401) ^ 138553) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 17524618617 := by rw [factor_6_17]; decide
      have factor_6_19 : (3 : ZMod 86262576401) ^ 554215 = 2156342358 := by
        calc
          (3 : ZMod 86262576401) ^ 554215 = (3 : ZMod 86262576401) ^ (277107 + 277107 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 277107 * (3 : ZMod 86262576401) ^ 277107) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 2156342358 := by rw [factor_6_18]; decide
      have factor_6_20 : (3 : ZMod 86262576401) ^ 1108431 = 57183857868 := by
        calc
          (3 : ZMod 86262576401) ^ 1108431 = (3 : ZMod 86262576401) ^ (554215 + 554215 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 554215 * (3 : ZMod 86262576401) ^ 554215) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 57183857868 := by rw [factor_6_19]; decide
      have factor_6_21 : (3 : ZMod 86262576401) ^ 2216863 = 53277128256 := by
        calc
          (3 : ZMod 86262576401) ^ 2216863 = (3 : ZMod 86262576401) ^ (1108431 + 1108431 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 1108431 * (3 : ZMod 86262576401) ^ 1108431) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 53277128256 := by rw [factor_6_20]; decide
      have factor_6_22 : (3 : ZMod 86262576401) ^ 4433726 = 57916090907 := by
        calc
          (3 : ZMod 86262576401) ^ 4433726 = (3 : ZMod 86262576401) ^ (2216863 + 2216863) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 2216863 * (3 : ZMod 86262576401) ^ 2216863 := by rw [pow_add]
          _ = 57916090907 := by rw [factor_6_21]; decide
      have factor_6_23 : (3 : ZMod 86262576401) ^ 8867452 = 64374576390 := by
        calc
          (3 : ZMod 86262576401) ^ 8867452 = (3 : ZMod 86262576401) ^ (4433726 + 4433726) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 4433726 * (3 : ZMod 86262576401) ^ 4433726 := by rw [pow_add]
          _ = 64374576390 := by rw [factor_6_22]; decide
      have factor_6_24 : (3 : ZMod 86262576401) ^ 17734904 = 4938895724 := by
        calc
          (3 : ZMod 86262576401) ^ 17734904 = (3 : ZMod 86262576401) ^ (8867452 + 8867452) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 8867452 * (3 : ZMod 86262576401) ^ 8867452 := by rw [pow_add]
          _ = 4938895724 := by rw [factor_6_23]; decide
      have factor_6_25 : (3 : ZMod 86262576401) ^ 35469809 = 7451139199 := by
        calc
          (3 : ZMod 86262576401) ^ 35469809 = (3 : ZMod 86262576401) ^ (17734904 + 17734904 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 17734904 * (3 : ZMod 86262576401) ^ 17734904) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 7451139199 := by rw [factor_6_24]; decide
      have factor_6_26 : (3 : ZMod 86262576401) ^ 70939618 = 18972825386 := by
        calc
          (3 : ZMod 86262576401) ^ 70939618 = (3 : ZMod 86262576401) ^ (35469809 + 35469809) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 35469809 * (3 : ZMod 86262576401) ^ 35469809 := by rw [pow_add]
          _ = 18972825386 := by rw [factor_6_25]; decide
      have factor_6_27 : (3 : ZMod 86262576401) ^ 141879237 = 24210996723 := by
        calc
          (3 : ZMod 86262576401) ^ 141879237 = (3 : ZMod 86262576401) ^ (70939618 + 70939618 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 70939618 * (3 : ZMod 86262576401) ^ 70939618) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 24210996723 := by rw [factor_6_26]; decide
      have factor_6_28 : (3 : ZMod 86262576401) ^ 283758475 = 61862437178 := by
        calc
          (3 : ZMod 86262576401) ^ 283758475 = (3 : ZMod 86262576401) ^ (141879237 + 141879237 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 141879237 * (3 : ZMod 86262576401) ^ 141879237) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 61862437178 := by rw [factor_6_27]; decide
      have factor_6_29 : (3 : ZMod 86262576401) ^ 567516950 = 65900272694 := by
        calc
          (3 : ZMod 86262576401) ^ 567516950 = (3 : ZMod 86262576401) ^ (283758475 + 283758475) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 283758475 * (3 : ZMod 86262576401) ^ 283758475 := by rw [pow_add]
          _ = 65900272694 := by rw [factor_6_28]; decide
      have factor_6_30 : (3 : ZMod 86262576401) ^ 1135033900 = 33728057937 := by
        calc
          (3 : ZMod 86262576401) ^ 1135033900 = (3 : ZMod 86262576401) ^ (567516950 + 567516950) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 567516950 * (3 : ZMod 86262576401) ^ 567516950 := by rw [pow_add]
          _ = 33728057937 := by rw [factor_6_29]; decide
      have factor_6_31 : (3 : ZMod 86262576401) ^ 2270067800 = 24008348401 := by
        calc
          (3 : ZMod 86262576401) ^ 2270067800 = (3 : ZMod 86262576401) ^ (1135033900 + 1135033900) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1135033900 * (3 : ZMod 86262576401) ^ 1135033900 := by rw [pow_add]
          _ = 24008348401 := by rw [factor_6_30]; decide
      have factor_6_32 : (3 : ZMod 86262576401) ^ 4540135600 = 18290847772 := by
        calc
          (3 : ZMod 86262576401) ^ 4540135600 = (3 : ZMod 86262576401) ^ (2270067800 + 2270067800) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 2270067800 * (3 : ZMod 86262576401) ^ 2270067800 := by rw [pow_add]
          _ = 18290847772 := by rw [factor_6_31]; decide
      change (3 : ZMod 86262576401) ^ 4540135600 ≠ 1
      rw [factor_6_32]
      decide
    ·
      have factor_7_0 : (3 : ZMod 86262576401) ^ 1 = 3 := by norm_num
      have factor_7_1 : (3 : ZMod 86262576401) ^ 3 = 27 := by
        calc
          (3 : ZMod 86262576401) ^ 3 = (3 : ZMod 86262576401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 1 * (3 : ZMod 86262576401) ^ 1) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_7_0]; decide
      have factor_7_2 : (3 : ZMod 86262576401) ^ 6 = 729 := by
        calc
          (3 : ZMod 86262576401) ^ 6 = (3 : ZMod 86262576401) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 3 * (3 : ZMod 86262576401) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_7_1]; decide
      have factor_7_3 : (3 : ZMod 86262576401) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 86262576401) ^ 13 = (3 : ZMod 86262576401) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 6 * (3 : ZMod 86262576401) ^ 6) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_7_2]; decide
      have factor_7_4 : (3 : ZMod 86262576401) ^ 27 = 34490761699 := by
        calc
          (3 : ZMod 86262576401) ^ 27 = (3 : ZMod 86262576401) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 13 * (3 : ZMod 86262576401) ^ 13) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 34490761699 := by rw [factor_7_3]; decide
      have factor_7_5 : (3 : ZMod 86262576401) ^ 55 = 72527547318 := by
        calc
          (3 : ZMod 86262576401) ^ 55 = (3 : ZMod 86262576401) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 27 * (3 : ZMod 86262576401) ^ 27) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 72527547318 := by rw [factor_7_4]; decide
      have factor_7_6 : (3 : ZMod 86262576401) ^ 111 = 77142144978 := by
        calc
          (3 : ZMod 86262576401) ^ 111 = (3 : ZMod 86262576401) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 55 * (3 : ZMod 86262576401) ^ 55) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 77142144978 := by rw [factor_7_5]; decide
      have factor_7_7 : (3 : ZMod 86262576401) ^ 223 = 18869858282 := by
        calc
          (3 : ZMod 86262576401) ^ 223 = (3 : ZMod 86262576401) ^ (111 + 111 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 111 * (3 : ZMod 86262576401) ^ 111) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 18869858282 := by rw [factor_7_6]; decide
      have factor_7_8 : (3 : ZMod 86262576401) ^ 447 = 13702891975 := by
        calc
          (3 : ZMod 86262576401) ^ 447 = (3 : ZMod 86262576401) ^ (223 + 223 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 223 * (3 : ZMod 86262576401) ^ 223) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 13702891975 := by rw [factor_7_7]; decide
      have factor_7_9 : (3 : ZMod 86262576401) ^ 894 = 45510615255 := by
        calc
          (3 : ZMod 86262576401) ^ 894 = (3 : ZMod 86262576401) ^ (447 + 447) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 447 * (3 : ZMod 86262576401) ^ 447 := by rw [pow_add]
          _ = 45510615255 := by rw [factor_7_8]; decide
      have factor_7_10 : (3 : ZMod 86262576401) ^ 1788 = 64215950771 := by
        calc
          (3 : ZMod 86262576401) ^ 1788 = (3 : ZMod 86262576401) ^ (894 + 894) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 894 * (3 : ZMod 86262576401) ^ 894 := by rw [pow_add]
          _ = 64215950771 := by rw [factor_7_9]; decide
      have factor_7_11 : (3 : ZMod 86262576401) ^ 3576 = 22310793661 := by
        calc
          (3 : ZMod 86262576401) ^ 3576 = (3 : ZMod 86262576401) ^ (1788 + 1788) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1788 * (3 : ZMod 86262576401) ^ 1788 := by rw [pow_add]
          _ = 22310793661 := by rw [factor_7_10]; decide
      have factor_7_12 : (3 : ZMod 86262576401) ^ 7153 = 82137309594 := by
        calc
          (3 : ZMod 86262576401) ^ 7153 = (3 : ZMod 86262576401) ^ (3576 + 3576 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 3576 * (3 : ZMod 86262576401) ^ 3576) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 82137309594 := by rw [factor_7_11]; decide
      have factor_7_13 : (3 : ZMod 86262576401) ^ 14307 = 58635858855 := by
        calc
          (3 : ZMod 86262576401) ^ 14307 = (3 : ZMod 86262576401) ^ (7153 + 7153 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 7153 * (3 : ZMod 86262576401) ^ 7153) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 58635858855 := by rw [factor_7_12]; decide
      have factor_7_14 : (3 : ZMod 86262576401) ^ 28614 = 73431494741 := by
        calc
          (3 : ZMod 86262576401) ^ 28614 = (3 : ZMod 86262576401) ^ (14307 + 14307) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 14307 * (3 : ZMod 86262576401) ^ 14307 := by rw [pow_add]
          _ = 73431494741 := by rw [factor_7_13]; decide
      have factor_7_15 : (3 : ZMod 86262576401) ^ 57228 = 28918191892 := by
        calc
          (3 : ZMod 86262576401) ^ 57228 = (3 : ZMod 86262576401) ^ (28614 + 28614) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 28614 * (3 : ZMod 86262576401) ^ 28614 := by rw [pow_add]
          _ = 28918191892 := by rw [factor_7_14]; decide
      have factor_7_16 : (3 : ZMod 86262576401) ^ 114457 = 19815858368 := by
        calc
          (3 : ZMod 86262576401) ^ 114457 = (3 : ZMod 86262576401) ^ (57228 + 57228 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 57228 * (3 : ZMod 86262576401) ^ 57228) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 19815858368 := by rw [factor_7_15]; decide
      have factor_7_17 : (3 : ZMod 86262576401) ^ 228915 = 47131937266 := by
        calc
          (3 : ZMod 86262576401) ^ 228915 = (3 : ZMod 86262576401) ^ (114457 + 114457 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 114457 * (3 : ZMod 86262576401) ^ 114457) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 47131937266 := by rw [factor_7_16]; decide
      have factor_7_18 : (3 : ZMod 86262576401) ^ 457830 = 79510855191 := by
        calc
          (3 : ZMod 86262576401) ^ 457830 = (3 : ZMod 86262576401) ^ (228915 + 228915) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 228915 * (3 : ZMod 86262576401) ^ 228915 := by rw [pow_add]
          _ = 79510855191 := by rw [factor_7_17]; decide
      have factor_7_19 : (3 : ZMod 86262576401) ^ 915660 = 13769228845 := by
        calc
          (3 : ZMod 86262576401) ^ 915660 = (3 : ZMod 86262576401) ^ (457830 + 457830) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 457830 * (3 : ZMod 86262576401) ^ 457830 := by rw [pow_add]
          _ = 13769228845 := by rw [factor_7_18]; decide
      have factor_7_20 : (3 : ZMod 86262576401) ^ 1831321 = 65562890875 := by
        calc
          (3 : ZMod 86262576401) ^ 1831321 = (3 : ZMod 86262576401) ^ (915660 + 915660 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 915660 * (3 : ZMod 86262576401) ^ 915660) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 65562890875 := by rw [factor_7_19]; decide
      have factor_7_21 : (3 : ZMod 86262576401) ^ 3662643 = 55468163287 := by
        calc
          (3 : ZMod 86262576401) ^ 3662643 = (3 : ZMod 86262576401) ^ (1831321 + 1831321 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 1831321 * (3 : ZMod 86262576401) ^ 1831321) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 55468163287 := by rw [factor_7_20]; decide
      have factor_7_22 : (3 : ZMod 86262576401) ^ 7325286 = 5876107512 := by
        calc
          (3 : ZMod 86262576401) ^ 7325286 = (3 : ZMod 86262576401) ^ (3662643 + 3662643) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 3662643 * (3 : ZMod 86262576401) ^ 3662643 := by rw [pow_add]
          _ = 5876107512 := by rw [factor_7_21]; decide
      have factor_7_23 : (3 : ZMod 86262576401) ^ 14650573 = 45568685372 := by
        calc
          (3 : ZMod 86262576401) ^ 14650573 = (3 : ZMod 86262576401) ^ (7325286 + 7325286 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 7325286 * (3 : ZMod 86262576401) ^ 7325286) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 45568685372 := by rw [factor_7_22]; decide
      have factor_7_24 : (3 : ZMod 86262576401) ^ 29301146 = 19395040297 := by
        calc
          (3 : ZMod 86262576401) ^ 29301146 = (3 : ZMod 86262576401) ^ (14650573 + 14650573) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 14650573 * (3 : ZMod 86262576401) ^ 14650573 := by rw [pow_add]
          _ = 19395040297 := by rw [factor_7_23]; decide
      have factor_7_25 : (3 : ZMod 86262576401) ^ 58602293 = 74139112563 := by
        calc
          (3 : ZMod 86262576401) ^ 58602293 = (3 : ZMod 86262576401) ^ (29301146 + 29301146 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 29301146 * (3 : ZMod 86262576401) ^ 29301146) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 74139112563 := by rw [factor_7_24]; decide
      have factor_7_26 : (3 : ZMod 86262576401) ^ 117204587 = 63068617945 := by
        calc
          (3 : ZMod 86262576401) ^ 117204587 = (3 : ZMod 86262576401) ^ (58602293 + 58602293 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 58602293 * (3 : ZMod 86262576401) ^ 58602293) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 63068617945 := by rw [factor_7_25]; decide
      have factor_7_27 : (3 : ZMod 86262576401) ^ 234409175 = 79507870971 := by
        calc
          (3 : ZMod 86262576401) ^ 234409175 = (3 : ZMod 86262576401) ^ (117204587 + 117204587 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 117204587 * (3 : ZMod 86262576401) ^ 117204587) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 79507870971 := by rw [factor_7_26]; decide
      have factor_7_28 : (3 : ZMod 86262576401) ^ 468818350 = 59716058796 := by
        calc
          (3 : ZMod 86262576401) ^ 468818350 = (3 : ZMod 86262576401) ^ (234409175 + 234409175) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 234409175 * (3 : ZMod 86262576401) ^ 234409175 := by rw [pow_add]
          _ = 59716058796 := by rw [factor_7_27]; decide
      have factor_7_29 : (3 : ZMod 86262576401) ^ 937636700 = 66234612435 := by
        calc
          (3 : ZMod 86262576401) ^ 937636700 = (3 : ZMod 86262576401) ^ (468818350 + 468818350) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 468818350 * (3 : ZMod 86262576401) ^ 468818350 := by rw [pow_add]
          _ = 66234612435 := by rw [factor_7_28]; decide
      have factor_7_30 : (3 : ZMod 86262576401) ^ 1875273400 = 37796679364 := by
        calc
          (3 : ZMod 86262576401) ^ 1875273400 = (3 : ZMod 86262576401) ^ (937636700 + 937636700) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 937636700 * (3 : ZMod 86262576401) ^ 937636700 := by rw [pow_add]
          _ = 37796679364 := by rw [factor_7_29]; decide
      have factor_7_31 : (3 : ZMod 86262576401) ^ 3750546800 = 30709044114 := by
        calc
          (3 : ZMod 86262576401) ^ 3750546800 = (3 : ZMod 86262576401) ^ (1875273400 + 1875273400) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1875273400 * (3 : ZMod 86262576401) ^ 1875273400 := by rw [pow_add]
          _ = 30709044114 := by rw [factor_7_30]; decide
      change (3 : ZMod 86262576401) ^ 3750546800 ≠ 1
      rw [factor_7_31]
      decide
    ·
      have factor_8_0 : (3 : ZMod 86262576401) ^ 1 = 3 := by norm_num
      have factor_8_1 : (3 : ZMod 86262576401) ^ 2 = 9 := by
        calc
          (3 : ZMod 86262576401) ^ 2 = (3 : ZMod 86262576401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1 * (3 : ZMod 86262576401) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_8_0]; decide
      have factor_8_2 : (3 : ZMod 86262576401) ^ 5 = 243 := by
        calc
          (3 : ZMod 86262576401) ^ 5 = (3 : ZMod 86262576401) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 2 * (3 : ZMod 86262576401) ^ 2) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_8_1]; decide
      have factor_8_3 : (3 : ZMod 86262576401) ^ 11 = 177147 := by
        calc
          (3 : ZMod 86262576401) ^ 11 = (3 : ZMod 86262576401) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 5 * (3 : ZMod 86262576401) ^ 5) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_8_2]; decide
      have factor_8_4 : (3 : ZMod 86262576401) ^ 22 = 31381059609 := by
        calc
          (3 : ZMod 86262576401) ^ 22 = (3 : ZMod 86262576401) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 11 * (3 : ZMod 86262576401) ^ 11 := by rw [pow_add]
          _ = 31381059609 := by rw [factor_8_3]; decide
      have factor_8_5 : (3 : ZMod 86262576401) ^ 44 = 75322573034 := by
        calc
          (3 : ZMod 86262576401) ^ 44 = (3 : ZMod 86262576401) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 22 * (3 : ZMod 86262576401) ^ 22 := by rw [pow_add]
          _ = 75322573034 := by rw [factor_8_4]; decide
      have factor_8_6 : (3 : ZMod 86262576401) ^ 88 = 61226442600 := by
        calc
          (3 : ZMod 86262576401) ^ 88 = (3 : ZMod 86262576401) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 44 * (3 : ZMod 86262576401) ^ 44 := by rw [pow_add]
          _ = 61226442600 := by rw [factor_8_5]; decide
      have factor_8_7 : (3 : ZMod 86262576401) ^ 177 = 18150132123 := by
        calc
          (3 : ZMod 86262576401) ^ 177 = (3 : ZMod 86262576401) ^ (88 + 88 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 88 * (3 : ZMod 86262576401) ^ 88) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 18150132123 := by rw [factor_8_6]; decide
      have factor_8_8 : (3 : ZMod 86262576401) ^ 354 = 83274131064 := by
        calc
          (3 : ZMod 86262576401) ^ 354 = (3 : ZMod 86262576401) ^ (177 + 177) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 177 * (3 : ZMod 86262576401) ^ 177 := by rw [pow_add]
          _ = 83274131064 := by rw [factor_8_7]; decide
      have factor_8_9 : (3 : ZMod 86262576401) ^ 709 = 68153169282 := by
        calc
          (3 : ZMod 86262576401) ^ 709 = (3 : ZMod 86262576401) ^ (354 + 354 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 354 * (3 : ZMod 86262576401) ^ 354) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 68153169282 := by rw [factor_8_8]; decide
      have factor_8_10 : (3 : ZMod 86262576401) ^ 1418 = 71886832010 := by
        calc
          (3 : ZMod 86262576401) ^ 1418 = (3 : ZMod 86262576401) ^ (709 + 709) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 709 * (3 : ZMod 86262576401) ^ 709 := by rw [pow_add]
          _ = 71886832010 := by rw [factor_8_9]; decide
      have factor_8_11 : (3 : ZMod 86262576401) ^ 2836 = 32286732741 := by
        calc
          (3 : ZMod 86262576401) ^ 2836 = (3 : ZMod 86262576401) ^ (1418 + 1418) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1418 * (3 : ZMod 86262576401) ^ 1418 := by rw [pow_add]
          _ = 32286732741 := by rw [factor_8_10]; decide
      have factor_8_12 : (3 : ZMod 86262576401) ^ 5673 = 65149988458 := by
        calc
          (3 : ZMod 86262576401) ^ 5673 = (3 : ZMod 86262576401) ^ (2836 + 2836 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 2836 * (3 : ZMod 86262576401) ^ 2836) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 65149988458 := by rw [factor_8_11]; decide
      have factor_8_13 : (3 : ZMod 86262576401) ^ 11347 = 49777545675 := by
        calc
          (3 : ZMod 86262576401) ^ 11347 = (3 : ZMod 86262576401) ^ (5673 + 5673 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 5673 * (3 : ZMod 86262576401) ^ 5673) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 49777545675 := by rw [factor_8_12]; decide
      have factor_8_14 : (3 : ZMod 86262576401) ^ 22694 = 40090367426 := by
        calc
          (3 : ZMod 86262576401) ^ 22694 = (3 : ZMod 86262576401) ^ (11347 + 11347) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 11347 * (3 : ZMod 86262576401) ^ 11347 := by rw [pow_add]
          _ = 40090367426 := by rw [factor_8_13]; decide
      have factor_8_15 : (3 : ZMod 86262576401) ^ 45388 = 6764856678 := by
        calc
          (3 : ZMod 86262576401) ^ 45388 = (3 : ZMod 86262576401) ^ (22694 + 22694) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 22694 * (3 : ZMod 86262576401) ^ 22694 := by rw [pow_add]
          _ = 6764856678 := by rw [factor_8_14]; decide
      have factor_8_16 : (3 : ZMod 86262576401) ^ 90776 = 6449681818 := by
        calc
          (3 : ZMod 86262576401) ^ 90776 = (3 : ZMod 86262576401) ^ (45388 + 45388) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 45388 * (3 : ZMod 86262576401) ^ 45388 := by rw [pow_add]
          _ = 6449681818 := by rw [factor_8_15]; decide
      have factor_8_17 : (3 : ZMod 86262576401) ^ 181553 = 19674390404 := by
        calc
          (3 : ZMod 86262576401) ^ 181553 = (3 : ZMod 86262576401) ^ (90776 + 90776 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 90776 * (3 : ZMod 86262576401) ^ 90776) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 19674390404 := by rw [factor_8_16]; decide
      have factor_8_18 : (3 : ZMod 86262576401) ^ 363106 = 73153416471 := by
        calc
          (3 : ZMod 86262576401) ^ 363106 = (3 : ZMod 86262576401) ^ (181553 + 181553) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 181553 * (3 : ZMod 86262576401) ^ 181553 := by rw [pow_add]
          _ = 73153416471 := by rw [factor_8_17]; decide
      have factor_8_19 : (3 : ZMod 86262576401) ^ 726213 = 84625675077 := by
        calc
          (3 : ZMod 86262576401) ^ 726213 = (3 : ZMod 86262576401) ^ (363106 + 363106 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 363106 * (3 : ZMod 86262576401) ^ 363106) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 84625675077 := by rw [factor_8_18]; decide
      have factor_8_20 : (3 : ZMod 86262576401) ^ 1452427 = 22497429596 := by
        calc
          (3 : ZMod 86262576401) ^ 1452427 = (3 : ZMod 86262576401) ^ (726213 + 726213 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 726213 * (3 : ZMod 86262576401) ^ 726213) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 22497429596 := by rw [factor_8_19]; decide
      have factor_8_21 : (3 : ZMod 86262576401) ^ 2904855 = 84703288430 := by
        calc
          (3 : ZMod 86262576401) ^ 2904855 = (3 : ZMod 86262576401) ^ (1452427 + 1452427 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 1452427 * (3 : ZMod 86262576401) ^ 1452427) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 84703288430 := by rw [factor_8_20]; decide
      have factor_8_22 : (3 : ZMod 86262576401) ^ 5809710 = 26945178650 := by
        calc
          (3 : ZMod 86262576401) ^ 5809710 = (3 : ZMod 86262576401) ^ (2904855 + 2904855) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 2904855 * (3 : ZMod 86262576401) ^ 2904855 := by rw [pow_add]
          _ = 26945178650 := by rw [factor_8_21]; decide
      have factor_8_23 : (3 : ZMod 86262576401) ^ 11619420 = 62234874336 := by
        calc
          (3 : ZMod 86262576401) ^ 11619420 = (3 : ZMod 86262576401) ^ (5809710 + 5809710) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 5809710 * (3 : ZMod 86262576401) ^ 5809710 := by rw [pow_add]
          _ = 62234874336 := by rw [factor_8_22]; decide
      have factor_8_24 : (3 : ZMod 86262576401) ^ 23238840 = 74854025144 := by
        calc
          (3 : ZMod 86262576401) ^ 23238840 = (3 : ZMod 86262576401) ^ (11619420 + 11619420) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 11619420 * (3 : ZMod 86262576401) ^ 11619420 := by rw [pow_add]
          _ = 74854025144 := by rw [factor_8_23]; decide
      have factor_8_25 : (3 : ZMod 86262576401) ^ 46477681 = 10461653079 := by
        calc
          (3 : ZMod 86262576401) ^ 46477681 = (3 : ZMod 86262576401) ^ (23238840 + 23238840 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 23238840 * (3 : ZMod 86262576401) ^ 23238840) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 10461653079 := by rw [factor_8_24]; decide
      have factor_8_26 : (3 : ZMod 86262576401) ^ 92955362 = 38914513966 := by
        calc
          (3 : ZMod 86262576401) ^ 92955362 = (3 : ZMod 86262576401) ^ (46477681 + 46477681) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 46477681 * (3 : ZMod 86262576401) ^ 46477681 := by rw [pow_add]
          _ = 38914513966 := by rw [factor_8_25]; decide
      have factor_8_27 : (3 : ZMod 86262576401) ^ 185910725 = 36386605642 := by
        calc
          (3 : ZMod 86262576401) ^ 185910725 = (3 : ZMod 86262576401) ^ (92955362 + 92955362 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = ((3 : ZMod 86262576401) ^ 92955362 * (3 : ZMod 86262576401) ^ 92955362) * (3 : ZMod 86262576401) := by rw [pow_succ, pow_add]
          _ = 36386605642 := by rw [factor_8_26]; decide
      have factor_8_28 : (3 : ZMod 86262576401) ^ 371821450 = 85572851416 := by
        calc
          (3 : ZMod 86262576401) ^ 371821450 = (3 : ZMod 86262576401) ^ (185910725 + 185910725) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 185910725 * (3 : ZMod 86262576401) ^ 185910725 := by rw [pow_add]
          _ = 85572851416 := by rw [factor_8_27]; decide
      have factor_8_29 : (3 : ZMod 86262576401) ^ 743642900 = 43647321029 := by
        calc
          (3 : ZMod 86262576401) ^ 743642900 = (3 : ZMod 86262576401) ^ (371821450 + 371821450) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 371821450 * (3 : ZMod 86262576401) ^ 371821450 := by rw [pow_add]
          _ = 43647321029 := by rw [factor_8_28]; decide
      have factor_8_30 : (3 : ZMod 86262576401) ^ 1487285800 = 45576624144 := by
        calc
          (3 : ZMod 86262576401) ^ 1487285800 = (3 : ZMod 86262576401) ^ (743642900 + 743642900) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 743642900 * (3 : ZMod 86262576401) ^ 743642900 := by rw [pow_add]
          _ = 45576624144 := by rw [factor_8_29]; decide
      have factor_8_31 : (3 : ZMod 86262576401) ^ 2974571600 = 59262898118 := by
        calc
          (3 : ZMod 86262576401) ^ 2974571600 = (3 : ZMod 86262576401) ^ (1487285800 + 1487285800) :=
            congrArg (fun n : ℕ => (3 : ZMod 86262576401) ^ n) (by norm_num)
          _ = (3 : ZMod 86262576401) ^ 1487285800 * (3 : ZMod 86262576401) ^ 1487285800 := by rw [pow_add]
          _ = 59262898118 := by rw [factor_8_30]; decide
      change (3 : ZMod 86262576401) ^ 2974571600 ≠ 1
      rw [factor_8_31]
      decide

#print axioms prime_lucas_86262576401

end TotientTailPeriodKiller
end Erdos249257
