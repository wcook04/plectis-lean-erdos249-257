import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1526311613 : Nat.Prime 1526311613 := by
  apply lucas_primality 1526311613 (2 : ZMod 1526311613)
  ·
      have fermat_0 : (2 : ZMod 1526311613) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 1526311613) ^ 2 = 4 := by
        calc
          (2 : ZMod 1526311613) ^ 2 = (2 : ZMod 1526311613) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 1 * (2 : ZMod 1526311613) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 1526311613) ^ 5 = 32 := by
        calc
          (2 : ZMod 1526311613) ^ 5 = (2 : ZMod 1526311613) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 2 * (2 : ZMod 1526311613) ^ 2) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 1526311613) ^ 11 = 2048 := by
        calc
          (2 : ZMod 1526311613) ^ 11 = (2 : ZMod 1526311613) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 5 * (2 : ZMod 1526311613) ^ 5) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 1526311613) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 1526311613) ^ 22 = (2 : ZMod 1526311613) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 11 * (2 : ZMod 1526311613) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 1526311613) ^ 45 = 1363097569 := by
        calc
          (2 : ZMod 1526311613) ^ 45 = (2 : ZMod 1526311613) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 22 * (2 : ZMod 1526311613) ^ 22) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1363097569 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 1526311613) ^ 90 = 735332026 := by
        calc
          (2 : ZMod 1526311613) ^ 90 = (2 : ZMod 1526311613) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 45 * (2 : ZMod 1526311613) ^ 45 := by rw [pow_add]
          _ = 735332026 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 1526311613) ^ 181 = 680385868 := by
        calc
          (2 : ZMod 1526311613) ^ 181 = (2 : ZMod 1526311613) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 90 * (2 : ZMod 1526311613) ^ 90) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 680385868 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 1526311613) ^ 363 = 904544950 := by
        calc
          (2 : ZMod 1526311613) ^ 363 = (2 : ZMod 1526311613) ^ (181 + 181 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 181 * (2 : ZMod 1526311613) ^ 181) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 904544950 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 1526311613) ^ 727 = 544287988 := by
        calc
          (2 : ZMod 1526311613) ^ 727 = (2 : ZMod 1526311613) ^ (363 + 363 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 363 * (2 : ZMod 1526311613) ^ 363) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 544287988 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 1526311613) ^ 1455 = 553598551 := by
        calc
          (2 : ZMod 1526311613) ^ 1455 = (2 : ZMod 1526311613) ^ (727 + 727 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 727 * (2 : ZMod 1526311613) ^ 727) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 553598551 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 1526311613) ^ 2911 = 860457500 := by
        calc
          (2 : ZMod 1526311613) ^ 2911 = (2 : ZMod 1526311613) ^ (1455 + 1455 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 1455 * (2 : ZMod 1526311613) ^ 1455) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 860457500 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 1526311613) ^ 5822 = 1345959432 := by
        calc
          (2 : ZMod 1526311613) ^ 5822 = (2 : ZMod 1526311613) ^ (2911 + 2911) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 2911 * (2 : ZMod 1526311613) ^ 2911 := by rw [pow_add]
          _ = 1345959432 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 1526311613) ^ 11644 = 1405940878 := by
        calc
          (2 : ZMod 1526311613) ^ 11644 = (2 : ZMod 1526311613) ^ (5822 + 5822) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 5822 * (2 : ZMod 1526311613) ^ 5822 := by rw [pow_add]
          _ = 1405940878 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 1526311613) ^ 23289 = 508836019 := by
        calc
          (2 : ZMod 1526311613) ^ 23289 = (2 : ZMod 1526311613) ^ (11644 + 11644 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 11644 * (2 : ZMod 1526311613) ^ 11644) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 508836019 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 1526311613) ^ 46579 = 774461786 := by
        calc
          (2 : ZMod 1526311613) ^ 46579 = (2 : ZMod 1526311613) ^ (23289 + 23289 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 23289 * (2 : ZMod 1526311613) ^ 23289) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 774461786 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 1526311613) ^ 93158 = 772222606 := by
        calc
          (2 : ZMod 1526311613) ^ 93158 = (2 : ZMod 1526311613) ^ (46579 + 46579) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 46579 * (2 : ZMod 1526311613) ^ 46579 := by rw [pow_add]
          _ = 772222606 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 1526311613) ^ 186317 = 182549847 := by
        calc
          (2 : ZMod 1526311613) ^ 186317 = (2 : ZMod 1526311613) ^ (93158 + 93158 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 93158 * (2 : ZMod 1526311613) ^ 93158) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 182549847 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 1526311613) ^ 372634 = 1352313088 := by
        calc
          (2 : ZMod 1526311613) ^ 372634 = (2 : ZMod 1526311613) ^ (186317 + 186317) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 186317 * (2 : ZMod 1526311613) ^ 186317 := by rw [pow_add]
          _ = 1352313088 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 1526311613) ^ 745269 = 1459476595 := by
        calc
          (2 : ZMod 1526311613) ^ 745269 = (2 : ZMod 1526311613) ^ (372634 + 372634 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 372634 * (2 : ZMod 1526311613) ^ 372634) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1459476595 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 1526311613) ^ 1490538 = 801338394 := by
        calc
          (2 : ZMod 1526311613) ^ 1490538 = (2 : ZMod 1526311613) ^ (745269 + 745269) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 745269 * (2 : ZMod 1526311613) ^ 745269 := by rw [pow_add]
          _ = 801338394 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 1526311613) ^ 2981077 = 823419309 := by
        calc
          (2 : ZMod 1526311613) ^ 2981077 = (2 : ZMod 1526311613) ^ (1490538 + 1490538 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 1490538 * (2 : ZMod 1526311613) ^ 1490538) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 823419309 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 1526311613) ^ 5962154 = 289445146 := by
        calc
          (2 : ZMod 1526311613) ^ 5962154 = (2 : ZMod 1526311613) ^ (2981077 + 2981077) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 2981077 * (2 : ZMod 1526311613) ^ 2981077 := by rw [pow_add]
          _ = 289445146 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 1526311613) ^ 11924309 = 1154033050 := by
        calc
          (2 : ZMod 1526311613) ^ 11924309 = (2 : ZMod 1526311613) ^ (5962154 + 5962154 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 5962154 * (2 : ZMod 1526311613) ^ 5962154) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1154033050 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 1526311613) ^ 23848618 = 1015055150 := by
        calc
          (2 : ZMod 1526311613) ^ 23848618 = (2 : ZMod 1526311613) ^ (11924309 + 11924309) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 11924309 * (2 : ZMod 1526311613) ^ 11924309 := by rw [pow_add]
          _ = 1015055150 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 1526311613) ^ 47697237 = 426034639 := by
        calc
          (2 : ZMod 1526311613) ^ 47697237 = (2 : ZMod 1526311613) ^ (23848618 + 23848618 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 23848618 * (2 : ZMod 1526311613) ^ 23848618) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 426034639 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 1526311613) ^ 95394475 = 1148212049 := by
        calc
          (2 : ZMod 1526311613) ^ 95394475 = (2 : ZMod 1526311613) ^ (47697237 + 47697237 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 47697237 * (2 : ZMod 1526311613) ^ 47697237) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1148212049 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 1526311613) ^ 190788951 = 115930534 := by
        calc
          (2 : ZMod 1526311613) ^ 190788951 = (2 : ZMod 1526311613) ^ (95394475 + 95394475 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 95394475 * (2 : ZMod 1526311613) ^ 95394475) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 115930534 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 1526311613) ^ 381577903 = 1294450544 := by
        calc
          (2 : ZMod 1526311613) ^ 381577903 = (2 : ZMod 1526311613) ^ (190788951 + 190788951 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 190788951 * (2 : ZMod 1526311613) ^ 190788951) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1294450544 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 1526311613) ^ 763155806 = 1526311612 := by
        calc
          (2 : ZMod 1526311613) ^ 763155806 = (2 : ZMod 1526311613) ^ (381577903 + 381577903) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 381577903 * (2 : ZMod 1526311613) ^ 381577903 := by rw [pow_add]
          _ = 1526311612 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 1526311613) ^ 1526311612 = 1 := by
        calc
          (2 : ZMod 1526311613) ^ 1526311612 = (2 : ZMod 1526311613) ^ (763155806 + 763155806) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 763155806 * (2 : ZMod 1526311613) ^ 763155806 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (17, 1), (3206537, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (17, 1), (3206537, 1)] : List FactorBlock).map factorBlockValue).prod = 1526311613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 1526311613) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 1526311613) ^ 2 = 4 := by
        calc
          (2 : ZMod 1526311613) ^ 2 = (2 : ZMod 1526311613) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 1 * (2 : ZMod 1526311613) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 1526311613) ^ 5 = 32 := by
        calc
          (2 : ZMod 1526311613) ^ 5 = (2 : ZMod 1526311613) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 2 * (2 : ZMod 1526311613) ^ 2) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 1526311613) ^ 11 = 2048 := by
        calc
          (2 : ZMod 1526311613) ^ 11 = (2 : ZMod 1526311613) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 5 * (2 : ZMod 1526311613) ^ 5) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 1526311613) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 1526311613) ^ 22 = (2 : ZMod 1526311613) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 11 * (2 : ZMod 1526311613) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 1526311613) ^ 45 = 1363097569 := by
        calc
          (2 : ZMod 1526311613) ^ 45 = (2 : ZMod 1526311613) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 22 * (2 : ZMod 1526311613) ^ 22) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1363097569 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 1526311613) ^ 90 = 735332026 := by
        calc
          (2 : ZMod 1526311613) ^ 90 = (2 : ZMod 1526311613) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 45 * (2 : ZMod 1526311613) ^ 45 := by rw [pow_add]
          _ = 735332026 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 1526311613) ^ 181 = 680385868 := by
        calc
          (2 : ZMod 1526311613) ^ 181 = (2 : ZMod 1526311613) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 90 * (2 : ZMod 1526311613) ^ 90) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 680385868 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 1526311613) ^ 363 = 904544950 := by
        calc
          (2 : ZMod 1526311613) ^ 363 = (2 : ZMod 1526311613) ^ (181 + 181 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 181 * (2 : ZMod 1526311613) ^ 181) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 904544950 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 1526311613) ^ 727 = 544287988 := by
        calc
          (2 : ZMod 1526311613) ^ 727 = (2 : ZMod 1526311613) ^ (363 + 363 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 363 * (2 : ZMod 1526311613) ^ 363) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 544287988 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 1526311613) ^ 1455 = 553598551 := by
        calc
          (2 : ZMod 1526311613) ^ 1455 = (2 : ZMod 1526311613) ^ (727 + 727 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 727 * (2 : ZMod 1526311613) ^ 727) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 553598551 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 1526311613) ^ 2911 = 860457500 := by
        calc
          (2 : ZMod 1526311613) ^ 2911 = (2 : ZMod 1526311613) ^ (1455 + 1455 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 1455 * (2 : ZMod 1526311613) ^ 1455) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 860457500 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 1526311613) ^ 5822 = 1345959432 := by
        calc
          (2 : ZMod 1526311613) ^ 5822 = (2 : ZMod 1526311613) ^ (2911 + 2911) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 2911 * (2 : ZMod 1526311613) ^ 2911 := by rw [pow_add]
          _ = 1345959432 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 1526311613) ^ 11644 = 1405940878 := by
        calc
          (2 : ZMod 1526311613) ^ 11644 = (2 : ZMod 1526311613) ^ (5822 + 5822) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 5822 * (2 : ZMod 1526311613) ^ 5822 := by rw [pow_add]
          _ = 1405940878 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 1526311613) ^ 23289 = 508836019 := by
        calc
          (2 : ZMod 1526311613) ^ 23289 = (2 : ZMod 1526311613) ^ (11644 + 11644 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 11644 * (2 : ZMod 1526311613) ^ 11644) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 508836019 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 1526311613) ^ 46579 = 774461786 := by
        calc
          (2 : ZMod 1526311613) ^ 46579 = (2 : ZMod 1526311613) ^ (23289 + 23289 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 23289 * (2 : ZMod 1526311613) ^ 23289) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 774461786 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 1526311613) ^ 93158 = 772222606 := by
        calc
          (2 : ZMod 1526311613) ^ 93158 = (2 : ZMod 1526311613) ^ (46579 + 46579) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 46579 * (2 : ZMod 1526311613) ^ 46579 := by rw [pow_add]
          _ = 772222606 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 1526311613) ^ 186317 = 182549847 := by
        calc
          (2 : ZMod 1526311613) ^ 186317 = (2 : ZMod 1526311613) ^ (93158 + 93158 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 93158 * (2 : ZMod 1526311613) ^ 93158) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 182549847 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 1526311613) ^ 372634 = 1352313088 := by
        calc
          (2 : ZMod 1526311613) ^ 372634 = (2 : ZMod 1526311613) ^ (186317 + 186317) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 186317 * (2 : ZMod 1526311613) ^ 186317 := by rw [pow_add]
          _ = 1352313088 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 1526311613) ^ 745269 = 1459476595 := by
        calc
          (2 : ZMod 1526311613) ^ 745269 = (2 : ZMod 1526311613) ^ (372634 + 372634 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 372634 * (2 : ZMod 1526311613) ^ 372634) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1459476595 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 1526311613) ^ 1490538 = 801338394 := by
        calc
          (2 : ZMod 1526311613) ^ 1490538 = (2 : ZMod 1526311613) ^ (745269 + 745269) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 745269 * (2 : ZMod 1526311613) ^ 745269 := by rw [pow_add]
          _ = 801338394 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 1526311613) ^ 2981077 = 823419309 := by
        calc
          (2 : ZMod 1526311613) ^ 2981077 = (2 : ZMod 1526311613) ^ (1490538 + 1490538 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 1490538 * (2 : ZMod 1526311613) ^ 1490538) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 823419309 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 1526311613) ^ 5962154 = 289445146 := by
        calc
          (2 : ZMod 1526311613) ^ 5962154 = (2 : ZMod 1526311613) ^ (2981077 + 2981077) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 2981077 * (2 : ZMod 1526311613) ^ 2981077 := by rw [pow_add]
          _ = 289445146 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 1526311613) ^ 11924309 = 1154033050 := by
        calc
          (2 : ZMod 1526311613) ^ 11924309 = (2 : ZMod 1526311613) ^ (5962154 + 5962154 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 5962154 * (2 : ZMod 1526311613) ^ 5962154) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1154033050 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 1526311613) ^ 23848618 = 1015055150 := by
        calc
          (2 : ZMod 1526311613) ^ 23848618 = (2 : ZMod 1526311613) ^ (11924309 + 11924309) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 11924309 * (2 : ZMod 1526311613) ^ 11924309 := by rw [pow_add]
          _ = 1015055150 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 1526311613) ^ 47697237 = 426034639 := by
        calc
          (2 : ZMod 1526311613) ^ 47697237 = (2 : ZMod 1526311613) ^ (23848618 + 23848618 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 23848618 * (2 : ZMod 1526311613) ^ 23848618) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 426034639 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 1526311613) ^ 95394475 = 1148212049 := by
        calc
          (2 : ZMod 1526311613) ^ 95394475 = (2 : ZMod 1526311613) ^ (47697237 + 47697237 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 47697237 * (2 : ZMod 1526311613) ^ 47697237) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1148212049 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 1526311613) ^ 190788951 = 115930534 := by
        calc
          (2 : ZMod 1526311613) ^ 190788951 = (2 : ZMod 1526311613) ^ (95394475 + 95394475 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 95394475 * (2 : ZMod 1526311613) ^ 95394475) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 115930534 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 1526311613) ^ 381577903 = 1294450544 := by
        calc
          (2 : ZMod 1526311613) ^ 381577903 = (2 : ZMod 1526311613) ^ (190788951 + 190788951 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 190788951 * (2 : ZMod 1526311613) ^ 190788951) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1294450544 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 1526311613) ^ 763155806 = 1526311612 := by
        calc
          (2 : ZMod 1526311613) ^ 763155806 = (2 : ZMod 1526311613) ^ (381577903 + 381577903) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 381577903 * (2 : ZMod 1526311613) ^ 381577903 := by rw [pow_add]
          _ = 1526311612 := by rw [factor_0_28]; decide
      change (2 : ZMod 1526311613) ^ 763155806 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (2 : ZMod 1526311613) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 1526311613) ^ 3 = 8 := by
        calc
          (2 : ZMod 1526311613) ^ 3 = (2 : ZMod 1526311613) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 1 * (2 : ZMod 1526311613) ^ 1) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 1526311613) ^ 6 = 64 := by
        calc
          (2 : ZMod 1526311613) ^ 6 = (2 : ZMod 1526311613) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 3 * (2 : ZMod 1526311613) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 1526311613) ^ 12 = 4096 := by
        calc
          (2 : ZMod 1526311613) ^ 12 = (2 : ZMod 1526311613) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 6 * (2 : ZMod 1526311613) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 1526311613) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 1526311613) ^ 25 = (2 : ZMod 1526311613) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 12 * (2 : ZMod 1526311613) ^ 12) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 1526311613) ^ 51 = 238482475 := by
        calc
          (2 : ZMod 1526311613) ^ 51 = (2 : ZMod 1526311613) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 25 * (2 : ZMod 1526311613) ^ 25) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 238482475 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 1526311613) ^ 103 = 1014332094 := by
        calc
          (2 : ZMod 1526311613) ^ 103 = (2 : ZMod 1526311613) ^ (51 + 51 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 51 * (2 : ZMod 1526311613) ^ 51) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1014332094 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 1526311613) ^ 207 = 938981513 := by
        calc
          (2 : ZMod 1526311613) ^ 207 = (2 : ZMod 1526311613) ^ (103 + 103 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 103 * (2 : ZMod 1526311613) ^ 103) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 938981513 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 1526311613) ^ 415 = 238275478 := by
        calc
          (2 : ZMod 1526311613) ^ 415 = (2 : ZMod 1526311613) ^ (207 + 207 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 207 * (2 : ZMod 1526311613) ^ 207) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 238275478 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 1526311613) ^ 831 = 1068572907 := by
        calc
          (2 : ZMod 1526311613) ^ 831 = (2 : ZMod 1526311613) ^ (415 + 415 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 415 * (2 : ZMod 1526311613) ^ 415) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1068572907 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 1526311613) ^ 1663 = 383053028 := by
        calc
          (2 : ZMod 1526311613) ^ 1663 = (2 : ZMod 1526311613) ^ (831 + 831 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 831 * (2 : ZMod 1526311613) ^ 831) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 383053028 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 1526311613) ^ 3327 = 1044014317 := by
        calc
          (2 : ZMod 1526311613) ^ 3327 = (2 : ZMod 1526311613) ^ (1663 + 1663 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 1663 * (2 : ZMod 1526311613) ^ 1663) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1044014317 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 1526311613) ^ 6654 = 1278296082 := by
        calc
          (2 : ZMod 1526311613) ^ 6654 = (2 : ZMod 1526311613) ^ (3327 + 3327) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 3327 * (2 : ZMod 1526311613) ^ 3327 := by rw [pow_add]
          _ = 1278296082 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 1526311613) ^ 13308 = 932780908 := by
        calc
          (2 : ZMod 1526311613) ^ 13308 = (2 : ZMod 1526311613) ^ (6654 + 6654) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 6654 * (2 : ZMod 1526311613) ^ 6654 := by rw [pow_add]
          _ = 932780908 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 1526311613) ^ 26616 = 461120517 := by
        calc
          (2 : ZMod 1526311613) ^ 26616 = (2 : ZMod 1526311613) ^ (13308 + 13308) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 13308 * (2 : ZMod 1526311613) ^ 13308 := by rw [pow_add]
          _ = 461120517 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 1526311613) ^ 53233 = 1054876303 := by
        calc
          (2 : ZMod 1526311613) ^ 53233 = (2 : ZMod 1526311613) ^ (26616 + 26616 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 26616 * (2 : ZMod 1526311613) ^ 26616) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1054876303 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 1526311613) ^ 106467 = 1119188338 := by
        calc
          (2 : ZMod 1526311613) ^ 106467 = (2 : ZMod 1526311613) ^ (53233 + 53233 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 53233 * (2 : ZMod 1526311613) ^ 53233) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1119188338 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 1526311613) ^ 212934 = 168604847 := by
        calc
          (2 : ZMod 1526311613) ^ 212934 = (2 : ZMod 1526311613) ^ (106467 + 106467) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 106467 * (2 : ZMod 1526311613) ^ 106467 := by rw [pow_add]
          _ = 168604847 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 1526311613) ^ 425868 = 955666471 := by
        calc
          (2 : ZMod 1526311613) ^ 425868 = (2 : ZMod 1526311613) ^ (212934 + 212934) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 212934 * (2 : ZMod 1526311613) ^ 212934 := by rw [pow_add]
          _ = 955666471 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 1526311613) ^ 851736 = 78828400 := by
        calc
          (2 : ZMod 1526311613) ^ 851736 = (2 : ZMod 1526311613) ^ (425868 + 425868) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 425868 * (2 : ZMod 1526311613) ^ 425868 := by rw [pow_add]
          _ = 78828400 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 1526311613) ^ 1703472 = 1386649239 := by
        calc
          (2 : ZMod 1526311613) ^ 1703472 = (2 : ZMod 1526311613) ^ (851736 + 851736) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 851736 * (2 : ZMod 1526311613) ^ 851736 := by rw [pow_add]
          _ = 1386649239 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 1526311613) ^ 3406945 = 169557000 := by
        calc
          (2 : ZMod 1526311613) ^ 3406945 = (2 : ZMod 1526311613) ^ (1703472 + 1703472 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 1703472 * (2 : ZMod 1526311613) ^ 1703472) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 169557000 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 1526311613) ^ 6813891 = 939216907 := by
        calc
          (2 : ZMod 1526311613) ^ 6813891 = (2 : ZMod 1526311613) ^ (3406945 + 3406945 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 3406945 * (2 : ZMod 1526311613) ^ 3406945) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 939216907 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 1526311613) ^ 13627782 = 757258800 := by
        calc
          (2 : ZMod 1526311613) ^ 13627782 = (2 : ZMod 1526311613) ^ (6813891 + 6813891) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 6813891 * (2 : ZMod 1526311613) ^ 6813891 := by rw [pow_add]
          _ = 757258800 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 1526311613) ^ 27255564 = 346604160 := by
        calc
          (2 : ZMod 1526311613) ^ 27255564 = (2 : ZMod 1526311613) ^ (13627782 + 13627782) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 13627782 * (2 : ZMod 1526311613) ^ 13627782 := by rw [pow_add]
          _ = 346604160 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 1526311613) ^ 54511129 = 1068544299 := by
        calc
          (2 : ZMod 1526311613) ^ 54511129 = (2 : ZMod 1526311613) ^ (27255564 + 27255564 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 27255564 * (2 : ZMod 1526311613) ^ 27255564) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1068544299 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 1526311613) ^ 109022258 = 1006779207 := by
        calc
          (2 : ZMod 1526311613) ^ 109022258 = (2 : ZMod 1526311613) ^ (54511129 + 54511129) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 54511129 * (2 : ZMod 1526311613) ^ 54511129 := by rw [pow_add]
          _ = 1006779207 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 1526311613) ^ 218044516 = 1454419742 := by
        calc
          (2 : ZMod 1526311613) ^ 218044516 = (2 : ZMod 1526311613) ^ (109022258 + 109022258) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 109022258 * (2 : ZMod 1526311613) ^ 109022258 := by rw [pow_add]
          _ = 1454419742 := by rw [factor_1_26]; decide
      change (2 : ZMod 1526311613) ^ 218044516 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (2 : ZMod 1526311613) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 1526311613) ^ 2 = 4 := by
        calc
          (2 : ZMod 1526311613) ^ 2 = (2 : ZMod 1526311613) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 1 * (2 : ZMod 1526311613) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 1526311613) ^ 5 = 32 := by
        calc
          (2 : ZMod 1526311613) ^ 5 = (2 : ZMod 1526311613) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 2 * (2 : ZMod 1526311613) ^ 2) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 1526311613) ^ 10 = 1024 := by
        calc
          (2 : ZMod 1526311613) ^ 10 = (2 : ZMod 1526311613) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 5 * (2 : ZMod 1526311613) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 1526311613) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 1526311613) ^ 21 = (2 : ZMod 1526311613) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 10 * (2 : ZMod 1526311613) ^ 10) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 1526311613) ^ 42 = 742754051 := by
        calc
          (2 : ZMod 1526311613) ^ 42 = (2 : ZMod 1526311613) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 21 * (2 : ZMod 1526311613) ^ 21 := by rw [pow_add]
          _ = 742754051 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 1526311613) ^ 85 = 1453896263 := by
        calc
          (2 : ZMod 1526311613) ^ 85 = (2 : ZMod 1526311613) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 42 * (2 : ZMod 1526311613) ^ 42) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1453896263 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 1526311613) ^ 171 = 1055965828 := by
        calc
          (2 : ZMod 1526311613) ^ 171 = (2 : ZMod 1526311613) ^ (85 + 85 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 85 * (2 : ZMod 1526311613) ^ 85) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1055965828 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 1526311613) ^ 342 = 20135804 := by
        calc
          (2 : ZMod 1526311613) ^ 342 = (2 : ZMod 1526311613) ^ (171 + 171) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 171 * (2 : ZMod 1526311613) ^ 171 := by rw [pow_add]
          _ = 20135804 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 1526311613) ^ 684 = 1185849096 := by
        calc
          (2 : ZMod 1526311613) ^ 684 = (2 : ZMod 1526311613) ^ (342 + 342) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 342 * (2 : ZMod 1526311613) ^ 342 := by rw [pow_add]
          _ = 1185849096 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 1526311613) ^ 1369 = 901956190 := by
        calc
          (2 : ZMod 1526311613) ^ 1369 = (2 : ZMod 1526311613) ^ (684 + 684 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 684 * (2 : ZMod 1526311613) ^ 684) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 901956190 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 1526311613) ^ 2739 = 1115965637 := by
        calc
          (2 : ZMod 1526311613) ^ 2739 = (2 : ZMod 1526311613) ^ (1369 + 1369 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 1369 * (2 : ZMod 1526311613) ^ 1369) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1115965637 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 1526311613) ^ 5479 = 542082429 := by
        calc
          (2 : ZMod 1526311613) ^ 5479 = (2 : ZMod 1526311613) ^ (2739 + 2739 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 2739 * (2 : ZMod 1526311613) ^ 2739) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 542082429 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 1526311613) ^ 10959 = 1129243603 := by
        calc
          (2 : ZMod 1526311613) ^ 10959 = (2 : ZMod 1526311613) ^ (5479 + 5479 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 5479 * (2 : ZMod 1526311613) ^ 5479) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1129243603 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 1526311613) ^ 21919 = 1278687929 := by
        calc
          (2 : ZMod 1526311613) ^ 21919 = (2 : ZMod 1526311613) ^ (10959 + 10959 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 10959 * (2 : ZMod 1526311613) ^ 10959) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1278687929 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 1526311613) ^ 43839 = 376370750 := by
        calc
          (2 : ZMod 1526311613) ^ 43839 = (2 : ZMod 1526311613) ^ (21919 + 21919 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 21919 * (2 : ZMod 1526311613) ^ 21919) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 376370750 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 1526311613) ^ 87678 = 1331659081 := by
        calc
          (2 : ZMod 1526311613) ^ 87678 = (2 : ZMod 1526311613) ^ (43839 + 43839) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 43839 * (2 : ZMod 1526311613) ^ 43839 := by rw [pow_add]
          _ = 1331659081 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 1526311613) ^ 175357 = 1520881217 := by
        calc
          (2 : ZMod 1526311613) ^ 175357 = (2 : ZMod 1526311613) ^ (87678 + 87678 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 87678 * (2 : ZMod 1526311613) ^ 87678) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1520881217 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 1526311613) ^ 350714 = 860353656 := by
        calc
          (2 : ZMod 1526311613) ^ 350714 = (2 : ZMod 1526311613) ^ (175357 + 175357) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 175357 * (2 : ZMod 1526311613) ^ 175357 := by rw [pow_add]
          _ = 860353656 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 1526311613) ^ 701429 = 1307670325 := by
        calc
          (2 : ZMod 1526311613) ^ 701429 = (2 : ZMod 1526311613) ^ (350714 + 350714 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 350714 * (2 : ZMod 1526311613) ^ 350714) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1307670325 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 1526311613) ^ 1402859 = 513699832 := by
        calc
          (2 : ZMod 1526311613) ^ 1402859 = (2 : ZMod 1526311613) ^ (701429 + 701429 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 701429 * (2 : ZMod 1526311613) ^ 701429) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 513699832 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 1526311613) ^ 2805719 = 1006524391 := by
        calc
          (2 : ZMod 1526311613) ^ 2805719 = (2 : ZMod 1526311613) ^ (1402859 + 1402859 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 1402859 * (2 : ZMod 1526311613) ^ 1402859) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1006524391 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 1526311613) ^ 5611439 = 583060216 := by
        calc
          (2 : ZMod 1526311613) ^ 5611439 = (2 : ZMod 1526311613) ^ (2805719 + 2805719 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 2805719 * (2 : ZMod 1526311613) ^ 2805719) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 583060216 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 1526311613) ^ 11222879 = 805279278 := by
        calc
          (2 : ZMod 1526311613) ^ 11222879 = (2 : ZMod 1526311613) ^ (5611439 + 5611439 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 5611439 * (2 : ZMod 1526311613) ^ 5611439) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 805279278 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 1526311613) ^ 22445759 = 755098586 := by
        calc
          (2 : ZMod 1526311613) ^ 22445759 = (2 : ZMod 1526311613) ^ (11222879 + 11222879 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 11222879 * (2 : ZMod 1526311613) ^ 11222879) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 755098586 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 1526311613) ^ 44891518 = 1335083601 := by
        calc
          (2 : ZMod 1526311613) ^ 44891518 = (2 : ZMod 1526311613) ^ (22445759 + 22445759) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 22445759 * (2 : ZMod 1526311613) ^ 22445759 := by rw [pow_add]
          _ = 1335083601 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 1526311613) ^ 89783036 = 530295514 := by
        calc
          (2 : ZMod 1526311613) ^ 89783036 = (2 : ZMod 1526311613) ^ (44891518 + 44891518) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 44891518 * (2 : ZMod 1526311613) ^ 44891518 := by rw [pow_add]
          _ = 530295514 := by rw [factor_2_25]; decide
      change (2 : ZMod 1526311613) ^ 89783036 ≠ 1
      rw [factor_2_26]
      decide
    ·
      have factor_3_0 : (2 : ZMod 1526311613) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 1526311613) ^ 3 = 8 := by
        calc
          (2 : ZMod 1526311613) ^ 3 = (2 : ZMod 1526311613) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 1 * (2 : ZMod 1526311613) ^ 1) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 1526311613) ^ 7 = 128 := by
        calc
          (2 : ZMod 1526311613) ^ 7 = (2 : ZMod 1526311613) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 3 * (2 : ZMod 1526311613) ^ 3) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 1526311613) ^ 14 = 16384 := by
        calc
          (2 : ZMod 1526311613) ^ 14 = (2 : ZMod 1526311613) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 7 * (2 : ZMod 1526311613) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 1526311613) ^ 29 = 536870912 := by
        calc
          (2 : ZMod 1526311613) ^ 29 = (2 : ZMod 1526311613) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 14 * (2 : ZMod 1526311613) ^ 14) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 536870912 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 1526311613) ^ 59 = 1525360693 := by
        calc
          (2 : ZMod 1526311613) ^ 59 = (2 : ZMod 1526311613) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 29 * (2 : ZMod 1526311613) ^ 29) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1525360693 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 1526311613) ^ 119 = 1344743008 := by
        calc
          (2 : ZMod 1526311613) ^ 119 = (2 : ZMod 1526311613) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = ((2 : ZMod 1526311613) ^ 59 * (2 : ZMod 1526311613) ^ 59) * (2 : ZMod 1526311613) := by rw [pow_succ, pow_add]
          _ = 1344743008 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 1526311613) ^ 238 = 1214476422 := by
        calc
          (2 : ZMod 1526311613) ^ 238 = (2 : ZMod 1526311613) ^ (119 + 119) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 119 * (2 : ZMod 1526311613) ^ 119 := by rw [pow_add]
          _ = 1214476422 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 1526311613) ^ 476 = 165640360 := by
        calc
          (2 : ZMod 1526311613) ^ 476 = (2 : ZMod 1526311613) ^ (238 + 238) :=
            congrArg (fun n : ℕ => (2 : ZMod 1526311613) ^ n) (by norm_num)
          _ = (2 : ZMod 1526311613) ^ 238 * (2 : ZMod 1526311613) ^ 238 := by rw [pow_add]
          _ = 165640360 := by rw [factor_3_7]; decide
      change (2 : ZMod 1526311613) ^ 476 ≠ 1
      rw [factor_3_8]
      decide

#print axioms prime_lucas_1526311613

end TotientTailPeriodKiller
end Erdos249257
