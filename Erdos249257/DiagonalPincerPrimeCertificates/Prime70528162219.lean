import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_70528162219 : Nat.Prime 70528162219 := by
  apply lucas_primality 70528162219 (2 : ZMod 70528162219)
  ·
      have fermat_0 : (2 : ZMod 70528162219) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 70528162219) ^ 2 = 4 := by
        calc
          (2 : ZMod 70528162219) ^ 2 = (2 : ZMod 70528162219) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 1 * (2 : ZMod 70528162219) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 70528162219) ^ 4 = 16 := by
        calc
          (2 : ZMod 70528162219) ^ 4 = (2 : ZMod 70528162219) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 2 * (2 : ZMod 70528162219) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 70528162219) ^ 8 = 256 := by
        calc
          (2 : ZMod 70528162219) ^ 8 = (2 : ZMod 70528162219) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 4 * (2 : ZMod 70528162219) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 70528162219) ^ 16 = 65536 := by
        calc
          (2 : ZMod 70528162219) ^ 16 = (2 : ZMod 70528162219) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 8 * (2 : ZMod 70528162219) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 70528162219) ^ 32 = 4294967296 := by
        calc
          (2 : ZMod 70528162219) ^ 32 = (2 : ZMod 70528162219) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 16 * (2 : ZMod 70528162219) ^ 16 := by rw [pow_add]
          _ = 4294967296 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 70528162219) ^ 65 = 54729388219 := by
        calc
          (2 : ZMod 70528162219) ^ 65 = (2 : ZMod 70528162219) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 32 * (2 : ZMod 70528162219) ^ 32) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 54729388219 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 70528162219) ^ 131 = 10438246875 := by
        calc
          (2 : ZMod 70528162219) ^ 131 = (2 : ZMod 70528162219) ^ (65 + 65 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 65 * (2 : ZMod 70528162219) ^ 65) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 10438246875 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 70528162219) ^ 262 = 59470393854 := by
        calc
          (2 : ZMod 70528162219) ^ 262 = (2 : ZMod 70528162219) ^ (131 + 131) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 131 * (2 : ZMod 70528162219) ^ 131 := by rw [pow_add]
          _ = 59470393854 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 70528162219) ^ 525 = 34639753493 := by
        calc
          (2 : ZMod 70528162219) ^ 525 = (2 : ZMod 70528162219) ^ (262 + 262 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 262 * (2 : ZMod 70528162219) ^ 262) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 34639753493 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 70528162219) ^ 1050 = 28931839744 := by
        calc
          (2 : ZMod 70528162219) ^ 1050 = (2 : ZMod 70528162219) ^ (525 + 525) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 525 * (2 : ZMod 70528162219) ^ 525 := by rw [pow_add]
          _ = 28931839744 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 70528162219) ^ 2101 = 32577190466 := by
        calc
          (2 : ZMod 70528162219) ^ 2101 = (2 : ZMod 70528162219) ^ (1050 + 1050 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 1050 * (2 : ZMod 70528162219) ^ 1050) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 32577190466 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 70528162219) ^ 4203 = 69308384578 := by
        calc
          (2 : ZMod 70528162219) ^ 4203 = (2 : ZMod 70528162219) ^ (2101 + 2101 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 2101 * (2 : ZMod 70528162219) ^ 2101) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 69308384578 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 70528162219) ^ 8407 = 5812252451 := by
        calc
          (2 : ZMod 70528162219) ^ 8407 = (2 : ZMod 70528162219) ^ (4203 + 4203 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 4203 * (2 : ZMod 70528162219) ^ 4203) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 5812252451 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 70528162219) ^ 16815 = 43956485375 := by
        calc
          (2 : ZMod 70528162219) ^ 16815 = (2 : ZMod 70528162219) ^ (8407 + 8407 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 8407 * (2 : ZMod 70528162219) ^ 8407) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 43956485375 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 70528162219) ^ 33630 = 1346855121 := by
        calc
          (2 : ZMod 70528162219) ^ 33630 = (2 : ZMod 70528162219) ^ (16815 + 16815) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 16815 * (2 : ZMod 70528162219) ^ 16815 := by rw [pow_add]
          _ = 1346855121 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 70528162219) ^ 67260 = 37476243988 := by
        calc
          (2 : ZMod 70528162219) ^ 67260 = (2 : ZMod 70528162219) ^ (33630 + 33630) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 33630 * (2 : ZMod 70528162219) ^ 33630 := by rw [pow_add]
          _ = 37476243988 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 70528162219) ^ 134521 = 46807179964 := by
        calc
          (2 : ZMod 70528162219) ^ 134521 = (2 : ZMod 70528162219) ^ (67260 + 67260 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 67260 * (2 : ZMod 70528162219) ^ 67260) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 46807179964 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 70528162219) ^ 269043 = 50184117823 := by
        calc
          (2 : ZMod 70528162219) ^ 269043 = (2 : ZMod 70528162219) ^ (134521 + 134521 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 134521 * (2 : ZMod 70528162219) ^ 134521) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 50184117823 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 70528162219) ^ 538087 = 57037804779 := by
        calc
          (2 : ZMod 70528162219) ^ 538087 = (2 : ZMod 70528162219) ^ (269043 + 269043 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 269043 * (2 : ZMod 70528162219) ^ 269043) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 57037804779 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 70528162219) ^ 1076174 = 51165579935 := by
        calc
          (2 : ZMod 70528162219) ^ 1076174 = (2 : ZMod 70528162219) ^ (538087 + 538087) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 538087 * (2 : ZMod 70528162219) ^ 538087 := by rw [pow_add]
          _ = 51165579935 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 70528162219) ^ 2152348 = 45946446690 := by
        calc
          (2 : ZMod 70528162219) ^ 2152348 = (2 : ZMod 70528162219) ^ (1076174 + 1076174) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 1076174 * (2 : ZMod 70528162219) ^ 1076174 := by rw [pow_add]
          _ = 45946446690 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 70528162219) ^ 4304697 = 69886104828 := by
        calc
          (2 : ZMod 70528162219) ^ 4304697 = (2 : ZMod 70528162219) ^ (2152348 + 2152348 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 2152348 * (2 : ZMod 70528162219) ^ 2152348) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 69886104828 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 70528162219) ^ 8609394 = 20942374129 := by
        calc
          (2 : ZMod 70528162219) ^ 8609394 = (2 : ZMod 70528162219) ^ (4304697 + 4304697) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 4304697 * (2 : ZMod 70528162219) ^ 4304697 := by rw [pow_add]
          _ = 20942374129 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 70528162219) ^ 17218789 = 42497635916 := by
        calc
          (2 : ZMod 70528162219) ^ 17218789 = (2 : ZMod 70528162219) ^ (8609394 + 8609394 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 8609394 * (2 : ZMod 70528162219) ^ 8609394) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 42497635916 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 70528162219) ^ 34437579 = 5973075490 := by
        calc
          (2 : ZMod 70528162219) ^ 34437579 = (2 : ZMod 70528162219) ^ (17218789 + 17218789 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 17218789 * (2 : ZMod 70528162219) ^ 17218789) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 5973075490 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 70528162219) ^ 68875158 = 62469789510 := by
        calc
          (2 : ZMod 70528162219) ^ 68875158 = (2 : ZMod 70528162219) ^ (34437579 + 34437579) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 34437579 * (2 : ZMod 70528162219) ^ 34437579 := by rw [pow_add]
          _ = 62469789510 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 70528162219) ^ 137750316 = 37887607579 := by
        calc
          (2 : ZMod 70528162219) ^ 137750316 = (2 : ZMod 70528162219) ^ (68875158 + 68875158) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 68875158 * (2 : ZMod 70528162219) ^ 68875158 := by rw [pow_add]
          _ = 37887607579 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 70528162219) ^ 275500633 = 40034123225 := by
        calc
          (2 : ZMod 70528162219) ^ 275500633 = (2 : ZMod 70528162219) ^ (137750316 + 137750316 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 137750316 * (2 : ZMod 70528162219) ^ 137750316) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 40034123225 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 70528162219) ^ 551001267 = 29803991104 := by
        calc
          (2 : ZMod 70528162219) ^ 551001267 = (2 : ZMod 70528162219) ^ (275500633 + 275500633 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 275500633 * (2 : ZMod 70528162219) ^ 275500633) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 29803991104 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 70528162219) ^ 1102002534 = 54585790045 := by
        calc
          (2 : ZMod 70528162219) ^ 1102002534 = (2 : ZMod 70528162219) ^ (551001267 + 551001267) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 551001267 * (2 : ZMod 70528162219) ^ 551001267 := by rw [pow_add]
          _ = 54585790045 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 70528162219) ^ 2204005069 = 56262084146 := by
        calc
          (2 : ZMod 70528162219) ^ 2204005069 = (2 : ZMod 70528162219) ^ (1102002534 + 1102002534 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 1102002534 * (2 : ZMod 70528162219) ^ 1102002534) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 56262084146 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 70528162219) ^ 4408010138 = 51751840269 := by
        calc
          (2 : ZMod 70528162219) ^ 4408010138 = (2 : ZMod 70528162219) ^ (2204005069 + 2204005069) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 2204005069 * (2 : ZMod 70528162219) ^ 2204005069 := by rw [pow_add]
          _ = 51751840269 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 70528162219) ^ 8816020277 = 45790138189 := by
        calc
          (2 : ZMod 70528162219) ^ 8816020277 = (2 : ZMod 70528162219) ^ (4408010138 + 4408010138 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 4408010138 * (2 : ZMod 70528162219) ^ 4408010138) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 45790138189 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 70528162219) ^ 17632040554 = 253153549 := by
        calc
          (2 : ZMod 70528162219) ^ 17632040554 = (2 : ZMod 70528162219) ^ (8816020277 + 8816020277) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 8816020277 * (2 : ZMod 70528162219) ^ 8816020277 := by rw [pow_add]
          _ = 253153549 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 70528162219) ^ 35264081109 = 70528162218 := by
        calc
          (2 : ZMod 70528162219) ^ 35264081109 = (2 : ZMod 70528162219) ^ (17632040554 + 17632040554 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 17632040554 * (2 : ZMod 70528162219) ^ 17632040554) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 70528162218 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 70528162219) ^ 70528162218 = 1 := by
        calc
          (2 : ZMod 70528162219) ^ 70528162218 = (2 : ZMod 70528162219) ^ (35264081109 + 35264081109) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 35264081109 * (2 : ZMod 70528162219) ^ 35264081109 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (9697, 1), (1212199, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (9697, 1), (1212199, 1)] : List FactorBlock).map factorBlockValue).prod = 70528162219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 70528162219) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 70528162219) ^ 2 = 4 := by
        calc
          (2 : ZMod 70528162219) ^ 2 = (2 : ZMod 70528162219) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 1 * (2 : ZMod 70528162219) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 70528162219) ^ 4 = 16 := by
        calc
          (2 : ZMod 70528162219) ^ 4 = (2 : ZMod 70528162219) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 2 * (2 : ZMod 70528162219) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 70528162219) ^ 8 = 256 := by
        calc
          (2 : ZMod 70528162219) ^ 8 = (2 : ZMod 70528162219) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 4 * (2 : ZMod 70528162219) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 70528162219) ^ 16 = 65536 := by
        calc
          (2 : ZMod 70528162219) ^ 16 = (2 : ZMod 70528162219) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 8 * (2 : ZMod 70528162219) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 70528162219) ^ 32 = 4294967296 := by
        calc
          (2 : ZMod 70528162219) ^ 32 = (2 : ZMod 70528162219) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 16 * (2 : ZMod 70528162219) ^ 16 := by rw [pow_add]
          _ = 4294967296 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 70528162219) ^ 65 = 54729388219 := by
        calc
          (2 : ZMod 70528162219) ^ 65 = (2 : ZMod 70528162219) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 32 * (2 : ZMod 70528162219) ^ 32) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 54729388219 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 70528162219) ^ 131 = 10438246875 := by
        calc
          (2 : ZMod 70528162219) ^ 131 = (2 : ZMod 70528162219) ^ (65 + 65 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 65 * (2 : ZMod 70528162219) ^ 65) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 10438246875 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 70528162219) ^ 262 = 59470393854 := by
        calc
          (2 : ZMod 70528162219) ^ 262 = (2 : ZMod 70528162219) ^ (131 + 131) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 131 * (2 : ZMod 70528162219) ^ 131 := by rw [pow_add]
          _ = 59470393854 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 70528162219) ^ 525 = 34639753493 := by
        calc
          (2 : ZMod 70528162219) ^ 525 = (2 : ZMod 70528162219) ^ (262 + 262 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 262 * (2 : ZMod 70528162219) ^ 262) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 34639753493 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 70528162219) ^ 1050 = 28931839744 := by
        calc
          (2 : ZMod 70528162219) ^ 1050 = (2 : ZMod 70528162219) ^ (525 + 525) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 525 * (2 : ZMod 70528162219) ^ 525 := by rw [pow_add]
          _ = 28931839744 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 70528162219) ^ 2101 = 32577190466 := by
        calc
          (2 : ZMod 70528162219) ^ 2101 = (2 : ZMod 70528162219) ^ (1050 + 1050 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 1050 * (2 : ZMod 70528162219) ^ 1050) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 32577190466 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 70528162219) ^ 4203 = 69308384578 := by
        calc
          (2 : ZMod 70528162219) ^ 4203 = (2 : ZMod 70528162219) ^ (2101 + 2101 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 2101 * (2 : ZMod 70528162219) ^ 2101) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 69308384578 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 70528162219) ^ 8407 = 5812252451 := by
        calc
          (2 : ZMod 70528162219) ^ 8407 = (2 : ZMod 70528162219) ^ (4203 + 4203 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 4203 * (2 : ZMod 70528162219) ^ 4203) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 5812252451 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 70528162219) ^ 16815 = 43956485375 := by
        calc
          (2 : ZMod 70528162219) ^ 16815 = (2 : ZMod 70528162219) ^ (8407 + 8407 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 8407 * (2 : ZMod 70528162219) ^ 8407) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 43956485375 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 70528162219) ^ 33630 = 1346855121 := by
        calc
          (2 : ZMod 70528162219) ^ 33630 = (2 : ZMod 70528162219) ^ (16815 + 16815) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 16815 * (2 : ZMod 70528162219) ^ 16815 := by rw [pow_add]
          _ = 1346855121 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 70528162219) ^ 67260 = 37476243988 := by
        calc
          (2 : ZMod 70528162219) ^ 67260 = (2 : ZMod 70528162219) ^ (33630 + 33630) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 33630 * (2 : ZMod 70528162219) ^ 33630 := by rw [pow_add]
          _ = 37476243988 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 70528162219) ^ 134521 = 46807179964 := by
        calc
          (2 : ZMod 70528162219) ^ 134521 = (2 : ZMod 70528162219) ^ (67260 + 67260 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 67260 * (2 : ZMod 70528162219) ^ 67260) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 46807179964 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 70528162219) ^ 269043 = 50184117823 := by
        calc
          (2 : ZMod 70528162219) ^ 269043 = (2 : ZMod 70528162219) ^ (134521 + 134521 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 134521 * (2 : ZMod 70528162219) ^ 134521) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 50184117823 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 70528162219) ^ 538087 = 57037804779 := by
        calc
          (2 : ZMod 70528162219) ^ 538087 = (2 : ZMod 70528162219) ^ (269043 + 269043 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 269043 * (2 : ZMod 70528162219) ^ 269043) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 57037804779 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 70528162219) ^ 1076174 = 51165579935 := by
        calc
          (2 : ZMod 70528162219) ^ 1076174 = (2 : ZMod 70528162219) ^ (538087 + 538087) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 538087 * (2 : ZMod 70528162219) ^ 538087 := by rw [pow_add]
          _ = 51165579935 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 70528162219) ^ 2152348 = 45946446690 := by
        calc
          (2 : ZMod 70528162219) ^ 2152348 = (2 : ZMod 70528162219) ^ (1076174 + 1076174) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 1076174 * (2 : ZMod 70528162219) ^ 1076174 := by rw [pow_add]
          _ = 45946446690 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 70528162219) ^ 4304697 = 69886104828 := by
        calc
          (2 : ZMod 70528162219) ^ 4304697 = (2 : ZMod 70528162219) ^ (2152348 + 2152348 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 2152348 * (2 : ZMod 70528162219) ^ 2152348) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 69886104828 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 70528162219) ^ 8609394 = 20942374129 := by
        calc
          (2 : ZMod 70528162219) ^ 8609394 = (2 : ZMod 70528162219) ^ (4304697 + 4304697) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 4304697 * (2 : ZMod 70528162219) ^ 4304697 := by rw [pow_add]
          _ = 20942374129 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 70528162219) ^ 17218789 = 42497635916 := by
        calc
          (2 : ZMod 70528162219) ^ 17218789 = (2 : ZMod 70528162219) ^ (8609394 + 8609394 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 8609394 * (2 : ZMod 70528162219) ^ 8609394) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 42497635916 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 70528162219) ^ 34437579 = 5973075490 := by
        calc
          (2 : ZMod 70528162219) ^ 34437579 = (2 : ZMod 70528162219) ^ (17218789 + 17218789 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 17218789 * (2 : ZMod 70528162219) ^ 17218789) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 5973075490 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 70528162219) ^ 68875158 = 62469789510 := by
        calc
          (2 : ZMod 70528162219) ^ 68875158 = (2 : ZMod 70528162219) ^ (34437579 + 34437579) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 34437579 * (2 : ZMod 70528162219) ^ 34437579 := by rw [pow_add]
          _ = 62469789510 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 70528162219) ^ 137750316 = 37887607579 := by
        calc
          (2 : ZMod 70528162219) ^ 137750316 = (2 : ZMod 70528162219) ^ (68875158 + 68875158) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 68875158 * (2 : ZMod 70528162219) ^ 68875158 := by rw [pow_add]
          _ = 37887607579 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 70528162219) ^ 275500633 = 40034123225 := by
        calc
          (2 : ZMod 70528162219) ^ 275500633 = (2 : ZMod 70528162219) ^ (137750316 + 137750316 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 137750316 * (2 : ZMod 70528162219) ^ 137750316) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 40034123225 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 70528162219) ^ 551001267 = 29803991104 := by
        calc
          (2 : ZMod 70528162219) ^ 551001267 = (2 : ZMod 70528162219) ^ (275500633 + 275500633 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 275500633 * (2 : ZMod 70528162219) ^ 275500633) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 29803991104 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 70528162219) ^ 1102002534 = 54585790045 := by
        calc
          (2 : ZMod 70528162219) ^ 1102002534 = (2 : ZMod 70528162219) ^ (551001267 + 551001267) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 551001267 * (2 : ZMod 70528162219) ^ 551001267 := by rw [pow_add]
          _ = 54585790045 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 70528162219) ^ 2204005069 = 56262084146 := by
        calc
          (2 : ZMod 70528162219) ^ 2204005069 = (2 : ZMod 70528162219) ^ (1102002534 + 1102002534 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 1102002534 * (2 : ZMod 70528162219) ^ 1102002534) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 56262084146 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 70528162219) ^ 4408010138 = 51751840269 := by
        calc
          (2 : ZMod 70528162219) ^ 4408010138 = (2 : ZMod 70528162219) ^ (2204005069 + 2204005069) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 2204005069 * (2 : ZMod 70528162219) ^ 2204005069 := by rw [pow_add]
          _ = 51751840269 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 70528162219) ^ 8816020277 = 45790138189 := by
        calc
          (2 : ZMod 70528162219) ^ 8816020277 = (2 : ZMod 70528162219) ^ (4408010138 + 4408010138 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 4408010138 * (2 : ZMod 70528162219) ^ 4408010138) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 45790138189 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 70528162219) ^ 17632040554 = 253153549 := by
        calc
          (2 : ZMod 70528162219) ^ 17632040554 = (2 : ZMod 70528162219) ^ (8816020277 + 8816020277) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 8816020277 * (2 : ZMod 70528162219) ^ 8816020277 := by rw [pow_add]
          _ = 253153549 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 70528162219) ^ 35264081109 = 70528162218 := by
        calc
          (2 : ZMod 70528162219) ^ 35264081109 = (2 : ZMod 70528162219) ^ (17632040554 + 17632040554 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 17632040554 * (2 : ZMod 70528162219) ^ 17632040554) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 70528162218 := by rw [factor_0_34]; decide
      change (2 : ZMod 70528162219) ^ 35264081109 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (2 : ZMod 70528162219) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 70528162219) ^ 2 = 4 := by
        calc
          (2 : ZMod 70528162219) ^ 2 = (2 : ZMod 70528162219) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 1 * (2 : ZMod 70528162219) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 70528162219) ^ 5 = 32 := by
        calc
          (2 : ZMod 70528162219) ^ 5 = (2 : ZMod 70528162219) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 2 * (2 : ZMod 70528162219) ^ 2) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 70528162219) ^ 10 = 1024 := by
        calc
          (2 : ZMod 70528162219) ^ 10 = (2 : ZMod 70528162219) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 5 * (2 : ZMod 70528162219) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 70528162219) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 70528162219) ^ 21 = (2 : ZMod 70528162219) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 10 * (2 : ZMod 70528162219) ^ 10) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 70528162219) ^ 43 = 50600907052 := by
        calc
          (2 : ZMod 70528162219) ^ 43 = (2 : ZMod 70528162219) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 21 * (2 : ZMod 70528162219) ^ 21) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 50600907052 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 70528162219) ^ 87 = 14885889888 := by
        calc
          (2 : ZMod 70528162219) ^ 87 = (2 : ZMod 70528162219) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 43 * (2 : ZMod 70528162219) ^ 43) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 14885889888 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 70528162219) ^ 175 = 8890994774 := by
        calc
          (2 : ZMod 70528162219) ^ 175 = (2 : ZMod 70528162219) ^ (87 + 87 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 87 * (2 : ZMod 70528162219) ^ 87) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 8890994774 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 70528162219) ^ 350 = 68493289955 := by
        calc
          (2 : ZMod 70528162219) ^ 350 = (2 : ZMod 70528162219) ^ (175 + 175) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 175 * (2 : ZMod 70528162219) ^ 175 := by rw [pow_add]
          _ = 68493289955 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 70528162219) ^ 700 = 41742619989 := by
        calc
          (2 : ZMod 70528162219) ^ 700 = (2 : ZMod 70528162219) ^ (350 + 350) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 350 * (2 : ZMod 70528162219) ^ 350 := by rw [pow_add]
          _ = 41742619989 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 70528162219) ^ 1401 = 31971773133 := by
        calc
          (2 : ZMod 70528162219) ^ 1401 = (2 : ZMod 70528162219) ^ (700 + 700 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 700 * (2 : ZMod 70528162219) ^ 700) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 31971773133 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 70528162219) ^ 2802 = 47280844594 := by
        calc
          (2 : ZMod 70528162219) ^ 2802 = (2 : ZMod 70528162219) ^ (1401 + 1401) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 1401 * (2 : ZMod 70528162219) ^ 1401 := by rw [pow_add]
          _ = 47280844594 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 70528162219) ^ 5605 = 29487192239 := by
        calc
          (2 : ZMod 70528162219) ^ 5605 = (2 : ZMod 70528162219) ^ (2802 + 2802 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 2802 * (2 : ZMod 70528162219) ^ 2802) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 29487192239 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 70528162219) ^ 11210 = 51227254201 := by
        calc
          (2 : ZMod 70528162219) ^ 11210 = (2 : ZMod 70528162219) ^ (5605 + 5605) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 5605 * (2 : ZMod 70528162219) ^ 5605 := by rw [pow_add]
          _ = 51227254201 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 70528162219) ^ 22420 = 14282802368 := by
        calc
          (2 : ZMod 70528162219) ^ 22420 = (2 : ZMod 70528162219) ^ (11210 + 11210) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 11210 * (2 : ZMod 70528162219) ^ 11210 := by rw [pow_add]
          _ = 14282802368 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 70528162219) ^ 44840 = 19724399201 := by
        calc
          (2 : ZMod 70528162219) ^ 44840 = (2 : ZMod 70528162219) ^ (22420 + 22420) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 22420 * (2 : ZMod 70528162219) ^ 22420 := by rw [pow_add]
          _ = 19724399201 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 70528162219) ^ 89681 = 16327901293 := by
        calc
          (2 : ZMod 70528162219) ^ 89681 = (2 : ZMod 70528162219) ^ (44840 + 44840 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 44840 * (2 : ZMod 70528162219) ^ 44840) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 16327901293 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 70528162219) ^ 179362 = 44887814811 := by
        calc
          (2 : ZMod 70528162219) ^ 179362 = (2 : ZMod 70528162219) ^ (89681 + 89681) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 89681 * (2 : ZMod 70528162219) ^ 89681 := by rw [pow_add]
          _ = 44887814811 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 70528162219) ^ 358724 = 26012448567 := by
        calc
          (2 : ZMod 70528162219) ^ 358724 = (2 : ZMod 70528162219) ^ (179362 + 179362) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 179362 * (2 : ZMod 70528162219) ^ 179362 := by rw [pow_add]
          _ = 26012448567 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 70528162219) ^ 717449 = 58701047001 := by
        calc
          (2 : ZMod 70528162219) ^ 717449 = (2 : ZMod 70528162219) ^ (358724 + 358724 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 358724 * (2 : ZMod 70528162219) ^ 358724) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 58701047001 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 70528162219) ^ 1434899 = 47117671523 := by
        calc
          (2 : ZMod 70528162219) ^ 1434899 = (2 : ZMod 70528162219) ^ (717449 + 717449 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 717449 * (2 : ZMod 70528162219) ^ 717449) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 47117671523 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 70528162219) ^ 2869798 = 35073185540 := by
        calc
          (2 : ZMod 70528162219) ^ 2869798 = (2 : ZMod 70528162219) ^ (1434899 + 1434899) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 1434899 * (2 : ZMod 70528162219) ^ 1434899 := by rw [pow_add]
          _ = 35073185540 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 70528162219) ^ 5739596 = 10477996994 := by
        calc
          (2 : ZMod 70528162219) ^ 5739596 = (2 : ZMod 70528162219) ^ (2869798 + 2869798) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 2869798 * (2 : ZMod 70528162219) ^ 2869798 := by rw [pow_add]
          _ = 10477996994 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 70528162219) ^ 11479193 = 54377881266 := by
        calc
          (2 : ZMod 70528162219) ^ 11479193 = (2 : ZMod 70528162219) ^ (5739596 + 5739596 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 5739596 * (2 : ZMod 70528162219) ^ 5739596) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 54377881266 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 70528162219) ^ 22958386 = 61924383596 := by
        calc
          (2 : ZMod 70528162219) ^ 22958386 = (2 : ZMod 70528162219) ^ (11479193 + 11479193) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 11479193 * (2 : ZMod 70528162219) ^ 11479193 := by rw [pow_add]
          _ = 61924383596 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 70528162219) ^ 45916772 = 47096249892 := by
        calc
          (2 : ZMod 70528162219) ^ 45916772 = (2 : ZMod 70528162219) ^ (22958386 + 22958386) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 22958386 * (2 : ZMod 70528162219) ^ 22958386 := by rw [pow_add]
          _ = 47096249892 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 70528162219) ^ 91833544 = 10307433611 := by
        calc
          (2 : ZMod 70528162219) ^ 91833544 = (2 : ZMod 70528162219) ^ (45916772 + 45916772) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 45916772 * (2 : ZMod 70528162219) ^ 45916772 := by rw [pow_add]
          _ = 10307433611 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 70528162219) ^ 183667089 = 26083149920 := by
        calc
          (2 : ZMod 70528162219) ^ 183667089 = (2 : ZMod 70528162219) ^ (91833544 + 91833544 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 91833544 * (2 : ZMod 70528162219) ^ 91833544) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 26083149920 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 70528162219) ^ 367334178 = 49614093327 := by
        calc
          (2 : ZMod 70528162219) ^ 367334178 = (2 : ZMod 70528162219) ^ (183667089 + 183667089) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 183667089 * (2 : ZMod 70528162219) ^ 183667089 := by rw [pow_add]
          _ = 49614093327 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 70528162219) ^ 734668356 = 23789468974 := by
        calc
          (2 : ZMod 70528162219) ^ 734668356 = (2 : ZMod 70528162219) ^ (367334178 + 367334178) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 367334178 * (2 : ZMod 70528162219) ^ 367334178 := by rw [pow_add]
          _ = 23789468974 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 70528162219) ^ 1469336712 = 23000450170 := by
        calc
          (2 : ZMod 70528162219) ^ 1469336712 = (2 : ZMod 70528162219) ^ (734668356 + 734668356) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 734668356 * (2 : ZMod 70528162219) ^ 734668356 := by rw [pow_add]
          _ = 23000450170 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 70528162219) ^ 2938673425 = 57966711544 := by
        calc
          (2 : ZMod 70528162219) ^ 2938673425 = (2 : ZMod 70528162219) ^ (1469336712 + 1469336712 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 1469336712 * (2 : ZMod 70528162219) ^ 1469336712) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 57966711544 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 70528162219) ^ 5877346851 = 61084616815 := by
        calc
          (2 : ZMod 70528162219) ^ 5877346851 = (2 : ZMod 70528162219) ^ (2938673425 + 2938673425 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 2938673425 * (2 : ZMod 70528162219) ^ 2938673425) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 61084616815 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 70528162219) ^ 11754693703 = 40832528568 := by
        calc
          (2 : ZMod 70528162219) ^ 11754693703 = (2 : ZMod 70528162219) ^ (5877346851 + 5877346851 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 5877346851 * (2 : ZMod 70528162219) ^ 5877346851) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 40832528568 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 70528162219) ^ 23509387406 = 40832528567 := by
        calc
          (2 : ZMod 70528162219) ^ 23509387406 = (2 : ZMod 70528162219) ^ (11754693703 + 11754693703) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 11754693703 * (2 : ZMod 70528162219) ^ 11754693703 := by rw [pow_add]
          _ = 40832528567 := by rw [factor_1_33]; decide
      change (2 : ZMod 70528162219) ^ 23509387406 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (2 : ZMod 70528162219) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 70528162219) ^ 3 = 8 := by
        calc
          (2 : ZMod 70528162219) ^ 3 = (2 : ZMod 70528162219) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 1 * (2 : ZMod 70528162219) ^ 1) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 70528162219) ^ 6 = 64 := by
        calc
          (2 : ZMod 70528162219) ^ 6 = (2 : ZMod 70528162219) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 3 * (2 : ZMod 70528162219) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 70528162219) ^ 13 = 8192 := by
        calc
          (2 : ZMod 70528162219) ^ 13 = (2 : ZMod 70528162219) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 6 * (2 : ZMod 70528162219) ^ 6) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 70528162219) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 70528162219) ^ 27 = (2 : ZMod 70528162219) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 13 * (2 : ZMod 70528162219) ^ 13) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 70528162219) ^ 55 = 49574685570 := by
        calc
          (2 : ZMod 70528162219) ^ 55 = (2 : ZMod 70528162219) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 27 * (2 : ZMod 70528162219) ^ 27) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 49574685570 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 70528162219) ^ 110 = 20588800929 := by
        calc
          (2 : ZMod 70528162219) ^ 110 = (2 : ZMod 70528162219) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 55 * (2 : ZMod 70528162219) ^ 55 := by rw [pow_add]
          _ = 20588800929 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 70528162219) ^ 221 = 69155466333 := by
        calc
          (2 : ZMod 70528162219) ^ 221 = (2 : ZMod 70528162219) ^ (110 + 110 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 110 * (2 : ZMod 70528162219) ^ 110) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 69155466333 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 70528162219) ^ 443 = 64920561135 := by
        calc
          (2 : ZMod 70528162219) ^ 443 = (2 : ZMod 70528162219) ^ (221 + 221 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 221 * (2 : ZMod 70528162219) ^ 221) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 64920561135 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 70528162219) ^ 887 = 57153313632 := by
        calc
          (2 : ZMod 70528162219) ^ 887 = (2 : ZMod 70528162219) ^ (443 + 443 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 443 * (2 : ZMod 70528162219) ^ 443) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 57153313632 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 70528162219) ^ 1775 = 41098078874 := by
        calc
          (2 : ZMod 70528162219) ^ 1775 = (2 : ZMod 70528162219) ^ (887 + 887 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 887 * (2 : ZMod 70528162219) ^ 887) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 41098078874 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 70528162219) ^ 3551 = 10400767211 := by
        calc
          (2 : ZMod 70528162219) ^ 3551 = (2 : ZMod 70528162219) ^ (1775 + 1775 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 1775 * (2 : ZMod 70528162219) ^ 1775) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 10400767211 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 70528162219) ^ 7102 = 49488898943 := by
        calc
          (2 : ZMod 70528162219) ^ 7102 = (2 : ZMod 70528162219) ^ (3551 + 3551) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 3551 * (2 : ZMod 70528162219) ^ 3551 := by rw [pow_add]
          _ = 49488898943 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 70528162219) ^ 14205 = 3358304026 := by
        calc
          (2 : ZMod 70528162219) ^ 14205 = (2 : ZMod 70528162219) ^ (7102 + 7102 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 7102 * (2 : ZMod 70528162219) ^ 7102) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 3358304026 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 70528162219) ^ 28410 = 45154345289 := by
        calc
          (2 : ZMod 70528162219) ^ 28410 = (2 : ZMod 70528162219) ^ (14205 + 14205) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 14205 * (2 : ZMod 70528162219) ^ 14205 := by rw [pow_add]
          _ = 45154345289 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 70528162219) ^ 56821 = 13435379166 := by
        calc
          (2 : ZMod 70528162219) ^ 56821 = (2 : ZMod 70528162219) ^ (28410 + 28410 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 28410 * (2 : ZMod 70528162219) ^ 28410) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 13435379166 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 70528162219) ^ 113643 = 9291802200 := by
        calc
          (2 : ZMod 70528162219) ^ 113643 = (2 : ZMod 70528162219) ^ (56821 + 56821 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 56821 * (2 : ZMod 70528162219) ^ 56821) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 9291802200 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 70528162219) ^ 227287 = 4147544746 := by
        calc
          (2 : ZMod 70528162219) ^ 227287 = (2 : ZMod 70528162219) ^ (113643 + 113643 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 113643 * (2 : ZMod 70528162219) ^ 113643) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 4147544746 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 70528162219) ^ 454574 = 23620234172 := by
        calc
          (2 : ZMod 70528162219) ^ 454574 = (2 : ZMod 70528162219) ^ (227287 + 227287) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 227287 * (2 : ZMod 70528162219) ^ 227287 := by rw [pow_add]
          _ = 23620234172 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 70528162219) ^ 909149 = 32248342561 := by
        calc
          (2 : ZMod 70528162219) ^ 909149 = (2 : ZMod 70528162219) ^ (454574 + 454574 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 454574 * (2 : ZMod 70528162219) ^ 454574) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 32248342561 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 70528162219) ^ 1818298 = 59978278494 := by
        calc
          (2 : ZMod 70528162219) ^ 1818298 = (2 : ZMod 70528162219) ^ (909149 + 909149) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 909149 * (2 : ZMod 70528162219) ^ 909149 := by rw [pow_add]
          _ = 59978278494 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 70528162219) ^ 3636597 = 19268508257 := by
        calc
          (2 : ZMod 70528162219) ^ 3636597 = (2 : ZMod 70528162219) ^ (1818298 + 1818298 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 1818298 * (2 : ZMod 70528162219) ^ 1818298) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 19268508257 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 70528162219) ^ 7273194 = 57517984202 := by
        calc
          (2 : ZMod 70528162219) ^ 7273194 = (2 : ZMod 70528162219) ^ (3636597 + 3636597) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 3636597 * (2 : ZMod 70528162219) ^ 3636597 := by rw [pow_add]
          _ = 57517984202 := by rw [factor_2_21]; decide
      change (2 : ZMod 70528162219) ^ 7273194 ≠ 1
      rw [factor_2_22]
      decide
    ·
      have factor_3_0 : (2 : ZMod 70528162219) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 70528162219) ^ 3 = 8 := by
        calc
          (2 : ZMod 70528162219) ^ 3 = (2 : ZMod 70528162219) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 1 * (2 : ZMod 70528162219) ^ 1) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 70528162219) ^ 7 = 128 := by
        calc
          (2 : ZMod 70528162219) ^ 7 = (2 : ZMod 70528162219) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 3 * (2 : ZMod 70528162219) ^ 3) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 70528162219) ^ 14 = 16384 := by
        calc
          (2 : ZMod 70528162219) ^ 14 = (2 : ZMod 70528162219) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 7 * (2 : ZMod 70528162219) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 70528162219) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 70528162219) ^ 28 = (2 : ZMod 70528162219) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 14 * (2 : ZMod 70528162219) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 70528162219) ^ 56 = 28621208921 := by
        calc
          (2 : ZMod 70528162219) ^ 56 = (2 : ZMod 70528162219) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 28 * (2 : ZMod 70528162219) ^ 28 := by rw [pow_add]
          _ = 28621208921 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 70528162219) ^ 113 = 23654082994 := by
        calc
          (2 : ZMod 70528162219) ^ 113 = (2 : ZMod 70528162219) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 56 * (2 : ZMod 70528162219) ^ 56) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 23654082994 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 70528162219) ^ 227 = 53203787734 := by
        calc
          (2 : ZMod 70528162219) ^ 227 = (2 : ZMod 70528162219) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 113 * (2 : ZMod 70528162219) ^ 113) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 53203787734 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 70528162219) ^ 454 = 11723421665 := by
        calc
          (2 : ZMod 70528162219) ^ 454 = (2 : ZMod 70528162219) ^ (227 + 227) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 227 * (2 : ZMod 70528162219) ^ 227 := by rw [pow_add]
          _ = 11723421665 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 70528162219) ^ 909 = 60357468590 := by
        calc
          (2 : ZMod 70528162219) ^ 909 = (2 : ZMod 70528162219) ^ (454 + 454 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 454 * (2 : ZMod 70528162219) ^ 454) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 60357468590 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 70528162219) ^ 1818 = 41093275652 := by
        calc
          (2 : ZMod 70528162219) ^ 1818 = (2 : ZMod 70528162219) ^ (909 + 909) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 909 * (2 : ZMod 70528162219) ^ 909 := by rw [pow_add]
          _ = 41093275652 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 70528162219) ^ 3636 = 10476614356 := by
        calc
          (2 : ZMod 70528162219) ^ 3636 = (2 : ZMod 70528162219) ^ (1818 + 1818) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 1818 * (2 : ZMod 70528162219) ^ 1818 := by rw [pow_add]
          _ = 10476614356 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 70528162219) ^ 7272 = 1659953438 := by
        calc
          (2 : ZMod 70528162219) ^ 7272 = (2 : ZMod 70528162219) ^ (3636 + 3636) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 3636 * (2 : ZMod 70528162219) ^ 3636 := by rw [pow_add]
          _ = 1659953438 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 70528162219) ^ 14545 = 13148875919 := by
        calc
          (2 : ZMod 70528162219) ^ 14545 = (2 : ZMod 70528162219) ^ (7272 + 7272 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 7272 * (2 : ZMod 70528162219) ^ 7272) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 13148875919 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 70528162219) ^ 29091 = 58150178603 := by
        calc
          (2 : ZMod 70528162219) ^ 29091 = (2 : ZMod 70528162219) ^ (14545 + 14545 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = ((2 : ZMod 70528162219) ^ 14545 * (2 : ZMod 70528162219) ^ 14545) * (2 : ZMod 70528162219) := by rw [pow_succ, pow_add]
          _ = 58150178603 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 70528162219) ^ 58182 = 2265669838 := by
        calc
          (2 : ZMod 70528162219) ^ 58182 = (2 : ZMod 70528162219) ^ (29091 + 29091) :=
            congrArg (fun n : ℕ => (2 : ZMod 70528162219) ^ n) (by norm_num)
          _ = (2 : ZMod 70528162219) ^ 29091 * (2 : ZMod 70528162219) ^ 29091 := by rw [pow_add]
          _ = 2265669838 := by rw [factor_3_14]; decide
      change (2 : ZMod 70528162219) ^ 58182 ≠ 1
      rw [factor_3_15]
      decide

#print axioms prime_lucas_70528162219

end TotientTailPeriodKiller
end Erdos249257
