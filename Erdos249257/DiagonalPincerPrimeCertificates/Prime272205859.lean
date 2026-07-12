import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_272205859 : Nat.Prime 272205859 := by
  apply lucas_primality 272205859 (2 : ZMod 272205859)
  ·
      have fermat_0 : (2 : ZMod 272205859) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 272205859) ^ 2 = 4 := by
        calc
          (2 : ZMod 272205859) ^ 2 = (2 : ZMod 272205859) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 1 * (2 : ZMod 272205859) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 272205859) ^ 4 = 16 := by
        calc
          (2 : ZMod 272205859) ^ 4 = (2 : ZMod 272205859) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 2 * (2 : ZMod 272205859) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 272205859) ^ 8 = 256 := by
        calc
          (2 : ZMod 272205859) ^ 8 = (2 : ZMod 272205859) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 4 * (2 : ZMod 272205859) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 272205859) ^ 16 = 65536 := by
        calc
          (2 : ZMod 272205859) ^ 16 = (2 : ZMod 272205859) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 8 * (2 : ZMod 272205859) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 272205859) ^ 32 = 211879411 := by
        calc
          (2 : ZMod 272205859) ^ 32 = (2 : ZMod 272205859) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 16 * (2 : ZMod 272205859) ^ 16 := by rw [pow_add]
          _ = 211879411 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 272205859) ^ 64 = 142280612 := by
        calc
          (2 : ZMod 272205859) ^ 64 = (2 : ZMod 272205859) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 32 * (2 : ZMod 272205859) ^ 32 := by rw [pow_add]
          _ = 142280612 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 272205859) ^ 129 = 46557506 := by
        calc
          (2 : ZMod 272205859) ^ 129 = (2 : ZMod 272205859) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 64 * (2 : ZMod 272205859) ^ 64) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 46557506 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 272205859) ^ 259 = 228127003 := by
        calc
          (2 : ZMod 272205859) ^ 259 = (2 : ZMod 272205859) ^ (129 + 129 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 129 * (2 : ZMod 272205859) ^ 129) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 228127003 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 272205859) ^ 519 = 20031432 := by
        calc
          (2 : ZMod 272205859) ^ 519 = (2 : ZMod 272205859) ^ (259 + 259 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 259 * (2 : ZMod 272205859) ^ 259) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 20031432 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 272205859) ^ 1038 = 155630442 := by
        calc
          (2 : ZMod 272205859) ^ 1038 = (2 : ZMod 272205859) ^ (519 + 519) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 519 * (2 : ZMod 272205859) ^ 519 := by rw [pow_add]
          _ = 155630442 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 272205859) ^ 2076 = 151821086 := by
        calc
          (2 : ZMod 272205859) ^ 2076 = (2 : ZMod 272205859) ^ (1038 + 1038) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 1038 * (2 : ZMod 272205859) ^ 1038 := by rw [pow_add]
          _ = 151821086 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 272205859) ^ 4153 = 154687741 := by
        calc
          (2 : ZMod 272205859) ^ 4153 = (2 : ZMod 272205859) ^ (2076 + 2076 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 2076 * (2 : ZMod 272205859) ^ 2076) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 154687741 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 272205859) ^ 8307 = 154406744 := by
        calc
          (2 : ZMod 272205859) ^ 8307 = (2 : ZMod 272205859) ^ (4153 + 4153 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 4153 * (2 : ZMod 272205859) ^ 4153) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 154406744 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 272205859) ^ 16614 = 83073970 := by
        calc
          (2 : ZMod 272205859) ^ 16614 = (2 : ZMod 272205859) ^ (8307 + 8307) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 8307 * (2 : ZMod 272205859) ^ 8307 := by rw [pow_add]
          _ = 83073970 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 272205859) ^ 33228 = 79073421 := by
        calc
          (2 : ZMod 272205859) ^ 33228 = (2 : ZMod 272205859) ^ (16614 + 16614) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 16614 * (2 : ZMod 272205859) ^ 16614 := by rw [pow_add]
          _ = 79073421 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 272205859) ^ 66456 = 35210558 := by
        calc
          (2 : ZMod 272205859) ^ 66456 = (2 : ZMod 272205859) ^ (33228 + 33228) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 33228 * (2 : ZMod 272205859) ^ 33228 := by rw [pow_add]
          _ = 35210558 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 272205859) ^ 132913 = 66774288 := by
        calc
          (2 : ZMod 272205859) ^ 132913 = (2 : ZMod 272205859) ^ (66456 + 66456 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 66456 * (2 : ZMod 272205859) ^ 66456) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 66774288 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 272205859) ^ 265826 = 71905014 := by
        calc
          (2 : ZMod 272205859) ^ 265826 = (2 : ZMod 272205859) ^ (132913 + 132913) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 132913 * (2 : ZMod 272205859) ^ 132913 := by rw [pow_add]
          _ = 71905014 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 272205859) ^ 531652 = 144557550 := by
        calc
          (2 : ZMod 272205859) ^ 531652 = (2 : ZMod 272205859) ^ (265826 + 265826) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 265826 * (2 : ZMod 272205859) ^ 265826 := by rw [pow_add]
          _ = 144557550 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 272205859) ^ 1063304 = 233894662 := by
        calc
          (2 : ZMod 272205859) ^ 1063304 = (2 : ZMod 272205859) ^ (531652 + 531652) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 531652 * (2 : ZMod 272205859) ^ 531652 := by rw [pow_add]
          _ = 233894662 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 272205859) ^ 2126608 = 213551859 := by
        calc
          (2 : ZMod 272205859) ^ 2126608 = (2 : ZMod 272205859) ^ (1063304 + 1063304) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 1063304 * (2 : ZMod 272205859) ^ 1063304 := by rw [pow_add]
          _ = 213551859 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 272205859) ^ 4253216 = 1441806 := by
        calc
          (2 : ZMod 272205859) ^ 4253216 = (2 : ZMod 272205859) ^ (2126608 + 2126608) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 2126608 * (2 : ZMod 272205859) ^ 2126608 := by rw [pow_add]
          _ = 1441806 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 272205859) ^ 8506433 = 208998765 := by
        calc
          (2 : ZMod 272205859) ^ 8506433 = (2 : ZMod 272205859) ^ (4253216 + 4253216 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 4253216 * (2 : ZMod 272205859) ^ 4253216) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 208998765 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 272205859) ^ 17012866 = 193202890 := by
        calc
          (2 : ZMod 272205859) ^ 17012866 = (2 : ZMod 272205859) ^ (8506433 + 8506433) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 8506433 * (2 : ZMod 272205859) ^ 8506433 := by rw [pow_add]
          _ = 193202890 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 272205859) ^ 34025732 = 267897404 := by
        calc
          (2 : ZMod 272205859) ^ 34025732 = (2 : ZMod 272205859) ^ (17012866 + 17012866) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 17012866 * (2 : ZMod 272205859) ^ 17012866 := by rw [pow_add]
          _ = 267897404 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 272205859) ^ 68051464 = 250344238 := by
        calc
          (2 : ZMod 272205859) ^ 68051464 = (2 : ZMod 272205859) ^ (34025732 + 34025732) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 34025732 * (2 : ZMod 272205859) ^ 34025732 := by rw [pow_add]
          _ = 250344238 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 272205859) ^ 136102929 = 272205858 := by
        calc
          (2 : ZMod 272205859) ^ 136102929 = (2 : ZMod 272205859) ^ (68051464 + 68051464 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 68051464 * (2 : ZMod 272205859) ^ 68051464) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 272205858 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 272205859) ^ 272205858 = 1 := by
        calc
          (2 : ZMod 272205859) ^ 272205858 = (2 : ZMod 272205859) ^ (136102929 + 136102929) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 136102929 * (2 : ZMod 272205859) ^ 136102929 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (47, 1), (67, 1), (14407, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (47, 1), (67, 1), (14407, 1)] : List FactorBlock).map factorBlockValue).prod = 272205859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 272205859) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 272205859) ^ 2 = 4 := by
        calc
          (2 : ZMod 272205859) ^ 2 = (2 : ZMod 272205859) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 1 * (2 : ZMod 272205859) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 272205859) ^ 4 = 16 := by
        calc
          (2 : ZMod 272205859) ^ 4 = (2 : ZMod 272205859) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 2 * (2 : ZMod 272205859) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 272205859) ^ 8 = 256 := by
        calc
          (2 : ZMod 272205859) ^ 8 = (2 : ZMod 272205859) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 4 * (2 : ZMod 272205859) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 272205859) ^ 16 = 65536 := by
        calc
          (2 : ZMod 272205859) ^ 16 = (2 : ZMod 272205859) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 8 * (2 : ZMod 272205859) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 272205859) ^ 32 = 211879411 := by
        calc
          (2 : ZMod 272205859) ^ 32 = (2 : ZMod 272205859) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 16 * (2 : ZMod 272205859) ^ 16 := by rw [pow_add]
          _ = 211879411 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 272205859) ^ 64 = 142280612 := by
        calc
          (2 : ZMod 272205859) ^ 64 = (2 : ZMod 272205859) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 32 * (2 : ZMod 272205859) ^ 32 := by rw [pow_add]
          _ = 142280612 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 272205859) ^ 129 = 46557506 := by
        calc
          (2 : ZMod 272205859) ^ 129 = (2 : ZMod 272205859) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 64 * (2 : ZMod 272205859) ^ 64) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 46557506 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 272205859) ^ 259 = 228127003 := by
        calc
          (2 : ZMod 272205859) ^ 259 = (2 : ZMod 272205859) ^ (129 + 129 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 129 * (2 : ZMod 272205859) ^ 129) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 228127003 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 272205859) ^ 519 = 20031432 := by
        calc
          (2 : ZMod 272205859) ^ 519 = (2 : ZMod 272205859) ^ (259 + 259 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 259 * (2 : ZMod 272205859) ^ 259) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 20031432 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 272205859) ^ 1038 = 155630442 := by
        calc
          (2 : ZMod 272205859) ^ 1038 = (2 : ZMod 272205859) ^ (519 + 519) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 519 * (2 : ZMod 272205859) ^ 519 := by rw [pow_add]
          _ = 155630442 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 272205859) ^ 2076 = 151821086 := by
        calc
          (2 : ZMod 272205859) ^ 2076 = (2 : ZMod 272205859) ^ (1038 + 1038) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 1038 * (2 : ZMod 272205859) ^ 1038 := by rw [pow_add]
          _ = 151821086 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 272205859) ^ 4153 = 154687741 := by
        calc
          (2 : ZMod 272205859) ^ 4153 = (2 : ZMod 272205859) ^ (2076 + 2076 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 2076 * (2 : ZMod 272205859) ^ 2076) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 154687741 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 272205859) ^ 8307 = 154406744 := by
        calc
          (2 : ZMod 272205859) ^ 8307 = (2 : ZMod 272205859) ^ (4153 + 4153 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 4153 * (2 : ZMod 272205859) ^ 4153) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 154406744 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 272205859) ^ 16614 = 83073970 := by
        calc
          (2 : ZMod 272205859) ^ 16614 = (2 : ZMod 272205859) ^ (8307 + 8307) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 8307 * (2 : ZMod 272205859) ^ 8307 := by rw [pow_add]
          _ = 83073970 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 272205859) ^ 33228 = 79073421 := by
        calc
          (2 : ZMod 272205859) ^ 33228 = (2 : ZMod 272205859) ^ (16614 + 16614) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 16614 * (2 : ZMod 272205859) ^ 16614 := by rw [pow_add]
          _ = 79073421 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 272205859) ^ 66456 = 35210558 := by
        calc
          (2 : ZMod 272205859) ^ 66456 = (2 : ZMod 272205859) ^ (33228 + 33228) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 33228 * (2 : ZMod 272205859) ^ 33228 := by rw [pow_add]
          _ = 35210558 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 272205859) ^ 132913 = 66774288 := by
        calc
          (2 : ZMod 272205859) ^ 132913 = (2 : ZMod 272205859) ^ (66456 + 66456 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 66456 * (2 : ZMod 272205859) ^ 66456) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 66774288 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 272205859) ^ 265826 = 71905014 := by
        calc
          (2 : ZMod 272205859) ^ 265826 = (2 : ZMod 272205859) ^ (132913 + 132913) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 132913 * (2 : ZMod 272205859) ^ 132913 := by rw [pow_add]
          _ = 71905014 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 272205859) ^ 531652 = 144557550 := by
        calc
          (2 : ZMod 272205859) ^ 531652 = (2 : ZMod 272205859) ^ (265826 + 265826) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 265826 * (2 : ZMod 272205859) ^ 265826 := by rw [pow_add]
          _ = 144557550 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 272205859) ^ 1063304 = 233894662 := by
        calc
          (2 : ZMod 272205859) ^ 1063304 = (2 : ZMod 272205859) ^ (531652 + 531652) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 531652 * (2 : ZMod 272205859) ^ 531652 := by rw [pow_add]
          _ = 233894662 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 272205859) ^ 2126608 = 213551859 := by
        calc
          (2 : ZMod 272205859) ^ 2126608 = (2 : ZMod 272205859) ^ (1063304 + 1063304) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 1063304 * (2 : ZMod 272205859) ^ 1063304 := by rw [pow_add]
          _ = 213551859 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 272205859) ^ 4253216 = 1441806 := by
        calc
          (2 : ZMod 272205859) ^ 4253216 = (2 : ZMod 272205859) ^ (2126608 + 2126608) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 2126608 * (2 : ZMod 272205859) ^ 2126608 := by rw [pow_add]
          _ = 1441806 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 272205859) ^ 8506433 = 208998765 := by
        calc
          (2 : ZMod 272205859) ^ 8506433 = (2 : ZMod 272205859) ^ (4253216 + 4253216 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 4253216 * (2 : ZMod 272205859) ^ 4253216) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 208998765 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 272205859) ^ 17012866 = 193202890 := by
        calc
          (2 : ZMod 272205859) ^ 17012866 = (2 : ZMod 272205859) ^ (8506433 + 8506433) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 8506433 * (2 : ZMod 272205859) ^ 8506433 := by rw [pow_add]
          _ = 193202890 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 272205859) ^ 34025732 = 267897404 := by
        calc
          (2 : ZMod 272205859) ^ 34025732 = (2 : ZMod 272205859) ^ (17012866 + 17012866) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 17012866 * (2 : ZMod 272205859) ^ 17012866 := by rw [pow_add]
          _ = 267897404 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 272205859) ^ 68051464 = 250344238 := by
        calc
          (2 : ZMod 272205859) ^ 68051464 = (2 : ZMod 272205859) ^ (34025732 + 34025732) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 34025732 * (2 : ZMod 272205859) ^ 34025732 := by rw [pow_add]
          _ = 250344238 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 272205859) ^ 136102929 = 272205858 := by
        calc
          (2 : ZMod 272205859) ^ 136102929 = (2 : ZMod 272205859) ^ (68051464 + 68051464 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 68051464 * (2 : ZMod 272205859) ^ 68051464) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 272205858 := by rw [factor_0_26]; decide
      change (2 : ZMod 272205859) ^ 136102929 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (2 : ZMod 272205859) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 272205859) ^ 2 = 4 := by
        calc
          (2 : ZMod 272205859) ^ 2 = (2 : ZMod 272205859) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 1 * (2 : ZMod 272205859) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 272205859) ^ 5 = 32 := by
        calc
          (2 : ZMod 272205859) ^ 5 = (2 : ZMod 272205859) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 2 * (2 : ZMod 272205859) ^ 2) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 272205859) ^ 10 = 1024 := by
        calc
          (2 : ZMod 272205859) ^ 10 = (2 : ZMod 272205859) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 5 * (2 : ZMod 272205859) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 272205859) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 272205859) ^ 21 = (2 : ZMod 272205859) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 10 * (2 : ZMod 272205859) ^ 10) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 272205859) ^ 43 = 32894482 := by
        calc
          (2 : ZMod 272205859) ^ 43 = (2 : ZMod 272205859) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 21 * (2 : ZMod 272205859) ^ 21) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 32894482 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 272205859) ^ 86 = 74908129 := by
        calc
          (2 : ZMod 272205859) ^ 86 = (2 : ZMod 272205859) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 43 * (2 : ZMod 272205859) ^ 43 := by rw [pow_add]
          _ = 74908129 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 272205859) ^ 173 = 61734607 := by
        calc
          (2 : ZMod 272205859) ^ 173 = (2 : ZMod 272205859) ^ (86 + 86 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 86 * (2 : ZMod 272205859) ^ 86) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 61734607 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 272205859) ^ 346 = 120027256 := by
        calc
          (2 : ZMod 272205859) ^ 346 = (2 : ZMod 272205859) ^ (173 + 173) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 173 * (2 : ZMod 272205859) ^ 173 := by rw [pow_add]
          _ = 120027256 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 272205859) ^ 692 = 3700929 := by
        calc
          (2 : ZMod 272205859) ^ 692 = (2 : ZMod 272205859) ^ (346 + 346) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 346 * (2 : ZMod 272205859) ^ 346 := by rw [pow_add]
          _ = 3700929 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 272205859) ^ 1384 = 21049879 := by
        calc
          (2 : ZMod 272205859) ^ 1384 = (2 : ZMod 272205859) ^ (692 + 692) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 692 * (2 : ZMod 272205859) ^ 692 := by rw [pow_add]
          _ = 21049879 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 272205859) ^ 2769 = 56239587 := by
        calc
          (2 : ZMod 272205859) ^ 2769 = (2 : ZMod 272205859) ^ (1384 + 1384 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 1384 * (2 : ZMod 272205859) ^ 1384) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 56239587 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 272205859) ^ 5538 = 66985531 := by
        calc
          (2 : ZMod 272205859) ^ 5538 = (2 : ZMod 272205859) ^ (2769 + 2769) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 2769 * (2 : ZMod 272205859) ^ 2769 := by rw [pow_add]
          _ = 66985531 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 272205859) ^ 11076 = 112568254 := by
        calc
          (2 : ZMod 272205859) ^ 11076 = (2 : ZMod 272205859) ^ (5538 + 5538) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 5538 * (2 : ZMod 272205859) ^ 5538 := by rw [pow_add]
          _ = 112568254 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 272205859) ^ 22152 = 75724732 := by
        calc
          (2 : ZMod 272205859) ^ 22152 = (2 : ZMod 272205859) ^ (11076 + 11076) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 11076 * (2 : ZMod 272205859) ^ 11076 := by rw [pow_add]
          _ = 75724732 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 272205859) ^ 44304 = 35332047 := by
        calc
          (2 : ZMod 272205859) ^ 44304 = (2 : ZMod 272205859) ^ (22152 + 22152) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 22152 * (2 : ZMod 272205859) ^ 22152 := by rw [pow_add]
          _ = 35332047 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 272205859) ^ 88608 = 54661233 := by
        calc
          (2 : ZMod 272205859) ^ 88608 = (2 : ZMod 272205859) ^ (44304 + 44304) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 44304 * (2 : ZMod 272205859) ^ 44304 := by rw [pow_add]
          _ = 54661233 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 272205859) ^ 177217 = 133677671 := by
        calc
          (2 : ZMod 272205859) ^ 177217 = (2 : ZMod 272205859) ^ (88608 + 88608 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 88608 * (2 : ZMod 272205859) ^ 88608) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 133677671 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 272205859) ^ 354434 = 122642015 := by
        calc
          (2 : ZMod 272205859) ^ 354434 = (2 : ZMod 272205859) ^ (177217 + 177217) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 177217 * (2 : ZMod 272205859) ^ 177217 := by rw [pow_add]
          _ = 122642015 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 272205859) ^ 708869 = 14663388 := by
        calc
          (2 : ZMod 272205859) ^ 708869 = (2 : ZMod 272205859) ^ (354434 + 354434 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 354434 * (2 : ZMod 272205859) ^ 354434) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 14663388 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 272205859) ^ 1417738 = 84026162 := by
        calc
          (2 : ZMod 272205859) ^ 1417738 = (2 : ZMod 272205859) ^ (708869 + 708869) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 708869 * (2 : ZMod 272205859) ^ 708869 := by rw [pow_add]
          _ = 84026162 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 272205859) ^ 2835477 = 172049862 := by
        calc
          (2 : ZMod 272205859) ^ 2835477 = (2 : ZMod 272205859) ^ (1417738 + 1417738 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 1417738 * (2 : ZMod 272205859) ^ 1417738) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 172049862 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 272205859) ^ 5670955 = 247785474 := by
        calc
          (2 : ZMod 272205859) ^ 5670955 = (2 : ZMod 272205859) ^ (2835477 + 2835477 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 2835477 * (2 : ZMod 272205859) ^ 2835477) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 247785474 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 272205859) ^ 11341910 = 74710409 := by
        calc
          (2 : ZMod 272205859) ^ 11341910 = (2 : ZMod 272205859) ^ (5670955 + 5670955) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 5670955 * (2 : ZMod 272205859) ^ 5670955 := by rw [pow_add]
          _ = 74710409 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 272205859) ^ 22683821 = 211550832 := by
        calc
          (2 : ZMod 272205859) ^ 22683821 = (2 : ZMod 272205859) ^ (11341910 + 11341910 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 11341910 * (2 : ZMod 272205859) ^ 11341910) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 211550832 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 272205859) ^ 45367643 = 246853567 := by
        calc
          (2 : ZMod 272205859) ^ 45367643 = (2 : ZMod 272205859) ^ (22683821 + 22683821 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 22683821 * (2 : ZMod 272205859) ^ 22683821) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 246853567 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 272205859) ^ 90735286 = 246853566 := by
        calc
          (2 : ZMod 272205859) ^ 90735286 = (2 : ZMod 272205859) ^ (45367643 + 45367643) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 45367643 * (2 : ZMod 272205859) ^ 45367643 := by rw [pow_add]
          _ = 246853566 := by rw [factor_1_25]; decide
      change (2 : ZMod 272205859) ^ 90735286 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (2 : ZMod 272205859) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 272205859) ^ 2 = 4 := by
        calc
          (2 : ZMod 272205859) ^ 2 = (2 : ZMod 272205859) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 1 * (2 : ZMod 272205859) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 272205859) ^ 5 = 32 := by
        calc
          (2 : ZMod 272205859) ^ 5 = (2 : ZMod 272205859) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 2 * (2 : ZMod 272205859) ^ 2) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 272205859) ^ 11 = 2048 := by
        calc
          (2 : ZMod 272205859) ^ 11 = (2 : ZMod 272205859) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 5 * (2 : ZMod 272205859) ^ 5) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 272205859) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 272205859) ^ 22 = (2 : ZMod 272205859) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 11 * (2 : ZMod 272205859) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 272205859) ^ 44 = 65788964 := by
        calc
          (2 : ZMod 272205859) ^ 44 = (2 : ZMod 272205859) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 22 * (2 : ZMod 272205859) ^ 22 := by rw [pow_add]
          _ = 65788964 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 272205859) ^ 88 = 27426657 := by
        calc
          (2 : ZMod 272205859) ^ 88 = (2 : ZMod 272205859) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 44 * (2 : ZMod 272205859) ^ 44 := by rw [pow_add]
          _ = 27426657 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 272205859) ^ 176 = 221670997 := by
        calc
          (2 : ZMod 272205859) ^ 176 = (2 : ZMod 272205859) ^ (88 + 88) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 88 * (2 : ZMod 272205859) ^ 88 := by rw [pow_add]
          _ = 221670997 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 272205859) ^ 353 = 119960664 := by
        calc
          (2 : ZMod 272205859) ^ 353 = (2 : ZMod 272205859) ^ (176 + 176 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 176 * (2 : ZMod 272205859) ^ 176) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 119960664 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 272205859) ^ 706 = 206320038 := by
        calc
          (2 : ZMod 272205859) ^ 706 = (2 : ZMod 272205859) ^ (353 + 353) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 353 * (2 : ZMod 272205859) ^ 353 := by rw [pow_add]
          _ = 206320038 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 272205859) ^ 1413 = 254137209 := by
        calc
          (2 : ZMod 272205859) ^ 1413 = (2 : ZMod 272205859) ^ (706 + 706 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 706 * (2 : ZMod 272205859) ^ 706) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 254137209 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 272205859) ^ 2827 = 54603904 := by
        calc
          (2 : ZMod 272205859) ^ 2827 = (2 : ZMod 272205859) ^ (1413 + 1413 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 1413 * (2 : ZMod 272205859) ^ 1413) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 54603904 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 272205859) ^ 5655 = 14054141 := by
        calc
          (2 : ZMod 272205859) ^ 5655 = (2 : ZMod 272205859) ^ (2827 + 2827 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 2827 * (2 : ZMod 272205859) ^ 2827) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 14054141 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 272205859) ^ 11311 = 94445448 := by
        calc
          (2 : ZMod 272205859) ^ 11311 = (2 : ZMod 272205859) ^ (5655 + 5655 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 5655 * (2 : ZMod 272205859) ^ 5655) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 94445448 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 272205859) ^ 22623 = 1057300 := by
        calc
          (2 : ZMod 272205859) ^ 22623 = (2 : ZMod 272205859) ^ (11311 + 11311 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 11311 * (2 : ZMod 272205859) ^ 11311) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 1057300 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 272205859) ^ 45246 = 206032946 := by
        calc
          (2 : ZMod 272205859) ^ 45246 = (2 : ZMod 272205859) ^ (22623 + 22623) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 22623 * (2 : ZMod 272205859) ^ 22623 := by rw [pow_add]
          _ = 206032946 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 272205859) ^ 90493 = 57765507 := by
        calc
          (2 : ZMod 272205859) ^ 90493 = (2 : ZMod 272205859) ^ (45246 + 45246 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 45246 * (2 : ZMod 272205859) ^ 45246) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 57765507 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 272205859) ^ 180987 = 77245992 := by
        calc
          (2 : ZMod 272205859) ^ 180987 = (2 : ZMod 272205859) ^ (90493 + 90493 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 90493 * (2 : ZMod 272205859) ^ 90493) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 77245992 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 272205859) ^ 361975 = 68953810 := by
        calc
          (2 : ZMod 272205859) ^ 361975 = (2 : ZMod 272205859) ^ (180987 + 180987 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 180987 * (2 : ZMod 272205859) ^ 180987) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 68953810 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 272205859) ^ 723951 = 16374660 := by
        calc
          (2 : ZMod 272205859) ^ 723951 = (2 : ZMod 272205859) ^ (361975 + 361975 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 361975 * (2 : ZMod 272205859) ^ 361975) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 16374660 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 272205859) ^ 1447903 = 99914109 := by
        calc
          (2 : ZMod 272205859) ^ 1447903 = (2 : ZMod 272205859) ^ (723951 + 723951 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 723951 * (2 : ZMod 272205859) ^ 723951) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 99914109 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 272205859) ^ 2895807 = 186087425 := by
        calc
          (2 : ZMod 272205859) ^ 2895807 = (2 : ZMod 272205859) ^ (1447903 + 1447903 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 1447903 * (2 : ZMod 272205859) ^ 1447903) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 186087425 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 272205859) ^ 5791614 = 215433715 := by
        calc
          (2 : ZMod 272205859) ^ 5791614 = (2 : ZMod 272205859) ^ (2895807 + 2895807) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 2895807 * (2 : ZMod 272205859) ^ 2895807 := by rw [pow_add]
          _ = 215433715 := by rw [factor_2_21]; decide
      change (2 : ZMod 272205859) ^ 5791614 ≠ 1
      rw [factor_2_22]
      decide
    ·
      have factor_3_0 : (2 : ZMod 272205859) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 272205859) ^ 3 = 8 := by
        calc
          (2 : ZMod 272205859) ^ 3 = (2 : ZMod 272205859) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 1 * (2 : ZMod 272205859) ^ 1) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 272205859) ^ 7 = 128 := by
        calc
          (2 : ZMod 272205859) ^ 7 = (2 : ZMod 272205859) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 3 * (2 : ZMod 272205859) ^ 3) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 272205859) ^ 15 = 32768 := by
        calc
          (2 : ZMod 272205859) ^ 15 = (2 : ZMod 272205859) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 7 * (2 : ZMod 272205859) ^ 7) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 272205859) ^ 30 = 257124247 := by
        calc
          (2 : ZMod 272205859) ^ 30 = (2 : ZMod 272205859) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 15 * (2 : ZMod 272205859) ^ 15 := by rw [pow_add]
          _ = 257124247 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 272205859) ^ 61 = 153888006 := by
        calc
          (2 : ZMod 272205859) ^ 61 = (2 : ZMod 272205859) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 30 * (2 : ZMod 272205859) ^ 30) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 153888006 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 272205859) ^ 123 = 179362556 := by
        calc
          (2 : ZMod 272205859) ^ 123 = (2 : ZMod 272205859) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 61 * (2 : ZMod 272205859) ^ 61) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 179362556 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 272205859) ^ 247 = 158953207 := by
        calc
          (2 : ZMod 272205859) ^ 247 = (2 : ZMod 272205859) ^ (123 + 123 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 123 * (2 : ZMod 272205859) ^ 123) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 158953207 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 272205859) ^ 495 = 85522908 := by
        calc
          (2 : ZMod 272205859) ^ 495 = (2 : ZMod 272205859) ^ (247 + 247 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 247 * (2 : ZMod 272205859) ^ 247) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 85522908 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 272205859) ^ 991 = 72451121 := by
        calc
          (2 : ZMod 272205859) ^ 991 = (2 : ZMod 272205859) ^ (495 + 495 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 495 * (2 : ZMod 272205859) ^ 495) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 72451121 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 272205859) ^ 1983 = 186480433 := by
        calc
          (2 : ZMod 272205859) ^ 1983 = (2 : ZMod 272205859) ^ (991 + 991 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 991 * (2 : ZMod 272205859) ^ 991) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 186480433 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 272205859) ^ 3967 = 221111778 := by
        calc
          (2 : ZMod 272205859) ^ 3967 = (2 : ZMod 272205859) ^ (1983 + 1983 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 1983 * (2 : ZMod 272205859) ^ 1983) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 221111778 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 272205859) ^ 7935 = 246757350 := by
        calc
          (2 : ZMod 272205859) ^ 7935 = (2 : ZMod 272205859) ^ (3967 + 3967 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 3967 * (2 : ZMod 272205859) ^ 3967) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 246757350 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 272205859) ^ 15870 = 146913320 := by
        calc
          (2 : ZMod 272205859) ^ 15870 = (2 : ZMod 272205859) ^ (7935 + 7935) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 7935 * (2 : ZMod 272205859) ^ 7935 := by rw [pow_add]
          _ = 146913320 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 272205859) ^ 31740 = 102604639 := by
        calc
          (2 : ZMod 272205859) ^ 31740 = (2 : ZMod 272205859) ^ (15870 + 15870) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 15870 * (2 : ZMod 272205859) ^ 15870 := by rw [pow_add]
          _ = 102604639 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 272205859) ^ 63480 = 89861153 := by
        calc
          (2 : ZMod 272205859) ^ 63480 = (2 : ZMod 272205859) ^ (31740 + 31740) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 31740 * (2 : ZMod 272205859) ^ 31740 := by rw [pow_add]
          _ = 89861153 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 272205859) ^ 126961 = 266192131 := by
        calc
          (2 : ZMod 272205859) ^ 126961 = (2 : ZMod 272205859) ^ (63480 + 63480 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 63480 * (2 : ZMod 272205859) ^ 63480) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 266192131 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 272205859) ^ 253923 = 124680065 := by
        calc
          (2 : ZMod 272205859) ^ 253923 = (2 : ZMod 272205859) ^ (126961 + 126961 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 126961 * (2 : ZMod 272205859) ^ 126961) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 124680065 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 272205859) ^ 507846 = 22925175 := by
        calc
          (2 : ZMod 272205859) ^ 507846 = (2 : ZMod 272205859) ^ (253923 + 253923) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 253923 * (2 : ZMod 272205859) ^ 253923 := by rw [pow_add]
          _ = 22925175 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 272205859) ^ 1015693 = 17739006 := by
        calc
          (2 : ZMod 272205859) ^ 1015693 = (2 : ZMod 272205859) ^ (507846 + 507846 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 507846 * (2 : ZMod 272205859) ^ 507846) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 17739006 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 272205859) ^ 2031387 = 94228469 := by
        calc
          (2 : ZMod 272205859) ^ 2031387 = (2 : ZMod 272205859) ^ (1015693 + 1015693 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 1015693 * (2 : ZMod 272205859) ^ 1015693) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 94228469 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 272205859) ^ 4062774 = 122856212 := by
        calc
          (2 : ZMod 272205859) ^ 4062774 = (2 : ZMod 272205859) ^ (2031387 + 2031387) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 2031387 * (2 : ZMod 272205859) ^ 2031387 := by rw [pow_add]
          _ = 122856212 := by rw [factor_3_20]; decide
      change (2 : ZMod 272205859) ^ 4062774 ≠ 1
      rw [factor_3_21]
      decide
    ·
      have factor_4_0 : (2 : ZMod 272205859) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 272205859) ^ 2 = 4 := by
        calc
          (2 : ZMod 272205859) ^ 2 = (2 : ZMod 272205859) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 1 * (2 : ZMod 272205859) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 272205859) ^ 4 = 16 := by
        calc
          (2 : ZMod 272205859) ^ 4 = (2 : ZMod 272205859) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 2 * (2 : ZMod 272205859) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 272205859) ^ 9 = 512 := by
        calc
          (2 : ZMod 272205859) ^ 9 = (2 : ZMod 272205859) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 4 * (2 : ZMod 272205859) ^ 4) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 272205859) ^ 18 = 262144 := by
        calc
          (2 : ZMod 272205859) ^ 18 = (2 : ZMod 272205859) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 9 * (2 : ZMod 272205859) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 272205859) ^ 36 = 123600268 := by
        calc
          (2 : ZMod 272205859) ^ 36 = (2 : ZMod 272205859) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 18 * (2 : ZMod 272205859) ^ 18 := by rw [pow_add]
          _ = 123600268 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 272205859) ^ 73 = 168708991 := by
        calc
          (2 : ZMod 272205859) ^ 73 = (2 : ZMod 272205859) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 36 * (2 : ZMod 272205859) ^ 36) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 168708991 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 272205859) ^ 147 = 148958740 := by
        calc
          (2 : ZMod 272205859) ^ 147 = (2 : ZMod 272205859) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 73 * (2 : ZMod 272205859) ^ 73) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 148958740 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 272205859) ^ 295 = 205655165 := by
        calc
          (2 : ZMod 272205859) ^ 295 = (2 : ZMod 272205859) ^ (147 + 147 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 147 * (2 : ZMod 272205859) ^ 147) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 205655165 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 272205859) ^ 590 = 30528091 := by
        calc
          (2 : ZMod 272205859) ^ 590 = (2 : ZMod 272205859) ^ (295 + 295) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 295 * (2 : ZMod 272205859) ^ 295 := by rw [pow_add]
          _ = 30528091 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 272205859) ^ 1180 = 74764749 := by
        calc
          (2 : ZMod 272205859) ^ 1180 = (2 : ZMod 272205859) ^ (590 + 590) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 590 * (2 : ZMod 272205859) ^ 590 := by rw [pow_add]
          _ = 74764749 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 272205859) ^ 2361 = 198263011 := by
        calc
          (2 : ZMod 272205859) ^ 2361 = (2 : ZMod 272205859) ^ (1180 + 1180 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 1180 * (2 : ZMod 272205859) ^ 1180) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 198263011 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 272205859) ^ 4723 = 113986679 := by
        calc
          (2 : ZMod 272205859) ^ 4723 = (2 : ZMod 272205859) ^ (2361 + 2361 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 2361 * (2 : ZMod 272205859) ^ 2361) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 113986679 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 272205859) ^ 9447 = 253710063 := by
        calc
          (2 : ZMod 272205859) ^ 9447 = (2 : ZMod 272205859) ^ (4723 + 4723 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = ((2 : ZMod 272205859) ^ 4723 * (2 : ZMod 272205859) ^ 4723) * (2 : ZMod 272205859) := by rw [pow_succ, pow_add]
          _ = 253710063 := by rw [factor_4_12]; decide
      have factor_4_14 : (2 : ZMod 272205859) ^ 18894 = 28581225 := by
        calc
          (2 : ZMod 272205859) ^ 18894 = (2 : ZMod 272205859) ^ (9447 + 9447) :=
            congrArg (fun n : ℕ => (2 : ZMod 272205859) ^ n) (by norm_num)
          _ = (2 : ZMod 272205859) ^ 9447 * (2 : ZMod 272205859) ^ 9447 := by rw [pow_add]
          _ = 28581225 := by rw [factor_4_13]; decide
      change (2 : ZMod 272205859) ^ 18894 ≠ 1
      rw [factor_4_14]
      decide

#print axioms prime_lucas_272205859

end TotientTailPeriodKiller
end Erdos249257
