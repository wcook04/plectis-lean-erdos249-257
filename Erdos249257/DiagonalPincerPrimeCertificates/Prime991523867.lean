import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime495761933

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_991523867 : Nat.Prime 991523867 := by
  apply lucas_primality 991523867 (2 : ZMod 991523867)
  ·
      have fermat_0 : (2 : ZMod 991523867) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 991523867) ^ 3 = 8 := by
        calc
          (2 : ZMod 991523867) ^ 3 = (2 : ZMod 991523867) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 1 * (2 : ZMod 991523867) ^ 1) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 991523867) ^ 7 = 128 := by
        calc
          (2 : ZMod 991523867) ^ 7 = (2 : ZMod 991523867) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 3 * (2 : ZMod 991523867) ^ 3) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 991523867) ^ 14 = 16384 := by
        calc
          (2 : ZMod 991523867) ^ 14 = (2 : ZMod 991523867) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 7 * (2 : ZMod 991523867) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 991523867) ^ 29 = 536870912 := by
        calc
          (2 : ZMod 991523867) ^ 29 = (2 : ZMod 991523867) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 14 * (2 : ZMod 991523867) ^ 14) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 536870912 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 991523867) ^ 59 = 79797928 := by
        calc
          (2 : ZMod 991523867) ^ 59 = (2 : ZMod 991523867) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 29 * (2 : ZMod 991523867) ^ 29) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 79797928 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 991523867) ^ 118 = 259782336 := by
        calc
          (2 : ZMod 991523867) ^ 118 = (2 : ZMod 991523867) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 59 * (2 : ZMod 991523867) ^ 59 := by rw [pow_add]
          _ = 259782336 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 991523867) ^ 236 = 740903503 := by
        calc
          (2 : ZMod 991523867) ^ 236 = (2 : ZMod 991523867) ^ (118 + 118) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 118 * (2 : ZMod 991523867) ^ 118 := by rw [pow_add]
          _ = 740903503 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 991523867) ^ 472 = 754519060 := by
        calc
          (2 : ZMod 991523867) ^ 472 = (2 : ZMod 991523867) ^ (236 + 236) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 236 * (2 : ZMod 991523867) ^ 236 := by rw [pow_add]
          _ = 754519060 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 991523867) ^ 945 = 760755789 := by
        calc
          (2 : ZMod 991523867) ^ 945 = (2 : ZMod 991523867) ^ (472 + 472 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 472 * (2 : ZMod 991523867) ^ 472) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 760755789 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 991523867) ^ 1891 = 470490467 := by
        calc
          (2 : ZMod 991523867) ^ 1891 = (2 : ZMod 991523867) ^ (945 + 945 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 945 * (2 : ZMod 991523867) ^ 945) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 470490467 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 991523867) ^ 3782 = 795063687 := by
        calc
          (2 : ZMod 991523867) ^ 3782 = (2 : ZMod 991523867) ^ (1891 + 1891) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 1891 * (2 : ZMod 991523867) ^ 1891 := by rw [pow_add]
          _ = 795063687 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 991523867) ^ 7564 = 923711284 := by
        calc
          (2 : ZMod 991523867) ^ 7564 = (2 : ZMod 991523867) ^ (3782 + 3782) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 3782 * (2 : ZMod 991523867) ^ 3782 := by rw [pow_add]
          _ = 923711284 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 991523867) ^ 15129 = 20273873 := by
        calc
          (2 : ZMod 991523867) ^ 15129 = (2 : ZMod 991523867) ^ (7564 + 7564 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 7564 * (2 : ZMod 991523867) ^ 7564) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 20273873 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 991523867) ^ 30258 = 648022348 := by
        calc
          (2 : ZMod 991523867) ^ 30258 = (2 : ZMod 991523867) ^ (15129 + 15129) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 15129 * (2 : ZMod 991523867) ^ 15129 := by rw [pow_add]
          _ = 648022348 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 991523867) ^ 60517 = 160578742 := by
        calc
          (2 : ZMod 991523867) ^ 60517 = (2 : ZMod 991523867) ^ (30258 + 30258 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 30258 * (2 : ZMod 991523867) ^ 30258) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 160578742 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 991523867) ^ 121035 = 750015020 := by
        calc
          (2 : ZMod 991523867) ^ 121035 = (2 : ZMod 991523867) ^ (60517 + 60517 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 60517 * (2 : ZMod 991523867) ^ 60517) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 750015020 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 991523867) ^ 242071 = 652164063 := by
        calc
          (2 : ZMod 991523867) ^ 242071 = (2 : ZMod 991523867) ^ (121035 + 121035 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 121035 * (2 : ZMod 991523867) ^ 121035) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 652164063 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 991523867) ^ 484142 = 816511891 := by
        calc
          (2 : ZMod 991523867) ^ 484142 = (2 : ZMod 991523867) ^ (242071 + 242071) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 242071 * (2 : ZMod 991523867) ^ 242071 := by rw [pow_add]
          _ = 816511891 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 991523867) ^ 968285 = 410518600 := by
        calc
          (2 : ZMod 991523867) ^ 968285 = (2 : ZMod 991523867) ^ (484142 + 484142 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 484142 * (2 : ZMod 991523867) ^ 484142) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 410518600 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 991523867) ^ 1936570 = 859237408 := by
        calc
          (2 : ZMod 991523867) ^ 1936570 = (2 : ZMod 991523867) ^ (968285 + 968285) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 968285 * (2 : ZMod 991523867) ^ 968285 := by rw [pow_add]
          _ = 859237408 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 991523867) ^ 3873140 = 91296246 := by
        calc
          (2 : ZMod 991523867) ^ 3873140 = (2 : ZMod 991523867) ^ (1936570 + 1936570) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 1936570 * (2 : ZMod 991523867) ^ 1936570 := by rw [pow_add]
          _ = 91296246 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 991523867) ^ 7746280 = 86056697 := by
        calc
          (2 : ZMod 991523867) ^ 7746280 = (2 : ZMod 991523867) ^ (3873140 + 3873140) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 3873140 * (2 : ZMod 991523867) ^ 3873140 := by rw [pow_add]
          _ = 86056697 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 991523867) ^ 15492560 = 869923188 := by
        calc
          (2 : ZMod 991523867) ^ 15492560 = (2 : ZMod 991523867) ^ (7746280 + 7746280) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 7746280 * (2 : ZMod 991523867) ^ 7746280 := by rw [pow_add]
          _ = 869923188 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 991523867) ^ 30985120 = 806587331 := by
        calc
          (2 : ZMod 991523867) ^ 30985120 = (2 : ZMod 991523867) ^ (15492560 + 15492560) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 15492560 * (2 : ZMod 991523867) ^ 15492560 := by rw [pow_add]
          _ = 806587331 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 991523867) ^ 61970241 = 412679194 := by
        calc
          (2 : ZMod 991523867) ^ 61970241 = (2 : ZMod 991523867) ^ (30985120 + 30985120 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 30985120 * (2 : ZMod 991523867) ^ 30985120) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 412679194 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 991523867) ^ 123940483 = 147713287 := by
        calc
          (2 : ZMod 991523867) ^ 123940483 = (2 : ZMod 991523867) ^ (61970241 + 61970241 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 61970241 * (2 : ZMod 991523867) ^ 61970241) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 147713287 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 991523867) ^ 247880966 = 718395523 := by
        calc
          (2 : ZMod 991523867) ^ 247880966 = (2 : ZMod 991523867) ^ (123940483 + 123940483) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 123940483 * (2 : ZMod 991523867) ^ 123940483 := by rw [pow_add]
          _ = 718395523 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 991523867) ^ 495761933 = 991523866 := by
        calc
          (2 : ZMod 991523867) ^ 495761933 = (2 : ZMod 991523867) ^ (247880966 + 247880966 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 247880966 * (2 : ZMod 991523867) ^ 247880966) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 991523866 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 991523867) ^ 991523866 = 1 := by
        calc
          (2 : ZMod 991523867) ^ 991523866 = (2 : ZMod 991523867) ^ (495761933 + 495761933) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 495761933 * (2 : ZMod 991523867) ^ 495761933 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (495761933, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (495761933, 1)] : List FactorBlock).map factorBlockValue).prod = 991523867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_495761933) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 991523867) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 991523867) ^ 3 = 8 := by
        calc
          (2 : ZMod 991523867) ^ 3 = (2 : ZMod 991523867) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 1 * (2 : ZMod 991523867) ^ 1) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 991523867) ^ 7 = 128 := by
        calc
          (2 : ZMod 991523867) ^ 7 = (2 : ZMod 991523867) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 3 * (2 : ZMod 991523867) ^ 3) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 991523867) ^ 14 = 16384 := by
        calc
          (2 : ZMod 991523867) ^ 14 = (2 : ZMod 991523867) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 7 * (2 : ZMod 991523867) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 991523867) ^ 29 = 536870912 := by
        calc
          (2 : ZMod 991523867) ^ 29 = (2 : ZMod 991523867) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 14 * (2 : ZMod 991523867) ^ 14) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 536870912 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 991523867) ^ 59 = 79797928 := by
        calc
          (2 : ZMod 991523867) ^ 59 = (2 : ZMod 991523867) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 29 * (2 : ZMod 991523867) ^ 29) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 79797928 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 991523867) ^ 118 = 259782336 := by
        calc
          (2 : ZMod 991523867) ^ 118 = (2 : ZMod 991523867) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 59 * (2 : ZMod 991523867) ^ 59 := by rw [pow_add]
          _ = 259782336 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 991523867) ^ 236 = 740903503 := by
        calc
          (2 : ZMod 991523867) ^ 236 = (2 : ZMod 991523867) ^ (118 + 118) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 118 * (2 : ZMod 991523867) ^ 118 := by rw [pow_add]
          _ = 740903503 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 991523867) ^ 472 = 754519060 := by
        calc
          (2 : ZMod 991523867) ^ 472 = (2 : ZMod 991523867) ^ (236 + 236) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 236 * (2 : ZMod 991523867) ^ 236 := by rw [pow_add]
          _ = 754519060 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 991523867) ^ 945 = 760755789 := by
        calc
          (2 : ZMod 991523867) ^ 945 = (2 : ZMod 991523867) ^ (472 + 472 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 472 * (2 : ZMod 991523867) ^ 472) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 760755789 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 991523867) ^ 1891 = 470490467 := by
        calc
          (2 : ZMod 991523867) ^ 1891 = (2 : ZMod 991523867) ^ (945 + 945 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 945 * (2 : ZMod 991523867) ^ 945) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 470490467 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 991523867) ^ 3782 = 795063687 := by
        calc
          (2 : ZMod 991523867) ^ 3782 = (2 : ZMod 991523867) ^ (1891 + 1891) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 1891 * (2 : ZMod 991523867) ^ 1891 := by rw [pow_add]
          _ = 795063687 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 991523867) ^ 7564 = 923711284 := by
        calc
          (2 : ZMod 991523867) ^ 7564 = (2 : ZMod 991523867) ^ (3782 + 3782) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 3782 * (2 : ZMod 991523867) ^ 3782 := by rw [pow_add]
          _ = 923711284 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 991523867) ^ 15129 = 20273873 := by
        calc
          (2 : ZMod 991523867) ^ 15129 = (2 : ZMod 991523867) ^ (7564 + 7564 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 7564 * (2 : ZMod 991523867) ^ 7564) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 20273873 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 991523867) ^ 30258 = 648022348 := by
        calc
          (2 : ZMod 991523867) ^ 30258 = (2 : ZMod 991523867) ^ (15129 + 15129) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 15129 * (2 : ZMod 991523867) ^ 15129 := by rw [pow_add]
          _ = 648022348 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 991523867) ^ 60517 = 160578742 := by
        calc
          (2 : ZMod 991523867) ^ 60517 = (2 : ZMod 991523867) ^ (30258 + 30258 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 30258 * (2 : ZMod 991523867) ^ 30258) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 160578742 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 991523867) ^ 121035 = 750015020 := by
        calc
          (2 : ZMod 991523867) ^ 121035 = (2 : ZMod 991523867) ^ (60517 + 60517 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 60517 * (2 : ZMod 991523867) ^ 60517) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 750015020 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 991523867) ^ 242071 = 652164063 := by
        calc
          (2 : ZMod 991523867) ^ 242071 = (2 : ZMod 991523867) ^ (121035 + 121035 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 121035 * (2 : ZMod 991523867) ^ 121035) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 652164063 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 991523867) ^ 484142 = 816511891 := by
        calc
          (2 : ZMod 991523867) ^ 484142 = (2 : ZMod 991523867) ^ (242071 + 242071) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 242071 * (2 : ZMod 991523867) ^ 242071 := by rw [pow_add]
          _ = 816511891 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 991523867) ^ 968285 = 410518600 := by
        calc
          (2 : ZMod 991523867) ^ 968285 = (2 : ZMod 991523867) ^ (484142 + 484142 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 484142 * (2 : ZMod 991523867) ^ 484142) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 410518600 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 991523867) ^ 1936570 = 859237408 := by
        calc
          (2 : ZMod 991523867) ^ 1936570 = (2 : ZMod 991523867) ^ (968285 + 968285) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 968285 * (2 : ZMod 991523867) ^ 968285 := by rw [pow_add]
          _ = 859237408 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 991523867) ^ 3873140 = 91296246 := by
        calc
          (2 : ZMod 991523867) ^ 3873140 = (2 : ZMod 991523867) ^ (1936570 + 1936570) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 1936570 * (2 : ZMod 991523867) ^ 1936570 := by rw [pow_add]
          _ = 91296246 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 991523867) ^ 7746280 = 86056697 := by
        calc
          (2 : ZMod 991523867) ^ 7746280 = (2 : ZMod 991523867) ^ (3873140 + 3873140) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 3873140 * (2 : ZMod 991523867) ^ 3873140 := by rw [pow_add]
          _ = 86056697 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 991523867) ^ 15492560 = 869923188 := by
        calc
          (2 : ZMod 991523867) ^ 15492560 = (2 : ZMod 991523867) ^ (7746280 + 7746280) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 7746280 * (2 : ZMod 991523867) ^ 7746280 := by rw [pow_add]
          _ = 869923188 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 991523867) ^ 30985120 = 806587331 := by
        calc
          (2 : ZMod 991523867) ^ 30985120 = (2 : ZMod 991523867) ^ (15492560 + 15492560) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 15492560 * (2 : ZMod 991523867) ^ 15492560 := by rw [pow_add]
          _ = 806587331 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 991523867) ^ 61970241 = 412679194 := by
        calc
          (2 : ZMod 991523867) ^ 61970241 = (2 : ZMod 991523867) ^ (30985120 + 30985120 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 30985120 * (2 : ZMod 991523867) ^ 30985120) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 412679194 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 991523867) ^ 123940483 = 147713287 := by
        calc
          (2 : ZMod 991523867) ^ 123940483 = (2 : ZMod 991523867) ^ (61970241 + 61970241 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 61970241 * (2 : ZMod 991523867) ^ 61970241) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 147713287 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 991523867) ^ 247880966 = 718395523 := by
        calc
          (2 : ZMod 991523867) ^ 247880966 = (2 : ZMod 991523867) ^ (123940483 + 123940483) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 123940483 * (2 : ZMod 991523867) ^ 123940483 := by rw [pow_add]
          _ = 718395523 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 991523867) ^ 495761933 = 991523866 := by
        calc
          (2 : ZMod 991523867) ^ 495761933 = (2 : ZMod 991523867) ^ (247880966 + 247880966 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = ((2 : ZMod 991523867) ^ 247880966 * (2 : ZMod 991523867) ^ 247880966) * (2 : ZMod 991523867) := by rw [pow_succ, pow_add]
          _ = 991523866 := by rw [factor_0_27]; decide
      change (2 : ZMod 991523867) ^ 495761933 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (2 : ZMod 991523867) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 991523867) ^ 2 = 4 := by
        calc
          (2 : ZMod 991523867) ^ 2 = (2 : ZMod 991523867) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 991523867) ^ n) (by norm_num)
          _ = (2 : ZMod 991523867) ^ 1 * (2 : ZMod 991523867) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      change (2 : ZMod 991523867) ^ 2 ≠ 1
      rw [factor_1_1]
      decide

#print axioms prime_lucas_991523867

end TotientTailPeriodKiller
end Erdos249257
