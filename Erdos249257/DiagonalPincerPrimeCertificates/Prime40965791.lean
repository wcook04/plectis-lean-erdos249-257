import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_40965791 : Nat.Prime 40965791 := by
  apply lucas_primality 40965791 (19 : ZMod 40965791)
  ·
      have fermat_0 : (19 : ZMod 40965791) ^ 1 = 19 := by norm_num
      have fermat_1 : (19 : ZMod 40965791) ^ 2 = 361 := by
        calc
          (19 : ZMod 40965791) ^ 2 = (19 : ZMod 40965791) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 1 * (19 : ZMod 40965791) ^ 1 := by rw [pow_add]
          _ = 361 := by rw [fermat_0]; decide
      have fermat_2 : (19 : ZMod 40965791) ^ 4 = 130321 := by
        calc
          (19 : ZMod 40965791) ^ 4 = (19 : ZMod 40965791) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 2 * (19 : ZMod 40965791) ^ 2 := by rw [pow_add]
          _ = 130321 := by rw [fermat_1]; decide
      have fermat_3 : (19 : ZMod 40965791) ^ 9 = 162072 := by
        calc
          (19 : ZMod 40965791) ^ 9 = (19 : ZMod 40965791) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 4 * (19 : ZMod 40965791) ^ 4) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 162072 := by rw [fermat_2]; decide
      have fermat_4 : (19 : ZMod 40965791) ^ 19 = 34064534 := by
        calc
          (19 : ZMod 40965791) ^ 19 = (19 : ZMod 40965791) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 9 * (19 : ZMod 40965791) ^ 9) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 34064534 := by rw [fermat_3]; decide
      have fermat_5 : (19 : ZMod 40965791) ^ 39 = 39915691 := by
        calc
          (19 : ZMod 40965791) ^ 39 = (19 : ZMod 40965791) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 19 * (19 : ZMod 40965791) ^ 19) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 39915691 := by rw [fermat_4]; decide
      have fermat_6 : (19 : ZMod 40965791) ^ 78 = 33813653 := by
        calc
          (19 : ZMod 40965791) ^ 78 = (19 : ZMod 40965791) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 39 * (19 : ZMod 40965791) ^ 39 := by rw [pow_add]
          _ = 33813653 := by rw [fermat_5]; decide
      have fermat_7 : (19 : ZMod 40965791) ^ 156 = 36962537 := by
        calc
          (19 : ZMod 40965791) ^ 156 = (19 : ZMod 40965791) ^ (78 + 78) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 78 * (19 : ZMod 40965791) ^ 78 := by rw [pow_add]
          _ = 36962537 := by rw [fermat_6]; decide
      have fermat_8 : (19 : ZMod 40965791) ^ 312 = 20320361 := by
        calc
          (19 : ZMod 40965791) ^ 312 = (19 : ZMod 40965791) ^ (156 + 156) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 156 * (19 : ZMod 40965791) ^ 156 := by rw [pow_add]
          _ = 20320361 := by rw [fermat_7]; decide
      have fermat_9 : (19 : ZMod 40965791) ^ 625 = 8697335 := by
        calc
          (19 : ZMod 40965791) ^ 625 = (19 : ZMod 40965791) ^ (312 + 312 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 312 * (19 : ZMod 40965791) ^ 312) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 8697335 := by rw [fermat_8]; decide
      have fermat_10 : (19 : ZMod 40965791) ^ 1250 = 16260188 := by
        calc
          (19 : ZMod 40965791) ^ 1250 = (19 : ZMod 40965791) ^ (625 + 625) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 625 * (19 : ZMod 40965791) ^ 625 := by rw [pow_add]
          _ = 16260188 := by rw [fermat_9]; decide
      have fermat_11 : (19 : ZMod 40965791) ^ 2500 = 7091852 := by
        calc
          (19 : ZMod 40965791) ^ 2500 = (19 : ZMod 40965791) ^ (1250 + 1250) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 1250 * (19 : ZMod 40965791) ^ 1250 := by rw [pow_add]
          _ = 7091852 := by rw [fermat_10]; decide
      have fermat_12 : (19 : ZMod 40965791) ^ 5000 = 7726548 := by
        calc
          (19 : ZMod 40965791) ^ 5000 = (19 : ZMod 40965791) ^ (2500 + 2500) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 2500 * (19 : ZMod 40965791) ^ 2500 := by rw [pow_add]
          _ = 7726548 := by rw [fermat_11]; decide
      have fermat_13 : (19 : ZMod 40965791) ^ 10001 = 36173272 := by
        calc
          (19 : ZMod 40965791) ^ 10001 = (19 : ZMod 40965791) ^ (5000 + 5000 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 5000 * (19 : ZMod 40965791) ^ 5000) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 36173272 := by rw [fermat_12]; decide
      have fermat_14 : (19 : ZMod 40965791) ^ 20002 = 30256973 := by
        calc
          (19 : ZMod 40965791) ^ 20002 = (19 : ZMod 40965791) ^ (10001 + 10001) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 10001 * (19 : ZMod 40965791) ^ 10001 := by rw [pow_add]
          _ = 30256973 := by rw [fermat_13]; decide
      have fermat_15 : (19 : ZMod 40965791) ^ 40005 = 27455992 := by
        calc
          (19 : ZMod 40965791) ^ 40005 = (19 : ZMod 40965791) ^ (20002 + 20002 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 20002 * (19 : ZMod 40965791) ^ 20002) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 27455992 := by rw [fermat_14]; decide
      have fermat_16 : (19 : ZMod 40965791) ^ 80011 = 5694601 := by
        calc
          (19 : ZMod 40965791) ^ 80011 = (19 : ZMod 40965791) ^ (40005 + 40005 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 40005 * (19 : ZMod 40965791) ^ 40005) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 5694601 := by rw [fermat_15]; decide
      have fermat_17 : (19 : ZMod 40965791) ^ 160022 = 1359392 := by
        calc
          (19 : ZMod 40965791) ^ 160022 = (19 : ZMod 40965791) ^ (80011 + 80011) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 80011 * (19 : ZMod 40965791) ^ 80011 := by rw [pow_add]
          _ = 1359392 := by rw [fermat_16]; decide
      have fermat_18 : (19 : ZMod 40965791) ^ 320045 = 25433336 := by
        calc
          (19 : ZMod 40965791) ^ 320045 = (19 : ZMod 40965791) ^ (160022 + 160022 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 160022 * (19 : ZMod 40965791) ^ 160022) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 25433336 := by rw [fermat_17]; decide
      have fermat_19 : (19 : ZMod 40965791) ^ 640090 = 29132931 := by
        calc
          (19 : ZMod 40965791) ^ 640090 = (19 : ZMod 40965791) ^ (320045 + 320045) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 320045 * (19 : ZMod 40965791) ^ 320045 := by rw [pow_add]
          _ = 29132931 := by rw [fermat_18]; decide
      have fermat_20 : (19 : ZMod 40965791) ^ 1280180 = 8378610 := by
        calc
          (19 : ZMod 40965791) ^ 1280180 = (19 : ZMod 40965791) ^ (640090 + 640090) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 640090 * (19 : ZMod 40965791) ^ 640090 := by rw [pow_add]
          _ = 8378610 := by rw [fermat_19]; decide
      have fermat_21 : (19 : ZMod 40965791) ^ 2560361 = 3145574 := by
        calc
          (19 : ZMod 40965791) ^ 2560361 = (19 : ZMod 40965791) ^ (1280180 + 1280180 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 1280180 * (19 : ZMod 40965791) ^ 1280180) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 3145574 := by rw [fermat_20]; decide
      have fermat_22 : (19 : ZMod 40965791) ^ 5120723 = 2163976 := by
        calc
          (19 : ZMod 40965791) ^ 5120723 = (19 : ZMod 40965791) ^ (2560361 + 2560361 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 2560361 * (19 : ZMod 40965791) ^ 2560361) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 2163976 := by rw [fermat_21]; decide
      have fermat_23 : (19 : ZMod 40965791) ^ 10241447 = 22491118 := by
        calc
          (19 : ZMod 40965791) ^ 10241447 = (19 : ZMod 40965791) ^ (5120723 + 5120723 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 5120723 * (19 : ZMod 40965791) ^ 5120723) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 22491118 := by rw [fermat_22]; decide
      have fermat_24 : (19 : ZMod 40965791) ^ 20482895 = 40965790 := by
        calc
          (19 : ZMod 40965791) ^ 20482895 = (19 : ZMod 40965791) ^ (10241447 + 10241447 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 10241447 * (19 : ZMod 40965791) ^ 10241447) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 40965790 := by rw [fermat_23]; decide
      have fermat_25 : (19 : ZMod 40965791) ^ 40965790 = 1 := by
        calc
          (19 : ZMod 40965791) ^ 40965790 = (19 : ZMod 40965791) ^ (20482895 + 20482895) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 20482895 * (19 : ZMod 40965791) ^ 20482895 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (4096579, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (4096579, 1)] : List FactorBlock).map factorBlockValue).prod = 40965791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (19 : ZMod 40965791) ^ 1 = 19 := by norm_num
      have factor_0_1 : (19 : ZMod 40965791) ^ 2 = 361 := by
        calc
          (19 : ZMod 40965791) ^ 2 = (19 : ZMod 40965791) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 1 * (19 : ZMod 40965791) ^ 1 := by rw [pow_add]
          _ = 361 := by rw [factor_0_0]; decide
      have factor_0_2 : (19 : ZMod 40965791) ^ 4 = 130321 := by
        calc
          (19 : ZMod 40965791) ^ 4 = (19 : ZMod 40965791) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 2 * (19 : ZMod 40965791) ^ 2 := by rw [pow_add]
          _ = 130321 := by rw [factor_0_1]; decide
      have factor_0_3 : (19 : ZMod 40965791) ^ 9 = 162072 := by
        calc
          (19 : ZMod 40965791) ^ 9 = (19 : ZMod 40965791) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 4 * (19 : ZMod 40965791) ^ 4) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 162072 := by rw [factor_0_2]; decide
      have factor_0_4 : (19 : ZMod 40965791) ^ 19 = 34064534 := by
        calc
          (19 : ZMod 40965791) ^ 19 = (19 : ZMod 40965791) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 9 * (19 : ZMod 40965791) ^ 9) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 34064534 := by rw [factor_0_3]; decide
      have factor_0_5 : (19 : ZMod 40965791) ^ 39 = 39915691 := by
        calc
          (19 : ZMod 40965791) ^ 39 = (19 : ZMod 40965791) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 19 * (19 : ZMod 40965791) ^ 19) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 39915691 := by rw [factor_0_4]; decide
      have factor_0_6 : (19 : ZMod 40965791) ^ 78 = 33813653 := by
        calc
          (19 : ZMod 40965791) ^ 78 = (19 : ZMod 40965791) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 39 * (19 : ZMod 40965791) ^ 39 := by rw [pow_add]
          _ = 33813653 := by rw [factor_0_5]; decide
      have factor_0_7 : (19 : ZMod 40965791) ^ 156 = 36962537 := by
        calc
          (19 : ZMod 40965791) ^ 156 = (19 : ZMod 40965791) ^ (78 + 78) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 78 * (19 : ZMod 40965791) ^ 78 := by rw [pow_add]
          _ = 36962537 := by rw [factor_0_6]; decide
      have factor_0_8 : (19 : ZMod 40965791) ^ 312 = 20320361 := by
        calc
          (19 : ZMod 40965791) ^ 312 = (19 : ZMod 40965791) ^ (156 + 156) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 156 * (19 : ZMod 40965791) ^ 156 := by rw [pow_add]
          _ = 20320361 := by rw [factor_0_7]; decide
      have factor_0_9 : (19 : ZMod 40965791) ^ 625 = 8697335 := by
        calc
          (19 : ZMod 40965791) ^ 625 = (19 : ZMod 40965791) ^ (312 + 312 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 312 * (19 : ZMod 40965791) ^ 312) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 8697335 := by rw [factor_0_8]; decide
      have factor_0_10 : (19 : ZMod 40965791) ^ 1250 = 16260188 := by
        calc
          (19 : ZMod 40965791) ^ 1250 = (19 : ZMod 40965791) ^ (625 + 625) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 625 * (19 : ZMod 40965791) ^ 625 := by rw [pow_add]
          _ = 16260188 := by rw [factor_0_9]; decide
      have factor_0_11 : (19 : ZMod 40965791) ^ 2500 = 7091852 := by
        calc
          (19 : ZMod 40965791) ^ 2500 = (19 : ZMod 40965791) ^ (1250 + 1250) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 1250 * (19 : ZMod 40965791) ^ 1250 := by rw [pow_add]
          _ = 7091852 := by rw [factor_0_10]; decide
      have factor_0_12 : (19 : ZMod 40965791) ^ 5000 = 7726548 := by
        calc
          (19 : ZMod 40965791) ^ 5000 = (19 : ZMod 40965791) ^ (2500 + 2500) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 2500 * (19 : ZMod 40965791) ^ 2500 := by rw [pow_add]
          _ = 7726548 := by rw [factor_0_11]; decide
      have factor_0_13 : (19 : ZMod 40965791) ^ 10001 = 36173272 := by
        calc
          (19 : ZMod 40965791) ^ 10001 = (19 : ZMod 40965791) ^ (5000 + 5000 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 5000 * (19 : ZMod 40965791) ^ 5000) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 36173272 := by rw [factor_0_12]; decide
      have factor_0_14 : (19 : ZMod 40965791) ^ 20002 = 30256973 := by
        calc
          (19 : ZMod 40965791) ^ 20002 = (19 : ZMod 40965791) ^ (10001 + 10001) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 10001 * (19 : ZMod 40965791) ^ 10001 := by rw [pow_add]
          _ = 30256973 := by rw [factor_0_13]; decide
      have factor_0_15 : (19 : ZMod 40965791) ^ 40005 = 27455992 := by
        calc
          (19 : ZMod 40965791) ^ 40005 = (19 : ZMod 40965791) ^ (20002 + 20002 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 20002 * (19 : ZMod 40965791) ^ 20002) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 27455992 := by rw [factor_0_14]; decide
      have factor_0_16 : (19 : ZMod 40965791) ^ 80011 = 5694601 := by
        calc
          (19 : ZMod 40965791) ^ 80011 = (19 : ZMod 40965791) ^ (40005 + 40005 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 40005 * (19 : ZMod 40965791) ^ 40005) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 5694601 := by rw [factor_0_15]; decide
      have factor_0_17 : (19 : ZMod 40965791) ^ 160022 = 1359392 := by
        calc
          (19 : ZMod 40965791) ^ 160022 = (19 : ZMod 40965791) ^ (80011 + 80011) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 80011 * (19 : ZMod 40965791) ^ 80011 := by rw [pow_add]
          _ = 1359392 := by rw [factor_0_16]; decide
      have factor_0_18 : (19 : ZMod 40965791) ^ 320045 = 25433336 := by
        calc
          (19 : ZMod 40965791) ^ 320045 = (19 : ZMod 40965791) ^ (160022 + 160022 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 160022 * (19 : ZMod 40965791) ^ 160022) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 25433336 := by rw [factor_0_17]; decide
      have factor_0_19 : (19 : ZMod 40965791) ^ 640090 = 29132931 := by
        calc
          (19 : ZMod 40965791) ^ 640090 = (19 : ZMod 40965791) ^ (320045 + 320045) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 320045 * (19 : ZMod 40965791) ^ 320045 := by rw [pow_add]
          _ = 29132931 := by rw [factor_0_18]; decide
      have factor_0_20 : (19 : ZMod 40965791) ^ 1280180 = 8378610 := by
        calc
          (19 : ZMod 40965791) ^ 1280180 = (19 : ZMod 40965791) ^ (640090 + 640090) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 640090 * (19 : ZMod 40965791) ^ 640090 := by rw [pow_add]
          _ = 8378610 := by rw [factor_0_19]; decide
      have factor_0_21 : (19 : ZMod 40965791) ^ 2560361 = 3145574 := by
        calc
          (19 : ZMod 40965791) ^ 2560361 = (19 : ZMod 40965791) ^ (1280180 + 1280180 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 1280180 * (19 : ZMod 40965791) ^ 1280180) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 3145574 := by rw [factor_0_20]; decide
      have factor_0_22 : (19 : ZMod 40965791) ^ 5120723 = 2163976 := by
        calc
          (19 : ZMod 40965791) ^ 5120723 = (19 : ZMod 40965791) ^ (2560361 + 2560361 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 2560361 * (19 : ZMod 40965791) ^ 2560361) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 2163976 := by rw [factor_0_21]; decide
      have factor_0_23 : (19 : ZMod 40965791) ^ 10241447 = 22491118 := by
        calc
          (19 : ZMod 40965791) ^ 10241447 = (19 : ZMod 40965791) ^ (5120723 + 5120723 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 5120723 * (19 : ZMod 40965791) ^ 5120723) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 22491118 := by rw [factor_0_22]; decide
      have factor_0_24 : (19 : ZMod 40965791) ^ 20482895 = 40965790 := by
        calc
          (19 : ZMod 40965791) ^ 20482895 = (19 : ZMod 40965791) ^ (10241447 + 10241447 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 10241447 * (19 : ZMod 40965791) ^ 10241447) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 40965790 := by rw [factor_0_23]; decide
      change (19 : ZMod 40965791) ^ 20482895 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (19 : ZMod 40965791) ^ 1 = 19 := by norm_num
      have factor_1_1 : (19 : ZMod 40965791) ^ 3 = 6859 := by
        calc
          (19 : ZMod 40965791) ^ 3 = (19 : ZMod 40965791) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 1 * (19 : ZMod 40965791) ^ 1) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 6859 := by rw [factor_1_0]; decide
      have factor_1_2 : (19 : ZMod 40965791) ^ 7 = 33590128 := by
        calc
          (19 : ZMod 40965791) ^ 7 = (19 : ZMod 40965791) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 3 * (19 : ZMod 40965791) ^ 3) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 33590128 := by rw [factor_1_1]; decide
      have factor_1_3 : (19 : ZMod 40965791) ^ 15 = 21209766 := by
        calc
          (19 : ZMod 40965791) ^ 15 = (19 : ZMod 40965791) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 7 * (19 : ZMod 40965791) ^ 7) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 21209766 := by rw [factor_1_2]; decide
      have factor_1_4 : (19 : ZMod 40965791) ^ 31 = 1254592 := by
        calc
          (19 : ZMod 40965791) ^ 31 = (19 : ZMod 40965791) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 15 * (19 : ZMod 40965791) ^ 15) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 1254592 := by rw [factor_1_3]; decide
      have factor_1_5 : (19 : ZMod 40965791) ^ 62 = 13464662 := by
        calc
          (19 : ZMod 40965791) ^ 62 = (19 : ZMod 40965791) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 31 * (19 : ZMod 40965791) ^ 31 := by rw [pow_add]
          _ = 13464662 := by rw [factor_1_4]; decide
      have factor_1_6 : (19 : ZMod 40965791) ^ 125 = 9195318 := by
        calc
          (19 : ZMod 40965791) ^ 125 = (19 : ZMod 40965791) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 62 * (19 : ZMod 40965791) ^ 62) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 9195318 := by rw [factor_1_5]; decide
      have factor_1_7 : (19 : ZMod 40965791) ^ 250 = 29873423 := by
        calc
          (19 : ZMod 40965791) ^ 250 = (19 : ZMod 40965791) ^ (125 + 125) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 125 * (19 : ZMod 40965791) ^ 125 := by rw [pow_add]
          _ = 29873423 := by rw [factor_1_6]; decide
      have factor_1_8 : (19 : ZMod 40965791) ^ 500 = 38442088 := by
        calc
          (19 : ZMod 40965791) ^ 500 = (19 : ZMod 40965791) ^ (250 + 250) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 250 * (19 : ZMod 40965791) ^ 250 := by rw [pow_add]
          _ = 38442088 := by rw [factor_1_7]; decide
      have factor_1_9 : (19 : ZMod 40965791) ^ 1000 = 2408066 := by
        calc
          (19 : ZMod 40965791) ^ 1000 = (19 : ZMod 40965791) ^ (500 + 500) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 500 * (19 : ZMod 40965791) ^ 500 := by rw [pow_add]
          _ = 2408066 := by rw [factor_1_8]; decide
      have factor_1_10 : (19 : ZMod 40965791) ^ 2000 = 33178515 := by
        calc
          (19 : ZMod 40965791) ^ 2000 = (19 : ZMod 40965791) ^ (1000 + 1000) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 1000 * (19 : ZMod 40965791) ^ 1000 := by rw [pow_add]
          _ = 33178515 := by rw [factor_1_9]; decide
      have factor_1_11 : (19 : ZMod 40965791) ^ 4000 = 7082876 := by
        calc
          (19 : ZMod 40965791) ^ 4000 = (19 : ZMod 40965791) ^ (2000 + 2000) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 2000 * (19 : ZMod 40965791) ^ 2000 := by rw [pow_add]
          _ = 7082876 := by rw [factor_1_10]; decide
      have factor_1_12 : (19 : ZMod 40965791) ^ 8001 = 421917 := by
        calc
          (19 : ZMod 40965791) ^ 8001 = (19 : ZMod 40965791) ^ (4000 + 4000 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 4000 * (19 : ZMod 40965791) ^ 4000) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 421917 := by rw [factor_1_11]; decide
      have factor_1_13 : (19 : ZMod 40965791) ^ 16002 = 17592994 := by
        calc
          (19 : ZMod 40965791) ^ 16002 = (19 : ZMod 40965791) ^ (8001 + 8001) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 8001 * (19 : ZMod 40965791) ^ 8001 := by rw [pow_add]
          _ = 17592994 := by rw [factor_1_12]; decide
      have factor_1_14 : (19 : ZMod 40965791) ^ 32004 = 8973144 := by
        calc
          (19 : ZMod 40965791) ^ 32004 = (19 : ZMod 40965791) ^ (16002 + 16002) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 16002 * (19 : ZMod 40965791) ^ 16002 := by rw [pow_add]
          _ = 8973144 := by rw [factor_1_13]; decide
      have factor_1_15 : (19 : ZMod 40965791) ^ 64009 = 35564315 := by
        calc
          (19 : ZMod 40965791) ^ 64009 = (19 : ZMod 40965791) ^ (32004 + 32004 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 32004 * (19 : ZMod 40965791) ^ 32004) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 35564315 := by rw [factor_1_14]; decide
      have factor_1_16 : (19 : ZMod 40965791) ^ 128018 = 24696794 := by
        calc
          (19 : ZMod 40965791) ^ 128018 = (19 : ZMod 40965791) ^ (64009 + 64009) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 64009 * (19 : ZMod 40965791) ^ 64009 := by rw [pow_add]
          _ = 24696794 := by rw [factor_1_15]; decide
      have factor_1_17 : (19 : ZMod 40965791) ^ 256036 = 974472 := by
        calc
          (19 : ZMod 40965791) ^ 256036 = (19 : ZMod 40965791) ^ (128018 + 128018) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 128018 * (19 : ZMod 40965791) ^ 128018 := by rw [pow_add]
          _ = 974472 := by rw [factor_1_16]; decide
      have factor_1_18 : (19 : ZMod 40965791) ^ 512072 = 8643404 := by
        calc
          (19 : ZMod 40965791) ^ 512072 = (19 : ZMod 40965791) ^ (256036 + 256036) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 256036 * (19 : ZMod 40965791) ^ 256036 := by rw [pow_add]
          _ = 8643404 := by rw [factor_1_17]; decide
      have factor_1_19 : (19 : ZMod 40965791) ^ 1024144 = 20907918 := by
        calc
          (19 : ZMod 40965791) ^ 1024144 = (19 : ZMod 40965791) ^ (512072 + 512072) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 512072 * (19 : ZMod 40965791) ^ 512072 := by rw [pow_add]
          _ = 20907918 := by rw [factor_1_18]; decide
      have factor_1_20 : (19 : ZMod 40965791) ^ 2048289 = 32241609 := by
        calc
          (19 : ZMod 40965791) ^ 2048289 = (19 : ZMod 40965791) ^ (1024144 + 1024144 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 1024144 * (19 : ZMod 40965791) ^ 1024144) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 32241609 := by rw [factor_1_19]; decide
      have factor_1_21 : (19 : ZMod 40965791) ^ 4096579 = 29909859 := by
        calc
          (19 : ZMod 40965791) ^ 4096579 = (19 : ZMod 40965791) ^ (2048289 + 2048289 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 2048289 * (19 : ZMod 40965791) ^ 2048289) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 29909859 := by rw [factor_1_20]; decide
      have factor_1_22 : (19 : ZMod 40965791) ^ 8193158 = 28100197 := by
        calc
          (19 : ZMod 40965791) ^ 8193158 = (19 : ZMod 40965791) ^ (4096579 + 4096579) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 4096579 * (19 : ZMod 40965791) ^ 4096579 := by rw [pow_add]
          _ = 28100197 := by rw [factor_1_21]; decide
      change (19 : ZMod 40965791) ^ 8193158 ≠ 1
      rw [factor_1_22]
      decide
    ·
      have factor_2_0 : (19 : ZMod 40965791) ^ 1 = 19 := by norm_num
      have factor_2_1 : (19 : ZMod 40965791) ^ 2 = 361 := by
        calc
          (19 : ZMod 40965791) ^ 2 = (19 : ZMod 40965791) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 1 * (19 : ZMod 40965791) ^ 1 := by rw [pow_add]
          _ = 361 := by rw [factor_2_0]; decide
      have factor_2_2 : (19 : ZMod 40965791) ^ 5 = 2476099 := by
        calc
          (19 : ZMod 40965791) ^ 5 = (19 : ZMod 40965791) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = ((19 : ZMod 40965791) ^ 2 * (19 : ZMod 40965791) ^ 2) * (19 : ZMod 40965791) := by rw [pow_succ, pow_add]
          _ = 2476099 := by rw [factor_2_1]; decide
      have factor_2_3 : (19 : ZMod 40965791) ^ 10 = 3079368 := by
        calc
          (19 : ZMod 40965791) ^ 10 = (19 : ZMod 40965791) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (19 : ZMod 40965791) ^ n) (by norm_num)
          _ = (19 : ZMod 40965791) ^ 5 * (19 : ZMod 40965791) ^ 5 := by rw [pow_add]
          _ = 3079368 := by rw [factor_2_2]; decide
      change (19 : ZMod 40965791) ^ 10 ≠ 1
      rw [factor_2_3]
      decide

#print axioms prime_lucas_40965791

end TotientTailPeriodKiller
end Erdos249257
