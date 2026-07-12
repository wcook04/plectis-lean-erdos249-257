import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_9191096507 : Nat.Prime 9191096507 := by
  apply lucas_primality 9191096507 (2 : ZMod 9191096507)
  ·
      have fermat_0 : (2 : ZMod 9191096507) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 9191096507) ^ 2 = 4 := by
        calc
          (2 : ZMod 9191096507) ^ 2 = (2 : ZMod 9191096507) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 1 * (2 : ZMod 9191096507) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 9191096507) ^ 4 = 16 := by
        calc
          (2 : ZMod 9191096507) ^ 4 = (2 : ZMod 9191096507) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 2 * (2 : ZMod 9191096507) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 9191096507) ^ 8 = 256 := by
        calc
          (2 : ZMod 9191096507) ^ 8 = (2 : ZMod 9191096507) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 4 * (2 : ZMod 9191096507) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 9191096507) ^ 17 = 131072 := by
        calc
          (2 : ZMod 9191096507) ^ 17 = (2 : ZMod 9191096507) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 8 * (2 : ZMod 9191096507) ^ 8) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 9191096507) ^ 34 = 7988772677 := by
        calc
          (2 : ZMod 9191096507) ^ 34 = (2 : ZMod 9191096507) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 17 * (2 : ZMod 9191096507) ^ 17 := by rw [pow_add]
          _ = 7988772677 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 9191096507) ^ 68 = 3478142622 := by
        calc
          (2 : ZMod 9191096507) ^ 68 = (2 : ZMod 9191096507) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 34 * (2 : ZMod 9191096507) ^ 34 := by rw [pow_add]
          _ = 3478142622 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 9191096507) ^ 136 = 6483491934 := by
        calc
          (2 : ZMod 9191096507) ^ 136 = (2 : ZMod 9191096507) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 68 * (2 : ZMod 9191096507) ^ 68 := by rw [pow_add]
          _ = 6483491934 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 9191096507) ^ 273 = 371651678 := by
        calc
          (2 : ZMod 9191096507) ^ 273 = (2 : ZMod 9191096507) ^ (136 + 136 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 136 * (2 : ZMod 9191096507) ^ 136) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 371651678 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 9191096507) ^ 547 = 8367526590 := by
        calc
          (2 : ZMod 9191096507) ^ 547 = (2 : ZMod 9191096507) ^ (273 + 273 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 273 * (2 : ZMod 9191096507) ^ 273) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 8367526590 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 9191096507) ^ 1095 = 735379874 := by
        calc
          (2 : ZMod 9191096507) ^ 1095 = (2 : ZMod 9191096507) ^ (547 + 547 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 547 * (2 : ZMod 9191096507) ^ 547) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 735379874 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 9191096507) ^ 2191 = 2190524070 := by
        calc
          (2 : ZMod 9191096507) ^ 2191 = (2 : ZMod 9191096507) ^ (1095 + 1095 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 1095 * (2 : ZMod 9191096507) ^ 1095) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 2190524070 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 9191096507) ^ 4382 = 2986453942 := by
        calc
          (2 : ZMod 9191096507) ^ 4382 = (2 : ZMod 9191096507) ^ (2191 + 2191) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 2191 * (2 : ZMod 9191096507) ^ 2191 := by rw [pow_add]
          _ = 2986453942 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 9191096507) ^ 8765 = 1100061168 := by
        calc
          (2 : ZMod 9191096507) ^ 8765 = (2 : ZMod 9191096507) ^ (4382 + 4382 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 4382 * (2 : ZMod 9191096507) ^ 4382) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 1100061168 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 9191096507) ^ 17530 = 547432215 := by
        calc
          (2 : ZMod 9191096507) ^ 17530 = (2 : ZMod 9191096507) ^ (8765 + 8765) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 8765 * (2 : ZMod 9191096507) ^ 8765 := by rw [pow_add]
          _ = 547432215 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 9191096507) ^ 35061 = 678252311 := by
        calc
          (2 : ZMod 9191096507) ^ 35061 = (2 : ZMod 9191096507) ^ (17530 + 17530 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 17530 * (2 : ZMod 9191096507) ^ 17530) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 678252311 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 9191096507) ^ 70122 = 6642479226 := by
        calc
          (2 : ZMod 9191096507) ^ 70122 = (2 : ZMod 9191096507) ^ (35061 + 35061) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 35061 * (2 : ZMod 9191096507) ^ 35061 := by rw [pow_add]
          _ = 6642479226 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 9191096507) ^ 140245 = 5718901340 := by
        calc
          (2 : ZMod 9191096507) ^ 140245 = (2 : ZMod 9191096507) ^ (70122 + 70122 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 70122 * (2 : ZMod 9191096507) ^ 70122) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 5718901340 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 9191096507) ^ 280490 = 3922399834 := by
        calc
          (2 : ZMod 9191096507) ^ 280490 = (2 : ZMod 9191096507) ^ (140245 + 140245) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 140245 * (2 : ZMod 9191096507) ^ 140245 := by rw [pow_add]
          _ = 3922399834 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 9191096507) ^ 560980 = 274763213 := by
        calc
          (2 : ZMod 9191096507) ^ 560980 = (2 : ZMod 9191096507) ^ (280490 + 280490) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 280490 * (2 : ZMod 9191096507) ^ 280490 := by rw [pow_add]
          _ = 274763213 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 9191096507) ^ 1121960 = 2090464013 := by
        calc
          (2 : ZMod 9191096507) ^ 1121960 = (2 : ZMod 9191096507) ^ (560980 + 560980) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 560980 * (2 : ZMod 9191096507) ^ 560980 := by rw [pow_add]
          _ = 2090464013 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 9191096507) ^ 2243920 = 6183940414 := by
        calc
          (2 : ZMod 9191096507) ^ 2243920 = (2 : ZMod 9191096507) ^ (1121960 + 1121960) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 1121960 * (2 : ZMod 9191096507) ^ 1121960 := by rw [pow_add]
          _ = 6183940414 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 9191096507) ^ 4487840 = 8868723253 := by
        calc
          (2 : ZMod 9191096507) ^ 4487840 = (2 : ZMod 9191096507) ^ (2243920 + 2243920) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 2243920 * (2 : ZMod 9191096507) ^ 2243920 := by rw [pow_add]
          _ = 8868723253 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 9191096507) ^ 8975680 = 5446696421 := by
        calc
          (2 : ZMod 9191096507) ^ 8975680 = (2 : ZMod 9191096507) ^ (4487840 + 4487840) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 4487840 * (2 : ZMod 9191096507) ^ 4487840 := by rw [pow_add]
          _ = 5446696421 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 9191096507) ^ 17951360 = 4485412825 := by
        calc
          (2 : ZMod 9191096507) ^ 17951360 = (2 : ZMod 9191096507) ^ (8975680 + 8975680) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 8975680 * (2 : ZMod 9191096507) ^ 8975680 := by rw [pow_add]
          _ = 4485412825 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 9191096507) ^ 35902720 = 3159987094 := by
        calc
          (2 : ZMod 9191096507) ^ 35902720 = (2 : ZMod 9191096507) ^ (17951360 + 17951360) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 17951360 * (2 : ZMod 9191096507) ^ 17951360 := by rw [pow_add]
          _ = 3159987094 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 9191096507) ^ 71805441 = 2983558167 := by
        calc
          (2 : ZMod 9191096507) ^ 71805441 = (2 : ZMod 9191096507) ^ (35902720 + 35902720 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 35902720 * (2 : ZMod 9191096507) ^ 35902720) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 2983558167 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 9191096507) ^ 143610882 = 7079099126 := by
        calc
          (2 : ZMod 9191096507) ^ 143610882 = (2 : ZMod 9191096507) ^ (71805441 + 71805441) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 71805441 * (2 : ZMod 9191096507) ^ 71805441 := by rw [pow_add]
          _ = 7079099126 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 9191096507) ^ 287221765 = 5536713945 := by
        calc
          (2 : ZMod 9191096507) ^ 287221765 = (2 : ZMod 9191096507) ^ (143610882 + 143610882 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 143610882 * (2 : ZMod 9191096507) ^ 143610882) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 5536713945 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 9191096507) ^ 574443531 = 4792053677 := by
        calc
          (2 : ZMod 9191096507) ^ 574443531 = (2 : ZMod 9191096507) ^ (287221765 + 287221765 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 287221765 * (2 : ZMod 9191096507) ^ 287221765) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 4792053677 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 9191096507) ^ 1148887063 = 86229517 := by
        calc
          (2 : ZMod 9191096507) ^ 1148887063 = (2 : ZMod 9191096507) ^ (574443531 + 574443531 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 574443531 * (2 : ZMod 9191096507) ^ 574443531) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 86229517 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 9191096507) ^ 2297774126 = 6056662345 := by
        calc
          (2 : ZMod 9191096507) ^ 2297774126 = (2 : ZMod 9191096507) ^ (1148887063 + 1148887063) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 1148887063 * (2 : ZMod 9191096507) ^ 1148887063 := by rw [pow_add]
          _ = 6056662345 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 9191096507) ^ 4595548253 = 9191096506 := by
        calc
          (2 : ZMod 9191096507) ^ 4595548253 = (2 : ZMod 9191096507) ^ (2297774126 + 2297774126 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 2297774126 * (2 : ZMod 9191096507) ^ 2297774126) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 9191096506 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 9191096507) ^ 9191096506 = 1 := by
        calc
          (2 : ZMod 9191096507) ^ 9191096506 = (2 : ZMod 9191096507) ^ (4595548253 + 4595548253) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 4595548253 * (2 : ZMod 9191096507) ^ 4595548253 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7727, 1), (594739, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7727, 1), (594739, 1)] : List FactorBlock).map factorBlockValue).prod = 9191096507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 9191096507) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 9191096507) ^ 2 = 4 := by
        calc
          (2 : ZMod 9191096507) ^ 2 = (2 : ZMod 9191096507) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 1 * (2 : ZMod 9191096507) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 9191096507) ^ 4 = 16 := by
        calc
          (2 : ZMod 9191096507) ^ 4 = (2 : ZMod 9191096507) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 2 * (2 : ZMod 9191096507) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 9191096507) ^ 8 = 256 := by
        calc
          (2 : ZMod 9191096507) ^ 8 = (2 : ZMod 9191096507) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 4 * (2 : ZMod 9191096507) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 9191096507) ^ 17 = 131072 := by
        calc
          (2 : ZMod 9191096507) ^ 17 = (2 : ZMod 9191096507) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 8 * (2 : ZMod 9191096507) ^ 8) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 9191096507) ^ 34 = 7988772677 := by
        calc
          (2 : ZMod 9191096507) ^ 34 = (2 : ZMod 9191096507) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 17 * (2 : ZMod 9191096507) ^ 17 := by rw [pow_add]
          _ = 7988772677 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 9191096507) ^ 68 = 3478142622 := by
        calc
          (2 : ZMod 9191096507) ^ 68 = (2 : ZMod 9191096507) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 34 * (2 : ZMod 9191096507) ^ 34 := by rw [pow_add]
          _ = 3478142622 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 9191096507) ^ 136 = 6483491934 := by
        calc
          (2 : ZMod 9191096507) ^ 136 = (2 : ZMod 9191096507) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 68 * (2 : ZMod 9191096507) ^ 68 := by rw [pow_add]
          _ = 6483491934 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 9191096507) ^ 273 = 371651678 := by
        calc
          (2 : ZMod 9191096507) ^ 273 = (2 : ZMod 9191096507) ^ (136 + 136 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 136 * (2 : ZMod 9191096507) ^ 136) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 371651678 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 9191096507) ^ 547 = 8367526590 := by
        calc
          (2 : ZMod 9191096507) ^ 547 = (2 : ZMod 9191096507) ^ (273 + 273 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 273 * (2 : ZMod 9191096507) ^ 273) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 8367526590 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 9191096507) ^ 1095 = 735379874 := by
        calc
          (2 : ZMod 9191096507) ^ 1095 = (2 : ZMod 9191096507) ^ (547 + 547 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 547 * (2 : ZMod 9191096507) ^ 547) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 735379874 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 9191096507) ^ 2191 = 2190524070 := by
        calc
          (2 : ZMod 9191096507) ^ 2191 = (2 : ZMod 9191096507) ^ (1095 + 1095 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 1095 * (2 : ZMod 9191096507) ^ 1095) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 2190524070 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 9191096507) ^ 4382 = 2986453942 := by
        calc
          (2 : ZMod 9191096507) ^ 4382 = (2 : ZMod 9191096507) ^ (2191 + 2191) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 2191 * (2 : ZMod 9191096507) ^ 2191 := by rw [pow_add]
          _ = 2986453942 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 9191096507) ^ 8765 = 1100061168 := by
        calc
          (2 : ZMod 9191096507) ^ 8765 = (2 : ZMod 9191096507) ^ (4382 + 4382 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 4382 * (2 : ZMod 9191096507) ^ 4382) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 1100061168 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 9191096507) ^ 17530 = 547432215 := by
        calc
          (2 : ZMod 9191096507) ^ 17530 = (2 : ZMod 9191096507) ^ (8765 + 8765) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 8765 * (2 : ZMod 9191096507) ^ 8765 := by rw [pow_add]
          _ = 547432215 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 9191096507) ^ 35061 = 678252311 := by
        calc
          (2 : ZMod 9191096507) ^ 35061 = (2 : ZMod 9191096507) ^ (17530 + 17530 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 17530 * (2 : ZMod 9191096507) ^ 17530) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 678252311 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 9191096507) ^ 70122 = 6642479226 := by
        calc
          (2 : ZMod 9191096507) ^ 70122 = (2 : ZMod 9191096507) ^ (35061 + 35061) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 35061 * (2 : ZMod 9191096507) ^ 35061 := by rw [pow_add]
          _ = 6642479226 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 9191096507) ^ 140245 = 5718901340 := by
        calc
          (2 : ZMod 9191096507) ^ 140245 = (2 : ZMod 9191096507) ^ (70122 + 70122 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 70122 * (2 : ZMod 9191096507) ^ 70122) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 5718901340 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 9191096507) ^ 280490 = 3922399834 := by
        calc
          (2 : ZMod 9191096507) ^ 280490 = (2 : ZMod 9191096507) ^ (140245 + 140245) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 140245 * (2 : ZMod 9191096507) ^ 140245 := by rw [pow_add]
          _ = 3922399834 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 9191096507) ^ 560980 = 274763213 := by
        calc
          (2 : ZMod 9191096507) ^ 560980 = (2 : ZMod 9191096507) ^ (280490 + 280490) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 280490 * (2 : ZMod 9191096507) ^ 280490 := by rw [pow_add]
          _ = 274763213 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 9191096507) ^ 1121960 = 2090464013 := by
        calc
          (2 : ZMod 9191096507) ^ 1121960 = (2 : ZMod 9191096507) ^ (560980 + 560980) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 560980 * (2 : ZMod 9191096507) ^ 560980 := by rw [pow_add]
          _ = 2090464013 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 9191096507) ^ 2243920 = 6183940414 := by
        calc
          (2 : ZMod 9191096507) ^ 2243920 = (2 : ZMod 9191096507) ^ (1121960 + 1121960) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 1121960 * (2 : ZMod 9191096507) ^ 1121960 := by rw [pow_add]
          _ = 6183940414 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 9191096507) ^ 4487840 = 8868723253 := by
        calc
          (2 : ZMod 9191096507) ^ 4487840 = (2 : ZMod 9191096507) ^ (2243920 + 2243920) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 2243920 * (2 : ZMod 9191096507) ^ 2243920 := by rw [pow_add]
          _ = 8868723253 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 9191096507) ^ 8975680 = 5446696421 := by
        calc
          (2 : ZMod 9191096507) ^ 8975680 = (2 : ZMod 9191096507) ^ (4487840 + 4487840) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 4487840 * (2 : ZMod 9191096507) ^ 4487840 := by rw [pow_add]
          _ = 5446696421 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 9191096507) ^ 17951360 = 4485412825 := by
        calc
          (2 : ZMod 9191096507) ^ 17951360 = (2 : ZMod 9191096507) ^ (8975680 + 8975680) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 8975680 * (2 : ZMod 9191096507) ^ 8975680 := by rw [pow_add]
          _ = 4485412825 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 9191096507) ^ 35902720 = 3159987094 := by
        calc
          (2 : ZMod 9191096507) ^ 35902720 = (2 : ZMod 9191096507) ^ (17951360 + 17951360) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 17951360 * (2 : ZMod 9191096507) ^ 17951360 := by rw [pow_add]
          _ = 3159987094 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 9191096507) ^ 71805441 = 2983558167 := by
        calc
          (2 : ZMod 9191096507) ^ 71805441 = (2 : ZMod 9191096507) ^ (35902720 + 35902720 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 35902720 * (2 : ZMod 9191096507) ^ 35902720) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 2983558167 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 9191096507) ^ 143610882 = 7079099126 := by
        calc
          (2 : ZMod 9191096507) ^ 143610882 = (2 : ZMod 9191096507) ^ (71805441 + 71805441) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 71805441 * (2 : ZMod 9191096507) ^ 71805441 := by rw [pow_add]
          _ = 7079099126 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 9191096507) ^ 287221765 = 5536713945 := by
        calc
          (2 : ZMod 9191096507) ^ 287221765 = (2 : ZMod 9191096507) ^ (143610882 + 143610882 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 143610882 * (2 : ZMod 9191096507) ^ 143610882) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 5536713945 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 9191096507) ^ 574443531 = 4792053677 := by
        calc
          (2 : ZMod 9191096507) ^ 574443531 = (2 : ZMod 9191096507) ^ (287221765 + 287221765 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 287221765 * (2 : ZMod 9191096507) ^ 287221765) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 4792053677 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 9191096507) ^ 1148887063 = 86229517 := by
        calc
          (2 : ZMod 9191096507) ^ 1148887063 = (2 : ZMod 9191096507) ^ (574443531 + 574443531 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 574443531 * (2 : ZMod 9191096507) ^ 574443531) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 86229517 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 9191096507) ^ 2297774126 = 6056662345 := by
        calc
          (2 : ZMod 9191096507) ^ 2297774126 = (2 : ZMod 9191096507) ^ (1148887063 + 1148887063) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 1148887063 * (2 : ZMod 9191096507) ^ 1148887063 := by rw [pow_add]
          _ = 6056662345 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 9191096507) ^ 4595548253 = 9191096506 := by
        calc
          (2 : ZMod 9191096507) ^ 4595548253 = (2 : ZMod 9191096507) ^ (2297774126 + 2297774126 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 2297774126 * (2 : ZMod 9191096507) ^ 2297774126) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 9191096506 := by rw [factor_0_31]; decide
      change (2 : ZMod 9191096507) ^ 4595548253 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (2 : ZMod 9191096507) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 9191096507) ^ 2 = 4 := by
        calc
          (2 : ZMod 9191096507) ^ 2 = (2 : ZMod 9191096507) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 1 * (2 : ZMod 9191096507) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 9191096507) ^ 4 = 16 := by
        calc
          (2 : ZMod 9191096507) ^ 4 = (2 : ZMod 9191096507) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 2 * (2 : ZMod 9191096507) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 9191096507) ^ 9 = 512 := by
        calc
          (2 : ZMod 9191096507) ^ 9 = (2 : ZMod 9191096507) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 4 * (2 : ZMod 9191096507) ^ 4) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 9191096507) ^ 18 = 262144 := by
        calc
          (2 : ZMod 9191096507) ^ 18 = (2 : ZMod 9191096507) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 9 * (2 : ZMod 9191096507) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 9191096507) ^ 36 = 4381801187 := by
        calc
          (2 : ZMod 9191096507) ^ 36 = (2 : ZMod 9191096507) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 18 * (2 : ZMod 9191096507) ^ 18 := by rw [pow_add]
          _ = 4381801187 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 9191096507) ^ 72 = 503702910 := by
        calc
          (2 : ZMod 9191096507) ^ 72 = (2 : ZMod 9191096507) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 36 * (2 : ZMod 9191096507) ^ 36 := by rw [pow_add]
          _ = 503702910 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 9191096507) ^ 145 = 1562031181 := by
        calc
          (2 : ZMod 9191096507) ^ 145 = (2 : ZMod 9191096507) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 72 * (2 : ZMod 9191096507) ^ 72) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 1562031181 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 9191096507) ^ 290 = 317251716 := by
        calc
          (2 : ZMod 9191096507) ^ 290 = (2 : ZMod 9191096507) ^ (145 + 145) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 145 * (2 : ZMod 9191096507) ^ 145 := by rw [pow_add]
          _ = 317251716 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 9191096507) ^ 580 = 4900827980 := by
        calc
          (2 : ZMod 9191096507) ^ 580 = (2 : ZMod 9191096507) ^ (290 + 290) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 290 * (2 : ZMod 9191096507) ^ 290 := by rw [pow_add]
          _ = 4900827980 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 9191096507) ^ 1161 = 6766591417 := by
        calc
          (2 : ZMod 9191096507) ^ 1161 = (2 : ZMod 9191096507) ^ (580 + 580 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 580 * (2 : ZMod 9191096507) ^ 580) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 6766591417 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 9191096507) ^ 2323 = 3782781589 := by
        calc
          (2 : ZMod 9191096507) ^ 2323 = (2 : ZMod 9191096507) ^ (1161 + 1161 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 1161 * (2 : ZMod 9191096507) ^ 1161) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 3782781589 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 9191096507) ^ 4646 = 5204946734 := by
        calc
          (2 : ZMod 9191096507) ^ 4646 = (2 : ZMod 9191096507) ^ (2323 + 2323) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 2323 * (2 : ZMod 9191096507) ^ 2323 := by rw [pow_add]
          _ = 5204946734 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 9191096507) ^ 9292 = 7808542318 := by
        calc
          (2 : ZMod 9191096507) ^ 9292 = (2 : ZMod 9191096507) ^ (4646 + 4646) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 4646 * (2 : ZMod 9191096507) ^ 4646 := by rw [pow_add]
          _ = 7808542318 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 9191096507) ^ 18585 = 8020757208 := by
        calc
          (2 : ZMod 9191096507) ^ 18585 = (2 : ZMod 9191096507) ^ (9292 + 9292 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 9292 * (2 : ZMod 9191096507) ^ 9292) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 8020757208 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 9191096507) ^ 37171 = 6454067141 := by
        calc
          (2 : ZMod 9191096507) ^ 37171 = (2 : ZMod 9191096507) ^ (18585 + 18585 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 18585 * (2 : ZMod 9191096507) ^ 18585) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 6454067141 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 9191096507) ^ 74342 = 8490400087 := by
        calc
          (2 : ZMod 9191096507) ^ 74342 = (2 : ZMod 9191096507) ^ (37171 + 37171) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 37171 * (2 : ZMod 9191096507) ^ 37171 := by rw [pow_add]
          _ = 8490400087 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 9191096507) ^ 148684 = 1896372228 := by
        calc
          (2 : ZMod 9191096507) ^ 148684 = (2 : ZMod 9191096507) ^ (74342 + 74342) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 74342 * (2 : ZMod 9191096507) ^ 74342 := by rw [pow_add]
          _ = 1896372228 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 9191096507) ^ 297369 = 7749432895 := by
        calc
          (2 : ZMod 9191096507) ^ 297369 = (2 : ZMod 9191096507) ^ (148684 + 148684 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 148684 * (2 : ZMod 9191096507) ^ 148684) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 7749432895 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 9191096507) ^ 594739 = 5594352854 := by
        calc
          (2 : ZMod 9191096507) ^ 594739 = (2 : ZMod 9191096507) ^ (297369 + 297369 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 297369 * (2 : ZMod 9191096507) ^ 297369) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 5594352854 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 9191096507) ^ 1189478 = 942285360 := by
        calc
          (2 : ZMod 9191096507) ^ 1189478 = (2 : ZMod 9191096507) ^ (594739 + 594739) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 594739 * (2 : ZMod 9191096507) ^ 594739 := by rw [pow_add]
          _ = 942285360 := by rw [factor_1_19]; decide
      change (2 : ZMod 9191096507) ^ 1189478 ≠ 1
      rw [factor_1_20]
      decide
    ·
      have factor_2_0 : (2 : ZMod 9191096507) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 9191096507) ^ 3 = 8 := by
        calc
          (2 : ZMod 9191096507) ^ 3 = (2 : ZMod 9191096507) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 1 * (2 : ZMod 9191096507) ^ 1) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 9191096507) ^ 7 = 128 := by
        calc
          (2 : ZMod 9191096507) ^ 7 = (2 : ZMod 9191096507) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 3 * (2 : ZMod 9191096507) ^ 3) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 9191096507) ^ 15 = 32768 := by
        calc
          (2 : ZMod 9191096507) ^ 15 = (2 : ZMod 9191096507) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 7 * (2 : ZMod 9191096507) ^ 7) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 9191096507) ^ 30 = 1073741824 := by
        calc
          (2 : ZMod 9191096507) ^ 30 = (2 : ZMod 9191096507) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 15 * (2 : ZMod 9191096507) ^ 15 := by rw [pow_add]
          _ = 1073741824 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 9191096507) ^ 60 = 229002819 := by
        calc
          (2 : ZMod 9191096507) ^ 60 = (2 : ZMod 9191096507) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 30 * (2 : ZMod 9191096507) ^ 30 := by rw [pow_add]
          _ = 229002819 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 9191096507) ^ 120 = 8393201371 := by
        calc
          (2 : ZMod 9191096507) ^ 120 = (2 : ZMod 9191096507) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 60 * (2 : ZMod 9191096507) ^ 60 := by rw [pow_add]
          _ = 8393201371 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 9191096507) ^ 241 = 7918970119 := by
        calc
          (2 : ZMod 9191096507) ^ 241 = (2 : ZMod 9191096507) ^ (120 + 120 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 120 * (2 : ZMod 9191096507) ^ 120) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 7918970119 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 9191096507) ^ 482 = 3327026819 := by
        calc
          (2 : ZMod 9191096507) ^ 482 = (2 : ZMod 9191096507) ^ (241 + 241) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 241 * (2 : ZMod 9191096507) ^ 241 := by rw [pow_add]
          _ = 3327026819 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 9191096507) ^ 965 = 4494785863 := by
        calc
          (2 : ZMod 9191096507) ^ 965 = (2 : ZMod 9191096507) ^ (482 + 482 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 482 * (2 : ZMod 9191096507) ^ 482) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 4494785863 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 9191096507) ^ 1931 = 3983769459 := by
        calc
          (2 : ZMod 9191096507) ^ 1931 = (2 : ZMod 9191096507) ^ (965 + 965 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 965 * (2 : ZMod 9191096507) ^ 965) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 3983769459 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 9191096507) ^ 3863 = 6409516175 := by
        calc
          (2 : ZMod 9191096507) ^ 3863 = (2 : ZMod 9191096507) ^ (1931 + 1931 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 1931 * (2 : ZMod 9191096507) ^ 1931) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 6409516175 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 9191096507) ^ 7727 = 1992088913 := by
        calc
          (2 : ZMod 9191096507) ^ 7727 = (2 : ZMod 9191096507) ^ (3863 + 3863 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = ((2 : ZMod 9191096507) ^ 3863 * (2 : ZMod 9191096507) ^ 3863) * (2 : ZMod 9191096507) := by rw [pow_succ, pow_add]
          _ = 1992088913 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 9191096507) ^ 15454 = 5635957949 := by
        calc
          (2 : ZMod 9191096507) ^ 15454 = (2 : ZMod 9191096507) ^ (7727 + 7727) :=
            congrArg (fun n : ℕ => (2 : ZMod 9191096507) ^ n) (by norm_num)
          _ = (2 : ZMod 9191096507) ^ 7727 * (2 : ZMod 9191096507) ^ 7727 := by rw [pow_add]
          _ = 5635957949 := by rw [factor_2_12]; decide
      change (2 : ZMod 9191096507) ^ 15454 ≠ 1
      rw [factor_2_13]
      decide

#print axioms prime_lucas_9191096507

end TotientTailPeriodKiller
end Erdos249257
