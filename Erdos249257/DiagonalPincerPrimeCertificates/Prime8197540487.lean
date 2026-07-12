import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_8197540487 : Nat.Prime 8197540487 := by
  apply lucas_primality 8197540487 (5 : ZMod 8197540487)
  ·
      have fermat_0 : (5 : ZMod 8197540487) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 8197540487) ^ 3 = 125 := by
        calc
          (5 : ZMod 8197540487) ^ 3 = (5 : ZMod 8197540487) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 1 * (5 : ZMod 8197540487) ^ 1) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 8197540487) ^ 7 = 78125 := by
        calc
          (5 : ZMod 8197540487) ^ 7 = (5 : ZMod 8197540487) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 3 * (5 : ZMod 8197540487) ^ 3) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 8197540487) ^ 15 = 5924956664 := by
        calc
          (5 : ZMod 8197540487) ^ 15 = (5 : ZMod 8197540487) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 7 * (5 : ZMod 8197540487) ^ 7) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 5924956664 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 8197540487) ^ 30 = 2174082443 := by
        calc
          (5 : ZMod 8197540487) ^ 30 = (5 : ZMod 8197540487) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 15 * (5 : ZMod 8197540487) ^ 15 := by rw [pow_add]
          _ = 2174082443 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 8197540487) ^ 61 = 6907094997 := by
        calc
          (5 : ZMod 8197540487) ^ 61 = (5 : ZMod 8197540487) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 30 * (5 : ZMod 8197540487) ^ 30) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 6907094997 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 8197540487) ^ 122 = 7686329972 := by
        calc
          (5 : ZMod 8197540487) ^ 122 = (5 : ZMod 8197540487) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 61 * (5 : ZMod 8197540487) ^ 61 := by rw [pow_add]
          _ = 7686329972 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 8197540487) ^ 244 = 1700428502 := by
        calc
          (5 : ZMod 8197540487) ^ 244 = (5 : ZMod 8197540487) ^ (122 + 122) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 122 * (5 : ZMod 8197540487) ^ 122 := by rw [pow_add]
          _ = 1700428502 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 8197540487) ^ 488 = 1222539686 := by
        calc
          (5 : ZMod 8197540487) ^ 488 = (5 : ZMod 8197540487) ^ (244 + 244) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 244 * (5 : ZMod 8197540487) ^ 244 := by rw [pow_add]
          _ = 1222539686 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 8197540487) ^ 977 = 5631624628 := by
        calc
          (5 : ZMod 8197540487) ^ 977 = (5 : ZMod 8197540487) ^ (488 + 488 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 488 * (5 : ZMod 8197540487) ^ 488) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 5631624628 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 8197540487) ^ 1954 = 5400166173 := by
        calc
          (5 : ZMod 8197540487) ^ 1954 = (5 : ZMod 8197540487) ^ (977 + 977) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 977 * (5 : ZMod 8197540487) ^ 977 := by rw [pow_add]
          _ = 5400166173 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 8197540487) ^ 3908 = 805535519 := by
        calc
          (5 : ZMod 8197540487) ^ 3908 = (5 : ZMod 8197540487) ^ (1954 + 1954) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 1954 * (5 : ZMod 8197540487) ^ 1954 := by rw [pow_add]
          _ = 805535519 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 8197540487) ^ 7817 = 7742638744 := by
        calc
          (5 : ZMod 8197540487) ^ 7817 = (5 : ZMod 8197540487) ^ (3908 + 3908 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 3908 * (5 : ZMod 8197540487) ^ 3908) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 7742638744 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 8197540487) ^ 15635 = 2177516032 := by
        calc
          (5 : ZMod 8197540487) ^ 15635 = (5 : ZMod 8197540487) ^ (7817 + 7817 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 7817 * (5 : ZMod 8197540487) ^ 7817) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 2177516032 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 8197540487) ^ 31271 = 3676080930 := by
        calc
          (5 : ZMod 8197540487) ^ 31271 = (5 : ZMod 8197540487) ^ (15635 + 15635 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 15635 * (5 : ZMod 8197540487) ^ 15635) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 3676080930 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 8197540487) ^ 62542 = 2140570269 := by
        calc
          (5 : ZMod 8197540487) ^ 62542 = (5 : ZMod 8197540487) ^ (31271 + 31271) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 31271 * (5 : ZMod 8197540487) ^ 31271 := by rw [pow_add]
          _ = 2140570269 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 8197540487) ^ 125084 = 7263088798 := by
        calc
          (5 : ZMod 8197540487) ^ 125084 = (5 : ZMod 8197540487) ^ (62542 + 62542) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 62542 * (5 : ZMod 8197540487) ^ 62542 := by rw [pow_add]
          _ = 7263088798 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 8197540487) ^ 250169 = 3516793816 := by
        calc
          (5 : ZMod 8197540487) ^ 250169 = (5 : ZMod 8197540487) ^ (125084 + 125084 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 125084 * (5 : ZMod 8197540487) ^ 125084) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 3516793816 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 8197540487) ^ 500338 = 5347201441 := by
        calc
          (5 : ZMod 8197540487) ^ 500338 = (5 : ZMod 8197540487) ^ (250169 + 250169) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 250169 * (5 : ZMod 8197540487) ^ 250169 := by rw [pow_add]
          _ = 5347201441 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 8197540487) ^ 1000676 = 3970863710 := by
        calc
          (5 : ZMod 8197540487) ^ 1000676 = (5 : ZMod 8197540487) ^ (500338 + 500338) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 500338 * (5 : ZMod 8197540487) ^ 500338 := by rw [pow_add]
          _ = 3970863710 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 8197540487) ^ 2001352 = 5885251234 := by
        calc
          (5 : ZMod 8197540487) ^ 2001352 = (5 : ZMod 8197540487) ^ (1000676 + 1000676) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 1000676 * (5 : ZMod 8197540487) ^ 1000676 := by rw [pow_add]
          _ = 5885251234 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 8197540487) ^ 4002705 = 1752432121 := by
        calc
          (5 : ZMod 8197540487) ^ 4002705 = (5 : ZMod 8197540487) ^ (2001352 + 2001352 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 2001352 * (5 : ZMod 8197540487) ^ 2001352) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 1752432121 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 8197540487) ^ 8005410 = 2789928502 := by
        calc
          (5 : ZMod 8197540487) ^ 8005410 = (5 : ZMod 8197540487) ^ (4002705 + 4002705) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 4002705 * (5 : ZMod 8197540487) ^ 4002705 := by rw [pow_add]
          _ = 2789928502 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 8197540487) ^ 16010821 = 4477637691 := by
        calc
          (5 : ZMod 8197540487) ^ 16010821 = (5 : ZMod 8197540487) ^ (8005410 + 8005410 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 8005410 * (5 : ZMod 8197540487) ^ 8005410) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 4477637691 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 8197540487) ^ 32021642 = 4179244926 := by
        calc
          (5 : ZMod 8197540487) ^ 32021642 = (5 : ZMod 8197540487) ^ (16010821 + 16010821) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 16010821 * (5 : ZMod 8197540487) ^ 16010821 := by rw [pow_add]
          _ = 4179244926 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 8197540487) ^ 64043285 = 7717739576 := by
        calc
          (5 : ZMod 8197540487) ^ 64043285 = (5 : ZMod 8197540487) ^ (32021642 + 32021642 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 32021642 * (5 : ZMod 8197540487) ^ 32021642) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 7717739576 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 8197540487) ^ 128086570 = 7912964761 := by
        calc
          (5 : ZMod 8197540487) ^ 128086570 = (5 : ZMod 8197540487) ^ (64043285 + 64043285) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 64043285 * (5 : ZMod 8197540487) ^ 64043285 := by rw [pow_add]
          _ = 7912964761 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 8197540487) ^ 256173140 = 5308163816 := by
        calc
          (5 : ZMod 8197540487) ^ 256173140 = (5 : ZMod 8197540487) ^ (128086570 + 128086570) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 128086570 * (5 : ZMod 8197540487) ^ 128086570 := by rw [pow_add]
          _ = 5308163816 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 8197540487) ^ 512346280 = 7654176201 := by
        calc
          (5 : ZMod 8197540487) ^ 512346280 = (5 : ZMod 8197540487) ^ (256173140 + 256173140) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 256173140 * (5 : ZMod 8197540487) ^ 256173140 := by rw [pow_add]
          _ = 7654176201 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 8197540487) ^ 1024692560 = 5957511663 := by
        calc
          (5 : ZMod 8197540487) ^ 1024692560 = (5 : ZMod 8197540487) ^ (512346280 + 512346280) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 512346280 * (5 : ZMod 8197540487) ^ 512346280 := by rw [pow_add]
          _ = 5957511663 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 8197540487) ^ 2049385121 = 2192578145 := by
        calc
          (5 : ZMod 8197540487) ^ 2049385121 = (5 : ZMod 8197540487) ^ (1024692560 + 1024692560 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 1024692560 * (5 : ZMod 8197540487) ^ 1024692560) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 2192578145 := by rw [fermat_29]; decide
      have fermat_31 : (5 : ZMod 8197540487) ^ 4098770243 = 8197540486 := by
        calc
          (5 : ZMod 8197540487) ^ 4098770243 = (5 : ZMod 8197540487) ^ (2049385121 + 2049385121 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 2049385121 * (5 : ZMod 8197540487) ^ 2049385121) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 8197540486 := by rw [fermat_30]; decide
      have fermat_32 : (5 : ZMod 8197540487) ^ 8197540486 = 1 := by
        calc
          (5 : ZMod 8197540487) ^ 8197540486 = (5 : ZMod 8197540487) ^ (4098770243 + 4098770243) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 4098770243 * (5 : ZMod 8197540487) ^ 4098770243 := by rw [pow_add]
          _ = 1 := by rw [fermat_31]; decide
      simpa using fermat_32
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (10723, 1), (382241, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (10723, 1), (382241, 1)] : List FactorBlock).map factorBlockValue).prod = 8197540487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 8197540487) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 8197540487) ^ 3 = 125 := by
        calc
          (5 : ZMod 8197540487) ^ 3 = (5 : ZMod 8197540487) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 1 * (5 : ZMod 8197540487) ^ 1) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 8197540487) ^ 7 = 78125 := by
        calc
          (5 : ZMod 8197540487) ^ 7 = (5 : ZMod 8197540487) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 3 * (5 : ZMod 8197540487) ^ 3) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 8197540487) ^ 15 = 5924956664 := by
        calc
          (5 : ZMod 8197540487) ^ 15 = (5 : ZMod 8197540487) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 7 * (5 : ZMod 8197540487) ^ 7) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 5924956664 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 8197540487) ^ 30 = 2174082443 := by
        calc
          (5 : ZMod 8197540487) ^ 30 = (5 : ZMod 8197540487) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 15 * (5 : ZMod 8197540487) ^ 15 := by rw [pow_add]
          _ = 2174082443 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 8197540487) ^ 61 = 6907094997 := by
        calc
          (5 : ZMod 8197540487) ^ 61 = (5 : ZMod 8197540487) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 30 * (5 : ZMod 8197540487) ^ 30) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 6907094997 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 8197540487) ^ 122 = 7686329972 := by
        calc
          (5 : ZMod 8197540487) ^ 122 = (5 : ZMod 8197540487) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 61 * (5 : ZMod 8197540487) ^ 61 := by rw [pow_add]
          _ = 7686329972 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 8197540487) ^ 244 = 1700428502 := by
        calc
          (5 : ZMod 8197540487) ^ 244 = (5 : ZMod 8197540487) ^ (122 + 122) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 122 * (5 : ZMod 8197540487) ^ 122 := by rw [pow_add]
          _ = 1700428502 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 8197540487) ^ 488 = 1222539686 := by
        calc
          (5 : ZMod 8197540487) ^ 488 = (5 : ZMod 8197540487) ^ (244 + 244) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 244 * (5 : ZMod 8197540487) ^ 244 := by rw [pow_add]
          _ = 1222539686 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 8197540487) ^ 977 = 5631624628 := by
        calc
          (5 : ZMod 8197540487) ^ 977 = (5 : ZMod 8197540487) ^ (488 + 488 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 488 * (5 : ZMod 8197540487) ^ 488) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 5631624628 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 8197540487) ^ 1954 = 5400166173 := by
        calc
          (5 : ZMod 8197540487) ^ 1954 = (5 : ZMod 8197540487) ^ (977 + 977) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 977 * (5 : ZMod 8197540487) ^ 977 := by rw [pow_add]
          _ = 5400166173 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 8197540487) ^ 3908 = 805535519 := by
        calc
          (5 : ZMod 8197540487) ^ 3908 = (5 : ZMod 8197540487) ^ (1954 + 1954) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 1954 * (5 : ZMod 8197540487) ^ 1954 := by rw [pow_add]
          _ = 805535519 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 8197540487) ^ 7817 = 7742638744 := by
        calc
          (5 : ZMod 8197540487) ^ 7817 = (5 : ZMod 8197540487) ^ (3908 + 3908 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 3908 * (5 : ZMod 8197540487) ^ 3908) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 7742638744 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 8197540487) ^ 15635 = 2177516032 := by
        calc
          (5 : ZMod 8197540487) ^ 15635 = (5 : ZMod 8197540487) ^ (7817 + 7817 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 7817 * (5 : ZMod 8197540487) ^ 7817) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 2177516032 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 8197540487) ^ 31271 = 3676080930 := by
        calc
          (5 : ZMod 8197540487) ^ 31271 = (5 : ZMod 8197540487) ^ (15635 + 15635 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 15635 * (5 : ZMod 8197540487) ^ 15635) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 3676080930 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 8197540487) ^ 62542 = 2140570269 := by
        calc
          (5 : ZMod 8197540487) ^ 62542 = (5 : ZMod 8197540487) ^ (31271 + 31271) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 31271 * (5 : ZMod 8197540487) ^ 31271 := by rw [pow_add]
          _ = 2140570269 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 8197540487) ^ 125084 = 7263088798 := by
        calc
          (5 : ZMod 8197540487) ^ 125084 = (5 : ZMod 8197540487) ^ (62542 + 62542) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 62542 * (5 : ZMod 8197540487) ^ 62542 := by rw [pow_add]
          _ = 7263088798 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 8197540487) ^ 250169 = 3516793816 := by
        calc
          (5 : ZMod 8197540487) ^ 250169 = (5 : ZMod 8197540487) ^ (125084 + 125084 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 125084 * (5 : ZMod 8197540487) ^ 125084) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 3516793816 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 8197540487) ^ 500338 = 5347201441 := by
        calc
          (5 : ZMod 8197540487) ^ 500338 = (5 : ZMod 8197540487) ^ (250169 + 250169) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 250169 * (5 : ZMod 8197540487) ^ 250169 := by rw [pow_add]
          _ = 5347201441 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 8197540487) ^ 1000676 = 3970863710 := by
        calc
          (5 : ZMod 8197540487) ^ 1000676 = (5 : ZMod 8197540487) ^ (500338 + 500338) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 500338 * (5 : ZMod 8197540487) ^ 500338 := by rw [pow_add]
          _ = 3970863710 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 8197540487) ^ 2001352 = 5885251234 := by
        calc
          (5 : ZMod 8197540487) ^ 2001352 = (5 : ZMod 8197540487) ^ (1000676 + 1000676) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 1000676 * (5 : ZMod 8197540487) ^ 1000676 := by rw [pow_add]
          _ = 5885251234 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 8197540487) ^ 4002705 = 1752432121 := by
        calc
          (5 : ZMod 8197540487) ^ 4002705 = (5 : ZMod 8197540487) ^ (2001352 + 2001352 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 2001352 * (5 : ZMod 8197540487) ^ 2001352) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 1752432121 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 8197540487) ^ 8005410 = 2789928502 := by
        calc
          (5 : ZMod 8197540487) ^ 8005410 = (5 : ZMod 8197540487) ^ (4002705 + 4002705) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 4002705 * (5 : ZMod 8197540487) ^ 4002705 := by rw [pow_add]
          _ = 2789928502 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 8197540487) ^ 16010821 = 4477637691 := by
        calc
          (5 : ZMod 8197540487) ^ 16010821 = (5 : ZMod 8197540487) ^ (8005410 + 8005410 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 8005410 * (5 : ZMod 8197540487) ^ 8005410) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 4477637691 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 8197540487) ^ 32021642 = 4179244926 := by
        calc
          (5 : ZMod 8197540487) ^ 32021642 = (5 : ZMod 8197540487) ^ (16010821 + 16010821) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 16010821 * (5 : ZMod 8197540487) ^ 16010821 := by rw [pow_add]
          _ = 4179244926 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 8197540487) ^ 64043285 = 7717739576 := by
        calc
          (5 : ZMod 8197540487) ^ 64043285 = (5 : ZMod 8197540487) ^ (32021642 + 32021642 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 32021642 * (5 : ZMod 8197540487) ^ 32021642) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 7717739576 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 8197540487) ^ 128086570 = 7912964761 := by
        calc
          (5 : ZMod 8197540487) ^ 128086570 = (5 : ZMod 8197540487) ^ (64043285 + 64043285) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 64043285 * (5 : ZMod 8197540487) ^ 64043285 := by rw [pow_add]
          _ = 7912964761 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 8197540487) ^ 256173140 = 5308163816 := by
        calc
          (5 : ZMod 8197540487) ^ 256173140 = (5 : ZMod 8197540487) ^ (128086570 + 128086570) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 128086570 * (5 : ZMod 8197540487) ^ 128086570 := by rw [pow_add]
          _ = 5308163816 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 8197540487) ^ 512346280 = 7654176201 := by
        calc
          (5 : ZMod 8197540487) ^ 512346280 = (5 : ZMod 8197540487) ^ (256173140 + 256173140) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 256173140 * (5 : ZMod 8197540487) ^ 256173140 := by rw [pow_add]
          _ = 7654176201 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 8197540487) ^ 1024692560 = 5957511663 := by
        calc
          (5 : ZMod 8197540487) ^ 1024692560 = (5 : ZMod 8197540487) ^ (512346280 + 512346280) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 512346280 * (5 : ZMod 8197540487) ^ 512346280 := by rw [pow_add]
          _ = 5957511663 := by rw [factor_0_28]; decide
      have factor_0_30 : (5 : ZMod 8197540487) ^ 2049385121 = 2192578145 := by
        calc
          (5 : ZMod 8197540487) ^ 2049385121 = (5 : ZMod 8197540487) ^ (1024692560 + 1024692560 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 1024692560 * (5 : ZMod 8197540487) ^ 1024692560) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 2192578145 := by rw [factor_0_29]; decide
      have factor_0_31 : (5 : ZMod 8197540487) ^ 4098770243 = 8197540486 := by
        calc
          (5 : ZMod 8197540487) ^ 4098770243 = (5 : ZMod 8197540487) ^ (2049385121 + 2049385121 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 2049385121 * (5 : ZMod 8197540487) ^ 2049385121) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 8197540486 := by rw [factor_0_30]; decide
      change (5 : ZMod 8197540487) ^ 4098770243 ≠ 1
      rw [factor_0_31]
      decide
    ·
      have factor_1_0 : (5 : ZMod 8197540487) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 8197540487) ^ 2 = 25 := by
        calc
          (5 : ZMod 8197540487) ^ 2 = (5 : ZMod 8197540487) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 1 * (5 : ZMod 8197540487) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 8197540487) ^ 5 = 3125 := by
        calc
          (5 : ZMod 8197540487) ^ 5 = (5 : ZMod 8197540487) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 2 * (5 : ZMod 8197540487) ^ 2) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 8197540487) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 8197540487) ^ 11 = (5 : ZMod 8197540487) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 5 * (5 : ZMod 8197540487) ^ 5) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 8197540487) ^ 23 = 8196099316 := by
        calc
          (5 : ZMod 8197540487) ^ 23 = (5 : ZMod 8197540487) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 11 * (5 : ZMod 8197540487) ^ 11) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 8196099316 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 8197540487) ^ 46 = 2996108030 := by
        calc
          (5 : ZMod 8197540487) ^ 46 = (5 : ZMod 8197540487) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 23 * (5 : ZMod 8197540487) ^ 23 := by rw [pow_add]
          _ = 2996108030 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 8197540487) ^ 93 = 5821451707 := by
        calc
          (5 : ZMod 8197540487) ^ 93 = (5 : ZMod 8197540487) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 46 * (5 : ZMod 8197540487) ^ 46) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 5821451707 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 8197540487) ^ 186 = 4175493056 := by
        calc
          (5 : ZMod 8197540487) ^ 186 = (5 : ZMod 8197540487) ^ (93 + 93) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 93 * (5 : ZMod 8197540487) ^ 93 := by rw [pow_add]
          _ = 4175493056 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 8197540487) ^ 373 = 2524380810 := by
        calc
          (5 : ZMod 8197540487) ^ 373 = (5 : ZMod 8197540487) ^ (186 + 186 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 186 * (5 : ZMod 8197540487) ^ 186) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 2524380810 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 8197540487) ^ 746 = 1643506712 := by
        calc
          (5 : ZMod 8197540487) ^ 746 = (5 : ZMod 8197540487) ^ (373 + 373) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 373 * (5 : ZMod 8197540487) ^ 373 := by rw [pow_add]
          _ = 1643506712 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 8197540487) ^ 1493 = 7097291734 := by
        calc
          (5 : ZMod 8197540487) ^ 1493 = (5 : ZMod 8197540487) ^ (746 + 746 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 746 * (5 : ZMod 8197540487) ^ 746) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 7097291734 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 8197540487) ^ 2986 = 4916224191 := by
        calc
          (5 : ZMod 8197540487) ^ 2986 = (5 : ZMod 8197540487) ^ (1493 + 1493) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 1493 * (5 : ZMod 8197540487) ^ 1493 := by rw [pow_add]
          _ = 4916224191 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 8197540487) ^ 5972 = 2068211268 := by
        calc
          (5 : ZMod 8197540487) ^ 5972 = (5 : ZMod 8197540487) ^ (2986 + 2986) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 2986 * (5 : ZMod 8197540487) ^ 2986 := by rw [pow_add]
          _ = 2068211268 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 8197540487) ^ 11945 = 5863775392 := by
        calc
          (5 : ZMod 8197540487) ^ 11945 = (5 : ZMod 8197540487) ^ (5972 + 5972 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 5972 * (5 : ZMod 8197540487) ^ 5972) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 5863775392 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 8197540487) ^ 23890 = 2962810118 := by
        calc
          (5 : ZMod 8197540487) ^ 23890 = (5 : ZMod 8197540487) ^ (11945 + 11945) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 11945 * (5 : ZMod 8197540487) ^ 11945 := by rw [pow_add]
          _ = 2962810118 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 8197540487) ^ 47780 = 285755336 := by
        calc
          (5 : ZMod 8197540487) ^ 47780 = (5 : ZMod 8197540487) ^ (23890 + 23890) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 23890 * (5 : ZMod 8197540487) ^ 23890 := by rw [pow_add]
          _ = 285755336 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 8197540487) ^ 95560 = 1384441546 := by
        calc
          (5 : ZMod 8197540487) ^ 95560 = (5 : ZMod 8197540487) ^ (47780 + 47780) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 47780 * (5 : ZMod 8197540487) ^ 47780 := by rw [pow_add]
          _ = 1384441546 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 8197540487) ^ 191120 = 1061339777 := by
        calc
          (5 : ZMod 8197540487) ^ 191120 = (5 : ZMod 8197540487) ^ (95560 + 95560) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 95560 * (5 : ZMod 8197540487) ^ 95560 := by rw [pow_add]
          _ = 1061339777 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 8197540487) ^ 382241 = 747127035 := by
        calc
          (5 : ZMod 8197540487) ^ 382241 = (5 : ZMod 8197540487) ^ (191120 + 191120 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 191120 * (5 : ZMod 8197540487) ^ 191120) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 747127035 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 8197540487) ^ 764482 = 1350921562 := by
        calc
          (5 : ZMod 8197540487) ^ 764482 = (5 : ZMod 8197540487) ^ (382241 + 382241) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 382241 * (5 : ZMod 8197540487) ^ 382241 := by rw [pow_add]
          _ = 1350921562 := by rw [factor_1_18]; decide
      change (5 : ZMod 8197540487) ^ 764482 ≠ 1
      rw [factor_1_19]
      decide
    ·
      have factor_2_0 : (5 : ZMod 8197540487) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 8197540487) ^ 2 = 25 := by
        calc
          (5 : ZMod 8197540487) ^ 2 = (5 : ZMod 8197540487) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 1 * (5 : ZMod 8197540487) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 8197540487) ^ 5 = 3125 := by
        calc
          (5 : ZMod 8197540487) ^ 5 = (5 : ZMod 8197540487) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 2 * (5 : ZMod 8197540487) ^ 2) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 8197540487) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 8197540487) ^ 10 = (5 : ZMod 8197540487) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 5 * (5 : ZMod 8197540487) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 8197540487) ^ 20 = 5443155354 := by
        calc
          (5 : ZMod 8197540487) ^ 20 = (5 : ZMod 8197540487) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 10 * (5 : ZMod 8197540487) ^ 10 := by rw [pow_add]
          _ = 5443155354 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 8197540487) ^ 41 = 7044285541 := by
        calc
          (5 : ZMod 8197540487) ^ 41 = (5 : ZMod 8197540487) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 20 * (5 : ZMod 8197540487) ^ 20) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 7044285541 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 8197540487) ^ 83 = 3518937107 := by
        calc
          (5 : ZMod 8197540487) ^ 83 = (5 : ZMod 8197540487) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 41 * (5 : ZMod 8197540487) ^ 41) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 3518937107 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 8197540487) ^ 167 = 4106649133 := by
        calc
          (5 : ZMod 8197540487) ^ 167 = (5 : ZMod 8197540487) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 83 * (5 : ZMod 8197540487) ^ 83) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 4106649133 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 8197540487) ^ 335 = 3072691892 := by
        calc
          (5 : ZMod 8197540487) ^ 335 = (5 : ZMod 8197540487) ^ (167 + 167 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 167 * (5 : ZMod 8197540487) ^ 167) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 3072691892 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 8197540487) ^ 670 = 2319268950 := by
        calc
          (5 : ZMod 8197540487) ^ 670 = (5 : ZMod 8197540487) ^ (335 + 335) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 335 * (5 : ZMod 8197540487) ^ 335 := by rw [pow_add]
          _ = 2319268950 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 8197540487) ^ 1340 = 6774470402 := by
        calc
          (5 : ZMod 8197540487) ^ 1340 = (5 : ZMod 8197540487) ^ (670 + 670) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 670 * (5 : ZMod 8197540487) ^ 670 := by rw [pow_add]
          _ = 6774470402 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 8197540487) ^ 2680 = 6731128504 := by
        calc
          (5 : ZMod 8197540487) ^ 2680 = (5 : ZMod 8197540487) ^ (1340 + 1340) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 1340 * (5 : ZMod 8197540487) ^ 1340 := by rw [pow_add]
          _ = 6731128504 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 8197540487) ^ 5361 = 6001713244 := by
        calc
          (5 : ZMod 8197540487) ^ 5361 = (5 : ZMod 8197540487) ^ (2680 + 2680 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 2680 * (5 : ZMod 8197540487) ^ 2680) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 6001713244 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 8197540487) ^ 10723 = 7764733096 := by
        calc
          (5 : ZMod 8197540487) ^ 10723 = (5 : ZMod 8197540487) ^ (5361 + 5361 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = ((5 : ZMod 8197540487) ^ 5361 * (5 : ZMod 8197540487) ^ 5361) * (5 : ZMod 8197540487) := by rw [pow_succ, pow_add]
          _ = 7764733096 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 8197540487) ^ 21446 = 2307115758 := by
        calc
          (5 : ZMod 8197540487) ^ 21446 = (5 : ZMod 8197540487) ^ (10723 + 10723) :=
            congrArg (fun n : ℕ => (5 : ZMod 8197540487) ^ n) (by norm_num)
          _ = (5 : ZMod 8197540487) ^ 10723 * (5 : ZMod 8197540487) ^ 10723 := by rw [pow_add]
          _ = 2307115758 := by rw [factor_2_13]; decide
      change (5 : ZMod 8197540487) ^ 21446 ≠ 1
      rw [factor_2_14]
      decide

#print axioms prime_lucas_8197540487

end TotientTailPeriodKiller
end Erdos249257
