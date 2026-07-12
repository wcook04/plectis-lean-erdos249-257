import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_49732087 : Nat.Prime 49732087 := by
  apply lucas_primality 49732087 (5 : ZMod 49732087)
  ·
      have fermat_0 : (5 : ZMod 49732087) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 49732087) ^ 2 = 25 := by
        calc
          (5 : ZMod 49732087) ^ 2 = (5 : ZMod 49732087) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 1 * (5 : ZMod 49732087) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 49732087) ^ 5 = 3125 := by
        calc
          (5 : ZMod 49732087) ^ 5 = (5 : ZMod 49732087) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 2 * (5 : ZMod 49732087) ^ 2) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 49732087) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 49732087) ^ 11 = (5 : ZMod 49732087) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 5 * (5 : ZMod 49732087) ^ 5) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 49732087) ^ 23 = 46611822 := by
        calc
          (5 : ZMod 49732087) ^ 23 = (5 : ZMod 49732087) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 11 * (5 : ZMod 49732087) ^ 11) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 46611822 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 49732087) ^ 47 = 14991175 := by
        calc
          (5 : ZMod 49732087) ^ 47 = (5 : ZMod 49732087) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 23 * (5 : ZMod 49732087) ^ 23) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 14991175 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 49732087) ^ 94 = 5294585 := by
        calc
          (5 : ZMod 49732087) ^ 94 = (5 : ZMod 49732087) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 47 * (5 : ZMod 49732087) ^ 47 := by rw [pow_add]
          _ = 5294585 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 49732087) ^ 189 = 27965457 := by
        calc
          (5 : ZMod 49732087) ^ 189 = (5 : ZMod 49732087) ^ (94 + 94 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 94 * (5 : ZMod 49732087) ^ 94) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 27965457 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 49732087) ^ 379 = 35975376 := by
        calc
          (5 : ZMod 49732087) ^ 379 = (5 : ZMod 49732087) ^ (189 + 189 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 189 * (5 : ZMod 49732087) ^ 189) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 35975376 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 49732087) ^ 758 = 45181724 := by
        calc
          (5 : ZMod 49732087) ^ 758 = (5 : ZMod 49732087) ^ (379 + 379) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 379 * (5 : ZMod 49732087) ^ 379 := by rw [pow_add]
          _ = 45181724 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 49732087) ^ 1517 = 40759987 := by
        calc
          (5 : ZMod 49732087) ^ 1517 = (5 : ZMod 49732087) ^ (758 + 758 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 758 * (5 : ZMod 49732087) ^ 758) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 40759987 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 49732087) ^ 3035 = 21703599 := by
        calc
          (5 : ZMod 49732087) ^ 3035 = (5 : ZMod 49732087) ^ (1517 + 1517 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 1517 * (5 : ZMod 49732087) ^ 1517) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 21703599 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 49732087) ^ 6070 = 44417076 := by
        calc
          (5 : ZMod 49732087) ^ 6070 = (5 : ZMod 49732087) ^ (3035 + 3035) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 3035 * (5 : ZMod 49732087) ^ 3035 := by rw [pow_add]
          _ = 44417076 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 49732087) ^ 12141 = 23293381 := by
        calc
          (5 : ZMod 49732087) ^ 12141 = (5 : ZMod 49732087) ^ (6070 + 6070 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 6070 * (5 : ZMod 49732087) ^ 6070) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 23293381 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 49732087) ^ 24283 = 18106220 := by
        calc
          (5 : ZMod 49732087) ^ 24283 = (5 : ZMod 49732087) ^ (12141 + 12141 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 12141 * (5 : ZMod 49732087) ^ 12141) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 18106220 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 49732087) ^ 48566 = 41882225 := by
        calc
          (5 : ZMod 49732087) ^ 48566 = (5 : ZMod 49732087) ^ (24283 + 24283) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 24283 * (5 : ZMod 49732087) ^ 24283 := by rw [pow_add]
          _ = 41882225 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 49732087) ^ 97132 = 39682129 := by
        calc
          (5 : ZMod 49732087) ^ 97132 = (5 : ZMod 49732087) ^ (48566 + 48566) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 48566 * (5 : ZMod 49732087) ^ 48566 := by rw [pow_add]
          _ = 39682129 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 49732087) ^ 194265 = 21928708 := by
        calc
          (5 : ZMod 49732087) ^ 194265 = (5 : ZMod 49732087) ^ (97132 + 97132 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 97132 * (5 : ZMod 49732087) ^ 97132) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 21928708 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 49732087) ^ 388531 = 10619369 := by
        calc
          (5 : ZMod 49732087) ^ 388531 = (5 : ZMod 49732087) ^ (194265 + 194265 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 194265 * (5 : ZMod 49732087) ^ 194265) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 10619369 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 49732087) ^ 777063 = 47197855 := by
        calc
          (5 : ZMod 49732087) ^ 777063 = (5 : ZMod 49732087) ^ (388531 + 388531 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 388531 * (5 : ZMod 49732087) ^ 388531) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 47197855 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 49732087) ^ 1554127 = 48429916 := by
        calc
          (5 : ZMod 49732087) ^ 1554127 = (5 : ZMod 49732087) ^ (777063 + 777063 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 777063 * (5 : ZMod 49732087) ^ 777063) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 48429916 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 49732087) ^ 3108255 = 19838619 := by
        calc
          (5 : ZMod 49732087) ^ 3108255 = (5 : ZMod 49732087) ^ (1554127 + 1554127 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 1554127 * (5 : ZMod 49732087) ^ 1554127) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 19838619 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 49732087) ^ 6216510 = 19084821 := by
        calc
          (5 : ZMod 49732087) ^ 6216510 = (5 : ZMod 49732087) ^ (3108255 + 3108255) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 3108255 * (5 : ZMod 49732087) ^ 3108255 := by rw [pow_add]
          _ = 19084821 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 49732087) ^ 12433021 = 37207107 := by
        calc
          (5 : ZMod 49732087) ^ 12433021 = (5 : ZMod 49732087) ^ (6216510 + 6216510 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 6216510 * (5 : ZMod 49732087) ^ 6216510) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 37207107 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 49732087) ^ 24866043 = 49732086 := by
        calc
          (5 : ZMod 49732087) ^ 24866043 = (5 : ZMod 49732087) ^ (12433021 + 12433021 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 12433021 * (5 : ZMod 49732087) ^ 12433021) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 49732086 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 49732087) ^ 49732086 = 1 := by
        calc
          (5 : ZMod 49732087) ^ 49732086 = (5 : ZMod 49732087) ^ (24866043 + 24866043) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 24866043 * (5 : ZMod 49732087) ^ 24866043 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (8288681, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (8288681, 1)] : List FactorBlock).map factorBlockValue).prod = 49732087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 49732087) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 49732087) ^ 2 = 25 := by
        calc
          (5 : ZMod 49732087) ^ 2 = (5 : ZMod 49732087) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 1 * (5 : ZMod 49732087) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 49732087) ^ 5 = 3125 := by
        calc
          (5 : ZMod 49732087) ^ 5 = (5 : ZMod 49732087) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 2 * (5 : ZMod 49732087) ^ 2) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 49732087) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 49732087) ^ 11 = (5 : ZMod 49732087) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 5 * (5 : ZMod 49732087) ^ 5) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 49732087) ^ 23 = 46611822 := by
        calc
          (5 : ZMod 49732087) ^ 23 = (5 : ZMod 49732087) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 11 * (5 : ZMod 49732087) ^ 11) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 46611822 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 49732087) ^ 47 = 14991175 := by
        calc
          (5 : ZMod 49732087) ^ 47 = (5 : ZMod 49732087) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 23 * (5 : ZMod 49732087) ^ 23) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 14991175 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 49732087) ^ 94 = 5294585 := by
        calc
          (5 : ZMod 49732087) ^ 94 = (5 : ZMod 49732087) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 47 * (5 : ZMod 49732087) ^ 47 := by rw [pow_add]
          _ = 5294585 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 49732087) ^ 189 = 27965457 := by
        calc
          (5 : ZMod 49732087) ^ 189 = (5 : ZMod 49732087) ^ (94 + 94 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 94 * (5 : ZMod 49732087) ^ 94) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 27965457 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 49732087) ^ 379 = 35975376 := by
        calc
          (5 : ZMod 49732087) ^ 379 = (5 : ZMod 49732087) ^ (189 + 189 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 189 * (5 : ZMod 49732087) ^ 189) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 35975376 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 49732087) ^ 758 = 45181724 := by
        calc
          (5 : ZMod 49732087) ^ 758 = (5 : ZMod 49732087) ^ (379 + 379) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 379 * (5 : ZMod 49732087) ^ 379 := by rw [pow_add]
          _ = 45181724 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 49732087) ^ 1517 = 40759987 := by
        calc
          (5 : ZMod 49732087) ^ 1517 = (5 : ZMod 49732087) ^ (758 + 758 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 758 * (5 : ZMod 49732087) ^ 758) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 40759987 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 49732087) ^ 3035 = 21703599 := by
        calc
          (5 : ZMod 49732087) ^ 3035 = (5 : ZMod 49732087) ^ (1517 + 1517 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 1517 * (5 : ZMod 49732087) ^ 1517) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 21703599 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 49732087) ^ 6070 = 44417076 := by
        calc
          (5 : ZMod 49732087) ^ 6070 = (5 : ZMod 49732087) ^ (3035 + 3035) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 3035 * (5 : ZMod 49732087) ^ 3035 := by rw [pow_add]
          _ = 44417076 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 49732087) ^ 12141 = 23293381 := by
        calc
          (5 : ZMod 49732087) ^ 12141 = (5 : ZMod 49732087) ^ (6070 + 6070 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 6070 * (5 : ZMod 49732087) ^ 6070) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 23293381 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 49732087) ^ 24283 = 18106220 := by
        calc
          (5 : ZMod 49732087) ^ 24283 = (5 : ZMod 49732087) ^ (12141 + 12141 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 12141 * (5 : ZMod 49732087) ^ 12141) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 18106220 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 49732087) ^ 48566 = 41882225 := by
        calc
          (5 : ZMod 49732087) ^ 48566 = (5 : ZMod 49732087) ^ (24283 + 24283) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 24283 * (5 : ZMod 49732087) ^ 24283 := by rw [pow_add]
          _ = 41882225 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 49732087) ^ 97132 = 39682129 := by
        calc
          (5 : ZMod 49732087) ^ 97132 = (5 : ZMod 49732087) ^ (48566 + 48566) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 48566 * (5 : ZMod 49732087) ^ 48566 := by rw [pow_add]
          _ = 39682129 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 49732087) ^ 194265 = 21928708 := by
        calc
          (5 : ZMod 49732087) ^ 194265 = (5 : ZMod 49732087) ^ (97132 + 97132 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 97132 * (5 : ZMod 49732087) ^ 97132) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 21928708 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 49732087) ^ 388531 = 10619369 := by
        calc
          (5 : ZMod 49732087) ^ 388531 = (5 : ZMod 49732087) ^ (194265 + 194265 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 194265 * (5 : ZMod 49732087) ^ 194265) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 10619369 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 49732087) ^ 777063 = 47197855 := by
        calc
          (5 : ZMod 49732087) ^ 777063 = (5 : ZMod 49732087) ^ (388531 + 388531 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 388531 * (5 : ZMod 49732087) ^ 388531) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 47197855 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 49732087) ^ 1554127 = 48429916 := by
        calc
          (5 : ZMod 49732087) ^ 1554127 = (5 : ZMod 49732087) ^ (777063 + 777063 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 777063 * (5 : ZMod 49732087) ^ 777063) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 48429916 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 49732087) ^ 3108255 = 19838619 := by
        calc
          (5 : ZMod 49732087) ^ 3108255 = (5 : ZMod 49732087) ^ (1554127 + 1554127 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 1554127 * (5 : ZMod 49732087) ^ 1554127) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 19838619 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 49732087) ^ 6216510 = 19084821 := by
        calc
          (5 : ZMod 49732087) ^ 6216510 = (5 : ZMod 49732087) ^ (3108255 + 3108255) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 3108255 * (5 : ZMod 49732087) ^ 3108255 := by rw [pow_add]
          _ = 19084821 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 49732087) ^ 12433021 = 37207107 := by
        calc
          (5 : ZMod 49732087) ^ 12433021 = (5 : ZMod 49732087) ^ (6216510 + 6216510 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 6216510 * (5 : ZMod 49732087) ^ 6216510) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 37207107 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 49732087) ^ 24866043 = 49732086 := by
        calc
          (5 : ZMod 49732087) ^ 24866043 = (5 : ZMod 49732087) ^ (12433021 + 12433021 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 12433021 * (5 : ZMod 49732087) ^ 12433021) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 49732086 := by rw [factor_0_23]; decide
      change (5 : ZMod 49732087) ^ 24866043 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (5 : ZMod 49732087) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 49732087) ^ 3 = 125 := by
        calc
          (5 : ZMod 49732087) ^ 3 = (5 : ZMod 49732087) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 1 * (5 : ZMod 49732087) ^ 1) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 49732087) ^ 7 = 78125 := by
        calc
          (5 : ZMod 49732087) ^ 7 = (5 : ZMod 49732087) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 3 * (5 : ZMod 49732087) ^ 3) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 49732087) ^ 15 = 31808794 := by
        calc
          (5 : ZMod 49732087) ^ 15 = (5 : ZMod 49732087) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 7 * (5 : ZMod 49732087) ^ 7) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 31808794 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 49732087) ^ 31 = 30204658 := by
        calc
          (5 : ZMod 49732087) ^ 31 = (5 : ZMod 49732087) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 15 * (5 : ZMod 49732087) ^ 15) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 30204658 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 49732087) ^ 63 = 23350315 := by
        calc
          (5 : ZMod 49732087) ^ 63 = (5 : ZMod 49732087) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 31 * (5 : ZMod 49732087) ^ 31) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 23350315 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 49732087) ^ 126 = 21827682 := by
        calc
          (5 : ZMod 49732087) ^ 126 = (5 : ZMod 49732087) ^ (63 + 63) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 63 * (5 : ZMod 49732087) ^ 63 := by rw [pow_add]
          _ = 21827682 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 49732087) ^ 252 = 34924155 := by
        calc
          (5 : ZMod 49732087) ^ 252 = (5 : ZMod 49732087) ^ (126 + 126) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 126 * (5 : ZMod 49732087) ^ 126 := by rw [pow_add]
          _ = 34924155 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 49732087) ^ 505 = 6362963 := by
        calc
          (5 : ZMod 49732087) ^ 505 = (5 : ZMod 49732087) ^ (252 + 252 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 252 * (5 : ZMod 49732087) ^ 252) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 6362963 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 49732087) ^ 1011 = 41279865 := by
        calc
          (5 : ZMod 49732087) ^ 1011 = (5 : ZMod 49732087) ^ (505 + 505 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 505 * (5 : ZMod 49732087) ^ 505) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 41279865 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 49732087) ^ 2023 = 16397703 := by
        calc
          (5 : ZMod 49732087) ^ 2023 = (5 : ZMod 49732087) ^ (1011 + 1011 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 1011 * (5 : ZMod 49732087) ^ 1011) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 16397703 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 49732087) ^ 4047 = 45438466 := by
        calc
          (5 : ZMod 49732087) ^ 4047 = (5 : ZMod 49732087) ^ (2023 + 2023 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 2023 * (5 : ZMod 49732087) ^ 2023) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 45438466 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 49732087) ^ 8094 = 43693698 := by
        calc
          (5 : ZMod 49732087) ^ 8094 = (5 : ZMod 49732087) ^ (4047 + 4047) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 4047 * (5 : ZMod 49732087) ^ 4047 := by rw [pow_add]
          _ = 43693698 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 49732087) ^ 16188 = 17757444 := by
        calc
          (5 : ZMod 49732087) ^ 16188 = (5 : ZMod 49732087) ^ (8094 + 8094) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 8094 * (5 : ZMod 49732087) ^ 8094 := by rw [pow_add]
          _ = 17757444 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 49732087) ^ 32377 = 12879656 := by
        calc
          (5 : ZMod 49732087) ^ 32377 = (5 : ZMod 49732087) ^ (16188 + 16188 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 16188 * (5 : ZMod 49732087) ^ 16188) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 12879656 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 49732087) ^ 64755 = 24436814 := by
        calc
          (5 : ZMod 49732087) ^ 64755 = (5 : ZMod 49732087) ^ (32377 + 32377 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 32377 * (5 : ZMod 49732087) ^ 32377) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 24436814 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 49732087) ^ 129510 = 42746444 := by
        calc
          (5 : ZMod 49732087) ^ 129510 = (5 : ZMod 49732087) ^ (64755 + 64755) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 64755 * (5 : ZMod 49732087) ^ 64755 := by rw [pow_add]
          _ = 42746444 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 49732087) ^ 259021 = 27789062 := by
        calc
          (5 : ZMod 49732087) ^ 259021 = (5 : ZMod 49732087) ^ (129510 + 129510 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 129510 * (5 : ZMod 49732087) ^ 129510) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 27789062 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 49732087) ^ 518042 = 27305677 := by
        calc
          (5 : ZMod 49732087) ^ 518042 = (5 : ZMod 49732087) ^ (259021 + 259021) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 259021 * (5 : ZMod 49732087) ^ 259021 := by rw [pow_add]
          _ = 27305677 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 49732087) ^ 1036085 = 36160964 := by
        calc
          (5 : ZMod 49732087) ^ 1036085 = (5 : ZMod 49732087) ^ (518042 + 518042 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 518042 * (5 : ZMod 49732087) ^ 518042) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 36160964 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 49732087) ^ 2072170 = 5357592 := by
        calc
          (5 : ZMod 49732087) ^ 2072170 = (5 : ZMod 49732087) ^ (1036085 + 1036085) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 1036085 * (5 : ZMod 49732087) ^ 1036085 := by rw [pow_add]
          _ = 5357592 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 49732087) ^ 4144340 = 22848848 := by
        calc
          (5 : ZMod 49732087) ^ 4144340 = (5 : ZMod 49732087) ^ (2072170 + 2072170) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 2072170 * (5 : ZMod 49732087) ^ 2072170 := by rw [pow_add]
          _ = 22848848 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 49732087) ^ 8288681 = 4067423 := by
        calc
          (5 : ZMod 49732087) ^ 8288681 = (5 : ZMod 49732087) ^ (4144340 + 4144340 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 4144340 * (5 : ZMod 49732087) ^ 4144340) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 4067423 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 49732087) ^ 16577362 = 4067422 := by
        calc
          (5 : ZMod 49732087) ^ 16577362 = (5 : ZMod 49732087) ^ (8288681 + 8288681) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 8288681 * (5 : ZMod 49732087) ^ 8288681 := by rw [pow_add]
          _ = 4067422 := by rw [factor_1_22]; decide
      change (5 : ZMod 49732087) ^ 16577362 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (5 : ZMod 49732087) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 49732087) ^ 3 = 125 := by
        calc
          (5 : ZMod 49732087) ^ 3 = (5 : ZMod 49732087) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = ((5 : ZMod 49732087) ^ 1 * (5 : ZMod 49732087) ^ 1) * (5 : ZMod 49732087) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 49732087) ^ 6 = 15625 := by
        calc
          (5 : ZMod 49732087) ^ 6 = (5 : ZMod 49732087) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 49732087) ^ n) (by norm_num)
          _ = (5 : ZMod 49732087) ^ 3 * (5 : ZMod 49732087) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_2_1]; decide
      change (5 : ZMod 49732087) ^ 6 ≠ 1
      rw [factor_2_2]
      decide

#print axioms prime_lucas_49732087

end TotientTailPeriodKiller
end Erdos249257
