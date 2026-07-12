import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_6790288171 : Nat.Prime 6790288171 := by
  apply lucas_primality 6790288171 (2 : ZMod 6790288171)
  ·
      have fermat_0 : (2 : ZMod 6790288171) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 6790288171) ^ 3 = 8 := by
        calc
          (2 : ZMod 6790288171) ^ 3 = (2 : ZMod 6790288171) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 1 * (2 : ZMod 6790288171) ^ 1) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 6790288171) ^ 6 = 64 := by
        calc
          (2 : ZMod 6790288171) ^ 6 = (2 : ZMod 6790288171) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 3 * (2 : ZMod 6790288171) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 6790288171) ^ 12 = 4096 := by
        calc
          (2 : ZMod 6790288171) ^ 12 = (2 : ZMod 6790288171) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 6 * (2 : ZMod 6790288171) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 6790288171) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 6790288171) ^ 25 = (2 : ZMod 6790288171) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 12 * (2 : ZMod 6790288171) ^ 12) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 6790288171) ^ 50 = 2225209114 := by
        calc
          (2 : ZMod 6790288171) ^ 50 = (2 : ZMod 6790288171) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 25 * (2 : ZMod 6790288171) ^ 25 := by rw [pow_add]
          _ = 2225209114 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 6790288171) ^ 101 = 6256020456 := by
        calc
          (2 : ZMod 6790288171) ^ 101 = (2 : ZMod 6790288171) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 50 * (2 : ZMod 6790288171) ^ 50) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 6256020456 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 6790288171) ^ 202 = 5504628425 := by
        calc
          (2 : ZMod 6790288171) ^ 202 = (2 : ZMod 6790288171) ^ (101 + 101) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 101 * (2 : ZMod 6790288171) ^ 101 := by rw [pow_add]
          _ = 5504628425 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 6790288171) ^ 404 = 627745320 := by
        calc
          (2 : ZMod 6790288171) ^ 404 = (2 : ZMod 6790288171) ^ (202 + 202) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 202 * (2 : ZMod 6790288171) ^ 202 := by rw [pow_add]
          _ = 627745320 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 6790288171) ^ 809 = 3210635971 := by
        calc
          (2 : ZMod 6790288171) ^ 809 = (2 : ZMod 6790288171) ^ (404 + 404 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 404 * (2 : ZMod 6790288171) ^ 404) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 3210635971 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 6790288171) ^ 1618 = 462845233 := by
        calc
          (2 : ZMod 6790288171) ^ 1618 = (2 : ZMod 6790288171) ^ (809 + 809) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 809 * (2 : ZMod 6790288171) ^ 809 := by rw [pow_add]
          _ = 462845233 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 6790288171) ^ 3237 = 2880681640 := by
        calc
          (2 : ZMod 6790288171) ^ 3237 = (2 : ZMod 6790288171) ^ (1618 + 1618 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 1618 * (2 : ZMod 6790288171) ^ 1618) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 2880681640 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 6790288171) ^ 6475 = 3297097338 := by
        calc
          (2 : ZMod 6790288171) ^ 6475 = (2 : ZMod 6790288171) ^ (3237 + 3237 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 3237 * (2 : ZMod 6790288171) ^ 3237) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 3297097338 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 6790288171) ^ 12951 = 5295464503 := by
        calc
          (2 : ZMod 6790288171) ^ 12951 = (2 : ZMod 6790288171) ^ (6475 + 6475 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 6475 * (2 : ZMod 6790288171) ^ 6475) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 5295464503 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 6790288171) ^ 25902 = 1652183282 := by
        calc
          (2 : ZMod 6790288171) ^ 25902 = (2 : ZMod 6790288171) ^ (12951 + 12951) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 12951 * (2 : ZMod 6790288171) ^ 12951 := by rw [pow_add]
          _ = 1652183282 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 6790288171) ^ 51805 = 4489490498 := by
        calc
          (2 : ZMod 6790288171) ^ 51805 = (2 : ZMod 6790288171) ^ (25902 + 25902 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 25902 * (2 : ZMod 6790288171) ^ 25902) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 4489490498 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 6790288171) ^ 103611 = 4758396455 := by
        calc
          (2 : ZMod 6790288171) ^ 103611 = (2 : ZMod 6790288171) ^ (51805 + 51805 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 51805 * (2 : ZMod 6790288171) ^ 51805) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 4758396455 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 6790288171) ^ 207223 = 4191212056 := by
        calc
          (2 : ZMod 6790288171) ^ 207223 = (2 : ZMod 6790288171) ^ (103611 + 103611 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 103611 * (2 : ZMod 6790288171) ^ 103611) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 4191212056 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 6790288171) ^ 414446 = 4012115954 := by
        calc
          (2 : ZMod 6790288171) ^ 414446 = (2 : ZMod 6790288171) ^ (207223 + 207223) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 207223 * (2 : ZMod 6790288171) ^ 207223 := by rw [pow_add]
          _ = 4012115954 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 6790288171) ^ 828892 = 2095046750 := by
        calc
          (2 : ZMod 6790288171) ^ 828892 = (2 : ZMod 6790288171) ^ (414446 + 414446) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 414446 * (2 : ZMod 6790288171) ^ 414446 := by rw [pow_add]
          _ = 2095046750 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 6790288171) ^ 1657785 = 717802300 := by
        calc
          (2 : ZMod 6790288171) ^ 1657785 = (2 : ZMod 6790288171) ^ (828892 + 828892 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 828892 * (2 : ZMod 6790288171) ^ 828892) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 717802300 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 6790288171) ^ 3315570 = 1563744420 := by
        calc
          (2 : ZMod 6790288171) ^ 3315570 = (2 : ZMod 6790288171) ^ (1657785 + 1657785) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 1657785 * (2 : ZMod 6790288171) ^ 1657785 := by rw [pow_add]
          _ = 1563744420 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 6790288171) ^ 6631140 = 1522849585 := by
        calc
          (2 : ZMod 6790288171) ^ 6631140 = (2 : ZMod 6790288171) ^ (3315570 + 3315570) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 3315570 * (2 : ZMod 6790288171) ^ 3315570 := by rw [pow_add]
          _ = 1522849585 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 6790288171) ^ 13262281 = 4466423540 := by
        calc
          (2 : ZMod 6790288171) ^ 13262281 = (2 : ZMod 6790288171) ^ (6631140 + 6631140 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 6631140 * (2 : ZMod 6790288171) ^ 6631140) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 4466423540 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 6790288171) ^ 26524563 = 6072477218 := by
        calc
          (2 : ZMod 6790288171) ^ 26524563 = (2 : ZMod 6790288171) ^ (13262281 + 13262281 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 13262281 * (2 : ZMod 6790288171) ^ 13262281) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 6072477218 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 6790288171) ^ 53049126 = 4488157870 := by
        calc
          (2 : ZMod 6790288171) ^ 53049126 = (2 : ZMod 6790288171) ^ (26524563 + 26524563) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 26524563 * (2 : ZMod 6790288171) ^ 26524563 := by rw [pow_add]
          _ = 4488157870 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 6790288171) ^ 106098252 = 3235781477 := by
        calc
          (2 : ZMod 6790288171) ^ 106098252 = (2 : ZMod 6790288171) ^ (53049126 + 53049126) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 53049126 * (2 : ZMod 6790288171) ^ 53049126 := by rw [pow_add]
          _ = 3235781477 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 6790288171) ^ 212196505 = 2037074155 := by
        calc
          (2 : ZMod 6790288171) ^ 212196505 = (2 : ZMod 6790288171) ^ (106098252 + 106098252 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 106098252 * (2 : ZMod 6790288171) ^ 106098252) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 2037074155 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 6790288171) ^ 424393010 = 4293274778 := by
        calc
          (2 : ZMod 6790288171) ^ 424393010 = (2 : ZMod 6790288171) ^ (212196505 + 212196505) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 212196505 * (2 : ZMod 6790288171) ^ 212196505 := by rw [pow_add]
          _ = 4293274778 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 6790288171) ^ 848786021 = 4927827317 := by
        calc
          (2 : ZMod 6790288171) ^ 848786021 = (2 : ZMod 6790288171) ^ (424393010 + 424393010 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 424393010 * (2 : ZMod 6790288171) ^ 424393010) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 4927827317 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 6790288171) ^ 1697572042 = 1570431009 := by
        calc
          (2 : ZMod 6790288171) ^ 1697572042 = (2 : ZMod 6790288171) ^ (848786021 + 848786021) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 848786021 * (2 : ZMod 6790288171) ^ 848786021 := by rw [pow_add]
          _ = 1570431009 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 6790288171) ^ 3395144085 = 6790288170 := by
        calc
          (2 : ZMod 6790288171) ^ 3395144085 = (2 : ZMod 6790288171) ^ (1697572042 + 1697572042 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 1697572042 * (2 : ZMod 6790288171) ^ 1697572042) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 6790288170 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 6790288171) ^ 6790288170 = 1 := by
        calc
          (2 : ZMod 6790288171) ^ 6790288170 = (2 : ZMod 6790288171) ^ (3395144085 + 3395144085) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 3395144085 * (2 : ZMod 6790288171) ^ 3395144085 := by rw [pow_add]
          _ = 1 := by rw [fermat_31]; decide
      simpa using fermat_32
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (59, 1), (3836321, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (59, 1), (3836321, 1)] : List FactorBlock).map factorBlockValue).prod = 6790288171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 6790288171) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 6790288171) ^ 3 = 8 := by
        calc
          (2 : ZMod 6790288171) ^ 3 = (2 : ZMod 6790288171) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 1 * (2 : ZMod 6790288171) ^ 1) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 6790288171) ^ 6 = 64 := by
        calc
          (2 : ZMod 6790288171) ^ 6 = (2 : ZMod 6790288171) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 3 * (2 : ZMod 6790288171) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 6790288171) ^ 12 = 4096 := by
        calc
          (2 : ZMod 6790288171) ^ 12 = (2 : ZMod 6790288171) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 6 * (2 : ZMod 6790288171) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 6790288171) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 6790288171) ^ 25 = (2 : ZMod 6790288171) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 12 * (2 : ZMod 6790288171) ^ 12) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 6790288171) ^ 50 = 2225209114 := by
        calc
          (2 : ZMod 6790288171) ^ 50 = (2 : ZMod 6790288171) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 25 * (2 : ZMod 6790288171) ^ 25 := by rw [pow_add]
          _ = 2225209114 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 6790288171) ^ 101 = 6256020456 := by
        calc
          (2 : ZMod 6790288171) ^ 101 = (2 : ZMod 6790288171) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 50 * (2 : ZMod 6790288171) ^ 50) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 6256020456 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 6790288171) ^ 202 = 5504628425 := by
        calc
          (2 : ZMod 6790288171) ^ 202 = (2 : ZMod 6790288171) ^ (101 + 101) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 101 * (2 : ZMod 6790288171) ^ 101 := by rw [pow_add]
          _ = 5504628425 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 6790288171) ^ 404 = 627745320 := by
        calc
          (2 : ZMod 6790288171) ^ 404 = (2 : ZMod 6790288171) ^ (202 + 202) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 202 * (2 : ZMod 6790288171) ^ 202 := by rw [pow_add]
          _ = 627745320 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 6790288171) ^ 809 = 3210635971 := by
        calc
          (2 : ZMod 6790288171) ^ 809 = (2 : ZMod 6790288171) ^ (404 + 404 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 404 * (2 : ZMod 6790288171) ^ 404) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 3210635971 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 6790288171) ^ 1618 = 462845233 := by
        calc
          (2 : ZMod 6790288171) ^ 1618 = (2 : ZMod 6790288171) ^ (809 + 809) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 809 * (2 : ZMod 6790288171) ^ 809 := by rw [pow_add]
          _ = 462845233 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 6790288171) ^ 3237 = 2880681640 := by
        calc
          (2 : ZMod 6790288171) ^ 3237 = (2 : ZMod 6790288171) ^ (1618 + 1618 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 1618 * (2 : ZMod 6790288171) ^ 1618) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 2880681640 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 6790288171) ^ 6475 = 3297097338 := by
        calc
          (2 : ZMod 6790288171) ^ 6475 = (2 : ZMod 6790288171) ^ (3237 + 3237 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 3237 * (2 : ZMod 6790288171) ^ 3237) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 3297097338 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 6790288171) ^ 12951 = 5295464503 := by
        calc
          (2 : ZMod 6790288171) ^ 12951 = (2 : ZMod 6790288171) ^ (6475 + 6475 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 6475 * (2 : ZMod 6790288171) ^ 6475) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 5295464503 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 6790288171) ^ 25902 = 1652183282 := by
        calc
          (2 : ZMod 6790288171) ^ 25902 = (2 : ZMod 6790288171) ^ (12951 + 12951) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 12951 * (2 : ZMod 6790288171) ^ 12951 := by rw [pow_add]
          _ = 1652183282 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 6790288171) ^ 51805 = 4489490498 := by
        calc
          (2 : ZMod 6790288171) ^ 51805 = (2 : ZMod 6790288171) ^ (25902 + 25902 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 25902 * (2 : ZMod 6790288171) ^ 25902) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 4489490498 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 6790288171) ^ 103611 = 4758396455 := by
        calc
          (2 : ZMod 6790288171) ^ 103611 = (2 : ZMod 6790288171) ^ (51805 + 51805 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 51805 * (2 : ZMod 6790288171) ^ 51805) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 4758396455 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 6790288171) ^ 207223 = 4191212056 := by
        calc
          (2 : ZMod 6790288171) ^ 207223 = (2 : ZMod 6790288171) ^ (103611 + 103611 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 103611 * (2 : ZMod 6790288171) ^ 103611) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 4191212056 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 6790288171) ^ 414446 = 4012115954 := by
        calc
          (2 : ZMod 6790288171) ^ 414446 = (2 : ZMod 6790288171) ^ (207223 + 207223) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 207223 * (2 : ZMod 6790288171) ^ 207223 := by rw [pow_add]
          _ = 4012115954 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 6790288171) ^ 828892 = 2095046750 := by
        calc
          (2 : ZMod 6790288171) ^ 828892 = (2 : ZMod 6790288171) ^ (414446 + 414446) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 414446 * (2 : ZMod 6790288171) ^ 414446 := by rw [pow_add]
          _ = 2095046750 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 6790288171) ^ 1657785 = 717802300 := by
        calc
          (2 : ZMod 6790288171) ^ 1657785 = (2 : ZMod 6790288171) ^ (828892 + 828892 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 828892 * (2 : ZMod 6790288171) ^ 828892) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 717802300 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 6790288171) ^ 3315570 = 1563744420 := by
        calc
          (2 : ZMod 6790288171) ^ 3315570 = (2 : ZMod 6790288171) ^ (1657785 + 1657785) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 1657785 * (2 : ZMod 6790288171) ^ 1657785 := by rw [pow_add]
          _ = 1563744420 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 6790288171) ^ 6631140 = 1522849585 := by
        calc
          (2 : ZMod 6790288171) ^ 6631140 = (2 : ZMod 6790288171) ^ (3315570 + 3315570) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 3315570 * (2 : ZMod 6790288171) ^ 3315570 := by rw [pow_add]
          _ = 1522849585 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 6790288171) ^ 13262281 = 4466423540 := by
        calc
          (2 : ZMod 6790288171) ^ 13262281 = (2 : ZMod 6790288171) ^ (6631140 + 6631140 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 6631140 * (2 : ZMod 6790288171) ^ 6631140) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 4466423540 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 6790288171) ^ 26524563 = 6072477218 := by
        calc
          (2 : ZMod 6790288171) ^ 26524563 = (2 : ZMod 6790288171) ^ (13262281 + 13262281 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 13262281 * (2 : ZMod 6790288171) ^ 13262281) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 6072477218 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 6790288171) ^ 53049126 = 4488157870 := by
        calc
          (2 : ZMod 6790288171) ^ 53049126 = (2 : ZMod 6790288171) ^ (26524563 + 26524563) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 26524563 * (2 : ZMod 6790288171) ^ 26524563 := by rw [pow_add]
          _ = 4488157870 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 6790288171) ^ 106098252 = 3235781477 := by
        calc
          (2 : ZMod 6790288171) ^ 106098252 = (2 : ZMod 6790288171) ^ (53049126 + 53049126) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 53049126 * (2 : ZMod 6790288171) ^ 53049126 := by rw [pow_add]
          _ = 3235781477 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 6790288171) ^ 212196505 = 2037074155 := by
        calc
          (2 : ZMod 6790288171) ^ 212196505 = (2 : ZMod 6790288171) ^ (106098252 + 106098252 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 106098252 * (2 : ZMod 6790288171) ^ 106098252) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 2037074155 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 6790288171) ^ 424393010 = 4293274778 := by
        calc
          (2 : ZMod 6790288171) ^ 424393010 = (2 : ZMod 6790288171) ^ (212196505 + 212196505) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 212196505 * (2 : ZMod 6790288171) ^ 212196505 := by rw [pow_add]
          _ = 4293274778 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 6790288171) ^ 848786021 = 4927827317 := by
        calc
          (2 : ZMod 6790288171) ^ 848786021 = (2 : ZMod 6790288171) ^ (424393010 + 424393010 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 424393010 * (2 : ZMod 6790288171) ^ 424393010) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 4927827317 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 6790288171) ^ 1697572042 = 1570431009 := by
        calc
          (2 : ZMod 6790288171) ^ 1697572042 = (2 : ZMod 6790288171) ^ (848786021 + 848786021) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 848786021 * (2 : ZMod 6790288171) ^ 848786021 := by rw [pow_add]
          _ = 1570431009 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 6790288171) ^ 3395144085 = 6790288170 := by
        calc
          (2 : ZMod 6790288171) ^ 3395144085 = (2 : ZMod 6790288171) ^ (1697572042 + 1697572042 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 1697572042 * (2 : ZMod 6790288171) ^ 1697572042) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 6790288170 := by rw [factor_0_30]; decide
      change (2 : ZMod 6790288171) ^ 3395144085 ≠ 1
      rw [factor_0_31]
      decide
    ·
      have factor_1_0 : (2 : ZMod 6790288171) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 6790288171) ^ 2 = 4 := by
        calc
          (2 : ZMod 6790288171) ^ 2 = (2 : ZMod 6790288171) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 1 * (2 : ZMod 6790288171) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 6790288171) ^ 4 = 16 := by
        calc
          (2 : ZMod 6790288171) ^ 4 = (2 : ZMod 6790288171) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 2 * (2 : ZMod 6790288171) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 6790288171) ^ 8 = 256 := by
        calc
          (2 : ZMod 6790288171) ^ 8 = (2 : ZMod 6790288171) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 4 * (2 : ZMod 6790288171) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 6790288171) ^ 16 = 65536 := by
        calc
          (2 : ZMod 6790288171) ^ 16 = (2 : ZMod 6790288171) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 8 * (2 : ZMod 6790288171) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 6790288171) ^ 33 = 1799646421 := by
        calc
          (2 : ZMod 6790288171) ^ 33 = (2 : ZMod 6790288171) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 16 * (2 : ZMod 6790288171) ^ 16) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 1799646421 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 6790288171) ^ 67 = 6151469416 := by
        calc
          (2 : ZMod 6790288171) ^ 67 = (2 : ZMod 6790288171) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 33 * (2 : ZMod 6790288171) ^ 33) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 6151469416 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 6790288171) ^ 134 = 1966296274 := by
        calc
          (2 : ZMod 6790288171) ^ 134 = (2 : ZMod 6790288171) ^ (67 + 67) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 67 * (2 : ZMod 6790288171) ^ 67 := by rw [pow_add]
          _ = 1966296274 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 6790288171) ^ 269 = 6038587950 := by
        calc
          (2 : ZMod 6790288171) ^ 269 = (2 : ZMod 6790288171) ^ (134 + 134 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 134 * (2 : ZMod 6790288171) ^ 134) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 6038587950 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 6790288171) ^ 539 = 6455238462 := by
        calc
          (2 : ZMod 6790288171) ^ 539 = (2 : ZMod 6790288171) ^ (269 + 269 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 269 * (2 : ZMod 6790288171) ^ 269) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 6455238462 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 6790288171) ^ 1079 = 928825750 := by
        calc
          (2 : ZMod 6790288171) ^ 1079 = (2 : ZMod 6790288171) ^ (539 + 539 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 539 * (2 : ZMod 6790288171) ^ 539) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 928825750 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 6790288171) ^ 2158 = 5294047547 := by
        calc
          (2 : ZMod 6790288171) ^ 2158 = (2 : ZMod 6790288171) ^ (1079 + 1079) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 1079 * (2 : ZMod 6790288171) ^ 1079 := by rw [pow_add]
          _ = 5294047547 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 6790288171) ^ 4317 = 4506343174 := by
        calc
          (2 : ZMod 6790288171) ^ 4317 = (2 : ZMod 6790288171) ^ (2158 + 2158 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 2158 * (2 : ZMod 6790288171) ^ 2158) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 4506343174 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 6790288171) ^ 8634 = 4667292431 := by
        calc
          (2 : ZMod 6790288171) ^ 8634 = (2 : ZMod 6790288171) ^ (4317 + 4317) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 4317 * (2 : ZMod 6790288171) ^ 4317 := by rw [pow_add]
          _ = 4667292431 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 6790288171) ^ 17268 = 5072226806 := by
        calc
          (2 : ZMod 6790288171) ^ 17268 = (2 : ZMod 6790288171) ^ (8634 + 8634) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 8634 * (2 : ZMod 6790288171) ^ 8634 := by rw [pow_add]
          _ = 5072226806 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 6790288171) ^ 34537 = 2973826476 := by
        calc
          (2 : ZMod 6790288171) ^ 34537 = (2 : ZMod 6790288171) ^ (17268 + 17268 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 17268 * (2 : ZMod 6790288171) ^ 17268) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 2973826476 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 6790288171) ^ 69074 = 1051236732 := by
        calc
          (2 : ZMod 6790288171) ^ 69074 = (2 : ZMod 6790288171) ^ (34537 + 34537) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 34537 * (2 : ZMod 6790288171) ^ 34537 := by rw [pow_add]
          _ = 1051236732 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 6790288171) ^ 138148 = 4415864058 := by
        calc
          (2 : ZMod 6790288171) ^ 138148 = (2 : ZMod 6790288171) ^ (69074 + 69074) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 69074 * (2 : ZMod 6790288171) ^ 69074 := by rw [pow_add]
          _ = 4415864058 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 6790288171) ^ 276297 = 6072737317 := by
        calc
          (2 : ZMod 6790288171) ^ 276297 = (2 : ZMod 6790288171) ^ (138148 + 138148 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 138148 * (2 : ZMod 6790288171) ^ 138148) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 6072737317 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 6790288171) ^ 552595 = 3512609285 := by
        calc
          (2 : ZMod 6790288171) ^ 552595 = (2 : ZMod 6790288171) ^ (276297 + 276297 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 276297 * (2 : ZMod 6790288171) ^ 276297) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 3512609285 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 6790288171) ^ 1105190 = 5519029713 := by
        calc
          (2 : ZMod 6790288171) ^ 1105190 = (2 : ZMod 6790288171) ^ (552595 + 552595) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 552595 * (2 : ZMod 6790288171) ^ 552595 := by rw [pow_add]
          _ = 5519029713 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 6790288171) ^ 2210380 = 3096251048 := by
        calc
          (2 : ZMod 6790288171) ^ 2210380 = (2 : ZMod 6790288171) ^ (1105190 + 1105190) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 1105190 * (2 : ZMod 6790288171) ^ 1105190 := by rw [pow_add]
          _ = 3096251048 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 6790288171) ^ 4420760 = 5325563388 := by
        calc
          (2 : ZMod 6790288171) ^ 4420760 = (2 : ZMod 6790288171) ^ (2210380 + 2210380) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 2210380 * (2 : ZMod 6790288171) ^ 2210380 := by rw [pow_add]
          _ = 5325563388 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 6790288171) ^ 8841521 = 3050255204 := by
        calc
          (2 : ZMod 6790288171) ^ 8841521 = (2 : ZMod 6790288171) ^ (4420760 + 4420760 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 4420760 * (2 : ZMod 6790288171) ^ 4420760) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 3050255204 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 6790288171) ^ 17683042 = 5677166094 := by
        calc
          (2 : ZMod 6790288171) ^ 17683042 = (2 : ZMod 6790288171) ^ (8841521 + 8841521) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 8841521 * (2 : ZMod 6790288171) ^ 8841521 := by rw [pow_add]
          _ = 5677166094 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 6790288171) ^ 35366084 = 1876318994 := by
        calc
          (2 : ZMod 6790288171) ^ 35366084 = (2 : ZMod 6790288171) ^ (17683042 + 17683042) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 17683042 * (2 : ZMod 6790288171) ^ 17683042 := by rw [pow_add]
          _ = 1876318994 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 6790288171) ^ 70732168 = 2756653381 := by
        calc
          (2 : ZMod 6790288171) ^ 70732168 = (2 : ZMod 6790288171) ^ (35366084 + 35366084) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 35366084 * (2 : ZMod 6790288171) ^ 35366084 := by rw [pow_add]
          _ = 2756653381 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 6790288171) ^ 141464336 = 3549768851 := by
        calc
          (2 : ZMod 6790288171) ^ 141464336 = (2 : ZMod 6790288171) ^ (70732168 + 70732168) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 70732168 * (2 : ZMod 6790288171) ^ 70732168 := by rw [pow_add]
          _ = 3549768851 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 6790288171) ^ 282928673 = 2518667293 := by
        calc
          (2 : ZMod 6790288171) ^ 282928673 = (2 : ZMod 6790288171) ^ (141464336 + 141464336 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 141464336 * (2 : ZMod 6790288171) ^ 141464336) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 2518667293 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 6790288171) ^ 565857347 = 947281171 := by
        calc
          (2 : ZMod 6790288171) ^ 565857347 = (2 : ZMod 6790288171) ^ (282928673 + 282928673 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 282928673 * (2 : ZMod 6790288171) ^ 282928673) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 947281171 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 6790288171) ^ 1131714695 = 269604889 := by
        calc
          (2 : ZMod 6790288171) ^ 1131714695 = (2 : ZMod 6790288171) ^ (565857347 + 565857347 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 565857347 * (2 : ZMod 6790288171) ^ 565857347) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 269604889 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 6790288171) ^ 2263429390 = 269604888 := by
        calc
          (2 : ZMod 6790288171) ^ 2263429390 = (2 : ZMod 6790288171) ^ (1131714695 + 1131714695) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 1131714695 * (2 : ZMod 6790288171) ^ 1131714695 := by rw [pow_add]
          _ = 269604888 := by rw [factor_1_30]; decide
      change (2 : ZMod 6790288171) ^ 2263429390 ≠ 1
      rw [factor_1_31]
      decide
    ·
      have factor_2_0 : (2 : ZMod 6790288171) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 6790288171) ^ 2 = 4 := by
        calc
          (2 : ZMod 6790288171) ^ 2 = (2 : ZMod 6790288171) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 1 * (2 : ZMod 6790288171) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 6790288171) ^ 5 = 32 := by
        calc
          (2 : ZMod 6790288171) ^ 5 = (2 : ZMod 6790288171) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 2 * (2 : ZMod 6790288171) ^ 2) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 6790288171) ^ 10 = 1024 := by
        calc
          (2 : ZMod 6790288171) ^ 10 = (2 : ZMod 6790288171) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 5 * (2 : ZMod 6790288171) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 6790288171) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 6790288171) ^ 20 = (2 : ZMod 6790288171) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 10 * (2 : ZMod 6790288171) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 6790288171) ^ 40 = 6275232245 := by
        calc
          (2 : ZMod 6790288171) ^ 40 = (2 : ZMod 6790288171) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 20 * (2 : ZMod 6790288171) ^ 20 := by rw [pow_add]
          _ = 6275232245 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 6790288171) ^ 80 = 2108938881 := by
        calc
          (2 : ZMod 6790288171) ^ 80 = (2 : ZMod 6790288171) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 40 * (2 : ZMod 6790288171) ^ 40 := by rw [pow_add]
          _ = 2108938881 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 6790288171) ^ 161 = 3096887502 := by
        calc
          (2 : ZMod 6790288171) ^ 161 = (2 : ZMod 6790288171) ^ (80 + 80 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 80 * (2 : ZMod 6790288171) ^ 80) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 3096887502 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 6790288171) ^ 323 = 5769508819 := by
        calc
          (2 : ZMod 6790288171) ^ 323 = (2 : ZMod 6790288171) ^ (161 + 161 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 161 * (2 : ZMod 6790288171) ^ 161) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 5769508819 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 6790288171) ^ 647 = 1856725972 := by
        calc
          (2 : ZMod 6790288171) ^ 647 = (2 : ZMod 6790288171) ^ (323 + 323 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 323 * (2 : ZMod 6790288171) ^ 323) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 1856725972 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 6790288171) ^ 1295 = 772963310 := by
        calc
          (2 : ZMod 6790288171) ^ 1295 = (2 : ZMod 6790288171) ^ (647 + 647 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 647 * (2 : ZMod 6790288171) ^ 647) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 772963310 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 6790288171) ^ 2590 = 3429740573 := by
        calc
          (2 : ZMod 6790288171) ^ 2590 = (2 : ZMod 6790288171) ^ (1295 + 1295) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 1295 * (2 : ZMod 6790288171) ^ 1295 := by rw [pow_add]
          _ = 3429740573 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 6790288171) ^ 5180 = 1339295700 := by
        calc
          (2 : ZMod 6790288171) ^ 5180 = (2 : ZMod 6790288171) ^ (2590 + 2590) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 2590 * (2 : ZMod 6790288171) ^ 2590 := by rw [pow_add]
          _ = 1339295700 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 6790288171) ^ 10361 = 5445173194 := by
        calc
          (2 : ZMod 6790288171) ^ 10361 = (2 : ZMod 6790288171) ^ (5180 + 5180 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 5180 * (2 : ZMod 6790288171) ^ 5180) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 5445173194 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 6790288171) ^ 20722 = 2484894786 := by
        calc
          (2 : ZMod 6790288171) ^ 20722 = (2 : ZMod 6790288171) ^ (10361 + 10361) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 10361 * (2 : ZMod 6790288171) ^ 10361 := by rw [pow_add]
          _ = 2484894786 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 6790288171) ^ 41444 = 1552513607 := by
        calc
          (2 : ZMod 6790288171) ^ 41444 = (2 : ZMod 6790288171) ^ (20722 + 20722) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 20722 * (2 : ZMod 6790288171) ^ 20722 := by rw [pow_add]
          _ = 1552513607 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 6790288171) ^ 82889 = 6422524003 := by
        calc
          (2 : ZMod 6790288171) ^ 82889 = (2 : ZMod 6790288171) ^ (41444 + 41444 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 41444 * (2 : ZMod 6790288171) ^ 41444) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 6422524003 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 6790288171) ^ 165778 = 2450203920 := by
        calc
          (2 : ZMod 6790288171) ^ 165778 = (2 : ZMod 6790288171) ^ (82889 + 82889) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 82889 * (2 : ZMod 6790288171) ^ 82889 := by rw [pow_add]
          _ = 2450203920 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 6790288171) ^ 331557 = 174135709 := by
        calc
          (2 : ZMod 6790288171) ^ 331557 = (2 : ZMod 6790288171) ^ (165778 + 165778 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 165778 * (2 : ZMod 6790288171) ^ 165778) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 174135709 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 6790288171) ^ 663114 = 4650037743 := by
        calc
          (2 : ZMod 6790288171) ^ 663114 = (2 : ZMod 6790288171) ^ (331557 + 331557) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 331557 * (2 : ZMod 6790288171) ^ 331557 := by rw [pow_add]
          _ = 4650037743 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 6790288171) ^ 1326228 = 3175742246 := by
        calc
          (2 : ZMod 6790288171) ^ 1326228 = (2 : ZMod 6790288171) ^ (663114 + 663114) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 663114 * (2 : ZMod 6790288171) ^ 663114 := by rw [pow_add]
          _ = 3175742246 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 6790288171) ^ 2652456 = 1194756283 := by
        calc
          (2 : ZMod 6790288171) ^ 2652456 = (2 : ZMod 6790288171) ^ (1326228 + 1326228) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 1326228 * (2 : ZMod 6790288171) ^ 1326228 := by rw [pow_add]
          _ = 1194756283 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 6790288171) ^ 5304912 = 4771485458 := by
        calc
          (2 : ZMod 6790288171) ^ 5304912 = (2 : ZMod 6790288171) ^ (2652456 + 2652456) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 2652456 * (2 : ZMod 6790288171) ^ 2652456 := by rw [pow_add]
          _ = 4771485458 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 6790288171) ^ 10609825 = 3596300901 := by
        calc
          (2 : ZMod 6790288171) ^ 10609825 = (2 : ZMod 6790288171) ^ (5304912 + 5304912 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 5304912 * (2 : ZMod 6790288171) ^ 5304912) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 3596300901 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 6790288171) ^ 21219650 = 5557561615 := by
        calc
          (2 : ZMod 6790288171) ^ 21219650 = (2 : ZMod 6790288171) ^ (10609825 + 10609825) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 10609825 * (2 : ZMod 6790288171) ^ 10609825 := by rw [pow_add]
          _ = 5557561615 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 6790288171) ^ 42439301 = 2016503799 := by
        calc
          (2 : ZMod 6790288171) ^ 42439301 = (2 : ZMod 6790288171) ^ (21219650 + 21219650 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 21219650 * (2 : ZMod 6790288171) ^ 21219650) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 2016503799 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 6790288171) ^ 84878602 = 6354905058 := by
        calc
          (2 : ZMod 6790288171) ^ 84878602 = (2 : ZMod 6790288171) ^ (42439301 + 42439301) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 42439301 * (2 : ZMod 6790288171) ^ 42439301 := by rw [pow_add]
          _ = 6354905058 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 6790288171) ^ 169757204 = 3201371446 := by
        calc
          (2 : ZMod 6790288171) ^ 169757204 = (2 : ZMod 6790288171) ^ (84878602 + 84878602) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 84878602 * (2 : ZMod 6790288171) ^ 84878602 := by rw [pow_add]
          _ = 3201371446 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 6790288171) ^ 339514408 = 2015056905 := by
        calc
          (2 : ZMod 6790288171) ^ 339514408 = (2 : ZMod 6790288171) ^ (169757204 + 169757204) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 169757204 * (2 : ZMod 6790288171) ^ 169757204 := by rw [pow_add]
          _ = 2015056905 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 6790288171) ^ 679028817 = 6313356516 := by
        calc
          (2 : ZMod 6790288171) ^ 679028817 = (2 : ZMod 6790288171) ^ (339514408 + 339514408 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 339514408 * (2 : ZMod 6790288171) ^ 339514408) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 6313356516 := by rw [factor_2_28]; decide
      have factor_2_30 : (2 : ZMod 6790288171) ^ 1358057634 = 693036283 := by
        calc
          (2 : ZMod 6790288171) ^ 1358057634 = (2 : ZMod 6790288171) ^ (679028817 + 679028817) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 679028817 * (2 : ZMod 6790288171) ^ 679028817 := by rw [pow_add]
          _ = 693036283 := by rw [factor_2_29]; decide
      change (2 : ZMod 6790288171) ^ 1358057634 ≠ 1
      rw [factor_2_30]
      decide
    ·
      have factor_3_0 : (2 : ZMod 6790288171) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 6790288171) ^ 3 = 8 := by
        calc
          (2 : ZMod 6790288171) ^ 3 = (2 : ZMod 6790288171) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 1 * (2 : ZMod 6790288171) ^ 1) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 6790288171) ^ 6 = 64 := by
        calc
          (2 : ZMod 6790288171) ^ 6 = (2 : ZMod 6790288171) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 3 * (2 : ZMod 6790288171) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 6790288171) ^ 13 = 8192 := by
        calc
          (2 : ZMod 6790288171) ^ 13 = (2 : ZMod 6790288171) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 6 * (2 : ZMod 6790288171) ^ 6) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 6790288171) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 6790288171) ^ 27 = (2 : ZMod 6790288171) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 13 * (2 : ZMod 6790288171) ^ 13) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 6790288171) ^ 54 = 1651904969 := by
        calc
          (2 : ZMod 6790288171) ^ 54 = (2 : ZMod 6790288171) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 27 * (2 : ZMod 6790288171) ^ 27 := by rw [pow_add]
          _ = 1651904969 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 6790288171) ^ 109 = 5823516551 := by
        calc
          (2 : ZMod 6790288171) ^ 109 = (2 : ZMod 6790288171) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 54 * (2 : ZMod 6790288171) ^ 54) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 5823516551 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 6790288171) ^ 219 = 587311995 := by
        calc
          (2 : ZMod 6790288171) ^ 219 = (2 : ZMod 6790288171) ^ (109 + 109 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 109 * (2 : ZMod 6790288171) ^ 109) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 587311995 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 6790288171) ^ 439 = 4154023257 := by
        calc
          (2 : ZMod 6790288171) ^ 439 = (2 : ZMod 6790288171) ^ (219 + 219 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 219 * (2 : ZMod 6790288171) ^ 219) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 4154023257 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 6790288171) ^ 878 = 4209078663 := by
        calc
          (2 : ZMod 6790288171) ^ 878 = (2 : ZMod 6790288171) ^ (439 + 439) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 439 * (2 : ZMod 6790288171) ^ 439 := by rw [pow_add]
          _ = 4209078663 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 6790288171) ^ 1756 = 3235001721 := by
        calc
          (2 : ZMod 6790288171) ^ 1756 = (2 : ZMod 6790288171) ^ (878 + 878) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 878 * (2 : ZMod 6790288171) ^ 878 := by rw [pow_add]
          _ = 3235001721 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 6790288171) ^ 3512 = 4660413761 := by
        calc
          (2 : ZMod 6790288171) ^ 3512 = (2 : ZMod 6790288171) ^ (1756 + 1756) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 1756 * (2 : ZMod 6790288171) ^ 1756 := by rw [pow_add]
          _ = 4660413761 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 6790288171) ^ 7024 = 6131420831 := by
        calc
          (2 : ZMod 6790288171) ^ 7024 = (2 : ZMod 6790288171) ^ (3512 + 3512) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 3512 * (2 : ZMod 6790288171) ^ 3512 := by rw [pow_add]
          _ = 6131420831 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 6790288171) ^ 14049 = 214513642 := by
        calc
          (2 : ZMod 6790288171) ^ 14049 = (2 : ZMod 6790288171) ^ (7024 + 7024 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 7024 * (2 : ZMod 6790288171) ^ 7024) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 214513642 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 6790288171) ^ 28098 = 3660703572 := by
        calc
          (2 : ZMod 6790288171) ^ 28098 = (2 : ZMod 6790288171) ^ (14049 + 14049) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 14049 * (2 : ZMod 6790288171) ^ 14049 := by rw [pow_add]
          _ = 3660703572 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 6790288171) ^ 56196 = 1032466393 := by
        calc
          (2 : ZMod 6790288171) ^ 56196 = (2 : ZMod 6790288171) ^ (28098 + 28098) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 28098 * (2 : ZMod 6790288171) ^ 28098 := by rw [pow_add]
          _ = 1032466393 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 6790288171) ^ 112392 = 5798840527 := by
        calc
          (2 : ZMod 6790288171) ^ 112392 = (2 : ZMod 6790288171) ^ (56196 + 56196) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 56196 * (2 : ZMod 6790288171) ^ 56196 := by rw [pow_add]
          _ = 5798840527 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 6790288171) ^ 224784 = 191191706 := by
        calc
          (2 : ZMod 6790288171) ^ 224784 = (2 : ZMod 6790288171) ^ (112392 + 112392) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 112392 * (2 : ZMod 6790288171) ^ 112392 := by rw [pow_add]
          _ = 191191706 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 6790288171) ^ 449568 = 1487635400 := by
        calc
          (2 : ZMod 6790288171) ^ 449568 = (2 : ZMod 6790288171) ^ (224784 + 224784) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 224784 * (2 : ZMod 6790288171) ^ 224784 := by rw [pow_add]
          _ = 1487635400 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 6790288171) ^ 899137 = 3977145549 := by
        calc
          (2 : ZMod 6790288171) ^ 899137 = (2 : ZMod 6790288171) ^ (449568 + 449568 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 449568 * (2 : ZMod 6790288171) ^ 449568) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 3977145549 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 6790288171) ^ 1798275 = 4430703734 := by
        calc
          (2 : ZMod 6790288171) ^ 1798275 = (2 : ZMod 6790288171) ^ (899137 + 899137 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 899137 * (2 : ZMod 6790288171) ^ 899137) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 4430703734 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 6790288171) ^ 3596550 = 65595361 := by
        calc
          (2 : ZMod 6790288171) ^ 3596550 = (2 : ZMod 6790288171) ^ (1798275 + 1798275) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 1798275 * (2 : ZMod 6790288171) ^ 1798275 := by rw [pow_add]
          _ = 65595361 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 6790288171) ^ 7193101 = 813128067 := by
        calc
          (2 : ZMod 6790288171) ^ 7193101 = (2 : ZMod 6790288171) ^ (3596550 + 3596550 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 3596550 * (2 : ZMod 6790288171) ^ 3596550) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 813128067 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 6790288171) ^ 14386203 = 3980785848 := by
        calc
          (2 : ZMod 6790288171) ^ 14386203 = (2 : ZMod 6790288171) ^ (7193101 + 7193101 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 7193101 * (2 : ZMod 6790288171) ^ 7193101) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 3980785848 := by rw [factor_3_22]; decide
      have factor_3_24 : (2 : ZMod 6790288171) ^ 28772407 = 3349220406 := by
        calc
          (2 : ZMod 6790288171) ^ 28772407 = (2 : ZMod 6790288171) ^ (14386203 + 14386203 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 14386203 * (2 : ZMod 6790288171) ^ 14386203) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 3349220406 := by rw [factor_3_23]; decide
      have factor_3_25 : (2 : ZMod 6790288171) ^ 57544815 = 1237584259 := by
        calc
          (2 : ZMod 6790288171) ^ 57544815 = (2 : ZMod 6790288171) ^ (28772407 + 28772407 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 28772407 * (2 : ZMod 6790288171) ^ 28772407) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 1237584259 := by rw [factor_3_24]; decide
      have factor_3_26 : (2 : ZMod 6790288171) ^ 115089630 = 5744476745 := by
        calc
          (2 : ZMod 6790288171) ^ 115089630 = (2 : ZMod 6790288171) ^ (57544815 + 57544815) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 57544815 * (2 : ZMod 6790288171) ^ 57544815 := by rw [pow_add]
          _ = 5744476745 := by rw [factor_3_25]; decide
      change (2 : ZMod 6790288171) ^ 115089630 ≠ 1
      rw [factor_3_26]
      decide
    ·
      have factor_4_0 : (2 : ZMod 6790288171) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 6790288171) ^ 3 = 8 := by
        calc
          (2 : ZMod 6790288171) ^ 3 = (2 : ZMod 6790288171) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 1 * (2 : ZMod 6790288171) ^ 1) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 6790288171) ^ 6 = 64 := by
        calc
          (2 : ZMod 6790288171) ^ 6 = (2 : ZMod 6790288171) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 3 * (2 : ZMod 6790288171) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 6790288171) ^ 13 = 8192 := by
        calc
          (2 : ZMod 6790288171) ^ 13 = (2 : ZMod 6790288171) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 6 * (2 : ZMod 6790288171) ^ 6) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 6790288171) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 6790288171) ^ 27 = (2 : ZMod 6790288171) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 13 * (2 : ZMod 6790288171) ^ 13) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 6790288171) ^ 55 = 3303809938 := by
        calc
          (2 : ZMod 6790288171) ^ 55 = (2 : ZMod 6790288171) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 27 * (2 : ZMod 6790288171) ^ 27) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 3303809938 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 6790288171) ^ 110 = 4856744931 := by
        calc
          (2 : ZMod 6790288171) ^ 110 = (2 : ZMod 6790288171) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 55 * (2 : ZMod 6790288171) ^ 55 := by rw [pow_add]
          _ = 4856744931 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 6790288171) ^ 221 = 2349247980 := by
        calc
          (2 : ZMod 6790288171) ^ 221 = (2 : ZMod 6790288171) ^ (110 + 110 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 110 * (2 : ZMod 6790288171) ^ 110) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 2349247980 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 6790288171) ^ 442 = 6071033372 := by
        calc
          (2 : ZMod 6790288171) ^ 442 = (2 : ZMod 6790288171) ^ (221 + 221) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 221 * (2 : ZMod 6790288171) ^ 221 := by rw [pow_add]
          _ = 6071033372 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 6790288171) ^ 885 = 2329303355 := by
        calc
          (2 : ZMod 6790288171) ^ 885 = (2 : ZMod 6790288171) ^ (442 + 442 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = ((2 : ZMod 6790288171) ^ 442 * (2 : ZMod 6790288171) ^ 442) * (2 : ZMod 6790288171) := by rw [pow_succ, pow_add]
          _ = 2329303355 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 6790288171) ^ 1770 = 4069022209 := by
        calc
          (2 : ZMod 6790288171) ^ 1770 = (2 : ZMod 6790288171) ^ (885 + 885) :=
            congrArg (fun n : ℕ => (2 : ZMod 6790288171) ^ n) (by norm_num)
          _ = (2 : ZMod 6790288171) ^ 885 * (2 : ZMod 6790288171) ^ 885 := by rw [pow_add]
          _ = 4069022209 := by rw [factor_4_9]; decide
      change (2 : ZMod 6790288171) ^ 1770 ≠ 1
      rw [factor_4_10]
      decide

#print axioms prime_lucas_6790288171

end TotientTailPeriodKiller
end Erdos249257
