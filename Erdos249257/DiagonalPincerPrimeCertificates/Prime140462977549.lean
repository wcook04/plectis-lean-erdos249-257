import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_140462977549 : Nat.Prime 140462977549 := by
  apply lucas_primality 140462977549 (2 : ZMod 140462977549)
  ·
      have fermat_0 : (2 : ZMod 140462977549) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 140462977549) ^ 2 = 4 := by
        calc
          (2 : ZMod 140462977549) ^ 2 = (2 : ZMod 140462977549) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 1 * (2 : ZMod 140462977549) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 140462977549) ^ 4 = 16 := by
        calc
          (2 : ZMod 140462977549) ^ 4 = (2 : ZMod 140462977549) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 2 * (2 : ZMod 140462977549) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 140462977549) ^ 8 = 256 := by
        calc
          (2 : ZMod 140462977549) ^ 8 = (2 : ZMod 140462977549) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 4 * (2 : ZMod 140462977549) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 140462977549) ^ 16 = 65536 := by
        calc
          (2 : ZMod 140462977549) ^ 16 = (2 : ZMod 140462977549) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 8 * (2 : ZMod 140462977549) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 140462977549) ^ 32 = 4294967296 := by
        calc
          (2 : ZMod 140462977549) ^ 32 = (2 : ZMod 140462977549) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 16 * (2 : ZMod 140462977549) ^ 16 := by rw [pow_add]
          _ = 4294967296 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 140462977549) ^ 65 = 70471031297 := by
        calc
          (2 : ZMod 140462977549) ^ 65 = (2 : ZMod 140462977549) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 32 * (2 : ZMod 140462977549) ^ 32) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 70471031297 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 140462977549) ^ 130 = 54011376629 := by
        calc
          (2 : ZMod 140462977549) ^ 130 = (2 : ZMod 140462977549) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 65 * (2 : ZMod 140462977549) ^ 65 := by rw [pow_add]
          _ = 54011376629 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 140462977549) ^ 261 = 19931059615 := by
        calc
          (2 : ZMod 140462977549) ^ 261 = (2 : ZMod 140462977549) ^ (130 + 130 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 130 * (2 : ZMod 140462977549) ^ 130) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 19931059615 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 140462977549) ^ 523 = 72889821822 := by
        calc
          (2 : ZMod 140462977549) ^ 523 = (2 : ZMod 140462977549) ^ (261 + 261 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 261 * (2 : ZMod 140462977549) ^ 261) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 72889821822 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 140462977549) ^ 1046 = 16931438169 := by
        calc
          (2 : ZMod 140462977549) ^ 1046 = (2 : ZMod 140462977549) ^ (523 + 523) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 523 * (2 : ZMod 140462977549) ^ 523 := by rw [pow_add]
          _ = 16931438169 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 140462977549) ^ 2093 = 53121476074 := by
        calc
          (2 : ZMod 140462977549) ^ 2093 = (2 : ZMod 140462977549) ^ (1046 + 1046 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 1046 * (2 : ZMod 140462977549) ^ 1046) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 53121476074 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 140462977549) ^ 4186 = 37738301492 := by
        calc
          (2 : ZMod 140462977549) ^ 4186 = (2 : ZMod 140462977549) ^ (2093 + 2093) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 2093 * (2 : ZMod 140462977549) ^ 2093 := by rw [pow_add]
          _ = 37738301492 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 140462977549) ^ 8372 = 139802473219 := by
        calc
          (2 : ZMod 140462977549) ^ 8372 = (2 : ZMod 140462977549) ^ (4186 + 4186) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 4186 * (2 : ZMod 140462977549) ^ 4186 := by rw [pow_add]
          _ = 139802473219 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 140462977549) ^ 16744 = 41497624114 := by
        calc
          (2 : ZMod 140462977549) ^ 16744 = (2 : ZMod 140462977549) ^ (8372 + 8372) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 8372 * (2 : ZMod 140462977549) ^ 8372 := by rw [pow_add]
          _ = 41497624114 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 140462977549) ^ 33488 = 107402472332 := by
        calc
          (2 : ZMod 140462977549) ^ 33488 = (2 : ZMod 140462977549) ^ (16744 + 16744) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 16744 * (2 : ZMod 140462977549) ^ 16744 := by rw [pow_add]
          _ = 107402472332 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 140462977549) ^ 66977 = 9177106278 := by
        calc
          (2 : ZMod 140462977549) ^ 66977 = (2 : ZMod 140462977549) ^ (33488 + 33488 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 33488 * (2 : ZMod 140462977549) ^ 33488) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 9177106278 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 140462977549) ^ 133955 = 23765041410 := by
        calc
          (2 : ZMod 140462977549) ^ 133955 = (2 : ZMod 140462977549) ^ (66977 + 66977 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 66977 * (2 : ZMod 140462977549) ^ 66977) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 23765041410 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 140462977549) ^ 267911 = 138676942514 := by
        calc
          (2 : ZMod 140462977549) ^ 267911 = (2 : ZMod 140462977549) ^ (133955 + 133955 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 133955 * (2 : ZMod 140462977549) ^ 133955) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 138676942514 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 140462977549) ^ 535823 = 86847522648 := by
        calc
          (2 : ZMod 140462977549) ^ 535823 = (2 : ZMod 140462977549) ^ (267911 + 267911 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 267911 * (2 : ZMod 140462977549) ^ 267911) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 86847522648 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 140462977549) ^ 1071647 = 58927958826 := by
        calc
          (2 : ZMod 140462977549) ^ 1071647 = (2 : ZMod 140462977549) ^ (535823 + 535823 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 535823 * (2 : ZMod 140462977549) ^ 535823) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 58927958826 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 140462977549) ^ 2143294 = 107465865975 := by
        calc
          (2 : ZMod 140462977549) ^ 2143294 = (2 : ZMod 140462977549) ^ (1071647 + 1071647) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 1071647 * (2 : ZMod 140462977549) ^ 1071647 := by rw [pow_add]
          _ = 107465865975 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 140462977549) ^ 4286589 = 63549583206 := by
        calc
          (2 : ZMod 140462977549) ^ 4286589 = (2 : ZMod 140462977549) ^ (2143294 + 2143294 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 2143294 * (2 : ZMod 140462977549) ^ 2143294) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 63549583206 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 140462977549) ^ 8573179 = 118106713380 := by
        calc
          (2 : ZMod 140462977549) ^ 8573179 = (2 : ZMod 140462977549) ^ (4286589 + 4286589 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 4286589 * (2 : ZMod 140462977549) ^ 4286589) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 118106713380 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 140462977549) ^ 17146359 = 121383423617 := by
        calc
          (2 : ZMod 140462977549) ^ 17146359 = (2 : ZMod 140462977549) ^ (8573179 + 8573179 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 8573179 * (2 : ZMod 140462977549) ^ 8573179) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 121383423617 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 140462977549) ^ 34292719 = 50531898575 := by
        calc
          (2 : ZMod 140462977549) ^ 34292719 = (2 : ZMod 140462977549) ^ (17146359 + 17146359 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 17146359 * (2 : ZMod 140462977549) ^ 17146359) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 50531898575 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 140462977549) ^ 68585438 = 30829389717 := by
        calc
          (2 : ZMod 140462977549) ^ 68585438 = (2 : ZMod 140462977549) ^ (34292719 + 34292719) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 34292719 * (2 : ZMod 140462977549) ^ 34292719 := by rw [pow_add]
          _ = 30829389717 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 140462977549) ^ 137170876 = 32859670986 := by
        calc
          (2 : ZMod 140462977549) ^ 137170876 = (2 : ZMod 140462977549) ^ (68585438 + 68585438) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 68585438 * (2 : ZMod 140462977549) ^ 68585438 := by rw [pow_add]
          _ = 32859670986 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 140462977549) ^ 274341753 = 113128185206 := by
        calc
          (2 : ZMod 140462977549) ^ 274341753 = (2 : ZMod 140462977549) ^ (137170876 + 137170876 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 137170876 * (2 : ZMod 140462977549) ^ 137170876) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 113128185206 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 140462977549) ^ 548683506 = 66560375261 := by
        calc
          (2 : ZMod 140462977549) ^ 548683506 = (2 : ZMod 140462977549) ^ (274341753 + 274341753) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 274341753 * (2 : ZMod 140462977549) ^ 274341753 := by rw [pow_add]
          _ = 66560375261 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 140462977549) ^ 1097367012 = 46244341815 := by
        calc
          (2 : ZMod 140462977549) ^ 1097367012 = (2 : ZMod 140462977549) ^ (548683506 + 548683506) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 548683506 * (2 : ZMod 140462977549) ^ 548683506 := by rw [pow_add]
          _ = 46244341815 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 140462977549) ^ 2194734024 = 96241744736 := by
        calc
          (2 : ZMod 140462977549) ^ 2194734024 = (2 : ZMod 140462977549) ^ (1097367012 + 1097367012) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 1097367012 * (2 : ZMod 140462977549) ^ 1097367012 := by rw [pow_add]
          _ = 96241744736 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 140462977549) ^ 4389468048 = 863520754 := by
        calc
          (2 : ZMod 140462977549) ^ 4389468048 = (2 : ZMod 140462977549) ^ (2194734024 + 2194734024) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 2194734024 * (2 : ZMod 140462977549) ^ 2194734024 := by rw [pow_add]
          _ = 863520754 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 140462977549) ^ 8778936096 = 9138117411 := by
        calc
          (2 : ZMod 140462977549) ^ 8778936096 = (2 : ZMod 140462977549) ^ (4389468048 + 4389468048) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 4389468048 * (2 : ZMod 140462977549) ^ 4389468048 := by rw [pow_add]
          _ = 9138117411 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 140462977549) ^ 17557872193 = 40636588475 := by
        calc
          (2 : ZMod 140462977549) ^ 17557872193 = (2 : ZMod 140462977549) ^ (8778936096 + 8778936096 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 8778936096 * (2 : ZMod 140462977549) ^ 8778936096) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 40636588475 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 140462977549) ^ 35115744387 = 81273176949 := by
        calc
          (2 : ZMod 140462977549) ^ 35115744387 = (2 : ZMod 140462977549) ^ (17557872193 + 17557872193 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 17557872193 * (2 : ZMod 140462977549) ^ 17557872193) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 81273176949 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 140462977549) ^ 70231488774 = 140462977548 := by
        calc
          (2 : ZMod 140462977549) ^ 70231488774 = (2 : ZMod 140462977549) ^ (35115744387 + 35115744387) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 35115744387 * (2 : ZMod 140462977549) ^ 35115744387 := by rw [pow_add]
          _ = 140462977548 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 140462977549) ^ 140462977548 = 1 := by
        calc
          (2 : ZMod 140462977549) ^ 140462977548 = (2 : ZMod 140462977549) ^ (70231488774 + 70231488774) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 70231488774 * (2 : ZMod 140462977549) ^ 70231488774 := by rw [pow_add]
          _ = 1 := by rw [fermat_36]; decide
      simpa using fermat_37
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (5557, 1), (110863, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (5557, 1), (110863, 1)] : List FactorBlock).map factorBlockValue).prod = 140462977549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 140462977549) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 140462977549) ^ 2 = 4 := by
        calc
          (2 : ZMod 140462977549) ^ 2 = (2 : ZMod 140462977549) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 1 * (2 : ZMod 140462977549) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 140462977549) ^ 4 = 16 := by
        calc
          (2 : ZMod 140462977549) ^ 4 = (2 : ZMod 140462977549) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 2 * (2 : ZMod 140462977549) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 140462977549) ^ 8 = 256 := by
        calc
          (2 : ZMod 140462977549) ^ 8 = (2 : ZMod 140462977549) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 4 * (2 : ZMod 140462977549) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 140462977549) ^ 16 = 65536 := by
        calc
          (2 : ZMod 140462977549) ^ 16 = (2 : ZMod 140462977549) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 8 * (2 : ZMod 140462977549) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 140462977549) ^ 32 = 4294967296 := by
        calc
          (2 : ZMod 140462977549) ^ 32 = (2 : ZMod 140462977549) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 16 * (2 : ZMod 140462977549) ^ 16 := by rw [pow_add]
          _ = 4294967296 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 140462977549) ^ 65 = 70471031297 := by
        calc
          (2 : ZMod 140462977549) ^ 65 = (2 : ZMod 140462977549) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 32 * (2 : ZMod 140462977549) ^ 32) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 70471031297 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 140462977549) ^ 130 = 54011376629 := by
        calc
          (2 : ZMod 140462977549) ^ 130 = (2 : ZMod 140462977549) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 65 * (2 : ZMod 140462977549) ^ 65 := by rw [pow_add]
          _ = 54011376629 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 140462977549) ^ 261 = 19931059615 := by
        calc
          (2 : ZMod 140462977549) ^ 261 = (2 : ZMod 140462977549) ^ (130 + 130 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 130 * (2 : ZMod 140462977549) ^ 130) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 19931059615 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 140462977549) ^ 523 = 72889821822 := by
        calc
          (2 : ZMod 140462977549) ^ 523 = (2 : ZMod 140462977549) ^ (261 + 261 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 261 * (2 : ZMod 140462977549) ^ 261) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 72889821822 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 140462977549) ^ 1046 = 16931438169 := by
        calc
          (2 : ZMod 140462977549) ^ 1046 = (2 : ZMod 140462977549) ^ (523 + 523) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 523 * (2 : ZMod 140462977549) ^ 523 := by rw [pow_add]
          _ = 16931438169 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 140462977549) ^ 2093 = 53121476074 := by
        calc
          (2 : ZMod 140462977549) ^ 2093 = (2 : ZMod 140462977549) ^ (1046 + 1046 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 1046 * (2 : ZMod 140462977549) ^ 1046) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 53121476074 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 140462977549) ^ 4186 = 37738301492 := by
        calc
          (2 : ZMod 140462977549) ^ 4186 = (2 : ZMod 140462977549) ^ (2093 + 2093) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 2093 * (2 : ZMod 140462977549) ^ 2093 := by rw [pow_add]
          _ = 37738301492 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 140462977549) ^ 8372 = 139802473219 := by
        calc
          (2 : ZMod 140462977549) ^ 8372 = (2 : ZMod 140462977549) ^ (4186 + 4186) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 4186 * (2 : ZMod 140462977549) ^ 4186 := by rw [pow_add]
          _ = 139802473219 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 140462977549) ^ 16744 = 41497624114 := by
        calc
          (2 : ZMod 140462977549) ^ 16744 = (2 : ZMod 140462977549) ^ (8372 + 8372) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 8372 * (2 : ZMod 140462977549) ^ 8372 := by rw [pow_add]
          _ = 41497624114 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 140462977549) ^ 33488 = 107402472332 := by
        calc
          (2 : ZMod 140462977549) ^ 33488 = (2 : ZMod 140462977549) ^ (16744 + 16744) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 16744 * (2 : ZMod 140462977549) ^ 16744 := by rw [pow_add]
          _ = 107402472332 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 140462977549) ^ 66977 = 9177106278 := by
        calc
          (2 : ZMod 140462977549) ^ 66977 = (2 : ZMod 140462977549) ^ (33488 + 33488 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 33488 * (2 : ZMod 140462977549) ^ 33488) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 9177106278 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 140462977549) ^ 133955 = 23765041410 := by
        calc
          (2 : ZMod 140462977549) ^ 133955 = (2 : ZMod 140462977549) ^ (66977 + 66977 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 66977 * (2 : ZMod 140462977549) ^ 66977) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 23765041410 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 140462977549) ^ 267911 = 138676942514 := by
        calc
          (2 : ZMod 140462977549) ^ 267911 = (2 : ZMod 140462977549) ^ (133955 + 133955 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 133955 * (2 : ZMod 140462977549) ^ 133955) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 138676942514 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 140462977549) ^ 535823 = 86847522648 := by
        calc
          (2 : ZMod 140462977549) ^ 535823 = (2 : ZMod 140462977549) ^ (267911 + 267911 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 267911 * (2 : ZMod 140462977549) ^ 267911) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 86847522648 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 140462977549) ^ 1071647 = 58927958826 := by
        calc
          (2 : ZMod 140462977549) ^ 1071647 = (2 : ZMod 140462977549) ^ (535823 + 535823 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 535823 * (2 : ZMod 140462977549) ^ 535823) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 58927958826 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 140462977549) ^ 2143294 = 107465865975 := by
        calc
          (2 : ZMod 140462977549) ^ 2143294 = (2 : ZMod 140462977549) ^ (1071647 + 1071647) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 1071647 * (2 : ZMod 140462977549) ^ 1071647 := by rw [pow_add]
          _ = 107465865975 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 140462977549) ^ 4286589 = 63549583206 := by
        calc
          (2 : ZMod 140462977549) ^ 4286589 = (2 : ZMod 140462977549) ^ (2143294 + 2143294 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 2143294 * (2 : ZMod 140462977549) ^ 2143294) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 63549583206 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 140462977549) ^ 8573179 = 118106713380 := by
        calc
          (2 : ZMod 140462977549) ^ 8573179 = (2 : ZMod 140462977549) ^ (4286589 + 4286589 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 4286589 * (2 : ZMod 140462977549) ^ 4286589) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 118106713380 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 140462977549) ^ 17146359 = 121383423617 := by
        calc
          (2 : ZMod 140462977549) ^ 17146359 = (2 : ZMod 140462977549) ^ (8573179 + 8573179 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 8573179 * (2 : ZMod 140462977549) ^ 8573179) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 121383423617 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 140462977549) ^ 34292719 = 50531898575 := by
        calc
          (2 : ZMod 140462977549) ^ 34292719 = (2 : ZMod 140462977549) ^ (17146359 + 17146359 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 17146359 * (2 : ZMod 140462977549) ^ 17146359) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 50531898575 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 140462977549) ^ 68585438 = 30829389717 := by
        calc
          (2 : ZMod 140462977549) ^ 68585438 = (2 : ZMod 140462977549) ^ (34292719 + 34292719) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 34292719 * (2 : ZMod 140462977549) ^ 34292719 := by rw [pow_add]
          _ = 30829389717 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 140462977549) ^ 137170876 = 32859670986 := by
        calc
          (2 : ZMod 140462977549) ^ 137170876 = (2 : ZMod 140462977549) ^ (68585438 + 68585438) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 68585438 * (2 : ZMod 140462977549) ^ 68585438 := by rw [pow_add]
          _ = 32859670986 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 140462977549) ^ 274341753 = 113128185206 := by
        calc
          (2 : ZMod 140462977549) ^ 274341753 = (2 : ZMod 140462977549) ^ (137170876 + 137170876 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 137170876 * (2 : ZMod 140462977549) ^ 137170876) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 113128185206 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 140462977549) ^ 548683506 = 66560375261 := by
        calc
          (2 : ZMod 140462977549) ^ 548683506 = (2 : ZMod 140462977549) ^ (274341753 + 274341753) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 274341753 * (2 : ZMod 140462977549) ^ 274341753 := by rw [pow_add]
          _ = 66560375261 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 140462977549) ^ 1097367012 = 46244341815 := by
        calc
          (2 : ZMod 140462977549) ^ 1097367012 = (2 : ZMod 140462977549) ^ (548683506 + 548683506) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 548683506 * (2 : ZMod 140462977549) ^ 548683506 := by rw [pow_add]
          _ = 46244341815 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 140462977549) ^ 2194734024 = 96241744736 := by
        calc
          (2 : ZMod 140462977549) ^ 2194734024 = (2 : ZMod 140462977549) ^ (1097367012 + 1097367012) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 1097367012 * (2 : ZMod 140462977549) ^ 1097367012 := by rw [pow_add]
          _ = 96241744736 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 140462977549) ^ 4389468048 = 863520754 := by
        calc
          (2 : ZMod 140462977549) ^ 4389468048 = (2 : ZMod 140462977549) ^ (2194734024 + 2194734024) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 2194734024 * (2 : ZMod 140462977549) ^ 2194734024 := by rw [pow_add]
          _ = 863520754 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 140462977549) ^ 8778936096 = 9138117411 := by
        calc
          (2 : ZMod 140462977549) ^ 8778936096 = (2 : ZMod 140462977549) ^ (4389468048 + 4389468048) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 4389468048 * (2 : ZMod 140462977549) ^ 4389468048 := by rw [pow_add]
          _ = 9138117411 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 140462977549) ^ 17557872193 = 40636588475 := by
        calc
          (2 : ZMod 140462977549) ^ 17557872193 = (2 : ZMod 140462977549) ^ (8778936096 + 8778936096 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 8778936096 * (2 : ZMod 140462977549) ^ 8778936096) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 40636588475 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 140462977549) ^ 35115744387 = 81273176949 := by
        calc
          (2 : ZMod 140462977549) ^ 35115744387 = (2 : ZMod 140462977549) ^ (17557872193 + 17557872193 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 17557872193 * (2 : ZMod 140462977549) ^ 17557872193) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 81273176949 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 140462977549) ^ 70231488774 = 140462977548 := by
        calc
          (2 : ZMod 140462977549) ^ 70231488774 = (2 : ZMod 140462977549) ^ (35115744387 + 35115744387) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 35115744387 * (2 : ZMod 140462977549) ^ 35115744387 := by rw [pow_add]
          _ = 140462977548 := by rw [factor_0_35]; decide
      change (2 : ZMod 140462977549) ^ 70231488774 ≠ 1
      rw [factor_0_36]
      decide
    ·
      have factor_1_0 : (2 : ZMod 140462977549) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 140462977549) ^ 2 = 4 := by
        calc
          (2 : ZMod 140462977549) ^ 2 = (2 : ZMod 140462977549) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 1 * (2 : ZMod 140462977549) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 140462977549) ^ 5 = 32 := by
        calc
          (2 : ZMod 140462977549) ^ 5 = (2 : ZMod 140462977549) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 2 * (2 : ZMod 140462977549) ^ 2) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 140462977549) ^ 10 = 1024 := by
        calc
          (2 : ZMod 140462977549) ^ 10 = (2 : ZMod 140462977549) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 5 * (2 : ZMod 140462977549) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 140462977549) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 140462977549) ^ 21 = (2 : ZMod 140462977549) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 10 * (2 : ZMod 140462977549) ^ 10) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 140462977549) ^ 43 = 87388414170 := by
        calc
          (2 : ZMod 140462977549) ^ 43 = (2 : ZMod 140462977549) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 21 * (2 : ZMod 140462977549) ^ 21) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 87388414170 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 140462977549) ^ 87 = 122944861392 := by
        calc
          (2 : ZMod 140462977549) ^ 87 = (2 : ZMod 140462977549) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 43 * (2 : ZMod 140462977549) ^ 43) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 122944861392 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 140462977549) ^ 174 = 59608949066 := by
        calc
          (2 : ZMod 140462977549) ^ 174 = (2 : ZMod 140462977549) ^ (87 + 87) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 87 * (2 : ZMod 140462977549) ^ 87 := by rw [pow_add]
          _ = 59608949066 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 140462977549) ^ 348 = 64174474244 := by
        calc
          (2 : ZMod 140462977549) ^ 348 = (2 : ZMod 140462977549) ^ (174 + 174) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 174 * (2 : ZMod 140462977549) ^ 174 := by rw [pow_add]
          _ = 64174474244 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 140462977549) ^ 697 = 63304146960 := by
        calc
          (2 : ZMod 140462977549) ^ 697 = (2 : ZMod 140462977549) ^ (348 + 348 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 348 * (2 : ZMod 140462977549) ^ 348) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 63304146960 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 140462977549) ^ 1395 = 129311716716 := by
        calc
          (2 : ZMod 140462977549) ^ 1395 = (2 : ZMod 140462977549) ^ (697 + 697 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 697 * (2 : ZMod 140462977549) ^ 697) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 129311716716 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 140462977549) ^ 2790 = 20952419498 := by
        calc
          (2 : ZMod 140462977549) ^ 2790 = (2 : ZMod 140462977549) ^ (1395 + 1395) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 1395 * (2 : ZMod 140462977549) ^ 1395 := by rw [pow_add]
          _ = 20952419498 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 140462977549) ^ 5581 = 11681341120 := by
        calc
          (2 : ZMod 140462977549) ^ 5581 = (2 : ZMod 140462977549) ^ (2790 + 2790 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 2790 * (2 : ZMod 140462977549) ^ 2790) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 11681341120 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 140462977549) ^ 11162 = 82188963261 := by
        calc
          (2 : ZMod 140462977549) ^ 11162 = (2 : ZMod 140462977549) ^ (5581 + 5581) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 5581 * (2 : ZMod 140462977549) ^ 5581 := by rw [pow_add]
          _ = 82188963261 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 140462977549) ^ 22325 = 10942883315 := by
        calc
          (2 : ZMod 140462977549) ^ 22325 = (2 : ZMod 140462977549) ^ (11162 + 11162 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 11162 * (2 : ZMod 140462977549) ^ 11162) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 10942883315 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 140462977549) ^ 44651 = 40782315775 := by
        calc
          (2 : ZMod 140462977549) ^ 44651 = (2 : ZMod 140462977549) ^ (22325 + 22325 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 22325 * (2 : ZMod 140462977549) ^ 22325) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 40782315775 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 140462977549) ^ 89303 = 79293950002 := by
        calc
          (2 : ZMod 140462977549) ^ 89303 = (2 : ZMod 140462977549) ^ (44651 + 44651 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 44651 * (2 : ZMod 140462977549) ^ 44651) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 79293950002 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 140462977549) ^ 178607 = 97008830775 := by
        calc
          (2 : ZMod 140462977549) ^ 178607 = (2 : ZMod 140462977549) ^ (89303 + 89303 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 89303 * (2 : ZMod 140462977549) ^ 89303) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 97008830775 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 140462977549) ^ 357215 = 93147627906 := by
        calc
          (2 : ZMod 140462977549) ^ 357215 = (2 : ZMod 140462977549) ^ (178607 + 178607 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 178607 * (2 : ZMod 140462977549) ^ 178607) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 93147627906 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 140462977549) ^ 714431 = 127655394557 := by
        calc
          (2 : ZMod 140462977549) ^ 714431 = (2 : ZMod 140462977549) ^ (357215 + 357215 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 357215 * (2 : ZMod 140462977549) ^ 357215) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 127655394557 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 140462977549) ^ 1428863 = 111101840826 := by
        calc
          (2 : ZMod 140462977549) ^ 1428863 = (2 : ZMod 140462977549) ^ (714431 + 714431 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 714431 * (2 : ZMod 140462977549) ^ 714431) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 111101840826 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 140462977549) ^ 2857726 = 17954162493 := by
        calc
          (2 : ZMod 140462977549) ^ 2857726 = (2 : ZMod 140462977549) ^ (1428863 + 1428863) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 1428863 * (2 : ZMod 140462977549) ^ 1428863 := by rw [pow_add]
          _ = 17954162493 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 140462977549) ^ 5715453 = 83031966065 := by
        calc
          (2 : ZMod 140462977549) ^ 5715453 = (2 : ZMod 140462977549) ^ (2857726 + 2857726 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 2857726 * (2 : ZMod 140462977549) ^ 2857726) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 83031966065 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 140462977549) ^ 11430906 = 114191487598 := by
        calc
          (2 : ZMod 140462977549) ^ 11430906 = (2 : ZMod 140462977549) ^ (5715453 + 5715453) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 5715453 * (2 : ZMod 140462977549) ^ 5715453 := by rw [pow_add]
          _ = 114191487598 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 140462977549) ^ 22861812 = 86580189902 := by
        calc
          (2 : ZMod 140462977549) ^ 22861812 = (2 : ZMod 140462977549) ^ (11430906 + 11430906) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 11430906 * (2 : ZMod 140462977549) ^ 11430906 := by rw [pow_add]
          _ = 86580189902 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 140462977549) ^ 45723625 = 3427277674 := by
        calc
          (2 : ZMod 140462977549) ^ 45723625 = (2 : ZMod 140462977549) ^ (22861812 + 22861812 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 22861812 * (2 : ZMod 140462977549) ^ 22861812) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 3427277674 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 140462977549) ^ 91447251 = 50620479576 := by
        calc
          (2 : ZMod 140462977549) ^ 91447251 = (2 : ZMod 140462977549) ^ (45723625 + 45723625 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 45723625 * (2 : ZMod 140462977549) ^ 45723625) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 50620479576 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 140462977549) ^ 182894502 = 93120062992 := by
        calc
          (2 : ZMod 140462977549) ^ 182894502 = (2 : ZMod 140462977549) ^ (91447251 + 91447251) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 91447251 * (2 : ZMod 140462977549) ^ 91447251 := by rw [pow_add]
          _ = 93120062992 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 140462977549) ^ 365789004 = 32948318501 := by
        calc
          (2 : ZMod 140462977549) ^ 365789004 = (2 : ZMod 140462977549) ^ (182894502 + 182894502) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 182894502 * (2 : ZMod 140462977549) ^ 182894502 := by rw [pow_add]
          _ = 32948318501 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 140462977549) ^ 731578008 = 87333709703 := by
        calc
          (2 : ZMod 140462977549) ^ 731578008 = (2 : ZMod 140462977549) ^ (365789004 + 365789004) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 365789004 * (2 : ZMod 140462977549) ^ 365789004 := by rw [pow_add]
          _ = 87333709703 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 140462977549) ^ 1463156016 = 123594354280 := by
        calc
          (2 : ZMod 140462977549) ^ 1463156016 = (2 : ZMod 140462977549) ^ (731578008 + 731578008) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 731578008 * (2 : ZMod 140462977549) ^ 731578008 := by rw [pow_add]
          _ = 123594354280 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 140462977549) ^ 2926312032 = 36423121634 := by
        calc
          (2 : ZMod 140462977549) ^ 2926312032 = (2 : ZMod 140462977549) ^ (1463156016 + 1463156016) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 1463156016 * (2 : ZMod 140462977549) ^ 1463156016 := by rw [pow_add]
          _ = 36423121634 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 140462977549) ^ 5852624064 = 31387253158 := by
        calc
          (2 : ZMod 140462977549) ^ 5852624064 = (2 : ZMod 140462977549) ^ (2926312032 + 2926312032) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 2926312032 * (2 : ZMod 140462977549) ^ 2926312032 := by rw [pow_add]
          _ = 31387253158 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 140462977549) ^ 11705248129 = 138974193111 := by
        calc
          (2 : ZMod 140462977549) ^ 11705248129 = (2 : ZMod 140462977549) ^ (5852624064 + 5852624064 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 5852624064 * (2 : ZMod 140462977549) ^ 5852624064) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 138974193111 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 140462977549) ^ 23410496258 = 5073490154 := by
        calc
          (2 : ZMod 140462977549) ^ 23410496258 = (2 : ZMod 140462977549) ^ (11705248129 + 11705248129) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 11705248129 * (2 : ZMod 140462977549) ^ 11705248129 := by rw [pow_add]
          _ = 5073490154 := by rw [factor_1_33]; decide
      have factor_1_35 : (2 : ZMod 140462977549) ^ 46820992516 = 5073490153 := by
        calc
          (2 : ZMod 140462977549) ^ 46820992516 = (2 : ZMod 140462977549) ^ (23410496258 + 23410496258) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 23410496258 * (2 : ZMod 140462977549) ^ 23410496258 := by rw [pow_add]
          _ = 5073490153 := by rw [factor_1_34]; decide
      change (2 : ZMod 140462977549) ^ 46820992516 ≠ 1
      rw [factor_1_35]
      decide
    ·
      have factor_2_0 : (2 : ZMod 140462977549) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 140462977549) ^ 3 = 8 := by
        calc
          (2 : ZMod 140462977549) ^ 3 = (2 : ZMod 140462977549) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 1 * (2 : ZMod 140462977549) ^ 1) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 140462977549) ^ 6 = 64 := by
        calc
          (2 : ZMod 140462977549) ^ 6 = (2 : ZMod 140462977549) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 3 * (2 : ZMod 140462977549) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 140462977549) ^ 13 = 8192 := by
        calc
          (2 : ZMod 140462977549) ^ 13 = (2 : ZMod 140462977549) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 6 * (2 : ZMod 140462977549) ^ 6) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 140462977549) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 140462977549) ^ 27 = (2 : ZMod 140462977549) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 13 * (2 : ZMod 140462977549) ^ 13) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 140462977549) ^ 55 = 43277645468 := by
        calc
          (2 : ZMod 140462977549) ^ 55 = (2 : ZMod 140462977549) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 27 * (2 : ZMod 140462977549) ^ 27) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 43277645468 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 140462977549) ^ 110 = 38698179442 := by
        calc
          (2 : ZMod 140462977549) ^ 110 = (2 : ZMod 140462977549) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 55 * (2 : ZMod 140462977549) ^ 55 := by rw [pow_add]
          _ = 38698179442 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 140462977549) ^ 220 = 90787532477 := by
        calc
          (2 : ZMod 140462977549) ^ 220 = (2 : ZMod 140462977549) ^ (110 + 110) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 110 * (2 : ZMod 140462977549) ^ 110 := by rw [pow_add]
          _ = 90787532477 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 140462977549) ^ 440 = 89457249661 := by
        calc
          (2 : ZMod 140462977549) ^ 440 = (2 : ZMod 140462977549) ^ (220 + 220) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 220 * (2 : ZMod 140462977549) ^ 220 := by rw [pow_add]
          _ = 89457249661 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 140462977549) ^ 881 = 40471512248 := by
        calc
          (2 : ZMod 140462977549) ^ 881 = (2 : ZMod 140462977549) ^ (440 + 440 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 440 * (2 : ZMod 140462977549) ^ 440) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 40471512248 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 140462977549) ^ 1762 = 95099845900 := by
        calc
          (2 : ZMod 140462977549) ^ 1762 = (2 : ZMod 140462977549) ^ (881 + 881) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 881 * (2 : ZMod 140462977549) ^ 881 := by rw [pow_add]
          _ = 95099845900 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 140462977549) ^ 3525 = 20372110808 := by
        calc
          (2 : ZMod 140462977549) ^ 3525 = (2 : ZMod 140462977549) ^ (1762 + 1762 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 1762 * (2 : ZMod 140462977549) ^ 1762) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 20372110808 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 140462977549) ^ 7050 = 119069838221 := by
        calc
          (2 : ZMod 140462977549) ^ 7050 = (2 : ZMod 140462977549) ^ (3525 + 3525) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 3525 * (2 : ZMod 140462977549) ^ 3525 := by rw [pow_add]
          _ = 119069838221 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 140462977549) ^ 14100 = 84647742677 := by
        calc
          (2 : ZMod 140462977549) ^ 14100 = (2 : ZMod 140462977549) ^ (7050 + 7050) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 7050 * (2 : ZMod 140462977549) ^ 7050 := by rw [pow_add]
          _ = 84647742677 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 140462977549) ^ 28201 = 81909457803 := by
        calc
          (2 : ZMod 140462977549) ^ 28201 = (2 : ZMod 140462977549) ^ (14100 + 14100 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 14100 * (2 : ZMod 140462977549) ^ 14100) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 81909457803 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 140462977549) ^ 56402 = 127666369349 := by
        calc
          (2 : ZMod 140462977549) ^ 56402 = (2 : ZMod 140462977549) ^ (28201 + 28201) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 28201 * (2 : ZMod 140462977549) ^ 28201 := by rw [pow_add]
          _ = 127666369349 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 140462977549) ^ 112804 = 64292544417 := by
        calc
          (2 : ZMod 140462977549) ^ 112804 = (2 : ZMod 140462977549) ^ (56402 + 56402) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 56402 * (2 : ZMod 140462977549) ^ 56402 := by rw [pow_add]
          _ = 64292544417 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 140462977549) ^ 225609 = 112177646769 := by
        calc
          (2 : ZMod 140462977549) ^ 225609 = (2 : ZMod 140462977549) ^ (112804 + 112804 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 112804 * (2 : ZMod 140462977549) ^ 112804) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 112177646769 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 140462977549) ^ 451219 = 101909955140 := by
        calc
          (2 : ZMod 140462977549) ^ 451219 = (2 : ZMod 140462977549) ^ (225609 + 225609 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 225609 * (2 : ZMod 140462977549) ^ 225609) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 101909955140 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 140462977549) ^ 902439 = 32713379854 := by
        calc
          (2 : ZMod 140462977549) ^ 902439 = (2 : ZMod 140462977549) ^ (451219 + 451219 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 451219 * (2 : ZMod 140462977549) ^ 451219) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 32713379854 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 140462977549) ^ 1804879 = 108431969570 := by
        calc
          (2 : ZMod 140462977549) ^ 1804879 = (2 : ZMod 140462977549) ^ (902439 + 902439 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 902439 * (2 : ZMod 140462977549) ^ 902439) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 108431969570 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 140462977549) ^ 3609759 = 114672813781 := by
        calc
          (2 : ZMod 140462977549) ^ 3609759 = (2 : ZMod 140462977549) ^ (1804879 + 1804879 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 1804879 * (2 : ZMod 140462977549) ^ 1804879) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 114672813781 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 140462977549) ^ 7219519 = 7647172305 := by
        calc
          (2 : ZMod 140462977549) ^ 7219519 = (2 : ZMod 140462977549) ^ (3609759 + 3609759 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 3609759 * (2 : ZMod 140462977549) ^ 3609759) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 7647172305 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 140462977549) ^ 14439039 = 48614284269 := by
        calc
          (2 : ZMod 140462977549) ^ 14439039 = (2 : ZMod 140462977549) ^ (7219519 + 7219519 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 7219519 * (2 : ZMod 140462977549) ^ 7219519) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 48614284269 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 140462977549) ^ 28878079 = 24096398538 := by
        calc
          (2 : ZMod 140462977549) ^ 28878079 = (2 : ZMod 140462977549) ^ (14439039 + 14439039 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 14439039 * (2 : ZMod 140462977549) ^ 14439039) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 24096398538 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 140462977549) ^ 57756158 = 105959416029 := by
        calc
          (2 : ZMod 140462977549) ^ 57756158 = (2 : ZMod 140462977549) ^ (28878079 + 28878079) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 28878079 * (2 : ZMod 140462977549) ^ 28878079 := by rw [pow_add]
          _ = 105959416029 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 140462977549) ^ 115512317 = 47045056006 := by
        calc
          (2 : ZMod 140462977549) ^ 115512317 = (2 : ZMod 140462977549) ^ (57756158 + 57756158 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 57756158 * (2 : ZMod 140462977549) ^ 57756158) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 47045056006 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 140462977549) ^ 231024634 = 60717058322 := by
        calc
          (2 : ZMod 140462977549) ^ 231024634 = (2 : ZMod 140462977549) ^ (115512317 + 115512317) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 115512317 * (2 : ZMod 140462977549) ^ 115512317 := by rw [pow_add]
          _ = 60717058322 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 140462977549) ^ 462049268 = 122095391575 := by
        calc
          (2 : ZMod 140462977549) ^ 462049268 = (2 : ZMod 140462977549) ^ (231024634 + 231024634) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 231024634 * (2 : ZMod 140462977549) ^ 231024634 := by rw [pow_add]
          _ = 122095391575 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 140462977549) ^ 924098536 = 76320226326 := by
        calc
          (2 : ZMod 140462977549) ^ 924098536 = (2 : ZMod 140462977549) ^ (462049268 + 462049268) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 462049268 * (2 : ZMod 140462977549) ^ 462049268 := by rw [pow_add]
          _ = 76320226326 := by rw [factor_2_28]; decide
      have factor_2_30 : (2 : ZMod 140462977549) ^ 1848197073 = 119443680446 := by
        calc
          (2 : ZMod 140462977549) ^ 1848197073 = (2 : ZMod 140462977549) ^ (924098536 + 924098536 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 924098536 * (2 : ZMod 140462977549) ^ 924098536) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 119443680446 := by rw [factor_2_29]; decide
      have factor_2_31 : (2 : ZMod 140462977549) ^ 3696394146 = 132815980649 := by
        calc
          (2 : ZMod 140462977549) ^ 3696394146 = (2 : ZMod 140462977549) ^ (1848197073 + 1848197073) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 1848197073 * (2 : ZMod 140462977549) ^ 1848197073 := by rw [pow_add]
          _ = 132815980649 := by rw [factor_2_30]; decide
      have factor_2_32 : (2 : ZMod 140462977549) ^ 7392788292 = 123197436235 := by
        calc
          (2 : ZMod 140462977549) ^ 7392788292 = (2 : ZMod 140462977549) ^ (3696394146 + 3696394146) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 3696394146 * (2 : ZMod 140462977549) ^ 3696394146 := by rw [pow_add]
          _ = 123197436235 := by rw [factor_2_31]; decide
      change (2 : ZMod 140462977549) ^ 7392788292 ≠ 1
      rw [factor_2_32]
      decide
    ·
      have factor_3_0 : (2 : ZMod 140462977549) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 140462977549) ^ 3 = 8 := by
        calc
          (2 : ZMod 140462977549) ^ 3 = (2 : ZMod 140462977549) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 1 * (2 : ZMod 140462977549) ^ 1) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 140462977549) ^ 6 = 64 := by
        calc
          (2 : ZMod 140462977549) ^ 6 = (2 : ZMod 140462977549) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 3 * (2 : ZMod 140462977549) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 140462977549) ^ 12 = 4096 := by
        calc
          (2 : ZMod 140462977549) ^ 12 = (2 : ZMod 140462977549) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 6 * (2 : ZMod 140462977549) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 140462977549) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 140462977549) ^ 24 = (2 : ZMod 140462977549) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 12 * (2 : ZMod 140462977549) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 140462977549) ^ 48 = 127632680009 := by
        calc
          (2 : ZMod 140462977549) ^ 48 = (2 : ZMod 140462977549) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 24 * (2 : ZMod 140462977549) ^ 24 := by rw [pow_add]
          _ = 127632680009 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 140462977549) ^ 96 = 20355090752 := by
        calc
          (2 : ZMod 140462977549) ^ 96 = (2 : ZMod 140462977549) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 48 * (2 : ZMod 140462977549) ^ 48 := by rw [pow_add]
          _ = 20355090752 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 140462977549) ^ 192 = 43480563901 := by
        calc
          (2 : ZMod 140462977549) ^ 192 = (2 : ZMod 140462977549) ^ (96 + 96) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 96 * (2 : ZMod 140462977549) ^ 96 := by rw [pow_add]
          _ = 43480563901 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 140462977549) ^ 385 = 21219397394 := by
        calc
          (2 : ZMod 140462977549) ^ 385 = (2 : ZMod 140462977549) ^ (192 + 192 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 192 * (2 : ZMod 140462977549) ^ 192) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 21219397394 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 140462977549) ^ 771 = 73031489327 := by
        calc
          (2 : ZMod 140462977549) ^ 771 = (2 : ZMod 140462977549) ^ (385 + 385 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 385 * (2 : ZMod 140462977549) ^ 385) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 73031489327 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 140462977549) ^ 1542 = 22814026760 := by
        calc
          (2 : ZMod 140462977549) ^ 1542 = (2 : ZMod 140462977549) ^ (771 + 771) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 771 * (2 : ZMod 140462977549) ^ 771 := by rw [pow_add]
          _ = 22814026760 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 140462977549) ^ 3085 = 77176254380 := by
        calc
          (2 : ZMod 140462977549) ^ 3085 = (2 : ZMod 140462977549) ^ (1542 + 1542 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 1542 * (2 : ZMod 140462977549) ^ 1542) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 77176254380 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 140462977549) ^ 6171 = 12537079500 := by
        calc
          (2 : ZMod 140462977549) ^ 6171 = (2 : ZMod 140462977549) ^ (3085 + 3085 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 3085 * (2 : ZMod 140462977549) ^ 3085) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 12537079500 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 140462977549) ^ 12342 = 34551678668 := by
        calc
          (2 : ZMod 140462977549) ^ 12342 = (2 : ZMod 140462977549) ^ (6171 + 6171) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 6171 * (2 : ZMod 140462977549) ^ 6171 := by rw [pow_add]
          _ = 34551678668 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 140462977549) ^ 24684 = 26985778114 := by
        calc
          (2 : ZMod 140462977549) ^ 24684 = (2 : ZMod 140462977549) ^ (12342 + 12342) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 12342 * (2 : ZMod 140462977549) ^ 12342 := by rw [pow_add]
          _ = 26985778114 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 140462977549) ^ 49368 = 69033702067 := by
        calc
          (2 : ZMod 140462977549) ^ 49368 = (2 : ZMod 140462977549) ^ (24684 + 24684) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 24684 * (2 : ZMod 140462977549) ^ 24684 := by rw [pow_add]
          _ = 69033702067 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 140462977549) ^ 98737 = 70872222496 := by
        calc
          (2 : ZMod 140462977549) ^ 98737 = (2 : ZMod 140462977549) ^ (49368 + 49368 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 49368 * (2 : ZMod 140462977549) ^ 49368) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 70872222496 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 140462977549) ^ 197474 = 94490379935 := by
        calc
          (2 : ZMod 140462977549) ^ 197474 = (2 : ZMod 140462977549) ^ (98737 + 98737) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 98737 * (2 : ZMod 140462977549) ^ 98737 := by rw [pow_add]
          _ = 94490379935 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 140462977549) ^ 394949 = 41391516392 := by
        calc
          (2 : ZMod 140462977549) ^ 394949 = (2 : ZMod 140462977549) ^ (197474 + 197474 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 197474 * (2 : ZMod 140462977549) ^ 197474) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 41391516392 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 140462977549) ^ 789898 = 60679375870 := by
        calc
          (2 : ZMod 140462977549) ^ 789898 = (2 : ZMod 140462977549) ^ (394949 + 394949) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 394949 * (2 : ZMod 140462977549) ^ 394949 := by rw [pow_add]
          _ = 60679375870 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 140462977549) ^ 1579797 = 113760586664 := by
        calc
          (2 : ZMod 140462977549) ^ 1579797 = (2 : ZMod 140462977549) ^ (789898 + 789898 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 789898 * (2 : ZMod 140462977549) ^ 789898) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 113760586664 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 140462977549) ^ 3159595 = 57110666706 := by
        calc
          (2 : ZMod 140462977549) ^ 3159595 = (2 : ZMod 140462977549) ^ (1579797 + 1579797 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 1579797 * (2 : ZMod 140462977549) ^ 1579797) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 57110666706 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 140462977549) ^ 6319191 = 137744291644 := by
        calc
          (2 : ZMod 140462977549) ^ 6319191 = (2 : ZMod 140462977549) ^ (3159595 + 3159595 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 3159595 * (2 : ZMod 140462977549) ^ 3159595) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 137744291644 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 140462977549) ^ 12638382 = 10944859724 := by
        calc
          (2 : ZMod 140462977549) ^ 12638382 = (2 : ZMod 140462977549) ^ (6319191 + 6319191) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 6319191 * (2 : ZMod 140462977549) ^ 6319191 := by rw [pow_add]
          _ = 10944859724 := by rw [factor_3_22]; decide
      have factor_3_24 : (2 : ZMod 140462977549) ^ 25276764 = 137443960338 := by
        calc
          (2 : ZMod 140462977549) ^ 25276764 = (2 : ZMod 140462977549) ^ (12638382 + 12638382) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 12638382 * (2 : ZMod 140462977549) ^ 12638382 := by rw [pow_add]
          _ = 137443960338 := by rw [factor_3_23]; decide
      change (2 : ZMod 140462977549) ^ 25276764 ≠ 1
      rw [factor_3_24]
      decide
    ·
      have factor_4_0 : (2 : ZMod 140462977549) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 140462977549) ^ 2 = 4 := by
        calc
          (2 : ZMod 140462977549) ^ 2 = (2 : ZMod 140462977549) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 1 * (2 : ZMod 140462977549) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 140462977549) ^ 4 = 16 := by
        calc
          (2 : ZMod 140462977549) ^ 4 = (2 : ZMod 140462977549) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 2 * (2 : ZMod 140462977549) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 140462977549) ^ 9 = 512 := by
        calc
          (2 : ZMod 140462977549) ^ 9 = (2 : ZMod 140462977549) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 4 * (2 : ZMod 140462977549) ^ 4) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 140462977549) ^ 19 = 524288 := by
        calc
          (2 : ZMod 140462977549) ^ 19 = (2 : ZMod 140462977549) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 9 * (2 : ZMod 140462977549) ^ 9) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 140462977549) ^ 38 = 134414929395 := by
        calc
          (2 : ZMod 140462977549) ^ 38 = (2 : ZMod 140462977549) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 19 * (2 : ZMod 140462977549) ^ 19 := by rw [pow_add]
          _ = 134414929395 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 140462977549) ^ 77 = 138388306866 := by
        calc
          (2 : ZMod 140462977549) ^ 77 = (2 : ZMod 140462977549) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 38 * (2 : ZMod 140462977549) ^ 38) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 138388306866 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 140462977549) ^ 154 = 12415896555 := by
        calc
          (2 : ZMod 140462977549) ^ 154 = (2 : ZMod 140462977549) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 77 * (2 : ZMod 140462977549) ^ 77 := by rw [pow_add]
          _ = 12415896555 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 140462977549) ^ 309 = 42491131605 := by
        calc
          (2 : ZMod 140462977549) ^ 309 = (2 : ZMod 140462977549) ^ (154 + 154 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 154 * (2 : ZMod 140462977549) ^ 154) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 42491131605 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 140462977549) ^ 618 = 140403558364 := by
        calc
          (2 : ZMod 140462977549) ^ 618 = (2 : ZMod 140462977549) ^ (309 + 309) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 309 * (2 : ZMod 140462977549) ^ 309 := by rw [pow_add]
          _ = 140403558364 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 140462977549) ^ 1237 = 64747762671 := by
        calc
          (2 : ZMod 140462977549) ^ 1237 = (2 : ZMod 140462977549) ^ (618 + 618 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 618 * (2 : ZMod 140462977549) ^ 618) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 64747762671 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 140462977549) ^ 2474 = 119026488750 := by
        calc
          (2 : ZMod 140462977549) ^ 2474 = (2 : ZMod 140462977549) ^ (1237 + 1237) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 1237 * (2 : ZMod 140462977549) ^ 1237 := by rw [pow_add]
          _ = 119026488750 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 140462977549) ^ 4949 = 125785136518 := by
        calc
          (2 : ZMod 140462977549) ^ 4949 = (2 : ZMod 140462977549) ^ (2474 + 2474 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 2474 * (2 : ZMod 140462977549) ^ 2474) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 125785136518 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 140462977549) ^ 9898 = 137157808607 := by
        calc
          (2 : ZMod 140462977549) ^ 9898 = (2 : ZMod 140462977549) ^ (4949 + 4949) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 4949 * (2 : ZMod 140462977549) ^ 4949 := by rw [pow_add]
          _ = 137157808607 := by rw [factor_4_12]; decide
      have factor_4_14 : (2 : ZMod 140462977549) ^ 19796 = 124196349705 := by
        calc
          (2 : ZMod 140462977549) ^ 19796 = (2 : ZMod 140462977549) ^ (9898 + 9898) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 9898 * (2 : ZMod 140462977549) ^ 9898 := by rw [pow_add]
          _ = 124196349705 := by rw [factor_4_13]; decide
      have factor_4_15 : (2 : ZMod 140462977549) ^ 39593 = 68926864929 := by
        calc
          (2 : ZMod 140462977549) ^ 39593 = (2 : ZMod 140462977549) ^ (19796 + 19796 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 19796 * (2 : ZMod 140462977549) ^ 19796) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 68926864929 := by rw [factor_4_14]; decide
      have factor_4_16 : (2 : ZMod 140462977549) ^ 79187 = 136477523726 := by
        calc
          (2 : ZMod 140462977549) ^ 79187 = (2 : ZMod 140462977549) ^ (39593 + 39593 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 39593 * (2 : ZMod 140462977549) ^ 39593) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 136477523726 := by rw [factor_4_15]; decide
      have factor_4_17 : (2 : ZMod 140462977549) ^ 158374 = 22605532134 := by
        calc
          (2 : ZMod 140462977549) ^ 158374 = (2 : ZMod 140462977549) ^ (79187 + 79187) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 79187 * (2 : ZMod 140462977549) ^ 79187 := by rw [pow_add]
          _ = 22605532134 := by rw [factor_4_16]; decide
      have factor_4_18 : (2 : ZMod 140462977549) ^ 316749 = 54612919229 := by
        calc
          (2 : ZMod 140462977549) ^ 316749 = (2 : ZMod 140462977549) ^ (158374 + 158374 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = ((2 : ZMod 140462977549) ^ 158374 * (2 : ZMod 140462977549) ^ 158374) * (2 : ZMod 140462977549) := by rw [pow_succ, pow_add]
          _ = 54612919229 := by rw [factor_4_17]; decide
      have factor_4_19 : (2 : ZMod 140462977549) ^ 633498 = 71269245484 := by
        calc
          (2 : ZMod 140462977549) ^ 633498 = (2 : ZMod 140462977549) ^ (316749 + 316749) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 316749 * (2 : ZMod 140462977549) ^ 316749 := by rw [pow_add]
          _ = 71269245484 := by rw [factor_4_18]; decide
      have factor_4_20 : (2 : ZMod 140462977549) ^ 1266996 = 33571821769 := by
        calc
          (2 : ZMod 140462977549) ^ 1266996 = (2 : ZMod 140462977549) ^ (633498 + 633498) :=
            congrArg (fun n : ℕ => (2 : ZMod 140462977549) ^ n) (by norm_num)
          _ = (2 : ZMod 140462977549) ^ 633498 * (2 : ZMod 140462977549) ^ 633498 := by rw [pow_add]
          _ = 33571821769 := by rw [factor_4_19]; decide
      change (2 : ZMod 140462977549) ^ 1266996 ≠ 1
      rw [factor_4_20]
      decide

#print axioms prime_lucas_140462977549

end TotientTailPeriodKiller
end Erdos249257
