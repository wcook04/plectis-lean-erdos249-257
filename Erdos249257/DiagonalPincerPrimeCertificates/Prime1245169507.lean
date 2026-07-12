import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1245169507 : Nat.Prime 1245169507 := by
  apply lucas_primality 1245169507 (2 : ZMod 1245169507)
  ·
      have fermat_0 : (2 : ZMod 1245169507) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 1245169507) ^ 2 = 4 := by
        calc
          (2 : ZMod 1245169507) ^ 2 = (2 : ZMod 1245169507) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 1 * (2 : ZMod 1245169507) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 1245169507) ^ 4 = 16 := by
        calc
          (2 : ZMod 1245169507) ^ 4 = (2 : ZMod 1245169507) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 2 * (2 : ZMod 1245169507) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 1245169507) ^ 9 = 512 := by
        calc
          (2 : ZMod 1245169507) ^ 9 = (2 : ZMod 1245169507) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 4 * (2 : ZMod 1245169507) ^ 4) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 1245169507) ^ 18 = 262144 := by
        calc
          (2 : ZMod 1245169507) ^ 18 = (2 : ZMod 1245169507) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 9 * (2 : ZMod 1245169507) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 1245169507) ^ 37 = 470307702 := by
        calc
          (2 : ZMod 1245169507) ^ 37 = (2 : ZMod 1245169507) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 18 * (2 : ZMod 1245169507) ^ 18) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 470307702 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 1245169507) ^ 74 = 837920294 := by
        calc
          (2 : ZMod 1245169507) ^ 74 = (2 : ZMod 1245169507) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 37 * (2 : ZMod 1245169507) ^ 37 := by rw [pow_add]
          _ = 837920294 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 1245169507) ^ 148 = 90675549 := by
        calc
          (2 : ZMod 1245169507) ^ 148 = (2 : ZMod 1245169507) ^ (74 + 74) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 74 * (2 : ZMod 1245169507) ^ 74 := by rw [pow_add]
          _ = 90675549 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 1245169507) ^ 296 = 459439774 := by
        calc
          (2 : ZMod 1245169507) ^ 296 = (2 : ZMod 1245169507) ^ (148 + 148) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 148 * (2 : ZMod 1245169507) ^ 148 := by rw [pow_add]
          _ = 459439774 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 1245169507) ^ 593 = 221358253 := by
        calc
          (2 : ZMod 1245169507) ^ 593 = (2 : ZMod 1245169507) ^ (296 + 296 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 296 * (2 : ZMod 1245169507) ^ 296) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 221358253 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 1245169507) ^ 1187 = 591811904 := by
        calc
          (2 : ZMod 1245169507) ^ 1187 = (2 : ZMod 1245169507) ^ (593 + 593 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 593 * (2 : ZMod 1245169507) ^ 593) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 591811904 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 1245169507) ^ 2374 = 980364936 := by
        calc
          (2 : ZMod 1245169507) ^ 2374 = (2 : ZMod 1245169507) ^ (1187 + 1187) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 1187 * (2 : ZMod 1245169507) ^ 1187 := by rw [pow_add]
          _ = 980364936 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 1245169507) ^ 4749 = 552432008 := by
        calc
          (2 : ZMod 1245169507) ^ 4749 = (2 : ZMod 1245169507) ^ (2374 + 2374 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 2374 * (2 : ZMod 1245169507) ^ 2374) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 552432008 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 1245169507) ^ 9499 = 106026694 := by
        calc
          (2 : ZMod 1245169507) ^ 9499 = (2 : ZMod 1245169507) ^ (4749 + 4749 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 4749 * (2 : ZMod 1245169507) ^ 4749) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 106026694 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 1245169507) ^ 18999 = 1149520248 := by
        calc
          (2 : ZMod 1245169507) ^ 18999 = (2 : ZMod 1245169507) ^ (9499 + 9499 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 9499 * (2 : ZMod 1245169507) ^ 9499) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 1149520248 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 1245169507) ^ 37999 = 1042101817 := by
        calc
          (2 : ZMod 1245169507) ^ 37999 = (2 : ZMod 1245169507) ^ (18999 + 18999 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 18999 * (2 : ZMod 1245169507) ^ 18999) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 1042101817 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 1245169507) ^ 75999 = 430618862 := by
        calc
          (2 : ZMod 1245169507) ^ 75999 = (2 : ZMod 1245169507) ^ (37999 + 37999 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 37999 * (2 : ZMod 1245169507) ^ 37999) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 430618862 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 1245169507) ^ 151998 = 185761519 := by
        calc
          (2 : ZMod 1245169507) ^ 151998 = (2 : ZMod 1245169507) ^ (75999 + 75999) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 75999 * (2 : ZMod 1245169507) ^ 75999 := by rw [pow_add]
          _ = 185761519 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 1245169507) ^ 303996 = 484290092 := by
        calc
          (2 : ZMod 1245169507) ^ 303996 = (2 : ZMod 1245169507) ^ (151998 + 151998) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 151998 * (2 : ZMod 1245169507) ^ 151998 := by rw [pow_add]
          _ = 484290092 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 1245169507) ^ 607992 = 1066397157 := by
        calc
          (2 : ZMod 1245169507) ^ 607992 = (2 : ZMod 1245169507) ^ (303996 + 303996) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 303996 * (2 : ZMod 1245169507) ^ 303996 := by rw [pow_add]
          _ = 1066397157 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 1245169507) ^ 1215985 = 624678394 := by
        calc
          (2 : ZMod 1245169507) ^ 1215985 = (2 : ZMod 1245169507) ^ (607992 + 607992 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 607992 * (2 : ZMod 1245169507) ^ 607992) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 624678394 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 1245169507) ^ 2431971 = 45172447 := by
        calc
          (2 : ZMod 1245169507) ^ 2431971 = (2 : ZMod 1245169507) ^ (1215985 + 1215985 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 1215985 * (2 : ZMod 1245169507) ^ 1215985) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 45172447 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 1245169507) ^ 4863943 = 844115303 := by
        calc
          (2 : ZMod 1245169507) ^ 4863943 = (2 : ZMod 1245169507) ^ (2431971 + 2431971 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 2431971 * (2 : ZMod 1245169507) ^ 2431971) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 844115303 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 1245169507) ^ 9727886 = 1074860789 := by
        calc
          (2 : ZMod 1245169507) ^ 9727886 = (2 : ZMod 1245169507) ^ (4863943 + 4863943) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 4863943 * (2 : ZMod 1245169507) ^ 4863943 := by rw [pow_add]
          _ = 1074860789 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 1245169507) ^ 19455773 = 1234624645 := by
        calc
          (2 : ZMod 1245169507) ^ 19455773 = (2 : ZMod 1245169507) ^ (9727886 + 9727886 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 9727886 * (2 : ZMod 1245169507) ^ 9727886) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 1234624645 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 1245169507) ^ 38911547 = 955247888 := by
        calc
          (2 : ZMod 1245169507) ^ 38911547 = (2 : ZMod 1245169507) ^ (19455773 + 19455773 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 19455773 * (2 : ZMod 1245169507) ^ 19455773) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 955247888 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 1245169507) ^ 77823094 = 178299661 := by
        calc
          (2 : ZMod 1245169507) ^ 77823094 = (2 : ZMod 1245169507) ^ (38911547 + 38911547) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 38911547 * (2 : ZMod 1245169507) ^ 38911547 := by rw [pow_add]
          _ = 178299661 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 1245169507) ^ 155646188 = 272374975 := by
        calc
          (2 : ZMod 1245169507) ^ 155646188 = (2 : ZMod 1245169507) ^ (77823094 + 77823094) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 77823094 * (2 : ZMod 1245169507) ^ 77823094 := by rw [pow_add]
          _ = 272374975 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 1245169507) ^ 311292376 = 127907910 := by
        calc
          (2 : ZMod 1245169507) ^ 311292376 = (2 : ZMod 1245169507) ^ (155646188 + 155646188) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 155646188 * (2 : ZMod 1245169507) ^ 155646188 := by rw [pow_add]
          _ = 127907910 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 1245169507) ^ 622584753 = 1245169506 := by
        calc
          (2 : ZMod 1245169507) ^ 622584753 = (2 : ZMod 1245169507) ^ (311292376 + 311292376 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 311292376 * (2 : ZMod 1245169507) ^ 311292376) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 1245169506 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 1245169507) ^ 1245169506 = 1 := by
        calc
          (2 : ZMod 1245169507) ^ 1245169506 = (2 : ZMod 1245169507) ^ (622584753 + 622584753) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 622584753 * (2 : ZMod 1245169507) ^ 622584753 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (139, 1), (213287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (139, 1), (213287, 1)] : List FactorBlock).map factorBlockValue).prod = 1245169507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 1245169507) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 1245169507) ^ 2 = 4 := by
        calc
          (2 : ZMod 1245169507) ^ 2 = (2 : ZMod 1245169507) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 1 * (2 : ZMod 1245169507) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 1245169507) ^ 4 = 16 := by
        calc
          (2 : ZMod 1245169507) ^ 4 = (2 : ZMod 1245169507) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 2 * (2 : ZMod 1245169507) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 1245169507) ^ 9 = 512 := by
        calc
          (2 : ZMod 1245169507) ^ 9 = (2 : ZMod 1245169507) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 4 * (2 : ZMod 1245169507) ^ 4) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 1245169507) ^ 18 = 262144 := by
        calc
          (2 : ZMod 1245169507) ^ 18 = (2 : ZMod 1245169507) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 9 * (2 : ZMod 1245169507) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 1245169507) ^ 37 = 470307702 := by
        calc
          (2 : ZMod 1245169507) ^ 37 = (2 : ZMod 1245169507) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 18 * (2 : ZMod 1245169507) ^ 18) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 470307702 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 1245169507) ^ 74 = 837920294 := by
        calc
          (2 : ZMod 1245169507) ^ 74 = (2 : ZMod 1245169507) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 37 * (2 : ZMod 1245169507) ^ 37 := by rw [pow_add]
          _ = 837920294 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 1245169507) ^ 148 = 90675549 := by
        calc
          (2 : ZMod 1245169507) ^ 148 = (2 : ZMod 1245169507) ^ (74 + 74) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 74 * (2 : ZMod 1245169507) ^ 74 := by rw [pow_add]
          _ = 90675549 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 1245169507) ^ 296 = 459439774 := by
        calc
          (2 : ZMod 1245169507) ^ 296 = (2 : ZMod 1245169507) ^ (148 + 148) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 148 * (2 : ZMod 1245169507) ^ 148 := by rw [pow_add]
          _ = 459439774 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 1245169507) ^ 593 = 221358253 := by
        calc
          (2 : ZMod 1245169507) ^ 593 = (2 : ZMod 1245169507) ^ (296 + 296 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 296 * (2 : ZMod 1245169507) ^ 296) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 221358253 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 1245169507) ^ 1187 = 591811904 := by
        calc
          (2 : ZMod 1245169507) ^ 1187 = (2 : ZMod 1245169507) ^ (593 + 593 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 593 * (2 : ZMod 1245169507) ^ 593) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 591811904 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 1245169507) ^ 2374 = 980364936 := by
        calc
          (2 : ZMod 1245169507) ^ 2374 = (2 : ZMod 1245169507) ^ (1187 + 1187) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 1187 * (2 : ZMod 1245169507) ^ 1187 := by rw [pow_add]
          _ = 980364936 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 1245169507) ^ 4749 = 552432008 := by
        calc
          (2 : ZMod 1245169507) ^ 4749 = (2 : ZMod 1245169507) ^ (2374 + 2374 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 2374 * (2 : ZMod 1245169507) ^ 2374) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 552432008 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 1245169507) ^ 9499 = 106026694 := by
        calc
          (2 : ZMod 1245169507) ^ 9499 = (2 : ZMod 1245169507) ^ (4749 + 4749 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 4749 * (2 : ZMod 1245169507) ^ 4749) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 106026694 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 1245169507) ^ 18999 = 1149520248 := by
        calc
          (2 : ZMod 1245169507) ^ 18999 = (2 : ZMod 1245169507) ^ (9499 + 9499 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 9499 * (2 : ZMod 1245169507) ^ 9499) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 1149520248 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 1245169507) ^ 37999 = 1042101817 := by
        calc
          (2 : ZMod 1245169507) ^ 37999 = (2 : ZMod 1245169507) ^ (18999 + 18999 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 18999 * (2 : ZMod 1245169507) ^ 18999) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 1042101817 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 1245169507) ^ 75999 = 430618862 := by
        calc
          (2 : ZMod 1245169507) ^ 75999 = (2 : ZMod 1245169507) ^ (37999 + 37999 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 37999 * (2 : ZMod 1245169507) ^ 37999) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 430618862 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 1245169507) ^ 151998 = 185761519 := by
        calc
          (2 : ZMod 1245169507) ^ 151998 = (2 : ZMod 1245169507) ^ (75999 + 75999) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 75999 * (2 : ZMod 1245169507) ^ 75999 := by rw [pow_add]
          _ = 185761519 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 1245169507) ^ 303996 = 484290092 := by
        calc
          (2 : ZMod 1245169507) ^ 303996 = (2 : ZMod 1245169507) ^ (151998 + 151998) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 151998 * (2 : ZMod 1245169507) ^ 151998 := by rw [pow_add]
          _ = 484290092 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 1245169507) ^ 607992 = 1066397157 := by
        calc
          (2 : ZMod 1245169507) ^ 607992 = (2 : ZMod 1245169507) ^ (303996 + 303996) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 303996 * (2 : ZMod 1245169507) ^ 303996 := by rw [pow_add]
          _ = 1066397157 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 1245169507) ^ 1215985 = 624678394 := by
        calc
          (2 : ZMod 1245169507) ^ 1215985 = (2 : ZMod 1245169507) ^ (607992 + 607992 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 607992 * (2 : ZMod 1245169507) ^ 607992) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 624678394 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 1245169507) ^ 2431971 = 45172447 := by
        calc
          (2 : ZMod 1245169507) ^ 2431971 = (2 : ZMod 1245169507) ^ (1215985 + 1215985 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 1215985 * (2 : ZMod 1245169507) ^ 1215985) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 45172447 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 1245169507) ^ 4863943 = 844115303 := by
        calc
          (2 : ZMod 1245169507) ^ 4863943 = (2 : ZMod 1245169507) ^ (2431971 + 2431971 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 2431971 * (2 : ZMod 1245169507) ^ 2431971) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 844115303 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 1245169507) ^ 9727886 = 1074860789 := by
        calc
          (2 : ZMod 1245169507) ^ 9727886 = (2 : ZMod 1245169507) ^ (4863943 + 4863943) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 4863943 * (2 : ZMod 1245169507) ^ 4863943 := by rw [pow_add]
          _ = 1074860789 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 1245169507) ^ 19455773 = 1234624645 := by
        calc
          (2 : ZMod 1245169507) ^ 19455773 = (2 : ZMod 1245169507) ^ (9727886 + 9727886 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 9727886 * (2 : ZMod 1245169507) ^ 9727886) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 1234624645 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 1245169507) ^ 38911547 = 955247888 := by
        calc
          (2 : ZMod 1245169507) ^ 38911547 = (2 : ZMod 1245169507) ^ (19455773 + 19455773 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 19455773 * (2 : ZMod 1245169507) ^ 19455773) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 955247888 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 1245169507) ^ 77823094 = 178299661 := by
        calc
          (2 : ZMod 1245169507) ^ 77823094 = (2 : ZMod 1245169507) ^ (38911547 + 38911547) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 38911547 * (2 : ZMod 1245169507) ^ 38911547 := by rw [pow_add]
          _ = 178299661 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 1245169507) ^ 155646188 = 272374975 := by
        calc
          (2 : ZMod 1245169507) ^ 155646188 = (2 : ZMod 1245169507) ^ (77823094 + 77823094) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 77823094 * (2 : ZMod 1245169507) ^ 77823094 := by rw [pow_add]
          _ = 272374975 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 1245169507) ^ 311292376 = 127907910 := by
        calc
          (2 : ZMod 1245169507) ^ 311292376 = (2 : ZMod 1245169507) ^ (155646188 + 155646188) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 155646188 * (2 : ZMod 1245169507) ^ 155646188 := by rw [pow_add]
          _ = 127907910 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 1245169507) ^ 622584753 = 1245169506 := by
        calc
          (2 : ZMod 1245169507) ^ 622584753 = (2 : ZMod 1245169507) ^ (311292376 + 311292376 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 311292376 * (2 : ZMod 1245169507) ^ 311292376) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 1245169506 := by rw [factor_0_28]; decide
      change (2 : ZMod 1245169507) ^ 622584753 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (2 : ZMod 1245169507) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 1245169507) ^ 3 = 8 := by
        calc
          (2 : ZMod 1245169507) ^ 3 = (2 : ZMod 1245169507) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 1 * (2 : ZMod 1245169507) ^ 1) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 1245169507) ^ 6 = 64 := by
        calc
          (2 : ZMod 1245169507) ^ 6 = (2 : ZMod 1245169507) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 3 * (2 : ZMod 1245169507) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 1245169507) ^ 12 = 4096 := by
        calc
          (2 : ZMod 1245169507) ^ 12 = (2 : ZMod 1245169507) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 6 * (2 : ZMod 1245169507) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 1245169507) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 1245169507) ^ 24 = (2 : ZMod 1245169507) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 12 * (2 : ZMod 1245169507) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 1245169507) ^ 49 = 103120063 := by
        calc
          (2 : ZMod 1245169507) ^ 49 = (2 : ZMod 1245169507) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 24 * (2 : ZMod 1245169507) ^ 24) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 103120063 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 1245169507) ^ 98 = 1048513476 := by
        calc
          (2 : ZMod 1245169507) ^ 98 = (2 : ZMod 1245169507) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 49 * (2 : ZMod 1245169507) ^ 49 := by rw [pow_add]
          _ = 1048513476 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 1245169507) ^ 197 = 1145760336 := by
        calc
          (2 : ZMod 1245169507) ^ 197 = (2 : ZMod 1245169507) ^ (98 + 98 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 98 * (2 : ZMod 1245169507) ^ 98) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 1145760336 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 1245169507) ^ 395 = 161680658 := by
        calc
          (2 : ZMod 1245169507) ^ 395 = (2 : ZMod 1245169507) ^ (197 + 197 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 197 * (2 : ZMod 1245169507) ^ 197) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 161680658 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 1245169507) ^ 791 = 811280531 := by
        calc
          (2 : ZMod 1245169507) ^ 791 = (2 : ZMod 1245169507) ^ (395 + 395 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 395 * (2 : ZMod 1245169507) ^ 395) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 811280531 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 1245169507) ^ 1583 = 590749432 := by
        calc
          (2 : ZMod 1245169507) ^ 1583 = (2 : ZMod 1245169507) ^ (791 + 791 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 791 * (2 : ZMod 1245169507) ^ 791) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 590749432 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 1245169507) ^ 3166 = 963620694 := by
        calc
          (2 : ZMod 1245169507) ^ 3166 = (2 : ZMod 1245169507) ^ (1583 + 1583) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 1583 * (2 : ZMod 1245169507) ^ 1583 := by rw [pow_add]
          _ = 963620694 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 1245169507) ^ 6333 = 226444217 := by
        calc
          (2 : ZMod 1245169507) ^ 6333 = (2 : ZMod 1245169507) ^ (3166 + 3166 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 3166 * (2 : ZMod 1245169507) ^ 3166) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 226444217 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 1245169507) ^ 12666 = 366590514 := by
        calc
          (2 : ZMod 1245169507) ^ 12666 = (2 : ZMod 1245169507) ^ (6333 + 6333) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 6333 * (2 : ZMod 1245169507) ^ 6333 := by rw [pow_add]
          _ = 366590514 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 1245169507) ^ 25333 = 420136952 := by
        calc
          (2 : ZMod 1245169507) ^ 25333 = (2 : ZMod 1245169507) ^ (12666 + 12666 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 12666 * (2 : ZMod 1245169507) ^ 12666) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 420136952 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 1245169507) ^ 50666 = 956922270 := by
        calc
          (2 : ZMod 1245169507) ^ 50666 = (2 : ZMod 1245169507) ^ (25333 + 25333) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 25333 * (2 : ZMod 1245169507) ^ 25333 := by rw [pow_add]
          _ = 956922270 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 1245169507) ^ 101332 = 363612424 := by
        calc
          (2 : ZMod 1245169507) ^ 101332 = (2 : ZMod 1245169507) ^ (50666 + 50666) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 50666 * (2 : ZMod 1245169507) ^ 50666 := by rw [pow_add]
          _ = 363612424 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 1245169507) ^ 202664 = 240736615 := by
        calc
          (2 : ZMod 1245169507) ^ 202664 = (2 : ZMod 1245169507) ^ (101332 + 101332) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 101332 * (2 : ZMod 1245169507) ^ 101332 := by rw [pow_add]
          _ = 240736615 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 1245169507) ^ 405328 = 436083640 := by
        calc
          (2 : ZMod 1245169507) ^ 405328 = (2 : ZMod 1245169507) ^ (202664 + 202664) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 202664 * (2 : ZMod 1245169507) ^ 202664 := by rw [pow_add]
          _ = 436083640 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 1245169507) ^ 810657 = 806697891 := by
        calc
          (2 : ZMod 1245169507) ^ 810657 = (2 : ZMod 1245169507) ^ (405328 + 405328 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 405328 * (2 : ZMod 1245169507) ^ 405328) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 806697891 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 1245169507) ^ 1621314 = 1013252550 := by
        calc
          (2 : ZMod 1245169507) ^ 1621314 = (2 : ZMod 1245169507) ^ (810657 + 810657) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 810657 * (2 : ZMod 1245169507) ^ 810657 := by rw [pow_add]
          _ = 1013252550 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 1245169507) ^ 3242628 = 802914228 := by
        calc
          (2 : ZMod 1245169507) ^ 3242628 = (2 : ZMod 1245169507) ^ (1621314 + 1621314) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 1621314 * (2 : ZMod 1245169507) ^ 1621314 := by rw [pow_add]
          _ = 802914228 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 1245169507) ^ 6485257 = 939601989 := by
        calc
          (2 : ZMod 1245169507) ^ 6485257 = (2 : ZMod 1245169507) ^ (3242628 + 3242628 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 3242628 * (2 : ZMod 1245169507) ^ 3242628) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 939601989 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 1245169507) ^ 12970515 = 580458351 := by
        calc
          (2 : ZMod 1245169507) ^ 12970515 = (2 : ZMod 1245169507) ^ (6485257 + 6485257 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 6485257 * (2 : ZMod 1245169507) ^ 6485257) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 580458351 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 1245169507) ^ 25941031 = 925100263 := by
        calc
          (2 : ZMod 1245169507) ^ 25941031 = (2 : ZMod 1245169507) ^ (12970515 + 12970515 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 12970515 * (2 : ZMod 1245169507) ^ 12970515) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 925100263 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 1245169507) ^ 51882062 = 753704285 := by
        calc
          (2 : ZMod 1245169507) ^ 51882062 = (2 : ZMod 1245169507) ^ (25941031 + 25941031) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 25941031 * (2 : ZMod 1245169507) ^ 25941031 := by rw [pow_add]
          _ = 753704285 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 1245169507) ^ 103764125 = 82584630 := by
        calc
          (2 : ZMod 1245169507) ^ 103764125 = (2 : ZMod 1245169507) ^ (51882062 + 51882062 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 51882062 * (2 : ZMod 1245169507) ^ 51882062) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 82584630 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 1245169507) ^ 207528251 = 13344491 := by
        calc
          (2 : ZMod 1245169507) ^ 207528251 = (2 : ZMod 1245169507) ^ (103764125 + 103764125 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 103764125 * (2 : ZMod 1245169507) ^ 103764125) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 13344491 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 1245169507) ^ 415056502 = 13344490 := by
        calc
          (2 : ZMod 1245169507) ^ 415056502 = (2 : ZMod 1245169507) ^ (207528251 + 207528251) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 207528251 * (2 : ZMod 1245169507) ^ 207528251 := by rw [pow_add]
          _ = 13344490 := by rw [factor_1_27]; decide
      change (2 : ZMod 1245169507) ^ 415056502 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (2 : ZMod 1245169507) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 1245169507) ^ 2 = 4 := by
        calc
          (2 : ZMod 1245169507) ^ 2 = (2 : ZMod 1245169507) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 1 * (2 : ZMod 1245169507) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 1245169507) ^ 5 = 32 := by
        calc
          (2 : ZMod 1245169507) ^ 5 = (2 : ZMod 1245169507) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 2 * (2 : ZMod 1245169507) ^ 2) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 1245169507) ^ 10 = 1024 := by
        calc
          (2 : ZMod 1245169507) ^ 10 = (2 : ZMod 1245169507) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 5 * (2 : ZMod 1245169507) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 1245169507) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 1245169507) ^ 21 = (2 : ZMod 1245169507) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 10 * (2 : ZMod 1245169507) ^ 10) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 1245169507) ^ 42 = 107812380 := by
        calc
          (2 : ZMod 1245169507) ^ 42 = (2 : ZMod 1245169507) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 21 * (2 : ZMod 1245169507) ^ 21 := by rw [pow_add]
          _ = 107812380 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 1245169507) ^ 84 = 108590733 := by
        calc
          (2 : ZMod 1245169507) ^ 84 = (2 : ZMod 1245169507) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 42 * (2 : ZMod 1245169507) ^ 42 := by rw [pow_add]
          _ = 108590733 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 1245169507) ^ 169 = 612166422 := by
        calc
          (2 : ZMod 1245169507) ^ 169 = (2 : ZMod 1245169507) ^ (84 + 84 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 84 * (2 : ZMod 1245169507) ^ 84) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 612166422 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 1245169507) ^ 339 = 1033222158 := by
        calc
          (2 : ZMod 1245169507) ^ 339 = (2 : ZMod 1245169507) ^ (169 + 169 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 169 * (2 : ZMod 1245169507) ^ 169) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 1033222158 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 1245169507) ^ 678 = 1020279002 := by
        calc
          (2 : ZMod 1245169507) ^ 678 = (2 : ZMod 1245169507) ^ (339 + 339) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 339 * (2 : ZMod 1245169507) ^ 339 := by rw [pow_add]
          _ = 1020279002 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 1245169507) ^ 1357 = 344027801 := by
        calc
          (2 : ZMod 1245169507) ^ 1357 = (2 : ZMod 1245169507) ^ (678 + 678 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 678 * (2 : ZMod 1245169507) ^ 678) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 344027801 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 1245169507) ^ 2714 = 570184675 := by
        calc
          (2 : ZMod 1245169507) ^ 2714 = (2 : ZMod 1245169507) ^ (1357 + 1357) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 1357 * (2 : ZMod 1245169507) ^ 1357 := by rw [pow_add]
          _ = 570184675 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 1245169507) ^ 5428 = 432110587 := by
        calc
          (2 : ZMod 1245169507) ^ 5428 = (2 : ZMod 1245169507) ^ (2714 + 2714) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 2714 * (2 : ZMod 1245169507) ^ 2714 := by rw [pow_add]
          _ = 432110587 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 1245169507) ^ 10857 = 735510276 := by
        calc
          (2 : ZMod 1245169507) ^ 10857 = (2 : ZMod 1245169507) ^ (5428 + 5428 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 5428 * (2 : ZMod 1245169507) ^ 5428) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 735510276 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 1245169507) ^ 21714 = 793608678 := by
        calc
          (2 : ZMod 1245169507) ^ 21714 = (2 : ZMod 1245169507) ^ (10857 + 10857) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 10857 * (2 : ZMod 1245169507) ^ 10857 := by rw [pow_add]
          _ = 793608678 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 1245169507) ^ 43428 = 677733730 := by
        calc
          (2 : ZMod 1245169507) ^ 43428 = (2 : ZMod 1245169507) ^ (21714 + 21714) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 21714 * (2 : ZMod 1245169507) ^ 21714 := by rw [pow_add]
          _ = 677733730 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 1245169507) ^ 86856 = 1218254967 := by
        calc
          (2 : ZMod 1245169507) ^ 86856 = (2 : ZMod 1245169507) ^ (43428 + 43428) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 43428 * (2 : ZMod 1245169507) ^ 43428 := by rw [pow_add]
          _ = 1218254967 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 1245169507) ^ 173712 = 160680266 := by
        calc
          (2 : ZMod 1245169507) ^ 173712 = (2 : ZMod 1245169507) ^ (86856 + 86856) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 86856 * (2 : ZMod 1245169507) ^ 86856 := by rw [pow_add]
          _ = 160680266 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 1245169507) ^ 347424 = 189360741 := by
        calc
          (2 : ZMod 1245169507) ^ 347424 = (2 : ZMod 1245169507) ^ (173712 + 173712) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 173712 * (2 : ZMod 1245169507) ^ 173712 := by rw [pow_add]
          _ = 189360741 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 1245169507) ^ 694849 = 544412298 := by
        calc
          (2 : ZMod 1245169507) ^ 694849 = (2 : ZMod 1245169507) ^ (347424 + 347424 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 347424 * (2 : ZMod 1245169507) ^ 347424) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 544412298 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 1245169507) ^ 1389698 = 1023823380 := by
        calc
          (2 : ZMod 1245169507) ^ 1389698 = (2 : ZMod 1245169507) ^ (694849 + 694849) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 694849 * (2 : ZMod 1245169507) ^ 694849 := by rw [pow_add]
          _ = 1023823380 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 1245169507) ^ 2779396 = 1233508256 := by
        calc
          (2 : ZMod 1245169507) ^ 2779396 = (2 : ZMod 1245169507) ^ (1389698 + 1389698) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 1389698 * (2 : ZMod 1245169507) ^ 1389698 := by rw [pow_add]
          _ = 1233508256 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 1245169507) ^ 5558792 = 1058195038 := by
        calc
          (2 : ZMod 1245169507) ^ 5558792 = (2 : ZMod 1245169507) ^ (2779396 + 2779396) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 2779396 * (2 : ZMod 1245169507) ^ 2779396 := by rw [pow_add]
          _ = 1058195038 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 1245169507) ^ 11117584 = 759468555 := by
        calc
          (2 : ZMod 1245169507) ^ 11117584 = (2 : ZMod 1245169507) ^ (5558792 + 5558792) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 5558792 * (2 : ZMod 1245169507) ^ 5558792 := by rw [pow_add]
          _ = 759468555 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 1245169507) ^ 22235169 = 813048084 := by
        calc
          (2 : ZMod 1245169507) ^ 22235169 = (2 : ZMod 1245169507) ^ (11117584 + 11117584 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 11117584 * (2 : ZMod 1245169507) ^ 11117584) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 813048084 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 1245169507) ^ 44470339 = 531906702 := by
        calc
          (2 : ZMod 1245169507) ^ 44470339 = (2 : ZMod 1245169507) ^ (22235169 + 22235169 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 22235169 * (2 : ZMod 1245169507) ^ 22235169) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 531906702 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 1245169507) ^ 88940679 = 242494694 := by
        calc
          (2 : ZMod 1245169507) ^ 88940679 = (2 : ZMod 1245169507) ^ (44470339 + 44470339 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 44470339 * (2 : ZMod 1245169507) ^ 44470339) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 242494694 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 1245169507) ^ 177881358 = 20665063 := by
        calc
          (2 : ZMod 1245169507) ^ 177881358 = (2 : ZMod 1245169507) ^ (88940679 + 88940679) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 88940679 * (2 : ZMod 1245169507) ^ 88940679 := by rw [pow_add]
          _ = 20665063 := by rw [factor_2_26]; decide
      change (2 : ZMod 1245169507) ^ 177881358 ≠ 1
      rw [factor_2_27]
      decide
    ·
      have factor_3_0 : (2 : ZMod 1245169507) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 1245169507) ^ 2 = 4 := by
        calc
          (2 : ZMod 1245169507) ^ 2 = (2 : ZMod 1245169507) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 1 * (2 : ZMod 1245169507) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 1245169507) ^ 4 = 16 := by
        calc
          (2 : ZMod 1245169507) ^ 4 = (2 : ZMod 1245169507) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 2 * (2 : ZMod 1245169507) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 1245169507) ^ 8 = 256 := by
        calc
          (2 : ZMod 1245169507) ^ 8 = (2 : ZMod 1245169507) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 4 * (2 : ZMod 1245169507) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 1245169507) ^ 17 = 131072 := by
        calc
          (2 : ZMod 1245169507) ^ 17 = (2 : ZMod 1245169507) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 8 * (2 : ZMod 1245169507) ^ 8) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 1245169507) ^ 34 = 992665593 := by
        calc
          (2 : ZMod 1245169507) ^ 34 = (2 : ZMod 1245169507) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 17 * (2 : ZMod 1245169507) ^ 17 := by rw [pow_add]
          _ = 992665593 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 1245169507) ^ 68 = 596765711 := by
        calc
          (2 : ZMod 1245169507) ^ 68 = (2 : ZMod 1245169507) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 34 * (2 : ZMod 1245169507) ^ 34 := by rw [pow_add]
          _ = 596765711 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 1245169507) ^ 136 = 603455114 := by
        calc
          (2 : ZMod 1245169507) ^ 136 = (2 : ZMod 1245169507) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 68 * (2 : ZMod 1245169507) ^ 68 := by rw [pow_add]
          _ = 603455114 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 1245169507) ^ 273 = 1104560214 := by
        calc
          (2 : ZMod 1245169507) ^ 273 = (2 : ZMod 1245169507) ^ (136 + 136 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 136 * (2 : ZMod 1245169507) ^ 136) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 1104560214 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 1245169507) ^ 546 = 12421883 := by
        calc
          (2 : ZMod 1245169507) ^ 546 = (2 : ZMod 1245169507) ^ (273 + 273) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 273 * (2 : ZMod 1245169507) ^ 273 := by rw [pow_add]
          _ = 12421883 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 1245169507) ^ 1093 = 1053577484 := by
        calc
          (2 : ZMod 1245169507) ^ 1093 = (2 : ZMod 1245169507) ^ (546 + 546 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 546 * (2 : ZMod 1245169507) ^ 546) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 1053577484 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 1245169507) ^ 2187 = 442340615 := by
        calc
          (2 : ZMod 1245169507) ^ 2187 = (2 : ZMod 1245169507) ^ (1093 + 1093 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 1093 * (2 : ZMod 1245169507) ^ 1093) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 442340615 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 1245169507) ^ 4374 = 566234257 := by
        calc
          (2 : ZMod 1245169507) ^ 4374 = (2 : ZMod 1245169507) ^ (2187 + 2187) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 2187 * (2 : ZMod 1245169507) ^ 2187 := by rw [pow_add]
          _ = 566234257 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 1245169507) ^ 8748 = 1032626290 := by
        calc
          (2 : ZMod 1245169507) ^ 8748 = (2 : ZMod 1245169507) ^ (4374 + 4374) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 4374 * (2 : ZMod 1245169507) ^ 4374 := by rw [pow_add]
          _ = 1032626290 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 1245169507) ^ 17496 = 121547324 := by
        calc
          (2 : ZMod 1245169507) ^ 17496 = (2 : ZMod 1245169507) ^ (8748 + 8748) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 8748 * (2 : ZMod 1245169507) ^ 8748 := by rw [pow_add]
          _ = 121547324 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 1245169507) ^ 34992 = 56093012 := by
        calc
          (2 : ZMod 1245169507) ^ 34992 = (2 : ZMod 1245169507) ^ (17496 + 17496) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 17496 * (2 : ZMod 1245169507) ^ 17496 := by rw [pow_add]
          _ = 56093012 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 1245169507) ^ 69984 = 942146309 := by
        calc
          (2 : ZMod 1245169507) ^ 69984 = (2 : ZMod 1245169507) ^ (34992 + 34992) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 34992 * (2 : ZMod 1245169507) ^ 34992 := by rw [pow_add]
          _ = 942146309 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 1245169507) ^ 139969 = 1200506528 := by
        calc
          (2 : ZMod 1245169507) ^ 139969 = (2 : ZMod 1245169507) ^ (69984 + 69984 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 69984 * (2 : ZMod 1245169507) ^ 69984) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 1200506528 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 1245169507) ^ 279939 = 440456658 := by
        calc
          (2 : ZMod 1245169507) ^ 279939 = (2 : ZMod 1245169507) ^ (139969 + 139969 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 139969 * (2 : ZMod 1245169507) ^ 139969) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 440456658 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 1245169507) ^ 559878 = 206803277 := by
        calc
          (2 : ZMod 1245169507) ^ 559878 = (2 : ZMod 1245169507) ^ (279939 + 279939) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 279939 * (2 : ZMod 1245169507) ^ 279939 := by rw [pow_add]
          _ = 206803277 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 1245169507) ^ 1119756 = 1129063594 := by
        calc
          (2 : ZMod 1245169507) ^ 1119756 = (2 : ZMod 1245169507) ^ (559878 + 559878) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 559878 * (2 : ZMod 1245169507) ^ 559878 := by rw [pow_add]
          _ = 1129063594 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 1245169507) ^ 2239513 = 83672389 := by
        calc
          (2 : ZMod 1245169507) ^ 2239513 = (2 : ZMod 1245169507) ^ (1119756 + 1119756 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 1119756 * (2 : ZMod 1245169507) ^ 1119756) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 83672389 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 1245169507) ^ 4479027 = 802750987 := by
        calc
          (2 : ZMod 1245169507) ^ 4479027 = (2 : ZMod 1245169507) ^ (2239513 + 2239513 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 2239513 * (2 : ZMod 1245169507) ^ 2239513) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 802750987 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 1245169507) ^ 8958054 = 123416940 := by
        calc
          (2 : ZMod 1245169507) ^ 8958054 = (2 : ZMod 1245169507) ^ (4479027 + 4479027) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 4479027 * (2 : ZMod 1245169507) ^ 4479027 := by rw [pow_add]
          _ = 123416940 := by rw [factor_3_22]; decide
      change (2 : ZMod 1245169507) ^ 8958054 ≠ 1
      rw [factor_3_23]
      decide
    ·
      have factor_4_0 : (2 : ZMod 1245169507) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 1245169507) ^ 2 = 4 := by
        calc
          (2 : ZMod 1245169507) ^ 2 = (2 : ZMod 1245169507) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 1 * (2 : ZMod 1245169507) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 1245169507) ^ 5 = 32 := by
        calc
          (2 : ZMod 1245169507) ^ 5 = (2 : ZMod 1245169507) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 2 * (2 : ZMod 1245169507) ^ 2) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 1245169507) ^ 11 = 2048 := by
        calc
          (2 : ZMod 1245169507) ^ 11 = (2 : ZMod 1245169507) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 5 * (2 : ZMod 1245169507) ^ 5) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 1245169507) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 1245169507) ^ 22 = (2 : ZMod 1245169507) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 11 * (2 : ZMod 1245169507) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 1245169507) ^ 45 = 862499040 := by
        calc
          (2 : ZMod 1245169507) ^ 45 = (2 : ZMod 1245169507) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 22 * (2 : ZMod 1245169507) ^ 22) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 862499040 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 1245169507) ^ 91 = 202749247 := by
        calc
          (2 : ZMod 1245169507) ^ 91 = (2 : ZMod 1245169507) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 45 * (2 : ZMod 1245169507) ^ 45) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 202749247 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 1245169507) ^ 182 = 569724335 := by
        calc
          (2 : ZMod 1245169507) ^ 182 = (2 : ZMod 1245169507) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 91 * (2 : ZMod 1245169507) ^ 91 := by rw [pow_add]
          _ = 569724335 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 1245169507) ^ 364 = 277934662 := by
        calc
          (2 : ZMod 1245169507) ^ 364 = (2 : ZMod 1245169507) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 182 * (2 : ZMod 1245169507) ^ 182 := by rw [pow_add]
          _ = 277934662 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 1245169507) ^ 729 = 1017427675 := by
        calc
          (2 : ZMod 1245169507) ^ 729 = (2 : ZMod 1245169507) ^ (364 + 364 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 364 * (2 : ZMod 1245169507) ^ 364) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 1017427675 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 1245169507) ^ 1459 = 692376874 := by
        calc
          (2 : ZMod 1245169507) ^ 1459 = (2 : ZMod 1245169507) ^ (729 + 729 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 729 * (2 : ZMod 1245169507) ^ 729) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 692376874 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 1245169507) ^ 2919 = 802000628 := by
        calc
          (2 : ZMod 1245169507) ^ 2919 = (2 : ZMod 1245169507) ^ (1459 + 1459 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = ((2 : ZMod 1245169507) ^ 1459 * (2 : ZMod 1245169507) ^ 1459) * (2 : ZMod 1245169507) := by rw [pow_succ, pow_add]
          _ = 802000628 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 1245169507) ^ 5838 = 232911998 := by
        calc
          (2 : ZMod 1245169507) ^ 5838 = (2 : ZMod 1245169507) ^ (2919 + 2919) :=
            congrArg (fun n : ℕ => (2 : ZMod 1245169507) ^ n) (by norm_num)
          _ = (2 : ZMod 1245169507) ^ 2919 * (2 : ZMod 1245169507) ^ 2919 := by rw [pow_add]
          _ = 232911998 := by rw [factor_4_11]; decide
      change (2 : ZMod 1245169507) ^ 5838 ≠ 1
      rw [factor_4_12]
      decide

#print axioms prime_lucas_1245169507

end TotientTailPeriodKiller
end Erdos249257
