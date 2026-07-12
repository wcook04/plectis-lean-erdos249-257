import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_232908956281 : Nat.Prime 232908956281 := by
  apply lucas_primality 232908956281 (47 : ZMod 232908956281)
  ·
      have fermat_0 : (47 : ZMod 232908956281) ^ 1 = 47 := by norm_num
      have fermat_1 : (47 : ZMod 232908956281) ^ 3 = 103823 := by
        calc
          (47 : ZMod 232908956281) ^ 3 = (47 : ZMod 232908956281) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 1 * (47 : ZMod 232908956281) ^ 1) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [fermat_0]; decide
      have fermat_2 : (47 : ZMod 232908956281) ^ 6 = 10779215329 := by
        calc
          (47 : ZMod 232908956281) ^ 6 = (47 : ZMod 232908956281) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 3 * (47 : ZMod 232908956281) ^ 3 := by rw [pow_add]
          _ = 10779215329 := by rw [fermat_1]; decide
      have fermat_3 : (47 : ZMod 232908956281) ^ 13 = 168203723205 := by
        calc
          (47 : ZMod 232908956281) ^ 13 = (47 : ZMod 232908956281) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 6 * (47 : ZMod 232908956281) ^ 6) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 168203723205 := by rw [fermat_2]; decide
      have fermat_4 : (47 : ZMod 232908956281) ^ 27 = 181978832891 := by
        calc
          (47 : ZMod 232908956281) ^ 27 = (47 : ZMod 232908956281) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 13 * (47 : ZMod 232908956281) ^ 13) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 181978832891 := by rw [fermat_3]; decide
      have fermat_5 : (47 : ZMod 232908956281) ^ 54 = 226213085133 := by
        calc
          (47 : ZMod 232908956281) ^ 54 = (47 : ZMod 232908956281) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 27 * (47 : ZMod 232908956281) ^ 27 := by rw [pow_add]
          _ = 226213085133 := by rw [fermat_4]; decide
      have fermat_6 : (47 : ZMod 232908956281) ^ 108 = 29635088162 := by
        calc
          (47 : ZMod 232908956281) ^ 108 = (47 : ZMod 232908956281) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 54 * (47 : ZMod 232908956281) ^ 54 := by rw [pow_add]
          _ = 29635088162 := by rw [fermat_5]; decide
      have fermat_7 : (47 : ZMod 232908956281) ^ 216 = 79563299590 := by
        calc
          (47 : ZMod 232908956281) ^ 216 = (47 : ZMod 232908956281) ^ (108 + 108) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 108 * (47 : ZMod 232908956281) ^ 108 := by rw [pow_add]
          _ = 79563299590 := by rw [fermat_6]; decide
      have fermat_8 : (47 : ZMod 232908956281) ^ 433 = 111540651209 := by
        calc
          (47 : ZMod 232908956281) ^ 433 = (47 : ZMod 232908956281) ^ (216 + 216 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 216 * (47 : ZMod 232908956281) ^ 216) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 111540651209 := by rw [fermat_7]; decide
      have fermat_9 : (47 : ZMod 232908956281) ^ 867 = 155972037641 := by
        calc
          (47 : ZMod 232908956281) ^ 867 = (47 : ZMod 232908956281) ^ (433 + 433 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 433 * (47 : ZMod 232908956281) ^ 433) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 155972037641 := by rw [fermat_8]; decide
      have fermat_10 : (47 : ZMod 232908956281) ^ 1735 = 78950900782 := by
        calc
          (47 : ZMod 232908956281) ^ 1735 = (47 : ZMod 232908956281) ^ (867 + 867 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 867 * (47 : ZMod 232908956281) ^ 867) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 78950900782 := by rw [fermat_9]; decide
      have fermat_11 : (47 : ZMod 232908956281) ^ 3470 = 25626091601 := by
        calc
          (47 : ZMod 232908956281) ^ 3470 = (47 : ZMod 232908956281) ^ (1735 + 1735) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1735 * (47 : ZMod 232908956281) ^ 1735 := by rw [pow_add]
          _ = 25626091601 := by rw [fermat_10]; decide
      have fermat_12 : (47 : ZMod 232908956281) ^ 6941 = 218584115726 := by
        calc
          (47 : ZMod 232908956281) ^ 6941 = (47 : ZMod 232908956281) ^ (3470 + 3470 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 3470 * (47 : ZMod 232908956281) ^ 3470) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 218584115726 := by rw [fermat_11]; decide
      have fermat_13 : (47 : ZMod 232908956281) ^ 13882 = 37935382773 := by
        calc
          (47 : ZMod 232908956281) ^ 13882 = (47 : ZMod 232908956281) ^ (6941 + 6941) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 6941 * (47 : ZMod 232908956281) ^ 6941 := by rw [pow_add]
          _ = 37935382773 := by rw [fermat_12]; decide
      have fermat_14 : (47 : ZMod 232908956281) ^ 27764 = 29600230849 := by
        calc
          (47 : ZMod 232908956281) ^ 27764 = (47 : ZMod 232908956281) ^ (13882 + 13882) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 13882 * (47 : ZMod 232908956281) ^ 13882 := by rw [pow_add]
          _ = 29600230849 := by rw [fermat_13]; decide
      have fermat_15 : (47 : ZMod 232908956281) ^ 55529 = 134319552928 := by
        calc
          (47 : ZMod 232908956281) ^ 55529 = (47 : ZMod 232908956281) ^ (27764 + 27764 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 27764 * (47 : ZMod 232908956281) ^ 27764) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 134319552928 := by rw [fermat_14]; decide
      have fermat_16 : (47 : ZMod 232908956281) ^ 111059 = 223091901528 := by
        calc
          (47 : ZMod 232908956281) ^ 111059 = (47 : ZMod 232908956281) ^ (55529 + 55529 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 55529 * (47 : ZMod 232908956281) ^ 55529) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 223091901528 := by rw [fermat_15]; decide
      have fermat_17 : (47 : ZMod 232908956281) ^ 222119 = 13596402118 := by
        calc
          (47 : ZMod 232908956281) ^ 222119 = (47 : ZMod 232908956281) ^ (111059 + 111059 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 111059 * (47 : ZMod 232908956281) ^ 111059) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 13596402118 := by rw [fermat_16]; decide
      have fermat_18 : (47 : ZMod 232908956281) ^ 444238 = 99825140718 := by
        calc
          (47 : ZMod 232908956281) ^ 444238 = (47 : ZMod 232908956281) ^ (222119 + 222119) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 222119 * (47 : ZMod 232908956281) ^ 222119 := by rw [pow_add]
          _ = 99825140718 := by rw [fermat_17]; decide
      have fermat_19 : (47 : ZMod 232908956281) ^ 888477 = 169045395223 := by
        calc
          (47 : ZMod 232908956281) ^ 888477 = (47 : ZMod 232908956281) ^ (444238 + 444238 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 444238 * (47 : ZMod 232908956281) ^ 444238) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 169045395223 := by rw [fermat_18]; decide
      have fermat_20 : (47 : ZMod 232908956281) ^ 1776954 = 119293223100 := by
        calc
          (47 : ZMod 232908956281) ^ 1776954 = (47 : ZMod 232908956281) ^ (888477 + 888477) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 888477 * (47 : ZMod 232908956281) ^ 888477 := by rw [pow_add]
          _ = 119293223100 := by rw [fermat_19]; decide
      have fermat_21 : (47 : ZMod 232908956281) ^ 3553908 = 10343591130 := by
        calc
          (47 : ZMod 232908956281) ^ 3553908 = (47 : ZMod 232908956281) ^ (1776954 + 1776954) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1776954 * (47 : ZMod 232908956281) ^ 1776954 := by rw [pow_add]
          _ = 10343591130 := by rw [fermat_20]; decide
      have fermat_22 : (47 : ZMod 232908956281) ^ 7107817 = 143042444008 := by
        calc
          (47 : ZMod 232908956281) ^ 7107817 = (47 : ZMod 232908956281) ^ (3553908 + 3553908 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 3553908 * (47 : ZMod 232908956281) ^ 3553908) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 143042444008 := by rw [fermat_21]; decide
      have fermat_23 : (47 : ZMod 232908956281) ^ 14215634 = 54488117353 := by
        calc
          (47 : ZMod 232908956281) ^ 14215634 = (47 : ZMod 232908956281) ^ (7107817 + 7107817) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 7107817 * (47 : ZMod 232908956281) ^ 7107817 := by rw [pow_add]
          _ = 54488117353 := by rw [fermat_22]; decide
      have fermat_24 : (47 : ZMod 232908956281) ^ 28431269 = 55673092035 := by
        calc
          (47 : ZMod 232908956281) ^ 28431269 = (47 : ZMod 232908956281) ^ (14215634 + 14215634 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 14215634 * (47 : ZMod 232908956281) ^ 14215634) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 55673092035 := by rw [fermat_23]; decide
      have fermat_25 : (47 : ZMod 232908956281) ^ 56862538 = 158532541260 := by
        calc
          (47 : ZMod 232908956281) ^ 56862538 = (47 : ZMod 232908956281) ^ (28431269 + 28431269) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 28431269 * (47 : ZMod 232908956281) ^ 28431269 := by rw [pow_add]
          _ = 158532541260 := by rw [fermat_24]; decide
      have fermat_26 : (47 : ZMod 232908956281) ^ 113725076 = 168718772169 := by
        calc
          (47 : ZMod 232908956281) ^ 113725076 = (47 : ZMod 232908956281) ^ (56862538 + 56862538) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 56862538 * (47 : ZMod 232908956281) ^ 56862538 := by rw [pow_add]
          _ = 168718772169 := by rw [fermat_25]; decide
      have fermat_27 : (47 : ZMod 232908956281) ^ 227450152 = 223270325603 := by
        calc
          (47 : ZMod 232908956281) ^ 227450152 = (47 : ZMod 232908956281) ^ (113725076 + 113725076) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 113725076 * (47 : ZMod 232908956281) ^ 113725076 := by rw [pow_add]
          _ = 223270325603 := by rw [fermat_26]; decide
      have fermat_28 : (47 : ZMod 232908956281) ^ 454900305 = 83366640799 := by
        calc
          (47 : ZMod 232908956281) ^ 454900305 = (47 : ZMod 232908956281) ^ (227450152 + 227450152 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 227450152 * (47 : ZMod 232908956281) ^ 227450152) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 83366640799 := by rw [fermat_27]; decide
      have fermat_29 : (47 : ZMod 232908956281) ^ 909800610 = 85264249126 := by
        calc
          (47 : ZMod 232908956281) ^ 909800610 = (47 : ZMod 232908956281) ^ (454900305 + 454900305) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 454900305 * (47 : ZMod 232908956281) ^ 454900305 := by rw [pow_add]
          _ = 85264249126 := by rw [fermat_28]; decide
      have fermat_30 : (47 : ZMod 232908956281) ^ 1819601220 = 46192232059 := by
        calc
          (47 : ZMod 232908956281) ^ 1819601220 = (47 : ZMod 232908956281) ^ (909800610 + 909800610) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 909800610 * (47 : ZMod 232908956281) ^ 909800610 := by rw [pow_add]
          _ = 46192232059 := by rw [fermat_29]; decide
      have fermat_31 : (47 : ZMod 232908956281) ^ 3639202441 = 139608764461 := by
        calc
          (47 : ZMod 232908956281) ^ 3639202441 = (47 : ZMod 232908956281) ^ (1819601220 + 1819601220 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 1819601220 * (47 : ZMod 232908956281) ^ 1819601220) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 139608764461 := by rw [fermat_30]; decide
      have fermat_32 : (47 : ZMod 232908956281) ^ 7278404883 = 216611291832 := by
        calc
          (47 : ZMod 232908956281) ^ 7278404883 = (47 : ZMod 232908956281) ^ (3639202441 + 3639202441 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 3639202441 * (47 : ZMod 232908956281) ^ 3639202441) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 216611291832 := by rw [fermat_31]; decide
      have fermat_33 : (47 : ZMod 232908956281) ^ 14556809767 = 48847870 := by
        calc
          (47 : ZMod 232908956281) ^ 14556809767 = (47 : ZMod 232908956281) ^ (7278404883 + 7278404883 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 7278404883 * (47 : ZMod 232908956281) ^ 7278404883) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 48847870 := by rw [fermat_32]; decide
      have fermat_34 : (47 : ZMod 232908956281) ^ 29113619535 = 84154238833 := by
        calc
          (47 : ZMod 232908956281) ^ 29113619535 = (47 : ZMod 232908956281) ^ (14556809767 + 14556809767 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 14556809767 * (47 : ZMod 232908956281) ^ 14556809767) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 84154238833 := by rw [fermat_33]; decide
      have fermat_35 : (47 : ZMod 232908956281) ^ 58227239070 = 98535743245 := by
        calc
          (47 : ZMod 232908956281) ^ 58227239070 = (47 : ZMod 232908956281) ^ (29113619535 + 29113619535) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 29113619535 * (47 : ZMod 232908956281) ^ 29113619535 := by rw [pow_add]
          _ = 98535743245 := by rw [fermat_34]; decide
      have fermat_36 : (47 : ZMod 232908956281) ^ 116454478140 = 232908956280 := by
        calc
          (47 : ZMod 232908956281) ^ 116454478140 = (47 : ZMod 232908956281) ^ (58227239070 + 58227239070) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 58227239070 * (47 : ZMod 232908956281) ^ 58227239070 := by rw [pow_add]
          _ = 232908956280 := by rw [fermat_35]; decide
      have fermat_37 : (47 : ZMod 232908956281) ^ 232908956280 = 1 := by
        calc
          (47 : ZMod 232908956281) ^ 232908956280 = (47 : ZMod 232908956281) ^ (116454478140 + 116454478140) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 116454478140 * (47 : ZMod 232908956281) ^ 116454478140 := by rw [pow_add]
          _ = 1 := by rw [fermat_36]; decide
      simpa using fermat_37
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod = 232908956281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (47 : ZMod 232908956281) ^ 1 = 47 := by norm_num
      have factor_0_1 : (47 : ZMod 232908956281) ^ 3 = 103823 := by
        calc
          (47 : ZMod 232908956281) ^ 3 = (47 : ZMod 232908956281) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 1 * (47 : ZMod 232908956281) ^ 1) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_0_0]; decide
      have factor_0_2 : (47 : ZMod 232908956281) ^ 6 = 10779215329 := by
        calc
          (47 : ZMod 232908956281) ^ 6 = (47 : ZMod 232908956281) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 3 * (47 : ZMod 232908956281) ^ 3 := by rw [pow_add]
          _ = 10779215329 := by rw [factor_0_1]; decide
      have factor_0_3 : (47 : ZMod 232908956281) ^ 13 = 168203723205 := by
        calc
          (47 : ZMod 232908956281) ^ 13 = (47 : ZMod 232908956281) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 6 * (47 : ZMod 232908956281) ^ 6) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 168203723205 := by rw [factor_0_2]; decide
      have factor_0_4 : (47 : ZMod 232908956281) ^ 27 = 181978832891 := by
        calc
          (47 : ZMod 232908956281) ^ 27 = (47 : ZMod 232908956281) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 13 * (47 : ZMod 232908956281) ^ 13) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 181978832891 := by rw [factor_0_3]; decide
      have factor_0_5 : (47 : ZMod 232908956281) ^ 54 = 226213085133 := by
        calc
          (47 : ZMod 232908956281) ^ 54 = (47 : ZMod 232908956281) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 27 * (47 : ZMod 232908956281) ^ 27 := by rw [pow_add]
          _ = 226213085133 := by rw [factor_0_4]; decide
      have factor_0_6 : (47 : ZMod 232908956281) ^ 108 = 29635088162 := by
        calc
          (47 : ZMod 232908956281) ^ 108 = (47 : ZMod 232908956281) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 54 * (47 : ZMod 232908956281) ^ 54 := by rw [pow_add]
          _ = 29635088162 := by rw [factor_0_5]; decide
      have factor_0_7 : (47 : ZMod 232908956281) ^ 216 = 79563299590 := by
        calc
          (47 : ZMod 232908956281) ^ 216 = (47 : ZMod 232908956281) ^ (108 + 108) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 108 * (47 : ZMod 232908956281) ^ 108 := by rw [pow_add]
          _ = 79563299590 := by rw [factor_0_6]; decide
      have factor_0_8 : (47 : ZMod 232908956281) ^ 433 = 111540651209 := by
        calc
          (47 : ZMod 232908956281) ^ 433 = (47 : ZMod 232908956281) ^ (216 + 216 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 216 * (47 : ZMod 232908956281) ^ 216) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 111540651209 := by rw [factor_0_7]; decide
      have factor_0_9 : (47 : ZMod 232908956281) ^ 867 = 155972037641 := by
        calc
          (47 : ZMod 232908956281) ^ 867 = (47 : ZMod 232908956281) ^ (433 + 433 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 433 * (47 : ZMod 232908956281) ^ 433) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 155972037641 := by rw [factor_0_8]; decide
      have factor_0_10 : (47 : ZMod 232908956281) ^ 1735 = 78950900782 := by
        calc
          (47 : ZMod 232908956281) ^ 1735 = (47 : ZMod 232908956281) ^ (867 + 867 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 867 * (47 : ZMod 232908956281) ^ 867) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 78950900782 := by rw [factor_0_9]; decide
      have factor_0_11 : (47 : ZMod 232908956281) ^ 3470 = 25626091601 := by
        calc
          (47 : ZMod 232908956281) ^ 3470 = (47 : ZMod 232908956281) ^ (1735 + 1735) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1735 * (47 : ZMod 232908956281) ^ 1735 := by rw [pow_add]
          _ = 25626091601 := by rw [factor_0_10]; decide
      have factor_0_12 : (47 : ZMod 232908956281) ^ 6941 = 218584115726 := by
        calc
          (47 : ZMod 232908956281) ^ 6941 = (47 : ZMod 232908956281) ^ (3470 + 3470 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 3470 * (47 : ZMod 232908956281) ^ 3470) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 218584115726 := by rw [factor_0_11]; decide
      have factor_0_13 : (47 : ZMod 232908956281) ^ 13882 = 37935382773 := by
        calc
          (47 : ZMod 232908956281) ^ 13882 = (47 : ZMod 232908956281) ^ (6941 + 6941) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 6941 * (47 : ZMod 232908956281) ^ 6941 := by rw [pow_add]
          _ = 37935382773 := by rw [factor_0_12]; decide
      have factor_0_14 : (47 : ZMod 232908956281) ^ 27764 = 29600230849 := by
        calc
          (47 : ZMod 232908956281) ^ 27764 = (47 : ZMod 232908956281) ^ (13882 + 13882) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 13882 * (47 : ZMod 232908956281) ^ 13882 := by rw [pow_add]
          _ = 29600230849 := by rw [factor_0_13]; decide
      have factor_0_15 : (47 : ZMod 232908956281) ^ 55529 = 134319552928 := by
        calc
          (47 : ZMod 232908956281) ^ 55529 = (47 : ZMod 232908956281) ^ (27764 + 27764 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 27764 * (47 : ZMod 232908956281) ^ 27764) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 134319552928 := by rw [factor_0_14]; decide
      have factor_0_16 : (47 : ZMod 232908956281) ^ 111059 = 223091901528 := by
        calc
          (47 : ZMod 232908956281) ^ 111059 = (47 : ZMod 232908956281) ^ (55529 + 55529 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 55529 * (47 : ZMod 232908956281) ^ 55529) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 223091901528 := by rw [factor_0_15]; decide
      have factor_0_17 : (47 : ZMod 232908956281) ^ 222119 = 13596402118 := by
        calc
          (47 : ZMod 232908956281) ^ 222119 = (47 : ZMod 232908956281) ^ (111059 + 111059 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 111059 * (47 : ZMod 232908956281) ^ 111059) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 13596402118 := by rw [factor_0_16]; decide
      have factor_0_18 : (47 : ZMod 232908956281) ^ 444238 = 99825140718 := by
        calc
          (47 : ZMod 232908956281) ^ 444238 = (47 : ZMod 232908956281) ^ (222119 + 222119) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 222119 * (47 : ZMod 232908956281) ^ 222119 := by rw [pow_add]
          _ = 99825140718 := by rw [factor_0_17]; decide
      have factor_0_19 : (47 : ZMod 232908956281) ^ 888477 = 169045395223 := by
        calc
          (47 : ZMod 232908956281) ^ 888477 = (47 : ZMod 232908956281) ^ (444238 + 444238 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 444238 * (47 : ZMod 232908956281) ^ 444238) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 169045395223 := by rw [factor_0_18]; decide
      have factor_0_20 : (47 : ZMod 232908956281) ^ 1776954 = 119293223100 := by
        calc
          (47 : ZMod 232908956281) ^ 1776954 = (47 : ZMod 232908956281) ^ (888477 + 888477) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 888477 * (47 : ZMod 232908956281) ^ 888477 := by rw [pow_add]
          _ = 119293223100 := by rw [factor_0_19]; decide
      have factor_0_21 : (47 : ZMod 232908956281) ^ 3553908 = 10343591130 := by
        calc
          (47 : ZMod 232908956281) ^ 3553908 = (47 : ZMod 232908956281) ^ (1776954 + 1776954) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1776954 * (47 : ZMod 232908956281) ^ 1776954 := by rw [pow_add]
          _ = 10343591130 := by rw [factor_0_20]; decide
      have factor_0_22 : (47 : ZMod 232908956281) ^ 7107817 = 143042444008 := by
        calc
          (47 : ZMod 232908956281) ^ 7107817 = (47 : ZMod 232908956281) ^ (3553908 + 3553908 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 3553908 * (47 : ZMod 232908956281) ^ 3553908) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 143042444008 := by rw [factor_0_21]; decide
      have factor_0_23 : (47 : ZMod 232908956281) ^ 14215634 = 54488117353 := by
        calc
          (47 : ZMod 232908956281) ^ 14215634 = (47 : ZMod 232908956281) ^ (7107817 + 7107817) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 7107817 * (47 : ZMod 232908956281) ^ 7107817 := by rw [pow_add]
          _ = 54488117353 := by rw [factor_0_22]; decide
      have factor_0_24 : (47 : ZMod 232908956281) ^ 28431269 = 55673092035 := by
        calc
          (47 : ZMod 232908956281) ^ 28431269 = (47 : ZMod 232908956281) ^ (14215634 + 14215634 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 14215634 * (47 : ZMod 232908956281) ^ 14215634) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 55673092035 := by rw [factor_0_23]; decide
      have factor_0_25 : (47 : ZMod 232908956281) ^ 56862538 = 158532541260 := by
        calc
          (47 : ZMod 232908956281) ^ 56862538 = (47 : ZMod 232908956281) ^ (28431269 + 28431269) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 28431269 * (47 : ZMod 232908956281) ^ 28431269 := by rw [pow_add]
          _ = 158532541260 := by rw [factor_0_24]; decide
      have factor_0_26 : (47 : ZMod 232908956281) ^ 113725076 = 168718772169 := by
        calc
          (47 : ZMod 232908956281) ^ 113725076 = (47 : ZMod 232908956281) ^ (56862538 + 56862538) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 56862538 * (47 : ZMod 232908956281) ^ 56862538 := by rw [pow_add]
          _ = 168718772169 := by rw [factor_0_25]; decide
      have factor_0_27 : (47 : ZMod 232908956281) ^ 227450152 = 223270325603 := by
        calc
          (47 : ZMod 232908956281) ^ 227450152 = (47 : ZMod 232908956281) ^ (113725076 + 113725076) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 113725076 * (47 : ZMod 232908956281) ^ 113725076 := by rw [pow_add]
          _ = 223270325603 := by rw [factor_0_26]; decide
      have factor_0_28 : (47 : ZMod 232908956281) ^ 454900305 = 83366640799 := by
        calc
          (47 : ZMod 232908956281) ^ 454900305 = (47 : ZMod 232908956281) ^ (227450152 + 227450152 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 227450152 * (47 : ZMod 232908956281) ^ 227450152) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 83366640799 := by rw [factor_0_27]; decide
      have factor_0_29 : (47 : ZMod 232908956281) ^ 909800610 = 85264249126 := by
        calc
          (47 : ZMod 232908956281) ^ 909800610 = (47 : ZMod 232908956281) ^ (454900305 + 454900305) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 454900305 * (47 : ZMod 232908956281) ^ 454900305 := by rw [pow_add]
          _ = 85264249126 := by rw [factor_0_28]; decide
      have factor_0_30 : (47 : ZMod 232908956281) ^ 1819601220 = 46192232059 := by
        calc
          (47 : ZMod 232908956281) ^ 1819601220 = (47 : ZMod 232908956281) ^ (909800610 + 909800610) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 909800610 * (47 : ZMod 232908956281) ^ 909800610 := by rw [pow_add]
          _ = 46192232059 := by rw [factor_0_29]; decide
      have factor_0_31 : (47 : ZMod 232908956281) ^ 3639202441 = 139608764461 := by
        calc
          (47 : ZMod 232908956281) ^ 3639202441 = (47 : ZMod 232908956281) ^ (1819601220 + 1819601220 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 1819601220 * (47 : ZMod 232908956281) ^ 1819601220) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 139608764461 := by rw [factor_0_30]; decide
      have factor_0_32 : (47 : ZMod 232908956281) ^ 7278404883 = 216611291832 := by
        calc
          (47 : ZMod 232908956281) ^ 7278404883 = (47 : ZMod 232908956281) ^ (3639202441 + 3639202441 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 3639202441 * (47 : ZMod 232908956281) ^ 3639202441) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 216611291832 := by rw [factor_0_31]; decide
      have factor_0_33 : (47 : ZMod 232908956281) ^ 14556809767 = 48847870 := by
        calc
          (47 : ZMod 232908956281) ^ 14556809767 = (47 : ZMod 232908956281) ^ (7278404883 + 7278404883 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 7278404883 * (47 : ZMod 232908956281) ^ 7278404883) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 48847870 := by rw [factor_0_32]; decide
      have factor_0_34 : (47 : ZMod 232908956281) ^ 29113619535 = 84154238833 := by
        calc
          (47 : ZMod 232908956281) ^ 29113619535 = (47 : ZMod 232908956281) ^ (14556809767 + 14556809767 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 14556809767 * (47 : ZMod 232908956281) ^ 14556809767) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 84154238833 := by rw [factor_0_33]; decide
      have factor_0_35 : (47 : ZMod 232908956281) ^ 58227239070 = 98535743245 := by
        calc
          (47 : ZMod 232908956281) ^ 58227239070 = (47 : ZMod 232908956281) ^ (29113619535 + 29113619535) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 29113619535 * (47 : ZMod 232908956281) ^ 29113619535 := by rw [pow_add]
          _ = 98535743245 := by rw [factor_0_34]; decide
      have factor_0_36 : (47 : ZMod 232908956281) ^ 116454478140 = 232908956280 := by
        calc
          (47 : ZMod 232908956281) ^ 116454478140 = (47 : ZMod 232908956281) ^ (58227239070 + 58227239070) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 58227239070 * (47 : ZMod 232908956281) ^ 58227239070 := by rw [pow_add]
          _ = 232908956280 := by rw [factor_0_35]; decide
      change (47 : ZMod 232908956281) ^ 116454478140 ≠ 1
      rw [factor_0_36]
      decide
    ·
      have factor_1_0 : (47 : ZMod 232908956281) ^ 1 = 47 := by norm_num
      have factor_1_1 : (47 : ZMod 232908956281) ^ 2 = 2209 := by
        calc
          (47 : ZMod 232908956281) ^ 2 = (47 : ZMod 232908956281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1 * (47 : ZMod 232908956281) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_1_0]; decide
      have factor_1_2 : (47 : ZMod 232908956281) ^ 4 = 4879681 := by
        calc
          (47 : ZMod 232908956281) ^ 4 = (47 : ZMod 232908956281) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 2 * (47 : ZMod 232908956281) ^ 2 := by rw [pow_add]
          _ = 4879681 := by rw [factor_1_1]; decide
      have factor_1_3 : (47 : ZMod 232908956281) ^ 9 = 2938172562 := by
        calc
          (47 : ZMod 232908956281) ^ 9 = (47 : ZMod 232908956281) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 4 * (47 : ZMod 232908956281) ^ 4) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 2938172562 := by rw [factor_1_2]; decide
      have factor_1_4 : (47 : ZMod 232908956281) ^ 18 = 198675773469 := by
        calc
          (47 : ZMod 232908956281) ^ 18 = (47 : ZMod 232908956281) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 9 * (47 : ZMod 232908956281) ^ 9 := by rw [pow_add]
          _ = 198675773469 := by rw [factor_1_3]; decide
      have factor_1_5 : (47 : ZMod 232908956281) ^ 36 = 199131802830 := by
        calc
          (47 : ZMod 232908956281) ^ 36 = (47 : ZMod 232908956281) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 18 * (47 : ZMod 232908956281) ^ 18 := by rw [pow_add]
          _ = 199131802830 := by rw [factor_1_4]; decide
      have factor_1_6 : (47 : ZMod 232908956281) ^ 72 = 21778868543 := by
        calc
          (47 : ZMod 232908956281) ^ 72 = (47 : ZMod 232908956281) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 36 * (47 : ZMod 232908956281) ^ 36 := by rw [pow_add]
          _ = 21778868543 := by rw [factor_1_5]; decide
      have factor_1_7 : (47 : ZMod 232908956281) ^ 144 = 159942208220 := by
        calc
          (47 : ZMod 232908956281) ^ 144 = (47 : ZMod 232908956281) ^ (72 + 72) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 72 * (47 : ZMod 232908956281) ^ 72 := by rw [pow_add]
          _ = 159942208220 := by rw [factor_1_6]; decide
      have factor_1_8 : (47 : ZMod 232908956281) ^ 289 = 165025770005 := by
        calc
          (47 : ZMod 232908956281) ^ 289 = (47 : ZMod 232908956281) ^ (144 + 144 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 144 * (47 : ZMod 232908956281) ^ 144) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 165025770005 := by rw [factor_1_7]; decide
      have factor_1_9 : (47 : ZMod 232908956281) ^ 578 = 178167374788 := by
        calc
          (47 : ZMod 232908956281) ^ 578 = (47 : ZMod 232908956281) ^ (289 + 289) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 289 * (47 : ZMod 232908956281) ^ 289 := by rw [pow_add]
          _ = 178167374788 := by rw [factor_1_8]; decide
      have factor_1_10 : (47 : ZMod 232908956281) ^ 1156 = 66041368665 := by
        calc
          (47 : ZMod 232908956281) ^ 1156 = (47 : ZMod 232908956281) ^ (578 + 578) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 578 * (47 : ZMod 232908956281) ^ 578 := by rw [pow_add]
          _ = 66041368665 := by rw [factor_1_9]; decide
      have factor_1_11 : (47 : ZMod 232908956281) ^ 2313 = 124145438223 := by
        calc
          (47 : ZMod 232908956281) ^ 2313 = (47 : ZMod 232908956281) ^ (1156 + 1156 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 1156 * (47 : ZMod 232908956281) ^ 1156) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 124145438223 := by rw [factor_1_10]; decide
      have factor_1_12 : (47 : ZMod 232908956281) ^ 4627 = 91236203724 := by
        calc
          (47 : ZMod 232908956281) ^ 4627 = (47 : ZMod 232908956281) ^ (2313 + 2313 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 2313 * (47 : ZMod 232908956281) ^ 2313) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 91236203724 := by rw [factor_1_11]; decide
      have factor_1_13 : (47 : ZMod 232908956281) ^ 9254 = 198581990990 := by
        calc
          (47 : ZMod 232908956281) ^ 9254 = (47 : ZMod 232908956281) ^ (4627 + 4627) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 4627 * (47 : ZMod 232908956281) ^ 4627 := by rw [pow_add]
          _ = 198581990990 := by rw [factor_1_12]; decide
      have factor_1_14 : (47 : ZMod 232908956281) ^ 18509 = 61542013028 := by
        calc
          (47 : ZMod 232908956281) ^ 18509 = (47 : ZMod 232908956281) ^ (9254 + 9254 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 9254 * (47 : ZMod 232908956281) ^ 9254) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 61542013028 := by rw [factor_1_13]; decide
      have factor_1_15 : (47 : ZMod 232908956281) ^ 37019 = 149329827048 := by
        calc
          (47 : ZMod 232908956281) ^ 37019 = (47 : ZMod 232908956281) ^ (18509 + 18509 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 18509 * (47 : ZMod 232908956281) ^ 18509) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 149329827048 := by rw [factor_1_14]; decide
      have factor_1_16 : (47 : ZMod 232908956281) ^ 74039 = 133153773031 := by
        calc
          (47 : ZMod 232908956281) ^ 74039 = (47 : ZMod 232908956281) ^ (37019 + 37019 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 37019 * (47 : ZMod 232908956281) ^ 37019) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 133153773031 := by rw [factor_1_15]; decide
      have factor_1_17 : (47 : ZMod 232908956281) ^ 148079 = 174914926294 := by
        calc
          (47 : ZMod 232908956281) ^ 148079 = (47 : ZMod 232908956281) ^ (74039 + 74039 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 74039 * (47 : ZMod 232908956281) ^ 74039) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 174914926294 := by rw [factor_1_16]; decide
      have factor_1_18 : (47 : ZMod 232908956281) ^ 296159 = 27896047773 := by
        calc
          (47 : ZMod 232908956281) ^ 296159 = (47 : ZMod 232908956281) ^ (148079 + 148079 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 148079 * (47 : ZMod 232908956281) ^ 148079) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 27896047773 := by rw [factor_1_17]; decide
      have factor_1_19 : (47 : ZMod 232908956281) ^ 592318 = 200906154202 := by
        calc
          (47 : ZMod 232908956281) ^ 592318 = (47 : ZMod 232908956281) ^ (296159 + 296159) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 296159 * (47 : ZMod 232908956281) ^ 296159 := by rw [pow_add]
          _ = 200906154202 := by rw [factor_1_18]; decide
      have factor_1_20 : (47 : ZMod 232908956281) ^ 1184636 = 31193896392 := by
        calc
          (47 : ZMod 232908956281) ^ 1184636 = (47 : ZMod 232908956281) ^ (592318 + 592318) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 592318 * (47 : ZMod 232908956281) ^ 592318 := by rw [pow_add]
          _ = 31193896392 := by rw [factor_1_19]; decide
      have factor_1_21 : (47 : ZMod 232908956281) ^ 2369272 = 7446577564 := by
        calc
          (47 : ZMod 232908956281) ^ 2369272 = (47 : ZMod 232908956281) ^ (1184636 + 1184636) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1184636 * (47 : ZMod 232908956281) ^ 1184636 := by rw [pow_add]
          _ = 7446577564 := by rw [factor_1_20]; decide
      have factor_1_22 : (47 : ZMod 232908956281) ^ 4738544 = 179425483002 := by
        calc
          (47 : ZMod 232908956281) ^ 4738544 = (47 : ZMod 232908956281) ^ (2369272 + 2369272) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 2369272 * (47 : ZMod 232908956281) ^ 2369272 := by rw [pow_add]
          _ = 179425483002 := by rw [factor_1_21]; decide
      have factor_1_23 : (47 : ZMod 232908956281) ^ 9477089 = 191965987829 := by
        calc
          (47 : ZMod 232908956281) ^ 9477089 = (47 : ZMod 232908956281) ^ (4738544 + 4738544 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 4738544 * (47 : ZMod 232908956281) ^ 4738544) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 191965987829 := by rw [factor_1_22]; decide
      have factor_1_24 : (47 : ZMod 232908956281) ^ 18954179 = 160038601191 := by
        calc
          (47 : ZMod 232908956281) ^ 18954179 = (47 : ZMod 232908956281) ^ (9477089 + 9477089 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 9477089 * (47 : ZMod 232908956281) ^ 9477089) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 160038601191 := by rw [factor_1_23]; decide
      have factor_1_25 : (47 : ZMod 232908956281) ^ 37908358 = 208823697450 := by
        calc
          (47 : ZMod 232908956281) ^ 37908358 = (47 : ZMod 232908956281) ^ (18954179 + 18954179) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 18954179 * (47 : ZMod 232908956281) ^ 18954179 := by rw [pow_add]
          _ = 208823697450 := by rw [factor_1_24]; decide
      have factor_1_26 : (47 : ZMod 232908956281) ^ 75816717 = 169887571349 := by
        calc
          (47 : ZMod 232908956281) ^ 75816717 = (47 : ZMod 232908956281) ^ (37908358 + 37908358 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 37908358 * (47 : ZMod 232908956281) ^ 37908358) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 169887571349 := by rw [factor_1_25]; decide
      have factor_1_27 : (47 : ZMod 232908956281) ^ 151633435 = 47802438954 := by
        calc
          (47 : ZMod 232908956281) ^ 151633435 = (47 : ZMod 232908956281) ^ (75816717 + 75816717 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 75816717 * (47 : ZMod 232908956281) ^ 75816717) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 47802438954 := by rw [factor_1_26]; decide
      have factor_1_28 : (47 : ZMod 232908956281) ^ 303266870 = 105970780359 := by
        calc
          (47 : ZMod 232908956281) ^ 303266870 = (47 : ZMod 232908956281) ^ (151633435 + 151633435) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 151633435 * (47 : ZMod 232908956281) ^ 151633435 := by rw [pow_add]
          _ = 105970780359 := by rw [factor_1_27]; decide
      have factor_1_29 : (47 : ZMod 232908956281) ^ 606533740 = 35182743315 := by
        calc
          (47 : ZMod 232908956281) ^ 606533740 = (47 : ZMod 232908956281) ^ (303266870 + 303266870) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 303266870 * (47 : ZMod 232908956281) ^ 303266870 := by rw [pow_add]
          _ = 35182743315 := by rw [factor_1_28]; decide
      have factor_1_30 : (47 : ZMod 232908956281) ^ 1213067480 = 95230155075 := by
        calc
          (47 : ZMod 232908956281) ^ 1213067480 = (47 : ZMod 232908956281) ^ (606533740 + 606533740) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 606533740 * (47 : ZMod 232908956281) ^ 606533740 := by rw [pow_add]
          _ = 95230155075 := by rw [factor_1_29]; decide
      have factor_1_31 : (47 : ZMod 232908956281) ^ 2426134961 = 141903903776 := by
        calc
          (47 : ZMod 232908956281) ^ 2426134961 = (47 : ZMod 232908956281) ^ (1213067480 + 1213067480 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 1213067480 * (47 : ZMod 232908956281) ^ 1213067480) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 141903903776 := by rw [factor_1_30]; decide
      have factor_1_32 : (47 : ZMod 232908956281) ^ 4852269922 = 130798928301 := by
        calc
          (47 : ZMod 232908956281) ^ 4852269922 = (47 : ZMod 232908956281) ^ (2426134961 + 2426134961) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 2426134961 * (47 : ZMod 232908956281) ^ 2426134961 := by rw [pow_add]
          _ = 130798928301 := by rw [factor_1_31]; decide
      have factor_1_33 : (47 : ZMod 232908956281) ^ 9704539845 = 110783944626 := by
        calc
          (47 : ZMod 232908956281) ^ 9704539845 = (47 : ZMod 232908956281) ^ (4852269922 + 4852269922 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 4852269922 * (47 : ZMod 232908956281) ^ 4852269922) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 110783944626 := by rw [factor_1_32]; decide
      have factor_1_34 : (47 : ZMod 232908956281) ^ 19409079690 = 4783233896 := by
        calc
          (47 : ZMod 232908956281) ^ 19409079690 = (47 : ZMod 232908956281) ^ (9704539845 + 9704539845) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 9704539845 * (47 : ZMod 232908956281) ^ 9704539845 := by rw [pow_add]
          _ = 4783233896 := by rw [factor_1_33]; decide
      have factor_1_35 : (47 : ZMod 232908956281) ^ 38818159380 = 100026280858 := by
        calc
          (47 : ZMod 232908956281) ^ 38818159380 = (47 : ZMod 232908956281) ^ (19409079690 + 19409079690) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 19409079690 * (47 : ZMod 232908956281) ^ 19409079690 := by rw [pow_add]
          _ = 100026280858 := by rw [factor_1_34]; decide
      have factor_1_36 : (47 : ZMod 232908956281) ^ 77636318760 = 100026280857 := by
        calc
          (47 : ZMod 232908956281) ^ 77636318760 = (47 : ZMod 232908956281) ^ (38818159380 + 38818159380) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 38818159380 * (47 : ZMod 232908956281) ^ 38818159380 := by rw [pow_add]
          _ = 100026280857 := by rw [factor_1_35]; decide
      change (47 : ZMod 232908956281) ^ 77636318760 ≠ 1
      rw [factor_1_36]
      decide
    ·
      have factor_2_0 : (47 : ZMod 232908956281) ^ 1 = 47 := by norm_num
      have factor_2_1 : (47 : ZMod 232908956281) ^ 2 = 2209 := by
        calc
          (47 : ZMod 232908956281) ^ 2 = (47 : ZMod 232908956281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1 * (47 : ZMod 232908956281) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_2_0]; decide
      have factor_2_2 : (47 : ZMod 232908956281) ^ 5 = 229345007 := by
        calc
          (47 : ZMod 232908956281) ^ 5 = (47 : ZMod 232908956281) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 2 * (47 : ZMod 232908956281) ^ 2) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 229345007 := by rw [factor_2_1]; decide
      have factor_2_3 : (47 : ZMod 232908956281) ^ 10 = 138094110414 := by
        calc
          (47 : ZMod 232908956281) ^ 10 = (47 : ZMod 232908956281) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 5 * (47 : ZMod 232908956281) ^ 5 := by rw [pow_add]
          _ = 138094110414 := by rw [factor_2_2]; decide
      have factor_2_4 : (47 : ZMod 232908956281) ^ 21 = 231842714065 := by
        calc
          (47 : ZMod 232908956281) ^ 21 = (47 : ZMod 232908956281) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 10 * (47 : ZMod 232908956281) ^ 10) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 231842714065 := by rw [factor_2_3]; decide
      have factor_2_5 : (47 : ZMod 232908956281) ^ 43 = 57487219544 := by
        calc
          (47 : ZMod 232908956281) ^ 43 = (47 : ZMod 232908956281) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 21 * (47 : ZMod 232908956281) ^ 21) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 57487219544 := by rw [factor_2_4]; decide
      have factor_2_6 : (47 : ZMod 232908956281) ^ 86 = 187310547595 := by
        calc
          (47 : ZMod 232908956281) ^ 86 = (47 : ZMod 232908956281) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 43 * (47 : ZMod 232908956281) ^ 43 := by rw [pow_add]
          _ = 187310547595 := by rw [factor_2_5]; decide
      have factor_2_7 : (47 : ZMod 232908956281) ^ 173 = 2695689019 := by
        calc
          (47 : ZMod 232908956281) ^ 173 = (47 : ZMod 232908956281) ^ (86 + 86 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 86 * (47 : ZMod 232908956281) ^ 86) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 2695689019 := by rw [factor_2_6]; decide
      have factor_2_8 : (47 : ZMod 232908956281) ^ 347 = 13745409513 := by
        calc
          (47 : ZMod 232908956281) ^ 347 = (47 : ZMod 232908956281) ^ (173 + 173 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 173 * (47 : ZMod 232908956281) ^ 173) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 13745409513 := by rw [factor_2_7]; decide
      have factor_2_9 : (47 : ZMod 232908956281) ^ 694 = 23961556902 := by
        calc
          (47 : ZMod 232908956281) ^ 694 = (47 : ZMod 232908956281) ^ (347 + 347) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 347 * (47 : ZMod 232908956281) ^ 347 := by rw [pow_add]
          _ = 23961556902 := by rw [factor_2_8]; decide
      have factor_2_10 : (47 : ZMod 232908956281) ^ 1388 = 125533232538 := by
        calc
          (47 : ZMod 232908956281) ^ 1388 = (47 : ZMod 232908956281) ^ (694 + 694) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 694 * (47 : ZMod 232908956281) ^ 694 := by rw [pow_add]
          _ = 125533232538 := by rw [factor_2_9]; decide
      have factor_2_11 : (47 : ZMod 232908956281) ^ 2776 = 207219920602 := by
        calc
          (47 : ZMod 232908956281) ^ 2776 = (47 : ZMod 232908956281) ^ (1388 + 1388) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1388 * (47 : ZMod 232908956281) ^ 1388 := by rw [pow_add]
          _ = 207219920602 := by rw [factor_2_10]; decide
      have factor_2_12 : (47 : ZMod 232908956281) ^ 5552 = 179143551372 := by
        calc
          (47 : ZMod 232908956281) ^ 5552 = (47 : ZMod 232908956281) ^ (2776 + 2776) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 2776 * (47 : ZMod 232908956281) ^ 2776 := by rw [pow_add]
          _ = 179143551372 := by rw [factor_2_11]; decide
      have factor_2_13 : (47 : ZMod 232908956281) ^ 11105 = 117573317425 := by
        calc
          (47 : ZMod 232908956281) ^ 11105 = (47 : ZMod 232908956281) ^ (5552 + 5552 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 5552 * (47 : ZMod 232908956281) ^ 5552) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 117573317425 := by rw [factor_2_12]; decide
      have factor_2_14 : (47 : ZMod 232908956281) ^ 22211 = 185397091353 := by
        calc
          (47 : ZMod 232908956281) ^ 22211 = (47 : ZMod 232908956281) ^ (11105 + 11105 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 11105 * (47 : ZMod 232908956281) ^ 11105) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 185397091353 := by rw [factor_2_13]; decide
      have factor_2_15 : (47 : ZMod 232908956281) ^ 44423 = 9294585272 := by
        calc
          (47 : ZMod 232908956281) ^ 44423 = (47 : ZMod 232908956281) ^ (22211 + 22211 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 22211 * (47 : ZMod 232908956281) ^ 22211) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 9294585272 := by rw [factor_2_14]; decide
      have factor_2_16 : (47 : ZMod 232908956281) ^ 88847 = 31535653754 := by
        calc
          (47 : ZMod 232908956281) ^ 88847 = (47 : ZMod 232908956281) ^ (44423 + 44423 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 44423 * (47 : ZMod 232908956281) ^ 44423) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 31535653754 := by rw [factor_2_15]; decide
      have factor_2_17 : (47 : ZMod 232908956281) ^ 177695 = 58472761887 := by
        calc
          (47 : ZMod 232908956281) ^ 177695 = (47 : ZMod 232908956281) ^ (88847 + 88847 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 88847 * (47 : ZMod 232908956281) ^ 88847) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 58472761887 := by rw [factor_2_16]; decide
      have factor_2_18 : (47 : ZMod 232908956281) ^ 355390 = 175832352174 := by
        calc
          (47 : ZMod 232908956281) ^ 355390 = (47 : ZMod 232908956281) ^ (177695 + 177695) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 177695 * (47 : ZMod 232908956281) ^ 177695 := by rw [pow_add]
          _ = 175832352174 := by rw [factor_2_17]; decide
      have factor_2_19 : (47 : ZMod 232908956281) ^ 710781 = 42867581451 := by
        calc
          (47 : ZMod 232908956281) ^ 710781 = (47 : ZMod 232908956281) ^ (355390 + 355390 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 355390 * (47 : ZMod 232908956281) ^ 355390) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 42867581451 := by rw [factor_2_18]; decide
      have factor_2_20 : (47 : ZMod 232908956281) ^ 1421563 = 168917740416 := by
        calc
          (47 : ZMod 232908956281) ^ 1421563 = (47 : ZMod 232908956281) ^ (710781 + 710781 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 710781 * (47 : ZMod 232908956281) ^ 710781) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 168917740416 := by rw [factor_2_19]; decide
      have factor_2_21 : (47 : ZMod 232908956281) ^ 2843126 = 211049867781 := by
        calc
          (47 : ZMod 232908956281) ^ 2843126 = (47 : ZMod 232908956281) ^ (1421563 + 1421563) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1421563 * (47 : ZMod 232908956281) ^ 1421563 := by rw [pow_add]
          _ = 211049867781 := by rw [factor_2_20]; decide
      have factor_2_22 : (47 : ZMod 232908956281) ^ 5686253 = 72566846216 := by
        calc
          (47 : ZMod 232908956281) ^ 5686253 = (47 : ZMod 232908956281) ^ (2843126 + 2843126 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 2843126 * (47 : ZMod 232908956281) ^ 2843126) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 72566846216 := by rw [factor_2_21]; decide
      have factor_2_23 : (47 : ZMod 232908956281) ^ 11372507 = 203677935837 := by
        calc
          (47 : ZMod 232908956281) ^ 11372507 = (47 : ZMod 232908956281) ^ (5686253 + 5686253 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 5686253 * (47 : ZMod 232908956281) ^ 5686253) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 203677935837 := by rw [factor_2_22]; decide
      have factor_2_24 : (47 : ZMod 232908956281) ^ 22745015 = 87583131121 := by
        calc
          (47 : ZMod 232908956281) ^ 22745015 = (47 : ZMod 232908956281) ^ (11372507 + 11372507 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 11372507 * (47 : ZMod 232908956281) ^ 11372507) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 87583131121 := by rw [factor_2_23]; decide
      have factor_2_25 : (47 : ZMod 232908956281) ^ 45490030 = 58070536985 := by
        calc
          (47 : ZMod 232908956281) ^ 45490030 = (47 : ZMod 232908956281) ^ (22745015 + 22745015) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 22745015 * (47 : ZMod 232908956281) ^ 22745015 := by rw [pow_add]
          _ = 58070536985 := by rw [factor_2_24]; decide
      have factor_2_26 : (47 : ZMod 232908956281) ^ 90980061 = 99913017143 := by
        calc
          (47 : ZMod 232908956281) ^ 90980061 = (47 : ZMod 232908956281) ^ (45490030 + 45490030 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 45490030 * (47 : ZMod 232908956281) ^ 45490030) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 99913017143 := by rw [factor_2_25]; decide
      have factor_2_27 : (47 : ZMod 232908956281) ^ 181960122 = 216340181940 := by
        calc
          (47 : ZMod 232908956281) ^ 181960122 = (47 : ZMod 232908956281) ^ (90980061 + 90980061) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 90980061 * (47 : ZMod 232908956281) ^ 90980061 := by rw [pow_add]
          _ = 216340181940 := by rw [factor_2_26]; decide
      have factor_2_28 : (47 : ZMod 232908956281) ^ 363920244 = 33202204311 := by
        calc
          (47 : ZMod 232908956281) ^ 363920244 = (47 : ZMod 232908956281) ^ (181960122 + 181960122) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 181960122 * (47 : ZMod 232908956281) ^ 181960122 := by rw [pow_add]
          _ = 33202204311 := by rw [factor_2_27]; decide
      have factor_2_29 : (47 : ZMod 232908956281) ^ 727840488 = 61397564296 := by
        calc
          (47 : ZMod 232908956281) ^ 727840488 = (47 : ZMod 232908956281) ^ (363920244 + 363920244) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 363920244 * (47 : ZMod 232908956281) ^ 363920244 := by rw [pow_add]
          _ = 61397564296 := by rw [factor_2_28]; decide
      have factor_2_30 : (47 : ZMod 232908956281) ^ 1455680976 = 189033844158 := by
        calc
          (47 : ZMod 232908956281) ^ 1455680976 = (47 : ZMod 232908956281) ^ (727840488 + 727840488) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 727840488 * (47 : ZMod 232908956281) ^ 727840488 := by rw [pow_add]
          _ = 189033844158 := by rw [factor_2_29]; decide
      have factor_2_31 : (47 : ZMod 232908956281) ^ 2911361953 = 146291498888 := by
        calc
          (47 : ZMod 232908956281) ^ 2911361953 = (47 : ZMod 232908956281) ^ (1455680976 + 1455680976 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 1455680976 * (47 : ZMod 232908956281) ^ 1455680976) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 146291498888 := by rw [factor_2_30]; decide
      have factor_2_32 : (47 : ZMod 232908956281) ^ 5822723907 = 172471273089 := by
        calc
          (47 : ZMod 232908956281) ^ 5822723907 = (47 : ZMod 232908956281) ^ (2911361953 + 2911361953 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 2911361953 * (47 : ZMod 232908956281) ^ 2911361953) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 172471273089 := by rw [factor_2_31]; decide
      have factor_2_33 : (47 : ZMod 232908956281) ^ 11645447814 = 13198603490 := by
        calc
          (47 : ZMod 232908956281) ^ 11645447814 = (47 : ZMod 232908956281) ^ (5822723907 + 5822723907) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 5822723907 * (47 : ZMod 232908956281) ^ 5822723907 := by rw [pow_add]
          _ = 13198603490 := by rw [factor_2_32]; decide
      have factor_2_34 : (47 : ZMod 232908956281) ^ 23290895628 = 62128029148 := by
        calc
          (47 : ZMod 232908956281) ^ 23290895628 = (47 : ZMod 232908956281) ^ (11645447814 + 11645447814) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 11645447814 * (47 : ZMod 232908956281) ^ 11645447814 := by rw [pow_add]
          _ = 62128029148 := by rw [factor_2_33]; decide
      have factor_2_35 : (47 : ZMod 232908956281) ^ 46581791256 = 188133278749 := by
        calc
          (47 : ZMod 232908956281) ^ 46581791256 = (47 : ZMod 232908956281) ^ (23290895628 + 23290895628) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 23290895628 * (47 : ZMod 232908956281) ^ 23290895628 := by rw [pow_add]
          _ = 188133278749 := by rw [factor_2_34]; decide
      change (47 : ZMod 232908956281) ^ 46581791256 ≠ 1
      rw [factor_2_35]
      decide
    ·
      have factor_3_0 : (47 : ZMod 232908956281) ^ 1 = 47 := by norm_num
      have factor_3_1 : (47 : ZMod 232908956281) ^ 3 = 103823 := by
        calc
          (47 : ZMod 232908956281) ^ 3 = (47 : ZMod 232908956281) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 1 * (47 : ZMod 232908956281) ^ 1) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_3_0]; decide
      have factor_3_2 : (47 : ZMod 232908956281) ^ 7 = 40805207901 := by
        calc
          (47 : ZMod 232908956281) ^ 7 = (47 : ZMod 232908956281) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 3 * (47 : ZMod 232908956281) ^ 3) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 40805207901 := by rw [factor_3_1]; decide
      have factor_3_3 : (47 : ZMod 232908956281) ^ 15 = 72239291650 := by
        calc
          (47 : ZMod 232908956281) ^ 15 = (47 : ZMod 232908956281) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 7 * (47 : ZMod 232908956281) ^ 7) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 72239291650 := by rw [factor_3_2]; decide
      have factor_3_4 : (47 : ZMod 232908956281) ^ 30 = 13833727573 := by
        calc
          (47 : ZMod 232908956281) ^ 30 = (47 : ZMod 232908956281) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 15 * (47 : ZMod 232908956281) ^ 15 := by rw [pow_add]
          _ = 13833727573 := by rw [factor_3_3]; decide
      have factor_3_5 : (47 : ZMod 232908956281) ^ 61 = 2081306792 := by
        calc
          (47 : ZMod 232908956281) ^ 61 = (47 : ZMod 232908956281) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 30 * (47 : ZMod 232908956281) ^ 30) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 2081306792 := by rw [factor_3_4]; decide
      have factor_3_6 : (47 : ZMod 232908956281) ^ 123 = 181842449856 := by
        calc
          (47 : ZMod 232908956281) ^ 123 = (47 : ZMod 232908956281) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 61 * (47 : ZMod 232908956281) ^ 61) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 181842449856 := by rw [factor_3_5]; decide
      have factor_3_7 : (47 : ZMod 232908956281) ^ 247 = 152824662837 := by
        calc
          (47 : ZMod 232908956281) ^ 247 = (47 : ZMod 232908956281) ^ (123 + 123 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 123 * (47 : ZMod 232908956281) ^ 123) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 152824662837 := by rw [factor_3_6]; decide
      have factor_3_8 : (47 : ZMod 232908956281) ^ 495 = 208272921572 := by
        calc
          (47 : ZMod 232908956281) ^ 495 = (47 : ZMod 232908956281) ^ (247 + 247 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 247 * (47 : ZMod 232908956281) ^ 247) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 208272921572 := by rw [factor_3_7]; decide
      have factor_3_9 : (47 : ZMod 232908956281) ^ 991 = 634658308 := by
        calc
          (47 : ZMod 232908956281) ^ 991 = (47 : ZMod 232908956281) ^ (495 + 495 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 495 * (47 : ZMod 232908956281) ^ 495) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 634658308 := by rw [factor_3_8]; decide
      have factor_3_10 : (47 : ZMod 232908956281) ^ 1983 = 220155898728 := by
        calc
          (47 : ZMod 232908956281) ^ 1983 = (47 : ZMod 232908956281) ^ (991 + 991 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 991 * (47 : ZMod 232908956281) ^ 991) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 220155898728 := by rw [factor_3_9]; decide
      have factor_3_11 : (47 : ZMod 232908956281) ^ 3966 = 223741683754 := by
        calc
          (47 : ZMod 232908956281) ^ 3966 = (47 : ZMod 232908956281) ^ (1983 + 1983) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1983 * (47 : ZMod 232908956281) ^ 1983 := by rw [pow_add]
          _ = 223741683754 := by rw [factor_3_10]; decide
      have factor_3_12 : (47 : ZMod 232908956281) ^ 7932 = 77187418267 := by
        calc
          (47 : ZMod 232908956281) ^ 7932 = (47 : ZMod 232908956281) ^ (3966 + 3966) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 3966 * (47 : ZMod 232908956281) ^ 3966 := by rw [pow_add]
          _ = 77187418267 := by rw [factor_3_11]; decide
      have factor_3_13 : (47 : ZMod 232908956281) ^ 15865 = 183418043487 := by
        calc
          (47 : ZMod 232908956281) ^ 15865 = (47 : ZMod 232908956281) ^ (7932 + 7932 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 7932 * (47 : ZMod 232908956281) ^ 7932) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 183418043487 := by rw [factor_3_12]; decide
      have factor_3_14 : (47 : ZMod 232908956281) ^ 31731 = 12067160621 := by
        calc
          (47 : ZMod 232908956281) ^ 31731 = (47 : ZMod 232908956281) ^ (15865 + 15865 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 15865 * (47 : ZMod 232908956281) ^ 15865) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 12067160621 := by rw [factor_3_13]; decide
      have factor_3_15 : (47 : ZMod 232908956281) ^ 63462 = 191106343763 := by
        calc
          (47 : ZMod 232908956281) ^ 63462 = (47 : ZMod 232908956281) ^ (31731 + 31731) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 31731 * (47 : ZMod 232908956281) ^ 31731 := by rw [pow_add]
          _ = 191106343763 := by rw [factor_3_14]; decide
      have factor_3_16 : (47 : ZMod 232908956281) ^ 126925 = 35237413578 := by
        calc
          (47 : ZMod 232908956281) ^ 126925 = (47 : ZMod 232908956281) ^ (63462 + 63462 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 63462 * (47 : ZMod 232908956281) ^ 63462) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 35237413578 := by rw [factor_3_15]; decide
      have factor_3_17 : (47 : ZMod 232908956281) ^ 253850 = 202963654549 := by
        calc
          (47 : ZMod 232908956281) ^ 253850 = (47 : ZMod 232908956281) ^ (126925 + 126925) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 126925 * (47 : ZMod 232908956281) ^ 126925 := by rw [pow_add]
          _ = 202963654549 := by rw [factor_3_16]; decide
      have factor_3_18 : (47 : ZMod 232908956281) ^ 507701 = 196246799731 := by
        calc
          (47 : ZMod 232908956281) ^ 507701 = (47 : ZMod 232908956281) ^ (253850 + 253850 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 253850 * (47 : ZMod 232908956281) ^ 253850) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 196246799731 := by rw [factor_3_17]; decide
      have factor_3_19 : (47 : ZMod 232908956281) ^ 1015402 = 158641604290 := by
        calc
          (47 : ZMod 232908956281) ^ 1015402 = (47 : ZMod 232908956281) ^ (507701 + 507701) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 507701 * (47 : ZMod 232908956281) ^ 507701 := by rw [pow_add]
          _ = 158641604290 := by rw [factor_3_18]; decide
      have factor_3_20 : (47 : ZMod 232908956281) ^ 2030804 = 177220580310 := by
        calc
          (47 : ZMod 232908956281) ^ 2030804 = (47 : ZMod 232908956281) ^ (1015402 + 1015402) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1015402 * (47 : ZMod 232908956281) ^ 1015402 := by rw [pow_add]
          _ = 177220580310 := by rw [factor_3_19]; decide
      have factor_3_21 : (47 : ZMod 232908956281) ^ 4061609 = 217060590424 := by
        calc
          (47 : ZMod 232908956281) ^ 4061609 = (47 : ZMod 232908956281) ^ (2030804 + 2030804 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 2030804 * (47 : ZMod 232908956281) ^ 2030804) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 217060590424 := by rw [factor_3_20]; decide
      have factor_3_22 : (47 : ZMod 232908956281) ^ 8123219 = 174842442827 := by
        calc
          (47 : ZMod 232908956281) ^ 8123219 = (47 : ZMod 232908956281) ^ (4061609 + 4061609 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 4061609 * (47 : ZMod 232908956281) ^ 4061609) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 174842442827 := by rw [factor_3_21]; decide
      have factor_3_23 : (47 : ZMod 232908956281) ^ 16246439 = 60335660989 := by
        calc
          (47 : ZMod 232908956281) ^ 16246439 = (47 : ZMod 232908956281) ^ (8123219 + 8123219 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 8123219 * (47 : ZMod 232908956281) ^ 8123219) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 60335660989 := by rw [factor_3_22]; decide
      have factor_3_24 : (47 : ZMod 232908956281) ^ 32492878 = 93048211862 := by
        calc
          (47 : ZMod 232908956281) ^ 32492878 = (47 : ZMod 232908956281) ^ (16246439 + 16246439) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 16246439 * (47 : ZMod 232908956281) ^ 16246439 := by rw [pow_add]
          _ = 93048211862 := by rw [factor_3_23]; decide
      have factor_3_25 : (47 : ZMod 232908956281) ^ 64985757 = 106732738913 := by
        calc
          (47 : ZMod 232908956281) ^ 64985757 = (47 : ZMod 232908956281) ^ (32492878 + 32492878 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 32492878 * (47 : ZMod 232908956281) ^ 32492878) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 106732738913 := by rw [factor_3_24]; decide
      have factor_3_26 : (47 : ZMod 232908956281) ^ 129971515 = 78881117128 := by
        calc
          (47 : ZMod 232908956281) ^ 129971515 = (47 : ZMod 232908956281) ^ (64985757 + 64985757 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 64985757 * (47 : ZMod 232908956281) ^ 64985757) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 78881117128 := by rw [factor_3_25]; decide
      have factor_3_27 : (47 : ZMod 232908956281) ^ 259943031 = 150071496475 := by
        calc
          (47 : ZMod 232908956281) ^ 259943031 = (47 : ZMod 232908956281) ^ (129971515 + 129971515 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 129971515 * (47 : ZMod 232908956281) ^ 129971515) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 150071496475 := by rw [factor_3_26]; decide
      have factor_3_28 : (47 : ZMod 232908956281) ^ 519886063 = 51117336239 := by
        calc
          (47 : ZMod 232908956281) ^ 519886063 = (47 : ZMod 232908956281) ^ (259943031 + 259943031 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 259943031 * (47 : ZMod 232908956281) ^ 259943031) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 51117336239 := by rw [factor_3_27]; decide
      have factor_3_29 : (47 : ZMod 232908956281) ^ 1039772126 = 5941445129 := by
        calc
          (47 : ZMod 232908956281) ^ 1039772126 = (47 : ZMod 232908956281) ^ (519886063 + 519886063) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 519886063 * (47 : ZMod 232908956281) ^ 519886063 := by rw [pow_add]
          _ = 5941445129 := by rw [factor_3_28]; decide
      have factor_3_30 : (47 : ZMod 232908956281) ^ 2079544252 = 190507809247 := by
        calc
          (47 : ZMod 232908956281) ^ 2079544252 = (47 : ZMod 232908956281) ^ (1039772126 + 1039772126) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1039772126 * (47 : ZMod 232908956281) ^ 1039772126 := by rw [pow_add]
          _ = 190507809247 := by rw [factor_3_29]; decide
      have factor_3_31 : (47 : ZMod 232908956281) ^ 4159088505 = 168363727600 := by
        calc
          (47 : ZMod 232908956281) ^ 4159088505 = (47 : ZMod 232908956281) ^ (2079544252 + 2079544252 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 2079544252 * (47 : ZMod 232908956281) ^ 2079544252) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 168363727600 := by rw [factor_3_30]; decide
      have factor_3_32 : (47 : ZMod 232908956281) ^ 8318177010 = 3251524975 := by
        calc
          (47 : ZMod 232908956281) ^ 8318177010 = (47 : ZMod 232908956281) ^ (4159088505 + 4159088505) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 4159088505 * (47 : ZMod 232908956281) ^ 4159088505 := by rw [pow_add]
          _ = 3251524975 := by rw [factor_3_31]; decide
      have factor_3_33 : (47 : ZMod 232908956281) ^ 16636354020 = 71118251758 := by
        calc
          (47 : ZMod 232908956281) ^ 16636354020 = (47 : ZMod 232908956281) ^ (8318177010 + 8318177010) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 8318177010 * (47 : ZMod 232908956281) ^ 8318177010 := by rw [pow_add]
          _ = 71118251758 := by rw [factor_3_32]; decide
      have factor_3_34 : (47 : ZMod 232908956281) ^ 33272708040 = 28514889026 := by
        calc
          (47 : ZMod 232908956281) ^ 33272708040 = (47 : ZMod 232908956281) ^ (16636354020 + 16636354020) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 16636354020 * (47 : ZMod 232908956281) ^ 16636354020 := by rw [pow_add]
          _ = 28514889026 := by rw [factor_3_33]; decide
      change (47 : ZMod 232908956281) ^ 33272708040 ≠ 1
      rw [factor_3_34]
      decide
    ·
      have factor_4_0 : (47 : ZMod 232908956281) ^ 1 = 47 := by norm_num
      have factor_4_1 : (47 : ZMod 232908956281) ^ 2 = 2209 := by
        calc
          (47 : ZMod 232908956281) ^ 2 = (47 : ZMod 232908956281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1 * (47 : ZMod 232908956281) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_4_0]; decide
      have factor_4_2 : (47 : ZMod 232908956281) ^ 4 = 4879681 := by
        calc
          (47 : ZMod 232908956281) ^ 4 = (47 : ZMod 232908956281) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 2 * (47 : ZMod 232908956281) ^ 2 := by rw [pow_add]
          _ = 4879681 := by rw [factor_4_1]; decide
      have factor_4_3 : (47 : ZMod 232908956281) ^ 9 = 2938172562 := by
        calc
          (47 : ZMod 232908956281) ^ 9 = (47 : ZMod 232908956281) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 4 * (47 : ZMod 232908956281) ^ 4) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 2938172562 := by rw [factor_4_2]; decide
      have factor_4_4 : (47 : ZMod 232908956281) ^ 19 = 21403101803 := by
        calc
          (47 : ZMod 232908956281) ^ 19 = (47 : ZMod 232908956281) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 9 * (47 : ZMod 232908956281) ^ 9) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 21403101803 := by rw [factor_4_3]; decide
      have factor_4_5 : (47 : ZMod 232908956281) ^ 39 = 64751979844 := by
        calc
          (47 : ZMod 232908956281) ^ 39 = (47 : ZMod 232908956281) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 19 * (47 : ZMod 232908956281) ^ 19) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 64751979844 := by rw [factor_4_4]; decide
      have factor_4_6 : (47 : ZMod 232908956281) ^ 78 = 120334809914 := by
        calc
          (47 : ZMod 232908956281) ^ 78 = (47 : ZMod 232908956281) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 39 * (47 : ZMod 232908956281) ^ 39 := by rw [pow_add]
          _ = 120334809914 := by rw [factor_4_5]; decide
      have factor_4_7 : (47 : ZMod 232908956281) ^ 157 = 184238031325 := by
        calc
          (47 : ZMod 232908956281) ^ 157 = (47 : ZMod 232908956281) ^ (78 + 78 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 78 * (47 : ZMod 232908956281) ^ 78) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 184238031325 := by rw [factor_4_6]; decide
      have factor_4_8 : (47 : ZMod 232908956281) ^ 315 = 217742771454 := by
        calc
          (47 : ZMod 232908956281) ^ 315 = (47 : ZMod 232908956281) ^ (157 + 157 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 157 * (47 : ZMod 232908956281) ^ 157) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 217742771454 := by rw [factor_4_7]; decide
      have factor_4_9 : (47 : ZMod 232908956281) ^ 631 = 83646943014 := by
        calc
          (47 : ZMod 232908956281) ^ 631 = (47 : ZMod 232908956281) ^ (315 + 315 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 315 * (47 : ZMod 232908956281) ^ 315) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 83646943014 := by rw [factor_4_8]; decide
      have factor_4_10 : (47 : ZMod 232908956281) ^ 1262 = 80410944936 := by
        calc
          (47 : ZMod 232908956281) ^ 1262 = (47 : ZMod 232908956281) ^ (631 + 631) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 631 * (47 : ZMod 232908956281) ^ 631 := by rw [pow_add]
          _ = 80410944936 := by rw [factor_4_9]; decide
      have factor_4_11 : (47 : ZMod 232908956281) ^ 2524 = 107163488248 := by
        calc
          (47 : ZMod 232908956281) ^ 2524 = (47 : ZMod 232908956281) ^ (1262 + 1262) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1262 * (47 : ZMod 232908956281) ^ 1262 := by rw [pow_add]
          _ = 107163488248 := by rw [factor_4_10]; decide
      have factor_4_12 : (47 : ZMod 232908956281) ^ 5048 = 49563016142 := by
        calc
          (47 : ZMod 232908956281) ^ 5048 = (47 : ZMod 232908956281) ^ (2524 + 2524) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 2524 * (47 : ZMod 232908956281) ^ 2524 := by rw [pow_add]
          _ = 49563016142 := by rw [factor_4_11]; decide
      have factor_4_13 : (47 : ZMod 232908956281) ^ 10096 = 55853779885 := by
        calc
          (47 : ZMod 232908956281) ^ 10096 = (47 : ZMod 232908956281) ^ (5048 + 5048) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 5048 * (47 : ZMod 232908956281) ^ 5048 := by rw [pow_add]
          _ = 55853779885 := by rw [factor_4_12]; decide
      have factor_4_14 : (47 : ZMod 232908956281) ^ 20192 = 120250870110 := by
        calc
          (47 : ZMod 232908956281) ^ 20192 = (47 : ZMod 232908956281) ^ (10096 + 10096) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 10096 * (47 : ZMod 232908956281) ^ 10096 := by rw [pow_add]
          _ = 120250870110 := by rw [factor_4_13]; decide
      have factor_4_15 : (47 : ZMod 232908956281) ^ 40385 = 23817196664 := by
        calc
          (47 : ZMod 232908956281) ^ 40385 = (47 : ZMod 232908956281) ^ (20192 + 20192 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 20192 * (47 : ZMod 232908956281) ^ 20192) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 23817196664 := by rw [factor_4_14]; decide
      have factor_4_16 : (47 : ZMod 232908956281) ^ 80770 = 211988193532 := by
        calc
          (47 : ZMod 232908956281) ^ 80770 = (47 : ZMod 232908956281) ^ (40385 + 40385) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 40385 * (47 : ZMod 232908956281) ^ 40385 := by rw [pow_add]
          _ = 211988193532 := by rw [factor_4_15]; decide
      have factor_4_17 : (47 : ZMod 232908956281) ^ 161541 = 207730248112 := by
        calc
          (47 : ZMod 232908956281) ^ 161541 = (47 : ZMod 232908956281) ^ (80770 + 80770 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 80770 * (47 : ZMod 232908956281) ^ 80770) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 207730248112 := by rw [factor_4_16]; decide
      have factor_4_18 : (47 : ZMod 232908956281) ^ 323082 = 55795699557 := by
        calc
          (47 : ZMod 232908956281) ^ 323082 = (47 : ZMod 232908956281) ^ (161541 + 161541) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 161541 * (47 : ZMod 232908956281) ^ 161541 := by rw [pow_add]
          _ = 55795699557 := by rw [factor_4_17]; decide
      have factor_4_19 : (47 : ZMod 232908956281) ^ 646165 = 222079904417 := by
        calc
          (47 : ZMod 232908956281) ^ 646165 = (47 : ZMod 232908956281) ^ (323082 + 323082 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 323082 * (47 : ZMod 232908956281) ^ 323082) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 222079904417 := by rw [factor_4_18]; decide
      have factor_4_20 : (47 : ZMod 232908956281) ^ 1292330 = 225333209418 := by
        calc
          (47 : ZMod 232908956281) ^ 1292330 = (47 : ZMod 232908956281) ^ (646165 + 646165) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 646165 * (47 : ZMod 232908956281) ^ 646165 := by rw [pow_add]
          _ = 225333209418 := by rw [factor_4_19]; decide
      have factor_4_21 : (47 : ZMod 232908956281) ^ 2584660 = 87177655863 := by
        calc
          (47 : ZMod 232908956281) ^ 2584660 = (47 : ZMod 232908956281) ^ (1292330 + 1292330) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1292330 * (47 : ZMod 232908956281) ^ 1292330 := by rw [pow_add]
          _ = 87177655863 := by rw [factor_4_20]; decide
      have factor_4_22 : (47 : ZMod 232908956281) ^ 5169321 = 184734226200 := by
        calc
          (47 : ZMod 232908956281) ^ 5169321 = (47 : ZMod 232908956281) ^ (2584660 + 2584660 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 2584660 * (47 : ZMod 232908956281) ^ 2584660) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 184734226200 := by rw [factor_4_21]; decide
      have factor_4_23 : (47 : ZMod 232908956281) ^ 10338643 = 215396013369 := by
        calc
          (47 : ZMod 232908956281) ^ 10338643 = (47 : ZMod 232908956281) ^ (5169321 + 5169321 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 5169321 * (47 : ZMod 232908956281) ^ 5169321) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 215396013369 := by rw [factor_4_22]; decide
      have factor_4_24 : (47 : ZMod 232908956281) ^ 20677286 = 212607968941 := by
        calc
          (47 : ZMod 232908956281) ^ 20677286 = (47 : ZMod 232908956281) ^ (10338643 + 10338643) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 10338643 * (47 : ZMod 232908956281) ^ 10338643 := by rw [pow_add]
          _ = 212607968941 := by rw [factor_4_23]; decide
      have factor_4_25 : (47 : ZMod 232908956281) ^ 41354573 = 6554698542 := by
        calc
          (47 : ZMod 232908956281) ^ 41354573 = (47 : ZMod 232908956281) ^ (20677286 + 20677286 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 20677286 * (47 : ZMod 232908956281) ^ 20677286) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 6554698542 := by rw [factor_4_24]; decide
      have factor_4_26 : (47 : ZMod 232908956281) ^ 82709146 = 174242278762 := by
        calc
          (47 : ZMod 232908956281) ^ 82709146 = (47 : ZMod 232908956281) ^ (41354573 + 41354573) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 41354573 * (47 : ZMod 232908956281) ^ 41354573 := by rw [pow_add]
          _ = 174242278762 := by rw [factor_4_25]; decide
      have factor_4_27 : (47 : ZMod 232908956281) ^ 165418292 = 155485638104 := by
        calc
          (47 : ZMod 232908956281) ^ 165418292 = (47 : ZMod 232908956281) ^ (82709146 + 82709146) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 82709146 * (47 : ZMod 232908956281) ^ 82709146 := by rw [pow_add]
          _ = 155485638104 := by rw [factor_4_26]; decide
      have factor_4_28 : (47 : ZMod 232908956281) ^ 330836585 = 154866257502 := by
        calc
          (47 : ZMod 232908956281) ^ 330836585 = (47 : ZMod 232908956281) ^ (165418292 + 165418292 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 165418292 * (47 : ZMod 232908956281) ^ 165418292) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 154866257502 := by rw [factor_4_27]; decide
      have factor_4_29 : (47 : ZMod 232908956281) ^ 661673171 = 13012714541 := by
        calc
          (47 : ZMod 232908956281) ^ 661673171 = (47 : ZMod 232908956281) ^ (330836585 + 330836585 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 330836585 * (47 : ZMod 232908956281) ^ 330836585) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 13012714541 := by rw [factor_4_28]; decide
      have factor_4_30 : (47 : ZMod 232908956281) ^ 1323346342 = 44692664107 := by
        calc
          (47 : ZMod 232908956281) ^ 1323346342 = (47 : ZMod 232908956281) ^ (661673171 + 661673171) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 661673171 * (47 : ZMod 232908956281) ^ 661673171 := by rw [pow_add]
          _ = 44692664107 := by rw [factor_4_29]; decide
      have factor_4_31 : (47 : ZMod 232908956281) ^ 2646692685 = 175571535923 := by
        calc
          (47 : ZMod 232908956281) ^ 2646692685 = (47 : ZMod 232908956281) ^ (1323346342 + 1323346342 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 1323346342 * (47 : ZMod 232908956281) ^ 1323346342) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 175571535923 := by rw [factor_4_30]; decide
      have factor_4_32 : (47 : ZMod 232908956281) ^ 5293385370 = 184965269239 := by
        calc
          (47 : ZMod 232908956281) ^ 5293385370 = (47 : ZMod 232908956281) ^ (2646692685 + 2646692685) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 2646692685 * (47 : ZMod 232908956281) ^ 2646692685 := by rw [pow_add]
          _ = 184965269239 := by rw [factor_4_31]; decide
      have factor_4_33 : (47 : ZMod 232908956281) ^ 10586770740 = 36459147863 := by
        calc
          (47 : ZMod 232908956281) ^ 10586770740 = (47 : ZMod 232908956281) ^ (5293385370 + 5293385370) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 5293385370 * (47 : ZMod 232908956281) ^ 5293385370 := by rw [pow_add]
          _ = 36459147863 := by rw [factor_4_32]; decide
      have factor_4_34 : (47 : ZMod 232908956281) ^ 21173541480 = 103802815453 := by
        calc
          (47 : ZMod 232908956281) ^ 21173541480 = (47 : ZMod 232908956281) ^ (10586770740 + 10586770740) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 10586770740 * (47 : ZMod 232908956281) ^ 10586770740 := by rw [pow_add]
          _ = 103802815453 := by rw [factor_4_33]; decide
      change (47 : ZMod 232908956281) ^ 21173541480 ≠ 1
      rw [factor_4_34]
      decide
    ·
      have factor_5_0 : (47 : ZMod 232908956281) ^ 1 = 47 := by norm_num
      have factor_5_1 : (47 : ZMod 232908956281) ^ 2 = 2209 := by
        calc
          (47 : ZMod 232908956281) ^ 2 = (47 : ZMod 232908956281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1 * (47 : ZMod 232908956281) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_5_0]; decide
      have factor_5_2 : (47 : ZMod 232908956281) ^ 4 = 4879681 := by
        calc
          (47 : ZMod 232908956281) ^ 4 = (47 : ZMod 232908956281) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 2 * (47 : ZMod 232908956281) ^ 2 := by rw [pow_add]
          _ = 4879681 := by rw [factor_5_1]; decide
      have factor_5_3 : (47 : ZMod 232908956281) ^ 8 = 54573121099 := by
        calc
          (47 : ZMod 232908956281) ^ 8 = (47 : ZMod 232908956281) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 4 * (47 : ZMod 232908956281) ^ 4 := by rw [pow_add]
          _ = 54573121099 := by rw [factor_5_2]; decide
      have factor_5_4 : (47 : ZMod 232908956281) ^ 16 = 134521319616 := by
        calc
          (47 : ZMod 232908956281) ^ 16 = (47 : ZMod 232908956281) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 8 * (47 : ZMod 232908956281) ^ 8 := by rw [pow_add]
          _ = 134521319616 := by rw [factor_5_3]; decide
      have factor_5_5 : (47 : ZMod 232908956281) ^ 33 = 142473382933 := by
        calc
          (47 : ZMod 232908956281) ^ 33 = (47 : ZMod 232908956281) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 16 * (47 : ZMod 232908956281) ^ 16) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 142473382933 := by rw [factor_5_4]; decide
      have factor_5_6 : (47 : ZMod 232908956281) ^ 66 = 197058641846 := by
        calc
          (47 : ZMod 232908956281) ^ 66 = (47 : ZMod 232908956281) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 33 * (47 : ZMod 232908956281) ^ 33 := by rw [pow_add]
          _ = 197058641846 := by rw [factor_5_5]; decide
      have factor_5_7 : (47 : ZMod 232908956281) ^ 133 = 22713886461 := by
        calc
          (47 : ZMod 232908956281) ^ 133 = (47 : ZMod 232908956281) ^ (66 + 66 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 66 * (47 : ZMod 232908956281) ^ 66) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 22713886461 := by rw [factor_5_6]; decide
      have factor_5_8 : (47 : ZMod 232908956281) ^ 266 = 43291539668 := by
        calc
          (47 : ZMod 232908956281) ^ 266 = (47 : ZMod 232908956281) ^ (133 + 133) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 133 * (47 : ZMod 232908956281) ^ 133 := by rw [pow_add]
          _ = 43291539668 := by rw [factor_5_7]; decide
      have factor_5_9 : (47 : ZMod 232908956281) ^ 533 = 144218814349 := by
        calc
          (47 : ZMod 232908956281) ^ 533 = (47 : ZMod 232908956281) ^ (266 + 266 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 266 * (47 : ZMod 232908956281) ^ 266) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 144218814349 := by rw [factor_5_8]; decide
      have factor_5_10 : (47 : ZMod 232908956281) ^ 1067 = 144156501739 := by
        calc
          (47 : ZMod 232908956281) ^ 1067 = (47 : ZMod 232908956281) ^ (533 + 533 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 533 * (47 : ZMod 232908956281) ^ 533) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 144156501739 := by rw [factor_5_9]; decide
      have factor_5_11 : (47 : ZMod 232908956281) ^ 2135 = 110361770989 := by
        calc
          (47 : ZMod 232908956281) ^ 2135 = (47 : ZMod 232908956281) ^ (1067 + 1067 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 1067 * (47 : ZMod 232908956281) ^ 1067) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 110361770989 := by rw [factor_5_10]; decide
      have factor_5_12 : (47 : ZMod 232908956281) ^ 4271 = 38937825898 := by
        calc
          (47 : ZMod 232908956281) ^ 4271 = (47 : ZMod 232908956281) ^ (2135 + 2135 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 2135 * (47 : ZMod 232908956281) ^ 2135) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 38937825898 := by rw [factor_5_11]; decide
      have factor_5_13 : (47 : ZMod 232908956281) ^ 8543 = 99736738203 := by
        calc
          (47 : ZMod 232908956281) ^ 8543 = (47 : ZMod 232908956281) ^ (4271 + 4271 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 4271 * (47 : ZMod 232908956281) ^ 4271) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 99736738203 := by rw [factor_5_12]; decide
      have factor_5_14 : (47 : ZMod 232908956281) ^ 17086 = 159877775117 := by
        calc
          (47 : ZMod 232908956281) ^ 17086 = (47 : ZMod 232908956281) ^ (8543 + 8543) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 8543 * (47 : ZMod 232908956281) ^ 8543 := by rw [pow_add]
          _ = 159877775117 := by rw [factor_5_13]; decide
      have factor_5_15 : (47 : ZMod 232908956281) ^ 34172 = 227710122787 := by
        calc
          (47 : ZMod 232908956281) ^ 34172 = (47 : ZMod 232908956281) ^ (17086 + 17086) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 17086 * (47 : ZMod 232908956281) ^ 17086 := by rw [pow_add]
          _ = 227710122787 := by rw [factor_5_14]; decide
      have factor_5_16 : (47 : ZMod 232908956281) ^ 68344 = 175042159732 := by
        calc
          (47 : ZMod 232908956281) ^ 68344 = (47 : ZMod 232908956281) ^ (34172 + 34172) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 34172 * (47 : ZMod 232908956281) ^ 34172 := by rw [pow_add]
          _ = 175042159732 := by rw [factor_5_15]; decide
      have factor_5_17 : (47 : ZMod 232908956281) ^ 136688 = 84574098605 := by
        calc
          (47 : ZMod 232908956281) ^ 136688 = (47 : ZMod 232908956281) ^ (68344 + 68344) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 68344 * (47 : ZMod 232908956281) ^ 68344 := by rw [pow_add]
          _ = 84574098605 := by rw [factor_5_16]; decide
      have factor_5_18 : (47 : ZMod 232908956281) ^ 273377 = 118406869206 := by
        calc
          (47 : ZMod 232908956281) ^ 273377 = (47 : ZMod 232908956281) ^ (136688 + 136688 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 136688 * (47 : ZMod 232908956281) ^ 136688) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 118406869206 := by rw [factor_5_17]; decide
      have factor_5_19 : (47 : ZMod 232908956281) ^ 546755 = 23322497376 := by
        calc
          (47 : ZMod 232908956281) ^ 546755 = (47 : ZMod 232908956281) ^ (273377 + 273377 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 273377 * (47 : ZMod 232908956281) ^ 273377) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 23322497376 := by rw [factor_5_18]; decide
      have factor_5_20 : (47 : ZMod 232908956281) ^ 1093510 = 47700295176 := by
        calc
          (47 : ZMod 232908956281) ^ 1093510 = (47 : ZMod 232908956281) ^ (546755 + 546755) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 546755 * (47 : ZMod 232908956281) ^ 546755 := by rw [pow_add]
          _ = 47700295176 := by rw [factor_5_19]; decide
      have factor_5_21 : (47 : ZMod 232908956281) ^ 2187020 = 161562333941 := by
        calc
          (47 : ZMod 232908956281) ^ 2187020 = (47 : ZMod 232908956281) ^ (1093510 + 1093510) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1093510 * (47 : ZMod 232908956281) ^ 1093510 := by rw [pow_add]
          _ = 161562333941 := by rw [factor_5_20]; decide
      have factor_5_22 : (47 : ZMod 232908956281) ^ 4374041 = 48636726564 := by
        calc
          (47 : ZMod 232908956281) ^ 4374041 = (47 : ZMod 232908956281) ^ (2187020 + 2187020 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 2187020 * (47 : ZMod 232908956281) ^ 2187020) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 48636726564 := by rw [factor_5_21]; decide
      have factor_5_23 : (47 : ZMod 232908956281) ^ 8748082 = 110512246568 := by
        calc
          (47 : ZMod 232908956281) ^ 8748082 = (47 : ZMod 232908956281) ^ (4374041 + 4374041) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 4374041 * (47 : ZMod 232908956281) ^ 4374041 := by rw [pow_add]
          _ = 110512246568 := by rw [factor_5_22]; decide
      have factor_5_24 : (47 : ZMod 232908956281) ^ 17496165 = 9461600468 := by
        calc
          (47 : ZMod 232908956281) ^ 17496165 = (47 : ZMod 232908956281) ^ (8748082 + 8748082 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 8748082 * (47 : ZMod 232908956281) ^ 8748082) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 9461600468 := by rw [factor_5_23]; decide
      have factor_5_25 : (47 : ZMod 232908956281) ^ 34992331 = 33676624862 := by
        calc
          (47 : ZMod 232908956281) ^ 34992331 = (47 : ZMod 232908956281) ^ (17496165 + 17496165 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 17496165 * (47 : ZMod 232908956281) ^ 17496165) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 33676624862 := by rw [factor_5_24]; decide
      have factor_5_26 : (47 : ZMod 232908956281) ^ 69984662 = 29803347149 := by
        calc
          (47 : ZMod 232908956281) ^ 69984662 = (47 : ZMod 232908956281) ^ (34992331 + 34992331) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 34992331 * (47 : ZMod 232908956281) ^ 34992331 := by rw [pow_add]
          _ = 29803347149 := by rw [factor_5_25]; decide
      have factor_5_27 : (47 : ZMod 232908956281) ^ 139969324 = 35843857483 := by
        calc
          (47 : ZMod 232908956281) ^ 139969324 = (47 : ZMod 232908956281) ^ (69984662 + 69984662) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 69984662 * (47 : ZMod 232908956281) ^ 69984662 := by rw [pow_add]
          _ = 35843857483 := by rw [factor_5_26]; decide
      have factor_5_28 : (47 : ZMod 232908956281) ^ 279938649 = 59701857059 := by
        calc
          (47 : ZMod 232908956281) ^ 279938649 = (47 : ZMod 232908956281) ^ (139969324 + 139969324 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 139969324 * (47 : ZMod 232908956281) ^ 139969324) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 59701857059 := by rw [factor_5_27]; decide
      have factor_5_29 : (47 : ZMod 232908956281) ^ 559877298 = 91838148861 := by
        calc
          (47 : ZMod 232908956281) ^ 559877298 = (47 : ZMod 232908956281) ^ (279938649 + 279938649) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 279938649 * (47 : ZMod 232908956281) ^ 279938649 := by rw [pow_add]
          _ = 91838148861 := by rw [factor_5_28]; decide
      have factor_5_30 : (47 : ZMod 232908956281) ^ 1119754597 = 217822354870 := by
        calc
          (47 : ZMod 232908956281) ^ 1119754597 = (47 : ZMod 232908956281) ^ (559877298 + 559877298 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 559877298 * (47 : ZMod 232908956281) ^ 559877298) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 217822354870 := by rw [factor_5_29]; decide
      have factor_5_31 : (47 : ZMod 232908956281) ^ 2239509195 = 218918133829 := by
        calc
          (47 : ZMod 232908956281) ^ 2239509195 = (47 : ZMod 232908956281) ^ (1119754597 + 1119754597 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 1119754597 * (47 : ZMod 232908956281) ^ 1119754597) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 218918133829 := by rw [factor_5_30]; decide
      have factor_5_32 : (47 : ZMod 232908956281) ^ 4479018390 = 66731099514 := by
        calc
          (47 : ZMod 232908956281) ^ 4479018390 = (47 : ZMod 232908956281) ^ (2239509195 + 2239509195) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 2239509195 * (47 : ZMod 232908956281) ^ 2239509195 := by rw [pow_add]
          _ = 66731099514 := by rw [factor_5_31]; decide
      have factor_5_33 : (47 : ZMod 232908956281) ^ 8958036780 = 173563222321 := by
        calc
          (47 : ZMod 232908956281) ^ 8958036780 = (47 : ZMod 232908956281) ^ (4479018390 + 4479018390) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 4479018390 * (47 : ZMod 232908956281) ^ 4479018390 := by rw [pow_add]
          _ = 173563222321 := by rw [factor_5_32]; decide
      have factor_5_34 : (47 : ZMod 232908956281) ^ 17916073560 = 56153709298 := by
        calc
          (47 : ZMod 232908956281) ^ 17916073560 = (47 : ZMod 232908956281) ^ (8958036780 + 8958036780) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 8958036780 * (47 : ZMod 232908956281) ^ 8958036780 := by rw [pow_add]
          _ = 56153709298 := by rw [factor_5_33]; decide
      change (47 : ZMod 232908956281) ^ 17916073560 ≠ 1
      rw [factor_5_34]
      decide
    ·
      have factor_6_0 : (47 : ZMod 232908956281) ^ 1 = 47 := by norm_num
      have factor_6_1 : (47 : ZMod 232908956281) ^ 3 = 103823 := by
        calc
          (47 : ZMod 232908956281) ^ 3 = (47 : ZMod 232908956281) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 1 * (47 : ZMod 232908956281) ^ 1) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_6_0]; decide
      have factor_6_2 : (47 : ZMod 232908956281) ^ 6 = 10779215329 := by
        calc
          (47 : ZMod 232908956281) ^ 6 = (47 : ZMod 232908956281) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 3 * (47 : ZMod 232908956281) ^ 3 := by rw [pow_add]
          _ = 10779215329 := by rw [factor_6_1]; decide
      have factor_6_3 : (47 : ZMod 232908956281) ^ 12 = 172066132697 := by
        calc
          (47 : ZMod 232908956281) ^ 12 = (47 : ZMod 232908956281) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 6 * (47 : ZMod 232908956281) ^ 6 := by rw [pow_add]
          _ = 172066132697 := by rw [factor_6_2]; decide
      have factor_6_4 : (47 : ZMod 232908956281) ^ 25 = 31291548163 := by
        calc
          (47 : ZMod 232908956281) ^ 25 = (47 : ZMod 232908956281) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 12 * (47 : ZMod 232908956281) ^ 12) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 31291548163 := by rw [factor_6_3]; decide
      have factor_6_5 : (47 : ZMod 232908956281) ^ 51 = 61038624347 := by
        calc
          (47 : ZMod 232908956281) ^ 51 = (47 : ZMod 232908956281) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 25 * (47 : ZMod 232908956281) ^ 25) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 61038624347 := by rw [factor_6_4]; decide
      have factor_6_6 : (47 : ZMod 232908956281) ^ 102 = 149898950641 := by
        calc
          (47 : ZMod 232908956281) ^ 102 = (47 : ZMod 232908956281) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 51 * (47 : ZMod 232908956281) ^ 51 := by rw [pow_add]
          _ = 149898950641 := by rw [factor_6_5]; decide
      have factor_6_7 : (47 : ZMod 232908956281) ^ 204 = 123187518833 := by
        calc
          (47 : ZMod 232908956281) ^ 204 = (47 : ZMod 232908956281) ^ (102 + 102) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 102 * (47 : ZMod 232908956281) ^ 102 := by rw [pow_add]
          _ = 123187518833 := by rw [factor_6_6]; decide
      have factor_6_8 : (47 : ZMod 232908956281) ^ 408 = 22170948487 := by
        calc
          (47 : ZMod 232908956281) ^ 408 = (47 : ZMod 232908956281) ^ (204 + 204) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 204 * (47 : ZMod 232908956281) ^ 204 := by rw [pow_add]
          _ = 22170948487 := by rw [factor_6_7]; decide
      have factor_6_9 : (47 : ZMod 232908956281) ^ 816 = 161830709868 := by
        calc
          (47 : ZMod 232908956281) ^ 816 = (47 : ZMod 232908956281) ^ (408 + 408) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 408 * (47 : ZMod 232908956281) ^ 408 := by rw [pow_add]
          _ = 161830709868 := by rw [factor_6_8]; decide
      have factor_6_10 : (47 : ZMod 232908956281) ^ 1633 = 66311365948 := by
        calc
          (47 : ZMod 232908956281) ^ 1633 = (47 : ZMod 232908956281) ^ (816 + 816 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 816 * (47 : ZMod 232908956281) ^ 816) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 66311365948 := by rw [factor_6_9]; decide
      have factor_6_11 : (47 : ZMod 232908956281) ^ 3266 = 24164978057 := by
        calc
          (47 : ZMod 232908956281) ^ 3266 = (47 : ZMod 232908956281) ^ (1633 + 1633) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1633 * (47 : ZMod 232908956281) ^ 1633 := by rw [pow_add]
          _ = 24164978057 := by rw [factor_6_10]; decide
      have factor_6_12 : (47 : ZMod 232908956281) ^ 6532 = 130099104783 := by
        calc
          (47 : ZMod 232908956281) ^ 6532 = (47 : ZMod 232908956281) ^ (3266 + 3266) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 3266 * (47 : ZMod 232908956281) ^ 3266 := by rw [pow_add]
          _ = 130099104783 := by rw [factor_6_11]; decide
      have factor_6_13 : (47 : ZMod 232908956281) ^ 13065 = 138620516811 := by
        calc
          (47 : ZMod 232908956281) ^ 13065 = (47 : ZMod 232908956281) ^ (6532 + 6532 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 6532 * (47 : ZMod 232908956281) ^ 6532) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 138620516811 := by rw [factor_6_12]; decide
      have factor_6_14 : (47 : ZMod 232908956281) ^ 26131 = 62318846222 := by
        calc
          (47 : ZMod 232908956281) ^ 26131 = (47 : ZMod 232908956281) ^ (13065 + 13065 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 13065 * (47 : ZMod 232908956281) ^ 13065) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 62318846222 := by rw [factor_6_13]; decide
      have factor_6_15 : (47 : ZMod 232908956281) ^ 52263 = 223025842469 := by
        calc
          (47 : ZMod 232908956281) ^ 52263 = (47 : ZMod 232908956281) ^ (26131 + 26131 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 26131 * (47 : ZMod 232908956281) ^ 26131) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 223025842469 := by rw [factor_6_14]; decide
      have factor_6_16 : (47 : ZMod 232908956281) ^ 104526 = 115907924039 := by
        calc
          (47 : ZMod 232908956281) ^ 104526 = (47 : ZMod 232908956281) ^ (52263 + 52263) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 52263 * (47 : ZMod 232908956281) ^ 52263 := by rw [pow_add]
          _ = 115907924039 := by rw [factor_6_15]; decide
      have factor_6_17 : (47 : ZMod 232908956281) ^ 209053 = 55239524378 := by
        calc
          (47 : ZMod 232908956281) ^ 209053 = (47 : ZMod 232908956281) ^ (104526 + 104526 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 104526 * (47 : ZMod 232908956281) ^ 104526) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 55239524378 := by rw [factor_6_16]; decide
      have factor_6_18 : (47 : ZMod 232908956281) ^ 418106 = 105196022270 := by
        calc
          (47 : ZMod 232908956281) ^ 418106 = (47 : ZMod 232908956281) ^ (209053 + 209053) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 209053 * (47 : ZMod 232908956281) ^ 209053 := by rw [pow_add]
          _ = 105196022270 := by rw [factor_6_17]; decide
      have factor_6_19 : (47 : ZMod 232908956281) ^ 836213 = 190749195539 := by
        calc
          (47 : ZMod 232908956281) ^ 836213 = (47 : ZMod 232908956281) ^ (418106 + 418106 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 418106 * (47 : ZMod 232908956281) ^ 418106) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 190749195539 := by rw [factor_6_18]; decide
      have factor_6_20 : (47 : ZMod 232908956281) ^ 1672427 = 88486515132 := by
        calc
          (47 : ZMod 232908956281) ^ 1672427 = (47 : ZMod 232908956281) ^ (836213 + 836213 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 836213 * (47 : ZMod 232908956281) ^ 836213) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 88486515132 := by rw [factor_6_19]; decide
      have factor_6_21 : (47 : ZMod 232908956281) ^ 3344855 = 230186285308 := by
        calc
          (47 : ZMod 232908956281) ^ 3344855 = (47 : ZMod 232908956281) ^ (1672427 + 1672427 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 1672427 * (47 : ZMod 232908956281) ^ 1672427) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 230186285308 := by rw [factor_6_20]; decide
      have factor_6_22 : (47 : ZMod 232908956281) ^ 6689710 = 170835354352 := by
        calc
          (47 : ZMod 232908956281) ^ 6689710 = (47 : ZMod 232908956281) ^ (3344855 + 3344855) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 3344855 * (47 : ZMod 232908956281) ^ 3344855 := by rw [pow_add]
          _ = 170835354352 := by rw [factor_6_21]; decide
      have factor_6_23 : (47 : ZMod 232908956281) ^ 13379420 = 127538981605 := by
        calc
          (47 : ZMod 232908956281) ^ 13379420 = (47 : ZMod 232908956281) ^ (6689710 + 6689710) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 6689710 * (47 : ZMod 232908956281) ^ 6689710 := by rw [pow_add]
          _ = 127538981605 := by rw [factor_6_22]; decide
      have factor_6_24 : (47 : ZMod 232908956281) ^ 26758841 = 110437751772 := by
        calc
          (47 : ZMod 232908956281) ^ 26758841 = (47 : ZMod 232908956281) ^ (13379420 + 13379420 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 13379420 * (47 : ZMod 232908956281) ^ 13379420) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 110437751772 := by rw [factor_6_23]; decide
      have factor_6_25 : (47 : ZMod 232908956281) ^ 53517682 = 148577040707 := by
        calc
          (47 : ZMod 232908956281) ^ 53517682 = (47 : ZMod 232908956281) ^ (26758841 + 26758841) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 26758841 * (47 : ZMod 232908956281) ^ 26758841 := by rw [pow_add]
          _ = 148577040707 := by rw [factor_6_24]; decide
      have factor_6_26 : (47 : ZMod 232908956281) ^ 107035365 = 2721608963 := by
        calc
          (47 : ZMod 232908956281) ^ 107035365 = (47 : ZMod 232908956281) ^ (53517682 + 53517682 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 53517682 * (47 : ZMod 232908956281) ^ 53517682) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 2721608963 := by rw [factor_6_25]; decide
      have factor_6_27 : (47 : ZMod 232908956281) ^ 214070731 = 150832574068 := by
        calc
          (47 : ZMod 232908956281) ^ 214070731 = (47 : ZMod 232908956281) ^ (107035365 + 107035365 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 107035365 * (47 : ZMod 232908956281) ^ 107035365) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 150832574068 := by rw [factor_6_26]; decide
      have factor_6_28 : (47 : ZMod 232908956281) ^ 428141463 = 50292746288 := by
        calc
          (47 : ZMod 232908956281) ^ 428141463 = (47 : ZMod 232908956281) ^ (214070731 + 214070731 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 214070731 * (47 : ZMod 232908956281) ^ 214070731) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 50292746288 := by rw [factor_6_27]; decide
      have factor_6_29 : (47 : ZMod 232908956281) ^ 856282927 = 27005691961 := by
        calc
          (47 : ZMod 232908956281) ^ 856282927 = (47 : ZMod 232908956281) ^ (428141463 + 428141463 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 428141463 * (47 : ZMod 232908956281) ^ 428141463) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 27005691961 := by rw [factor_6_28]; decide
      have factor_6_30 : (47 : ZMod 232908956281) ^ 1712565855 = 14837517537 := by
        calc
          (47 : ZMod 232908956281) ^ 1712565855 = (47 : ZMod 232908956281) ^ (856282927 + 856282927 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 856282927 * (47 : ZMod 232908956281) ^ 856282927) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 14837517537 := by rw [factor_6_29]; decide
      have factor_6_31 : (47 : ZMod 232908956281) ^ 3425131710 = 177306115812 := by
        calc
          (47 : ZMod 232908956281) ^ 3425131710 = (47 : ZMod 232908956281) ^ (1712565855 + 1712565855) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1712565855 * (47 : ZMod 232908956281) ^ 1712565855 := by rw [pow_add]
          _ = 177306115812 := by rw [factor_6_30]; decide
      have factor_6_32 : (47 : ZMod 232908956281) ^ 6850263420 = 104295686391 := by
        calc
          (47 : ZMod 232908956281) ^ 6850263420 = (47 : ZMod 232908956281) ^ (3425131710 + 3425131710) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 3425131710 * (47 : ZMod 232908956281) ^ 3425131710 := by rw [pow_add]
          _ = 104295686391 := by rw [factor_6_31]; decide
      have factor_6_33 : (47 : ZMod 232908956281) ^ 13700526840 = 184713315579 := by
        calc
          (47 : ZMod 232908956281) ^ 13700526840 = (47 : ZMod 232908956281) ^ (6850263420 + 6850263420) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 6850263420 * (47 : ZMod 232908956281) ^ 6850263420 := by rw [pow_add]
          _ = 184713315579 := by rw [factor_6_32]; decide
      change (47 : ZMod 232908956281) ^ 13700526840 ≠ 1
      rw [factor_6_33]
      decide
    ·
      have factor_7_0 : (47 : ZMod 232908956281) ^ 1 = 47 := by norm_num
      have factor_7_1 : (47 : ZMod 232908956281) ^ 2 = 2209 := by
        calc
          (47 : ZMod 232908956281) ^ 2 = (47 : ZMod 232908956281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1 * (47 : ZMod 232908956281) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_7_0]; decide
      have factor_7_2 : (47 : ZMod 232908956281) ^ 5 = 229345007 := by
        calc
          (47 : ZMod 232908956281) ^ 5 = (47 : ZMod 232908956281) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 2 * (47 : ZMod 232908956281) ^ 2) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 229345007 := by rw [factor_7_1]; decide
      have factor_7_3 : (47 : ZMod 232908956281) ^ 11 = 201881369871 := by
        calc
          (47 : ZMod 232908956281) ^ 11 = (47 : ZMod 232908956281) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 5 * (47 : ZMod 232908956281) ^ 5) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 201881369871 := by rw [factor_7_2]; decide
      have factor_7_4 : (47 : ZMod 232908956281) ^ 22 = 182795572129 := by
        calc
          (47 : ZMod 232908956281) ^ 22 = (47 : ZMod 232908956281) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 11 * (47 : ZMod 232908956281) ^ 11 := by rw [pow_add]
          _ = 182795572129 := by rw [factor_7_3]; decide
      have factor_7_5 : (47 : ZMod 232908956281) ^ 45 = 53886799551 := by
        calc
          (47 : ZMod 232908956281) ^ 45 = (47 : ZMod 232908956281) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 22 * (47 : ZMod 232908956281) ^ 22) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 53886799551 := by rw [factor_7_4]; decide
      have factor_7_6 : (47 : ZMod 232908956281) ^ 91 = 128011208625 := by
        calc
          (47 : ZMod 232908956281) ^ 91 = (47 : ZMod 232908956281) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 45 * (47 : ZMod 232908956281) ^ 45) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 128011208625 := by rw [factor_7_5]; decide
      have factor_7_7 : (47 : ZMod 232908956281) ^ 182 = 188075085220 := by
        calc
          (47 : ZMod 232908956281) ^ 182 = (47 : ZMod 232908956281) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 91 * (47 : ZMod 232908956281) ^ 91 := by rw [pow_add]
          _ = 188075085220 := by rw [factor_7_6]; decide
      have factor_7_8 : (47 : ZMod 232908956281) ^ 365 = 112894672779 := by
        calc
          (47 : ZMod 232908956281) ^ 365 = (47 : ZMod 232908956281) ^ (182 + 182 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 182 * (47 : ZMod 232908956281) ^ 182) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 112894672779 := by rw [factor_7_7]; decide
      have factor_7_9 : (47 : ZMod 232908956281) ^ 730 = 15714713567 := by
        calc
          (47 : ZMod 232908956281) ^ 730 = (47 : ZMod 232908956281) ^ (365 + 365) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 365 * (47 : ZMod 232908956281) ^ 365 := by rw [pow_add]
          _ = 15714713567 := by rw [factor_7_8]; decide
      have factor_7_10 : (47 : ZMod 232908956281) ^ 1461 = 170983045808 := by
        calc
          (47 : ZMod 232908956281) ^ 1461 = (47 : ZMod 232908956281) ^ (730 + 730 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 730 * (47 : ZMod 232908956281) ^ 730) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 170983045808 := by rw [factor_7_9]; decide
      have factor_7_11 : (47 : ZMod 232908956281) ^ 2922 = 95405579253 := by
        calc
          (47 : ZMod 232908956281) ^ 2922 = (47 : ZMod 232908956281) ^ (1461 + 1461) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1461 * (47 : ZMod 232908956281) ^ 1461 := by rw [pow_add]
          _ = 95405579253 := by rw [factor_7_10]; decide
      have factor_7_12 : (47 : ZMod 232908956281) ^ 5845 = 20533665810 := by
        calc
          (47 : ZMod 232908956281) ^ 5845 = (47 : ZMod 232908956281) ^ (2922 + 2922 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 2922 * (47 : ZMod 232908956281) ^ 2922) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 20533665810 := by rw [factor_7_11]; decide
      have factor_7_13 : (47 : ZMod 232908956281) ^ 11690 = 53703142180 := by
        calc
          (47 : ZMod 232908956281) ^ 11690 = (47 : ZMod 232908956281) ^ (5845 + 5845) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 5845 * (47 : ZMod 232908956281) ^ 5845 := by rw [pow_add]
          _ = 53703142180 := by rw [factor_7_12]; decide
      have factor_7_14 : (47 : ZMod 232908956281) ^ 23380 = 161045024476 := by
        calc
          (47 : ZMod 232908956281) ^ 23380 = (47 : ZMod 232908956281) ^ (11690 + 11690) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 11690 * (47 : ZMod 232908956281) ^ 11690 := by rw [pow_add]
          _ = 161045024476 := by rw [factor_7_13]; decide
      have factor_7_15 : (47 : ZMod 232908956281) ^ 46761 = 111032985665 := by
        calc
          (47 : ZMod 232908956281) ^ 46761 = (47 : ZMod 232908956281) ^ (23380 + 23380 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 23380 * (47 : ZMod 232908956281) ^ 23380) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 111032985665 := by rw [factor_7_14]; decide
      have factor_7_16 : (47 : ZMod 232908956281) ^ 93523 = 27252921657 := by
        calc
          (47 : ZMod 232908956281) ^ 93523 = (47 : ZMod 232908956281) ^ (46761 + 46761 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 46761 * (47 : ZMod 232908956281) ^ 46761) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 27252921657 := by rw [factor_7_15]; decide
      have factor_7_17 : (47 : ZMod 232908956281) ^ 187047 = 117034482522 := by
        calc
          (47 : ZMod 232908956281) ^ 187047 = (47 : ZMod 232908956281) ^ (93523 + 93523 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 93523 * (47 : ZMod 232908956281) ^ 93523) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 117034482522 := by rw [factor_7_16]; decide
      have factor_7_18 : (47 : ZMod 232908956281) ^ 374095 = 1018549134 := by
        calc
          (47 : ZMod 232908956281) ^ 374095 = (47 : ZMod 232908956281) ^ (187047 + 187047 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 187047 * (47 : ZMod 232908956281) ^ 187047) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 1018549134 := by rw [factor_7_17]; decide
      have factor_7_19 : (47 : ZMod 232908956281) ^ 748191 = 152236964285 := by
        calc
          (47 : ZMod 232908956281) ^ 748191 = (47 : ZMod 232908956281) ^ (374095 + 374095 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 374095 * (47 : ZMod 232908956281) ^ 374095) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 152236964285 := by rw [factor_7_18]; decide
      have factor_7_20 : (47 : ZMod 232908956281) ^ 1496382 = 180398205824 := by
        calc
          (47 : ZMod 232908956281) ^ 1496382 = (47 : ZMod 232908956281) ^ (748191 + 748191) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 748191 * (47 : ZMod 232908956281) ^ 748191 := by rw [pow_add]
          _ = 180398205824 := by rw [factor_7_19]; decide
      have factor_7_21 : (47 : ZMod 232908956281) ^ 2992765 = 204732623657 := by
        calc
          (47 : ZMod 232908956281) ^ 2992765 = (47 : ZMod 232908956281) ^ (1496382 + 1496382 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 1496382 * (47 : ZMod 232908956281) ^ 1496382) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 204732623657 := by rw [factor_7_20]; decide
      have factor_7_22 : (47 : ZMod 232908956281) ^ 5985530 = 49042875933 := by
        calc
          (47 : ZMod 232908956281) ^ 5985530 = (47 : ZMod 232908956281) ^ (2992765 + 2992765) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 2992765 * (47 : ZMod 232908956281) ^ 2992765 := by rw [pow_add]
          _ = 49042875933 := by rw [factor_7_21]; decide
      have factor_7_23 : (47 : ZMod 232908956281) ^ 11971060 = 157784316045 := by
        calc
          (47 : ZMod 232908956281) ^ 11971060 = (47 : ZMod 232908956281) ^ (5985530 + 5985530) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 5985530 * (47 : ZMod 232908956281) ^ 5985530 := by rw [pow_add]
          _ = 157784316045 := by rw [factor_7_22]; decide
      have factor_7_24 : (47 : ZMod 232908956281) ^ 23942121 = 207360485810 := by
        calc
          (47 : ZMod 232908956281) ^ 23942121 = (47 : ZMod 232908956281) ^ (11971060 + 11971060 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 11971060 * (47 : ZMod 232908956281) ^ 11971060) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 207360485810 := by rw [factor_7_23]; decide
      have factor_7_25 : (47 : ZMod 232908956281) ^ 47884242 = 51773093270 := by
        calc
          (47 : ZMod 232908956281) ^ 47884242 = (47 : ZMod 232908956281) ^ (23942121 + 23942121) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 23942121 * (47 : ZMod 232908956281) ^ 23942121 := by rw [pow_add]
          _ = 51773093270 := by rw [factor_7_24]; decide
      have factor_7_26 : (47 : ZMod 232908956281) ^ 95768485 = 156601379280 := by
        calc
          (47 : ZMod 232908956281) ^ 95768485 = (47 : ZMod 232908956281) ^ (47884242 + 47884242 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 47884242 * (47 : ZMod 232908956281) ^ 47884242) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 156601379280 := by rw [factor_7_25]; decide
      have factor_7_27 : (47 : ZMod 232908956281) ^ 191536970 = 94749800071 := by
        calc
          (47 : ZMod 232908956281) ^ 191536970 = (47 : ZMod 232908956281) ^ (95768485 + 95768485) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 95768485 * (47 : ZMod 232908956281) ^ 95768485 := by rw [pow_add]
          _ = 94749800071 := by rw [factor_7_26]; decide
      have factor_7_28 : (47 : ZMod 232908956281) ^ 383073941 = 128115868526 := by
        calc
          (47 : ZMod 232908956281) ^ 383073941 = (47 : ZMod 232908956281) ^ (191536970 + 191536970 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 191536970 * (47 : ZMod 232908956281) ^ 191536970) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 128115868526 := by rw [factor_7_27]; decide
      have factor_7_29 : (47 : ZMod 232908956281) ^ 766147882 = 201076237162 := by
        calc
          (47 : ZMod 232908956281) ^ 766147882 = (47 : ZMod 232908956281) ^ (383073941 + 383073941) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 383073941 * (47 : ZMod 232908956281) ^ 383073941 := by rw [pow_add]
          _ = 201076237162 := by rw [factor_7_28]; decide
      have factor_7_30 : (47 : ZMod 232908956281) ^ 1532295765 = 30350906087 := by
        calc
          (47 : ZMod 232908956281) ^ 1532295765 = (47 : ZMod 232908956281) ^ (766147882 + 766147882 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 766147882 * (47 : ZMod 232908956281) ^ 766147882) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 30350906087 := by rw [factor_7_29]; decide
      have factor_7_31 : (47 : ZMod 232908956281) ^ 3064591530 = 16316771429 := by
        calc
          (47 : ZMod 232908956281) ^ 3064591530 = (47 : ZMod 232908956281) ^ (1532295765 + 1532295765) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1532295765 * (47 : ZMod 232908956281) ^ 1532295765 := by rw [pow_add]
          _ = 16316771429 := by rw [factor_7_30]; decide
      have factor_7_32 : (47 : ZMod 232908956281) ^ 6129183060 = 25090711505 := by
        calc
          (47 : ZMod 232908956281) ^ 6129183060 = (47 : ZMod 232908956281) ^ (3064591530 + 3064591530) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 3064591530 * (47 : ZMod 232908956281) ^ 3064591530 := by rw [pow_add]
          _ = 25090711505 := by rw [factor_7_31]; decide
      have factor_7_33 : (47 : ZMod 232908956281) ^ 12258366120 = 109424258158 := by
        calc
          (47 : ZMod 232908956281) ^ 12258366120 = (47 : ZMod 232908956281) ^ (6129183060 + 6129183060) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 6129183060 * (47 : ZMod 232908956281) ^ 6129183060 := by rw [pow_add]
          _ = 109424258158 := by rw [factor_7_32]; decide
      change (47 : ZMod 232908956281) ^ 12258366120 ≠ 1
      rw [factor_7_33]
      decide
    ·
      have factor_8_0 : (47 : ZMod 232908956281) ^ 1 = 47 := by norm_num
      have factor_8_1 : (47 : ZMod 232908956281) ^ 2 = 2209 := by
        calc
          (47 : ZMod 232908956281) ^ 2 = (47 : ZMod 232908956281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1 * (47 : ZMod 232908956281) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_8_0]; decide
      have factor_8_2 : (47 : ZMod 232908956281) ^ 4 = 4879681 := by
        calc
          (47 : ZMod 232908956281) ^ 4 = (47 : ZMod 232908956281) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 2 * (47 : ZMod 232908956281) ^ 2 := by rw [pow_add]
          _ = 4879681 := by rw [factor_8_1]; decide
      have factor_8_3 : (47 : ZMod 232908956281) ^ 9 = 2938172562 := by
        calc
          (47 : ZMod 232908956281) ^ 9 = (47 : ZMod 232908956281) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 4 * (47 : ZMod 232908956281) ^ 4) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 2938172562 := by rw [factor_8_2]; decide
      have factor_8_4 : (47 : ZMod 232908956281) ^ 18 = 198675773469 := by
        calc
          (47 : ZMod 232908956281) ^ 18 = (47 : ZMod 232908956281) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 9 * (47 : ZMod 232908956281) ^ 9 := by rw [pow_add]
          _ = 198675773469 := by rw [factor_8_3]; decide
      have factor_8_5 : (47 : ZMod 232908956281) ^ 37 = 42836481770 := by
        calc
          (47 : ZMod 232908956281) ^ 37 = (47 : ZMod 232908956281) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 18 * (47 : ZMod 232908956281) ^ 18) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 42836481770 := by rw [factor_8_4]; decide
      have factor_8_6 : (47 : ZMod 232908956281) ^ 75 = 67321163941 := by
        calc
          (47 : ZMod 232908956281) ^ 75 = (47 : ZMod 232908956281) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 37 * (47 : ZMod 232908956281) ^ 37) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 67321163941 := by rw [factor_8_5]; decide
      have factor_8_7 : (47 : ZMod 232908956281) ^ 150 = 119693209710 := by
        calc
          (47 : ZMod 232908956281) ^ 150 = (47 : ZMod 232908956281) ^ (75 + 75) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 75 * (47 : ZMod 232908956281) ^ 75 := by rw [pow_add]
          _ = 119693209710 := by rw [factor_8_6]; decide
      have factor_8_8 : (47 : ZMod 232908956281) ^ 301 = 148600675418 := by
        calc
          (47 : ZMod 232908956281) ^ 301 = (47 : ZMod 232908956281) ^ (150 + 150 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 150 * (47 : ZMod 232908956281) ^ 150) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 148600675418 := by rw [factor_8_7]; decide
      have factor_8_9 : (47 : ZMod 232908956281) ^ 603 = 41922359546 := by
        calc
          (47 : ZMod 232908956281) ^ 603 = (47 : ZMod 232908956281) ^ (301 + 301 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 301 * (47 : ZMod 232908956281) ^ 301) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 41922359546 := by rw [factor_8_8]; decide
      have factor_8_10 : (47 : ZMod 232908956281) ^ 1207 = 52182743442 := by
        calc
          (47 : ZMod 232908956281) ^ 1207 = (47 : ZMod 232908956281) ^ (603 + 603 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 603 * (47 : ZMod 232908956281) ^ 603) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 52182743442 := by rw [factor_8_9]; decide
      have factor_8_11 : (47 : ZMod 232908956281) ^ 2414 = 51377608440 := by
        calc
          (47 : ZMod 232908956281) ^ 2414 = (47 : ZMod 232908956281) ^ (1207 + 1207) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1207 * (47 : ZMod 232908956281) ^ 1207 := by rw [pow_add]
          _ = 51377608440 := by rw [factor_8_10]; decide
      have factor_8_12 : (47 : ZMod 232908956281) ^ 4828 = 26025787273 := by
        calc
          (47 : ZMod 232908956281) ^ 4828 = (47 : ZMod 232908956281) ^ (2414 + 2414) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 2414 * (47 : ZMod 232908956281) ^ 2414 := by rw [pow_add]
          _ = 26025787273 := by rw [factor_8_11]; decide
      have factor_8_13 : (47 : ZMod 232908956281) ^ 9657 = 228354267543 := by
        calc
          (47 : ZMod 232908956281) ^ 9657 = (47 : ZMod 232908956281) ^ (4828 + 4828 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 4828 * (47 : ZMod 232908956281) ^ 4828) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 228354267543 := by rw [factor_8_12]; decide
      have factor_8_14 : (47 : ZMod 232908956281) ^ 19314 = 176654220413 := by
        calc
          (47 : ZMod 232908956281) ^ 19314 = (47 : ZMod 232908956281) ^ (9657 + 9657) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 9657 * (47 : ZMod 232908956281) ^ 9657 := by rw [pow_add]
          _ = 176654220413 := by rw [factor_8_13]; decide
      have factor_8_15 : (47 : ZMod 232908956281) ^ 38629 = 158030567508 := by
        calc
          (47 : ZMod 232908956281) ^ 38629 = (47 : ZMod 232908956281) ^ (19314 + 19314 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 19314 * (47 : ZMod 232908956281) ^ 19314) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 158030567508 := by rw [factor_8_14]; decide
      have factor_8_16 : (47 : ZMod 232908956281) ^ 77258 = 53561847180 := by
        calc
          (47 : ZMod 232908956281) ^ 77258 = (47 : ZMod 232908956281) ^ (38629 + 38629) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 38629 * (47 : ZMod 232908956281) ^ 38629 := by rw [pow_add]
          _ = 53561847180 := by rw [factor_8_15]; decide
      have factor_8_17 : (47 : ZMod 232908956281) ^ 154517 = 83402998432 := by
        calc
          (47 : ZMod 232908956281) ^ 154517 = (47 : ZMod 232908956281) ^ (77258 + 77258 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 77258 * (47 : ZMod 232908956281) ^ 77258) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 83402998432 := by rw [factor_8_16]; decide
      have factor_8_18 : (47 : ZMod 232908956281) ^ 309035 = 210358203476 := by
        calc
          (47 : ZMod 232908956281) ^ 309035 = (47 : ZMod 232908956281) ^ (154517 + 154517 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 154517 * (47 : ZMod 232908956281) ^ 154517) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 210358203476 := by rw [factor_8_17]; decide
      have factor_8_19 : (47 : ZMod 232908956281) ^ 618071 = 170209161697 := by
        calc
          (47 : ZMod 232908956281) ^ 618071 = (47 : ZMod 232908956281) ^ (309035 + 309035 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 309035 * (47 : ZMod 232908956281) ^ 309035) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 170209161697 := by rw [factor_8_18]; decide
      have factor_8_20 : (47 : ZMod 232908956281) ^ 1236142 = 150764410956 := by
        calc
          (47 : ZMod 232908956281) ^ 1236142 = (47 : ZMod 232908956281) ^ (618071 + 618071) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 618071 * (47 : ZMod 232908956281) ^ 618071 := by rw [pow_add]
          _ = 150764410956 := by rw [factor_8_19]; decide
      have factor_8_21 : (47 : ZMod 232908956281) ^ 2472284 = 187861462986 := by
        calc
          (47 : ZMod 232908956281) ^ 2472284 = (47 : ZMod 232908956281) ^ (1236142 + 1236142) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1236142 * (47 : ZMod 232908956281) ^ 1236142 := by rw [pow_add]
          _ = 187861462986 := by rw [factor_8_20]; decide
      have factor_8_22 : (47 : ZMod 232908956281) ^ 4944568 = 197837364824 := by
        calc
          (47 : ZMod 232908956281) ^ 4944568 = (47 : ZMod 232908956281) ^ (2472284 + 2472284) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 2472284 * (47 : ZMod 232908956281) ^ 2472284 := by rw [pow_add]
          _ = 197837364824 := by rw [factor_8_21]; decide
      have factor_8_23 : (47 : ZMod 232908956281) ^ 9889137 = 140961561097 := by
        calc
          (47 : ZMod 232908956281) ^ 9889137 = (47 : ZMod 232908956281) ^ (4944568 + 4944568 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 4944568 * (47 : ZMod 232908956281) ^ 4944568) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 140961561097 := by rw [factor_8_22]; decide
      have factor_8_24 : (47 : ZMod 232908956281) ^ 19778274 = 55900760354 := by
        calc
          (47 : ZMod 232908956281) ^ 19778274 = (47 : ZMod 232908956281) ^ (9889137 + 9889137) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 9889137 * (47 : ZMod 232908956281) ^ 9889137 := by rw [pow_add]
          _ = 55900760354 := by rw [factor_8_23]; decide
      have factor_8_25 : (47 : ZMod 232908956281) ^ 39556548 = 93462991439 := by
        calc
          (47 : ZMod 232908956281) ^ 39556548 = (47 : ZMod 232908956281) ^ (19778274 + 19778274) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 19778274 * (47 : ZMod 232908956281) ^ 19778274 := by rw [pow_add]
          _ = 93462991439 := by rw [factor_8_24]; decide
      have factor_8_26 : (47 : ZMod 232908956281) ^ 79113096 = 35589181919 := by
        calc
          (47 : ZMod 232908956281) ^ 79113096 = (47 : ZMod 232908956281) ^ (39556548 + 39556548) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 39556548 * (47 : ZMod 232908956281) ^ 39556548 := by rw [pow_add]
          _ = 35589181919 := by rw [factor_8_25]; decide
      have factor_8_27 : (47 : ZMod 232908956281) ^ 158226193 = 154378688725 := by
        calc
          (47 : ZMod 232908956281) ^ 158226193 = (47 : ZMod 232908956281) ^ (79113096 + 79113096 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 79113096 * (47 : ZMod 232908956281) ^ 79113096) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 154378688725 := by rw [factor_8_26]; decide
      have factor_8_28 : (47 : ZMod 232908956281) ^ 316452386 = 22596339087 := by
        calc
          (47 : ZMod 232908956281) ^ 316452386 = (47 : ZMod 232908956281) ^ (158226193 + 158226193) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 158226193 * (47 : ZMod 232908956281) ^ 158226193 := by rw [pow_add]
          _ = 22596339087 := by rw [factor_8_27]; decide
      have factor_8_29 : (47 : ZMod 232908956281) ^ 632904772 = 209956315722 := by
        calc
          (47 : ZMod 232908956281) ^ 632904772 = (47 : ZMod 232908956281) ^ (316452386 + 316452386) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 316452386 * (47 : ZMod 232908956281) ^ 316452386 := by rw [pow_add]
          _ = 209956315722 := by rw [factor_8_28]; decide
      have factor_8_30 : (47 : ZMod 232908956281) ^ 1265809545 = 202748253462 := by
        calc
          (47 : ZMod 232908956281) ^ 1265809545 = (47 : ZMod 232908956281) ^ (632904772 + 632904772 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 632904772 * (47 : ZMod 232908956281) ^ 632904772) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 202748253462 := by rw [factor_8_29]; decide
      have factor_8_31 : (47 : ZMod 232908956281) ^ 2531619090 = 93995135351 := by
        calc
          (47 : ZMod 232908956281) ^ 2531619090 = (47 : ZMod 232908956281) ^ (1265809545 + 1265809545) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1265809545 * (47 : ZMod 232908956281) ^ 1265809545 := by rw [pow_add]
          _ = 93995135351 := by rw [factor_8_30]; decide
      have factor_8_32 : (47 : ZMod 232908956281) ^ 5063238180 = 179449967960 := by
        calc
          (47 : ZMod 232908956281) ^ 5063238180 = (47 : ZMod 232908956281) ^ (2531619090 + 2531619090) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 2531619090 * (47 : ZMod 232908956281) ^ 2531619090 := by rw [pow_add]
          _ = 179449967960 := by rw [factor_8_31]; decide
      have factor_8_33 : (47 : ZMod 232908956281) ^ 10126476360 = 163354091662 := by
        calc
          (47 : ZMod 232908956281) ^ 10126476360 = (47 : ZMod 232908956281) ^ (5063238180 + 5063238180) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 5063238180 * (47 : ZMod 232908956281) ^ 5063238180 := by rw [pow_add]
          _ = 163354091662 := by rw [factor_8_32]; decide
      change (47 : ZMod 232908956281) ^ 10126476360 ≠ 1
      rw [factor_8_33]
      decide
    ·
      have factor_9_0 : (47 : ZMod 232908956281) ^ 1 = 47 := by norm_num
      have factor_9_1 : (47 : ZMod 232908956281) ^ 3 = 103823 := by
        calc
          (47 : ZMod 232908956281) ^ 3 = (47 : ZMod 232908956281) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 1 * (47 : ZMod 232908956281) ^ 1) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_9_0]; decide
      have factor_9_2 : (47 : ZMod 232908956281) ^ 7 = 40805207901 := by
        calc
          (47 : ZMod 232908956281) ^ 7 = (47 : ZMod 232908956281) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 3 * (47 : ZMod 232908956281) ^ 3) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 40805207901 := by rw [factor_9_1]; decide
      have factor_9_3 : (47 : ZMod 232908956281) ^ 14 = 219579433362 := by
        calc
          (47 : ZMod 232908956281) ^ 14 = (47 : ZMod 232908956281) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 7 * (47 : ZMod 232908956281) ^ 7 := by rw [pow_add]
          _ = 219579433362 := by rw [factor_9_2]; decide
      have factor_9_4 : (47 : ZMod 232908956281) ^ 29 = 223292271494 := by
        calc
          (47 : ZMod 232908956281) ^ 29 = (47 : ZMod 232908956281) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 14 * (47 : ZMod 232908956281) ^ 14) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 223292271494 := by rw [factor_9_3]; decide
      have factor_9_5 : (47 : ZMod 232908956281) ^ 59 = 91941462736 := by
        calc
          (47 : ZMod 232908956281) ^ 59 = (47 : ZMod 232908956281) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 29 * (47 : ZMod 232908956281) ^ 29) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 91941462736 := by rw [factor_9_4]; decide
      have factor_9_6 : (47 : ZMod 232908956281) ^ 119 = 216484783953 := by
        calc
          (47 : ZMod 232908956281) ^ 119 = (47 : ZMod 232908956281) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 59 * (47 : ZMod 232908956281) ^ 59) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 216484783953 := by rw [factor_9_5]; decide
      have factor_9_7 : (47 : ZMod 232908956281) ^ 239 = 209689198352 := by
        calc
          (47 : ZMod 232908956281) ^ 239 = (47 : ZMod 232908956281) ^ (119 + 119 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 119 * (47 : ZMod 232908956281) ^ 119) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 209689198352 := by rw [factor_9_6]; decide
      have factor_9_8 : (47 : ZMod 232908956281) ^ 478 = 157011035291 := by
        calc
          (47 : ZMod 232908956281) ^ 478 = (47 : ZMod 232908956281) ^ (239 + 239) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 239 * (47 : ZMod 232908956281) ^ 239 := by rw [pow_add]
          _ = 157011035291 := by rw [factor_9_7]; decide
      have factor_9_9 : (47 : ZMod 232908956281) ^ 957 = 211830788980 := by
        calc
          (47 : ZMod 232908956281) ^ 957 = (47 : ZMod 232908956281) ^ (478 + 478 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 478 * (47 : ZMod 232908956281) ^ 478) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 211830788980 := by rw [factor_9_8]; decide
      have factor_9_10 : (47 : ZMod 232908956281) ^ 1914 = 78692550339 := by
        calc
          (47 : ZMod 232908956281) ^ 1914 = (47 : ZMod 232908956281) ^ (957 + 957) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 957 * (47 : ZMod 232908956281) ^ 957 := by rw [pow_add]
          _ = 78692550339 := by rw [factor_9_9]; decide
      have factor_9_11 : (47 : ZMod 232908956281) ^ 3829 = 116142578877 := by
        calc
          (47 : ZMod 232908956281) ^ 3829 = (47 : ZMod 232908956281) ^ (1914 + 1914 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 1914 * (47 : ZMod 232908956281) ^ 1914) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 116142578877 := by rw [factor_9_10]; decide
      have factor_9_12 : (47 : ZMod 232908956281) ^ 7659 = 74884456519 := by
        calc
          (47 : ZMod 232908956281) ^ 7659 = (47 : ZMod 232908956281) ^ (3829 + 3829 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 3829 * (47 : ZMod 232908956281) ^ 3829) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 74884456519 := by rw [factor_9_11]; decide
      have factor_9_13 : (47 : ZMod 232908956281) ^ 15318 = 18299054949 := by
        calc
          (47 : ZMod 232908956281) ^ 15318 = (47 : ZMod 232908956281) ^ (7659 + 7659) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 7659 * (47 : ZMod 232908956281) ^ 7659 := by rw [pow_add]
          _ = 18299054949 := by rw [factor_9_12]; decide
      have factor_9_14 : (47 : ZMod 232908956281) ^ 30637 = 135775829891 := by
        calc
          (47 : ZMod 232908956281) ^ 30637 = (47 : ZMod 232908956281) ^ (15318 + 15318 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 15318 * (47 : ZMod 232908956281) ^ 15318) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 135775829891 := by rw [factor_9_13]; decide
      have factor_9_15 : (47 : ZMod 232908956281) ^ 61274 = 179123720593 := by
        calc
          (47 : ZMod 232908956281) ^ 61274 = (47 : ZMod 232908956281) ^ (30637 + 30637) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 30637 * (47 : ZMod 232908956281) ^ 30637 := by rw [pow_add]
          _ = 179123720593 := by rw [factor_9_14]; decide
      have factor_9_16 : (47 : ZMod 232908956281) ^ 122548 = 217496243631 := by
        calc
          (47 : ZMod 232908956281) ^ 122548 = (47 : ZMod 232908956281) ^ (61274 + 61274) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 61274 * (47 : ZMod 232908956281) ^ 61274 := by rw [pow_add]
          _ = 217496243631 := by rw [factor_9_15]; decide
      have factor_9_17 : (47 : ZMod 232908956281) ^ 245097 = 114553314711 := by
        calc
          (47 : ZMod 232908956281) ^ 245097 = (47 : ZMod 232908956281) ^ (122548 + 122548 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 122548 * (47 : ZMod 232908956281) ^ 122548) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 114553314711 := by rw [factor_9_16]; decide
      have factor_9_18 : (47 : ZMod 232908956281) ^ 490194 = 1044898114 := by
        calc
          (47 : ZMod 232908956281) ^ 490194 = (47 : ZMod 232908956281) ^ (245097 + 245097) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 245097 * (47 : ZMod 232908956281) ^ 245097 := by rw [pow_add]
          _ = 1044898114 := by rw [factor_9_17]; decide
      have factor_9_19 : (47 : ZMod 232908956281) ^ 980388 = 96103187676 := by
        calc
          (47 : ZMod 232908956281) ^ 980388 = (47 : ZMod 232908956281) ^ (490194 + 490194) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 490194 * (47 : ZMod 232908956281) ^ 490194 := by rw [pow_add]
          _ = 96103187676 := by rw [factor_9_18]; decide
      have factor_9_20 : (47 : ZMod 232908956281) ^ 1960777 = 25165260440 := by
        calc
          (47 : ZMod 232908956281) ^ 1960777 = (47 : ZMod 232908956281) ^ (980388 + 980388 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 980388 * (47 : ZMod 232908956281) ^ 980388) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 25165260440 := by rw [factor_9_19]; decide
      have factor_9_21 : (47 : ZMod 232908956281) ^ 3921554 = 77279414123 := by
        calc
          (47 : ZMod 232908956281) ^ 3921554 = (47 : ZMod 232908956281) ^ (1960777 + 1960777) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1960777 * (47 : ZMod 232908956281) ^ 1960777 := by rw [pow_add]
          _ = 77279414123 := by rw [factor_9_20]; decide
      have factor_9_22 : (47 : ZMod 232908956281) ^ 7843108 = 35901073481 := by
        calc
          (47 : ZMod 232908956281) ^ 7843108 = (47 : ZMod 232908956281) ^ (3921554 + 3921554) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 3921554 * (47 : ZMod 232908956281) ^ 3921554 := by rw [pow_add]
          _ = 35901073481 := by rw [factor_9_21]; decide
      have factor_9_23 : (47 : ZMod 232908956281) ^ 15686217 = 93317853101 := by
        calc
          (47 : ZMod 232908956281) ^ 15686217 = (47 : ZMod 232908956281) ^ (7843108 + 7843108 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 7843108 * (47 : ZMod 232908956281) ^ 7843108) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 93317853101 := by rw [factor_9_22]; decide
      have factor_9_24 : (47 : ZMod 232908956281) ^ 31372434 = 41361896022 := by
        calc
          (47 : ZMod 232908956281) ^ 31372434 = (47 : ZMod 232908956281) ^ (15686217 + 15686217) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 15686217 * (47 : ZMod 232908956281) ^ 15686217 := by rw [pow_add]
          _ = 41361896022 := by rw [factor_9_23]; decide
      have factor_9_25 : (47 : ZMod 232908956281) ^ 62744869 = 7982736090 := by
        calc
          (47 : ZMod 232908956281) ^ 62744869 = (47 : ZMod 232908956281) ^ (31372434 + 31372434 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 31372434 * (47 : ZMod 232908956281) ^ 31372434) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 7982736090 := by rw [factor_9_24]; decide
      have factor_9_26 : (47 : ZMod 232908956281) ^ 125489739 = 19687251879 := by
        calc
          (47 : ZMod 232908956281) ^ 125489739 = (47 : ZMod 232908956281) ^ (62744869 + 62744869 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 62744869 * (47 : ZMod 232908956281) ^ 62744869) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 19687251879 := by rw [factor_9_25]; decide
      have factor_9_27 : (47 : ZMod 232908956281) ^ 250979478 = 189615073471 := by
        calc
          (47 : ZMod 232908956281) ^ 250979478 = (47 : ZMod 232908956281) ^ (125489739 + 125489739) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 125489739 * (47 : ZMod 232908956281) ^ 125489739 := by rw [pow_add]
          _ = 189615073471 := by rw [factor_9_26]; decide
      have factor_9_28 : (47 : ZMod 232908956281) ^ 501958957 = 42884903160 := by
        calc
          (47 : ZMod 232908956281) ^ 501958957 = (47 : ZMod 232908956281) ^ (250979478 + 250979478 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 250979478 * (47 : ZMod 232908956281) ^ 250979478) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 42884903160 := by rw [factor_9_27]; decide
      have factor_9_29 : (47 : ZMod 232908956281) ^ 1003917915 = 176311905281 := by
        calc
          (47 : ZMod 232908956281) ^ 1003917915 = (47 : ZMod 232908956281) ^ (501958957 + 501958957 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = ((47 : ZMod 232908956281) ^ 501958957 * (47 : ZMod 232908956281) ^ 501958957) * (47 : ZMod 232908956281) := by rw [pow_succ, pow_add]
          _ = 176311905281 := by rw [factor_9_28]; decide
      have factor_9_30 : (47 : ZMod 232908956281) ^ 2007835830 = 161674986894 := by
        calc
          (47 : ZMod 232908956281) ^ 2007835830 = (47 : ZMod 232908956281) ^ (1003917915 + 1003917915) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 1003917915 * (47 : ZMod 232908956281) ^ 1003917915 := by rw [pow_add]
          _ = 161674986894 := by rw [factor_9_29]; decide
      have factor_9_31 : (47 : ZMod 232908956281) ^ 4015671660 = 228880149638 := by
        calc
          (47 : ZMod 232908956281) ^ 4015671660 = (47 : ZMod 232908956281) ^ (2007835830 + 2007835830) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 2007835830 * (47 : ZMod 232908956281) ^ 2007835830 := by rw [pow_add]
          _ = 228880149638 := by rw [factor_9_30]; decide
      have factor_9_32 : (47 : ZMod 232908956281) ^ 8031343320 = 110830327140 := by
        calc
          (47 : ZMod 232908956281) ^ 8031343320 = (47 : ZMod 232908956281) ^ (4015671660 + 4015671660) :=
            congrArg (fun n : ℕ => (47 : ZMod 232908956281) ^ n) (by norm_num)
          _ = (47 : ZMod 232908956281) ^ 4015671660 * (47 : ZMod 232908956281) ^ 4015671660 := by rw [pow_add]
          _ = 110830327140 := by rw [factor_9_31]; decide
      change (47 : ZMod 232908956281) ^ 8031343320 ≠ 1
      rw [factor_9_32]
      decide

#print axioms prime_lucas_232908956281

end TotientTailPeriodKiller
end Erdos249257
