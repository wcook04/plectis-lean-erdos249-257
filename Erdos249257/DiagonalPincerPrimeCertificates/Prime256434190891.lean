import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_256434190891 : Nat.Prime 256434190891 := by
  apply lucas_primality 256434190891 (2 : ZMod 256434190891)
  ·
      have fermat_0 : (2 : ZMod 256434190891) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 256434190891) ^ 3 = 8 := by
        calc
          (2 : ZMod 256434190891) ^ 3 = (2 : ZMod 256434190891) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 1 * (2 : ZMod 256434190891) ^ 1) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 256434190891) ^ 7 = 128 := by
        calc
          (2 : ZMod 256434190891) ^ 7 = (2 : ZMod 256434190891) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 3 * (2 : ZMod 256434190891) ^ 3) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 256434190891) ^ 14 = 16384 := by
        calc
          (2 : ZMod 256434190891) ^ 14 = (2 : ZMod 256434190891) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 7 * (2 : ZMod 256434190891) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 256434190891) ^ 29 = 536870912 := by
        calc
          (2 : ZMod 256434190891) ^ 29 = (2 : ZMod 256434190891) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 14 * (2 : ZMod 256434190891) ^ 14) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 536870912 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 256434190891) ^ 59 = 24824937071 := by
        calc
          (2 : ZMod 256434190891) ^ 59 = (2 : ZMod 256434190891) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 29 * (2 : ZMod 256434190891) ^ 29) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 24824937071 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 256434190891) ^ 119 = 210176522860 := by
        calc
          (2 : ZMod 256434190891) ^ 119 = (2 : ZMod 256434190891) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 59 * (2 : ZMod 256434190891) ^ 59) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 210176522860 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 256434190891) ^ 238 = 69832647277 := by
        calc
          (2 : ZMod 256434190891) ^ 238 = (2 : ZMod 256434190891) ^ (119 + 119) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 119 * (2 : ZMod 256434190891) ^ 119 := by rw [pow_add]
          _ = 69832647277 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 256434190891) ^ 477 = 94538619074 := by
        calc
          (2 : ZMod 256434190891) ^ 477 = (2 : ZMod 256434190891) ^ (238 + 238 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 238 * (2 : ZMod 256434190891) ^ 238) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 94538619074 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 256434190891) ^ 955 = 246190920937 := by
        calc
          (2 : ZMod 256434190891) ^ 955 = (2 : ZMod 256434190891) ^ (477 + 477 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 477 * (2 : ZMod 256434190891) ^ 477) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 246190920937 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 256434190891) ^ 1910 = 237484422601 := by
        calc
          (2 : ZMod 256434190891) ^ 1910 = (2 : ZMod 256434190891) ^ (955 + 955) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 955 * (2 : ZMod 256434190891) ^ 955 := by rw [pow_add]
          _ = 237484422601 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 256434190891) ^ 3821 = 71213206875 := by
        calc
          (2 : ZMod 256434190891) ^ 3821 = (2 : ZMod 256434190891) ^ (1910 + 1910 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 1910 * (2 : ZMod 256434190891) ^ 1910) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 71213206875 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 256434190891) ^ 7642 = 132269505894 := by
        calc
          (2 : ZMod 256434190891) ^ 7642 = (2 : ZMod 256434190891) ^ (3821 + 3821) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 3821 * (2 : ZMod 256434190891) ^ 3821 := by rw [pow_add]
          _ = 132269505894 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 256434190891) ^ 15284 = 52178141444 := by
        calc
          (2 : ZMod 256434190891) ^ 15284 = (2 : ZMod 256434190891) ^ (7642 + 7642) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 7642 * (2 : ZMod 256434190891) ^ 7642 := by rw [pow_add]
          _ = 52178141444 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 256434190891) ^ 30569 = 91487490709 := by
        calc
          (2 : ZMod 256434190891) ^ 30569 = (2 : ZMod 256434190891) ^ (15284 + 15284 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 15284 * (2 : ZMod 256434190891) ^ 15284) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 91487490709 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 256434190891) ^ 61138 = 54055685937 := by
        calc
          (2 : ZMod 256434190891) ^ 61138 = (2 : ZMod 256434190891) ^ (30569 + 30569) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 30569 * (2 : ZMod 256434190891) ^ 30569 := by rw [pow_add]
          _ = 54055685937 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 256434190891) ^ 122277 = 168915694162 := by
        calc
          (2 : ZMod 256434190891) ^ 122277 = (2 : ZMod 256434190891) ^ (61138 + 61138 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 61138 * (2 : ZMod 256434190891) ^ 61138) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 168915694162 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 256434190891) ^ 244554 = 234542856966 := by
        calc
          (2 : ZMod 256434190891) ^ 244554 = (2 : ZMod 256434190891) ^ (122277 + 122277) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 122277 * (2 : ZMod 256434190891) ^ 122277 := by rw [pow_add]
          _ = 234542856966 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 256434190891) ^ 489109 = 9906925321 := by
        calc
          (2 : ZMod 256434190891) ^ 489109 = (2 : ZMod 256434190891) ^ (244554 + 244554 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 244554 * (2 : ZMod 256434190891) ^ 244554) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 9906925321 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 256434190891) ^ 978218 = 213464917438 := by
        calc
          (2 : ZMod 256434190891) ^ 978218 = (2 : ZMod 256434190891) ^ (489109 + 489109) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 489109 * (2 : ZMod 256434190891) ^ 489109 := by rw [pow_add]
          _ = 213464917438 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 256434190891) ^ 1956437 = 120504441926 := by
        calc
          (2 : ZMod 256434190891) ^ 1956437 = (2 : ZMod 256434190891) ^ (978218 + 978218 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 978218 * (2 : ZMod 256434190891) ^ 978218) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 120504441926 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 256434190891) ^ 3912875 = 232758363453 := by
        calc
          (2 : ZMod 256434190891) ^ 3912875 = (2 : ZMod 256434190891) ^ (1956437 + 1956437 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 1956437 * (2 : ZMod 256434190891) ^ 1956437) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 232758363453 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 256434190891) ^ 7825750 = 99736254599 := by
        calc
          (2 : ZMod 256434190891) ^ 7825750 = (2 : ZMod 256434190891) ^ (3912875 + 3912875) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 3912875 * (2 : ZMod 256434190891) ^ 3912875 := by rw [pow_add]
          _ = 99736254599 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 256434190891) ^ 15651500 = 181556929223 := by
        calc
          (2 : ZMod 256434190891) ^ 15651500 = (2 : ZMod 256434190891) ^ (7825750 + 7825750) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 7825750 * (2 : ZMod 256434190891) ^ 7825750 := by rw [pow_add]
          _ = 181556929223 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 256434190891) ^ 31303001 = 8245444126 := by
        calc
          (2 : ZMod 256434190891) ^ 31303001 = (2 : ZMod 256434190891) ^ (15651500 + 15651500 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 15651500 * (2 : ZMod 256434190891) ^ 15651500) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 8245444126 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 256434190891) ^ 62606003 = 214058872568 := by
        calc
          (2 : ZMod 256434190891) ^ 62606003 = (2 : ZMod 256434190891) ^ (31303001 + 31303001 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 31303001 * (2 : ZMod 256434190891) ^ 31303001) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 214058872568 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 256434190891) ^ 125212007 = 43806774165 := by
        calc
          (2 : ZMod 256434190891) ^ 125212007 = (2 : ZMod 256434190891) ^ (62606003 + 62606003 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 62606003 * (2 : ZMod 256434190891) ^ 62606003) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 43806774165 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 256434190891) ^ 250424014 = 86640452647 := by
        calc
          (2 : ZMod 256434190891) ^ 250424014 = (2 : ZMod 256434190891) ^ (125212007 + 125212007) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 125212007 * (2 : ZMod 256434190891) ^ 125212007 := by rw [pow_add]
          _ = 86640452647 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 256434190891) ^ 500848029 = 71697211750 := by
        calc
          (2 : ZMod 256434190891) ^ 500848029 = (2 : ZMod 256434190891) ^ (250424014 + 250424014 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 250424014 * (2 : ZMod 256434190891) ^ 250424014) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 71697211750 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 256434190891) ^ 1001696058 = 128699649474 := by
        calc
          (2 : ZMod 256434190891) ^ 1001696058 = (2 : ZMod 256434190891) ^ (500848029 + 500848029) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 500848029 * (2 : ZMod 256434190891) ^ 500848029 := by rw [pow_add]
          _ = 128699649474 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 256434190891) ^ 2003392116 = 53847072402 := by
        calc
          (2 : ZMod 256434190891) ^ 2003392116 = (2 : ZMod 256434190891) ^ (1001696058 + 1001696058) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 1001696058 * (2 : ZMod 256434190891) ^ 1001696058 := by rw [pow_add]
          _ = 53847072402 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 256434190891) ^ 4006784232 = 88664223108 := by
        calc
          (2 : ZMod 256434190891) ^ 4006784232 = (2 : ZMod 256434190891) ^ (2003392116 + 2003392116) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 2003392116 * (2 : ZMod 256434190891) ^ 2003392116 := by rw [pow_add]
          _ = 88664223108 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 256434190891) ^ 8013568465 = 44100764003 := by
        calc
          (2 : ZMod 256434190891) ^ 8013568465 = (2 : ZMod 256434190891) ^ (4006784232 + 4006784232 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 4006784232 * (2 : ZMod 256434190891) ^ 4006784232) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 44100764003 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 256434190891) ^ 16027136930 = 60145443659 := by
        calc
          (2 : ZMod 256434190891) ^ 16027136930 = (2 : ZMod 256434190891) ^ (8013568465 + 8013568465) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 8013568465 * (2 : ZMod 256434190891) ^ 8013568465 := by rw [pow_add]
          _ = 60145443659 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 256434190891) ^ 32054273861 = 3891359137 := by
        calc
          (2 : ZMod 256434190891) ^ 32054273861 = (2 : ZMod 256434190891) ^ (16027136930 + 16027136930 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 16027136930 * (2 : ZMod 256434190891) ^ 16027136930) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 3891359137 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 256434190891) ^ 64108547722 = 15807451485 := by
        calc
          (2 : ZMod 256434190891) ^ 64108547722 = (2 : ZMod 256434190891) ^ (32054273861 + 32054273861) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 32054273861 * (2 : ZMod 256434190891) ^ 32054273861 := by rw [pow_add]
          _ = 15807451485 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 256434190891) ^ 128217095445 = 256434190890 := by
        calc
          (2 : ZMod 256434190891) ^ 128217095445 = (2 : ZMod 256434190891) ^ (64108547722 + 64108547722 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 64108547722 * (2 : ZMod 256434190891) ^ 64108547722) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 256434190890 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 256434190891) ^ 256434190890 = 1 := by
        calc
          (2 : ZMod 256434190891) ^ 256434190890 = (2 : ZMod 256434190891) ^ (128217095445 + 128217095445) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 128217095445 * (2 : ZMod 256434190891) ^ 128217095445 := by rw [pow_add]
          _ = 1 := by rw [fermat_36]; decide
      simpa using fermat_37
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (17, 1), (6703, 1), (75013, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (17, 1), (6703, 1), (75013, 1)] : List FactorBlock).map factorBlockValue).prod = 256434190891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 256434190891) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 256434190891) ^ 3 = 8 := by
        calc
          (2 : ZMod 256434190891) ^ 3 = (2 : ZMod 256434190891) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 1 * (2 : ZMod 256434190891) ^ 1) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 256434190891) ^ 7 = 128 := by
        calc
          (2 : ZMod 256434190891) ^ 7 = (2 : ZMod 256434190891) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 3 * (2 : ZMod 256434190891) ^ 3) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 256434190891) ^ 14 = 16384 := by
        calc
          (2 : ZMod 256434190891) ^ 14 = (2 : ZMod 256434190891) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 7 * (2 : ZMod 256434190891) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 256434190891) ^ 29 = 536870912 := by
        calc
          (2 : ZMod 256434190891) ^ 29 = (2 : ZMod 256434190891) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 14 * (2 : ZMod 256434190891) ^ 14) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 536870912 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 256434190891) ^ 59 = 24824937071 := by
        calc
          (2 : ZMod 256434190891) ^ 59 = (2 : ZMod 256434190891) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 29 * (2 : ZMod 256434190891) ^ 29) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 24824937071 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 256434190891) ^ 119 = 210176522860 := by
        calc
          (2 : ZMod 256434190891) ^ 119 = (2 : ZMod 256434190891) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 59 * (2 : ZMod 256434190891) ^ 59) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 210176522860 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 256434190891) ^ 238 = 69832647277 := by
        calc
          (2 : ZMod 256434190891) ^ 238 = (2 : ZMod 256434190891) ^ (119 + 119) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 119 * (2 : ZMod 256434190891) ^ 119 := by rw [pow_add]
          _ = 69832647277 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 256434190891) ^ 477 = 94538619074 := by
        calc
          (2 : ZMod 256434190891) ^ 477 = (2 : ZMod 256434190891) ^ (238 + 238 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 238 * (2 : ZMod 256434190891) ^ 238) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 94538619074 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 256434190891) ^ 955 = 246190920937 := by
        calc
          (2 : ZMod 256434190891) ^ 955 = (2 : ZMod 256434190891) ^ (477 + 477 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 477 * (2 : ZMod 256434190891) ^ 477) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 246190920937 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 256434190891) ^ 1910 = 237484422601 := by
        calc
          (2 : ZMod 256434190891) ^ 1910 = (2 : ZMod 256434190891) ^ (955 + 955) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 955 * (2 : ZMod 256434190891) ^ 955 := by rw [pow_add]
          _ = 237484422601 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 256434190891) ^ 3821 = 71213206875 := by
        calc
          (2 : ZMod 256434190891) ^ 3821 = (2 : ZMod 256434190891) ^ (1910 + 1910 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 1910 * (2 : ZMod 256434190891) ^ 1910) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 71213206875 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 256434190891) ^ 7642 = 132269505894 := by
        calc
          (2 : ZMod 256434190891) ^ 7642 = (2 : ZMod 256434190891) ^ (3821 + 3821) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 3821 * (2 : ZMod 256434190891) ^ 3821 := by rw [pow_add]
          _ = 132269505894 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 256434190891) ^ 15284 = 52178141444 := by
        calc
          (2 : ZMod 256434190891) ^ 15284 = (2 : ZMod 256434190891) ^ (7642 + 7642) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 7642 * (2 : ZMod 256434190891) ^ 7642 := by rw [pow_add]
          _ = 52178141444 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 256434190891) ^ 30569 = 91487490709 := by
        calc
          (2 : ZMod 256434190891) ^ 30569 = (2 : ZMod 256434190891) ^ (15284 + 15284 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 15284 * (2 : ZMod 256434190891) ^ 15284) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 91487490709 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 256434190891) ^ 61138 = 54055685937 := by
        calc
          (2 : ZMod 256434190891) ^ 61138 = (2 : ZMod 256434190891) ^ (30569 + 30569) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 30569 * (2 : ZMod 256434190891) ^ 30569 := by rw [pow_add]
          _ = 54055685937 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 256434190891) ^ 122277 = 168915694162 := by
        calc
          (2 : ZMod 256434190891) ^ 122277 = (2 : ZMod 256434190891) ^ (61138 + 61138 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 61138 * (2 : ZMod 256434190891) ^ 61138) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 168915694162 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 256434190891) ^ 244554 = 234542856966 := by
        calc
          (2 : ZMod 256434190891) ^ 244554 = (2 : ZMod 256434190891) ^ (122277 + 122277) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 122277 * (2 : ZMod 256434190891) ^ 122277 := by rw [pow_add]
          _ = 234542856966 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 256434190891) ^ 489109 = 9906925321 := by
        calc
          (2 : ZMod 256434190891) ^ 489109 = (2 : ZMod 256434190891) ^ (244554 + 244554 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 244554 * (2 : ZMod 256434190891) ^ 244554) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 9906925321 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 256434190891) ^ 978218 = 213464917438 := by
        calc
          (2 : ZMod 256434190891) ^ 978218 = (2 : ZMod 256434190891) ^ (489109 + 489109) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 489109 * (2 : ZMod 256434190891) ^ 489109 := by rw [pow_add]
          _ = 213464917438 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 256434190891) ^ 1956437 = 120504441926 := by
        calc
          (2 : ZMod 256434190891) ^ 1956437 = (2 : ZMod 256434190891) ^ (978218 + 978218 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 978218 * (2 : ZMod 256434190891) ^ 978218) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 120504441926 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 256434190891) ^ 3912875 = 232758363453 := by
        calc
          (2 : ZMod 256434190891) ^ 3912875 = (2 : ZMod 256434190891) ^ (1956437 + 1956437 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 1956437 * (2 : ZMod 256434190891) ^ 1956437) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 232758363453 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 256434190891) ^ 7825750 = 99736254599 := by
        calc
          (2 : ZMod 256434190891) ^ 7825750 = (2 : ZMod 256434190891) ^ (3912875 + 3912875) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 3912875 * (2 : ZMod 256434190891) ^ 3912875 := by rw [pow_add]
          _ = 99736254599 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 256434190891) ^ 15651500 = 181556929223 := by
        calc
          (2 : ZMod 256434190891) ^ 15651500 = (2 : ZMod 256434190891) ^ (7825750 + 7825750) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 7825750 * (2 : ZMod 256434190891) ^ 7825750 := by rw [pow_add]
          _ = 181556929223 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 256434190891) ^ 31303001 = 8245444126 := by
        calc
          (2 : ZMod 256434190891) ^ 31303001 = (2 : ZMod 256434190891) ^ (15651500 + 15651500 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 15651500 * (2 : ZMod 256434190891) ^ 15651500) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 8245444126 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 256434190891) ^ 62606003 = 214058872568 := by
        calc
          (2 : ZMod 256434190891) ^ 62606003 = (2 : ZMod 256434190891) ^ (31303001 + 31303001 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 31303001 * (2 : ZMod 256434190891) ^ 31303001) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 214058872568 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 256434190891) ^ 125212007 = 43806774165 := by
        calc
          (2 : ZMod 256434190891) ^ 125212007 = (2 : ZMod 256434190891) ^ (62606003 + 62606003 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 62606003 * (2 : ZMod 256434190891) ^ 62606003) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 43806774165 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 256434190891) ^ 250424014 = 86640452647 := by
        calc
          (2 : ZMod 256434190891) ^ 250424014 = (2 : ZMod 256434190891) ^ (125212007 + 125212007) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 125212007 * (2 : ZMod 256434190891) ^ 125212007 := by rw [pow_add]
          _ = 86640452647 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 256434190891) ^ 500848029 = 71697211750 := by
        calc
          (2 : ZMod 256434190891) ^ 500848029 = (2 : ZMod 256434190891) ^ (250424014 + 250424014 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 250424014 * (2 : ZMod 256434190891) ^ 250424014) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 71697211750 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 256434190891) ^ 1001696058 = 128699649474 := by
        calc
          (2 : ZMod 256434190891) ^ 1001696058 = (2 : ZMod 256434190891) ^ (500848029 + 500848029) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 500848029 * (2 : ZMod 256434190891) ^ 500848029 := by rw [pow_add]
          _ = 128699649474 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 256434190891) ^ 2003392116 = 53847072402 := by
        calc
          (2 : ZMod 256434190891) ^ 2003392116 = (2 : ZMod 256434190891) ^ (1001696058 + 1001696058) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 1001696058 * (2 : ZMod 256434190891) ^ 1001696058 := by rw [pow_add]
          _ = 53847072402 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 256434190891) ^ 4006784232 = 88664223108 := by
        calc
          (2 : ZMod 256434190891) ^ 4006784232 = (2 : ZMod 256434190891) ^ (2003392116 + 2003392116) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 2003392116 * (2 : ZMod 256434190891) ^ 2003392116 := by rw [pow_add]
          _ = 88664223108 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 256434190891) ^ 8013568465 = 44100764003 := by
        calc
          (2 : ZMod 256434190891) ^ 8013568465 = (2 : ZMod 256434190891) ^ (4006784232 + 4006784232 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 4006784232 * (2 : ZMod 256434190891) ^ 4006784232) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 44100764003 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 256434190891) ^ 16027136930 = 60145443659 := by
        calc
          (2 : ZMod 256434190891) ^ 16027136930 = (2 : ZMod 256434190891) ^ (8013568465 + 8013568465) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 8013568465 * (2 : ZMod 256434190891) ^ 8013568465 := by rw [pow_add]
          _ = 60145443659 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 256434190891) ^ 32054273861 = 3891359137 := by
        calc
          (2 : ZMod 256434190891) ^ 32054273861 = (2 : ZMod 256434190891) ^ (16027136930 + 16027136930 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 16027136930 * (2 : ZMod 256434190891) ^ 16027136930) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 3891359137 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 256434190891) ^ 64108547722 = 15807451485 := by
        calc
          (2 : ZMod 256434190891) ^ 64108547722 = (2 : ZMod 256434190891) ^ (32054273861 + 32054273861) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 32054273861 * (2 : ZMod 256434190891) ^ 32054273861 := by rw [pow_add]
          _ = 15807451485 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 256434190891) ^ 128217095445 = 256434190890 := by
        calc
          (2 : ZMod 256434190891) ^ 128217095445 = (2 : ZMod 256434190891) ^ (64108547722 + 64108547722 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 64108547722 * (2 : ZMod 256434190891) ^ 64108547722) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 256434190890 := by rw [factor_0_35]; decide
      change (2 : ZMod 256434190891) ^ 128217095445 ≠ 1
      rw [factor_0_36]
      decide
    ·
      have factor_1_0 : (2 : ZMod 256434190891) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 256434190891) ^ 2 = 4 := by
        calc
          (2 : ZMod 256434190891) ^ 2 = (2 : ZMod 256434190891) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 1 * (2 : ZMod 256434190891) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 256434190891) ^ 4 = 16 := by
        calc
          (2 : ZMod 256434190891) ^ 4 = (2 : ZMod 256434190891) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 2 * (2 : ZMod 256434190891) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 256434190891) ^ 9 = 512 := by
        calc
          (2 : ZMod 256434190891) ^ 9 = (2 : ZMod 256434190891) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 4 * (2 : ZMod 256434190891) ^ 4) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 256434190891) ^ 19 = 524288 := by
        calc
          (2 : ZMod 256434190891) ^ 19 = (2 : ZMod 256434190891) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 9 * (2 : ZMod 256434190891) ^ 9) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 256434190891) ^ 39 = 36887432106 := by
        calc
          (2 : ZMod 256434190891) ^ 39 = (2 : ZMod 256434190891) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 19 * (2 : ZMod 256434190891) ^ 19) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 36887432106 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 256434190891) ^ 79 = 198496815486 := by
        calc
          (2 : ZMod 256434190891) ^ 79 = (2 : ZMod 256434190891) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 39 * (2 : ZMod 256434190891) ^ 39) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 198496815486 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 256434190891) ^ 159 = 220406927424 := by
        calc
          (2 : ZMod 256434190891) ^ 159 = (2 : ZMod 256434190891) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 79 * (2 : ZMod 256434190891) ^ 79) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 220406927424 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 256434190891) ^ 318 = 77512016070 := by
        calc
          (2 : ZMod 256434190891) ^ 318 = (2 : ZMod 256434190891) ^ (159 + 159) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 159 * (2 : ZMod 256434190891) ^ 159 := by rw [pow_add]
          _ = 77512016070 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 256434190891) ^ 636 = 128487545003 := by
        calc
          (2 : ZMod 256434190891) ^ 636 = (2 : ZMod 256434190891) ^ (318 + 318) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 318 * (2 : ZMod 256434190891) ^ 318 := by rw [pow_add]
          _ = 128487545003 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 256434190891) ^ 1273 = 93116925416 := by
        calc
          (2 : ZMod 256434190891) ^ 1273 = (2 : ZMod 256434190891) ^ (636 + 636 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 636 * (2 : ZMod 256434190891) ^ 636) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 93116925416 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 256434190891) ^ 2547 = 196194735280 := by
        calc
          (2 : ZMod 256434190891) ^ 2547 = (2 : ZMod 256434190891) ^ (1273 + 1273 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 1273 * (2 : ZMod 256434190891) ^ 1273) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 196194735280 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 256434190891) ^ 5094 = 86297685018 := by
        calc
          (2 : ZMod 256434190891) ^ 5094 = (2 : ZMod 256434190891) ^ (2547 + 2547) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 2547 * (2 : ZMod 256434190891) ^ 2547 := by rw [pow_add]
          _ = 86297685018 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 256434190891) ^ 10189 = 73233810479 := by
        calc
          (2 : ZMod 256434190891) ^ 10189 = (2 : ZMod 256434190891) ^ (5094 + 5094 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 5094 * (2 : ZMod 256434190891) ^ 5094) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 73233810479 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 256434190891) ^ 20379 = 18436479748 := by
        calc
          (2 : ZMod 256434190891) ^ 20379 = (2 : ZMod 256434190891) ^ (10189 + 10189 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 10189 * (2 : ZMod 256434190891) ^ 10189) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 18436479748 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 256434190891) ^ 40759 = 126012142638 := by
        calc
          (2 : ZMod 256434190891) ^ 40759 = (2 : ZMod 256434190891) ^ (20379 + 20379 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 20379 * (2 : ZMod 256434190891) ^ 20379) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 126012142638 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 256434190891) ^ 81518 = 89103889223 := by
        calc
          (2 : ZMod 256434190891) ^ 81518 = (2 : ZMod 256434190891) ^ (40759 + 40759) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 40759 * (2 : ZMod 256434190891) ^ 40759 := by rw [pow_add]
          _ = 89103889223 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 256434190891) ^ 163036 = 219359508753 := by
        calc
          (2 : ZMod 256434190891) ^ 163036 = (2 : ZMod 256434190891) ^ (81518 + 81518) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 81518 * (2 : ZMod 256434190891) ^ 81518 := by rw [pow_add]
          _ = 219359508753 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 256434190891) ^ 326072 = 72116556510 := by
        calc
          (2 : ZMod 256434190891) ^ 326072 = (2 : ZMod 256434190891) ^ (163036 + 163036) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 163036 * (2 : ZMod 256434190891) ^ 163036 := by rw [pow_add]
          _ = 72116556510 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 256434190891) ^ 652145 = 5878110731 := by
        calc
          (2 : ZMod 256434190891) ^ 652145 = (2 : ZMod 256434190891) ^ (326072 + 326072 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 326072 * (2 : ZMod 256434190891) ^ 326072) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 5878110731 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 256434190891) ^ 1304291 = 84130481168 := by
        calc
          (2 : ZMod 256434190891) ^ 1304291 = (2 : ZMod 256434190891) ^ (652145 + 652145 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 652145 * (2 : ZMod 256434190891) ^ 652145) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 84130481168 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 256434190891) ^ 2608583 = 73881018171 := by
        calc
          (2 : ZMod 256434190891) ^ 2608583 = (2 : ZMod 256434190891) ^ (1304291 + 1304291 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 1304291 * (2 : ZMod 256434190891) ^ 1304291) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 73881018171 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 256434190891) ^ 5217166 = 66721803933 := by
        calc
          (2 : ZMod 256434190891) ^ 5217166 = (2 : ZMod 256434190891) ^ (2608583 + 2608583) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 2608583 * (2 : ZMod 256434190891) ^ 2608583 := by rw [pow_add]
          _ = 66721803933 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 256434190891) ^ 10434333 = 119027758456 := by
        calc
          (2 : ZMod 256434190891) ^ 10434333 = (2 : ZMod 256434190891) ^ (5217166 + 5217166 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 5217166 * (2 : ZMod 256434190891) ^ 5217166) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 119027758456 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 256434190891) ^ 20868667 = 82518951661 := by
        calc
          (2 : ZMod 256434190891) ^ 20868667 = (2 : ZMod 256434190891) ^ (10434333 + 10434333 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 10434333 * (2 : ZMod 256434190891) ^ 10434333) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 82518951661 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 256434190891) ^ 41737335 = 113009114239 := by
        calc
          (2 : ZMod 256434190891) ^ 41737335 = (2 : ZMod 256434190891) ^ (20868667 + 20868667 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 20868667 * (2 : ZMod 256434190891) ^ 20868667) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 113009114239 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 256434190891) ^ 83474671 = 220606876528 := by
        calc
          (2 : ZMod 256434190891) ^ 83474671 = (2 : ZMod 256434190891) ^ (41737335 + 41737335 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 41737335 * (2 : ZMod 256434190891) ^ 41737335) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 220606876528 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 256434190891) ^ 166949343 = 74044396496 := by
        calc
          (2 : ZMod 256434190891) ^ 166949343 = (2 : ZMod 256434190891) ^ (83474671 + 83474671 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 83474671 * (2 : ZMod 256434190891) ^ 83474671) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 74044396496 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 256434190891) ^ 333898686 = 50068704340 := by
        calc
          (2 : ZMod 256434190891) ^ 333898686 = (2 : ZMod 256434190891) ^ (166949343 + 166949343) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 166949343 * (2 : ZMod 256434190891) ^ 166949343 := by rw [pow_add]
          _ = 50068704340 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 256434190891) ^ 667797372 = 105348173275 := by
        calc
          (2 : ZMod 256434190891) ^ 667797372 = (2 : ZMod 256434190891) ^ (333898686 + 333898686) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 333898686 * (2 : ZMod 256434190891) ^ 333898686 := by rw [pow_add]
          _ = 105348173275 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 256434190891) ^ 1335594744 = 165645305441 := by
        calc
          (2 : ZMod 256434190891) ^ 1335594744 = (2 : ZMod 256434190891) ^ (667797372 + 667797372) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 667797372 * (2 : ZMod 256434190891) ^ 667797372 := by rw [pow_add]
          _ = 165645305441 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 256434190891) ^ 2671189488 = 126108033380 := by
        calc
          (2 : ZMod 256434190891) ^ 2671189488 = (2 : ZMod 256434190891) ^ (1335594744 + 1335594744) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 1335594744 * (2 : ZMod 256434190891) ^ 1335594744 := by rw [pow_add]
          _ = 126108033380 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 256434190891) ^ 5342378976 = 253560235946 := by
        calc
          (2 : ZMod 256434190891) ^ 5342378976 = (2 : ZMod 256434190891) ^ (2671189488 + 2671189488) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 2671189488 * (2 : ZMod 256434190891) ^ 2671189488 := by rw [pow_add]
          _ = 253560235946 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 256434190891) ^ 10684757953 = 165206767941 := by
        calc
          (2 : ZMod 256434190891) ^ 10684757953 = (2 : ZMod 256434190891) ^ (5342378976 + 5342378976 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 5342378976 * (2 : ZMod 256434190891) ^ 5342378976) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 165206767941 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 256434190891) ^ 21369515907 = 48905308241 := by
        calc
          (2 : ZMod 256434190891) ^ 21369515907 = (2 : ZMod 256434190891) ^ (10684757953 + 10684757953 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 10684757953 * (2 : ZMod 256434190891) ^ 10684757953) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 48905308241 := by rw [factor_1_33]; decide
      have factor_1_35 : (2 : ZMod 256434190891) ^ 42739031815 = 49197584568 := by
        calc
          (2 : ZMod 256434190891) ^ 42739031815 = (2 : ZMod 256434190891) ^ (21369515907 + 21369515907 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 21369515907 * (2 : ZMod 256434190891) ^ 21369515907) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 49197584568 := by rw [factor_1_34]; decide
      have factor_1_36 : (2 : ZMod 256434190891) ^ 85478063630 = 49197584567 := by
        calc
          (2 : ZMod 256434190891) ^ 85478063630 = (2 : ZMod 256434190891) ^ (42739031815 + 42739031815) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 42739031815 * (2 : ZMod 256434190891) ^ 42739031815 := by rw [pow_add]
          _ = 49197584567 := by rw [factor_1_35]; decide
      change (2 : ZMod 256434190891) ^ 85478063630 ≠ 1
      rw [factor_1_36]
      decide
    ·
      have factor_2_0 : (2 : ZMod 256434190891) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 256434190891) ^ 2 = 4 := by
        calc
          (2 : ZMod 256434190891) ^ 2 = (2 : ZMod 256434190891) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 1 * (2 : ZMod 256434190891) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 256434190891) ^ 5 = 32 := by
        calc
          (2 : ZMod 256434190891) ^ 5 = (2 : ZMod 256434190891) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 2 * (2 : ZMod 256434190891) ^ 2) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 256434190891) ^ 11 = 2048 := by
        calc
          (2 : ZMod 256434190891) ^ 11 = (2 : ZMod 256434190891) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 5 * (2 : ZMod 256434190891) ^ 5) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 256434190891) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 256434190891) ^ 23 = (2 : ZMod 256434190891) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 11 * (2 : ZMod 256434190891) ^ 11) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 256434190891) ^ 47 = 211551747060 := by
        calc
          (2 : ZMod 256434190891) ^ 47 = (2 : ZMod 256434190891) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 23 * (2 : ZMod 256434190891) ^ 23) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 211551747060 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 256434190891) ^ 95 = 37229980957 := by
        calc
          (2 : ZMod 256434190891) ^ 95 = (2 : ZMod 256434190891) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 47 * (2 : ZMod 256434190891) ^ 47) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 37229980957 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 256434190891) ^ 191 = 193652912255 := by
        calc
          (2 : ZMod 256434190891) ^ 191 = (2 : ZMod 256434190891) ^ (95 + 95 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 95 * (2 : ZMod 256434190891) ^ 95) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 193652912255 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 256434190891) ^ 382 = 166523171282 := by
        calc
          (2 : ZMod 256434190891) ^ 382 = (2 : ZMod 256434190891) ^ (191 + 191) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 191 * (2 : ZMod 256434190891) ^ 191 := by rw [pow_add]
          _ = 166523171282 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 256434190891) ^ 764 = 85587674227 := by
        calc
          (2 : ZMod 256434190891) ^ 764 = (2 : ZMod 256434190891) ^ (382 + 382) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 382 * (2 : ZMod 256434190891) ^ 382 := by rw [pow_add]
          _ = 85587674227 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 256434190891) ^ 1528 = 256131500560 := by
        calc
          (2 : ZMod 256434190891) ^ 1528 = (2 : ZMod 256434190891) ^ (764 + 764) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 764 * (2 : ZMod 256434190891) ^ 764 := by rw [pow_add]
          _ = 256131500560 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 256434190891) ^ 3056 = 64417444171 := by
        calc
          (2 : ZMod 256434190891) ^ 3056 = (2 : ZMod 256434190891) ^ (1528 + 1528) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 1528 * (2 : ZMod 256434190891) ^ 1528 := by rw [pow_add]
          _ = 64417444171 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 256434190891) ^ 6113 = 226274462110 := by
        calc
          (2 : ZMod 256434190891) ^ 6113 = (2 : ZMod 256434190891) ^ (3056 + 3056 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 3056 * (2 : ZMod 256434190891) ^ 3056) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 226274462110 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 256434190891) ^ 12227 = 91633826662 := by
        calc
          (2 : ZMod 256434190891) ^ 12227 = (2 : ZMod 256434190891) ^ (6113 + 6113 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 6113 * (2 : ZMod 256434190891) ^ 6113) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 91633826662 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 256434190891) ^ 24455 = 247967067536 := by
        calc
          (2 : ZMod 256434190891) ^ 24455 = (2 : ZMod 256434190891) ^ (12227 + 12227 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 12227 * (2 : ZMod 256434190891) ^ 12227) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 247967067536 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 256434190891) ^ 48910 = 54443129298 := by
        calc
          (2 : ZMod 256434190891) ^ 48910 = (2 : ZMod 256434190891) ^ (24455 + 24455) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 24455 * (2 : ZMod 256434190891) ^ 24455 := by rw [pow_add]
          _ = 54443129298 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 256434190891) ^ 97821 = 206602937220 := by
        calc
          (2 : ZMod 256434190891) ^ 97821 = (2 : ZMod 256434190891) ^ (48910 + 48910 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 48910 * (2 : ZMod 256434190891) ^ 48910) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 206602937220 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 256434190891) ^ 195643 = 219616583865 := by
        calc
          (2 : ZMod 256434190891) ^ 195643 = (2 : ZMod 256434190891) ^ (97821 + 97821 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 97821 * (2 : ZMod 256434190891) ^ 97821) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 219616583865 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 256434190891) ^ 391287 = 132074455279 := by
        calc
          (2 : ZMod 256434190891) ^ 391287 = (2 : ZMod 256434190891) ^ (195643 + 195643 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 195643 * (2 : ZMod 256434190891) ^ 195643) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 132074455279 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 256434190891) ^ 782575 = 63116225188 := by
        calc
          (2 : ZMod 256434190891) ^ 782575 = (2 : ZMod 256434190891) ^ (391287 + 391287 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 391287 * (2 : ZMod 256434190891) ^ 391287) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 63116225188 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 256434190891) ^ 1565150 = 133731391194 := by
        calc
          (2 : ZMod 256434190891) ^ 1565150 = (2 : ZMod 256434190891) ^ (782575 + 782575) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 782575 * (2 : ZMod 256434190891) ^ 782575 := by rw [pow_add]
          _ = 133731391194 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 256434190891) ^ 3130300 = 75613670719 := by
        calc
          (2 : ZMod 256434190891) ^ 3130300 = (2 : ZMod 256434190891) ^ (1565150 + 1565150) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 1565150 * (2 : ZMod 256434190891) ^ 1565150 := by rw [pow_add]
          _ = 75613670719 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 256434190891) ^ 6260600 = 199677348881 := by
        calc
          (2 : ZMod 256434190891) ^ 6260600 = (2 : ZMod 256434190891) ^ (3130300 + 3130300) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 3130300 * (2 : ZMod 256434190891) ^ 3130300 := by rw [pow_add]
          _ = 199677348881 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 256434190891) ^ 12521200 = 87523834650 := by
        calc
          (2 : ZMod 256434190891) ^ 12521200 = (2 : ZMod 256434190891) ^ (6260600 + 6260600) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 6260600 * (2 : ZMod 256434190891) ^ 6260600 := by rw [pow_add]
          _ = 87523834650 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 256434190891) ^ 25042401 = 66946794764 := by
        calc
          (2 : ZMod 256434190891) ^ 25042401 = (2 : ZMod 256434190891) ^ (12521200 + 12521200 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 12521200 * (2 : ZMod 256434190891) ^ 12521200) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 66946794764 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 256434190891) ^ 50084802 = 108441391447 := by
        calc
          (2 : ZMod 256434190891) ^ 50084802 = (2 : ZMod 256434190891) ^ (25042401 + 25042401) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 25042401 * (2 : ZMod 256434190891) ^ 25042401 := by rw [pow_add]
          _ = 108441391447 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 256434190891) ^ 100169605 = 84074238837 := by
        calc
          (2 : ZMod 256434190891) ^ 100169605 = (2 : ZMod 256434190891) ^ (50084802 + 50084802 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 50084802 * (2 : ZMod 256434190891) ^ 50084802) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 84074238837 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 256434190891) ^ 200339211 = 80248173813 := by
        calc
          (2 : ZMod 256434190891) ^ 200339211 = (2 : ZMod 256434190891) ^ (100169605 + 100169605 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 100169605 * (2 : ZMod 256434190891) ^ 100169605) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 80248173813 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 256434190891) ^ 400678423 = 93674672170 := by
        calc
          (2 : ZMod 256434190891) ^ 400678423 = (2 : ZMod 256434190891) ^ (200339211 + 200339211 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 200339211 * (2 : ZMod 256434190891) ^ 200339211) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 93674672170 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 256434190891) ^ 801356846 = 48405096169 := by
        calc
          (2 : ZMod 256434190891) ^ 801356846 = (2 : ZMod 256434190891) ^ (400678423 + 400678423) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 400678423 * (2 : ZMod 256434190891) ^ 400678423 := by rw [pow_add]
          _ = 48405096169 := by rw [factor_2_28]; decide
      have factor_2_30 : (2 : ZMod 256434190891) ^ 1602713693 = 203017801756 := by
        calc
          (2 : ZMod 256434190891) ^ 1602713693 = (2 : ZMod 256434190891) ^ (801356846 + 801356846 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 801356846 * (2 : ZMod 256434190891) ^ 801356846) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 203017801756 := by rw [factor_2_29]; decide
      have factor_2_31 : (2 : ZMod 256434190891) ^ 3205427386 = 247289138278 := by
        calc
          (2 : ZMod 256434190891) ^ 3205427386 = (2 : ZMod 256434190891) ^ (1602713693 + 1602713693) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 1602713693 * (2 : ZMod 256434190891) ^ 1602713693 := by rw [pow_add]
          _ = 247289138278 := by rw [factor_2_30]; decide
      have factor_2_32 : (2 : ZMod 256434190891) ^ 6410854772 = 157196130232 := by
        calc
          (2 : ZMod 256434190891) ^ 6410854772 = (2 : ZMod 256434190891) ^ (3205427386 + 3205427386) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 3205427386 * (2 : ZMod 256434190891) ^ 3205427386 := by rw [pow_add]
          _ = 157196130232 := by rw [factor_2_31]; decide
      have factor_2_33 : (2 : ZMod 256434190891) ^ 12821709544 = 170427337842 := by
        calc
          (2 : ZMod 256434190891) ^ 12821709544 = (2 : ZMod 256434190891) ^ (6410854772 + 6410854772) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 6410854772 * (2 : ZMod 256434190891) ^ 6410854772 := by rw [pow_add]
          _ = 170427337842 := by rw [factor_2_32]; decide
      have factor_2_34 : (2 : ZMod 256434190891) ^ 25643419089 = 142291757972 := by
        calc
          (2 : ZMod 256434190891) ^ 25643419089 = (2 : ZMod 256434190891) ^ (12821709544 + 12821709544 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 12821709544 * (2 : ZMod 256434190891) ^ 12821709544) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 142291757972 := by rw [factor_2_33]; decide
      have factor_2_35 : (2 : ZMod 256434190891) ^ 51286838178 = 205057924836 := by
        calc
          (2 : ZMod 256434190891) ^ 51286838178 = (2 : ZMod 256434190891) ^ (25643419089 + 25643419089) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 25643419089 * (2 : ZMod 256434190891) ^ 25643419089 := by rw [pow_add]
          _ = 205057924836 := by rw [factor_2_34]; decide
      change (2 : ZMod 256434190891) ^ 51286838178 ≠ 1
      rw [factor_2_35]
      decide
    ·
      have factor_3_0 : (2 : ZMod 256434190891) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 256434190891) ^ 3 = 8 := by
        calc
          (2 : ZMod 256434190891) ^ 3 = (2 : ZMod 256434190891) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 1 * (2 : ZMod 256434190891) ^ 1) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 256434190891) ^ 7 = 128 := by
        calc
          (2 : ZMod 256434190891) ^ 7 = (2 : ZMod 256434190891) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 3 * (2 : ZMod 256434190891) ^ 3) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 256434190891) ^ 14 = 16384 := by
        calc
          (2 : ZMod 256434190891) ^ 14 = (2 : ZMod 256434190891) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 7 * (2 : ZMod 256434190891) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 256434190891) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 256434190891) ^ 28 = (2 : ZMod 256434190891) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 14 * (2 : ZMod 256434190891) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 256434190891) ^ 56 = 99265938718 := by
        calc
          (2 : ZMod 256434190891) ^ 56 = (2 : ZMod 256434190891) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 28 * (2 : ZMod 256434190891) ^ 28 := by rw [pow_add]
          _ = 99265938718 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 256434190891) ^ 112 = 121845531065 := by
        calc
          (2 : ZMod 256434190891) ^ 112 = (2 : ZMod 256434190891) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 56 * (2 : ZMod 256434190891) ^ 56 := by rw [pow_add]
          _ = 121845531065 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 256434190891) ^ 224 = 249317020224 := by
        calc
          (2 : ZMod 256434190891) ^ 224 = (2 : ZMod 256434190891) ^ (112 + 112) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 112 * (2 : ZMod 256434190891) ^ 112 := by rw [pow_add]
          _ = 249317020224 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 256434190891) ^ 449 = 155680766483 := by
        calc
          (2 : ZMod 256434190891) ^ 449 = (2 : ZMod 256434190891) ^ (224 + 224 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 224 * (2 : ZMod 256434190891) ^ 224) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 155680766483 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 256434190891) ^ 899 = 86272719689 := by
        calc
          (2 : ZMod 256434190891) ^ 899 = (2 : ZMod 256434190891) ^ (449 + 449 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 449 * (2 : ZMod 256434190891) ^ 449) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 86272719689 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 256434190891) ^ 1798 = 223773311474 := by
        calc
          (2 : ZMod 256434190891) ^ 1798 = (2 : ZMod 256434190891) ^ (899 + 899) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 899 * (2 : ZMod 256434190891) ^ 899 := by rw [pow_add]
          _ = 223773311474 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 256434190891) ^ 3596 = 206147091128 := by
        calc
          (2 : ZMod 256434190891) ^ 3596 = (2 : ZMod 256434190891) ^ (1798 + 1798) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 1798 * (2 : ZMod 256434190891) ^ 1798 := by rw [pow_add]
          _ = 206147091128 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 256434190891) ^ 7192 = 165749756454 := by
        calc
          (2 : ZMod 256434190891) ^ 7192 = (2 : ZMod 256434190891) ^ (3596 + 3596) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 3596 * (2 : ZMod 256434190891) ^ 3596 := by rw [pow_add]
          _ = 165749756454 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 256434190891) ^ 14385 = 76100119640 := by
        calc
          (2 : ZMod 256434190891) ^ 14385 = (2 : ZMod 256434190891) ^ (7192 + 7192 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 7192 * (2 : ZMod 256434190891) ^ 7192) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 76100119640 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 256434190891) ^ 28771 = 17291697172 := by
        calc
          (2 : ZMod 256434190891) ^ 28771 = (2 : ZMod 256434190891) ^ (14385 + 14385 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 14385 * (2 : ZMod 256434190891) ^ 14385) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 17291697172 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 256434190891) ^ 57542 = 101326425489 := by
        calc
          (2 : ZMod 256434190891) ^ 57542 = (2 : ZMod 256434190891) ^ (28771 + 28771) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 28771 * (2 : ZMod 256434190891) ^ 28771 := by rw [pow_add]
          _ = 101326425489 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 256434190891) ^ 115084 = 206819054134 := by
        calc
          (2 : ZMod 256434190891) ^ 115084 = (2 : ZMod 256434190891) ^ (57542 + 57542) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 57542 * (2 : ZMod 256434190891) ^ 57542 := by rw [pow_add]
          _ = 206819054134 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 256434190891) ^ 230169 = 208611872601 := by
        calc
          (2 : ZMod 256434190891) ^ 230169 = (2 : ZMod 256434190891) ^ (115084 + 115084 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 115084 * (2 : ZMod 256434190891) ^ 115084) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 208611872601 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 256434190891) ^ 460338 = 156105401917 := by
        calc
          (2 : ZMod 256434190891) ^ 460338 = (2 : ZMod 256434190891) ^ (230169 + 230169) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 230169 * (2 : ZMod 256434190891) ^ 230169 := by rw [pow_add]
          _ = 156105401917 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 256434190891) ^ 920676 = 182037124719 := by
        calc
          (2 : ZMod 256434190891) ^ 920676 = (2 : ZMod 256434190891) ^ (460338 + 460338) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 460338 * (2 : ZMod 256434190891) ^ 460338 := by rw [pow_add]
          _ = 182037124719 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 256434190891) ^ 1841353 = 220077140839 := by
        calc
          (2 : ZMod 256434190891) ^ 1841353 = (2 : ZMod 256434190891) ^ (920676 + 920676 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 920676 * (2 : ZMod 256434190891) ^ 920676) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 220077140839 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 256434190891) ^ 3682706 = 151581208260 := by
        calc
          (2 : ZMod 256434190891) ^ 3682706 = (2 : ZMod 256434190891) ^ (1841353 + 1841353) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 1841353 * (2 : ZMod 256434190891) ^ 1841353 := by rw [pow_add]
          _ = 151581208260 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 256434190891) ^ 7365412 = 202290622516 := by
        calc
          (2 : ZMod 256434190891) ^ 7365412 = (2 : ZMod 256434190891) ^ (3682706 + 3682706) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 3682706 * (2 : ZMod 256434190891) ^ 3682706 := by rw [pow_add]
          _ = 202290622516 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 256434190891) ^ 14730824 = 164089665363 := by
        calc
          (2 : ZMod 256434190891) ^ 14730824 = (2 : ZMod 256434190891) ^ (7365412 + 7365412) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 7365412 * (2 : ZMod 256434190891) ^ 7365412 := by rw [pow_add]
          _ = 164089665363 := by rw [factor_3_22]; decide
      have factor_3_24 : (2 : ZMod 256434190891) ^ 29461648 = 136064531389 := by
        calc
          (2 : ZMod 256434190891) ^ 29461648 = (2 : ZMod 256434190891) ^ (14730824 + 14730824) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 14730824 * (2 : ZMod 256434190891) ^ 14730824 := by rw [pow_add]
          _ = 136064531389 := by rw [factor_3_23]; decide
      have factor_3_25 : (2 : ZMod 256434190891) ^ 58923297 = 96350624746 := by
        calc
          (2 : ZMod 256434190891) ^ 58923297 = (2 : ZMod 256434190891) ^ (29461648 + 29461648 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 29461648 * (2 : ZMod 256434190891) ^ 29461648) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 96350624746 := by rw [factor_3_24]; decide
      have factor_3_26 : (2 : ZMod 256434190891) ^ 117846595 = 113949493231 := by
        calc
          (2 : ZMod 256434190891) ^ 117846595 = (2 : ZMod 256434190891) ^ (58923297 + 58923297 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 58923297 * (2 : ZMod 256434190891) ^ 58923297) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 113949493231 := by rw [factor_3_25]; decide
      have factor_3_27 : (2 : ZMod 256434190891) ^ 235693190 = 93088137338 := by
        calc
          (2 : ZMod 256434190891) ^ 235693190 = (2 : ZMod 256434190891) ^ (117846595 + 117846595) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 117846595 * (2 : ZMod 256434190891) ^ 117846595 := by rw [pow_add]
          _ = 93088137338 := by rw [factor_3_26]; decide
      have factor_3_28 : (2 : ZMod 256434190891) ^ 471386380 = 193611094932 := by
        calc
          (2 : ZMod 256434190891) ^ 471386380 = (2 : ZMod 256434190891) ^ (235693190 + 235693190) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 235693190 * (2 : ZMod 256434190891) ^ 235693190 := by rw [pow_add]
          _ = 193611094932 := by rw [factor_3_27]; decide
      have factor_3_29 : (2 : ZMod 256434190891) ^ 942772760 = 167265474758 := by
        calc
          (2 : ZMod 256434190891) ^ 942772760 = (2 : ZMod 256434190891) ^ (471386380 + 471386380) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 471386380 * (2 : ZMod 256434190891) ^ 471386380 := by rw [pow_add]
          _ = 167265474758 := by rw [factor_3_28]; decide
      have factor_3_30 : (2 : ZMod 256434190891) ^ 1885545521 = 207887212634 := by
        calc
          (2 : ZMod 256434190891) ^ 1885545521 = (2 : ZMod 256434190891) ^ (942772760 + 942772760 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 942772760 * (2 : ZMod 256434190891) ^ 942772760) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 207887212634 := by rw [factor_3_29]; decide
      have factor_3_31 : (2 : ZMod 256434190891) ^ 3771091042 = 234459014269 := by
        calc
          (2 : ZMod 256434190891) ^ 3771091042 = (2 : ZMod 256434190891) ^ (1885545521 + 1885545521) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 1885545521 * (2 : ZMod 256434190891) ^ 1885545521 := by rw [pow_add]
          _ = 234459014269 := by rw [factor_3_30]; decide
      have factor_3_32 : (2 : ZMod 256434190891) ^ 7542182085 = 147450556072 := by
        calc
          (2 : ZMod 256434190891) ^ 7542182085 = (2 : ZMod 256434190891) ^ (3771091042 + 3771091042 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 3771091042 * (2 : ZMod 256434190891) ^ 3771091042) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 147450556072 := by rw [factor_3_31]; decide
      have factor_3_33 : (2 : ZMod 256434190891) ^ 15084364170 = 152829545482 := by
        calc
          (2 : ZMod 256434190891) ^ 15084364170 = (2 : ZMod 256434190891) ^ (7542182085 + 7542182085) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 7542182085 * (2 : ZMod 256434190891) ^ 7542182085 := by rw [pow_add]
          _ = 152829545482 := by rw [factor_3_32]; decide
      change (2 : ZMod 256434190891) ^ 15084364170 ≠ 1
      rw [factor_3_33]
      decide
    ·
      have factor_4_0 : (2 : ZMod 256434190891) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 256434190891) ^ 2 = 4 := by
        calc
          (2 : ZMod 256434190891) ^ 2 = (2 : ZMod 256434190891) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 1 * (2 : ZMod 256434190891) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 256434190891) ^ 4 = 16 := by
        calc
          (2 : ZMod 256434190891) ^ 4 = (2 : ZMod 256434190891) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 2 * (2 : ZMod 256434190891) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 256434190891) ^ 9 = 512 := by
        calc
          (2 : ZMod 256434190891) ^ 9 = (2 : ZMod 256434190891) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 4 * (2 : ZMod 256434190891) ^ 4) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 256434190891) ^ 18 = 262144 := by
        calc
          (2 : ZMod 256434190891) ^ 18 = (2 : ZMod 256434190891) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 9 * (2 : ZMod 256434190891) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 256434190891) ^ 36 = 68719476736 := by
        calc
          (2 : ZMod 256434190891) ^ 36 = (2 : ZMod 256434190891) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 18 * (2 : ZMod 256434190891) ^ 18 := by rw [pow_add]
          _ = 68719476736 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 256434190891) ^ 72 = 13571109069 := by
        calc
          (2 : ZMod 256434190891) ^ 72 = (2 : ZMod 256434190891) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 36 * (2 : ZMod 256434190891) ^ 36 := by rw [pow_add]
          _ = 13571109069 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 256434190891) ^ 145 = 189334007565 := by
        calc
          (2 : ZMod 256434190891) ^ 145 = (2 : ZMod 256434190891) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 72 * (2 : ZMod 256434190891) ^ 72) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 189334007565 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 256434190891) ^ 291 = 226869816912 := by
        calc
          (2 : ZMod 256434190891) ^ 291 = (2 : ZMod 256434190891) ^ (145 + 145 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 145 * (2 : ZMod 256434190891) ^ 145) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 226869816912 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 256434190891) ^ 583 = 214918322091 := by
        calc
          (2 : ZMod 256434190891) ^ 583 = (2 : ZMod 256434190891) ^ (291 + 291 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 291 * (2 : ZMod 256434190891) ^ 291) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 214918322091 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 256434190891) ^ 1167 = 156285794215 := by
        calc
          (2 : ZMod 256434190891) ^ 1167 = (2 : ZMod 256434190891) ^ (583 + 583 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 583 * (2 : ZMod 256434190891) ^ 583) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 156285794215 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 256434190891) ^ 2334 = 26368411941 := by
        calc
          (2 : ZMod 256434190891) ^ 2334 = (2 : ZMod 256434190891) ^ (1167 + 1167) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 1167 * (2 : ZMod 256434190891) ^ 1167 := by rw [pow_add]
          _ = 26368411941 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 256434190891) ^ 4669 = 19995165292 := by
        calc
          (2 : ZMod 256434190891) ^ 4669 = (2 : ZMod 256434190891) ^ (2334 + 2334 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 2334 * (2 : ZMod 256434190891) ^ 2334) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 19995165292 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 256434190891) ^ 9339 = 158631739302 := by
        calc
          (2 : ZMod 256434190891) ^ 9339 = (2 : ZMod 256434190891) ^ (4669 + 4669 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 4669 * (2 : ZMod 256434190891) ^ 4669) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 158631739302 := by rw [factor_4_12]; decide
      have factor_4_14 : (2 : ZMod 256434190891) ^ 18679 = 82678150019 := by
        calc
          (2 : ZMod 256434190891) ^ 18679 = (2 : ZMod 256434190891) ^ (9339 + 9339 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 9339 * (2 : ZMod 256434190891) ^ 9339) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 82678150019 := by rw [factor_4_13]; decide
      have factor_4_15 : (2 : ZMod 256434190891) ^ 37359 = 101549430238 := by
        calc
          (2 : ZMod 256434190891) ^ 37359 = (2 : ZMod 256434190891) ^ (18679 + 18679 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 18679 * (2 : ZMod 256434190891) ^ 18679) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 101549430238 := by rw [factor_4_14]; decide
      have factor_4_16 : (2 : ZMod 256434190891) ^ 74719 = 204134377092 := by
        calc
          (2 : ZMod 256434190891) ^ 74719 = (2 : ZMod 256434190891) ^ (37359 + 37359 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 37359 * (2 : ZMod 256434190891) ^ 37359) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 204134377092 := by rw [factor_4_15]; decide
      have factor_4_17 : (2 : ZMod 256434190891) ^ 149439 = 212967745879 := by
        calc
          (2 : ZMod 256434190891) ^ 149439 = (2 : ZMod 256434190891) ^ (74719 + 74719 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 74719 * (2 : ZMod 256434190891) ^ 74719) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 212967745879 := by rw [factor_4_16]; decide
      have factor_4_18 : (2 : ZMod 256434190891) ^ 298879 = 19003848170 := by
        calc
          (2 : ZMod 256434190891) ^ 298879 = (2 : ZMod 256434190891) ^ (149439 + 149439 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 149439 * (2 : ZMod 256434190891) ^ 149439) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 19003848170 := by rw [factor_4_17]; decide
      have factor_4_19 : (2 : ZMod 256434190891) ^ 597759 = 201090496019 := by
        calc
          (2 : ZMod 256434190891) ^ 597759 = (2 : ZMod 256434190891) ^ (298879 + 298879 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 298879 * (2 : ZMod 256434190891) ^ 298879) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 201090496019 := by rw [factor_4_18]; decide
      have factor_4_20 : (2 : ZMod 256434190891) ^ 1195519 = 37647652921 := by
        calc
          (2 : ZMod 256434190891) ^ 1195519 = (2 : ZMod 256434190891) ^ (597759 + 597759 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 597759 * (2 : ZMod 256434190891) ^ 597759) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 37647652921 := by rw [factor_4_19]; decide
      have factor_4_21 : (2 : ZMod 256434190891) ^ 2391039 = 3159961377 := by
        calc
          (2 : ZMod 256434190891) ^ 2391039 = (2 : ZMod 256434190891) ^ (1195519 + 1195519 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 1195519 * (2 : ZMod 256434190891) ^ 1195519) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 3159961377 := by rw [factor_4_20]; decide
      have factor_4_22 : (2 : ZMod 256434190891) ^ 4782078 = 67176791706 := by
        calc
          (2 : ZMod 256434190891) ^ 4782078 = (2 : ZMod 256434190891) ^ (2391039 + 2391039) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 2391039 * (2 : ZMod 256434190891) ^ 2391039 := by rw [pow_add]
          _ = 67176791706 := by rw [factor_4_21]; decide
      have factor_4_23 : (2 : ZMod 256434190891) ^ 9564157 = 221631579587 := by
        calc
          (2 : ZMod 256434190891) ^ 9564157 = (2 : ZMod 256434190891) ^ (4782078 + 4782078 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 4782078 * (2 : ZMod 256434190891) ^ 4782078) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 221631579587 := by rw [factor_4_22]; decide
      have factor_4_24 : (2 : ZMod 256434190891) ^ 19128315 = 132465745297 := by
        calc
          (2 : ZMod 256434190891) ^ 19128315 = (2 : ZMod 256434190891) ^ (9564157 + 9564157 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 9564157 * (2 : ZMod 256434190891) ^ 9564157) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 132465745297 := by rw [factor_4_23]; decide
      have factor_4_25 : (2 : ZMod 256434190891) ^ 38256630 = 49292355536 := by
        calc
          (2 : ZMod 256434190891) ^ 38256630 = (2 : ZMod 256434190891) ^ (19128315 + 19128315) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 19128315 * (2 : ZMod 256434190891) ^ 19128315 := by rw [pow_add]
          _ = 49292355536 := by rw [factor_4_24]; decide
      change (2 : ZMod 256434190891) ^ 38256630 ≠ 1
      rw [factor_4_25]
      decide
    ·
      have factor_5_0 : (2 : ZMod 256434190891) ^ 1 = 2 := by norm_num
      have factor_5_1 : (2 : ZMod 256434190891) ^ 3 = 8 := by
        calc
          (2 : ZMod 256434190891) ^ 3 = (2 : ZMod 256434190891) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 1 * (2 : ZMod 256434190891) ^ 1) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_5_0]; decide
      have factor_5_2 : (2 : ZMod 256434190891) ^ 6 = 64 := by
        calc
          (2 : ZMod 256434190891) ^ 6 = (2 : ZMod 256434190891) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 3 * (2 : ZMod 256434190891) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_5_1]; decide
      have factor_5_3 : (2 : ZMod 256434190891) ^ 13 = 8192 := by
        calc
          (2 : ZMod 256434190891) ^ 13 = (2 : ZMod 256434190891) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 6 * (2 : ZMod 256434190891) ^ 6) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_5_2]; decide
      have factor_5_4 : (2 : ZMod 256434190891) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 256434190891) ^ 26 = (2 : ZMod 256434190891) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 13 * (2 : ZMod 256434190891) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [factor_5_3]; decide
      have factor_5_5 : (2 : ZMod 256434190891) ^ 52 = 102366942754 := by
        calc
          (2 : ZMod 256434190891) ^ 52 = (2 : ZMod 256434190891) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 26 * (2 : ZMod 256434190891) ^ 26 := by rw [pow_add]
          _ = 102366942754 := by rw [factor_5_4]; decide
      have factor_5_6 : (2 : ZMod 256434190891) ^ 104 = 85620124050 := by
        calc
          (2 : ZMod 256434190891) ^ 104 = (2 : ZMod 256434190891) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 52 * (2 : ZMod 256434190891) ^ 52 := by rw [pow_add]
          _ = 85620124050 := by rw [factor_5_5]; decide
      have factor_5_7 : (2 : ZMod 256434190891) ^ 208 = 105432314398 := by
        calc
          (2 : ZMod 256434190891) ^ 208 = (2 : ZMod 256434190891) ^ (104 + 104) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 104 * (2 : ZMod 256434190891) ^ 104 := by rw [pow_add]
          _ = 105432314398 := by rw [factor_5_6]; decide
      have factor_5_8 : (2 : ZMod 256434190891) ^ 417 = 199739262087 := by
        calc
          (2 : ZMod 256434190891) ^ 417 = (2 : ZMod 256434190891) ^ (208 + 208 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 208 * (2 : ZMod 256434190891) ^ 208) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 199739262087 := by rw [factor_5_7]; decide
      have factor_5_9 : (2 : ZMod 256434190891) ^ 834 = 15128670064 := by
        calc
          (2 : ZMod 256434190891) ^ 834 = (2 : ZMod 256434190891) ^ (417 + 417) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 417 * (2 : ZMod 256434190891) ^ 417 := by rw [pow_add]
          _ = 15128670064 := by rw [factor_5_8]; decide
      have factor_5_10 : (2 : ZMod 256434190891) ^ 1669 = 30323045437 := by
        calc
          (2 : ZMod 256434190891) ^ 1669 = (2 : ZMod 256434190891) ^ (834 + 834 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 834 * (2 : ZMod 256434190891) ^ 834) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 30323045437 := by rw [factor_5_9]; decide
      have factor_5_11 : (2 : ZMod 256434190891) ^ 3338 = 212884941012 := by
        calc
          (2 : ZMod 256434190891) ^ 3338 = (2 : ZMod 256434190891) ^ (1669 + 1669) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 1669 * (2 : ZMod 256434190891) ^ 1669 := by rw [pow_add]
          _ = 212884941012 := by rw [factor_5_10]; decide
      have factor_5_12 : (2 : ZMod 256434190891) ^ 6676 = 24724288515 := by
        calc
          (2 : ZMod 256434190891) ^ 6676 = (2 : ZMod 256434190891) ^ (3338 + 3338) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 3338 * (2 : ZMod 256434190891) ^ 3338 := by rw [pow_add]
          _ = 24724288515 := by rw [factor_5_11]; decide
      have factor_5_13 : (2 : ZMod 256434190891) ^ 13353 = 11378025339 := by
        calc
          (2 : ZMod 256434190891) ^ 13353 = (2 : ZMod 256434190891) ^ (6676 + 6676 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 6676 * (2 : ZMod 256434190891) ^ 6676) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 11378025339 := by rw [factor_5_12]; decide
      have factor_5_14 : (2 : ZMod 256434190891) ^ 26707 = 219543577029 := by
        calc
          (2 : ZMod 256434190891) ^ 26707 = (2 : ZMod 256434190891) ^ (13353 + 13353 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 13353 * (2 : ZMod 256434190891) ^ 13353) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 219543577029 := by rw [factor_5_13]; decide
      have factor_5_15 : (2 : ZMod 256434190891) ^ 53414 = 134820882786 := by
        calc
          (2 : ZMod 256434190891) ^ 53414 = (2 : ZMod 256434190891) ^ (26707 + 26707) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 26707 * (2 : ZMod 256434190891) ^ 26707 := by rw [pow_add]
          _ = 134820882786 := by rw [factor_5_14]; decide
      have factor_5_16 : (2 : ZMod 256434190891) ^ 106829 = 12590160898 := by
        calc
          (2 : ZMod 256434190891) ^ 106829 = (2 : ZMod 256434190891) ^ (53414 + 53414 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 53414 * (2 : ZMod 256434190891) ^ 53414) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 12590160898 := by rw [factor_5_15]; decide
      have factor_5_17 : (2 : ZMod 256434190891) ^ 213658 = 174764602614 := by
        calc
          (2 : ZMod 256434190891) ^ 213658 = (2 : ZMod 256434190891) ^ (106829 + 106829) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 106829 * (2 : ZMod 256434190891) ^ 106829 := by rw [pow_add]
          _ = 174764602614 := by rw [factor_5_16]; decide
      have factor_5_18 : (2 : ZMod 256434190891) ^ 427316 = 188532132082 := by
        calc
          (2 : ZMod 256434190891) ^ 427316 = (2 : ZMod 256434190891) ^ (213658 + 213658) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 213658 * (2 : ZMod 256434190891) ^ 213658 := by rw [pow_add]
          _ = 188532132082 := by rw [factor_5_17]; decide
      have factor_5_19 : (2 : ZMod 256434190891) ^ 854632 = 67089716893 := by
        calc
          (2 : ZMod 256434190891) ^ 854632 = (2 : ZMod 256434190891) ^ (427316 + 427316) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 427316 * (2 : ZMod 256434190891) ^ 427316 := by rw [pow_add]
          _ = 67089716893 := by rw [factor_5_18]; decide
      have factor_5_20 : (2 : ZMod 256434190891) ^ 1709265 = 128315369694 := by
        calc
          (2 : ZMod 256434190891) ^ 1709265 = (2 : ZMod 256434190891) ^ (854632 + 854632 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = ((2 : ZMod 256434190891) ^ 854632 * (2 : ZMod 256434190891) ^ 854632) * (2 : ZMod 256434190891) := by rw [pow_succ, pow_add]
          _ = 128315369694 := by rw [factor_5_19]; decide
      have factor_5_21 : (2 : ZMod 256434190891) ^ 3418530 = 67529450633 := by
        calc
          (2 : ZMod 256434190891) ^ 3418530 = (2 : ZMod 256434190891) ^ (1709265 + 1709265) :=
            congrArg (fun n : ℕ => (2 : ZMod 256434190891) ^ n) (by norm_num)
          _ = (2 : ZMod 256434190891) ^ 1709265 * (2 : ZMod 256434190891) ^ 1709265 := by rw [pow_add]
          _ = 67529450633 := by rw [factor_5_20]; decide
      change (2 : ZMod 256434190891) ^ 3418530 ≠ 1
      rw [factor_5_21]
      decide

#print axioms prime_lucas_256434190891

end TotientTailPeriodKiller
end Erdos249257
