import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_321535273 : Nat.Prime 321535273 := by
  apply lucas_primality 321535273 (13 : ZMod 321535273)
  ·
      have fermat_0 : (13 : ZMod 321535273) ^ 1 = 13 := by norm_num
      have fermat_1 : (13 : ZMod 321535273) ^ 2 = 169 := by
        calc
          (13 : ZMod 321535273) ^ 2 = (13 : ZMod 321535273) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 1 * (13 : ZMod 321535273) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [fermat_0]; decide
      have fermat_2 : (13 : ZMod 321535273) ^ 4 = 28561 := by
        calc
          (13 : ZMod 321535273) ^ 4 = (13 : ZMod 321535273) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 2 * (13 : ZMod 321535273) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [fermat_1]; decide
      have fermat_3 : (13 : ZMod 321535273) ^ 9 = 315370637 := by
        calc
          (13 : ZMod 321535273) ^ 9 = (13 : ZMod 321535273) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 4 * (13 : ZMod 321535273) ^ 4) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 315370637 := by rw [fermat_2]; decide
      have fermat_4 : (13 : ZMod 321535273) ^ 19 = 171085951 := by
        calc
          (13 : ZMod 321535273) ^ 19 = (13 : ZMod 321535273) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 9 * (13 : ZMod 321535273) ^ 9) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 171085951 := by rw [fermat_3]; decide
      have fermat_5 : (13 : ZMod 321535273) ^ 38 = 131070786 := by
        calc
          (13 : ZMod 321535273) ^ 38 = (13 : ZMod 321535273) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 19 * (13 : ZMod 321535273) ^ 19 := by rw [pow_add]
          _ = 131070786 := by rw [fermat_4]; decide
      have fermat_6 : (13 : ZMod 321535273) ^ 76 = 82409681 := by
        calc
          (13 : ZMod 321535273) ^ 76 = (13 : ZMod 321535273) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 38 * (13 : ZMod 321535273) ^ 38 := by rw [pow_add]
          _ = 82409681 := by rw [fermat_5]; decide
      have fermat_7 : (13 : ZMod 321535273) ^ 153 = 306297043 := by
        calc
          (13 : ZMod 321535273) ^ 153 = (13 : ZMod 321535273) ^ (76 + 76 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 76 * (13 : ZMod 321535273) ^ 76) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 306297043 := by rw [fermat_6]; decide
      have fermat_8 : (13 : ZMod 321535273) ^ 306 = 203895217 := by
        calc
          (13 : ZMod 321535273) ^ 306 = (13 : ZMod 321535273) ^ (153 + 153) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 153 * (13 : ZMod 321535273) ^ 153 := by rw [pow_add]
          _ = 203895217 := by rw [fermat_7]; decide
      have fermat_9 : (13 : ZMod 321535273) ^ 613 = 106498500 := by
        calc
          (13 : ZMod 321535273) ^ 613 = (13 : ZMod 321535273) ^ (306 + 306 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 306 * (13 : ZMod 321535273) ^ 306) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 106498500 := by rw [fermat_8]; decide
      have fermat_10 : (13 : ZMod 321535273) ^ 1226 = 108007192 := by
        calc
          (13 : ZMod 321535273) ^ 1226 = (13 : ZMod 321535273) ^ (613 + 613) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 613 * (13 : ZMod 321535273) ^ 613 := by rw [pow_add]
          _ = 108007192 := by rw [fermat_9]; decide
      have fermat_11 : (13 : ZMod 321535273) ^ 2453 = 55731706 := by
        calc
          (13 : ZMod 321535273) ^ 2453 = (13 : ZMod 321535273) ^ (1226 + 1226 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 1226 * (13 : ZMod 321535273) ^ 1226) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 55731706 := by rw [fermat_10]; decide
      have fermat_12 : (13 : ZMod 321535273) ^ 4906 = 33336988 := by
        calc
          (13 : ZMod 321535273) ^ 4906 = (13 : ZMod 321535273) ^ (2453 + 2453) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 2453 * (13 : ZMod 321535273) ^ 2453 := by rw [pow_add]
          _ = 33336988 := by rw [fermat_11]; decide
      have fermat_13 : (13 : ZMod 321535273) ^ 9812 = 251314944 := by
        calc
          (13 : ZMod 321535273) ^ 9812 = (13 : ZMod 321535273) ^ (4906 + 4906) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 4906 * (13 : ZMod 321535273) ^ 4906 := by rw [pow_add]
          _ = 251314944 := by rw [fermat_12]; decide
      have fermat_14 : (13 : ZMod 321535273) ^ 19624 = 71834931 := by
        calc
          (13 : ZMod 321535273) ^ 19624 = (13 : ZMod 321535273) ^ (9812 + 9812) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 9812 * (13 : ZMod 321535273) ^ 9812 := by rw [pow_add]
          _ = 71834931 := by rw [fermat_13]; decide
      have fermat_15 : (13 : ZMod 321535273) ^ 39249 = 247523580 := by
        calc
          (13 : ZMod 321535273) ^ 39249 = (13 : ZMod 321535273) ^ (19624 + 19624 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 19624 * (13 : ZMod 321535273) ^ 19624) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 247523580 := by rw [fermat_14]; decide
      have fermat_16 : (13 : ZMod 321535273) ^ 78499 = 206636622 := by
        calc
          (13 : ZMod 321535273) ^ 78499 = (13 : ZMod 321535273) ^ (39249 + 39249 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 39249 * (13 : ZMod 321535273) ^ 39249) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 206636622 := by rw [fermat_15]; decide
      have fermat_17 : (13 : ZMod 321535273) ^ 156999 = 214334258 := by
        calc
          (13 : ZMod 321535273) ^ 156999 = (13 : ZMod 321535273) ^ (78499 + 78499 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 78499 * (13 : ZMod 321535273) ^ 78499) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 214334258 := by rw [fermat_16]; decide
      have fermat_18 : (13 : ZMod 321535273) ^ 313999 = 60786840 := by
        calc
          (13 : ZMod 321535273) ^ 313999 = (13 : ZMod 321535273) ^ (156999 + 156999 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 156999 * (13 : ZMod 321535273) ^ 156999) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 60786840 := by rw [fermat_17]; decide
      have fermat_19 : (13 : ZMod 321535273) ^ 627998 = 288666728 := by
        calc
          (13 : ZMod 321535273) ^ 627998 = (13 : ZMod 321535273) ^ (313999 + 313999) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 313999 * (13 : ZMod 321535273) ^ 313999 := by rw [pow_add]
          _ = 288666728 := by rw [fermat_18]; decide
      have fermat_20 : (13 : ZMod 321535273) ^ 1255997 = 283937152 := by
        calc
          (13 : ZMod 321535273) ^ 1255997 = (13 : ZMod 321535273) ^ (627998 + 627998 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 627998 * (13 : ZMod 321535273) ^ 627998) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 283937152 := by rw [fermat_19]; decide
      have fermat_21 : (13 : ZMod 321535273) ^ 2511994 = 128720696 := by
        calc
          (13 : ZMod 321535273) ^ 2511994 = (13 : ZMod 321535273) ^ (1255997 + 1255997) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 1255997 * (13 : ZMod 321535273) ^ 1255997 := by rw [pow_add]
          _ = 128720696 := by rw [fermat_20]; decide
      have fermat_22 : (13 : ZMod 321535273) ^ 5023988 = 145595612 := by
        calc
          (13 : ZMod 321535273) ^ 5023988 = (13 : ZMod 321535273) ^ (2511994 + 2511994) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 2511994 * (13 : ZMod 321535273) ^ 2511994 := by rw [pow_add]
          _ = 145595612 := by rw [fermat_21]; decide
      have fermat_23 : (13 : ZMod 321535273) ^ 10047977 = 51373395 := by
        calc
          (13 : ZMod 321535273) ^ 10047977 = (13 : ZMod 321535273) ^ (5023988 + 5023988 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 5023988 * (13 : ZMod 321535273) ^ 5023988) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 51373395 := by rw [fermat_22]; decide
      have fermat_24 : (13 : ZMod 321535273) ^ 20095954 = 207522698 := by
        calc
          (13 : ZMod 321535273) ^ 20095954 = (13 : ZMod 321535273) ^ (10047977 + 10047977) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 10047977 * (13 : ZMod 321535273) ^ 10047977 := by rw [pow_add]
          _ = 207522698 := by rw [fermat_23]; decide
      have fermat_25 : (13 : ZMod 321535273) ^ 40191909 = 116000625 := by
        calc
          (13 : ZMod 321535273) ^ 40191909 = (13 : ZMod 321535273) ^ (20095954 + 20095954 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 20095954 * (13 : ZMod 321535273) ^ 20095954) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 116000625 := by rw [fermat_24]; decide
      have fermat_26 : (13 : ZMod 321535273) ^ 80383818 = 253515988 := by
        calc
          (13 : ZMod 321535273) ^ 80383818 = (13 : ZMod 321535273) ^ (40191909 + 40191909) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 40191909 * (13 : ZMod 321535273) ^ 40191909 := by rw [pow_add]
          _ = 253515988 := by rw [fermat_25]; decide
      have fermat_27 : (13 : ZMod 321535273) ^ 160767636 = 321535272 := by
        calc
          (13 : ZMod 321535273) ^ 160767636 = (13 : ZMod 321535273) ^ (80383818 + 80383818) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 80383818 * (13 : ZMod 321535273) ^ 80383818 := by rw [pow_add]
          _ = 321535272 := by rw [fermat_26]; decide
      have fermat_28 : (13 : ZMod 321535273) ^ 321535272 = 1 := by
        calc
          (13 : ZMod 321535273) ^ 321535272 = (13 : ZMod 321535273) ^ (160767636 + 160767636) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 160767636 * (13 : ZMod 321535273) ^ 160767636 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (47, 1), (285049, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (47, 1), (285049, 1)] : List FactorBlock).map factorBlockValue).prod = 321535273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (13 : ZMod 321535273) ^ 1 = 13 := by norm_num
      have factor_0_1 : (13 : ZMod 321535273) ^ 2 = 169 := by
        calc
          (13 : ZMod 321535273) ^ 2 = (13 : ZMod 321535273) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 1 * (13 : ZMod 321535273) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_0_0]; decide
      have factor_0_2 : (13 : ZMod 321535273) ^ 4 = 28561 := by
        calc
          (13 : ZMod 321535273) ^ 4 = (13 : ZMod 321535273) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 2 * (13 : ZMod 321535273) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_0_1]; decide
      have factor_0_3 : (13 : ZMod 321535273) ^ 9 = 315370637 := by
        calc
          (13 : ZMod 321535273) ^ 9 = (13 : ZMod 321535273) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 4 * (13 : ZMod 321535273) ^ 4) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 315370637 := by rw [factor_0_2]; decide
      have factor_0_4 : (13 : ZMod 321535273) ^ 19 = 171085951 := by
        calc
          (13 : ZMod 321535273) ^ 19 = (13 : ZMod 321535273) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 9 * (13 : ZMod 321535273) ^ 9) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 171085951 := by rw [factor_0_3]; decide
      have factor_0_5 : (13 : ZMod 321535273) ^ 38 = 131070786 := by
        calc
          (13 : ZMod 321535273) ^ 38 = (13 : ZMod 321535273) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 19 * (13 : ZMod 321535273) ^ 19 := by rw [pow_add]
          _ = 131070786 := by rw [factor_0_4]; decide
      have factor_0_6 : (13 : ZMod 321535273) ^ 76 = 82409681 := by
        calc
          (13 : ZMod 321535273) ^ 76 = (13 : ZMod 321535273) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 38 * (13 : ZMod 321535273) ^ 38 := by rw [pow_add]
          _ = 82409681 := by rw [factor_0_5]; decide
      have factor_0_7 : (13 : ZMod 321535273) ^ 153 = 306297043 := by
        calc
          (13 : ZMod 321535273) ^ 153 = (13 : ZMod 321535273) ^ (76 + 76 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 76 * (13 : ZMod 321535273) ^ 76) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 306297043 := by rw [factor_0_6]; decide
      have factor_0_8 : (13 : ZMod 321535273) ^ 306 = 203895217 := by
        calc
          (13 : ZMod 321535273) ^ 306 = (13 : ZMod 321535273) ^ (153 + 153) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 153 * (13 : ZMod 321535273) ^ 153 := by rw [pow_add]
          _ = 203895217 := by rw [factor_0_7]; decide
      have factor_0_9 : (13 : ZMod 321535273) ^ 613 = 106498500 := by
        calc
          (13 : ZMod 321535273) ^ 613 = (13 : ZMod 321535273) ^ (306 + 306 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 306 * (13 : ZMod 321535273) ^ 306) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 106498500 := by rw [factor_0_8]; decide
      have factor_0_10 : (13 : ZMod 321535273) ^ 1226 = 108007192 := by
        calc
          (13 : ZMod 321535273) ^ 1226 = (13 : ZMod 321535273) ^ (613 + 613) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 613 * (13 : ZMod 321535273) ^ 613 := by rw [pow_add]
          _ = 108007192 := by rw [factor_0_9]; decide
      have factor_0_11 : (13 : ZMod 321535273) ^ 2453 = 55731706 := by
        calc
          (13 : ZMod 321535273) ^ 2453 = (13 : ZMod 321535273) ^ (1226 + 1226 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 1226 * (13 : ZMod 321535273) ^ 1226) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 55731706 := by rw [factor_0_10]; decide
      have factor_0_12 : (13 : ZMod 321535273) ^ 4906 = 33336988 := by
        calc
          (13 : ZMod 321535273) ^ 4906 = (13 : ZMod 321535273) ^ (2453 + 2453) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 2453 * (13 : ZMod 321535273) ^ 2453 := by rw [pow_add]
          _ = 33336988 := by rw [factor_0_11]; decide
      have factor_0_13 : (13 : ZMod 321535273) ^ 9812 = 251314944 := by
        calc
          (13 : ZMod 321535273) ^ 9812 = (13 : ZMod 321535273) ^ (4906 + 4906) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 4906 * (13 : ZMod 321535273) ^ 4906 := by rw [pow_add]
          _ = 251314944 := by rw [factor_0_12]; decide
      have factor_0_14 : (13 : ZMod 321535273) ^ 19624 = 71834931 := by
        calc
          (13 : ZMod 321535273) ^ 19624 = (13 : ZMod 321535273) ^ (9812 + 9812) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 9812 * (13 : ZMod 321535273) ^ 9812 := by rw [pow_add]
          _ = 71834931 := by rw [factor_0_13]; decide
      have factor_0_15 : (13 : ZMod 321535273) ^ 39249 = 247523580 := by
        calc
          (13 : ZMod 321535273) ^ 39249 = (13 : ZMod 321535273) ^ (19624 + 19624 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 19624 * (13 : ZMod 321535273) ^ 19624) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 247523580 := by rw [factor_0_14]; decide
      have factor_0_16 : (13 : ZMod 321535273) ^ 78499 = 206636622 := by
        calc
          (13 : ZMod 321535273) ^ 78499 = (13 : ZMod 321535273) ^ (39249 + 39249 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 39249 * (13 : ZMod 321535273) ^ 39249) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 206636622 := by rw [factor_0_15]; decide
      have factor_0_17 : (13 : ZMod 321535273) ^ 156999 = 214334258 := by
        calc
          (13 : ZMod 321535273) ^ 156999 = (13 : ZMod 321535273) ^ (78499 + 78499 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 78499 * (13 : ZMod 321535273) ^ 78499) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 214334258 := by rw [factor_0_16]; decide
      have factor_0_18 : (13 : ZMod 321535273) ^ 313999 = 60786840 := by
        calc
          (13 : ZMod 321535273) ^ 313999 = (13 : ZMod 321535273) ^ (156999 + 156999 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 156999 * (13 : ZMod 321535273) ^ 156999) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 60786840 := by rw [factor_0_17]; decide
      have factor_0_19 : (13 : ZMod 321535273) ^ 627998 = 288666728 := by
        calc
          (13 : ZMod 321535273) ^ 627998 = (13 : ZMod 321535273) ^ (313999 + 313999) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 313999 * (13 : ZMod 321535273) ^ 313999 := by rw [pow_add]
          _ = 288666728 := by rw [factor_0_18]; decide
      have factor_0_20 : (13 : ZMod 321535273) ^ 1255997 = 283937152 := by
        calc
          (13 : ZMod 321535273) ^ 1255997 = (13 : ZMod 321535273) ^ (627998 + 627998 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 627998 * (13 : ZMod 321535273) ^ 627998) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 283937152 := by rw [factor_0_19]; decide
      have factor_0_21 : (13 : ZMod 321535273) ^ 2511994 = 128720696 := by
        calc
          (13 : ZMod 321535273) ^ 2511994 = (13 : ZMod 321535273) ^ (1255997 + 1255997) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 1255997 * (13 : ZMod 321535273) ^ 1255997 := by rw [pow_add]
          _ = 128720696 := by rw [factor_0_20]; decide
      have factor_0_22 : (13 : ZMod 321535273) ^ 5023988 = 145595612 := by
        calc
          (13 : ZMod 321535273) ^ 5023988 = (13 : ZMod 321535273) ^ (2511994 + 2511994) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 2511994 * (13 : ZMod 321535273) ^ 2511994 := by rw [pow_add]
          _ = 145595612 := by rw [factor_0_21]; decide
      have factor_0_23 : (13 : ZMod 321535273) ^ 10047977 = 51373395 := by
        calc
          (13 : ZMod 321535273) ^ 10047977 = (13 : ZMod 321535273) ^ (5023988 + 5023988 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 5023988 * (13 : ZMod 321535273) ^ 5023988) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 51373395 := by rw [factor_0_22]; decide
      have factor_0_24 : (13 : ZMod 321535273) ^ 20095954 = 207522698 := by
        calc
          (13 : ZMod 321535273) ^ 20095954 = (13 : ZMod 321535273) ^ (10047977 + 10047977) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 10047977 * (13 : ZMod 321535273) ^ 10047977 := by rw [pow_add]
          _ = 207522698 := by rw [factor_0_23]; decide
      have factor_0_25 : (13 : ZMod 321535273) ^ 40191909 = 116000625 := by
        calc
          (13 : ZMod 321535273) ^ 40191909 = (13 : ZMod 321535273) ^ (20095954 + 20095954 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 20095954 * (13 : ZMod 321535273) ^ 20095954) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 116000625 := by rw [factor_0_24]; decide
      have factor_0_26 : (13 : ZMod 321535273) ^ 80383818 = 253515988 := by
        calc
          (13 : ZMod 321535273) ^ 80383818 = (13 : ZMod 321535273) ^ (40191909 + 40191909) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 40191909 * (13 : ZMod 321535273) ^ 40191909 := by rw [pow_add]
          _ = 253515988 := by rw [factor_0_25]; decide
      have factor_0_27 : (13 : ZMod 321535273) ^ 160767636 = 321535272 := by
        calc
          (13 : ZMod 321535273) ^ 160767636 = (13 : ZMod 321535273) ^ (80383818 + 80383818) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 80383818 * (13 : ZMod 321535273) ^ 80383818 := by rw [pow_add]
          _ = 321535272 := by rw [factor_0_26]; decide
      change (13 : ZMod 321535273) ^ 160767636 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (13 : ZMod 321535273) ^ 1 = 13 := by norm_num
      have factor_1_1 : (13 : ZMod 321535273) ^ 3 = 2197 := by
        calc
          (13 : ZMod 321535273) ^ 3 = (13 : ZMod 321535273) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 1 * (13 : ZMod 321535273) ^ 1) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_1_0]; decide
      have factor_1_2 : (13 : ZMod 321535273) ^ 6 = 4826809 := by
        calc
          (13 : ZMod 321535273) ^ 6 = (13 : ZMod 321535273) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 3 * (13 : ZMod 321535273) ^ 3 := by rw [pow_add]
          _ = 4826809 := by rw [factor_1_1]; decide
      have factor_1_3 : (13 : ZMod 321535273) ^ 12 = 282311447 := by
        calc
          (13 : ZMod 321535273) ^ 12 = (13 : ZMod 321535273) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 6 * (13 : ZMod 321535273) ^ 6 := by rw [pow_add]
          _ = 282311447 := by rw [factor_1_2]; decide
      have factor_1_4 : (13 : ZMod 321535273) ^ 25 = 166414459 := by
        calc
          (13 : ZMod 321535273) ^ 25 = (13 : ZMod 321535273) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 12 * (13 : ZMod 321535273) ^ 12) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 166414459 := by rw [factor_1_3]; decide
      have factor_1_5 : (13 : ZMod 321535273) ^ 51 = 251422252 := by
        calc
          (13 : ZMod 321535273) ^ 51 = (13 : ZMod 321535273) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 25 * (13 : ZMod 321535273) ^ 25) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 251422252 := by rw [factor_1_4]; decide
      have factor_1_6 : (13 : ZMod 321535273) ^ 102 = 285224086 := by
        calc
          (13 : ZMod 321535273) ^ 102 = (13 : ZMod 321535273) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 51 * (13 : ZMod 321535273) ^ 51 := by rw [pow_add]
          _ = 285224086 := by rw [factor_1_5]; decide
      have factor_1_7 : (13 : ZMod 321535273) ^ 204 = 291797884 := by
        calc
          (13 : ZMod 321535273) ^ 204 = (13 : ZMod 321535273) ^ (102 + 102) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 102 * (13 : ZMod 321535273) ^ 102 := by rw [pow_add]
          _ = 291797884 := by rw [factor_1_6]; decide
      have factor_1_8 : (13 : ZMod 321535273) ^ 408 = 273910881 := by
        calc
          (13 : ZMod 321535273) ^ 408 = (13 : ZMod 321535273) ^ (204 + 204) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 204 * (13 : ZMod 321535273) ^ 204 := by rw [pow_add]
          _ = 273910881 := by rw [factor_1_7]; decide
      have factor_1_9 : (13 : ZMod 321535273) ^ 817 = 71818840 := by
        calc
          (13 : ZMod 321535273) ^ 817 = (13 : ZMod 321535273) ^ (408 + 408 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 408 * (13 : ZMod 321535273) ^ 408) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 71818840 := by rw [factor_1_8]; decide
      have factor_1_10 : (13 : ZMod 321535273) ^ 1635 = 42753248 := by
        calc
          (13 : ZMod 321535273) ^ 1635 = (13 : ZMod 321535273) ^ (817 + 817 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 817 * (13 : ZMod 321535273) ^ 817) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 42753248 := by rw [factor_1_9]; decide
      have factor_1_11 : (13 : ZMod 321535273) ^ 3270 = 288209306 := by
        calc
          (13 : ZMod 321535273) ^ 3270 = (13 : ZMod 321535273) ^ (1635 + 1635) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 1635 * (13 : ZMod 321535273) ^ 1635 := by rw [pow_add]
          _ = 288209306 := by rw [factor_1_10]; decide
      have factor_1_12 : (13 : ZMod 321535273) ^ 6541 = 255474292 := by
        calc
          (13 : ZMod 321535273) ^ 6541 = (13 : ZMod 321535273) ^ (3270 + 3270 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 3270 * (13 : ZMod 321535273) ^ 3270) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 255474292 := by rw [factor_1_11]; decide
      have factor_1_13 : (13 : ZMod 321535273) ^ 13083 = 157669838 := by
        calc
          (13 : ZMod 321535273) ^ 13083 = (13 : ZMod 321535273) ^ (6541 + 6541 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 6541 * (13 : ZMod 321535273) ^ 6541) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 157669838 := by rw [factor_1_12]; decide
      have factor_1_14 : (13 : ZMod 321535273) ^ 26166 = 54940099 := by
        calc
          (13 : ZMod 321535273) ^ 26166 = (13 : ZMod 321535273) ^ (13083 + 13083) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 13083 * (13 : ZMod 321535273) ^ 13083 := by rw [pow_add]
          _ = 54940099 := by rw [factor_1_13]; decide
      have factor_1_15 : (13 : ZMod 321535273) ^ 52333 = 6451708 := by
        calc
          (13 : ZMod 321535273) ^ 52333 = (13 : ZMod 321535273) ^ (26166 + 26166 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 26166 * (13 : ZMod 321535273) ^ 26166) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 6451708 := by rw [factor_1_14]; decide
      have factor_1_16 : (13 : ZMod 321535273) ^ 104666 = 187351049 := by
        calc
          (13 : ZMod 321535273) ^ 104666 = (13 : ZMod 321535273) ^ (52333 + 52333) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 52333 * (13 : ZMod 321535273) ^ 52333 := by rw [pow_add]
          _ = 187351049 := by rw [factor_1_15]; decide
      have factor_1_17 : (13 : ZMod 321535273) ^ 209332 = 121450659 := by
        calc
          (13 : ZMod 321535273) ^ 209332 = (13 : ZMod 321535273) ^ (104666 + 104666) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 104666 * (13 : ZMod 321535273) ^ 104666 := by rw [pow_add]
          _ = 121450659 := by rw [factor_1_16]; decide
      have factor_1_18 : (13 : ZMod 321535273) ^ 418665 = 148285961 := by
        calc
          (13 : ZMod 321535273) ^ 418665 = (13 : ZMod 321535273) ^ (209332 + 209332 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 209332 * (13 : ZMod 321535273) ^ 209332) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 148285961 := by rw [factor_1_17]; decide
      have factor_1_19 : (13 : ZMod 321535273) ^ 837331 = 226438311 := by
        calc
          (13 : ZMod 321535273) ^ 837331 = (13 : ZMod 321535273) ^ (418665 + 418665 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 418665 * (13 : ZMod 321535273) ^ 418665) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 226438311 := by rw [factor_1_18]; decide
      have factor_1_20 : (13 : ZMod 321535273) ^ 1674662 = 223315139 := by
        calc
          (13 : ZMod 321535273) ^ 1674662 = (13 : ZMod 321535273) ^ (837331 + 837331) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 837331 * (13 : ZMod 321535273) ^ 837331 := by rw [pow_add]
          _ = 223315139 := by rw [factor_1_19]; decide
      have factor_1_21 : (13 : ZMod 321535273) ^ 3349325 = 61383805 := by
        calc
          (13 : ZMod 321535273) ^ 3349325 = (13 : ZMod 321535273) ^ (1674662 + 1674662 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 1674662 * (13 : ZMod 321535273) ^ 1674662) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 61383805 := by rw [factor_1_20]; decide
      have factor_1_22 : (13 : ZMod 321535273) ^ 6698651 = 266021159 := by
        calc
          (13 : ZMod 321535273) ^ 6698651 = (13 : ZMod 321535273) ^ (3349325 + 3349325 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 3349325 * (13 : ZMod 321535273) ^ 3349325) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 266021159 := by rw [factor_1_21]; decide
      have factor_1_23 : (13 : ZMod 321535273) ^ 13397303 = 289845037 := by
        calc
          (13 : ZMod 321535273) ^ 13397303 = (13 : ZMod 321535273) ^ (6698651 + 6698651 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 6698651 * (13 : ZMod 321535273) ^ 6698651) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 289845037 := by rw [factor_1_22]; decide
      have factor_1_24 : (13 : ZMod 321535273) ^ 26794606 = 4387870 := by
        calc
          (13 : ZMod 321535273) ^ 26794606 = (13 : ZMod 321535273) ^ (13397303 + 13397303) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 13397303 * (13 : ZMod 321535273) ^ 13397303 := by rw [pow_add]
          _ = 4387870 := by rw [factor_1_23]; decide
      have factor_1_25 : (13 : ZMod 321535273) ^ 53589212 = 192524933 := by
        calc
          (13 : ZMod 321535273) ^ 53589212 = (13 : ZMod 321535273) ^ (26794606 + 26794606) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 26794606 * (13 : ZMod 321535273) ^ 26794606 := by rw [pow_add]
          _ = 192524933 := by rw [factor_1_24]; decide
      have factor_1_26 : (13 : ZMod 321535273) ^ 107178424 = 192524932 := by
        calc
          (13 : ZMod 321535273) ^ 107178424 = (13 : ZMod 321535273) ^ (53589212 + 53589212) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 53589212 * (13 : ZMod 321535273) ^ 53589212 := by rw [pow_add]
          _ = 192524932 := by rw [factor_1_25]; decide
      change (13 : ZMod 321535273) ^ 107178424 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (13 : ZMod 321535273) ^ 1 = 13 := by norm_num
      have factor_2_1 : (13 : ZMod 321535273) ^ 3 = 2197 := by
        calc
          (13 : ZMod 321535273) ^ 3 = (13 : ZMod 321535273) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 1 * (13 : ZMod 321535273) ^ 1) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_2_0]; decide
      have factor_2_2 : (13 : ZMod 321535273) ^ 6 = 4826809 := by
        calc
          (13 : ZMod 321535273) ^ 6 = (13 : ZMod 321535273) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 3 * (13 : ZMod 321535273) ^ 3 := by rw [pow_add]
          _ = 4826809 := by rw [factor_2_1]; decide
      have factor_2_3 : (13 : ZMod 321535273) ^ 13 = 133160808 := by
        calc
          (13 : ZMod 321535273) ^ 13 = (13 : ZMod 321535273) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 6 * (13 : ZMod 321535273) ^ 6) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 133160808 := by rw [factor_2_2]; decide
      have factor_2_4 : (13 : ZMod 321535273) ^ 26 = 234176329 := by
        calc
          (13 : ZMod 321535273) ^ 26 = (13 : ZMod 321535273) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 13 * (13 : ZMod 321535273) ^ 13 := by rw [pow_add]
          _ = 234176329 := by rw [factor_2_3]; decide
      have factor_2_5 : (13 : ZMod 321535273) ^ 52 = 53136546 := by
        calc
          (13 : ZMod 321535273) ^ 52 = (13 : ZMod 321535273) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 26 * (13 : ZMod 321535273) ^ 26 := by rw [pow_add]
          _ = 53136546 := by rw [factor_2_4]; decide
      have factor_2_6 : (13 : ZMod 321535273) ^ 104 = 294114857 := by
        calc
          (13 : ZMod 321535273) ^ 104 = (13 : ZMod 321535273) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 52 * (13 : ZMod 321535273) ^ 52 := by rw [pow_add]
          _ = 294114857 := by rw [factor_2_5]; decide
      have factor_2_7 : (13 : ZMod 321535273) ^ 208 = 166624037 := by
        calc
          (13 : ZMod 321535273) ^ 208 = (13 : ZMod 321535273) ^ (104 + 104) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 104 * (13 : ZMod 321535273) ^ 104 := by rw [pow_add]
          _ = 166624037 := by rw [factor_2_6]; decide
      have factor_2_8 : (13 : ZMod 321535273) ^ 417 = 257401018 := by
        calc
          (13 : ZMod 321535273) ^ 417 = (13 : ZMod 321535273) ^ (208 + 208 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 208 * (13 : ZMod 321535273) ^ 208) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 257401018 := by rw [factor_2_7]; decide
      have factor_2_9 : (13 : ZMod 321535273) ^ 835 = 95909782 := by
        calc
          (13 : ZMod 321535273) ^ 835 = (13 : ZMod 321535273) ^ (417 + 417 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 417 * (13 : ZMod 321535273) ^ 417) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 95909782 := by rw [factor_2_8]; decide
      have factor_2_10 : (13 : ZMod 321535273) ^ 1670 = 53799350 := by
        calc
          (13 : ZMod 321535273) ^ 1670 = (13 : ZMod 321535273) ^ (835 + 835) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 835 * (13 : ZMod 321535273) ^ 835 := by rw [pow_add]
          _ = 53799350 := by rw [factor_2_9]; decide
      have factor_2_11 : (13 : ZMod 321535273) ^ 3340 = 205823486 := by
        calc
          (13 : ZMod 321535273) ^ 3340 = (13 : ZMod 321535273) ^ (1670 + 1670) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 1670 * (13 : ZMod 321535273) ^ 1670 := by rw [pow_add]
          _ = 205823486 := by rw [factor_2_10]; decide
      have factor_2_12 : (13 : ZMod 321535273) ^ 6680 = 149398409 := by
        calc
          (13 : ZMod 321535273) ^ 6680 = (13 : ZMod 321535273) ^ (3340 + 3340) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 3340 * (13 : ZMod 321535273) ^ 3340 := by rw [pow_add]
          _ = 149398409 := by rw [factor_2_11]; decide
      have factor_2_13 : (13 : ZMod 321535273) ^ 13361 = 272192535 := by
        calc
          (13 : ZMod 321535273) ^ 13361 = (13 : ZMod 321535273) ^ (6680 + 6680 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 6680 * (13 : ZMod 321535273) ^ 6680) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 272192535 := by rw [factor_2_12]; decide
      have factor_2_14 : (13 : ZMod 321535273) ^ 26723 = 254824287 := by
        calc
          (13 : ZMod 321535273) ^ 26723 = (13 : ZMod 321535273) ^ (13361 + 13361 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 13361 * (13 : ZMod 321535273) ^ 13361) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 254824287 := by rw [factor_2_13]; decide
      have factor_2_15 : (13 : ZMod 321535273) ^ 53446 = 87051208 := by
        calc
          (13 : ZMod 321535273) ^ 53446 = (13 : ZMod 321535273) ^ (26723 + 26723) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 26723 * (13 : ZMod 321535273) ^ 26723 := by rw [pow_add]
          _ = 87051208 := by rw [factor_2_14]; decide
      have factor_2_16 : (13 : ZMod 321535273) ^ 106893 = 277065314 := by
        calc
          (13 : ZMod 321535273) ^ 106893 = (13 : ZMod 321535273) ^ (53446 + 53446 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 53446 * (13 : ZMod 321535273) ^ 53446) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 277065314 := by rw [factor_2_15]; decide
      have factor_2_17 : (13 : ZMod 321535273) ^ 213786 = 279697021 := by
        calc
          (13 : ZMod 321535273) ^ 213786 = (13 : ZMod 321535273) ^ (106893 + 106893) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 106893 * (13 : ZMod 321535273) ^ 106893 := by rw [pow_add]
          _ = 279697021 := by rw [factor_2_16]; decide
      have factor_2_18 : (13 : ZMod 321535273) ^ 427573 = 234811356 := by
        calc
          (13 : ZMod 321535273) ^ 427573 = (13 : ZMod 321535273) ^ (213786 + 213786 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 213786 * (13 : ZMod 321535273) ^ 213786) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 234811356 := by rw [factor_2_17]; decide
      have factor_2_19 : (13 : ZMod 321535273) ^ 855147 = 12685034 := by
        calc
          (13 : ZMod 321535273) ^ 855147 = (13 : ZMod 321535273) ^ (427573 + 427573 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 427573 * (13 : ZMod 321535273) ^ 427573) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 12685034 := by rw [factor_2_18]; decide
      have factor_2_20 : (13 : ZMod 321535273) ^ 1710294 = 10955217 := by
        calc
          (13 : ZMod 321535273) ^ 1710294 = (13 : ZMod 321535273) ^ (855147 + 855147) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 855147 * (13 : ZMod 321535273) ^ 855147 := by rw [pow_add]
          _ = 10955217 := by rw [factor_2_19]; decide
      have factor_2_21 : (13 : ZMod 321535273) ^ 3420588 = 201981836 := by
        calc
          (13 : ZMod 321535273) ^ 3420588 = (13 : ZMod 321535273) ^ (1710294 + 1710294) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 1710294 * (13 : ZMod 321535273) ^ 1710294 := by rw [pow_add]
          _ = 201981836 := by rw [factor_2_20]; decide
      have factor_2_22 : (13 : ZMod 321535273) ^ 6841176 = 82949579 := by
        calc
          (13 : ZMod 321535273) ^ 6841176 = (13 : ZMod 321535273) ^ (3420588 + 3420588) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 3420588 * (13 : ZMod 321535273) ^ 3420588 := by rw [pow_add]
          _ = 82949579 := by rw [factor_2_21]; decide
      change (13 : ZMod 321535273) ^ 6841176 ≠ 1
      rw [factor_2_22]
      decide
    ·
      have factor_3_0 : (13 : ZMod 321535273) ^ 1 = 13 := by norm_num
      have factor_3_1 : (13 : ZMod 321535273) ^ 2 = 169 := by
        calc
          (13 : ZMod 321535273) ^ 2 = (13 : ZMod 321535273) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 1 * (13 : ZMod 321535273) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_3_0]; decide
      have factor_3_2 : (13 : ZMod 321535273) ^ 4 = 28561 := by
        calc
          (13 : ZMod 321535273) ^ 4 = (13 : ZMod 321535273) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 2 * (13 : ZMod 321535273) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_3_1]; decide
      have factor_3_3 : (13 : ZMod 321535273) ^ 8 = 172660175 := by
        calc
          (13 : ZMod 321535273) ^ 8 = (13 : ZMod 321535273) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 4 * (13 : ZMod 321535273) ^ 4 := by rw [pow_add]
          _ = 172660175 := by rw [factor_3_2]; decide
      have factor_3_4 : (13 : ZMod 321535273) ^ 17 = 86628244 := by
        calc
          (13 : ZMod 321535273) ^ 17 = (13 : ZMod 321535273) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 8 * (13 : ZMod 321535273) ^ 8) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 86628244 := by rw [factor_3_3]; decide
      have factor_3_5 : (13 : ZMod 321535273) ^ 35 = 199244687 := by
        calc
          (13 : ZMod 321535273) ^ 35 = (13 : ZMod 321535273) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 17 * (13 : ZMod 321535273) ^ 17) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 199244687 := by rw [factor_3_4]; decide
      have factor_3_6 : (13 : ZMod 321535273) ^ 70 = 214624345 := by
        calc
          (13 : ZMod 321535273) ^ 70 = (13 : ZMod 321535273) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 35 * (13 : ZMod 321535273) ^ 35 := by rw [pow_add]
          _ = 214624345 := by rw [factor_3_5]; decide
      have factor_3_7 : (13 : ZMod 321535273) ^ 141 = 75656002 := by
        calc
          (13 : ZMod 321535273) ^ 141 = (13 : ZMod 321535273) ^ (70 + 70 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = ((13 : ZMod 321535273) ^ 70 * (13 : ZMod 321535273) ^ 70) * (13 : ZMod 321535273) := by rw [pow_succ, pow_add]
          _ = 75656002 := by rw [factor_3_6]; decide
      have factor_3_8 : (13 : ZMod 321535273) ^ 282 = 219592305 := by
        calc
          (13 : ZMod 321535273) ^ 282 = (13 : ZMod 321535273) ^ (141 + 141) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 141 * (13 : ZMod 321535273) ^ 141 := by rw [pow_add]
          _ = 219592305 := by rw [factor_3_7]; decide
      have factor_3_9 : (13 : ZMod 321535273) ^ 564 = 157053092 := by
        calc
          (13 : ZMod 321535273) ^ 564 = (13 : ZMod 321535273) ^ (282 + 282) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 282 * (13 : ZMod 321535273) ^ 282 := by rw [pow_add]
          _ = 157053092 := by rw [factor_3_8]; decide
      have factor_3_10 : (13 : ZMod 321535273) ^ 1128 = 38823686 := by
        calc
          (13 : ZMod 321535273) ^ 1128 = (13 : ZMod 321535273) ^ (564 + 564) :=
            congrArg (fun n : ℕ => (13 : ZMod 321535273) ^ n) (by norm_num)
          _ = (13 : ZMod 321535273) ^ 564 * (13 : ZMod 321535273) ^ 564 := by rw [pow_add]
          _ = 38823686 := by rw [factor_3_9]; decide
      change (13 : ZMod 321535273) ^ 1128 ≠ 1
      rw [factor_3_10]
      decide

#print axioms prime_lucas_321535273

end TotientTailPeriodKiller
end Erdos249257
