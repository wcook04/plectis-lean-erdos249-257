import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_8508455051 : Nat.Prime 8508455051 := by
  apply lucas_primality 8508455051 (2 : ZMod 8508455051)
  ·
      have fermat_0 : (2 : ZMod 8508455051) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 8508455051) ^ 3 = 8 := by
        calc
          (2 : ZMod 8508455051) ^ 3 = (2 : ZMod 8508455051) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 1 * (2 : ZMod 8508455051) ^ 1) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 8508455051) ^ 7 = 128 := by
        calc
          (2 : ZMod 8508455051) ^ 7 = (2 : ZMod 8508455051) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 3 * (2 : ZMod 8508455051) ^ 3) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 8508455051) ^ 15 = 32768 := by
        calc
          (2 : ZMod 8508455051) ^ 15 = (2 : ZMod 8508455051) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 7 * (2 : ZMod 8508455051) ^ 7) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 8508455051) ^ 31 = 2147483648 := by
        calc
          (2 : ZMod 8508455051) ^ 31 = (2 : ZMod 8508455051) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 15 * (2 : ZMod 8508455051) ^ 15) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 2147483648 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 8508455051) ^ 63 = 6113036508 := by
        calc
          (2 : ZMod 8508455051) ^ 63 = (2 : ZMod 8508455051) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 31 * (2 : ZMod 8508455051) ^ 31) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 6113036508 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 8508455051) ^ 126 = 1893489972 := by
        calc
          (2 : ZMod 8508455051) ^ 126 = (2 : ZMod 8508455051) ^ (63 + 63) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 63 * (2 : ZMod 8508455051) ^ 63 := by rw [pow_add]
          _ = 1893489972 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 8508455051) ^ 253 = 5028178919 := by
        calc
          (2 : ZMod 8508455051) ^ 253 = (2 : ZMod 8508455051) ^ (126 + 126 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 126 * (2 : ZMod 8508455051) ^ 126) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 5028178919 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 8508455051) ^ 507 = 8099955012 := by
        calc
          (2 : ZMod 8508455051) ^ 507 = (2 : ZMod 8508455051) ^ (253 + 253 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 253 * (2 : ZMod 8508455051) ^ 253) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 8099955012 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 8508455051) ^ 1014 = 2972342797 := by
        calc
          (2 : ZMod 8508455051) ^ 1014 = (2 : ZMod 8508455051) ^ (507 + 507) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 507 * (2 : ZMod 8508455051) ^ 507 := by rw [pow_add]
          _ = 2972342797 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 8508455051) ^ 2028 = 5199474238 := by
        calc
          (2 : ZMod 8508455051) ^ 2028 = (2 : ZMod 8508455051) ^ (1014 + 1014) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 1014 * (2 : ZMod 8508455051) ^ 1014 := by rw [pow_add]
          _ = 5199474238 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 8508455051) ^ 4057 = 190126243 := by
        calc
          (2 : ZMod 8508455051) ^ 4057 = (2 : ZMod 8508455051) ^ (2028 + 2028 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 2028 * (2 : ZMod 8508455051) ^ 2028) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 190126243 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 8508455051) ^ 8114 = 4179132671 := by
        calc
          (2 : ZMod 8508455051) ^ 8114 = (2 : ZMod 8508455051) ^ (4057 + 4057) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 4057 * (2 : ZMod 8508455051) ^ 4057 := by rw [pow_add]
          _ = 4179132671 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 8508455051) ^ 16228 = 5460788153 := by
        calc
          (2 : ZMod 8508455051) ^ 16228 = (2 : ZMod 8508455051) ^ (8114 + 8114) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 8114 * (2 : ZMod 8508455051) ^ 8114 := by rw [pow_add]
          _ = 5460788153 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 8508455051) ^ 32457 = 7092197295 := by
        calc
          (2 : ZMod 8508455051) ^ 32457 = (2 : ZMod 8508455051) ^ (16228 + 16228 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 16228 * (2 : ZMod 8508455051) ^ 16228) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 7092197295 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 8508455051) ^ 64914 = 4391883553 := by
        calc
          (2 : ZMod 8508455051) ^ 64914 = (2 : ZMod 8508455051) ^ (32457 + 32457) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 32457 * (2 : ZMod 8508455051) ^ 32457 := by rw [pow_add]
          _ = 4391883553 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 8508455051) ^ 129828 = 3790112419 := by
        calc
          (2 : ZMod 8508455051) ^ 129828 = (2 : ZMod 8508455051) ^ (64914 + 64914) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 64914 * (2 : ZMod 8508455051) ^ 64914 := by rw [pow_add]
          _ = 3790112419 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 8508455051) ^ 259657 = 7745404856 := by
        calc
          (2 : ZMod 8508455051) ^ 259657 = (2 : ZMod 8508455051) ^ (129828 + 129828 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 129828 * (2 : ZMod 8508455051) ^ 129828) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 7745404856 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 8508455051) ^ 519314 = 7011076013 := by
        calc
          (2 : ZMod 8508455051) ^ 519314 = (2 : ZMod 8508455051) ^ (259657 + 259657) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 259657 * (2 : ZMod 8508455051) ^ 259657 := by rw [pow_add]
          _ = 7011076013 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 8508455051) ^ 1038629 = 1938329950 := by
        calc
          (2 : ZMod 8508455051) ^ 1038629 = (2 : ZMod 8508455051) ^ (519314 + 519314 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 519314 * (2 : ZMod 8508455051) ^ 519314) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 1938329950 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 8508455051) ^ 2077259 = 6462486591 := by
        calc
          (2 : ZMod 8508455051) ^ 2077259 = (2 : ZMod 8508455051) ^ (1038629 + 1038629 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 1038629 * (2 : ZMod 8508455051) ^ 1038629) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 6462486591 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 8508455051) ^ 4154519 = 2668731503 := by
        calc
          (2 : ZMod 8508455051) ^ 4154519 = (2 : ZMod 8508455051) ^ (2077259 + 2077259 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 2077259 * (2 : ZMod 8508455051) ^ 2077259) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 2668731503 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 8508455051) ^ 8309038 = 919266555 := by
        calc
          (2 : ZMod 8508455051) ^ 8309038 = (2 : ZMod 8508455051) ^ (4154519 + 4154519) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 4154519 * (2 : ZMod 8508455051) ^ 4154519 := by rw [pow_add]
          _ = 919266555 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 8508455051) ^ 16618076 = 7184950555 := by
        calc
          (2 : ZMod 8508455051) ^ 16618076 = (2 : ZMod 8508455051) ^ (8309038 + 8309038) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 8309038 * (2 : ZMod 8508455051) ^ 8309038 := by rw [pow_add]
          _ = 7184950555 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 8508455051) ^ 33236152 = 6258423166 := by
        calc
          (2 : ZMod 8508455051) ^ 33236152 = (2 : ZMod 8508455051) ^ (16618076 + 16618076) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 16618076 * (2 : ZMod 8508455051) ^ 16618076 := by rw [pow_add]
          _ = 6258423166 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 8508455051) ^ 66472305 = 7809820103 := by
        calc
          (2 : ZMod 8508455051) ^ 66472305 = (2 : ZMod 8508455051) ^ (33236152 + 33236152 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 33236152 * (2 : ZMod 8508455051) ^ 33236152) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 7809820103 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 8508455051) ^ 132944610 = 7828063171 := by
        calc
          (2 : ZMod 8508455051) ^ 132944610 = (2 : ZMod 8508455051) ^ (66472305 + 66472305) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 66472305 * (2 : ZMod 8508455051) ^ 66472305 := by rw [pow_add]
          _ = 7828063171 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 8508455051) ^ 265889220 = 8407460953 := by
        calc
          (2 : ZMod 8508455051) ^ 265889220 = (2 : ZMod 8508455051) ^ (132944610 + 132944610) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 132944610 * (2 : ZMod 8508455051) ^ 132944610 := by rw [pow_add]
          _ = 8407460953 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 8508455051) ^ 531778440 = 8050975620 := by
        calc
          (2 : ZMod 8508455051) ^ 531778440 = (2 : ZMod 8508455051) ^ (265889220 + 265889220) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 265889220 * (2 : ZMod 8508455051) ^ 265889220 := by rw [pow_add]
          _ = 8050975620 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 8508455051) ^ 1063556881 = 938684056 := by
        calc
          (2 : ZMod 8508455051) ^ 1063556881 = (2 : ZMod 8508455051) ^ (531778440 + 531778440 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 531778440 * (2 : ZMod 8508455051) ^ 531778440) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 938684056 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 8508455051) ^ 2127113762 = 5211063209 := by
        calc
          (2 : ZMod 8508455051) ^ 2127113762 = (2 : ZMod 8508455051) ^ (1063556881 + 1063556881) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 1063556881 * (2 : ZMod 8508455051) ^ 1063556881 := by rw [pow_add]
          _ = 5211063209 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 8508455051) ^ 4254227525 = 8508455050 := by
        calc
          (2 : ZMod 8508455051) ^ 4254227525 = (2 : ZMod 8508455051) ^ (2127113762 + 2127113762 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 2127113762 * (2 : ZMod 8508455051) ^ 2127113762) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 8508455050 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 8508455051) ^ 8508455050 = 1 := by
        calc
          (2 : ZMod 8508455051) ^ 8508455050 = (2 : ZMod 8508455051) ^ (4254227525 + 4254227525) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 4254227525 * (2 : ZMod 8508455051) ^ 4254227525 := by rw [pow_add]
          _ = 1 := by rw [fermat_31]; decide
      simpa using fermat_32
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (10687, 1), (15923, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (10687, 1), (15923, 1)] : List FactorBlock).map factorBlockValue).prod = 8508455051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 8508455051) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 8508455051) ^ 3 = 8 := by
        calc
          (2 : ZMod 8508455051) ^ 3 = (2 : ZMod 8508455051) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 1 * (2 : ZMod 8508455051) ^ 1) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 8508455051) ^ 7 = 128 := by
        calc
          (2 : ZMod 8508455051) ^ 7 = (2 : ZMod 8508455051) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 3 * (2 : ZMod 8508455051) ^ 3) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 8508455051) ^ 15 = 32768 := by
        calc
          (2 : ZMod 8508455051) ^ 15 = (2 : ZMod 8508455051) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 7 * (2 : ZMod 8508455051) ^ 7) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 8508455051) ^ 31 = 2147483648 := by
        calc
          (2 : ZMod 8508455051) ^ 31 = (2 : ZMod 8508455051) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 15 * (2 : ZMod 8508455051) ^ 15) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 2147483648 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 8508455051) ^ 63 = 6113036508 := by
        calc
          (2 : ZMod 8508455051) ^ 63 = (2 : ZMod 8508455051) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 31 * (2 : ZMod 8508455051) ^ 31) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 6113036508 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 8508455051) ^ 126 = 1893489972 := by
        calc
          (2 : ZMod 8508455051) ^ 126 = (2 : ZMod 8508455051) ^ (63 + 63) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 63 * (2 : ZMod 8508455051) ^ 63 := by rw [pow_add]
          _ = 1893489972 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 8508455051) ^ 253 = 5028178919 := by
        calc
          (2 : ZMod 8508455051) ^ 253 = (2 : ZMod 8508455051) ^ (126 + 126 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 126 * (2 : ZMod 8508455051) ^ 126) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 5028178919 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 8508455051) ^ 507 = 8099955012 := by
        calc
          (2 : ZMod 8508455051) ^ 507 = (2 : ZMod 8508455051) ^ (253 + 253 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 253 * (2 : ZMod 8508455051) ^ 253) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 8099955012 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 8508455051) ^ 1014 = 2972342797 := by
        calc
          (2 : ZMod 8508455051) ^ 1014 = (2 : ZMod 8508455051) ^ (507 + 507) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 507 * (2 : ZMod 8508455051) ^ 507 := by rw [pow_add]
          _ = 2972342797 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 8508455051) ^ 2028 = 5199474238 := by
        calc
          (2 : ZMod 8508455051) ^ 2028 = (2 : ZMod 8508455051) ^ (1014 + 1014) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 1014 * (2 : ZMod 8508455051) ^ 1014 := by rw [pow_add]
          _ = 5199474238 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 8508455051) ^ 4057 = 190126243 := by
        calc
          (2 : ZMod 8508455051) ^ 4057 = (2 : ZMod 8508455051) ^ (2028 + 2028 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 2028 * (2 : ZMod 8508455051) ^ 2028) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 190126243 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 8508455051) ^ 8114 = 4179132671 := by
        calc
          (2 : ZMod 8508455051) ^ 8114 = (2 : ZMod 8508455051) ^ (4057 + 4057) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 4057 * (2 : ZMod 8508455051) ^ 4057 := by rw [pow_add]
          _ = 4179132671 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 8508455051) ^ 16228 = 5460788153 := by
        calc
          (2 : ZMod 8508455051) ^ 16228 = (2 : ZMod 8508455051) ^ (8114 + 8114) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 8114 * (2 : ZMod 8508455051) ^ 8114 := by rw [pow_add]
          _ = 5460788153 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 8508455051) ^ 32457 = 7092197295 := by
        calc
          (2 : ZMod 8508455051) ^ 32457 = (2 : ZMod 8508455051) ^ (16228 + 16228 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 16228 * (2 : ZMod 8508455051) ^ 16228) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 7092197295 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 8508455051) ^ 64914 = 4391883553 := by
        calc
          (2 : ZMod 8508455051) ^ 64914 = (2 : ZMod 8508455051) ^ (32457 + 32457) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 32457 * (2 : ZMod 8508455051) ^ 32457 := by rw [pow_add]
          _ = 4391883553 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 8508455051) ^ 129828 = 3790112419 := by
        calc
          (2 : ZMod 8508455051) ^ 129828 = (2 : ZMod 8508455051) ^ (64914 + 64914) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 64914 * (2 : ZMod 8508455051) ^ 64914 := by rw [pow_add]
          _ = 3790112419 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 8508455051) ^ 259657 = 7745404856 := by
        calc
          (2 : ZMod 8508455051) ^ 259657 = (2 : ZMod 8508455051) ^ (129828 + 129828 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 129828 * (2 : ZMod 8508455051) ^ 129828) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 7745404856 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 8508455051) ^ 519314 = 7011076013 := by
        calc
          (2 : ZMod 8508455051) ^ 519314 = (2 : ZMod 8508455051) ^ (259657 + 259657) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 259657 * (2 : ZMod 8508455051) ^ 259657 := by rw [pow_add]
          _ = 7011076013 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 8508455051) ^ 1038629 = 1938329950 := by
        calc
          (2 : ZMod 8508455051) ^ 1038629 = (2 : ZMod 8508455051) ^ (519314 + 519314 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 519314 * (2 : ZMod 8508455051) ^ 519314) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 1938329950 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 8508455051) ^ 2077259 = 6462486591 := by
        calc
          (2 : ZMod 8508455051) ^ 2077259 = (2 : ZMod 8508455051) ^ (1038629 + 1038629 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 1038629 * (2 : ZMod 8508455051) ^ 1038629) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 6462486591 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 8508455051) ^ 4154519 = 2668731503 := by
        calc
          (2 : ZMod 8508455051) ^ 4154519 = (2 : ZMod 8508455051) ^ (2077259 + 2077259 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 2077259 * (2 : ZMod 8508455051) ^ 2077259) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 2668731503 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 8508455051) ^ 8309038 = 919266555 := by
        calc
          (2 : ZMod 8508455051) ^ 8309038 = (2 : ZMod 8508455051) ^ (4154519 + 4154519) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 4154519 * (2 : ZMod 8508455051) ^ 4154519 := by rw [pow_add]
          _ = 919266555 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 8508455051) ^ 16618076 = 7184950555 := by
        calc
          (2 : ZMod 8508455051) ^ 16618076 = (2 : ZMod 8508455051) ^ (8309038 + 8309038) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 8309038 * (2 : ZMod 8508455051) ^ 8309038 := by rw [pow_add]
          _ = 7184950555 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 8508455051) ^ 33236152 = 6258423166 := by
        calc
          (2 : ZMod 8508455051) ^ 33236152 = (2 : ZMod 8508455051) ^ (16618076 + 16618076) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 16618076 * (2 : ZMod 8508455051) ^ 16618076 := by rw [pow_add]
          _ = 6258423166 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 8508455051) ^ 66472305 = 7809820103 := by
        calc
          (2 : ZMod 8508455051) ^ 66472305 = (2 : ZMod 8508455051) ^ (33236152 + 33236152 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 33236152 * (2 : ZMod 8508455051) ^ 33236152) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 7809820103 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 8508455051) ^ 132944610 = 7828063171 := by
        calc
          (2 : ZMod 8508455051) ^ 132944610 = (2 : ZMod 8508455051) ^ (66472305 + 66472305) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 66472305 * (2 : ZMod 8508455051) ^ 66472305 := by rw [pow_add]
          _ = 7828063171 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 8508455051) ^ 265889220 = 8407460953 := by
        calc
          (2 : ZMod 8508455051) ^ 265889220 = (2 : ZMod 8508455051) ^ (132944610 + 132944610) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 132944610 * (2 : ZMod 8508455051) ^ 132944610 := by rw [pow_add]
          _ = 8407460953 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 8508455051) ^ 531778440 = 8050975620 := by
        calc
          (2 : ZMod 8508455051) ^ 531778440 = (2 : ZMod 8508455051) ^ (265889220 + 265889220) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 265889220 * (2 : ZMod 8508455051) ^ 265889220 := by rw [pow_add]
          _ = 8050975620 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 8508455051) ^ 1063556881 = 938684056 := by
        calc
          (2 : ZMod 8508455051) ^ 1063556881 = (2 : ZMod 8508455051) ^ (531778440 + 531778440 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 531778440 * (2 : ZMod 8508455051) ^ 531778440) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 938684056 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 8508455051) ^ 2127113762 = 5211063209 := by
        calc
          (2 : ZMod 8508455051) ^ 2127113762 = (2 : ZMod 8508455051) ^ (1063556881 + 1063556881) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 1063556881 * (2 : ZMod 8508455051) ^ 1063556881 := by rw [pow_add]
          _ = 5211063209 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 8508455051) ^ 4254227525 = 8508455050 := by
        calc
          (2 : ZMod 8508455051) ^ 4254227525 = (2 : ZMod 8508455051) ^ (2127113762 + 2127113762 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 2127113762 * (2 : ZMod 8508455051) ^ 2127113762) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 8508455050 := by rw [factor_0_30]; decide
      change (2 : ZMod 8508455051) ^ 4254227525 ≠ 1
      rw [factor_0_31]
      decide
    ·
      have factor_1_0 : (2 : ZMod 8508455051) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 8508455051) ^ 3 = 8 := by
        calc
          (2 : ZMod 8508455051) ^ 3 = (2 : ZMod 8508455051) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 1 * (2 : ZMod 8508455051) ^ 1) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 8508455051) ^ 6 = 64 := by
        calc
          (2 : ZMod 8508455051) ^ 6 = (2 : ZMod 8508455051) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 3 * (2 : ZMod 8508455051) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 8508455051) ^ 12 = 4096 := by
        calc
          (2 : ZMod 8508455051) ^ 12 = (2 : ZMod 8508455051) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 6 * (2 : ZMod 8508455051) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 8508455051) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 8508455051) ^ 25 = (2 : ZMod 8508455051) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 12 * (2 : ZMod 8508455051) ^ 12) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 8508455051) ^ 50 = 1575308947 := by
        calc
          (2 : ZMod 8508455051) ^ 50 = (2 : ZMod 8508455051) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 25 * (2 : ZMod 8508455051) ^ 25 := by rw [pow_add]
          _ = 1575308947 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 8508455051) ^ 101 = 6376530582 := by
        calc
          (2 : ZMod 8508455051) ^ 101 = (2 : ZMod 8508455051) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 50 * (2 : ZMod 8508455051) ^ 50) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 6376530582 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 8508455051) ^ 202 = 6810004798 := by
        calc
          (2 : ZMod 8508455051) ^ 202 = (2 : ZMod 8508455051) ^ (101 + 101) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 101 * (2 : ZMod 8508455051) ^ 101 := by rw [pow_add]
          _ = 6810004798 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 8508455051) ^ 405 = 361643401 := by
        calc
          (2 : ZMod 8508455051) ^ 405 = (2 : ZMod 8508455051) ^ (202 + 202 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 202 * (2 : ZMod 8508455051) ^ 202) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 361643401 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 8508455051) ^ 811 = 4858101818 := by
        calc
          (2 : ZMod 8508455051) ^ 811 = (2 : ZMod 8508455051) ^ (405 + 405 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 405 * (2 : ZMod 8508455051) ^ 405) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 4858101818 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 8508455051) ^ 1622 = 7459663636 := by
        calc
          (2 : ZMod 8508455051) ^ 1622 = (2 : ZMod 8508455051) ^ (811 + 811) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 811 * (2 : ZMod 8508455051) ^ 811 := by rw [pow_add]
          _ = 7459663636 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 8508455051) ^ 3245 = 6527990016 := by
        calc
          (2 : ZMod 8508455051) ^ 3245 = (2 : ZMod 8508455051) ^ (1622 + 1622 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 1622 * (2 : ZMod 8508455051) ^ 1622) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 6527990016 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 8508455051) ^ 6491 = 282097875 := by
        calc
          (2 : ZMod 8508455051) ^ 6491 = (2 : ZMod 8508455051) ^ (3245 + 3245 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 3245 * (2 : ZMod 8508455051) ^ 3245) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 282097875 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 8508455051) ^ 12982 = 5359534869 := by
        calc
          (2 : ZMod 8508455051) ^ 12982 = (2 : ZMod 8508455051) ^ (6491 + 6491) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 6491 * (2 : ZMod 8508455051) ^ 6491 := by rw [pow_add]
          _ = 5359534869 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 8508455051) ^ 25965 = 6564223075 := by
        calc
          (2 : ZMod 8508455051) ^ 25965 = (2 : ZMod 8508455051) ^ (12982 + 12982 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 12982 * (2 : ZMod 8508455051) ^ 12982) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 6564223075 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 8508455051) ^ 51931 = 1518139190 := by
        calc
          (2 : ZMod 8508455051) ^ 51931 = (2 : ZMod 8508455051) ^ (25965 + 25965 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 25965 * (2 : ZMod 8508455051) ^ 25965) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 1518139190 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 8508455051) ^ 103862 = 554748186 := by
        calc
          (2 : ZMod 8508455051) ^ 103862 = (2 : ZMod 8508455051) ^ (51931 + 51931) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 51931 * (2 : ZMod 8508455051) ^ 51931 := by rw [pow_add]
          _ = 554748186 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 8508455051) ^ 207725 = 3327049381 := by
        calc
          (2 : ZMod 8508455051) ^ 207725 = (2 : ZMod 8508455051) ^ (103862 + 103862 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 103862 * (2 : ZMod 8508455051) ^ 103862) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 3327049381 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 8508455051) ^ 415451 = 4359412710 := by
        calc
          (2 : ZMod 8508455051) ^ 415451 = (2 : ZMod 8508455051) ^ (207725 + 207725 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 207725 * (2 : ZMod 8508455051) ^ 207725) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 4359412710 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 8508455051) ^ 830903 = 4872695467 := by
        calc
          (2 : ZMod 8508455051) ^ 830903 = (2 : ZMod 8508455051) ^ (415451 + 415451 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 415451 * (2 : ZMod 8508455051) ^ 415451) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 4872695467 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 8508455051) ^ 1661807 = 2510627445 := by
        calc
          (2 : ZMod 8508455051) ^ 1661807 = (2 : ZMod 8508455051) ^ (830903 + 830903 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 830903 * (2 : ZMod 8508455051) ^ 830903) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 2510627445 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 8508455051) ^ 3323615 = 6130583323 := by
        calc
          (2 : ZMod 8508455051) ^ 3323615 = (2 : ZMod 8508455051) ^ (1661807 + 1661807 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 1661807 * (2 : ZMod 8508455051) ^ 1661807) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 6130583323 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 8508455051) ^ 6647230 = 905289967 := by
        calc
          (2 : ZMod 8508455051) ^ 6647230 = (2 : ZMod 8508455051) ^ (3323615 + 3323615) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 3323615 * (2 : ZMod 8508455051) ^ 3323615 := by rw [pow_add]
          _ = 905289967 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 8508455051) ^ 13294461 = 3307690977 := by
        calc
          (2 : ZMod 8508455051) ^ 13294461 = (2 : ZMod 8508455051) ^ (6647230 + 6647230 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 6647230 * (2 : ZMod 8508455051) ^ 6647230) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 3307690977 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 8508455051) ^ 26588922 = 5730179859 := by
        calc
          (2 : ZMod 8508455051) ^ 26588922 = (2 : ZMod 8508455051) ^ (13294461 + 13294461) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 13294461 * (2 : ZMod 8508455051) ^ 13294461 := by rw [pow_add]
          _ = 5730179859 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 8508455051) ^ 53177844 = 1236300808 := by
        calc
          (2 : ZMod 8508455051) ^ 53177844 = (2 : ZMod 8508455051) ^ (26588922 + 26588922) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 26588922 * (2 : ZMod 8508455051) ^ 26588922 := by rw [pow_add]
          _ = 1236300808 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 8508455051) ^ 106355688 = 557497818 := by
        calc
          (2 : ZMod 8508455051) ^ 106355688 = (2 : ZMod 8508455051) ^ (53177844 + 53177844) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 53177844 * (2 : ZMod 8508455051) ^ 53177844 := by rw [pow_add]
          _ = 557497818 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 8508455051) ^ 212711376 = 2547146355 := by
        calc
          (2 : ZMod 8508455051) ^ 212711376 = (2 : ZMod 8508455051) ^ (106355688 + 106355688) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 106355688 * (2 : ZMod 8508455051) ^ 106355688 := by rw [pow_add]
          _ = 2547146355 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 8508455051) ^ 425422752 = 942527102 := by
        calc
          (2 : ZMod 8508455051) ^ 425422752 = (2 : ZMod 8508455051) ^ (212711376 + 212711376) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 212711376 * (2 : ZMod 8508455051) ^ 212711376 := by rw [pow_add]
          _ = 942527102 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 8508455051) ^ 850845505 = 6041732166 := by
        calc
          (2 : ZMod 8508455051) ^ 850845505 = (2 : ZMod 8508455051) ^ (425422752 + 425422752 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 425422752 * (2 : ZMod 8508455051) ^ 425422752) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 6041732166 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 8508455051) ^ 1701691010 = 8380096710 := by
        calc
          (2 : ZMod 8508455051) ^ 1701691010 = (2 : ZMod 8508455051) ^ (850845505 + 850845505) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 850845505 * (2 : ZMod 8508455051) ^ 850845505 := by rw [pow_add]
          _ = 8380096710 := by rw [factor_1_29]; decide
      change (2 : ZMod 8508455051) ^ 1701691010 ≠ 1
      rw [factor_1_30]
      decide
    ·
      have factor_2_0 : (2 : ZMod 8508455051) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 8508455051) ^ 3 = 8 := by
        calc
          (2 : ZMod 8508455051) ^ 3 = (2 : ZMod 8508455051) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 1 * (2 : ZMod 8508455051) ^ 1) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 8508455051) ^ 6 = 64 := by
        calc
          (2 : ZMod 8508455051) ^ 6 = (2 : ZMod 8508455051) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 3 * (2 : ZMod 8508455051) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 8508455051) ^ 12 = 4096 := by
        calc
          (2 : ZMod 8508455051) ^ 12 = (2 : ZMod 8508455051) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 6 * (2 : ZMod 8508455051) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 8508455051) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 8508455051) ^ 24 = (2 : ZMod 8508455051) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 12 * (2 : ZMod 8508455051) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 8508455051) ^ 48 = 6775168525 := by
        calc
          (2 : ZMod 8508455051) ^ 48 = (2 : ZMod 8508455051) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 24 * (2 : ZMod 8508455051) ^ 24 := by rw [pow_add]
          _ = 6775168525 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 8508455051) ^ 97 = 7843431331 := by
        calc
          (2 : ZMod 8508455051) ^ 97 = (2 : ZMod 8508455051) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 48 * (2 : ZMod 8508455051) ^ 48) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 7843431331 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 8508455051) ^ 194 = 4480246022 := by
        calc
          (2 : ZMod 8508455051) ^ 194 = (2 : ZMod 8508455051) ^ (97 + 97) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 97 * (2 : ZMod 8508455051) ^ 97 := by rw [pow_add]
          _ = 4480246022 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 8508455051) ^ 388 = 7166872723 := by
        calc
          (2 : ZMod 8508455051) ^ 388 = (2 : ZMod 8508455051) ^ (194 + 194) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 194 * (2 : ZMod 8508455051) ^ 194 := by rw [pow_add]
          _ = 7166872723 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 8508455051) ^ 777 = 6565749049 := by
        calc
          (2 : ZMod 8508455051) ^ 777 = (2 : ZMod 8508455051) ^ (388 + 388 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 388 * (2 : ZMod 8508455051) ^ 388) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 6565749049 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 8508455051) ^ 1554 = 6107906888 := by
        calc
          (2 : ZMod 8508455051) ^ 1554 = (2 : ZMod 8508455051) ^ (777 + 777) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 777 * (2 : ZMod 8508455051) ^ 777 := by rw [pow_add]
          _ = 6107906888 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 8508455051) ^ 3109 = 2607903901 := by
        calc
          (2 : ZMod 8508455051) ^ 3109 = (2 : ZMod 8508455051) ^ (1554 + 1554 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 1554 * (2 : ZMod 8508455051) ^ 1554) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 2607903901 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 8508455051) ^ 6219 = 4360384242 := by
        calc
          (2 : ZMod 8508455051) ^ 6219 = (2 : ZMod 8508455051) ^ (3109 + 3109 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 3109 * (2 : ZMod 8508455051) ^ 3109) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 4360384242 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 8508455051) ^ 12439 = 3637638667 := by
        calc
          (2 : ZMod 8508455051) ^ 12439 = (2 : ZMod 8508455051) ^ (6219 + 6219 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 6219 * (2 : ZMod 8508455051) ^ 6219) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 3637638667 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 8508455051) ^ 24879 = 3453130267 := by
        calc
          (2 : ZMod 8508455051) ^ 24879 = (2 : ZMod 8508455051) ^ (12439 + 12439 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 12439 * (2 : ZMod 8508455051) ^ 12439) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 3453130267 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 8508455051) ^ 49759 = 6857980120 := by
        calc
          (2 : ZMod 8508455051) ^ 49759 = (2 : ZMod 8508455051) ^ (24879 + 24879 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 24879 * (2 : ZMod 8508455051) ^ 24879) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 6857980120 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 8508455051) ^ 99518 = 1207081599 := by
        calc
          (2 : ZMod 8508455051) ^ 99518 = (2 : ZMod 8508455051) ^ (49759 + 49759) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 49759 * (2 : ZMod 8508455051) ^ 49759 := by rw [pow_add]
          _ = 1207081599 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 8508455051) ^ 199037 = 2367131585 := by
        calc
          (2 : ZMod 8508455051) ^ 199037 = (2 : ZMod 8508455051) ^ (99518 + 99518 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 99518 * (2 : ZMod 8508455051) ^ 99518) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 2367131585 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 8508455051) ^ 398075 = 7375213913 := by
        calc
          (2 : ZMod 8508455051) ^ 398075 = (2 : ZMod 8508455051) ^ (199037 + 199037 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 199037 * (2 : ZMod 8508455051) ^ 199037) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 7375213913 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 8508455051) ^ 796150 = 3997239256 := by
        calc
          (2 : ZMod 8508455051) ^ 796150 = (2 : ZMod 8508455051) ^ (398075 + 398075) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 398075 * (2 : ZMod 8508455051) ^ 398075 := by rw [pow_add]
          _ = 3997239256 := by rw [factor_2_18]; decide
      change (2 : ZMod 8508455051) ^ 796150 ≠ 1
      rw [factor_2_19]
      decide
    ·
      have factor_3_0 : (2 : ZMod 8508455051) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 8508455051) ^ 2 = 4 := by
        calc
          (2 : ZMod 8508455051) ^ 2 = (2 : ZMod 8508455051) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 1 * (2 : ZMod 8508455051) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 8508455051) ^ 4 = 16 := by
        calc
          (2 : ZMod 8508455051) ^ 4 = (2 : ZMod 8508455051) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 2 * (2 : ZMod 8508455051) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 8508455051) ^ 8 = 256 := by
        calc
          (2 : ZMod 8508455051) ^ 8 = (2 : ZMod 8508455051) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 4 * (2 : ZMod 8508455051) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 8508455051) ^ 16 = 65536 := by
        calc
          (2 : ZMod 8508455051) ^ 16 = (2 : ZMod 8508455051) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 8 * (2 : ZMod 8508455051) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 8508455051) ^ 32 = 4294967296 := by
        calc
          (2 : ZMod 8508455051) ^ 32 = (2 : ZMod 8508455051) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 16 * (2 : ZMod 8508455051) ^ 16 := by rw [pow_add]
          _ = 4294967296 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 8508455051) ^ 65 = 7435235930 := by
        calc
          (2 : ZMod 8508455051) ^ 65 = (2 : ZMod 8508455051) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 32 * (2 : ZMod 8508455051) ^ 32) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 7435235930 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 8508455051) ^ 130 = 4770474399 := by
        calc
          (2 : ZMod 8508455051) ^ 130 = (2 : ZMod 8508455051) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 65 * (2 : ZMod 8508455051) ^ 65 := by rw [pow_add]
          _ = 4770474399 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 8508455051) ^ 260 = 5472772807 := by
        calc
          (2 : ZMod 8508455051) ^ 260 = (2 : ZMod 8508455051) ^ (130 + 130) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 130 * (2 : ZMod 8508455051) ^ 130 := by rw [pow_add]
          _ = 5472772807 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 8508455051) ^ 521 = 3289486161 := by
        calc
          (2 : ZMod 8508455051) ^ 521 = (2 : ZMod 8508455051) ^ (260 + 260 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 260 * (2 : ZMod 8508455051) ^ 260) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 3289486161 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 8508455051) ^ 1043 = 1768209036 := by
        calc
          (2 : ZMod 8508455051) ^ 1043 = (2 : ZMod 8508455051) ^ (521 + 521 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 521 * (2 : ZMod 8508455051) ^ 521) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 1768209036 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 8508455051) ^ 2087 = 6386858559 := by
        calc
          (2 : ZMod 8508455051) ^ 2087 = (2 : ZMod 8508455051) ^ (1043 + 1043 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 1043 * (2 : ZMod 8508455051) ^ 1043) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 6386858559 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 8508455051) ^ 4174 = 8191703582 := by
        calc
          (2 : ZMod 8508455051) ^ 4174 = (2 : ZMod 8508455051) ^ (2087 + 2087) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 2087 * (2 : ZMod 8508455051) ^ 2087 := by rw [pow_add]
          _ = 8191703582 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 8508455051) ^ 8349 = 7727284472 := by
        calc
          (2 : ZMod 8508455051) ^ 8349 = (2 : ZMod 8508455051) ^ (4174 + 4174 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 4174 * (2 : ZMod 8508455051) ^ 4174) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 7727284472 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 8508455051) ^ 16698 = 5172138815 := by
        calc
          (2 : ZMod 8508455051) ^ 16698 = (2 : ZMod 8508455051) ^ (8349 + 8349) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 8349 * (2 : ZMod 8508455051) ^ 8349 := by rw [pow_add]
          _ = 5172138815 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 8508455051) ^ 33396 = 288988386 := by
        calc
          (2 : ZMod 8508455051) ^ 33396 = (2 : ZMod 8508455051) ^ (16698 + 16698) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 16698 * (2 : ZMod 8508455051) ^ 16698 := by rw [pow_add]
          _ = 288988386 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 8508455051) ^ 66793 = 3784279449 := by
        calc
          (2 : ZMod 8508455051) ^ 66793 = (2 : ZMod 8508455051) ^ (33396 + 33396 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 33396 * (2 : ZMod 8508455051) ^ 33396) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 3784279449 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 8508455051) ^ 133587 = 5461406482 := by
        calc
          (2 : ZMod 8508455051) ^ 133587 = (2 : ZMod 8508455051) ^ (66793 + 66793 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 66793 * (2 : ZMod 8508455051) ^ 66793) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 5461406482 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 8508455051) ^ 267175 = 7223855543 := by
        calc
          (2 : ZMod 8508455051) ^ 267175 = (2 : ZMod 8508455051) ^ (133587 + 133587 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = ((2 : ZMod 8508455051) ^ 133587 * (2 : ZMod 8508455051) ^ 133587) * (2 : ZMod 8508455051) := by rw [pow_succ, pow_add]
          _ = 7223855543 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 8508455051) ^ 534350 = 4158700743 := by
        calc
          (2 : ZMod 8508455051) ^ 534350 = (2 : ZMod 8508455051) ^ (267175 + 267175) :=
            congrArg (fun n : ℕ => (2 : ZMod 8508455051) ^ n) (by norm_num)
          _ = (2 : ZMod 8508455051) ^ 267175 * (2 : ZMod 8508455051) ^ 267175 := by rw [pow_add]
          _ = 4158700743 := by rw [factor_3_18]; decide
      change (2 : ZMod 8508455051) ^ 534350 ≠ 1
      rw [factor_3_19]
      decide

#print axioms prime_lucas_8508455051

end TotientTailPeriodKiller
end Erdos249257
