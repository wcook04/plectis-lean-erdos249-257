import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_23486071439 : Nat.Prime 23486071439 := by
  apply lucas_primality 23486071439 (29 : ZMod 23486071439)
  ·
      have fermat_0 : (29 : ZMod 23486071439) ^ 1 = 29 := by norm_num
      have fermat_1 : (29 : ZMod 23486071439) ^ 2 = 841 := by
        calc
          (29 : ZMod 23486071439) ^ 2 = (29 : ZMod 23486071439) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 1 * (29 : ZMod 23486071439) ^ 1 := by rw [pow_add]
          _ = 841 := by rw [fermat_0]; decide
      have fermat_2 : (29 : ZMod 23486071439) ^ 5 = 20511149 := by
        calc
          (29 : ZMod 23486071439) ^ 5 = (29 : ZMod 23486071439) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 2 * (29 : ZMod 23486071439) ^ 2) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 20511149 := by rw [fermat_1]; decide
      have fermat_3 : (29 : ZMod 23486071439) ^ 10 = 1235613394 := by
        calc
          (29 : ZMod 23486071439) ^ 10 = (29 : ZMod 23486071439) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 5 * (29 : ZMod 23486071439) ^ 5 := by rw [pow_add]
          _ = 1235613394 := by rw [fermat_2]; decide
      have fermat_4 : (29 : ZMod 23486071439) ^ 21 = 17342257333 := by
        calc
          (29 : ZMod 23486071439) ^ 21 = (29 : ZMod 23486071439) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 10 * (29 : ZMod 23486071439) ^ 10) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 17342257333 := by rw [fermat_3]; decide
      have fermat_5 : (29 : ZMod 23486071439) ^ 43 = 19713905349 := by
        calc
          (29 : ZMod 23486071439) ^ 43 = (29 : ZMod 23486071439) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 21 * (29 : ZMod 23486071439) ^ 21) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 19713905349 := by rw [fermat_4]; decide
      have fermat_6 : (29 : ZMod 23486071439) ^ 87 = 19640749991 := by
        calc
          (29 : ZMod 23486071439) ^ 87 = (29 : ZMod 23486071439) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 43 * (29 : ZMod 23486071439) ^ 43) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 19640749991 := by rw [fermat_5]; decide
      have fermat_7 : (29 : ZMod 23486071439) ^ 174 = 9640993382 := by
        calc
          (29 : ZMod 23486071439) ^ 174 = (29 : ZMod 23486071439) ^ (87 + 87) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 87 * (29 : ZMod 23486071439) ^ 87 := by rw [pow_add]
          _ = 9640993382 := by rw [fermat_6]; decide
      have fermat_8 : (29 : ZMod 23486071439) ^ 349 = 11788400628 := by
        calc
          (29 : ZMod 23486071439) ^ 349 = (29 : ZMod 23486071439) ^ (174 + 174 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 174 * (29 : ZMod 23486071439) ^ 174) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 11788400628 := by rw [fermat_7]; decide
      have fermat_9 : (29 : ZMod 23486071439) ^ 699 = 498562390 := by
        calc
          (29 : ZMod 23486071439) ^ 699 = (29 : ZMod 23486071439) ^ (349 + 349 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 349 * (29 : ZMod 23486071439) ^ 349) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 498562390 := by rw [fermat_8]; decide
      have fermat_10 : (29 : ZMod 23486071439) ^ 1399 = 8241388730 := by
        calc
          (29 : ZMod 23486071439) ^ 1399 = (29 : ZMod 23486071439) ^ (699 + 699 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 699 * (29 : ZMod 23486071439) ^ 699) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 8241388730 := by rw [fermat_9]; decide
      have fermat_11 : (29 : ZMod 23486071439) ^ 2799 = 7862503630 := by
        calc
          (29 : ZMod 23486071439) ^ 2799 = (29 : ZMod 23486071439) ^ (1399 + 1399 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 1399 * (29 : ZMod 23486071439) ^ 1399) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 7862503630 := by rw [fermat_10]; decide
      have fermat_12 : (29 : ZMod 23486071439) ^ 5599 = 10506687343 := by
        calc
          (29 : ZMod 23486071439) ^ 5599 = (29 : ZMod 23486071439) ^ (2799 + 2799 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 2799 * (29 : ZMod 23486071439) ^ 2799) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 10506687343 := by rw [fermat_11]; decide
      have fermat_13 : (29 : ZMod 23486071439) ^ 11199 = 4651203003 := by
        calc
          (29 : ZMod 23486071439) ^ 11199 = (29 : ZMod 23486071439) ^ (5599 + 5599 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 5599 * (29 : ZMod 23486071439) ^ 5599) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 4651203003 := by rw [fermat_12]; decide
      have fermat_14 : (29 : ZMod 23486071439) ^ 22398 = 18880520972 := by
        calc
          (29 : ZMod 23486071439) ^ 22398 = (29 : ZMod 23486071439) ^ (11199 + 11199) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 11199 * (29 : ZMod 23486071439) ^ 11199 := by rw [pow_add]
          _ = 18880520972 := by rw [fermat_13]; decide
      have fermat_15 : (29 : ZMod 23486071439) ^ 44796 = 2192652213 := by
        calc
          (29 : ZMod 23486071439) ^ 44796 = (29 : ZMod 23486071439) ^ (22398 + 22398) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 22398 * (29 : ZMod 23486071439) ^ 22398 := by rw [pow_add]
          _ = 2192652213 := by rw [fermat_14]; decide
      have fermat_16 : (29 : ZMod 23486071439) ^ 89592 = 4682584767 := by
        calc
          (29 : ZMod 23486071439) ^ 89592 = (29 : ZMod 23486071439) ^ (44796 + 44796) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 44796 * (29 : ZMod 23486071439) ^ 44796 := by rw [pow_add]
          _ = 4682584767 := by rw [fermat_15]; decide
      have fermat_17 : (29 : ZMod 23486071439) ^ 179184 = 23432542610 := by
        calc
          (29 : ZMod 23486071439) ^ 179184 = (29 : ZMod 23486071439) ^ (89592 + 89592) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 89592 * (29 : ZMod 23486071439) ^ 89592 := by rw [pow_add]
          _ = 23432542610 := by rw [fermat_16]; decide
      have fermat_18 : (29 : ZMod 23486071439) ^ 358369 = 23323043551 := by
        calc
          (29 : ZMod 23486071439) ^ 358369 = (29 : ZMod 23486071439) ^ (179184 + 179184 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 179184 * (29 : ZMod 23486071439) ^ 179184) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 23323043551 := by rw [fermat_17]; decide
      have fermat_19 : (29 : ZMod 23486071439) ^ 716738 = 9063581877 := by
        calc
          (29 : ZMod 23486071439) ^ 716738 = (29 : ZMod 23486071439) ^ (358369 + 358369) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 358369 * (29 : ZMod 23486071439) ^ 358369 := by rw [pow_add]
          _ = 9063581877 := by rw [fermat_18]; decide
      have fermat_20 : (29 : ZMod 23486071439) ^ 1433476 = 9589829975 := by
        calc
          (29 : ZMod 23486071439) ^ 1433476 = (29 : ZMod 23486071439) ^ (716738 + 716738) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 716738 * (29 : ZMod 23486071439) ^ 716738 := by rw [pow_add]
          _ = 9589829975 := by rw [fermat_19]; decide
      have fermat_21 : (29 : ZMod 23486071439) ^ 2866952 = 19135295851 := by
        calc
          (29 : ZMod 23486071439) ^ 2866952 = (29 : ZMod 23486071439) ^ (1433476 + 1433476) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 1433476 * (29 : ZMod 23486071439) ^ 1433476 := by rw [pow_add]
          _ = 19135295851 := by rw [fermat_20]; decide
      have fermat_22 : (29 : ZMod 23486071439) ^ 5733904 = 20720836174 := by
        calc
          (29 : ZMod 23486071439) ^ 5733904 = (29 : ZMod 23486071439) ^ (2866952 + 2866952) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 2866952 * (29 : ZMod 23486071439) ^ 2866952 := by rw [pow_add]
          _ = 20720836174 := by rw [fermat_21]; decide
      have fermat_23 : (29 : ZMod 23486071439) ^ 11467808 = 4226102324 := by
        calc
          (29 : ZMod 23486071439) ^ 11467808 = (29 : ZMod 23486071439) ^ (5733904 + 5733904) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 5733904 * (29 : ZMod 23486071439) ^ 5733904 := by rw [pow_add]
          _ = 4226102324 := by rw [fermat_22]; decide
      have fermat_24 : (29 : ZMod 23486071439) ^ 22935616 = 8114955420 := by
        calc
          (29 : ZMod 23486071439) ^ 22935616 = (29 : ZMod 23486071439) ^ (11467808 + 11467808) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 11467808 * (29 : ZMod 23486071439) ^ 11467808 := by rw [pow_add]
          _ = 8114955420 := by rw [fermat_23]; decide
      have fermat_25 : (29 : ZMod 23486071439) ^ 45871233 = 19186014835 := by
        calc
          (29 : ZMod 23486071439) ^ 45871233 = (29 : ZMod 23486071439) ^ (22935616 + 22935616 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 22935616 * (29 : ZMod 23486071439) ^ 22935616) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 19186014835 := by rw [fermat_24]; decide
      have fermat_26 : (29 : ZMod 23486071439) ^ 91742466 = 9501141715 := by
        calc
          (29 : ZMod 23486071439) ^ 91742466 = (29 : ZMod 23486071439) ^ (45871233 + 45871233) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 45871233 * (29 : ZMod 23486071439) ^ 45871233 := by rw [pow_add]
          _ = 9501141715 := by rw [fermat_25]; decide
      have fermat_27 : (29 : ZMod 23486071439) ^ 183484933 = 7678529709 := by
        calc
          (29 : ZMod 23486071439) ^ 183484933 = (29 : ZMod 23486071439) ^ (91742466 + 91742466 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 91742466 * (29 : ZMod 23486071439) ^ 91742466) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 7678529709 := by rw [fermat_26]; decide
      have fermat_28 : (29 : ZMod 23486071439) ^ 366969866 = 2707710983 := by
        calc
          (29 : ZMod 23486071439) ^ 366969866 = (29 : ZMod 23486071439) ^ (183484933 + 183484933) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 183484933 * (29 : ZMod 23486071439) ^ 183484933 := by rw [pow_add]
          _ = 2707710983 := by rw [fermat_27]; decide
      have fermat_29 : (29 : ZMod 23486071439) ^ 733939732 = 12586530416 := by
        calc
          (29 : ZMod 23486071439) ^ 733939732 = (29 : ZMod 23486071439) ^ (366969866 + 366969866) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 366969866 * (29 : ZMod 23486071439) ^ 366969866 := by rw [pow_add]
          _ = 12586530416 := by rw [fermat_28]; decide
      have fermat_30 : (29 : ZMod 23486071439) ^ 1467879464 = 18493509212 := by
        calc
          (29 : ZMod 23486071439) ^ 1467879464 = (29 : ZMod 23486071439) ^ (733939732 + 733939732) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 733939732 * (29 : ZMod 23486071439) ^ 733939732 := by rw [pow_add]
          _ = 18493509212 := by rw [fermat_29]; decide
      have fermat_31 : (29 : ZMod 23486071439) ^ 2935758929 = 1083931337 := by
        calc
          (29 : ZMod 23486071439) ^ 2935758929 = (29 : ZMod 23486071439) ^ (1467879464 + 1467879464 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 1467879464 * (29 : ZMod 23486071439) ^ 1467879464) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 1083931337 := by rw [fermat_30]; decide
      have fermat_32 : (29 : ZMod 23486071439) ^ 5871517859 = 11631990215 := by
        calc
          (29 : ZMod 23486071439) ^ 5871517859 = (29 : ZMod 23486071439) ^ (2935758929 + 2935758929 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 2935758929 * (29 : ZMod 23486071439) ^ 2935758929) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 11631990215 := by rw [fermat_31]; decide
      have fermat_33 : (29 : ZMod 23486071439) ^ 11743035719 = 23486071438 := by
        calc
          (29 : ZMod 23486071439) ^ 11743035719 = (29 : ZMod 23486071439) ^ (5871517859 + 5871517859 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 5871517859 * (29 : ZMod 23486071439) ^ 5871517859) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 23486071438 := by rw [fermat_32]; decide
      have fermat_34 : (29 : ZMod 23486071439) ^ 23486071438 = 1 := by
        calc
          (29 : ZMod 23486071439) ^ 23486071438 = (29 : ZMod 23486071439) ^ (11743035719 + 11743035719) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 11743035719 * (29 : ZMod 23486071439) ^ 11743035719 := by rw [pow_add]
          _ = 1 := by rw [fermat_33]; decide
      simpa using fermat_34
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (73, 1), (223, 1), (42433, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (73, 1), (223, 1), (42433, 1)] : List FactorBlock).map factorBlockValue).prod = 23486071439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (29 : ZMod 23486071439) ^ 1 = 29 := by norm_num
      have factor_0_1 : (29 : ZMod 23486071439) ^ 2 = 841 := by
        calc
          (29 : ZMod 23486071439) ^ 2 = (29 : ZMod 23486071439) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 1 * (29 : ZMod 23486071439) ^ 1 := by rw [pow_add]
          _ = 841 := by rw [factor_0_0]; decide
      have factor_0_2 : (29 : ZMod 23486071439) ^ 5 = 20511149 := by
        calc
          (29 : ZMod 23486071439) ^ 5 = (29 : ZMod 23486071439) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 2 * (29 : ZMod 23486071439) ^ 2) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 20511149 := by rw [factor_0_1]; decide
      have factor_0_3 : (29 : ZMod 23486071439) ^ 10 = 1235613394 := by
        calc
          (29 : ZMod 23486071439) ^ 10 = (29 : ZMod 23486071439) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 5 * (29 : ZMod 23486071439) ^ 5 := by rw [pow_add]
          _ = 1235613394 := by rw [factor_0_2]; decide
      have factor_0_4 : (29 : ZMod 23486071439) ^ 21 = 17342257333 := by
        calc
          (29 : ZMod 23486071439) ^ 21 = (29 : ZMod 23486071439) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 10 * (29 : ZMod 23486071439) ^ 10) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 17342257333 := by rw [factor_0_3]; decide
      have factor_0_5 : (29 : ZMod 23486071439) ^ 43 = 19713905349 := by
        calc
          (29 : ZMod 23486071439) ^ 43 = (29 : ZMod 23486071439) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 21 * (29 : ZMod 23486071439) ^ 21) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 19713905349 := by rw [factor_0_4]; decide
      have factor_0_6 : (29 : ZMod 23486071439) ^ 87 = 19640749991 := by
        calc
          (29 : ZMod 23486071439) ^ 87 = (29 : ZMod 23486071439) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 43 * (29 : ZMod 23486071439) ^ 43) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 19640749991 := by rw [factor_0_5]; decide
      have factor_0_7 : (29 : ZMod 23486071439) ^ 174 = 9640993382 := by
        calc
          (29 : ZMod 23486071439) ^ 174 = (29 : ZMod 23486071439) ^ (87 + 87) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 87 * (29 : ZMod 23486071439) ^ 87 := by rw [pow_add]
          _ = 9640993382 := by rw [factor_0_6]; decide
      have factor_0_8 : (29 : ZMod 23486071439) ^ 349 = 11788400628 := by
        calc
          (29 : ZMod 23486071439) ^ 349 = (29 : ZMod 23486071439) ^ (174 + 174 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 174 * (29 : ZMod 23486071439) ^ 174) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 11788400628 := by rw [factor_0_7]; decide
      have factor_0_9 : (29 : ZMod 23486071439) ^ 699 = 498562390 := by
        calc
          (29 : ZMod 23486071439) ^ 699 = (29 : ZMod 23486071439) ^ (349 + 349 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 349 * (29 : ZMod 23486071439) ^ 349) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 498562390 := by rw [factor_0_8]; decide
      have factor_0_10 : (29 : ZMod 23486071439) ^ 1399 = 8241388730 := by
        calc
          (29 : ZMod 23486071439) ^ 1399 = (29 : ZMod 23486071439) ^ (699 + 699 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 699 * (29 : ZMod 23486071439) ^ 699) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 8241388730 := by rw [factor_0_9]; decide
      have factor_0_11 : (29 : ZMod 23486071439) ^ 2799 = 7862503630 := by
        calc
          (29 : ZMod 23486071439) ^ 2799 = (29 : ZMod 23486071439) ^ (1399 + 1399 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 1399 * (29 : ZMod 23486071439) ^ 1399) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 7862503630 := by rw [factor_0_10]; decide
      have factor_0_12 : (29 : ZMod 23486071439) ^ 5599 = 10506687343 := by
        calc
          (29 : ZMod 23486071439) ^ 5599 = (29 : ZMod 23486071439) ^ (2799 + 2799 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 2799 * (29 : ZMod 23486071439) ^ 2799) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 10506687343 := by rw [factor_0_11]; decide
      have factor_0_13 : (29 : ZMod 23486071439) ^ 11199 = 4651203003 := by
        calc
          (29 : ZMod 23486071439) ^ 11199 = (29 : ZMod 23486071439) ^ (5599 + 5599 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 5599 * (29 : ZMod 23486071439) ^ 5599) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 4651203003 := by rw [factor_0_12]; decide
      have factor_0_14 : (29 : ZMod 23486071439) ^ 22398 = 18880520972 := by
        calc
          (29 : ZMod 23486071439) ^ 22398 = (29 : ZMod 23486071439) ^ (11199 + 11199) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 11199 * (29 : ZMod 23486071439) ^ 11199 := by rw [pow_add]
          _ = 18880520972 := by rw [factor_0_13]; decide
      have factor_0_15 : (29 : ZMod 23486071439) ^ 44796 = 2192652213 := by
        calc
          (29 : ZMod 23486071439) ^ 44796 = (29 : ZMod 23486071439) ^ (22398 + 22398) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 22398 * (29 : ZMod 23486071439) ^ 22398 := by rw [pow_add]
          _ = 2192652213 := by rw [factor_0_14]; decide
      have factor_0_16 : (29 : ZMod 23486071439) ^ 89592 = 4682584767 := by
        calc
          (29 : ZMod 23486071439) ^ 89592 = (29 : ZMod 23486071439) ^ (44796 + 44796) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 44796 * (29 : ZMod 23486071439) ^ 44796 := by rw [pow_add]
          _ = 4682584767 := by rw [factor_0_15]; decide
      have factor_0_17 : (29 : ZMod 23486071439) ^ 179184 = 23432542610 := by
        calc
          (29 : ZMod 23486071439) ^ 179184 = (29 : ZMod 23486071439) ^ (89592 + 89592) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 89592 * (29 : ZMod 23486071439) ^ 89592 := by rw [pow_add]
          _ = 23432542610 := by rw [factor_0_16]; decide
      have factor_0_18 : (29 : ZMod 23486071439) ^ 358369 = 23323043551 := by
        calc
          (29 : ZMod 23486071439) ^ 358369 = (29 : ZMod 23486071439) ^ (179184 + 179184 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 179184 * (29 : ZMod 23486071439) ^ 179184) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 23323043551 := by rw [factor_0_17]; decide
      have factor_0_19 : (29 : ZMod 23486071439) ^ 716738 = 9063581877 := by
        calc
          (29 : ZMod 23486071439) ^ 716738 = (29 : ZMod 23486071439) ^ (358369 + 358369) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 358369 * (29 : ZMod 23486071439) ^ 358369 := by rw [pow_add]
          _ = 9063581877 := by rw [factor_0_18]; decide
      have factor_0_20 : (29 : ZMod 23486071439) ^ 1433476 = 9589829975 := by
        calc
          (29 : ZMod 23486071439) ^ 1433476 = (29 : ZMod 23486071439) ^ (716738 + 716738) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 716738 * (29 : ZMod 23486071439) ^ 716738 := by rw [pow_add]
          _ = 9589829975 := by rw [factor_0_19]; decide
      have factor_0_21 : (29 : ZMod 23486071439) ^ 2866952 = 19135295851 := by
        calc
          (29 : ZMod 23486071439) ^ 2866952 = (29 : ZMod 23486071439) ^ (1433476 + 1433476) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 1433476 * (29 : ZMod 23486071439) ^ 1433476 := by rw [pow_add]
          _ = 19135295851 := by rw [factor_0_20]; decide
      have factor_0_22 : (29 : ZMod 23486071439) ^ 5733904 = 20720836174 := by
        calc
          (29 : ZMod 23486071439) ^ 5733904 = (29 : ZMod 23486071439) ^ (2866952 + 2866952) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 2866952 * (29 : ZMod 23486071439) ^ 2866952 := by rw [pow_add]
          _ = 20720836174 := by rw [factor_0_21]; decide
      have factor_0_23 : (29 : ZMod 23486071439) ^ 11467808 = 4226102324 := by
        calc
          (29 : ZMod 23486071439) ^ 11467808 = (29 : ZMod 23486071439) ^ (5733904 + 5733904) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 5733904 * (29 : ZMod 23486071439) ^ 5733904 := by rw [pow_add]
          _ = 4226102324 := by rw [factor_0_22]; decide
      have factor_0_24 : (29 : ZMod 23486071439) ^ 22935616 = 8114955420 := by
        calc
          (29 : ZMod 23486071439) ^ 22935616 = (29 : ZMod 23486071439) ^ (11467808 + 11467808) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 11467808 * (29 : ZMod 23486071439) ^ 11467808 := by rw [pow_add]
          _ = 8114955420 := by rw [factor_0_23]; decide
      have factor_0_25 : (29 : ZMod 23486071439) ^ 45871233 = 19186014835 := by
        calc
          (29 : ZMod 23486071439) ^ 45871233 = (29 : ZMod 23486071439) ^ (22935616 + 22935616 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 22935616 * (29 : ZMod 23486071439) ^ 22935616) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 19186014835 := by rw [factor_0_24]; decide
      have factor_0_26 : (29 : ZMod 23486071439) ^ 91742466 = 9501141715 := by
        calc
          (29 : ZMod 23486071439) ^ 91742466 = (29 : ZMod 23486071439) ^ (45871233 + 45871233) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 45871233 * (29 : ZMod 23486071439) ^ 45871233 := by rw [pow_add]
          _ = 9501141715 := by rw [factor_0_25]; decide
      have factor_0_27 : (29 : ZMod 23486071439) ^ 183484933 = 7678529709 := by
        calc
          (29 : ZMod 23486071439) ^ 183484933 = (29 : ZMod 23486071439) ^ (91742466 + 91742466 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 91742466 * (29 : ZMod 23486071439) ^ 91742466) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 7678529709 := by rw [factor_0_26]; decide
      have factor_0_28 : (29 : ZMod 23486071439) ^ 366969866 = 2707710983 := by
        calc
          (29 : ZMod 23486071439) ^ 366969866 = (29 : ZMod 23486071439) ^ (183484933 + 183484933) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 183484933 * (29 : ZMod 23486071439) ^ 183484933 := by rw [pow_add]
          _ = 2707710983 := by rw [factor_0_27]; decide
      have factor_0_29 : (29 : ZMod 23486071439) ^ 733939732 = 12586530416 := by
        calc
          (29 : ZMod 23486071439) ^ 733939732 = (29 : ZMod 23486071439) ^ (366969866 + 366969866) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 366969866 * (29 : ZMod 23486071439) ^ 366969866 := by rw [pow_add]
          _ = 12586530416 := by rw [factor_0_28]; decide
      have factor_0_30 : (29 : ZMod 23486071439) ^ 1467879464 = 18493509212 := by
        calc
          (29 : ZMod 23486071439) ^ 1467879464 = (29 : ZMod 23486071439) ^ (733939732 + 733939732) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 733939732 * (29 : ZMod 23486071439) ^ 733939732 := by rw [pow_add]
          _ = 18493509212 := by rw [factor_0_29]; decide
      have factor_0_31 : (29 : ZMod 23486071439) ^ 2935758929 = 1083931337 := by
        calc
          (29 : ZMod 23486071439) ^ 2935758929 = (29 : ZMod 23486071439) ^ (1467879464 + 1467879464 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 1467879464 * (29 : ZMod 23486071439) ^ 1467879464) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 1083931337 := by rw [factor_0_30]; decide
      have factor_0_32 : (29 : ZMod 23486071439) ^ 5871517859 = 11631990215 := by
        calc
          (29 : ZMod 23486071439) ^ 5871517859 = (29 : ZMod 23486071439) ^ (2935758929 + 2935758929 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 2935758929 * (29 : ZMod 23486071439) ^ 2935758929) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 11631990215 := by rw [factor_0_31]; decide
      have factor_0_33 : (29 : ZMod 23486071439) ^ 11743035719 = 23486071438 := by
        calc
          (29 : ZMod 23486071439) ^ 11743035719 = (29 : ZMod 23486071439) ^ (5871517859 + 5871517859 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 5871517859 * (29 : ZMod 23486071439) ^ 5871517859) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 23486071438 := by rw [factor_0_32]; decide
      change (29 : ZMod 23486071439) ^ 11743035719 ≠ 1
      rw [factor_0_33]
      decide
    ·
      have factor_1_0 : (29 : ZMod 23486071439) ^ 1 = 29 := by norm_num
      have factor_1_1 : (29 : ZMod 23486071439) ^ 2 = 841 := by
        calc
          (29 : ZMod 23486071439) ^ 2 = (29 : ZMod 23486071439) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 1 * (29 : ZMod 23486071439) ^ 1 := by rw [pow_add]
          _ = 841 := by rw [factor_1_0]; decide
      have factor_1_2 : (29 : ZMod 23486071439) ^ 5 = 20511149 := by
        calc
          (29 : ZMod 23486071439) ^ 5 = (29 : ZMod 23486071439) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 2 * (29 : ZMod 23486071439) ^ 2) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 20511149 := by rw [factor_1_1]; decide
      have factor_1_3 : (29 : ZMod 23486071439) ^ 10 = 1235613394 := by
        calc
          (29 : ZMod 23486071439) ^ 10 = (29 : ZMod 23486071439) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 5 * (29 : ZMod 23486071439) ^ 5 := by rw [pow_add]
          _ = 1235613394 := by rw [factor_1_2]; decide
      have factor_1_4 : (29 : ZMod 23486071439) ^ 20 = 14365705924 := by
        calc
          (29 : ZMod 23486071439) ^ 20 = (29 : ZMod 23486071439) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 10 * (29 : ZMod 23486071439) ^ 10 := by rw [pow_add]
          _ = 14365705924 := by rw [factor_1_3]; decide
      have factor_1_5 : (29 : ZMod 23486071439) ^ 41 = 21107845234 := by
        calc
          (29 : ZMod 23486071439) ^ 41 = (29 : ZMod 23486071439) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 20 * (29 : ZMod 23486071439) ^ 20) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 21107845234 := by rw [factor_1_4]; decide
      have factor_1_6 : (29 : ZMod 23486071439) ^ 82 = 4394416705 := by
        calc
          (29 : ZMod 23486071439) ^ 82 = (29 : ZMod 23486071439) ^ (41 + 41) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 41 * (29 : ZMod 23486071439) ^ 41 := by rw [pow_add]
          _ = 4394416705 := by rw [factor_1_5]; decide
      have factor_1_7 : (29 : ZMod 23486071439) ^ 164 = 4663396871 := by
        calc
          (29 : ZMod 23486071439) ^ 164 = (29 : ZMod 23486071439) ^ (82 + 82) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 82 * (29 : ZMod 23486071439) ^ 82 := by rw [pow_add]
          _ = 4663396871 := by rw [factor_1_6]; decide
      have factor_1_8 : (29 : ZMod 23486071439) ^ 329 = 4806982173 := by
        calc
          (29 : ZMod 23486071439) ^ 329 = (29 : ZMod 23486071439) ^ (164 + 164 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 164 * (29 : ZMod 23486071439) ^ 164) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 4806982173 := by rw [factor_1_7]; decide
      have factor_1_9 : (29 : ZMod 23486071439) ^ 658 = 14880230247 := by
        calc
          (29 : ZMod 23486071439) ^ 658 = (29 : ZMod 23486071439) ^ (329 + 329) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 329 * (29 : ZMod 23486071439) ^ 329 := by rw [pow_add]
          _ = 14880230247 := by rw [factor_1_8]; decide
      have factor_1_10 : (29 : ZMod 23486071439) ^ 1317 = 16475090871 := by
        calc
          (29 : ZMod 23486071439) ^ 1317 = (29 : ZMod 23486071439) ^ (658 + 658 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 658 * (29 : ZMod 23486071439) ^ 658) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 16475090871 := by rw [factor_1_9]; decide
      have factor_1_11 : (29 : ZMod 23486071439) ^ 2635 = 12018655518 := by
        calc
          (29 : ZMod 23486071439) ^ 2635 = (29 : ZMod 23486071439) ^ (1317 + 1317 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 1317 * (29 : ZMod 23486071439) ^ 1317) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 12018655518 := by rw [factor_1_10]; decide
      have factor_1_12 : (29 : ZMod 23486071439) ^ 5270 = 17461538426 := by
        calc
          (29 : ZMod 23486071439) ^ 5270 = (29 : ZMod 23486071439) ^ (2635 + 2635) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 2635 * (29 : ZMod 23486071439) ^ 2635 := by rw [pow_add]
          _ = 17461538426 := by rw [factor_1_11]; decide
      have factor_1_13 : (29 : ZMod 23486071439) ^ 10540 = 9940354046 := by
        calc
          (29 : ZMod 23486071439) ^ 10540 = (29 : ZMod 23486071439) ^ (5270 + 5270) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 5270 * (29 : ZMod 23486071439) ^ 5270 := by rw [pow_add]
          _ = 9940354046 := by rw [factor_1_12]; decide
      have factor_1_14 : (29 : ZMod 23486071439) ^ 21080 = 2677752888 := by
        calc
          (29 : ZMod 23486071439) ^ 21080 = (29 : ZMod 23486071439) ^ (10540 + 10540) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 10540 * (29 : ZMod 23486071439) ^ 10540 := by rw [pow_add]
          _ = 2677752888 := by rw [factor_1_13]; decide
      have factor_1_15 : (29 : ZMod 23486071439) ^ 42161 = 14213479866 := by
        calc
          (29 : ZMod 23486071439) ^ 42161 = (29 : ZMod 23486071439) ^ (21080 + 21080 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 21080 * (29 : ZMod 23486071439) ^ 21080) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 14213479866 := by rw [factor_1_14]; decide
      have factor_1_16 : (29 : ZMod 23486071439) ^ 84322 = 4937661082 := by
        calc
          (29 : ZMod 23486071439) ^ 84322 = (29 : ZMod 23486071439) ^ (42161 + 42161) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 42161 * (29 : ZMod 23486071439) ^ 42161 := by rw [pow_add]
          _ = 4937661082 := by rw [factor_1_15]; decide
      have factor_1_17 : (29 : ZMod 23486071439) ^ 168644 = 14317399876 := by
        calc
          (29 : ZMod 23486071439) ^ 168644 = (29 : ZMod 23486071439) ^ (84322 + 84322) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 84322 * (29 : ZMod 23486071439) ^ 84322 := by rw [pow_add]
          _ = 14317399876 := by rw [factor_1_16]; decide
      have factor_1_18 : (29 : ZMod 23486071439) ^ 337288 = 1336788771 := by
        calc
          (29 : ZMod 23486071439) ^ 337288 = (29 : ZMod 23486071439) ^ (168644 + 168644) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 168644 * (29 : ZMod 23486071439) ^ 168644 := by rw [pow_add]
          _ = 1336788771 := by rw [factor_1_17]; decide
      have factor_1_19 : (29 : ZMod 23486071439) ^ 674576 = 7253203071 := by
        calc
          (29 : ZMod 23486071439) ^ 674576 = (29 : ZMod 23486071439) ^ (337288 + 337288) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 337288 * (29 : ZMod 23486071439) ^ 337288 := by rw [pow_add]
          _ = 7253203071 := by rw [factor_1_18]; decide
      have factor_1_20 : (29 : ZMod 23486071439) ^ 1349153 = 20059107289 := by
        calc
          (29 : ZMod 23486071439) ^ 1349153 = (29 : ZMod 23486071439) ^ (674576 + 674576 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 674576 * (29 : ZMod 23486071439) ^ 674576) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 20059107289 := by rw [factor_1_19]; decide
      have factor_1_21 : (29 : ZMod 23486071439) ^ 2698307 = 12862605927 := by
        calc
          (29 : ZMod 23486071439) ^ 2698307 = (29 : ZMod 23486071439) ^ (1349153 + 1349153 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 1349153 * (29 : ZMod 23486071439) ^ 1349153) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 12862605927 := by rw [factor_1_20]; decide
      have factor_1_22 : (29 : ZMod 23486071439) ^ 5396615 = 5283357698 := by
        calc
          (29 : ZMod 23486071439) ^ 5396615 = (29 : ZMod 23486071439) ^ (2698307 + 2698307 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 2698307 * (29 : ZMod 23486071439) ^ 2698307) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 5283357698 := by rw [factor_1_21]; decide
      have factor_1_23 : (29 : ZMod 23486071439) ^ 10793231 = 1492397979 := by
        calc
          (29 : ZMod 23486071439) ^ 10793231 = (29 : ZMod 23486071439) ^ (5396615 + 5396615 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 5396615 * (29 : ZMod 23486071439) ^ 5396615) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 1492397979 := by rw [factor_1_22]; decide
      have factor_1_24 : (29 : ZMod 23486071439) ^ 21586462 = 3735384438 := by
        calc
          (29 : ZMod 23486071439) ^ 21586462 = (29 : ZMod 23486071439) ^ (10793231 + 10793231) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 10793231 * (29 : ZMod 23486071439) ^ 10793231 := by rw [pow_add]
          _ = 3735384438 := by rw [factor_1_23]; decide
      have factor_1_25 : (29 : ZMod 23486071439) ^ 43172925 = 8955532305 := by
        calc
          (29 : ZMod 23486071439) ^ 43172925 = (29 : ZMod 23486071439) ^ (21586462 + 21586462 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 21586462 * (29 : ZMod 23486071439) ^ 21586462) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 8955532305 := by rw [factor_1_24]; decide
      have factor_1_26 : (29 : ZMod 23486071439) ^ 86345850 = 14581897398 := by
        calc
          (29 : ZMod 23486071439) ^ 86345850 = (29 : ZMod 23486071439) ^ (43172925 + 43172925) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 43172925 * (29 : ZMod 23486071439) ^ 43172925 := by rw [pow_add]
          _ = 14581897398 := by rw [factor_1_25]; decide
      have factor_1_27 : (29 : ZMod 23486071439) ^ 172691701 = 23242422205 := by
        calc
          (29 : ZMod 23486071439) ^ 172691701 = (29 : ZMod 23486071439) ^ (86345850 + 86345850 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 86345850 * (29 : ZMod 23486071439) ^ 86345850) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 23242422205 := by rw [factor_1_26]; decide
      have factor_1_28 : (29 : ZMod 23486071439) ^ 345383403 = 3470377444 := by
        calc
          (29 : ZMod 23486071439) ^ 345383403 = (29 : ZMod 23486071439) ^ (172691701 + 172691701 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 172691701 * (29 : ZMod 23486071439) ^ 172691701) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 3470377444 := by rw [factor_1_27]; decide
      have factor_1_29 : (29 : ZMod 23486071439) ^ 690766807 = 21736624354 := by
        calc
          (29 : ZMod 23486071439) ^ 690766807 = (29 : ZMod 23486071439) ^ (345383403 + 345383403 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 345383403 * (29 : ZMod 23486071439) ^ 345383403) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 21736624354 := by rw [factor_1_28]; decide
      have factor_1_30 : (29 : ZMod 23486071439) ^ 1381533614 = 15409579275 := by
        calc
          (29 : ZMod 23486071439) ^ 1381533614 = (29 : ZMod 23486071439) ^ (690766807 + 690766807) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 690766807 * (29 : ZMod 23486071439) ^ 690766807 := by rw [pow_add]
          _ = 15409579275 := by rw [factor_1_29]; decide
      change (29 : ZMod 23486071439) ^ 1381533614 ≠ 1
      rw [factor_1_30]
      decide
    ·
      have factor_2_0 : (29 : ZMod 23486071439) ^ 1 = 29 := by norm_num
      have factor_2_1 : (29 : ZMod 23486071439) ^ 2 = 841 := by
        calc
          (29 : ZMod 23486071439) ^ 2 = (29 : ZMod 23486071439) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 1 * (29 : ZMod 23486071439) ^ 1 := by rw [pow_add]
          _ = 841 := by rw [factor_2_0]; decide
      have factor_2_2 : (29 : ZMod 23486071439) ^ 4 = 707281 := by
        calc
          (29 : ZMod 23486071439) ^ 4 = (29 : ZMod 23486071439) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 2 * (29 : ZMod 23486071439) ^ 2 := by rw [pow_add]
          _ = 707281 := by rw [factor_2_1]; decide
      have factor_2_3 : (29 : ZMod 23486071439) ^ 9 = 16239898006 := by
        calc
          (29 : ZMod 23486071439) ^ 9 = (29 : ZMod 23486071439) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 4 * (29 : ZMod 23486071439) ^ 4) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 16239898006 := by rw [factor_2_2]; decide
      have factor_2_4 : (29 : ZMod 23486071439) ^ 19 = 15882795285 := by
        calc
          (29 : ZMod 23486071439) ^ 19 = (29 : ZMod 23486071439) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 9 * (29 : ZMod 23486071439) ^ 9) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 15882795285 := by rw [factor_2_3]; decide
      have factor_2_5 : (29 : ZMod 23486071439) ^ 38 = 21960616710 := by
        calc
          (29 : ZMod 23486071439) ^ 38 = (29 : ZMod 23486071439) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 19 * (29 : ZMod 23486071439) ^ 19 := by rw [pow_add]
          _ = 21960616710 := by rw [factor_2_4]; decide
      have factor_2_6 : (29 : ZMod 23486071439) ^ 76 = 6267338039 := by
        calc
          (29 : ZMod 23486071439) ^ 76 = (29 : ZMod 23486071439) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 38 * (29 : ZMod 23486071439) ^ 38 := by rw [pow_add]
          _ = 6267338039 := by rw [factor_2_5]; decide
      have factor_2_7 : (29 : ZMod 23486071439) ^ 153 = 22205126320 := by
        calc
          (29 : ZMod 23486071439) ^ 153 = (29 : ZMod 23486071439) ^ (76 + 76 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 76 * (29 : ZMod 23486071439) ^ 76) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 22205126320 := by rw [factor_2_6]; decide
      have factor_2_8 : (29 : ZMod 23486071439) ^ 306 = 1149561394 := by
        calc
          (29 : ZMod 23486071439) ^ 306 = (29 : ZMod 23486071439) ^ (153 + 153) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 153 * (29 : ZMod 23486071439) ^ 153 := by rw [pow_add]
          _ = 1149561394 := by rw [factor_2_7]; decide
      have factor_2_9 : (29 : ZMod 23486071439) ^ 613 = 17692931765 := by
        calc
          (29 : ZMod 23486071439) ^ 613 = (29 : ZMod 23486071439) ^ (306 + 306 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 306 * (29 : ZMod 23486071439) ^ 306) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 17692931765 := by rw [factor_2_8]; decide
      have factor_2_10 : (29 : ZMod 23486071439) ^ 1227 = 20719997545 := by
        calc
          (29 : ZMod 23486071439) ^ 1227 = (29 : ZMod 23486071439) ^ (613 + 613 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 613 * (29 : ZMod 23486071439) ^ 613) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 20719997545 := by rw [factor_2_9]; decide
      have factor_2_11 : (29 : ZMod 23486071439) ^ 2454 = 10010959884 := by
        calc
          (29 : ZMod 23486071439) ^ 2454 = (29 : ZMod 23486071439) ^ (1227 + 1227) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 1227 * (29 : ZMod 23486071439) ^ 1227 := by rw [pow_add]
          _ = 10010959884 := by rw [factor_2_10]; decide
      have factor_2_12 : (29 : ZMod 23486071439) ^ 4909 = 12820127931 := by
        calc
          (29 : ZMod 23486071439) ^ 4909 = (29 : ZMod 23486071439) ^ (2454 + 2454 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 2454 * (29 : ZMod 23486071439) ^ 2454) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 12820127931 := by rw [factor_2_11]; decide
      have factor_2_13 : (29 : ZMod 23486071439) ^ 9818 = 369273163 := by
        calc
          (29 : ZMod 23486071439) ^ 9818 = (29 : ZMod 23486071439) ^ (4909 + 4909) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 4909 * (29 : ZMod 23486071439) ^ 4909 := by rw [pow_add]
          _ = 369273163 := by rw [factor_2_12]; decide
      have factor_2_14 : (29 : ZMod 23486071439) ^ 19636 = 1641475157 := by
        calc
          (29 : ZMod 23486071439) ^ 19636 = (29 : ZMod 23486071439) ^ (9818 + 9818) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 9818 * (29 : ZMod 23486071439) ^ 9818 := by rw [pow_add]
          _ = 1641475157 := by rw [factor_2_13]; decide
      have factor_2_15 : (29 : ZMod 23486071439) ^ 39273 = 1753075075 := by
        calc
          (29 : ZMod 23486071439) ^ 39273 = (29 : ZMod 23486071439) ^ (19636 + 19636 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 19636 * (29 : ZMod 23486071439) ^ 19636) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 1753075075 := by rw [factor_2_14]; decide
      have factor_2_16 : (29 : ZMod 23486071439) ^ 78546 = 15314838164 := by
        calc
          (29 : ZMod 23486071439) ^ 78546 = (29 : ZMod 23486071439) ^ (39273 + 39273) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 39273 * (29 : ZMod 23486071439) ^ 39273 := by rw [pow_add]
          _ = 15314838164 := by rw [factor_2_15]; decide
      have factor_2_17 : (29 : ZMod 23486071439) ^ 157093 = 14032837986 := by
        calc
          (29 : ZMod 23486071439) ^ 157093 = (29 : ZMod 23486071439) ^ (78546 + 78546 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 78546 * (29 : ZMod 23486071439) ^ 78546) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 14032837986 := by rw [factor_2_16]; decide
      have factor_2_18 : (29 : ZMod 23486071439) ^ 314186 = 22149407857 := by
        calc
          (29 : ZMod 23486071439) ^ 314186 = (29 : ZMod 23486071439) ^ (157093 + 157093) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 157093 * (29 : ZMod 23486071439) ^ 157093 := by rw [pow_add]
          _ = 22149407857 := by rw [factor_2_17]; decide
      have factor_2_19 : (29 : ZMod 23486071439) ^ 628373 = 5337369772 := by
        calc
          (29 : ZMod 23486071439) ^ 628373 = (29 : ZMod 23486071439) ^ (314186 + 314186 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 314186 * (29 : ZMod 23486071439) ^ 314186) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 5337369772 := by rw [factor_2_18]; decide
      have factor_2_20 : (29 : ZMod 23486071439) ^ 1256746 = 6963529634 := by
        calc
          (29 : ZMod 23486071439) ^ 1256746 = (29 : ZMod 23486071439) ^ (628373 + 628373) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 628373 * (29 : ZMod 23486071439) ^ 628373 := by rw [pow_add]
          _ = 6963529634 := by rw [factor_2_19]; decide
      have factor_2_21 : (29 : ZMod 23486071439) ^ 2513492 = 10518651485 := by
        calc
          (29 : ZMod 23486071439) ^ 2513492 = (29 : ZMod 23486071439) ^ (1256746 + 1256746) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 1256746 * (29 : ZMod 23486071439) ^ 1256746 := by rw [pow_add]
          _ = 10518651485 := by rw [factor_2_20]; decide
      have factor_2_22 : (29 : ZMod 23486071439) ^ 5026984 = 21085869924 := by
        calc
          (29 : ZMod 23486071439) ^ 5026984 = (29 : ZMod 23486071439) ^ (2513492 + 2513492) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 2513492 * (29 : ZMod 23486071439) ^ 2513492 := by rw [pow_add]
          _ = 21085869924 := by rw [factor_2_21]; decide
      have factor_2_23 : (29 : ZMod 23486071439) ^ 10053968 = 11660597516 := by
        calc
          (29 : ZMod 23486071439) ^ 10053968 = (29 : ZMod 23486071439) ^ (5026984 + 5026984) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 5026984 * (29 : ZMod 23486071439) ^ 5026984 := by rw [pow_add]
          _ = 11660597516 := by rw [factor_2_22]; decide
      have factor_2_24 : (29 : ZMod 23486071439) ^ 20107937 = 249063293 := by
        calc
          (29 : ZMod 23486071439) ^ 20107937 = (29 : ZMod 23486071439) ^ (10053968 + 10053968 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 10053968 * (29 : ZMod 23486071439) ^ 10053968) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 249063293 := by rw [factor_2_23]; decide
      have factor_2_25 : (29 : ZMod 23486071439) ^ 40215875 = 2648108674 := by
        calc
          (29 : ZMod 23486071439) ^ 40215875 = (29 : ZMod 23486071439) ^ (20107937 + 20107937 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 20107937 * (29 : ZMod 23486071439) ^ 20107937) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 2648108674 := by rw [factor_2_24]; decide
      have factor_2_26 : (29 : ZMod 23486071439) ^ 80431751 = 20073594060 := by
        calc
          (29 : ZMod 23486071439) ^ 80431751 = (29 : ZMod 23486071439) ^ (40215875 + 40215875 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 40215875 * (29 : ZMod 23486071439) ^ 40215875) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 20073594060 := by rw [factor_2_25]; decide
      have factor_2_27 : (29 : ZMod 23486071439) ^ 160863503 = 16298026450 := by
        calc
          (29 : ZMod 23486071439) ^ 160863503 = (29 : ZMod 23486071439) ^ (80431751 + 80431751 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 80431751 * (29 : ZMod 23486071439) ^ 80431751) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 16298026450 := by rw [factor_2_26]; decide
      have factor_2_28 : (29 : ZMod 23486071439) ^ 321727006 = 17724331141 := by
        calc
          (29 : ZMod 23486071439) ^ 321727006 = (29 : ZMod 23486071439) ^ (160863503 + 160863503) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 160863503 * (29 : ZMod 23486071439) ^ 160863503 := by rw [pow_add]
          _ = 17724331141 := by rw [factor_2_27]; decide
      change (29 : ZMod 23486071439) ^ 321727006 ≠ 1
      rw [factor_2_28]
      decide
    ·
      have factor_3_0 : (29 : ZMod 23486071439) ^ 1 = 29 := by norm_num
      have factor_3_1 : (29 : ZMod 23486071439) ^ 3 = 24389 := by
        calc
          (29 : ZMod 23486071439) ^ 3 = (29 : ZMod 23486071439) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 1 * (29 : ZMod 23486071439) ^ 1) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 24389 := by rw [factor_3_0]; decide
      have factor_3_2 : (29 : ZMod 23486071439) ^ 6 = 594823321 := by
        calc
          (29 : ZMod 23486071439) ^ 6 = (29 : ZMod 23486071439) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 3 * (29 : ZMod 23486071439) ^ 3 := by rw [pow_add]
          _ = 594823321 := by rw [factor_3_1]; decide
      have factor_3_3 : (29 : ZMod 23486071439) ^ 12 = 5763721038 := by
        calc
          (29 : ZMod 23486071439) ^ 12 = (29 : ZMod 23486071439) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 6 * (29 : ZMod 23486071439) ^ 6 := by rw [pow_add]
          _ = 5763721038 := by rw [factor_3_2]; decide
      have factor_3_4 : (29 : ZMod 23486071439) ^ 25 = 13439009433 := by
        calc
          (29 : ZMod 23486071439) ^ 25 = (29 : ZMod 23486071439) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 12 * (29 : ZMod 23486071439) ^ 12) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 13439009433 := by rw [factor_3_3]; decide
      have factor_3_5 : (29 : ZMod 23486071439) ^ 50 = 3807673417 := by
        calc
          (29 : ZMod 23486071439) ^ 50 = (29 : ZMod 23486071439) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 25 * (29 : ZMod 23486071439) ^ 25 := by rw [pow_add]
          _ = 3807673417 := by rw [factor_3_4]; decide
      have factor_3_6 : (29 : ZMod 23486071439) ^ 100 = 17743210062 := by
        calc
          (29 : ZMod 23486071439) ^ 100 = (29 : ZMod 23486071439) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 50 * (29 : ZMod 23486071439) ^ 50 := by rw [pow_add]
          _ = 17743210062 := by rw [factor_3_5]; decide
      have factor_3_7 : (29 : ZMod 23486071439) ^ 200 = 13821809251 := by
        calc
          (29 : ZMod 23486071439) ^ 200 = (29 : ZMod 23486071439) ^ (100 + 100) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 100 * (29 : ZMod 23486071439) ^ 100 := by rw [pow_add]
          _ = 13821809251 := by rw [factor_3_6]; decide
      have factor_3_8 : (29 : ZMod 23486071439) ^ 401 = 15943040645 := by
        calc
          (29 : ZMod 23486071439) ^ 401 = (29 : ZMod 23486071439) ^ (200 + 200 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 200 * (29 : ZMod 23486071439) ^ 200) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 15943040645 := by rw [factor_3_7]; decide
      have factor_3_9 : (29 : ZMod 23486071439) ^ 803 = 5797940614 := by
        calc
          (29 : ZMod 23486071439) ^ 803 = (29 : ZMod 23486071439) ^ (401 + 401 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 401 * (29 : ZMod 23486071439) ^ 401) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 5797940614 := by rw [factor_3_8]; decide
      have factor_3_10 : (29 : ZMod 23486071439) ^ 1607 = 5960600372 := by
        calc
          (29 : ZMod 23486071439) ^ 1607 = (29 : ZMod 23486071439) ^ (803 + 803 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 803 * (29 : ZMod 23486071439) ^ 803) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 5960600372 := by rw [factor_3_9]; decide
      have factor_3_11 : (29 : ZMod 23486071439) ^ 3214 = 10264198594 := by
        calc
          (29 : ZMod 23486071439) ^ 3214 = (29 : ZMod 23486071439) ^ (1607 + 1607) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 1607 * (29 : ZMod 23486071439) ^ 1607 := by rw [pow_add]
          _ = 10264198594 := by rw [factor_3_10]; decide
      have factor_3_12 : (29 : ZMod 23486071439) ^ 6428 = 18426826056 := by
        calc
          (29 : ZMod 23486071439) ^ 6428 = (29 : ZMod 23486071439) ^ (3214 + 3214) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 3214 * (29 : ZMod 23486071439) ^ 3214 := by rw [pow_add]
          _ = 18426826056 := by rw [factor_3_11]; decide
      have factor_3_13 : (29 : ZMod 23486071439) ^ 12856 = 17733885150 := by
        calc
          (29 : ZMod 23486071439) ^ 12856 = (29 : ZMod 23486071439) ^ (6428 + 6428) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 6428 * (29 : ZMod 23486071439) ^ 6428 := by rw [pow_add]
          _ = 17733885150 := by rw [factor_3_12]; decide
      have factor_3_14 : (29 : ZMod 23486071439) ^ 25712 = 9125825838 := by
        calc
          (29 : ZMod 23486071439) ^ 25712 = (29 : ZMod 23486071439) ^ (12856 + 12856) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 12856 * (29 : ZMod 23486071439) ^ 12856 := by rw [pow_add]
          _ = 9125825838 := by rw [factor_3_13]; decide
      have factor_3_15 : (29 : ZMod 23486071439) ^ 51425 = 17284767241 := by
        calc
          (29 : ZMod 23486071439) ^ 51425 = (29 : ZMod 23486071439) ^ (25712 + 25712 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 25712 * (29 : ZMod 23486071439) ^ 25712) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 17284767241 := by rw [factor_3_14]; decide
      have factor_3_16 : (29 : ZMod 23486071439) ^ 102850 = 12577358946 := by
        calc
          (29 : ZMod 23486071439) ^ 102850 = (29 : ZMod 23486071439) ^ (51425 + 51425) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 51425 * (29 : ZMod 23486071439) ^ 51425 := by rw [pow_add]
          _ = 12577358946 := by rw [factor_3_15]; decide
      have factor_3_17 : (29 : ZMod 23486071439) ^ 205700 = 12268013763 := by
        calc
          (29 : ZMod 23486071439) ^ 205700 = (29 : ZMod 23486071439) ^ (102850 + 102850) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 102850 * (29 : ZMod 23486071439) ^ 102850 := by rw [pow_add]
          _ = 12268013763 := by rw [factor_3_16]; decide
      have factor_3_18 : (29 : ZMod 23486071439) ^ 411401 = 15510301765 := by
        calc
          (29 : ZMod 23486071439) ^ 411401 = (29 : ZMod 23486071439) ^ (205700 + 205700 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 205700 * (29 : ZMod 23486071439) ^ 205700) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 15510301765 := by rw [factor_3_17]; decide
      have factor_3_19 : (29 : ZMod 23486071439) ^ 822802 = 7509748114 := by
        calc
          (29 : ZMod 23486071439) ^ 822802 = (29 : ZMod 23486071439) ^ (411401 + 411401) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 411401 * (29 : ZMod 23486071439) ^ 411401 := by rw [pow_add]
          _ = 7509748114 := by rw [factor_3_18]; decide
      have factor_3_20 : (29 : ZMod 23486071439) ^ 1645604 = 8246563423 := by
        calc
          (29 : ZMod 23486071439) ^ 1645604 = (29 : ZMod 23486071439) ^ (822802 + 822802) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 822802 * (29 : ZMod 23486071439) ^ 822802 := by rw [pow_add]
          _ = 8246563423 := by rw [factor_3_19]; decide
      have factor_3_21 : (29 : ZMod 23486071439) ^ 3291209 = 19707299375 := by
        calc
          (29 : ZMod 23486071439) ^ 3291209 = (29 : ZMod 23486071439) ^ (1645604 + 1645604 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 1645604 * (29 : ZMod 23486071439) ^ 1645604) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 19707299375 := by rw [factor_3_20]; decide
      have factor_3_22 : (29 : ZMod 23486071439) ^ 6582419 = 23221888269 := by
        calc
          (29 : ZMod 23486071439) ^ 6582419 = (29 : ZMod 23486071439) ^ (3291209 + 3291209 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 3291209 * (29 : ZMod 23486071439) ^ 3291209) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 23221888269 := by rw [factor_3_21]; decide
      have factor_3_23 : (29 : ZMod 23486071439) ^ 13164838 = 10828472965 := by
        calc
          (29 : ZMod 23486071439) ^ 13164838 = (29 : ZMod 23486071439) ^ (6582419 + 6582419) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 6582419 * (29 : ZMod 23486071439) ^ 6582419 := by rw [pow_add]
          _ = 10828472965 := by rw [factor_3_22]; decide
      have factor_3_24 : (29 : ZMod 23486071439) ^ 26329676 = 4367674073 := by
        calc
          (29 : ZMod 23486071439) ^ 26329676 = (29 : ZMod 23486071439) ^ (13164838 + 13164838) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 13164838 * (29 : ZMod 23486071439) ^ 13164838 := by rw [pow_add]
          _ = 4367674073 := by rw [factor_3_23]; decide
      have factor_3_25 : (29 : ZMod 23486071439) ^ 52659353 = 8549138050 := by
        calc
          (29 : ZMod 23486071439) ^ 52659353 = (29 : ZMod 23486071439) ^ (26329676 + 26329676 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 26329676 * (29 : ZMod 23486071439) ^ 26329676) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 8549138050 := by rw [factor_3_24]; decide
      have factor_3_26 : (29 : ZMod 23486071439) ^ 105318706 = 20225913280 := by
        calc
          (29 : ZMod 23486071439) ^ 105318706 = (29 : ZMod 23486071439) ^ (52659353 + 52659353) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 52659353 * (29 : ZMod 23486071439) ^ 52659353 := by rw [pow_add]
          _ = 20225913280 := by rw [factor_3_25]; decide
      change (29 : ZMod 23486071439) ^ 105318706 ≠ 1
      rw [factor_3_26]
      decide
    ·
      have factor_4_0 : (29 : ZMod 23486071439) ^ 1 = 29 := by norm_num
      have factor_4_1 : (29 : ZMod 23486071439) ^ 2 = 841 := by
        calc
          (29 : ZMod 23486071439) ^ 2 = (29 : ZMod 23486071439) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 1 * (29 : ZMod 23486071439) ^ 1 := by rw [pow_add]
          _ = 841 := by rw [factor_4_0]; decide
      have factor_4_2 : (29 : ZMod 23486071439) ^ 4 = 707281 := by
        calc
          (29 : ZMod 23486071439) ^ 4 = (29 : ZMod 23486071439) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 2 * (29 : ZMod 23486071439) ^ 2 := by rw [pow_add]
          _ = 707281 := by rw [factor_4_1]; decide
      have factor_4_3 : (29 : ZMod 23486071439) ^ 8 = 7038912742 := by
        calc
          (29 : ZMod 23486071439) ^ 8 = (29 : ZMod 23486071439) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 4 * (29 : ZMod 23486071439) ^ 4 := by rw [pow_add]
          _ = 7038912742 := by rw [factor_4_2]; decide
      have factor_4_4 : (29 : ZMod 23486071439) ^ 16 = 22501596131 := by
        calc
          (29 : ZMod 23486071439) ^ 16 = (29 : ZMod 23486071439) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 8 * (29 : ZMod 23486071439) ^ 8 := by rw [pow_add]
          _ = 22501596131 := by rw [factor_4_3]; decide
      have factor_4_5 : (29 : ZMod 23486071439) ^ 33 = 11228578081 := by
        calc
          (29 : ZMod 23486071439) ^ 33 = (29 : ZMod 23486071439) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 16 * (29 : ZMod 23486071439) ^ 16) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 11228578081 := by rw [factor_4_4]; decide
      have factor_4_6 : (29 : ZMod 23486071439) ^ 67 = 9060541026 := by
        calc
          (29 : ZMod 23486071439) ^ 67 = (29 : ZMod 23486071439) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 33 * (29 : ZMod 23486071439) ^ 33) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 9060541026 := by rw [factor_4_5]; decide
      have factor_4_7 : (29 : ZMod 23486071439) ^ 135 = 12446792167 := by
        calc
          (29 : ZMod 23486071439) ^ 135 = (29 : ZMod 23486071439) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 67 * (29 : ZMod 23486071439) ^ 67) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 12446792167 := by rw [factor_4_6]; decide
      have factor_4_8 : (29 : ZMod 23486071439) ^ 270 = 19581206627 := by
        calc
          (29 : ZMod 23486071439) ^ 270 = (29 : ZMod 23486071439) ^ (135 + 135) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 135 * (29 : ZMod 23486071439) ^ 135 := by rw [pow_add]
          _ = 19581206627 := by rw [factor_4_7]; decide
      have factor_4_9 : (29 : ZMod 23486071439) ^ 540 = 13626277821 := by
        calc
          (29 : ZMod 23486071439) ^ 540 = (29 : ZMod 23486071439) ^ (270 + 270) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 270 * (29 : ZMod 23486071439) ^ 270 := by rw [pow_add]
          _ = 13626277821 := by rw [factor_4_8]; decide
      have factor_4_10 : (29 : ZMod 23486071439) ^ 1081 = 18945200550 := by
        calc
          (29 : ZMod 23486071439) ^ 1081 = (29 : ZMod 23486071439) ^ (540 + 540 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 540 * (29 : ZMod 23486071439) ^ 540) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 18945200550 := by rw [factor_4_9]; decide
      have factor_4_11 : (29 : ZMod 23486071439) ^ 2162 = 13007282254 := by
        calc
          (29 : ZMod 23486071439) ^ 2162 = (29 : ZMod 23486071439) ^ (1081 + 1081) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 1081 * (29 : ZMod 23486071439) ^ 1081 := by rw [pow_add]
          _ = 13007282254 := by rw [factor_4_10]; decide
      have factor_4_12 : (29 : ZMod 23486071439) ^ 4324 = 8584572353 := by
        calc
          (29 : ZMod 23486071439) ^ 4324 = (29 : ZMod 23486071439) ^ (2162 + 2162) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 2162 * (29 : ZMod 23486071439) ^ 2162 := by rw [pow_add]
          _ = 8584572353 := by rw [factor_4_11]; decide
      have factor_4_13 : (29 : ZMod 23486071439) ^ 8648 = 6111200371 := by
        calc
          (29 : ZMod 23486071439) ^ 8648 = (29 : ZMod 23486071439) ^ (4324 + 4324) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 4324 * (29 : ZMod 23486071439) ^ 4324 := by rw [pow_add]
          _ = 6111200371 := by rw [factor_4_12]; decide
      have factor_4_14 : (29 : ZMod 23486071439) ^ 17296 = 13629870074 := by
        calc
          (29 : ZMod 23486071439) ^ 17296 = (29 : ZMod 23486071439) ^ (8648 + 8648) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 8648 * (29 : ZMod 23486071439) ^ 8648 := by rw [pow_add]
          _ = 13629870074 := by rw [factor_4_13]; decide
      have factor_4_15 : (29 : ZMod 23486071439) ^ 34592 = 21194631099 := by
        calc
          (29 : ZMod 23486071439) ^ 34592 = (29 : ZMod 23486071439) ^ (17296 + 17296) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 17296 * (29 : ZMod 23486071439) ^ 17296 := by rw [pow_add]
          _ = 21194631099 := by rw [factor_4_14]; decide
      have factor_4_16 : (29 : ZMod 23486071439) ^ 69185 = 3161897511 := by
        calc
          (29 : ZMod 23486071439) ^ 69185 = (29 : ZMod 23486071439) ^ (34592 + 34592 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 34592 * (29 : ZMod 23486071439) ^ 34592) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 3161897511 := by rw [factor_4_15]; decide
      have factor_4_17 : (29 : ZMod 23486071439) ^ 138371 = 1112056449 := by
        calc
          (29 : ZMod 23486071439) ^ 138371 = (29 : ZMod 23486071439) ^ (69185 + 69185 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 69185 * (29 : ZMod 23486071439) ^ 69185) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 1112056449 := by rw [factor_4_16]; decide
      have factor_4_18 : (29 : ZMod 23486071439) ^ 276743 = 11906258817 := by
        calc
          (29 : ZMod 23486071439) ^ 276743 = (29 : ZMod 23486071439) ^ (138371 + 138371 + 1) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = ((29 : ZMod 23486071439) ^ 138371 * (29 : ZMod 23486071439) ^ 138371) * (29 : ZMod 23486071439) := by rw [pow_succ, pow_add]
          _ = 11906258817 := by rw [factor_4_17]; decide
      have factor_4_19 : (29 : ZMod 23486071439) ^ 553486 = 8001111131 := by
        calc
          (29 : ZMod 23486071439) ^ 553486 = (29 : ZMod 23486071439) ^ (276743 + 276743) :=
            congrArg (fun n : ℕ => (29 : ZMod 23486071439) ^ n) (by norm_num)
          _ = (29 : ZMod 23486071439) ^ 276743 * (29 : ZMod 23486071439) ^ 276743 := by rw [pow_add]
          _ = 8001111131 := by rw [factor_4_18]; decide
      change (29 : ZMod 23486071439) ^ 553486 ≠ 1
      rw [factor_4_19]
      decide

#print axioms prime_lucas_23486071439

end TotientTailPeriodKiller
end Erdos249257
