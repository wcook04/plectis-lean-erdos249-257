import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_478361953 : Nat.Prime 478361953 := by
  apply lucas_primality 478361953 (10 : ZMod 478361953)
  ·
      have fermat_0 : (10 : ZMod 478361953) ^ 1 = 10 := by norm_num
      have fermat_1 : (10 : ZMod 478361953) ^ 3 = 1000 := by
        calc
          (10 : ZMod 478361953) ^ 3 = (10 : ZMod 478361953) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 1 * (10 : ZMod 478361953) ^ 1) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [fermat_0]; decide
      have fermat_2 : (10 : ZMod 478361953) ^ 7 = 10000000 := by
        calc
          (10 : ZMod 478361953) ^ 7 = (10 : ZMod 478361953) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 3 * (10 : ZMod 478361953) ^ 3) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 10000000 := by rw [fermat_1]; decide
      have fermat_3 : (10 : ZMod 478361953) ^ 14 = 347173162 := by
        calc
          (10 : ZMod 478361953) ^ 14 = (10 : ZMod 478361953) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 7 * (10 : ZMod 478361953) ^ 7 := by rw [pow_add]
          _ = 347173162 := by rw [fermat_2]; decide
      have fermat_4 : (10 : ZMod 478361953) ^ 28 = 192798929 := by
        calc
          (10 : ZMod 478361953) ^ 28 = (10 : ZMod 478361953) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 14 * (10 : ZMod 478361953) ^ 14 := by rw [pow_add]
          _ = 192798929 := by rw [fermat_3]; decide
      have fermat_5 : (10 : ZMod 478361953) ^ 57 = 42144427 := by
        calc
          (10 : ZMod 478361953) ^ 57 = (10 : ZMod 478361953) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 28 * (10 : ZMod 478361953) ^ 28) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 42144427 := by rw [fermat_4]; decide
      have fermat_6 : (10 : ZMod 478361953) ^ 114 = 57650812 := by
        calc
          (10 : ZMod 478361953) ^ 114 = (10 : ZMod 478361953) ^ (57 + 57) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 57 * (10 : ZMod 478361953) ^ 57 := by rw [pow_add]
          _ = 57650812 := by rw [fermat_5]; decide
      have fermat_7 : (10 : ZMod 478361953) ^ 228 = 327391114 := by
        calc
          (10 : ZMod 478361953) ^ 228 = (10 : ZMod 478361953) ^ (114 + 114) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 114 * (10 : ZMod 478361953) ^ 114 := by rw [pow_add]
          _ = 327391114 := by rw [fermat_6]; decide
      have fermat_8 : (10 : ZMod 478361953) ^ 456 = 364471666 := by
        calc
          (10 : ZMod 478361953) ^ 456 = (10 : ZMod 478361953) ^ (228 + 228) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 228 * (10 : ZMod 478361953) ^ 228 := by rw [pow_add]
          _ = 364471666 := by rw [fermat_7]; decide
      have fermat_9 : (10 : ZMod 478361953) ^ 912 = 246278284 := by
        calc
          (10 : ZMod 478361953) ^ 912 = (10 : ZMod 478361953) ^ (456 + 456) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 456 * (10 : ZMod 478361953) ^ 456 := by rw [pow_add]
          _ = 246278284 := by rw [fermat_8]; decide
      have fermat_10 : (10 : ZMod 478361953) ^ 1824 = 140508168 := by
        calc
          (10 : ZMod 478361953) ^ 1824 = (10 : ZMod 478361953) ^ (912 + 912) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 912 * (10 : ZMod 478361953) ^ 912 := by rw [pow_add]
          _ = 140508168 := by rw [fermat_9]; decide
      have fermat_11 : (10 : ZMod 478361953) ^ 3649 = 369872108 := by
        calc
          (10 : ZMod 478361953) ^ 3649 = (10 : ZMod 478361953) ^ (1824 + 1824 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 1824 * (10 : ZMod 478361953) ^ 1824) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 369872108 := by rw [fermat_10]; decide
      have fermat_12 : (10 : ZMod 478361953) ^ 7299 = 293487699 := by
        calc
          (10 : ZMod 478361953) ^ 7299 = (10 : ZMod 478361953) ^ (3649 + 3649 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 3649 * (10 : ZMod 478361953) ^ 3649) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 293487699 := by rw [fermat_11]; decide
      have fermat_13 : (10 : ZMod 478361953) ^ 14598 = 393454127 := by
        calc
          (10 : ZMod 478361953) ^ 14598 = (10 : ZMod 478361953) ^ (7299 + 7299) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 7299 * (10 : ZMod 478361953) ^ 7299 := by rw [pow_add]
          _ = 393454127 := by rw [fermat_12]; decide
      have fermat_14 : (10 : ZMod 478361953) ^ 29196 = 455645918 := by
        calc
          (10 : ZMod 478361953) ^ 29196 = (10 : ZMod 478361953) ^ (14598 + 14598) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 14598 * (10 : ZMod 478361953) ^ 14598 := by rw [pow_add]
          _ = 455645918 := by rw [fermat_13]; decide
      have fermat_15 : (10 : ZMod 478361953) ^ 58393 = 228706274 := by
        calc
          (10 : ZMod 478361953) ^ 58393 = (10 : ZMod 478361953) ^ (29196 + 29196 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 29196 * (10 : ZMod 478361953) ^ 29196) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 228706274 := by rw [fermat_14]; decide
      have fermat_16 : (10 : ZMod 478361953) ^ 116787 = 227041495 := by
        calc
          (10 : ZMod 478361953) ^ 116787 = (10 : ZMod 478361953) ^ (58393 + 58393 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 58393 * (10 : ZMod 478361953) ^ 58393) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 227041495 := by rw [fermat_15]; decide
      have fermat_17 : (10 : ZMod 478361953) ^ 233575 = 294302372 := by
        calc
          (10 : ZMod 478361953) ^ 233575 = (10 : ZMod 478361953) ^ (116787 + 116787 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 116787 * (10 : ZMod 478361953) ^ 116787) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 294302372 := by rw [fermat_16]; decide
      have fermat_18 : (10 : ZMod 478361953) ^ 467150 = 36344555 := by
        calc
          (10 : ZMod 478361953) ^ 467150 = (10 : ZMod 478361953) ^ (233575 + 233575) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 233575 * (10 : ZMod 478361953) ^ 233575 := by rw [pow_add]
          _ = 36344555 := by rw [fermat_17]; decide
      have fermat_19 : (10 : ZMod 478361953) ^ 934300 = 464145616 := by
        calc
          (10 : ZMod 478361953) ^ 934300 = (10 : ZMod 478361953) ^ (467150 + 467150) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 467150 * (10 : ZMod 478361953) ^ 467150 := by rw [pow_add]
          _ = 464145616 := by rw [fermat_18]; decide
      have fermat_20 : (10 : ZMod 478361953) ^ 1868601 = 437783024 := by
        calc
          (10 : ZMod 478361953) ^ 1868601 = (10 : ZMod 478361953) ^ (934300 + 934300 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 934300 * (10 : ZMod 478361953) ^ 934300) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 437783024 := by rw [fermat_19]; decide
      have fermat_21 : (10 : ZMod 478361953) ^ 3737202 = 392281543 := by
        calc
          (10 : ZMod 478361953) ^ 3737202 = (10 : ZMod 478361953) ^ (1868601 + 1868601) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 1868601 * (10 : ZMod 478361953) ^ 1868601 := by rw [pow_add]
          _ = 392281543 := by rw [fermat_20]; decide
      have fermat_22 : (10 : ZMod 478361953) ^ 7474405 = 11799152 := by
        calc
          (10 : ZMod 478361953) ^ 7474405 = (10 : ZMod 478361953) ^ (3737202 + 3737202 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 3737202 * (10 : ZMod 478361953) ^ 3737202) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 11799152 := by rw [fermat_21]; decide
      have fermat_23 : (10 : ZMod 478361953) ^ 14948811 = 126001396 := by
        calc
          (10 : ZMod 478361953) ^ 14948811 = (10 : ZMod 478361953) ^ (7474405 + 7474405 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 7474405 * (10 : ZMod 478361953) ^ 7474405) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 126001396 := by rw [fermat_22]; decide
      have fermat_24 : (10 : ZMod 478361953) ^ 29897622 = 284365487 := by
        calc
          (10 : ZMod 478361953) ^ 29897622 = (10 : ZMod 478361953) ^ (14948811 + 14948811) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 14948811 * (10 : ZMod 478361953) ^ 14948811 := by rw [pow_add]
          _ = 284365487 := by rw [fermat_23]; decide
      have fermat_25 : (10 : ZMod 478361953) ^ 59795244 = 143007229 := by
        calc
          (10 : ZMod 478361953) ^ 59795244 = (10 : ZMod 478361953) ^ (29897622 + 29897622) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 29897622 * (10 : ZMod 478361953) ^ 29897622 := by rw [pow_add]
          _ = 143007229 := by rw [fermat_24]; decide
      have fermat_26 : (10 : ZMod 478361953) ^ 119590488 = 41721930 := by
        calc
          (10 : ZMod 478361953) ^ 119590488 = (10 : ZMod 478361953) ^ (59795244 + 59795244) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 59795244 * (10 : ZMod 478361953) ^ 59795244 := by rw [pow_add]
          _ = 41721930 := by rw [fermat_25]; decide
      have fermat_27 : (10 : ZMod 478361953) ^ 239180976 = 478361952 := by
        calc
          (10 : ZMod 478361953) ^ 239180976 = (10 : ZMod 478361953) ^ (119590488 + 119590488) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 119590488 * (10 : ZMod 478361953) ^ 119590488 := by rw [pow_add]
          _ = 478361952 := by rw [fermat_26]; decide
      have fermat_28 : (10 : ZMod 478361953) ^ 478361952 = 1 := by
        calc
          (10 : ZMod 478361953) ^ 478361952 = (10 : ZMod 478361953) ^ (239180976 + 239180976) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 239180976 * (10 : ZMod 478361953) ^ 239180976 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 2), (1117, 1), (1487, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 2), (1117, 1), (1487, 1)] : List FactorBlock).map factorBlockValue).prod = 478361953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (10 : ZMod 478361953) ^ 1 = 10 := by norm_num
      have factor_0_1 : (10 : ZMod 478361953) ^ 3 = 1000 := by
        calc
          (10 : ZMod 478361953) ^ 3 = (10 : ZMod 478361953) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 1 * (10 : ZMod 478361953) ^ 1) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_0_0]; decide
      have factor_0_2 : (10 : ZMod 478361953) ^ 7 = 10000000 := by
        calc
          (10 : ZMod 478361953) ^ 7 = (10 : ZMod 478361953) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 3 * (10 : ZMod 478361953) ^ 3) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 10000000 := by rw [factor_0_1]; decide
      have factor_0_3 : (10 : ZMod 478361953) ^ 14 = 347173162 := by
        calc
          (10 : ZMod 478361953) ^ 14 = (10 : ZMod 478361953) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 7 * (10 : ZMod 478361953) ^ 7 := by rw [pow_add]
          _ = 347173162 := by rw [factor_0_2]; decide
      have factor_0_4 : (10 : ZMod 478361953) ^ 28 = 192798929 := by
        calc
          (10 : ZMod 478361953) ^ 28 = (10 : ZMod 478361953) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 14 * (10 : ZMod 478361953) ^ 14 := by rw [pow_add]
          _ = 192798929 := by rw [factor_0_3]; decide
      have factor_0_5 : (10 : ZMod 478361953) ^ 57 = 42144427 := by
        calc
          (10 : ZMod 478361953) ^ 57 = (10 : ZMod 478361953) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 28 * (10 : ZMod 478361953) ^ 28) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 42144427 := by rw [factor_0_4]; decide
      have factor_0_6 : (10 : ZMod 478361953) ^ 114 = 57650812 := by
        calc
          (10 : ZMod 478361953) ^ 114 = (10 : ZMod 478361953) ^ (57 + 57) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 57 * (10 : ZMod 478361953) ^ 57 := by rw [pow_add]
          _ = 57650812 := by rw [factor_0_5]; decide
      have factor_0_7 : (10 : ZMod 478361953) ^ 228 = 327391114 := by
        calc
          (10 : ZMod 478361953) ^ 228 = (10 : ZMod 478361953) ^ (114 + 114) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 114 * (10 : ZMod 478361953) ^ 114 := by rw [pow_add]
          _ = 327391114 := by rw [factor_0_6]; decide
      have factor_0_8 : (10 : ZMod 478361953) ^ 456 = 364471666 := by
        calc
          (10 : ZMod 478361953) ^ 456 = (10 : ZMod 478361953) ^ (228 + 228) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 228 * (10 : ZMod 478361953) ^ 228 := by rw [pow_add]
          _ = 364471666 := by rw [factor_0_7]; decide
      have factor_0_9 : (10 : ZMod 478361953) ^ 912 = 246278284 := by
        calc
          (10 : ZMod 478361953) ^ 912 = (10 : ZMod 478361953) ^ (456 + 456) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 456 * (10 : ZMod 478361953) ^ 456 := by rw [pow_add]
          _ = 246278284 := by rw [factor_0_8]; decide
      have factor_0_10 : (10 : ZMod 478361953) ^ 1824 = 140508168 := by
        calc
          (10 : ZMod 478361953) ^ 1824 = (10 : ZMod 478361953) ^ (912 + 912) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 912 * (10 : ZMod 478361953) ^ 912 := by rw [pow_add]
          _ = 140508168 := by rw [factor_0_9]; decide
      have factor_0_11 : (10 : ZMod 478361953) ^ 3649 = 369872108 := by
        calc
          (10 : ZMod 478361953) ^ 3649 = (10 : ZMod 478361953) ^ (1824 + 1824 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 1824 * (10 : ZMod 478361953) ^ 1824) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 369872108 := by rw [factor_0_10]; decide
      have factor_0_12 : (10 : ZMod 478361953) ^ 7299 = 293487699 := by
        calc
          (10 : ZMod 478361953) ^ 7299 = (10 : ZMod 478361953) ^ (3649 + 3649 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 3649 * (10 : ZMod 478361953) ^ 3649) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 293487699 := by rw [factor_0_11]; decide
      have factor_0_13 : (10 : ZMod 478361953) ^ 14598 = 393454127 := by
        calc
          (10 : ZMod 478361953) ^ 14598 = (10 : ZMod 478361953) ^ (7299 + 7299) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 7299 * (10 : ZMod 478361953) ^ 7299 := by rw [pow_add]
          _ = 393454127 := by rw [factor_0_12]; decide
      have factor_0_14 : (10 : ZMod 478361953) ^ 29196 = 455645918 := by
        calc
          (10 : ZMod 478361953) ^ 29196 = (10 : ZMod 478361953) ^ (14598 + 14598) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 14598 * (10 : ZMod 478361953) ^ 14598 := by rw [pow_add]
          _ = 455645918 := by rw [factor_0_13]; decide
      have factor_0_15 : (10 : ZMod 478361953) ^ 58393 = 228706274 := by
        calc
          (10 : ZMod 478361953) ^ 58393 = (10 : ZMod 478361953) ^ (29196 + 29196 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 29196 * (10 : ZMod 478361953) ^ 29196) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 228706274 := by rw [factor_0_14]; decide
      have factor_0_16 : (10 : ZMod 478361953) ^ 116787 = 227041495 := by
        calc
          (10 : ZMod 478361953) ^ 116787 = (10 : ZMod 478361953) ^ (58393 + 58393 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 58393 * (10 : ZMod 478361953) ^ 58393) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 227041495 := by rw [factor_0_15]; decide
      have factor_0_17 : (10 : ZMod 478361953) ^ 233575 = 294302372 := by
        calc
          (10 : ZMod 478361953) ^ 233575 = (10 : ZMod 478361953) ^ (116787 + 116787 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 116787 * (10 : ZMod 478361953) ^ 116787) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 294302372 := by rw [factor_0_16]; decide
      have factor_0_18 : (10 : ZMod 478361953) ^ 467150 = 36344555 := by
        calc
          (10 : ZMod 478361953) ^ 467150 = (10 : ZMod 478361953) ^ (233575 + 233575) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 233575 * (10 : ZMod 478361953) ^ 233575 := by rw [pow_add]
          _ = 36344555 := by rw [factor_0_17]; decide
      have factor_0_19 : (10 : ZMod 478361953) ^ 934300 = 464145616 := by
        calc
          (10 : ZMod 478361953) ^ 934300 = (10 : ZMod 478361953) ^ (467150 + 467150) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 467150 * (10 : ZMod 478361953) ^ 467150 := by rw [pow_add]
          _ = 464145616 := by rw [factor_0_18]; decide
      have factor_0_20 : (10 : ZMod 478361953) ^ 1868601 = 437783024 := by
        calc
          (10 : ZMod 478361953) ^ 1868601 = (10 : ZMod 478361953) ^ (934300 + 934300 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 934300 * (10 : ZMod 478361953) ^ 934300) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 437783024 := by rw [factor_0_19]; decide
      have factor_0_21 : (10 : ZMod 478361953) ^ 3737202 = 392281543 := by
        calc
          (10 : ZMod 478361953) ^ 3737202 = (10 : ZMod 478361953) ^ (1868601 + 1868601) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 1868601 * (10 : ZMod 478361953) ^ 1868601 := by rw [pow_add]
          _ = 392281543 := by rw [factor_0_20]; decide
      have factor_0_22 : (10 : ZMod 478361953) ^ 7474405 = 11799152 := by
        calc
          (10 : ZMod 478361953) ^ 7474405 = (10 : ZMod 478361953) ^ (3737202 + 3737202 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 3737202 * (10 : ZMod 478361953) ^ 3737202) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 11799152 := by rw [factor_0_21]; decide
      have factor_0_23 : (10 : ZMod 478361953) ^ 14948811 = 126001396 := by
        calc
          (10 : ZMod 478361953) ^ 14948811 = (10 : ZMod 478361953) ^ (7474405 + 7474405 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 7474405 * (10 : ZMod 478361953) ^ 7474405) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 126001396 := by rw [factor_0_22]; decide
      have factor_0_24 : (10 : ZMod 478361953) ^ 29897622 = 284365487 := by
        calc
          (10 : ZMod 478361953) ^ 29897622 = (10 : ZMod 478361953) ^ (14948811 + 14948811) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 14948811 * (10 : ZMod 478361953) ^ 14948811 := by rw [pow_add]
          _ = 284365487 := by rw [factor_0_23]; decide
      have factor_0_25 : (10 : ZMod 478361953) ^ 59795244 = 143007229 := by
        calc
          (10 : ZMod 478361953) ^ 59795244 = (10 : ZMod 478361953) ^ (29897622 + 29897622) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 29897622 * (10 : ZMod 478361953) ^ 29897622 := by rw [pow_add]
          _ = 143007229 := by rw [factor_0_24]; decide
      have factor_0_26 : (10 : ZMod 478361953) ^ 119590488 = 41721930 := by
        calc
          (10 : ZMod 478361953) ^ 119590488 = (10 : ZMod 478361953) ^ (59795244 + 59795244) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 59795244 * (10 : ZMod 478361953) ^ 59795244 := by rw [pow_add]
          _ = 41721930 := by rw [factor_0_25]; decide
      have factor_0_27 : (10 : ZMod 478361953) ^ 239180976 = 478361952 := by
        calc
          (10 : ZMod 478361953) ^ 239180976 = (10 : ZMod 478361953) ^ (119590488 + 119590488) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 119590488 * (10 : ZMod 478361953) ^ 119590488 := by rw [pow_add]
          _ = 478361952 := by rw [factor_0_26]; decide
      change (10 : ZMod 478361953) ^ 239180976 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (10 : ZMod 478361953) ^ 1 = 10 := by norm_num
      have factor_1_1 : (10 : ZMod 478361953) ^ 2 = 100 := by
        calc
          (10 : ZMod 478361953) ^ 2 = (10 : ZMod 478361953) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 1 * (10 : ZMod 478361953) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_1_0]; decide
      have factor_1_2 : (10 : ZMod 478361953) ^ 4 = 10000 := by
        calc
          (10 : ZMod 478361953) ^ 4 = (10 : ZMod 478361953) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 2 * (10 : ZMod 478361953) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [factor_1_1]; decide
      have factor_1_3 : (10 : ZMod 478361953) ^ 9 = 43276094 := by
        calc
          (10 : ZMod 478361953) ^ 9 = (10 : ZMod 478361953) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 4 * (10 : ZMod 478361953) ^ 4) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 43276094 := by rw [factor_1_2]; decide
      have factor_1_4 : (10 : ZMod 478361953) ^ 19 = 197461025 := by
        calc
          (10 : ZMod 478361953) ^ 19 = (10 : ZMod 478361953) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 9 * (10 : ZMod 478361953) ^ 9) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 197461025 := by rw [factor_1_3]; decide
      have factor_1_5 : (10 : ZMod 478361953) ^ 38 = 303882701 := by
        calc
          (10 : ZMod 478361953) ^ 38 = (10 : ZMod 478361953) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 19 * (10 : ZMod 478361953) ^ 19 := by rw [pow_add]
          _ = 303882701 := by rw [factor_1_4]; decide
      have factor_1_6 : (10 : ZMod 478361953) ^ 76 = 156296862 := by
        calc
          (10 : ZMod 478361953) ^ 76 = (10 : ZMod 478361953) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 38 * (10 : ZMod 478361953) ^ 38 := by rw [pow_add]
          _ = 156296862 := by rw [factor_1_5]; decide
      have factor_1_7 : (10 : ZMod 478361953) ^ 152 = 218623596 := by
        calc
          (10 : ZMod 478361953) ^ 152 = (10 : ZMod 478361953) ^ (76 + 76) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 76 * (10 : ZMod 478361953) ^ 76 := by rw [pow_add]
          _ = 218623596 := by rw [factor_1_6]; decide
      have factor_1_8 : (10 : ZMod 478361953) ^ 304 = 254587113 := by
        calc
          (10 : ZMod 478361953) ^ 304 = (10 : ZMod 478361953) ^ (152 + 152) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 152 * (10 : ZMod 478361953) ^ 152 := by rw [pow_add]
          _ = 254587113 := by rw [factor_1_7]; decide
      have factor_1_9 : (10 : ZMod 478361953) ^ 608 = 72046134 := by
        calc
          (10 : ZMod 478361953) ^ 608 = (10 : ZMod 478361953) ^ (304 + 304) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 304 * (10 : ZMod 478361953) ^ 304 := by rw [pow_add]
          _ = 72046134 := by rw [factor_1_8]; decide
      have factor_1_10 : (10 : ZMod 478361953) ^ 1216 = 145949034 := by
        calc
          (10 : ZMod 478361953) ^ 1216 = (10 : ZMod 478361953) ^ (608 + 608) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 608 * (10 : ZMod 478361953) ^ 608 := by rw [pow_add]
          _ = 145949034 := by rw [factor_1_9]; decide
      have factor_1_11 : (10 : ZMod 478361953) ^ 2433 = 36200210 := by
        calc
          (10 : ZMod 478361953) ^ 2433 = (10 : ZMod 478361953) ^ (1216 + 1216 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 1216 * (10 : ZMod 478361953) ^ 1216) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 36200210 := by rw [factor_1_10]; decide
      have factor_1_12 : (10 : ZMod 478361953) ^ 4866 = 333192861 := by
        calc
          (10 : ZMod 478361953) ^ 4866 = (10 : ZMod 478361953) ^ (2433 + 2433) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 2433 * (10 : ZMod 478361953) ^ 2433 := by rw [pow_add]
          _ = 333192861 := by rw [factor_1_11]; decide
      have factor_1_13 : (10 : ZMod 478361953) ^ 9732 = 207906685 := by
        calc
          (10 : ZMod 478361953) ^ 9732 = (10 : ZMod 478361953) ^ (4866 + 4866) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 4866 * (10 : ZMod 478361953) ^ 4866 := by rw [pow_add]
          _ = 207906685 := by rw [factor_1_12]; decide
      have factor_1_14 : (10 : ZMod 478361953) ^ 19464 = 335482846 := by
        calc
          (10 : ZMod 478361953) ^ 19464 = (10 : ZMod 478361953) ^ (9732 + 9732) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 9732 * (10 : ZMod 478361953) ^ 9732 := by rw [pow_add]
          _ = 335482846 := by rw [factor_1_13]; decide
      have factor_1_15 : (10 : ZMod 478361953) ^ 38929 = 308307339 := by
        calc
          (10 : ZMod 478361953) ^ 38929 = (10 : ZMod 478361953) ^ (19464 + 19464 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 19464 * (10 : ZMod 478361953) ^ 19464) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 308307339 := by rw [factor_1_14]; decide
      have factor_1_16 : (10 : ZMod 478361953) ^ 77858 = 173621365 := by
        calc
          (10 : ZMod 478361953) ^ 77858 = (10 : ZMod 478361953) ^ (38929 + 38929) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 38929 * (10 : ZMod 478361953) ^ 38929 := by rw [pow_add]
          _ = 173621365 := by rw [factor_1_15]; decide
      have factor_1_17 : (10 : ZMod 478361953) ^ 155716 = 5575517 := by
        calc
          (10 : ZMod 478361953) ^ 155716 = (10 : ZMod 478361953) ^ (77858 + 77858) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 77858 * (10 : ZMod 478361953) ^ 77858 := by rw [pow_add]
          _ = 5575517 := by rw [factor_1_16]; decide
      have factor_1_18 : (10 : ZMod 478361953) ^ 311433 = 383015840 := by
        calc
          (10 : ZMod 478361953) ^ 311433 = (10 : ZMod 478361953) ^ (155716 + 155716 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 155716 * (10 : ZMod 478361953) ^ 155716) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 383015840 := by rw [factor_1_17]; decide
      have factor_1_19 : (10 : ZMod 478361953) ^ 622867 = 119704802 := by
        calc
          (10 : ZMod 478361953) ^ 622867 = (10 : ZMod 478361953) ^ (311433 + 311433 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 311433 * (10 : ZMod 478361953) ^ 311433) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 119704802 := by rw [factor_1_18]; decide
      have factor_1_20 : (10 : ZMod 478361953) ^ 1245734 = 121963086 := by
        calc
          (10 : ZMod 478361953) ^ 1245734 = (10 : ZMod 478361953) ^ (622867 + 622867) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 622867 * (10 : ZMod 478361953) ^ 622867 := by rw [pow_add]
          _ = 121963086 := by rw [factor_1_19]; decide
      have factor_1_21 : (10 : ZMod 478361953) ^ 2491468 = 305084732 := by
        calc
          (10 : ZMod 478361953) ^ 2491468 = (10 : ZMod 478361953) ^ (1245734 + 1245734) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 1245734 * (10 : ZMod 478361953) ^ 1245734 := by rw [pow_add]
          _ = 305084732 := by rw [factor_1_20]; decide
      have factor_1_22 : (10 : ZMod 478361953) ^ 4982937 = 91023122 := by
        calc
          (10 : ZMod 478361953) ^ 4982937 = (10 : ZMod 478361953) ^ (2491468 + 2491468 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 2491468 * (10 : ZMod 478361953) ^ 2491468) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 91023122 := by rw [factor_1_21]; decide
      have factor_1_23 : (10 : ZMod 478361953) ^ 9965874 = 282230863 := by
        calc
          (10 : ZMod 478361953) ^ 9965874 = (10 : ZMod 478361953) ^ (4982937 + 4982937) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 4982937 * (10 : ZMod 478361953) ^ 4982937 := by rw [pow_add]
          _ = 282230863 := by rw [factor_1_22]; decide
      have factor_1_24 : (10 : ZMod 478361953) ^ 19931748 = 246748003 := by
        calc
          (10 : ZMod 478361953) ^ 19931748 = (10 : ZMod 478361953) ^ (9965874 + 9965874) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 9965874 * (10 : ZMod 478361953) ^ 9965874 := by rw [pow_add]
          _ = 246748003 := by rw [factor_1_23]; decide
      have factor_1_25 : (10 : ZMod 478361953) ^ 39863496 = 323049067 := by
        calc
          (10 : ZMod 478361953) ^ 39863496 = (10 : ZMod 478361953) ^ (19931748 + 19931748) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 19931748 * (10 : ZMod 478361953) ^ 19931748 := by rw [pow_add]
          _ = 323049067 := by rw [factor_1_24]; decide
      have factor_1_26 : (10 : ZMod 478361953) ^ 79726992 = 322963864 := by
        calc
          (10 : ZMod 478361953) ^ 79726992 = (10 : ZMod 478361953) ^ (39863496 + 39863496) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 39863496 * (10 : ZMod 478361953) ^ 39863496 := by rw [pow_add]
          _ = 322963864 := by rw [factor_1_25]; decide
      have factor_1_27 : (10 : ZMod 478361953) ^ 159453984 = 322963863 := by
        calc
          (10 : ZMod 478361953) ^ 159453984 = (10 : ZMod 478361953) ^ (79726992 + 79726992) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 79726992 * (10 : ZMod 478361953) ^ 79726992 := by rw [pow_add]
          _ = 322963863 := by rw [factor_1_26]; decide
      change (10 : ZMod 478361953) ^ 159453984 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (10 : ZMod 478361953) ^ 1 = 10 := by norm_num
      have factor_2_1 : (10 : ZMod 478361953) ^ 3 = 1000 := by
        calc
          (10 : ZMod 478361953) ^ 3 = (10 : ZMod 478361953) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 1 * (10 : ZMod 478361953) ^ 1) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_2_0]; decide
      have factor_2_2 : (10 : ZMod 478361953) ^ 6 = 1000000 := by
        calc
          (10 : ZMod 478361953) ^ 6 = (10 : ZMod 478361953) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 3 * (10 : ZMod 478361953) ^ 3 := by rw [pow_add]
          _ = 1000000 := by rw [factor_2_1]; decide
      have factor_2_3 : (10 : ZMod 478361953) ^ 13 = 321734488 := by
        calc
          (10 : ZMod 478361953) ^ 13 = (10 : ZMod 478361953) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 6 * (10 : ZMod 478361953) ^ 6) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 321734488 := by rw [factor_2_2]; decide
      have factor_2_4 : (10 : ZMod 478361953) ^ 26 = 35413326 := by
        calc
          (10 : ZMod 478361953) ^ 26 = (10 : ZMod 478361953) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 13 * (10 : ZMod 478361953) ^ 13 := by rw [pow_add]
          _ = 35413326 := by rw [factor_2_3]; decide
      have factor_2_5 : (10 : ZMod 478361953) ^ 52 = 303956390 := by
        calc
          (10 : ZMod 478361953) ^ 52 = (10 : ZMod 478361953) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 26 * (10 : ZMod 478361953) ^ 26 := by rw [pow_add]
          _ = 303956390 := by rw [factor_2_4]; decide
      have factor_2_6 : (10 : ZMod 478361953) ^ 104 = 267966359 := by
        calc
          (10 : ZMod 478361953) ^ 104 = (10 : ZMod 478361953) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 52 * (10 : ZMod 478361953) ^ 52 := by rw [pow_add]
          _ = 267966359 := by rw [factor_2_5]; decide
      have factor_2_7 : (10 : ZMod 478361953) ^ 209 = 249858064 := by
        calc
          (10 : ZMod 478361953) ^ 209 = (10 : ZMod 478361953) ^ (104 + 104 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 104 * (10 : ZMod 478361953) ^ 104) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 249858064 := by rw [factor_2_6]; decide
      have factor_2_8 : (10 : ZMod 478361953) ^ 418 = 205786879 := by
        calc
          (10 : ZMod 478361953) ^ 418 = (10 : ZMod 478361953) ^ (209 + 209) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 209 * (10 : ZMod 478361953) ^ 209 := by rw [pow_add]
          _ = 205786879 := by rw [factor_2_7]; decide
      have factor_2_9 : (10 : ZMod 478361953) ^ 836 = 111262217 := by
        calc
          (10 : ZMod 478361953) ^ 836 = (10 : ZMod 478361953) ^ (418 + 418) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 418 * (10 : ZMod 478361953) ^ 418 := by rw [pow_add]
          _ = 111262217 := by rw [factor_2_8]; decide
      have factor_2_10 : (10 : ZMod 478361953) ^ 1672 = 219921696 := by
        calc
          (10 : ZMod 478361953) ^ 1672 = (10 : ZMod 478361953) ^ (836 + 836) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 836 * (10 : ZMod 478361953) ^ 836 := by rw [pow_add]
          _ = 219921696 := by rw [factor_2_9]; decide
      have factor_2_11 : (10 : ZMod 478361953) ^ 3345 = 122235852 := by
        calc
          (10 : ZMod 478361953) ^ 3345 = (10 : ZMod 478361953) ^ (1672 + 1672 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 1672 * (10 : ZMod 478361953) ^ 1672) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 122235852 := by rw [factor_2_10]; decide
      have factor_2_12 : (10 : ZMod 478361953) ^ 6691 = 102979503 := by
        calc
          (10 : ZMod 478361953) ^ 6691 = (10 : ZMod 478361953) ^ (3345 + 3345 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 3345 * (10 : ZMod 478361953) ^ 3345) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 102979503 := by rw [factor_2_11]; decide
      have factor_2_13 : (10 : ZMod 478361953) ^ 13383 = 297528454 := by
        calc
          (10 : ZMod 478361953) ^ 13383 = (10 : ZMod 478361953) ^ (6691 + 6691 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 6691 * (10 : ZMod 478361953) ^ 6691) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 297528454 := by rw [factor_2_12]; decide
      have factor_2_14 : (10 : ZMod 478361953) ^ 26766 = 137624233 := by
        calc
          (10 : ZMod 478361953) ^ 26766 = (10 : ZMod 478361953) ^ (13383 + 13383) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 13383 * (10 : ZMod 478361953) ^ 13383 := by rw [pow_add]
          _ = 137624233 := by rw [factor_2_13]; decide
      have factor_2_15 : (10 : ZMod 478361953) ^ 53532 = 350158598 := by
        calc
          (10 : ZMod 478361953) ^ 53532 = (10 : ZMod 478361953) ^ (26766 + 26766) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 26766 * (10 : ZMod 478361953) ^ 26766 := by rw [pow_add]
          _ = 350158598 := by rw [factor_2_14]; decide
      have factor_2_16 : (10 : ZMod 478361953) ^ 107064 = 181437088 := by
        calc
          (10 : ZMod 478361953) ^ 107064 = (10 : ZMod 478361953) ^ (53532 + 53532) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 53532 * (10 : ZMod 478361953) ^ 53532 := by rw [pow_add]
          _ = 181437088 := by rw [factor_2_15]; decide
      have factor_2_17 : (10 : ZMod 478361953) ^ 214128 = 81711005 := by
        calc
          (10 : ZMod 478361953) ^ 214128 = (10 : ZMod 478361953) ^ (107064 + 107064) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 107064 * (10 : ZMod 478361953) ^ 107064 := by rw [pow_add]
          _ = 81711005 := by rw [factor_2_16]; decide
      have factor_2_18 : (10 : ZMod 478361953) ^ 428256 = 172031731 := by
        calc
          (10 : ZMod 478361953) ^ 428256 = (10 : ZMod 478361953) ^ (214128 + 214128) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 214128 * (10 : ZMod 478361953) ^ 214128 := by rw [pow_add]
          _ = 172031731 := by rw [factor_2_17]; decide
      change (10 : ZMod 478361953) ^ 428256 ≠ 1
      rw [factor_2_18]
      decide
    ·
      have factor_3_0 : (10 : ZMod 478361953) ^ 1 = 10 := by norm_num
      have factor_3_1 : (10 : ZMod 478361953) ^ 2 = 100 := by
        calc
          (10 : ZMod 478361953) ^ 2 = (10 : ZMod 478361953) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 1 * (10 : ZMod 478361953) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_3_0]; decide
      have factor_3_2 : (10 : ZMod 478361953) ^ 4 = 10000 := by
        calc
          (10 : ZMod 478361953) ^ 4 = (10 : ZMod 478361953) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 2 * (10 : ZMod 478361953) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [factor_3_1]; decide
      have factor_3_3 : (10 : ZMod 478361953) ^ 9 = 43276094 := by
        calc
          (10 : ZMod 478361953) ^ 9 = (10 : ZMod 478361953) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 4 * (10 : ZMod 478361953) ^ 4) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 43276094 := by rw [factor_3_2]; decide
      have factor_3_4 : (10 : ZMod 478361953) ^ 19 = 197461025 := by
        calc
          (10 : ZMod 478361953) ^ 19 = (10 : ZMod 478361953) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 9 * (10 : ZMod 478361953) ^ 9) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 197461025 := by rw [factor_3_3]; decide
      have factor_3_5 : (10 : ZMod 478361953) ^ 39 = 168655292 := by
        calc
          (10 : ZMod 478361953) ^ 39 = (10 : ZMod 478361953) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 19 * (10 : ZMod 478361953) ^ 19) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 168655292 := by rw [factor_3_4]; decide
      have factor_3_6 : (10 : ZMod 478361953) ^ 78 = 322103704 := by
        calc
          (10 : ZMod 478361953) ^ 78 = (10 : ZMod 478361953) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 39 * (10 : ZMod 478361953) ^ 39 := by rw [pow_add]
          _ = 322103704 := by rw [factor_3_5]; decide
      have factor_3_7 : (10 : ZMod 478361953) ^ 157 = 261623994 := by
        calc
          (10 : ZMod 478361953) ^ 157 = (10 : ZMod 478361953) ^ (78 + 78 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 78 * (10 : ZMod 478361953) ^ 78) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 261623994 := by rw [factor_3_6]; decide
      have factor_3_8 : (10 : ZMod 478361953) ^ 314 = 88313233 := by
        calc
          (10 : ZMod 478361953) ^ 314 = (10 : ZMod 478361953) ^ (157 + 157) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 157 * (10 : ZMod 478361953) ^ 157 := by rw [pow_add]
          _ = 88313233 := by rw [factor_3_7]; decide
      have factor_3_9 : (10 : ZMod 478361953) ^ 628 = 447065605 := by
        calc
          (10 : ZMod 478361953) ^ 628 = (10 : ZMod 478361953) ^ (314 + 314) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 314 * (10 : ZMod 478361953) ^ 314 := by rw [pow_add]
          _ = 447065605 := by rw [factor_3_8]; decide
      have factor_3_10 : (10 : ZMod 478361953) ^ 1256 = 470149061 := by
        calc
          (10 : ZMod 478361953) ^ 1256 = (10 : ZMod 478361953) ^ (628 + 628) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 628 * (10 : ZMod 478361953) ^ 628 := by rw [pow_add]
          _ = 470149061 := by rw [factor_3_9]; decide
      have factor_3_11 : (10 : ZMod 478361953) ^ 2513 = 243123131 := by
        calc
          (10 : ZMod 478361953) ^ 2513 = (10 : ZMod 478361953) ^ (1256 + 1256 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 1256 * (10 : ZMod 478361953) ^ 1256) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 243123131 := by rw [factor_3_10]; decide
      have factor_3_12 : (10 : ZMod 478361953) ^ 5026 = 396106224 := by
        calc
          (10 : ZMod 478361953) ^ 5026 = (10 : ZMod 478361953) ^ (2513 + 2513) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 2513 * (10 : ZMod 478361953) ^ 2513 := by rw [pow_add]
          _ = 396106224 := by rw [factor_3_11]; decide
      have factor_3_13 : (10 : ZMod 478361953) ^ 10053 = 92230956 := by
        calc
          (10 : ZMod 478361953) ^ 10053 = (10 : ZMod 478361953) ^ (5026 + 5026 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = ((10 : ZMod 478361953) ^ 5026 * (10 : ZMod 478361953) ^ 5026) * (10 : ZMod 478361953) := by rw [pow_succ, pow_add]
          _ = 92230956 := by rw [factor_3_12]; decide
      have factor_3_14 : (10 : ZMod 478361953) ^ 20106 = 320815050 := by
        calc
          (10 : ZMod 478361953) ^ 20106 = (10 : ZMod 478361953) ^ (10053 + 10053) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 10053 * (10 : ZMod 478361953) ^ 10053 := by rw [pow_add]
          _ = 320815050 := by rw [factor_3_13]; decide
      have factor_3_15 : (10 : ZMod 478361953) ^ 40212 = 239039930 := by
        calc
          (10 : ZMod 478361953) ^ 40212 = (10 : ZMod 478361953) ^ (20106 + 20106) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 20106 * (10 : ZMod 478361953) ^ 20106 := by rw [pow_add]
          _ = 239039930 := by rw [factor_3_14]; decide
      have factor_3_16 : (10 : ZMod 478361953) ^ 80424 = 161684601 := by
        calc
          (10 : ZMod 478361953) ^ 80424 = (10 : ZMod 478361953) ^ (40212 + 40212) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 40212 * (10 : ZMod 478361953) ^ 40212 := by rw [pow_add]
          _ = 161684601 := by rw [factor_3_15]; decide
      have factor_3_17 : (10 : ZMod 478361953) ^ 160848 = 154889130 := by
        calc
          (10 : ZMod 478361953) ^ 160848 = (10 : ZMod 478361953) ^ (80424 + 80424) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 80424 * (10 : ZMod 478361953) ^ 80424 := by rw [pow_add]
          _ = 154889130 := by rw [factor_3_16]; decide
      have factor_3_18 : (10 : ZMod 478361953) ^ 321696 = 395260544 := by
        calc
          (10 : ZMod 478361953) ^ 321696 = (10 : ZMod 478361953) ^ (160848 + 160848) :=
            congrArg (fun n : ℕ => (10 : ZMod 478361953) ^ n) (by norm_num)
          _ = (10 : ZMod 478361953) ^ 160848 * (10 : ZMod 478361953) ^ 160848 := by rw [pow_add]
          _ = 395260544 := by rw [factor_3_17]; decide
      change (10 : ZMod 478361953) ^ 321696 ≠ 1
      rw [factor_3_18]
      decide

#print axioms prime_lucas_478361953

end TotientTailPeriodKiller
end Erdos249257
