import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_5100359321 : Nat.Prime 5100359321 := by
  apply lucas_primality 5100359321 (6 : ZMod 5100359321)
  ·
      have fermat_0 : (6 : ZMod 5100359321) ^ 1 = 6 := by norm_num
      have fermat_1 : (6 : ZMod 5100359321) ^ 2 = 36 := by
        calc
          (6 : ZMod 5100359321) ^ 2 = (6 : ZMod 5100359321) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 1 * (6 : ZMod 5100359321) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [fermat_0]; decide
      have fermat_2 : (6 : ZMod 5100359321) ^ 4 = 1296 := by
        calc
          (6 : ZMod 5100359321) ^ 4 = (6 : ZMod 5100359321) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 2 * (6 : ZMod 5100359321) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [fermat_1]; decide
      have fermat_3 : (6 : ZMod 5100359321) ^ 9 = 10077696 := by
        calc
          (6 : ZMod 5100359321) ^ 9 = (6 : ZMod 5100359321) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 4 * (6 : ZMod 5100359321) ^ 4) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 10077696 := by rw [fermat_2]; decide
      have fermat_4 : (6 : ZMod 5100359321) ^ 19 = 4510852663 := by
        calc
          (6 : ZMod 5100359321) ^ 19 = (6 : ZMod 5100359321) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 9 * (6 : ZMod 5100359321) ^ 9) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 4510852663 := by rw [fermat_3]; decide
      have fermat_5 : (6 : ZMod 5100359321) ^ 38 = 1829595001 := by
        calc
          (6 : ZMod 5100359321) ^ 38 = (6 : ZMod 5100359321) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 19 * (6 : ZMod 5100359321) ^ 19 := by rw [pow_add]
          _ = 1829595001 := by rw [fermat_4]; decide
      have fermat_6 : (6 : ZMod 5100359321) ^ 76 = 1245378517 := by
        calc
          (6 : ZMod 5100359321) ^ 76 = (6 : ZMod 5100359321) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 38 * (6 : ZMod 5100359321) ^ 38 := by rw [pow_add]
          _ = 1245378517 := by rw [fermat_5]; decide
      have fermat_7 : (6 : ZMod 5100359321) ^ 152 = 1825707130 := by
        calc
          (6 : ZMod 5100359321) ^ 152 = (6 : ZMod 5100359321) ^ (76 + 76) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 76 * (6 : ZMod 5100359321) ^ 76 := by rw [pow_add]
          _ = 1825707130 := by rw [fermat_6]; decide
      have fermat_8 : (6 : ZMod 5100359321) ^ 304 = 3485219198 := by
        calc
          (6 : ZMod 5100359321) ^ 304 = (6 : ZMod 5100359321) ^ (152 + 152) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 152 * (6 : ZMod 5100359321) ^ 152 := by rw [pow_add]
          _ = 3485219198 := by rw [fermat_7]; decide
      have fermat_9 : (6 : ZMod 5100359321) ^ 608 = 2335723470 := by
        calc
          (6 : ZMod 5100359321) ^ 608 = (6 : ZMod 5100359321) ^ (304 + 304) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 304 * (6 : ZMod 5100359321) ^ 304 := by rw [pow_add]
          _ = 2335723470 := by rw [fermat_8]; decide
      have fermat_10 : (6 : ZMod 5100359321) ^ 1216 = 1564507123 := by
        calc
          (6 : ZMod 5100359321) ^ 1216 = (6 : ZMod 5100359321) ^ (608 + 608) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 608 * (6 : ZMod 5100359321) ^ 608 := by rw [pow_add]
          _ = 1564507123 := by rw [fermat_9]; decide
      have fermat_11 : (6 : ZMod 5100359321) ^ 2432 = 4354112389 := by
        calc
          (6 : ZMod 5100359321) ^ 2432 = (6 : ZMod 5100359321) ^ (1216 + 1216) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 1216 * (6 : ZMod 5100359321) ^ 1216 := by rw [pow_add]
          _ = 4354112389 := by rw [fermat_10]; decide
      have fermat_12 : (6 : ZMod 5100359321) ^ 4864 = 1632780521 := by
        calc
          (6 : ZMod 5100359321) ^ 4864 = (6 : ZMod 5100359321) ^ (2432 + 2432) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 2432 * (6 : ZMod 5100359321) ^ 2432 := by rw [pow_add]
          _ = 1632780521 := by rw [fermat_11]; decide
      have fermat_13 : (6 : ZMod 5100359321) ^ 9728 = 4155249616 := by
        calc
          (6 : ZMod 5100359321) ^ 9728 = (6 : ZMod 5100359321) ^ (4864 + 4864) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 4864 * (6 : ZMod 5100359321) ^ 4864 := by rw [pow_add]
          _ = 4155249616 := by rw [fermat_12]; decide
      have fermat_14 : (6 : ZMod 5100359321) ^ 19456 = 145712565 := by
        calc
          (6 : ZMod 5100359321) ^ 19456 = (6 : ZMod 5100359321) ^ (9728 + 9728) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 9728 * (6 : ZMod 5100359321) ^ 9728 := by rw [pow_add]
          _ = 145712565 := by rw [fermat_13]; decide
      have fermat_15 : (6 : ZMod 5100359321) ^ 38912 = 3491189992 := by
        calc
          (6 : ZMod 5100359321) ^ 38912 = (6 : ZMod 5100359321) ^ (19456 + 19456) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 19456 * (6 : ZMod 5100359321) ^ 19456 := by rw [pow_add]
          _ = 3491189992 := by rw [fermat_14]; decide
      have fermat_16 : (6 : ZMod 5100359321) ^ 77825 = 1136415658 := by
        calc
          (6 : ZMod 5100359321) ^ 77825 = (6 : ZMod 5100359321) ^ (38912 + 38912 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 38912 * (6 : ZMod 5100359321) ^ 38912) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 1136415658 := by rw [fermat_15]; decide
      have fermat_17 : (6 : ZMod 5100359321) ^ 155650 = 887389127 := by
        calc
          (6 : ZMod 5100359321) ^ 155650 = (6 : ZMod 5100359321) ^ (77825 + 77825) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 77825 * (6 : ZMod 5100359321) ^ 77825 := by rw [pow_add]
          _ = 887389127 := by rw [fermat_16]; decide
      have fermat_18 : (6 : ZMod 5100359321) ^ 311301 = 3556963544 := by
        calc
          (6 : ZMod 5100359321) ^ 311301 = (6 : ZMod 5100359321) ^ (155650 + 155650 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 155650 * (6 : ZMod 5100359321) ^ 155650) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 3556963544 := by rw [fermat_17]; decide
      have fermat_19 : (6 : ZMod 5100359321) ^ 622602 = 2672861263 := by
        calc
          (6 : ZMod 5100359321) ^ 622602 = (6 : ZMod 5100359321) ^ (311301 + 311301) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 311301 * (6 : ZMod 5100359321) ^ 311301 := by rw [pow_add]
          _ = 2672861263 := by rw [fermat_18]; decide
      have fermat_20 : (6 : ZMod 5100359321) ^ 1245204 = 1587915572 := by
        calc
          (6 : ZMod 5100359321) ^ 1245204 = (6 : ZMod 5100359321) ^ (622602 + 622602) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 622602 * (6 : ZMod 5100359321) ^ 622602 := by rw [pow_add]
          _ = 1587915572 := by rw [fermat_19]; decide
      have fermat_21 : (6 : ZMod 5100359321) ^ 2490409 = 2318709978 := by
        calc
          (6 : ZMod 5100359321) ^ 2490409 = (6 : ZMod 5100359321) ^ (1245204 + 1245204 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 1245204 * (6 : ZMod 5100359321) ^ 1245204) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 2318709978 := by rw [fermat_20]; decide
      have fermat_22 : (6 : ZMod 5100359321) ^ 4980819 = 3295887106 := by
        calc
          (6 : ZMod 5100359321) ^ 4980819 = (6 : ZMod 5100359321) ^ (2490409 + 2490409 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 2490409 * (6 : ZMod 5100359321) ^ 2490409) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 3295887106 := by rw [fermat_21]; decide
      have fermat_23 : (6 : ZMod 5100359321) ^ 9961639 = 3101881924 := by
        calc
          (6 : ZMod 5100359321) ^ 9961639 = (6 : ZMod 5100359321) ^ (4980819 + 4980819 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 4980819 * (6 : ZMod 5100359321) ^ 4980819) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 3101881924 := by rw [fermat_22]; decide
      have fermat_24 : (6 : ZMod 5100359321) ^ 19923278 = 3689301599 := by
        calc
          (6 : ZMod 5100359321) ^ 19923278 = (6 : ZMod 5100359321) ^ (9961639 + 9961639) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 9961639 * (6 : ZMod 5100359321) ^ 9961639 := by rw [pow_add]
          _ = 3689301599 := by rw [fermat_23]; decide
      have fermat_25 : (6 : ZMod 5100359321) ^ 39846557 = 4726546610 := by
        calc
          (6 : ZMod 5100359321) ^ 39846557 = (6 : ZMod 5100359321) ^ (19923278 + 19923278 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 19923278 * (6 : ZMod 5100359321) ^ 19923278) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 4726546610 := by rw [fermat_24]; decide
      have fermat_26 : (6 : ZMod 5100359321) ^ 79693114 = 1089278567 := by
        calc
          (6 : ZMod 5100359321) ^ 79693114 = (6 : ZMod 5100359321) ^ (39846557 + 39846557) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 39846557 * (6 : ZMod 5100359321) ^ 39846557 := by rw [pow_add]
          _ = 1089278567 := by rw [fermat_25]; decide
      have fermat_27 : (6 : ZMod 5100359321) ^ 159386228 = 3683017611 := by
        calc
          (6 : ZMod 5100359321) ^ 159386228 = (6 : ZMod 5100359321) ^ (79693114 + 79693114) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 79693114 * (6 : ZMod 5100359321) ^ 79693114 := by rw [pow_add]
          _ = 3683017611 := by rw [fermat_26]; decide
      have fermat_28 : (6 : ZMod 5100359321) ^ 318772457 = 2538827868 := by
        calc
          (6 : ZMod 5100359321) ^ 318772457 = (6 : ZMod 5100359321) ^ (159386228 + 159386228 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 159386228 * (6 : ZMod 5100359321) ^ 159386228) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 2538827868 := by rw [fermat_27]; decide
      have fermat_29 : (6 : ZMod 5100359321) ^ 637544915 = 2937409645 := by
        calc
          (6 : ZMod 5100359321) ^ 637544915 = (6 : ZMod 5100359321) ^ (318772457 + 318772457 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 318772457 * (6 : ZMod 5100359321) ^ 318772457) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 2937409645 := by rw [fermat_28]; decide
      have fermat_30 : (6 : ZMod 5100359321) ^ 1275089830 = 4630593258 := by
        calc
          (6 : ZMod 5100359321) ^ 1275089830 = (6 : ZMod 5100359321) ^ (637544915 + 637544915) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 637544915 * (6 : ZMod 5100359321) ^ 637544915 := by rw [pow_add]
          _ = 4630593258 := by rw [fermat_29]; decide
      have fermat_31 : (6 : ZMod 5100359321) ^ 2550179660 = 5100359320 := by
        calc
          (6 : ZMod 5100359321) ^ 2550179660 = (6 : ZMod 5100359321) ^ (1275089830 + 1275089830) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 1275089830 * (6 : ZMod 5100359321) ^ 1275089830 := by rw [pow_add]
          _ = 5100359320 := by rw [fermat_30]; decide
      have fermat_32 : (6 : ZMod 5100359321) ^ 5100359320 = 1 := by
        calc
          (6 : ZMod 5100359321) ^ 5100359320 = (6 : ZMod 5100359321) ^ (2550179660 + 2550179660) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 2550179660 * (6 : ZMod 5100359321) ^ 2550179660 := by rw [pow_add]
          _ = 1 := by rw [fermat_31]; decide
      simpa using fermat_32
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (7, 1), (31, 1), (587599, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (7, 1), (31, 1), (587599, 1)] : List FactorBlock).map factorBlockValue).prod = 5100359321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (6 : ZMod 5100359321) ^ 1 = 6 := by norm_num
      have factor_0_1 : (6 : ZMod 5100359321) ^ 2 = 36 := by
        calc
          (6 : ZMod 5100359321) ^ 2 = (6 : ZMod 5100359321) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 1 * (6 : ZMod 5100359321) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_0_0]; decide
      have factor_0_2 : (6 : ZMod 5100359321) ^ 4 = 1296 := by
        calc
          (6 : ZMod 5100359321) ^ 4 = (6 : ZMod 5100359321) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 2 * (6 : ZMod 5100359321) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_0_1]; decide
      have factor_0_3 : (6 : ZMod 5100359321) ^ 9 = 10077696 := by
        calc
          (6 : ZMod 5100359321) ^ 9 = (6 : ZMod 5100359321) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 4 * (6 : ZMod 5100359321) ^ 4) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 10077696 := by rw [factor_0_2]; decide
      have factor_0_4 : (6 : ZMod 5100359321) ^ 19 = 4510852663 := by
        calc
          (6 : ZMod 5100359321) ^ 19 = (6 : ZMod 5100359321) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 9 * (6 : ZMod 5100359321) ^ 9) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 4510852663 := by rw [factor_0_3]; decide
      have factor_0_5 : (6 : ZMod 5100359321) ^ 38 = 1829595001 := by
        calc
          (6 : ZMod 5100359321) ^ 38 = (6 : ZMod 5100359321) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 19 * (6 : ZMod 5100359321) ^ 19 := by rw [pow_add]
          _ = 1829595001 := by rw [factor_0_4]; decide
      have factor_0_6 : (6 : ZMod 5100359321) ^ 76 = 1245378517 := by
        calc
          (6 : ZMod 5100359321) ^ 76 = (6 : ZMod 5100359321) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 38 * (6 : ZMod 5100359321) ^ 38 := by rw [pow_add]
          _ = 1245378517 := by rw [factor_0_5]; decide
      have factor_0_7 : (6 : ZMod 5100359321) ^ 152 = 1825707130 := by
        calc
          (6 : ZMod 5100359321) ^ 152 = (6 : ZMod 5100359321) ^ (76 + 76) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 76 * (6 : ZMod 5100359321) ^ 76 := by rw [pow_add]
          _ = 1825707130 := by rw [factor_0_6]; decide
      have factor_0_8 : (6 : ZMod 5100359321) ^ 304 = 3485219198 := by
        calc
          (6 : ZMod 5100359321) ^ 304 = (6 : ZMod 5100359321) ^ (152 + 152) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 152 * (6 : ZMod 5100359321) ^ 152 := by rw [pow_add]
          _ = 3485219198 := by rw [factor_0_7]; decide
      have factor_0_9 : (6 : ZMod 5100359321) ^ 608 = 2335723470 := by
        calc
          (6 : ZMod 5100359321) ^ 608 = (6 : ZMod 5100359321) ^ (304 + 304) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 304 * (6 : ZMod 5100359321) ^ 304 := by rw [pow_add]
          _ = 2335723470 := by rw [factor_0_8]; decide
      have factor_0_10 : (6 : ZMod 5100359321) ^ 1216 = 1564507123 := by
        calc
          (6 : ZMod 5100359321) ^ 1216 = (6 : ZMod 5100359321) ^ (608 + 608) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 608 * (6 : ZMod 5100359321) ^ 608 := by rw [pow_add]
          _ = 1564507123 := by rw [factor_0_9]; decide
      have factor_0_11 : (6 : ZMod 5100359321) ^ 2432 = 4354112389 := by
        calc
          (6 : ZMod 5100359321) ^ 2432 = (6 : ZMod 5100359321) ^ (1216 + 1216) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 1216 * (6 : ZMod 5100359321) ^ 1216 := by rw [pow_add]
          _ = 4354112389 := by rw [factor_0_10]; decide
      have factor_0_12 : (6 : ZMod 5100359321) ^ 4864 = 1632780521 := by
        calc
          (6 : ZMod 5100359321) ^ 4864 = (6 : ZMod 5100359321) ^ (2432 + 2432) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 2432 * (6 : ZMod 5100359321) ^ 2432 := by rw [pow_add]
          _ = 1632780521 := by rw [factor_0_11]; decide
      have factor_0_13 : (6 : ZMod 5100359321) ^ 9728 = 4155249616 := by
        calc
          (6 : ZMod 5100359321) ^ 9728 = (6 : ZMod 5100359321) ^ (4864 + 4864) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 4864 * (6 : ZMod 5100359321) ^ 4864 := by rw [pow_add]
          _ = 4155249616 := by rw [factor_0_12]; decide
      have factor_0_14 : (6 : ZMod 5100359321) ^ 19456 = 145712565 := by
        calc
          (6 : ZMod 5100359321) ^ 19456 = (6 : ZMod 5100359321) ^ (9728 + 9728) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 9728 * (6 : ZMod 5100359321) ^ 9728 := by rw [pow_add]
          _ = 145712565 := by rw [factor_0_13]; decide
      have factor_0_15 : (6 : ZMod 5100359321) ^ 38912 = 3491189992 := by
        calc
          (6 : ZMod 5100359321) ^ 38912 = (6 : ZMod 5100359321) ^ (19456 + 19456) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 19456 * (6 : ZMod 5100359321) ^ 19456 := by rw [pow_add]
          _ = 3491189992 := by rw [factor_0_14]; decide
      have factor_0_16 : (6 : ZMod 5100359321) ^ 77825 = 1136415658 := by
        calc
          (6 : ZMod 5100359321) ^ 77825 = (6 : ZMod 5100359321) ^ (38912 + 38912 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 38912 * (6 : ZMod 5100359321) ^ 38912) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 1136415658 := by rw [factor_0_15]; decide
      have factor_0_17 : (6 : ZMod 5100359321) ^ 155650 = 887389127 := by
        calc
          (6 : ZMod 5100359321) ^ 155650 = (6 : ZMod 5100359321) ^ (77825 + 77825) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 77825 * (6 : ZMod 5100359321) ^ 77825 := by rw [pow_add]
          _ = 887389127 := by rw [factor_0_16]; decide
      have factor_0_18 : (6 : ZMod 5100359321) ^ 311301 = 3556963544 := by
        calc
          (6 : ZMod 5100359321) ^ 311301 = (6 : ZMod 5100359321) ^ (155650 + 155650 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 155650 * (6 : ZMod 5100359321) ^ 155650) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 3556963544 := by rw [factor_0_17]; decide
      have factor_0_19 : (6 : ZMod 5100359321) ^ 622602 = 2672861263 := by
        calc
          (6 : ZMod 5100359321) ^ 622602 = (6 : ZMod 5100359321) ^ (311301 + 311301) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 311301 * (6 : ZMod 5100359321) ^ 311301 := by rw [pow_add]
          _ = 2672861263 := by rw [factor_0_18]; decide
      have factor_0_20 : (6 : ZMod 5100359321) ^ 1245204 = 1587915572 := by
        calc
          (6 : ZMod 5100359321) ^ 1245204 = (6 : ZMod 5100359321) ^ (622602 + 622602) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 622602 * (6 : ZMod 5100359321) ^ 622602 := by rw [pow_add]
          _ = 1587915572 := by rw [factor_0_19]; decide
      have factor_0_21 : (6 : ZMod 5100359321) ^ 2490409 = 2318709978 := by
        calc
          (6 : ZMod 5100359321) ^ 2490409 = (6 : ZMod 5100359321) ^ (1245204 + 1245204 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 1245204 * (6 : ZMod 5100359321) ^ 1245204) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 2318709978 := by rw [factor_0_20]; decide
      have factor_0_22 : (6 : ZMod 5100359321) ^ 4980819 = 3295887106 := by
        calc
          (6 : ZMod 5100359321) ^ 4980819 = (6 : ZMod 5100359321) ^ (2490409 + 2490409 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 2490409 * (6 : ZMod 5100359321) ^ 2490409) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 3295887106 := by rw [factor_0_21]; decide
      have factor_0_23 : (6 : ZMod 5100359321) ^ 9961639 = 3101881924 := by
        calc
          (6 : ZMod 5100359321) ^ 9961639 = (6 : ZMod 5100359321) ^ (4980819 + 4980819 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 4980819 * (6 : ZMod 5100359321) ^ 4980819) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 3101881924 := by rw [factor_0_22]; decide
      have factor_0_24 : (6 : ZMod 5100359321) ^ 19923278 = 3689301599 := by
        calc
          (6 : ZMod 5100359321) ^ 19923278 = (6 : ZMod 5100359321) ^ (9961639 + 9961639) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 9961639 * (6 : ZMod 5100359321) ^ 9961639 := by rw [pow_add]
          _ = 3689301599 := by rw [factor_0_23]; decide
      have factor_0_25 : (6 : ZMod 5100359321) ^ 39846557 = 4726546610 := by
        calc
          (6 : ZMod 5100359321) ^ 39846557 = (6 : ZMod 5100359321) ^ (19923278 + 19923278 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 19923278 * (6 : ZMod 5100359321) ^ 19923278) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 4726546610 := by rw [factor_0_24]; decide
      have factor_0_26 : (6 : ZMod 5100359321) ^ 79693114 = 1089278567 := by
        calc
          (6 : ZMod 5100359321) ^ 79693114 = (6 : ZMod 5100359321) ^ (39846557 + 39846557) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 39846557 * (6 : ZMod 5100359321) ^ 39846557 := by rw [pow_add]
          _ = 1089278567 := by rw [factor_0_25]; decide
      have factor_0_27 : (6 : ZMod 5100359321) ^ 159386228 = 3683017611 := by
        calc
          (6 : ZMod 5100359321) ^ 159386228 = (6 : ZMod 5100359321) ^ (79693114 + 79693114) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 79693114 * (6 : ZMod 5100359321) ^ 79693114 := by rw [pow_add]
          _ = 3683017611 := by rw [factor_0_26]; decide
      have factor_0_28 : (6 : ZMod 5100359321) ^ 318772457 = 2538827868 := by
        calc
          (6 : ZMod 5100359321) ^ 318772457 = (6 : ZMod 5100359321) ^ (159386228 + 159386228 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 159386228 * (6 : ZMod 5100359321) ^ 159386228) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 2538827868 := by rw [factor_0_27]; decide
      have factor_0_29 : (6 : ZMod 5100359321) ^ 637544915 = 2937409645 := by
        calc
          (6 : ZMod 5100359321) ^ 637544915 = (6 : ZMod 5100359321) ^ (318772457 + 318772457 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 318772457 * (6 : ZMod 5100359321) ^ 318772457) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 2937409645 := by rw [factor_0_28]; decide
      have factor_0_30 : (6 : ZMod 5100359321) ^ 1275089830 = 4630593258 := by
        calc
          (6 : ZMod 5100359321) ^ 1275089830 = (6 : ZMod 5100359321) ^ (637544915 + 637544915) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 637544915 * (6 : ZMod 5100359321) ^ 637544915 := by rw [pow_add]
          _ = 4630593258 := by rw [factor_0_29]; decide
      have factor_0_31 : (6 : ZMod 5100359321) ^ 2550179660 = 5100359320 := by
        calc
          (6 : ZMod 5100359321) ^ 2550179660 = (6 : ZMod 5100359321) ^ (1275089830 + 1275089830) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 1275089830 * (6 : ZMod 5100359321) ^ 1275089830 := by rw [pow_add]
          _ = 5100359320 := by rw [factor_0_30]; decide
      change (6 : ZMod 5100359321) ^ 2550179660 ≠ 1
      rw [factor_0_31]
      decide
    ·
      have factor_1_0 : (6 : ZMod 5100359321) ^ 1 = 6 := by norm_num
      have factor_1_1 : (6 : ZMod 5100359321) ^ 3 = 216 := by
        calc
          (6 : ZMod 5100359321) ^ 3 = (6 : ZMod 5100359321) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 1 * (6 : ZMod 5100359321) ^ 1) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_1_0]; decide
      have factor_1_2 : (6 : ZMod 5100359321) ^ 7 = 279936 := by
        calc
          (6 : ZMod 5100359321) ^ 7 = (6 : ZMod 5100359321) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 3 * (6 : ZMod 5100359321) ^ 3) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 279936 := by rw [factor_1_1]; decide
      have factor_1_3 : (6 : ZMod 5100359321) ^ 15 = 951927044 := by
        calc
          (6 : ZMod 5100359321) ^ 15 = (6 : ZMod 5100359321) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 7 * (6 : ZMod 5100359321) ^ 7) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 951927044 := by rw [factor_1_2]; decide
      have factor_1_4 : (6 : ZMod 5100359321) ^ 30 = 1345731863 := by
        calc
          (6 : ZMod 5100359321) ^ 30 = (6 : ZMod 5100359321) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 15 * (6 : ZMod 5100359321) ^ 15 := by rw [pow_add]
          _ = 1345731863 := by rw [factor_1_3]; decide
      have factor_1_5 : (6 : ZMod 5100359321) ^ 60 = 2905426795 := by
        calc
          (6 : ZMod 5100359321) ^ 60 = (6 : ZMod 5100359321) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 30 * (6 : ZMod 5100359321) ^ 30 := by rw [pow_add]
          _ = 2905426795 := by rw [factor_1_4]; decide
      have factor_1_6 : (6 : ZMod 5100359321) ^ 121 = 2108514094 := by
        calc
          (6 : ZMod 5100359321) ^ 121 = (6 : ZMod 5100359321) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 60 * (6 : ZMod 5100359321) ^ 60) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 2108514094 := by rw [factor_1_5]; decide
      have factor_1_7 : (6 : ZMod 5100359321) ^ 243 = 2440003081 := by
        calc
          (6 : ZMod 5100359321) ^ 243 = (6 : ZMod 5100359321) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 121 * (6 : ZMod 5100359321) ^ 121) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 2440003081 := by rw [factor_1_6]; decide
      have factor_1_8 : (6 : ZMod 5100359321) ^ 486 = 1809812706 := by
        calc
          (6 : ZMod 5100359321) ^ 486 = (6 : ZMod 5100359321) ^ (243 + 243) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 243 * (6 : ZMod 5100359321) ^ 243 := by rw [pow_add]
          _ = 1809812706 := by rw [factor_1_7]; decide
      have factor_1_9 : (6 : ZMod 5100359321) ^ 972 = 76538308 := by
        calc
          (6 : ZMod 5100359321) ^ 972 = (6 : ZMod 5100359321) ^ (486 + 486) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 486 * (6 : ZMod 5100359321) ^ 486 := by rw [pow_add]
          _ = 76538308 := by rw [factor_1_8]; decide
      have factor_1_10 : (6 : ZMod 5100359321) ^ 1945 = 3220325253 := by
        calc
          (6 : ZMod 5100359321) ^ 1945 = (6 : ZMod 5100359321) ^ (972 + 972 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 972 * (6 : ZMod 5100359321) ^ 972) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 3220325253 := by rw [factor_1_9]; decide
      have factor_1_11 : (6 : ZMod 5100359321) ^ 3891 = 3365786986 := by
        calc
          (6 : ZMod 5100359321) ^ 3891 = (6 : ZMod 5100359321) ^ (1945 + 1945 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 1945 * (6 : ZMod 5100359321) ^ 1945) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 3365786986 := by rw [factor_1_10]; decide
      have factor_1_12 : (6 : ZMod 5100359321) ^ 7782 = 126273735 := by
        calc
          (6 : ZMod 5100359321) ^ 7782 = (6 : ZMod 5100359321) ^ (3891 + 3891) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 3891 * (6 : ZMod 5100359321) ^ 3891 := by rw [pow_add]
          _ = 126273735 := by rw [factor_1_11]; decide
      have factor_1_13 : (6 : ZMod 5100359321) ^ 15565 = 117010022 := by
        calc
          (6 : ZMod 5100359321) ^ 15565 = (6 : ZMod 5100359321) ^ (7782 + 7782 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 7782 * (6 : ZMod 5100359321) ^ 7782) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 117010022 := by rw [factor_1_12]; decide
      have factor_1_14 : (6 : ZMod 5100359321) ^ 31130 = 1891459936 := by
        calc
          (6 : ZMod 5100359321) ^ 31130 = (6 : ZMod 5100359321) ^ (15565 + 15565) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 15565 * (6 : ZMod 5100359321) ^ 15565 := by rw [pow_add]
          _ = 1891459936 := by rw [factor_1_13]; decide
      have factor_1_15 : (6 : ZMod 5100359321) ^ 62260 = 2434645024 := by
        calc
          (6 : ZMod 5100359321) ^ 62260 = (6 : ZMod 5100359321) ^ (31130 + 31130) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 31130 * (6 : ZMod 5100359321) ^ 31130 := by rw [pow_add]
          _ = 2434645024 := by rw [factor_1_14]; decide
      have factor_1_16 : (6 : ZMod 5100359321) ^ 124520 = 3670281103 := by
        calc
          (6 : ZMod 5100359321) ^ 124520 = (6 : ZMod 5100359321) ^ (62260 + 62260) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 62260 * (6 : ZMod 5100359321) ^ 62260 := by rw [pow_add]
          _ = 3670281103 := by rw [factor_1_15]; decide
      have factor_1_17 : (6 : ZMod 5100359321) ^ 249040 = 557749766 := by
        calc
          (6 : ZMod 5100359321) ^ 249040 = (6 : ZMod 5100359321) ^ (124520 + 124520) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 124520 * (6 : ZMod 5100359321) ^ 124520 := by rw [pow_add]
          _ = 557749766 := by rw [factor_1_16]; decide
      have factor_1_18 : (6 : ZMod 5100359321) ^ 498081 = 4542080001 := by
        calc
          (6 : ZMod 5100359321) ^ 498081 = (6 : ZMod 5100359321) ^ (249040 + 249040 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 249040 * (6 : ZMod 5100359321) ^ 249040) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 4542080001 := by rw [factor_1_17]; decide
      have factor_1_19 : (6 : ZMod 5100359321) ^ 996163 = 1426315862 := by
        calc
          (6 : ZMod 5100359321) ^ 996163 = (6 : ZMod 5100359321) ^ (498081 + 498081 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 498081 * (6 : ZMod 5100359321) ^ 498081) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 1426315862 := by rw [factor_1_18]; decide
      have factor_1_20 : (6 : ZMod 5100359321) ^ 1992327 = 4584014486 := by
        calc
          (6 : ZMod 5100359321) ^ 1992327 = (6 : ZMod 5100359321) ^ (996163 + 996163 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 996163 * (6 : ZMod 5100359321) ^ 996163) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 4584014486 := by rw [factor_1_19]; decide
      have factor_1_21 : (6 : ZMod 5100359321) ^ 3984655 = 3184588485 := by
        calc
          (6 : ZMod 5100359321) ^ 3984655 = (6 : ZMod 5100359321) ^ (1992327 + 1992327 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 1992327 * (6 : ZMod 5100359321) ^ 1992327) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 3184588485 := by rw [factor_1_20]; decide
      have factor_1_22 : (6 : ZMod 5100359321) ^ 7969311 = 3851305942 := by
        calc
          (6 : ZMod 5100359321) ^ 7969311 = (6 : ZMod 5100359321) ^ (3984655 + 3984655 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 3984655 * (6 : ZMod 5100359321) ^ 3984655) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 3851305942 := by rw [factor_1_21]; decide
      have factor_1_23 : (6 : ZMod 5100359321) ^ 15938622 = 2617207738 := by
        calc
          (6 : ZMod 5100359321) ^ 15938622 = (6 : ZMod 5100359321) ^ (7969311 + 7969311) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 7969311 * (6 : ZMod 5100359321) ^ 7969311 := by rw [pow_add]
          _ = 2617207738 := by rw [factor_1_22]; decide
      have factor_1_24 : (6 : ZMod 5100359321) ^ 31877245 = 4395767547 := by
        calc
          (6 : ZMod 5100359321) ^ 31877245 = (6 : ZMod 5100359321) ^ (15938622 + 15938622 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 15938622 * (6 : ZMod 5100359321) ^ 15938622) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 4395767547 := by rw [factor_1_23]; decide
      have factor_1_25 : (6 : ZMod 5100359321) ^ 63754491 = 1497979528 := by
        calc
          (6 : ZMod 5100359321) ^ 63754491 = (6 : ZMod 5100359321) ^ (31877245 + 31877245 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 31877245 * (6 : ZMod 5100359321) ^ 31877245) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 1497979528 := by rw [factor_1_24]; decide
      have factor_1_26 : (6 : ZMod 5100359321) ^ 127508983 = 5067493660 := by
        calc
          (6 : ZMod 5100359321) ^ 127508983 = (6 : ZMod 5100359321) ^ (63754491 + 63754491 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 63754491 * (6 : ZMod 5100359321) ^ 63754491) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 5067493660 := by rw [factor_1_25]; decide
      have factor_1_27 : (6 : ZMod 5100359321) ^ 255017966 = 2676324862 := by
        calc
          (6 : ZMod 5100359321) ^ 255017966 = (6 : ZMod 5100359321) ^ (127508983 + 127508983) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 127508983 * (6 : ZMod 5100359321) ^ 127508983 := by rw [pow_add]
          _ = 2676324862 := by rw [factor_1_26]; decide
      have factor_1_28 : (6 : ZMod 5100359321) ^ 510035932 = 4641157193 := by
        calc
          (6 : ZMod 5100359321) ^ 510035932 = (6 : ZMod 5100359321) ^ (255017966 + 255017966) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 255017966 * (6 : ZMod 5100359321) ^ 255017966 := by rw [pow_add]
          _ = 4641157193 := by rw [factor_1_27]; decide
      have factor_1_29 : (6 : ZMod 5100359321) ^ 1020071864 = 979869946 := by
        calc
          (6 : ZMod 5100359321) ^ 1020071864 = (6 : ZMod 5100359321) ^ (510035932 + 510035932) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 510035932 * (6 : ZMod 5100359321) ^ 510035932 := by rw [pow_add]
          _ = 979869946 := by rw [factor_1_28]; decide
      change (6 : ZMod 5100359321) ^ 1020071864 ≠ 1
      rw [factor_1_29]
      decide
    ·
      have factor_2_0 : (6 : ZMod 5100359321) ^ 1 = 6 := by norm_num
      have factor_2_1 : (6 : ZMod 5100359321) ^ 2 = 36 := by
        calc
          (6 : ZMod 5100359321) ^ 2 = (6 : ZMod 5100359321) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 1 * (6 : ZMod 5100359321) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_2_0]; decide
      have factor_2_2 : (6 : ZMod 5100359321) ^ 5 = 7776 := by
        calc
          (6 : ZMod 5100359321) ^ 5 = (6 : ZMod 5100359321) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 2 * (6 : ZMod 5100359321) ^ 2) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_2_1]; decide
      have factor_2_3 : (6 : ZMod 5100359321) ^ 10 = 60466176 := by
        calc
          (6 : ZMod 5100359321) ^ 10 = (6 : ZMod 5100359321) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 5 * (6 : ZMod 5100359321) ^ 5 := by rw [pow_add]
          _ = 60466176 := by rw [factor_2_2]; decide
      have factor_2_4 : (6 : ZMod 5100359321) ^ 21 = 4279556917 := by
        calc
          (6 : ZMod 5100359321) ^ 21 = (6 : ZMod 5100359321) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 10 * (6 : ZMod 5100359321) ^ 10) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 4279556917 := by rw [factor_2_3]; decide
      have factor_2_5 : (6 : ZMod 5100359321) ^ 43 = 2028581507 := by
        calc
          (6 : ZMod 5100359321) ^ 43 = (6 : ZMod 5100359321) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 21 * (6 : ZMod 5100359321) ^ 21) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 2028581507 := by rw [factor_2_4]; decide
      have factor_2_6 : (6 : ZMod 5100359321) ^ 86 = 669626124 := by
        calc
          (6 : ZMod 5100359321) ^ 86 = (6 : ZMod 5100359321) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 43 * (6 : ZMod 5100359321) ^ 43 := by rw [pow_add]
          _ = 669626124 := by rw [factor_2_5]; decide
      have factor_2_7 : (6 : ZMod 5100359321) ^ 173 = 2779013574 := by
        calc
          (6 : ZMod 5100359321) ^ 173 = (6 : ZMod 5100359321) ^ (86 + 86 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 86 * (6 : ZMod 5100359321) ^ 86) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 2779013574 := by rw [factor_2_6]; decide
      have factor_2_8 : (6 : ZMod 5100359321) ^ 347 = 3145747659 := by
        calc
          (6 : ZMod 5100359321) ^ 347 = (6 : ZMod 5100359321) ^ (173 + 173 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 173 * (6 : ZMod 5100359321) ^ 173) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 3145747659 := by rw [factor_2_7]; decide
      have factor_2_9 : (6 : ZMod 5100359321) ^ 694 = 4612507970 := by
        calc
          (6 : ZMod 5100359321) ^ 694 = (6 : ZMod 5100359321) ^ (347 + 347) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 347 * (6 : ZMod 5100359321) ^ 347 := by rw [pow_add]
          _ = 4612507970 := by rw [factor_2_8]; decide
      have factor_2_10 : (6 : ZMod 5100359321) ^ 1389 = 3991190539 := by
        calc
          (6 : ZMod 5100359321) ^ 1389 = (6 : ZMod 5100359321) ^ (694 + 694 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 694 * (6 : ZMod 5100359321) ^ 694) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 3991190539 := by rw [factor_2_9]; decide
      have factor_2_11 : (6 : ZMod 5100359321) ^ 2779 = 635575992 := by
        calc
          (6 : ZMod 5100359321) ^ 2779 = (6 : ZMod 5100359321) ^ (1389 + 1389 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 1389 * (6 : ZMod 5100359321) ^ 1389) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 635575992 := by rw [factor_2_10]; decide
      have factor_2_12 : (6 : ZMod 5100359321) ^ 5558 = 3493219661 := by
        calc
          (6 : ZMod 5100359321) ^ 5558 = (6 : ZMod 5100359321) ^ (2779 + 2779) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 2779 * (6 : ZMod 5100359321) ^ 2779 := by rw [pow_add]
          _ = 3493219661 := by rw [factor_2_11]; decide
      have factor_2_13 : (6 : ZMod 5100359321) ^ 11117 = 548901201 := by
        calc
          (6 : ZMod 5100359321) ^ 11117 = (6 : ZMod 5100359321) ^ (5558 + 5558 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 5558 * (6 : ZMod 5100359321) ^ 5558) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 548901201 := by rw [factor_2_12]; decide
      have factor_2_14 : (6 : ZMod 5100359321) ^ 22235 = 1560699260 := by
        calc
          (6 : ZMod 5100359321) ^ 22235 = (6 : ZMod 5100359321) ^ (11117 + 11117 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 11117 * (6 : ZMod 5100359321) ^ 11117) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 1560699260 := by rw [factor_2_13]; decide
      have factor_2_15 : (6 : ZMod 5100359321) ^ 44471 = 2894724190 := by
        calc
          (6 : ZMod 5100359321) ^ 44471 = (6 : ZMod 5100359321) ^ (22235 + 22235 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 22235 * (6 : ZMod 5100359321) ^ 22235) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 2894724190 := by rw [factor_2_14]; decide
      have factor_2_16 : (6 : ZMod 5100359321) ^ 88943 = 1993323560 := by
        calc
          (6 : ZMod 5100359321) ^ 88943 = (6 : ZMod 5100359321) ^ (44471 + 44471 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 44471 * (6 : ZMod 5100359321) ^ 44471) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 1993323560 := by rw [factor_2_15]; decide
      have factor_2_17 : (6 : ZMod 5100359321) ^ 177886 = 2097427845 := by
        calc
          (6 : ZMod 5100359321) ^ 177886 = (6 : ZMod 5100359321) ^ (88943 + 88943) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 88943 * (6 : ZMod 5100359321) ^ 88943 := by rw [pow_add]
          _ = 2097427845 := by rw [factor_2_16]; decide
      have factor_2_18 : (6 : ZMod 5100359321) ^ 355772 = 4098927381 := by
        calc
          (6 : ZMod 5100359321) ^ 355772 = (6 : ZMod 5100359321) ^ (177886 + 177886) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 177886 * (6 : ZMod 5100359321) ^ 177886 := by rw [pow_add]
          _ = 4098927381 := by rw [factor_2_17]; decide
      have factor_2_19 : (6 : ZMod 5100359321) ^ 711545 = 375085129 := by
        calc
          (6 : ZMod 5100359321) ^ 711545 = (6 : ZMod 5100359321) ^ (355772 + 355772 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 355772 * (6 : ZMod 5100359321) ^ 355772) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 375085129 := by rw [factor_2_18]; decide
      have factor_2_20 : (6 : ZMod 5100359321) ^ 1423091 = 889649048 := by
        calc
          (6 : ZMod 5100359321) ^ 1423091 = (6 : ZMod 5100359321) ^ (711545 + 711545 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 711545 * (6 : ZMod 5100359321) ^ 711545) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 889649048 := by rw [factor_2_19]; decide
      have factor_2_21 : (6 : ZMod 5100359321) ^ 2846182 = 1357028337 := by
        calc
          (6 : ZMod 5100359321) ^ 2846182 = (6 : ZMod 5100359321) ^ (1423091 + 1423091) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 1423091 * (6 : ZMod 5100359321) ^ 1423091 := by rw [pow_add]
          _ = 1357028337 := by rw [factor_2_20]; decide
      have factor_2_22 : (6 : ZMod 5100359321) ^ 5692365 = 1339182137 := by
        calc
          (6 : ZMod 5100359321) ^ 5692365 = (6 : ZMod 5100359321) ^ (2846182 + 2846182 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 2846182 * (6 : ZMod 5100359321) ^ 2846182) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 1339182137 := by rw [factor_2_21]; decide
      have factor_2_23 : (6 : ZMod 5100359321) ^ 11384730 = 4269348880 := by
        calc
          (6 : ZMod 5100359321) ^ 11384730 = (6 : ZMod 5100359321) ^ (5692365 + 5692365) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 5692365 * (6 : ZMod 5100359321) ^ 5692365 := by rw [pow_add]
          _ = 4269348880 := by rw [factor_2_22]; decide
      have factor_2_24 : (6 : ZMod 5100359321) ^ 22769461 = 1879220122 := by
        calc
          (6 : ZMod 5100359321) ^ 22769461 = (6 : ZMod 5100359321) ^ (11384730 + 11384730 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 11384730 * (6 : ZMod 5100359321) ^ 11384730) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 1879220122 := by rw [factor_2_23]; decide
      have factor_2_25 : (6 : ZMod 5100359321) ^ 45538922 = 2015561909 := by
        calc
          (6 : ZMod 5100359321) ^ 45538922 = (6 : ZMod 5100359321) ^ (22769461 + 22769461) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 22769461 * (6 : ZMod 5100359321) ^ 22769461 := by rw [pow_add]
          _ = 2015561909 := by rw [factor_2_24]; decide
      have factor_2_26 : (6 : ZMod 5100359321) ^ 91077845 = 4850766821 := by
        calc
          (6 : ZMod 5100359321) ^ 91077845 = (6 : ZMod 5100359321) ^ (45538922 + 45538922 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 45538922 * (6 : ZMod 5100359321) ^ 45538922) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 4850766821 := by rw [factor_2_25]; decide
      have factor_2_27 : (6 : ZMod 5100359321) ^ 182155690 = 5065718838 := by
        calc
          (6 : ZMod 5100359321) ^ 182155690 = (6 : ZMod 5100359321) ^ (91077845 + 91077845) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 91077845 * (6 : ZMod 5100359321) ^ 91077845 := by rw [pow_add]
          _ = 5065718838 := by rw [factor_2_26]; decide
      have factor_2_28 : (6 : ZMod 5100359321) ^ 364311380 = 1525021619 := by
        calc
          (6 : ZMod 5100359321) ^ 364311380 = (6 : ZMod 5100359321) ^ (182155690 + 182155690) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 182155690 * (6 : ZMod 5100359321) ^ 182155690 := by rw [pow_add]
          _ = 1525021619 := by rw [factor_2_27]; decide
      have factor_2_29 : (6 : ZMod 5100359321) ^ 728622760 = 2778234177 := by
        calc
          (6 : ZMod 5100359321) ^ 728622760 = (6 : ZMod 5100359321) ^ (364311380 + 364311380) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 364311380 * (6 : ZMod 5100359321) ^ 364311380 := by rw [pow_add]
          _ = 2778234177 := by rw [factor_2_28]; decide
      change (6 : ZMod 5100359321) ^ 728622760 ≠ 1
      rw [factor_2_29]
      decide
    ·
      have factor_3_0 : (6 : ZMod 5100359321) ^ 1 = 6 := by norm_num
      have factor_3_1 : (6 : ZMod 5100359321) ^ 2 = 36 := by
        calc
          (6 : ZMod 5100359321) ^ 2 = (6 : ZMod 5100359321) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 1 * (6 : ZMod 5100359321) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_3_0]; decide
      have factor_3_2 : (6 : ZMod 5100359321) ^ 4 = 1296 := by
        calc
          (6 : ZMod 5100359321) ^ 4 = (6 : ZMod 5100359321) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 2 * (6 : ZMod 5100359321) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_3_1]; decide
      have factor_3_3 : (6 : ZMod 5100359321) ^ 9 = 10077696 := by
        calc
          (6 : ZMod 5100359321) ^ 9 = (6 : ZMod 5100359321) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 4 * (6 : ZMod 5100359321) ^ 4) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 10077696 := by rw [factor_3_2]; decide
      have factor_3_4 : (6 : ZMod 5100359321) ^ 19 = 4510852663 := by
        calc
          (6 : ZMod 5100359321) ^ 19 = (6 : ZMod 5100359321) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 9 * (6 : ZMod 5100359321) ^ 9) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 4510852663 := by rw [factor_3_3]; decide
      have factor_3_5 : (6 : ZMod 5100359321) ^ 39 = 776851364 := by
        calc
          (6 : ZMod 5100359321) ^ 39 = (6 : ZMod 5100359321) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 19 * (6 : ZMod 5100359321) ^ 19) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 776851364 := by rw [factor_3_4]; decide
      have factor_3_6 : (6 : ZMod 5100359321) ^ 78 = 4030752044 := by
        calc
          (6 : ZMod 5100359321) ^ 78 = (6 : ZMod 5100359321) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 39 * (6 : ZMod 5100359321) ^ 39 := by rw [pow_add]
          _ = 4030752044 := by rw [factor_3_5]; decide
      have factor_3_7 : (6 : ZMod 5100359321) ^ 156 = 4650074857 := by
        calc
          (6 : ZMod 5100359321) ^ 156 = (6 : ZMod 5100359321) ^ (78 + 78) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 78 * (6 : ZMod 5100359321) ^ 78 := by rw [pow_add]
          _ = 4650074857 := by rw [factor_3_6]; decide
      have factor_3_8 : (6 : ZMod 5100359321) ^ 313 = 2852375075 := by
        calc
          (6 : ZMod 5100359321) ^ 313 = (6 : ZMod 5100359321) ^ (156 + 156 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 156 * (6 : ZMod 5100359321) ^ 156) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 2852375075 := by rw [factor_3_7]; decide
      have factor_3_9 : (6 : ZMod 5100359321) ^ 627 = 1006978483 := by
        calc
          (6 : ZMod 5100359321) ^ 627 = (6 : ZMod 5100359321) ^ (313 + 313 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 313 * (6 : ZMod 5100359321) ^ 313) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 1006978483 := by rw [factor_3_8]; decide
      have factor_3_10 : (6 : ZMod 5100359321) ^ 1255 = 537126576 := by
        calc
          (6 : ZMod 5100359321) ^ 1255 = (6 : ZMod 5100359321) ^ (627 + 627 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 627 * (6 : ZMod 5100359321) ^ 627) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 537126576 := by rw [factor_3_9]; decide
      have factor_3_11 : (6 : ZMod 5100359321) ^ 2510 = 2032495682 := by
        calc
          (6 : ZMod 5100359321) ^ 2510 = (6 : ZMod 5100359321) ^ (1255 + 1255) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 1255 * (6 : ZMod 5100359321) ^ 1255 := by rw [pow_add]
          _ = 2032495682 := by rw [factor_3_10]; decide
      have factor_3_12 : (6 : ZMod 5100359321) ^ 5020 = 2917129562 := by
        calc
          (6 : ZMod 5100359321) ^ 5020 = (6 : ZMod 5100359321) ^ (2510 + 2510) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 2510 * (6 : ZMod 5100359321) ^ 2510 := by rw [pow_add]
          _ = 2917129562 := by rw [factor_3_11]; decide
      have factor_3_13 : (6 : ZMod 5100359321) ^ 10041 = 3409049686 := by
        calc
          (6 : ZMod 5100359321) ^ 10041 = (6 : ZMod 5100359321) ^ (5020 + 5020 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 5020 * (6 : ZMod 5100359321) ^ 5020) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 3409049686 := by rw [factor_3_12]; decide
      have factor_3_14 : (6 : ZMod 5100359321) ^ 20083 = 850594408 := by
        calc
          (6 : ZMod 5100359321) ^ 20083 = (6 : ZMod 5100359321) ^ (10041 + 10041 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 10041 * (6 : ZMod 5100359321) ^ 10041) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 850594408 := by rw [factor_3_13]; decide
      have factor_3_15 : (6 : ZMod 5100359321) ^ 40167 = 1406593719 := by
        calc
          (6 : ZMod 5100359321) ^ 40167 = (6 : ZMod 5100359321) ^ (20083 + 20083 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 20083 * (6 : ZMod 5100359321) ^ 20083) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 1406593719 := by rw [factor_3_14]; decide
      have factor_3_16 : (6 : ZMod 5100359321) ^ 80335 = 445419161 := by
        calc
          (6 : ZMod 5100359321) ^ 80335 = (6 : ZMod 5100359321) ^ (40167 + 40167 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 40167 * (6 : ZMod 5100359321) ^ 40167) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 445419161 := by rw [factor_3_15]; decide
      have factor_3_17 : (6 : ZMod 5100359321) ^ 160671 = 2124351449 := by
        calc
          (6 : ZMod 5100359321) ^ 160671 = (6 : ZMod 5100359321) ^ (80335 + 80335 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 80335 * (6 : ZMod 5100359321) ^ 80335) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 2124351449 := by rw [factor_3_16]; decide
      have factor_3_18 : (6 : ZMod 5100359321) ^ 321343 = 4710070585 := by
        calc
          (6 : ZMod 5100359321) ^ 321343 = (6 : ZMod 5100359321) ^ (160671 + 160671 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 160671 * (6 : ZMod 5100359321) ^ 160671) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 4710070585 := by rw [factor_3_17]; decide
      have factor_3_19 : (6 : ZMod 5100359321) ^ 642686 = 1010860775 := by
        calc
          (6 : ZMod 5100359321) ^ 642686 = (6 : ZMod 5100359321) ^ (321343 + 321343) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 321343 * (6 : ZMod 5100359321) ^ 321343 := by rw [pow_add]
          _ = 1010860775 := by rw [factor_3_18]; decide
      have factor_3_20 : (6 : ZMod 5100359321) ^ 1285372 = 503003013 := by
        calc
          (6 : ZMod 5100359321) ^ 1285372 = (6 : ZMod 5100359321) ^ (642686 + 642686) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 642686 * (6 : ZMod 5100359321) ^ 642686 := by rw [pow_add]
          _ = 503003013 := by rw [factor_3_19]; decide
      have factor_3_21 : (6 : ZMod 5100359321) ^ 2570745 = 3933073332 := by
        calc
          (6 : ZMod 5100359321) ^ 2570745 = (6 : ZMod 5100359321) ^ (1285372 + 1285372 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 1285372 * (6 : ZMod 5100359321) ^ 1285372) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 3933073332 := by rw [factor_3_20]; decide
      have factor_3_22 : (6 : ZMod 5100359321) ^ 5141491 = 1028584037 := by
        calc
          (6 : ZMod 5100359321) ^ 5141491 = (6 : ZMod 5100359321) ^ (2570745 + 2570745 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 2570745 * (6 : ZMod 5100359321) ^ 2570745) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 1028584037 := by rw [factor_3_21]; decide
      have factor_3_23 : (6 : ZMod 5100359321) ^ 10282982 = 1177248561 := by
        calc
          (6 : ZMod 5100359321) ^ 10282982 = (6 : ZMod 5100359321) ^ (5141491 + 5141491) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 5141491 * (6 : ZMod 5100359321) ^ 5141491 := by rw [pow_add]
          _ = 1177248561 := by rw [factor_3_22]; decide
      have factor_3_24 : (6 : ZMod 5100359321) ^ 20565965 = 4720080531 := by
        calc
          (6 : ZMod 5100359321) ^ 20565965 = (6 : ZMod 5100359321) ^ (10282982 + 10282982 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 10282982 * (6 : ZMod 5100359321) ^ 10282982) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 4720080531 := by rw [factor_3_23]; decide
      have factor_3_25 : (6 : ZMod 5100359321) ^ 41131930 = 1392066652 := by
        calc
          (6 : ZMod 5100359321) ^ 41131930 = (6 : ZMod 5100359321) ^ (20565965 + 20565965) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 20565965 * (6 : ZMod 5100359321) ^ 20565965 := by rw [pow_add]
          _ = 1392066652 := by rw [factor_3_24]; decide
      have factor_3_26 : (6 : ZMod 5100359321) ^ 82263860 = 3548403811 := by
        calc
          (6 : ZMod 5100359321) ^ 82263860 = (6 : ZMod 5100359321) ^ (41131930 + 41131930) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 41131930 * (6 : ZMod 5100359321) ^ 41131930 := by rw [pow_add]
          _ = 3548403811 := by rw [factor_3_25]; decide
      have factor_3_27 : (6 : ZMod 5100359321) ^ 164527720 = 927541587 := by
        calc
          (6 : ZMod 5100359321) ^ 164527720 = (6 : ZMod 5100359321) ^ (82263860 + 82263860) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 82263860 * (6 : ZMod 5100359321) ^ 82263860 := by rw [pow_add]
          _ = 927541587 := by rw [factor_3_26]; decide
      change (6 : ZMod 5100359321) ^ 164527720 ≠ 1
      rw [factor_3_27]
      decide
    ·
      have factor_4_0 : (6 : ZMod 5100359321) ^ 1 = 6 := by norm_num
      have factor_4_1 : (6 : ZMod 5100359321) ^ 2 = 36 := by
        calc
          (6 : ZMod 5100359321) ^ 2 = (6 : ZMod 5100359321) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 1 * (6 : ZMod 5100359321) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_4_0]; decide
      have factor_4_2 : (6 : ZMod 5100359321) ^ 4 = 1296 := by
        calc
          (6 : ZMod 5100359321) ^ 4 = (6 : ZMod 5100359321) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 2 * (6 : ZMod 5100359321) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_4_1]; decide
      have factor_4_3 : (6 : ZMod 5100359321) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 5100359321) ^ 8 = (6 : ZMod 5100359321) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 4 * (6 : ZMod 5100359321) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_4_2]; decide
      have factor_4_4 : (6 : ZMod 5100359321) ^ 16 = 611202943 := by
        calc
          (6 : ZMod 5100359321) ^ 16 = (6 : ZMod 5100359321) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 8 * (6 : ZMod 5100359321) ^ 8 := by rw [pow_add]
          _ = 611202943 := by rw [factor_4_3]; decide
      have factor_4_5 : (6 : ZMod 5100359321) ^ 33 = 5057960432 := by
        calc
          (6 : ZMod 5100359321) ^ 33 = (6 : ZMod 5100359321) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 16 * (6 : ZMod 5100359321) ^ 16) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 5057960432 := by rw [factor_4_4]; decide
      have factor_4_6 : (6 : ZMod 5100359321) ^ 67 = 4756161855 := by
        calc
          (6 : ZMod 5100359321) ^ 67 = (6 : ZMod 5100359321) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 33 * (6 : ZMod 5100359321) ^ 33) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 4756161855 := by rw [factor_4_5]; decide
      have factor_4_7 : (6 : ZMod 5100359321) ^ 135 = 2339237135 := by
        calc
          (6 : ZMod 5100359321) ^ 135 = (6 : ZMod 5100359321) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 67 * (6 : ZMod 5100359321) ^ 67) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 2339237135 := by rw [factor_4_6]; decide
      have factor_4_8 : (6 : ZMod 5100359321) ^ 271 = 224194853 := by
        calc
          (6 : ZMod 5100359321) ^ 271 = (6 : ZMod 5100359321) ^ (135 + 135 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 135 * (6 : ZMod 5100359321) ^ 135) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 224194853 := by rw [factor_4_7]; decide
      have factor_4_9 : (6 : ZMod 5100359321) ^ 542 = 5053541549 := by
        calc
          (6 : ZMod 5100359321) ^ 542 = (6 : ZMod 5100359321) ^ (271 + 271) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 271 * (6 : ZMod 5100359321) ^ 271 := by rw [pow_add]
          _ = 5053541549 := by rw [factor_4_8]; decide
      have factor_4_10 : (6 : ZMod 5100359321) ^ 1085 = 3331004416 := by
        calc
          (6 : ZMod 5100359321) ^ 1085 = (6 : ZMod 5100359321) ^ (542 + 542 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = ((6 : ZMod 5100359321) ^ 542 * (6 : ZMod 5100359321) ^ 542) * (6 : ZMod 5100359321) := by rw [pow_succ, pow_add]
          _ = 3331004416 := by rw [factor_4_9]; decide
      have factor_4_11 : (6 : ZMod 5100359321) ^ 2170 = 4374758924 := by
        calc
          (6 : ZMod 5100359321) ^ 2170 = (6 : ZMod 5100359321) ^ (1085 + 1085) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 1085 * (6 : ZMod 5100359321) ^ 1085 := by rw [pow_add]
          _ = 4374758924 := by rw [factor_4_10]; decide
      have factor_4_12 : (6 : ZMod 5100359321) ^ 4340 = 2017202705 := by
        calc
          (6 : ZMod 5100359321) ^ 4340 = (6 : ZMod 5100359321) ^ (2170 + 2170) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 2170 * (6 : ZMod 5100359321) ^ 2170 := by rw [pow_add]
          _ = 2017202705 := by rw [factor_4_11]; decide
      have factor_4_13 : (6 : ZMod 5100359321) ^ 8680 = 3041613286 := by
        calc
          (6 : ZMod 5100359321) ^ 8680 = (6 : ZMod 5100359321) ^ (4340 + 4340) :=
            congrArg (fun n : ℕ => (6 : ZMod 5100359321) ^ n) (by norm_num)
          _ = (6 : ZMod 5100359321) ^ 4340 * (6 : ZMod 5100359321) ^ 4340 := by rw [pow_add]
          _ = 3041613286 := by rw [factor_4_12]; decide
      change (6 : ZMod 5100359321) ^ 8680 ≠ 1
      rw [factor_4_13]
      decide

#print axioms prime_lucas_5100359321

end TotientTailPeriodKiller
end Erdos249257
