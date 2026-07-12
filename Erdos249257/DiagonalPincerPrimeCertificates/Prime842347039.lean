import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_842347039 : Nat.Prime 842347039 := by
  apply lucas_primality 842347039 (3 : ZMod 842347039)
  ·
      have fermat_0 : (3 : ZMod 842347039) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 842347039) ^ 3 = 27 := by
        calc
          (3 : ZMod 842347039) ^ 3 = (3 : ZMod 842347039) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 1 * (3 : ZMod 842347039) ^ 1) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 842347039) ^ 6 = 729 := by
        calc
          (3 : ZMod 842347039) ^ 6 = (3 : ZMod 842347039) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 3 * (3 : ZMod 842347039) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 842347039) ^ 12 = 531441 := by
        calc
          (3 : ZMod 842347039) ^ 12 = (3 : ZMod 842347039) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 6 * (3 : ZMod 842347039) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 842347039) ^ 25 = 729835248 := by
        calc
          (3 : ZMod 842347039) ^ 25 = (3 : ZMod 842347039) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 12 * (3 : ZMod 842347039) ^ 12) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 729835248 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 842347039) ^ 50 = 622126533 := by
        calc
          (3 : ZMod 842347039) ^ 50 = (3 : ZMod 842347039) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 25 * (3 : ZMod 842347039) ^ 25 := by rw [pow_add]
          _ = 622126533 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 842347039) ^ 100 = 165046098 := by
        calc
          (3 : ZMod 842347039) ^ 100 = (3 : ZMod 842347039) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 50 * (3 : ZMod 842347039) ^ 50 := by rw [pow_add]
          _ = 165046098 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 842347039) ^ 200 = 14735274 := by
        calc
          (3 : ZMod 842347039) ^ 200 = (3 : ZMod 842347039) ^ (100 + 100) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 100 * (3 : ZMod 842347039) ^ 100 := by rw [pow_add]
          _ = 14735274 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 842347039) ^ 401 = 461347645 := by
        calc
          (3 : ZMod 842347039) ^ 401 = (3 : ZMod 842347039) ^ (200 + 200 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 200 * (3 : ZMod 842347039) ^ 200) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 461347645 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 842347039) ^ 803 = 173506254 := by
        calc
          (3 : ZMod 842347039) ^ 803 = (3 : ZMod 842347039) ^ (401 + 401 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 401 * (3 : ZMod 842347039) ^ 401) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 173506254 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 842347039) ^ 1606 = 45215734 := by
        calc
          (3 : ZMod 842347039) ^ 1606 = (3 : ZMod 842347039) ^ (803 + 803) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 803 * (3 : ZMod 842347039) ^ 803 := by rw [pow_add]
          _ = 45215734 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 842347039) ^ 3213 = 411976295 := by
        calc
          (3 : ZMod 842347039) ^ 3213 = (3 : ZMod 842347039) ^ (1606 + 1606 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 1606 * (3 : ZMod 842347039) ^ 1606) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 411976295 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 842347039) ^ 6426 = 659433780 := by
        calc
          (3 : ZMod 842347039) ^ 6426 = (3 : ZMod 842347039) ^ (3213 + 3213) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 3213 * (3 : ZMod 842347039) ^ 3213 := by rw [pow_add]
          _ = 659433780 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 842347039) ^ 12853 = 655403401 := by
        calc
          (3 : ZMod 842347039) ^ 12853 = (3 : ZMod 842347039) ^ (6426 + 6426 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 6426 * (3 : ZMod 842347039) ^ 6426) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 655403401 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 842347039) ^ 25706 = 601404911 := by
        calc
          (3 : ZMod 842347039) ^ 25706 = (3 : ZMod 842347039) ^ (12853 + 12853) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 12853 * (3 : ZMod 842347039) ^ 12853 := by rw [pow_add]
          _ = 601404911 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 842347039) ^ 51412 = 796542503 := by
        calc
          (3 : ZMod 842347039) ^ 51412 = (3 : ZMod 842347039) ^ (25706 + 25706) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 25706 * (3 : ZMod 842347039) ^ 25706 := by rw [pow_add]
          _ = 796542503 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 842347039) ^ 102825 = 383691985 := by
        calc
          (3 : ZMod 842347039) ^ 102825 = (3 : ZMod 842347039) ^ (51412 + 51412 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 51412 * (3 : ZMod 842347039) ^ 51412) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 383691985 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 842347039) ^ 205651 = 269292867 := by
        calc
          (3 : ZMod 842347039) ^ 205651 = (3 : ZMod 842347039) ^ (102825 + 102825 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 102825 * (3 : ZMod 842347039) ^ 102825) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 269292867 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 842347039) ^ 411302 = 187104786 := by
        calc
          (3 : ZMod 842347039) ^ 411302 = (3 : ZMod 842347039) ^ (205651 + 205651) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 205651 * (3 : ZMod 842347039) ^ 205651 := by rw [pow_add]
          _ = 187104786 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 842347039) ^ 822604 = 245071862 := by
        calc
          (3 : ZMod 842347039) ^ 822604 = (3 : ZMod 842347039) ^ (411302 + 411302) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 411302 * (3 : ZMod 842347039) ^ 411302 := by rw [pow_add]
          _ = 245071862 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 842347039) ^ 1645209 = 448702803 := by
        calc
          (3 : ZMod 842347039) ^ 1645209 = (3 : ZMod 842347039) ^ (822604 + 822604 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 822604 * (3 : ZMod 842347039) ^ 822604) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 448702803 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 842347039) ^ 3290418 = 344927754 := by
        calc
          (3 : ZMod 842347039) ^ 3290418 = (3 : ZMod 842347039) ^ (1645209 + 1645209) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 1645209 * (3 : ZMod 842347039) ^ 1645209 := by rw [pow_add]
          _ = 344927754 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 842347039) ^ 6580836 = 152614161 := by
        calc
          (3 : ZMod 842347039) ^ 6580836 = (3 : ZMod 842347039) ^ (3290418 + 3290418) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 3290418 * (3 : ZMod 842347039) ^ 3290418 := by rw [pow_add]
          _ = 152614161 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 842347039) ^ 13161672 = 350688302 := by
        calc
          (3 : ZMod 842347039) ^ 13161672 = (3 : ZMod 842347039) ^ (6580836 + 6580836) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 6580836 * (3 : ZMod 842347039) ^ 6580836 := by rw [pow_add]
          _ = 350688302 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 842347039) ^ 26323344 = 733545949 := by
        calc
          (3 : ZMod 842347039) ^ 26323344 = (3 : ZMod 842347039) ^ (13161672 + 13161672) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 13161672 * (3 : ZMod 842347039) ^ 13161672 := by rw [pow_add]
          _ = 733545949 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 842347039) ^ 52646689 = 483199120 := by
        calc
          (3 : ZMod 842347039) ^ 52646689 = (3 : ZMod 842347039) ^ (26323344 + 26323344 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 26323344 * (3 : ZMod 842347039) ^ 26323344) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 483199120 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 842347039) ^ 105293379 = 208637588 := by
        calc
          (3 : ZMod 842347039) ^ 105293379 = (3 : ZMod 842347039) ^ (52646689 + 52646689 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 52646689 * (3 : ZMod 842347039) ^ 52646689) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 208637588 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 842347039) ^ 210586759 = 171688355 := by
        calc
          (3 : ZMod 842347039) ^ 210586759 = (3 : ZMod 842347039) ^ (105293379 + 105293379 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 105293379 * (3 : ZMod 842347039) ^ 105293379) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 171688355 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 842347039) ^ 421173519 = 842347038 := by
        calc
          (3 : ZMod 842347039) ^ 421173519 = (3 : ZMod 842347039) ^ (210586759 + 210586759 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 210586759 * (3 : ZMod 842347039) ^ 210586759) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 842347038 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 842347039) ^ 842347038 = 1 := by
        calc
          (3 : ZMod 842347039) ^ 842347038 = (3 : ZMod 842347039) ^ (421173519 + 421173519) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 421173519 * (3 : ZMod 842347039) ^ 421173519 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 2), (43, 1), (19319, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 2), (43, 1), (19319, 1)] : List FactorBlock).map factorBlockValue).prod = 842347039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 842347039) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 842347039) ^ 3 = 27 := by
        calc
          (3 : ZMod 842347039) ^ 3 = (3 : ZMod 842347039) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 1 * (3 : ZMod 842347039) ^ 1) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 842347039) ^ 6 = 729 := by
        calc
          (3 : ZMod 842347039) ^ 6 = (3 : ZMod 842347039) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 3 * (3 : ZMod 842347039) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 842347039) ^ 12 = 531441 := by
        calc
          (3 : ZMod 842347039) ^ 12 = (3 : ZMod 842347039) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 6 * (3 : ZMod 842347039) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 842347039) ^ 25 = 729835248 := by
        calc
          (3 : ZMod 842347039) ^ 25 = (3 : ZMod 842347039) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 12 * (3 : ZMod 842347039) ^ 12) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 729835248 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 842347039) ^ 50 = 622126533 := by
        calc
          (3 : ZMod 842347039) ^ 50 = (3 : ZMod 842347039) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 25 * (3 : ZMod 842347039) ^ 25 := by rw [pow_add]
          _ = 622126533 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 842347039) ^ 100 = 165046098 := by
        calc
          (3 : ZMod 842347039) ^ 100 = (3 : ZMod 842347039) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 50 * (3 : ZMod 842347039) ^ 50 := by rw [pow_add]
          _ = 165046098 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 842347039) ^ 200 = 14735274 := by
        calc
          (3 : ZMod 842347039) ^ 200 = (3 : ZMod 842347039) ^ (100 + 100) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 100 * (3 : ZMod 842347039) ^ 100 := by rw [pow_add]
          _ = 14735274 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 842347039) ^ 401 = 461347645 := by
        calc
          (3 : ZMod 842347039) ^ 401 = (3 : ZMod 842347039) ^ (200 + 200 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 200 * (3 : ZMod 842347039) ^ 200) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 461347645 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 842347039) ^ 803 = 173506254 := by
        calc
          (3 : ZMod 842347039) ^ 803 = (3 : ZMod 842347039) ^ (401 + 401 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 401 * (3 : ZMod 842347039) ^ 401) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 173506254 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 842347039) ^ 1606 = 45215734 := by
        calc
          (3 : ZMod 842347039) ^ 1606 = (3 : ZMod 842347039) ^ (803 + 803) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 803 * (3 : ZMod 842347039) ^ 803 := by rw [pow_add]
          _ = 45215734 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 842347039) ^ 3213 = 411976295 := by
        calc
          (3 : ZMod 842347039) ^ 3213 = (3 : ZMod 842347039) ^ (1606 + 1606 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 1606 * (3 : ZMod 842347039) ^ 1606) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 411976295 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 842347039) ^ 6426 = 659433780 := by
        calc
          (3 : ZMod 842347039) ^ 6426 = (3 : ZMod 842347039) ^ (3213 + 3213) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 3213 * (3 : ZMod 842347039) ^ 3213 := by rw [pow_add]
          _ = 659433780 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 842347039) ^ 12853 = 655403401 := by
        calc
          (3 : ZMod 842347039) ^ 12853 = (3 : ZMod 842347039) ^ (6426 + 6426 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 6426 * (3 : ZMod 842347039) ^ 6426) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 655403401 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 842347039) ^ 25706 = 601404911 := by
        calc
          (3 : ZMod 842347039) ^ 25706 = (3 : ZMod 842347039) ^ (12853 + 12853) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 12853 * (3 : ZMod 842347039) ^ 12853 := by rw [pow_add]
          _ = 601404911 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 842347039) ^ 51412 = 796542503 := by
        calc
          (3 : ZMod 842347039) ^ 51412 = (3 : ZMod 842347039) ^ (25706 + 25706) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 25706 * (3 : ZMod 842347039) ^ 25706 := by rw [pow_add]
          _ = 796542503 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 842347039) ^ 102825 = 383691985 := by
        calc
          (3 : ZMod 842347039) ^ 102825 = (3 : ZMod 842347039) ^ (51412 + 51412 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 51412 * (3 : ZMod 842347039) ^ 51412) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 383691985 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 842347039) ^ 205651 = 269292867 := by
        calc
          (3 : ZMod 842347039) ^ 205651 = (3 : ZMod 842347039) ^ (102825 + 102825 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 102825 * (3 : ZMod 842347039) ^ 102825) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 269292867 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 842347039) ^ 411302 = 187104786 := by
        calc
          (3 : ZMod 842347039) ^ 411302 = (3 : ZMod 842347039) ^ (205651 + 205651) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 205651 * (3 : ZMod 842347039) ^ 205651 := by rw [pow_add]
          _ = 187104786 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 842347039) ^ 822604 = 245071862 := by
        calc
          (3 : ZMod 842347039) ^ 822604 = (3 : ZMod 842347039) ^ (411302 + 411302) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 411302 * (3 : ZMod 842347039) ^ 411302 := by rw [pow_add]
          _ = 245071862 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 842347039) ^ 1645209 = 448702803 := by
        calc
          (3 : ZMod 842347039) ^ 1645209 = (3 : ZMod 842347039) ^ (822604 + 822604 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 822604 * (3 : ZMod 842347039) ^ 822604) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 448702803 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 842347039) ^ 3290418 = 344927754 := by
        calc
          (3 : ZMod 842347039) ^ 3290418 = (3 : ZMod 842347039) ^ (1645209 + 1645209) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 1645209 * (3 : ZMod 842347039) ^ 1645209 := by rw [pow_add]
          _ = 344927754 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 842347039) ^ 6580836 = 152614161 := by
        calc
          (3 : ZMod 842347039) ^ 6580836 = (3 : ZMod 842347039) ^ (3290418 + 3290418) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 3290418 * (3 : ZMod 842347039) ^ 3290418 := by rw [pow_add]
          _ = 152614161 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 842347039) ^ 13161672 = 350688302 := by
        calc
          (3 : ZMod 842347039) ^ 13161672 = (3 : ZMod 842347039) ^ (6580836 + 6580836) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 6580836 * (3 : ZMod 842347039) ^ 6580836 := by rw [pow_add]
          _ = 350688302 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 842347039) ^ 26323344 = 733545949 := by
        calc
          (3 : ZMod 842347039) ^ 26323344 = (3 : ZMod 842347039) ^ (13161672 + 13161672) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 13161672 * (3 : ZMod 842347039) ^ 13161672 := by rw [pow_add]
          _ = 733545949 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 842347039) ^ 52646689 = 483199120 := by
        calc
          (3 : ZMod 842347039) ^ 52646689 = (3 : ZMod 842347039) ^ (26323344 + 26323344 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 26323344 * (3 : ZMod 842347039) ^ 26323344) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 483199120 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 842347039) ^ 105293379 = 208637588 := by
        calc
          (3 : ZMod 842347039) ^ 105293379 = (3 : ZMod 842347039) ^ (52646689 + 52646689 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 52646689 * (3 : ZMod 842347039) ^ 52646689) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 208637588 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 842347039) ^ 210586759 = 171688355 := by
        calc
          (3 : ZMod 842347039) ^ 210586759 = (3 : ZMod 842347039) ^ (105293379 + 105293379 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 105293379 * (3 : ZMod 842347039) ^ 105293379) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 171688355 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 842347039) ^ 421173519 = 842347038 := by
        calc
          (3 : ZMod 842347039) ^ 421173519 = (3 : ZMod 842347039) ^ (210586759 + 210586759 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 210586759 * (3 : ZMod 842347039) ^ 210586759) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 842347038 := by rw [factor_0_27]; decide
      change (3 : ZMod 842347039) ^ 421173519 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (3 : ZMod 842347039) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 842347039) ^ 2 = 9 := by
        calc
          (3 : ZMod 842347039) ^ 2 = (3 : ZMod 842347039) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 1 * (3 : ZMod 842347039) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 842347039) ^ 4 = 81 := by
        calc
          (3 : ZMod 842347039) ^ 4 = (3 : ZMod 842347039) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 2 * (3 : ZMod 842347039) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 842347039) ^ 8 = 6561 := by
        calc
          (3 : ZMod 842347039) ^ 8 = (3 : ZMod 842347039) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 4 * (3 : ZMod 842347039) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 842347039) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 842347039) ^ 16 = (3 : ZMod 842347039) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 8 * (3 : ZMod 842347039) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 842347039) ^ 33 = 548492452 := by
        calc
          (3 : ZMod 842347039) ^ 33 = (3 : ZMod 842347039) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 16 * (3 : ZMod 842347039) ^ 16) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 548492452 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 842347039) ^ 66 = 369604057 := by
        calc
          (3 : ZMod 842347039) ^ 66 = (3 : ZMod 842347039) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 33 * (3 : ZMod 842347039) ^ 33 := by rw [pow_add]
          _ = 369604057 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 842347039) ^ 133 = 530822345 := by
        calc
          (3 : ZMod 842347039) ^ 133 = (3 : ZMod 842347039) ^ (66 + 66 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 66 * (3 : ZMod 842347039) ^ 66) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 530822345 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 842347039) ^ 267 = 266840273 := by
        calc
          (3 : ZMod 842347039) ^ 267 = (3 : ZMod 842347039) ^ (133 + 133 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 133 * (3 : ZMod 842347039) ^ 133) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 266840273 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 842347039) ^ 535 = 568166711 := by
        calc
          (3 : ZMod 842347039) ^ 535 = (3 : ZMod 842347039) ^ (267 + 267 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 267 * (3 : ZMod 842347039) ^ 267) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 568166711 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 842347039) ^ 1071 = 441880614 := by
        calc
          (3 : ZMod 842347039) ^ 1071 = (3 : ZMod 842347039) ^ (535 + 535 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 535 * (3 : ZMod 842347039) ^ 535) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 441880614 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 842347039) ^ 2142 = 690568364 := by
        calc
          (3 : ZMod 842347039) ^ 2142 = (3 : ZMod 842347039) ^ (1071 + 1071) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 1071 * (3 : ZMod 842347039) ^ 1071 := by rw [pow_add]
          _ = 690568364 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 842347039) ^ 4284 = 761642652 := by
        calc
          (3 : ZMod 842347039) ^ 4284 = (3 : ZMod 842347039) ^ (2142 + 2142) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 2142 * (3 : ZMod 842347039) ^ 2142 := by rw [pow_add]
          _ = 761642652 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 842347039) ^ 8568 = 621395891 := by
        calc
          (3 : ZMod 842347039) ^ 8568 = (3 : ZMod 842347039) ^ (4284 + 4284) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 4284 * (3 : ZMod 842347039) ^ 4284 := by rw [pow_add]
          _ = 621395891 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 842347039) ^ 17137 = 28537820 := by
        calc
          (3 : ZMod 842347039) ^ 17137 = (3 : ZMod 842347039) ^ (8568 + 8568 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 8568 * (3 : ZMod 842347039) ^ 8568) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 28537820 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 842347039) ^ 34275 = 663214012 := by
        calc
          (3 : ZMod 842347039) ^ 34275 = (3 : ZMod 842347039) ^ (17137 + 17137 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 17137 * (3 : ZMod 842347039) ^ 17137) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 663214012 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 842347039) ^ 68550 = 338076093 := by
        calc
          (3 : ZMod 842347039) ^ 68550 = (3 : ZMod 842347039) ^ (34275 + 34275) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 34275 * (3 : ZMod 842347039) ^ 34275 := by rw [pow_add]
          _ = 338076093 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 842347039) ^ 137100 = 531955212 := by
        calc
          (3 : ZMod 842347039) ^ 137100 = (3 : ZMod 842347039) ^ (68550 + 68550) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 68550 * (3 : ZMod 842347039) ^ 68550 := by rw [pow_add]
          _ = 531955212 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 842347039) ^ 274201 = 829058317 := by
        calc
          (3 : ZMod 842347039) ^ 274201 = (3 : ZMod 842347039) ^ (137100 + 137100 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 137100 * (3 : ZMod 842347039) ^ 137100) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 829058317 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 842347039) ^ 548403 = 655064933 := by
        calc
          (3 : ZMod 842347039) ^ 548403 = (3 : ZMod 842347039) ^ (274201 + 274201 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 274201 * (3 : ZMod 842347039) ^ 274201) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 655064933 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 842347039) ^ 1096806 = 316270673 := by
        calc
          (3 : ZMod 842347039) ^ 1096806 = (3 : ZMod 842347039) ^ (548403 + 548403) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 548403 * (3 : ZMod 842347039) ^ 548403 := by rw [pow_add]
          _ = 316270673 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 842347039) ^ 2193612 = 380544742 := by
        calc
          (3 : ZMod 842347039) ^ 2193612 = (3 : ZMod 842347039) ^ (1096806 + 1096806) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 1096806 * (3 : ZMod 842347039) ^ 1096806 := by rw [pow_add]
          _ = 380544742 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 842347039) ^ 4387224 = 820225306 := by
        calc
          (3 : ZMod 842347039) ^ 4387224 = (3 : ZMod 842347039) ^ (2193612 + 2193612) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 2193612 * (3 : ZMod 842347039) ^ 2193612 := by rw [pow_add]
          _ = 820225306 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 842347039) ^ 8774448 = 292798810 := by
        calc
          (3 : ZMod 842347039) ^ 8774448 = (3 : ZMod 842347039) ^ (4387224 + 4387224) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 4387224 * (3 : ZMod 842347039) ^ 4387224 := by rw [pow_add]
          _ = 292798810 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 842347039) ^ 17548896 = 456815171 := by
        calc
          (3 : ZMod 842347039) ^ 17548896 = (3 : ZMod 842347039) ^ (8774448 + 8774448) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 8774448 * (3 : ZMod 842347039) ^ 8774448 := by rw [pow_add]
          _ = 456815171 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 842347039) ^ 35097793 = 744283198 := by
        calc
          (3 : ZMod 842347039) ^ 35097793 = (3 : ZMod 842347039) ^ (17548896 + 17548896 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 17548896 * (3 : ZMod 842347039) ^ 17548896) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 744283198 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 842347039) ^ 70195586 = 85844177 := by
        calc
          (3 : ZMod 842347039) ^ 70195586 = (3 : ZMod 842347039) ^ (35097793 + 35097793) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 35097793 * (3 : ZMod 842347039) ^ 35097793 := by rw [pow_add]
          _ = 85844177 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 842347039) ^ 140391173 = 584814507 := by
        calc
          (3 : ZMod 842347039) ^ 140391173 = (3 : ZMod 842347039) ^ (70195586 + 70195586 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 70195586 * (3 : ZMod 842347039) ^ 70195586) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 584814507 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 842347039) ^ 280782346 = 584814506 := by
        calc
          (3 : ZMod 842347039) ^ 280782346 = (3 : ZMod 842347039) ^ (140391173 + 140391173) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 140391173 * (3 : ZMod 842347039) ^ 140391173 := by rw [pow_add]
          _ = 584814506 := by rw [factor_1_27]; decide
      change (3 : ZMod 842347039) ^ 280782346 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (3 : ZMod 842347039) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 842347039) ^ 3 = 27 := by
        calc
          (3 : ZMod 842347039) ^ 3 = (3 : ZMod 842347039) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 1 * (3 : ZMod 842347039) ^ 1) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 842347039) ^ 7 = 2187 := by
        calc
          (3 : ZMod 842347039) ^ 7 = (3 : ZMod 842347039) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 3 * (3 : ZMod 842347039) ^ 3) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 842347039) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 842347039) ^ 15 = (3 : ZMod 842347039) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 7 * (3 : ZMod 842347039) ^ 7) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 842347039) ^ 30 = 457087074 := by
        calc
          (3 : ZMod 842347039) ^ 30 = (3 : ZMod 842347039) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 15 * (3 : ZMod 842347039) ^ 15 := by rw [pow_add]
          _ = 457087074 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 842347039) ^ 61 = 216440825 := by
        calc
          (3 : ZMod 842347039) ^ 61 = (3 : ZMod 842347039) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 30 * (3 : ZMod 842347039) ^ 30) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 216440825 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 842347039) ^ 123 = 678163334 := by
        calc
          (3 : ZMod 842347039) ^ 123 = (3 : ZMod 842347039) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 61 * (3 : ZMod 842347039) ^ 61) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 678163334 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 842347039) ^ 247 = 725811690 := by
        calc
          (3 : ZMod 842347039) ^ 247 = (3 : ZMod 842347039) ^ (123 + 123 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 123 * (3 : ZMod 842347039) ^ 123) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 725811690 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 842347039) ^ 494 = 134386001 := by
        calc
          (3 : ZMod 842347039) ^ 494 = (3 : ZMod 842347039) ^ (247 + 247) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 247 * (3 : ZMod 842347039) ^ 247 := by rw [pow_add]
          _ = 134386001 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 842347039) ^ 988 = 209874977 := by
        calc
          (3 : ZMod 842347039) ^ 988 = (3 : ZMod 842347039) ^ (494 + 494) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 494 * (3 : ZMod 842347039) ^ 494 := by rw [pow_add]
          _ = 209874977 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 842347039) ^ 1977 = 46757787 := by
        calc
          (3 : ZMod 842347039) ^ 1977 = (3 : ZMod 842347039) ^ (988 + 988 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 988 * (3 : ZMod 842347039) ^ 988) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 46757787 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 842347039) ^ 3954 = 806435883 := by
        calc
          (3 : ZMod 842347039) ^ 3954 = (3 : ZMod 842347039) ^ (1977 + 1977) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 1977 * (3 : ZMod 842347039) ^ 1977 := by rw [pow_add]
          _ = 806435883 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 842347039) ^ 7909 = 813405128 := by
        calc
          (3 : ZMod 842347039) ^ 7909 = (3 : ZMod 842347039) ^ (3954 + 3954 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 3954 * (3 : ZMod 842347039) ^ 3954) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 813405128 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 842347039) ^ 15819 = 315045378 := by
        calc
          (3 : ZMod 842347039) ^ 15819 = (3 : ZMod 842347039) ^ (7909 + 7909 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 7909 * (3 : ZMod 842347039) ^ 7909) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 315045378 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 842347039) ^ 31638 = 324424372 := by
        calc
          (3 : ZMod 842347039) ^ 31638 = (3 : ZMod 842347039) ^ (15819 + 15819) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 15819 * (3 : ZMod 842347039) ^ 15819 := by rw [pow_add]
          _ = 324424372 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 842347039) ^ 63277 = 582338593 := by
        calc
          (3 : ZMod 842347039) ^ 63277 = (3 : ZMod 842347039) ^ (31638 + 31638 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 31638 * (3 : ZMod 842347039) ^ 31638) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 582338593 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 842347039) ^ 126554 = 798621208 := by
        calc
          (3 : ZMod 842347039) ^ 126554 = (3 : ZMod 842347039) ^ (63277 + 63277) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 63277 * (3 : ZMod 842347039) ^ 63277 := by rw [pow_add]
          _ = 798621208 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 842347039) ^ 253109 = 656436643 := by
        calc
          (3 : ZMod 842347039) ^ 253109 = (3 : ZMod 842347039) ^ (126554 + 126554 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 126554 * (3 : ZMod 842347039) ^ 126554) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 656436643 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 842347039) ^ 506218 = 414240372 := by
        calc
          (3 : ZMod 842347039) ^ 506218 = (3 : ZMod 842347039) ^ (253109 + 253109) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 253109 * (3 : ZMod 842347039) ^ 253109 := by rw [pow_add]
          _ = 414240372 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 842347039) ^ 1012436 = 211062981 := by
        calc
          (3 : ZMod 842347039) ^ 1012436 = (3 : ZMod 842347039) ^ (506218 + 506218) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 506218 * (3 : ZMod 842347039) ^ 506218 := by rw [pow_add]
          _ = 211062981 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 842347039) ^ 2024872 = 669145670 := by
        calc
          (3 : ZMod 842347039) ^ 2024872 = (3 : ZMod 842347039) ^ (1012436 + 1012436) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 1012436 * (3 : ZMod 842347039) ^ 1012436 := by rw [pow_add]
          _ = 669145670 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 842347039) ^ 4049745 = 664504467 := by
        calc
          (3 : ZMod 842347039) ^ 4049745 = (3 : ZMod 842347039) ^ (2024872 + 2024872 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 2024872 * (3 : ZMod 842347039) ^ 2024872) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 664504467 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 842347039) ^ 8099490 = 455462790 := by
        calc
          (3 : ZMod 842347039) ^ 8099490 = (3 : ZMod 842347039) ^ (4049745 + 4049745) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 4049745 * (3 : ZMod 842347039) ^ 4049745 := by rw [pow_add]
          _ = 455462790 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 842347039) ^ 16198981 = 323283332 := by
        calc
          (3 : ZMod 842347039) ^ 16198981 = (3 : ZMod 842347039) ^ (8099490 + 8099490 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 8099490 * (3 : ZMod 842347039) ^ 8099490) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 323283332 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 842347039) ^ 32397963 = 618284846 := by
        calc
          (3 : ZMod 842347039) ^ 32397963 = (3 : ZMod 842347039) ^ (16198981 + 16198981 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 16198981 * (3 : ZMod 842347039) ^ 16198981) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 618284846 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 842347039) ^ 64795926 = 496857068 := by
        calc
          (3 : ZMod 842347039) ^ 64795926 = (3 : ZMod 842347039) ^ (32397963 + 32397963) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 32397963 * (3 : ZMod 842347039) ^ 32397963 := by rw [pow_add]
          _ = 496857068 := by rw [factor_2_24]; decide
      change (3 : ZMod 842347039) ^ 64795926 ≠ 1
      rw [factor_2_25]
      decide
    ·
      have factor_3_0 : (3 : ZMod 842347039) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 842347039) ^ 2 = 9 := by
        calc
          (3 : ZMod 842347039) ^ 2 = (3 : ZMod 842347039) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 1 * (3 : ZMod 842347039) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 842347039) ^ 4 = 81 := by
        calc
          (3 : ZMod 842347039) ^ 4 = (3 : ZMod 842347039) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 2 * (3 : ZMod 842347039) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 842347039) ^ 9 = 19683 := by
        calc
          (3 : ZMod 842347039) ^ 9 = (3 : ZMod 842347039) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 4 * (3 : ZMod 842347039) ^ 4) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 842347039) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 842347039) ^ 18 = (3 : ZMod 842347039) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 9 * (3 : ZMod 842347039) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 842347039) ^ 37 = 625842584 := by
        calc
          (3 : ZMod 842347039) ^ 37 = (3 : ZMod 842347039) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 18 * (3 : ZMod 842347039) ^ 18) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 625842584 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 842347039) ^ 74 = 697439735 := by
        calc
          (3 : ZMod 842347039) ^ 74 = (3 : ZMod 842347039) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 37 * (3 : ZMod 842347039) ^ 37 := by rw [pow_add]
          _ = 697439735 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 842347039) ^ 149 = 259870403 := by
        calc
          (3 : ZMod 842347039) ^ 149 = (3 : ZMod 842347039) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 74 * (3 : ZMod 842347039) ^ 74) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 259870403 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 842347039) ^ 298 = 603350384 := by
        calc
          (3 : ZMod 842347039) ^ 298 = (3 : ZMod 842347039) ^ (149 + 149) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 149 * (3 : ZMod 842347039) ^ 149 := by rw [pow_add]
          _ = 603350384 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 842347039) ^ 597 = 27198135 := by
        calc
          (3 : ZMod 842347039) ^ 597 = (3 : ZMod 842347039) ^ (298 + 298 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 298 * (3 : ZMod 842347039) ^ 298) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 27198135 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 842347039) ^ 1195 = 142672757 := by
        calc
          (3 : ZMod 842347039) ^ 1195 = (3 : ZMod 842347039) ^ (597 + 597 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 597 * (3 : ZMod 842347039) ^ 597) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 142672757 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 842347039) ^ 2391 = 111240457 := by
        calc
          (3 : ZMod 842347039) ^ 2391 = (3 : ZMod 842347039) ^ (1195 + 1195 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 1195 * (3 : ZMod 842347039) ^ 1195) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 111240457 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 842347039) ^ 4782 = 746126157 := by
        calc
          (3 : ZMod 842347039) ^ 4782 = (3 : ZMod 842347039) ^ (2391 + 2391) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 2391 * (3 : ZMod 842347039) ^ 2391 := by rw [pow_add]
          _ = 746126157 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 842347039) ^ 9565 = 27465962 := by
        calc
          (3 : ZMod 842347039) ^ 9565 = (3 : ZMod 842347039) ^ (4782 + 4782 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 4782 * (3 : ZMod 842347039) ^ 4782) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 27465962 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 842347039) ^ 19130 = 15562292 := by
        calc
          (3 : ZMod 842347039) ^ 19130 = (3 : ZMod 842347039) ^ (9565 + 9565) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 9565 * (3 : ZMod 842347039) ^ 9565 := by rw [pow_add]
          _ = 15562292 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 842347039) ^ 38260 = 50416296 := by
        calc
          (3 : ZMod 842347039) ^ 38260 = (3 : ZMod 842347039) ^ (19130 + 19130) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 19130 * (3 : ZMod 842347039) ^ 19130 := by rw [pow_add]
          _ = 50416296 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 842347039) ^ 76521 = 645197501 := by
        calc
          (3 : ZMod 842347039) ^ 76521 = (3 : ZMod 842347039) ^ (38260 + 38260 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 38260 * (3 : ZMod 842347039) ^ 38260) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 645197501 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 842347039) ^ 153042 = 208501635 := by
        calc
          (3 : ZMod 842347039) ^ 153042 = (3 : ZMod 842347039) ^ (76521 + 76521) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 76521 * (3 : ZMod 842347039) ^ 76521 := by rw [pow_add]
          _ = 208501635 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 842347039) ^ 306085 = 70883862 := by
        calc
          (3 : ZMod 842347039) ^ 306085 = (3 : ZMod 842347039) ^ (153042 + 153042 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 153042 * (3 : ZMod 842347039) ^ 153042) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 70883862 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 842347039) ^ 612170 = 142674671 := by
        calc
          (3 : ZMod 842347039) ^ 612170 = (3 : ZMod 842347039) ^ (306085 + 306085) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 306085 * (3 : ZMod 842347039) ^ 306085 := by rw [pow_add]
          _ = 142674671 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 842347039) ^ 1224341 = 211181178 := by
        calc
          (3 : ZMod 842347039) ^ 1224341 = (3 : ZMod 842347039) ^ (612170 + 612170 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 612170 * (3 : ZMod 842347039) ^ 612170) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 211181178 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 842347039) ^ 2448683 = 484532807 := by
        calc
          (3 : ZMod 842347039) ^ 2448683 = (3 : ZMod 842347039) ^ (1224341 + 1224341 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 1224341 * (3 : ZMod 842347039) ^ 1224341) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 484532807 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 842347039) ^ 4897366 = 126573907 := by
        calc
          (3 : ZMod 842347039) ^ 4897366 = (3 : ZMod 842347039) ^ (2448683 + 2448683) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 2448683 * (3 : ZMod 842347039) ^ 2448683 := by rw [pow_add]
          _ = 126573907 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 842347039) ^ 9794733 = 384159573 := by
        calc
          (3 : ZMod 842347039) ^ 9794733 = (3 : ZMod 842347039) ^ (4897366 + 4897366 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 4897366 * (3 : ZMod 842347039) ^ 4897366) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 384159573 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 842347039) ^ 19589466 = 473898228 := by
        calc
          (3 : ZMod 842347039) ^ 19589466 = (3 : ZMod 842347039) ^ (9794733 + 9794733) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 9794733 * (3 : ZMod 842347039) ^ 9794733 := by rw [pow_add]
          _ = 473898228 := by rw [factor_3_23]; decide
      change (3 : ZMod 842347039) ^ 19589466 ≠ 1
      rw [factor_3_24]
      decide
    ·
      have factor_4_0 : (3 : ZMod 842347039) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 842347039) ^ 2 = 9 := by
        calc
          (3 : ZMod 842347039) ^ 2 = (3 : ZMod 842347039) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 1 * (3 : ZMod 842347039) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 842347039) ^ 5 = 243 := by
        calc
          (3 : ZMod 842347039) ^ 5 = (3 : ZMod 842347039) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 2 * (3 : ZMod 842347039) ^ 2) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 842347039) ^ 10 = 59049 := by
        calc
          (3 : ZMod 842347039) ^ 10 = (3 : ZMod 842347039) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 5 * (3 : ZMod 842347039) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 842347039) ^ 21 = 352188735 := by
        calc
          (3 : ZMod 842347039) ^ 21 = (3 : ZMod 842347039) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 10 * (3 : ZMod 842347039) ^ 10) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 352188735 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 842347039) ^ 42 = 457280892 := by
        calc
          (3 : ZMod 842347039) ^ 42 = (3 : ZMod 842347039) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 21 * (3 : ZMod 842347039) ^ 21 := by rw [pow_add]
          _ = 457280892 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 842347039) ^ 85 = 631831837 := by
        calc
          (3 : ZMod 842347039) ^ 85 = (3 : ZMod 842347039) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 42 * (3 : ZMod 842347039) ^ 42) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 631831837 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 842347039) ^ 170 = 119076041 := by
        calc
          (3 : ZMod 842347039) ^ 170 = (3 : ZMod 842347039) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 85 * (3 : ZMod 842347039) ^ 85 := by rw [pow_add]
          _ = 119076041 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 842347039) ^ 340 = 500108453 := by
        calc
          (3 : ZMod 842347039) ^ 340 = (3 : ZMod 842347039) ^ (170 + 170) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 170 * (3 : ZMod 842347039) ^ 170 := by rw [pow_add]
          _ = 500108453 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 842347039) ^ 681 = 770321848 := by
        calc
          (3 : ZMod 842347039) ^ 681 = (3 : ZMod 842347039) ^ (340 + 340 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 340 * (3 : ZMod 842347039) ^ 340) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 770321848 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 842347039) ^ 1362 = 205023421 := by
        calc
          (3 : ZMod 842347039) ^ 1362 = (3 : ZMod 842347039) ^ (681 + 681) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 681 * (3 : ZMod 842347039) ^ 681 := by rw [pow_add]
          _ = 205023421 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 842347039) ^ 2725 = 36799335 := by
        calc
          (3 : ZMod 842347039) ^ 2725 = (3 : ZMod 842347039) ^ (1362 + 1362 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 1362 * (3 : ZMod 842347039) ^ 1362) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 36799335 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 842347039) ^ 5450 = 262664265 := by
        calc
          (3 : ZMod 842347039) ^ 5450 = (3 : ZMod 842347039) ^ (2725 + 2725) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 2725 * (3 : ZMod 842347039) ^ 2725 := by rw [pow_add]
          _ = 262664265 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 842347039) ^ 10900 = 171032442 := by
        calc
          (3 : ZMod 842347039) ^ 10900 = (3 : ZMod 842347039) ^ (5450 + 5450) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 5450 * (3 : ZMod 842347039) ^ 5450 := by rw [pow_add]
          _ = 171032442 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 842347039) ^ 21801 = 488096533 := by
        calc
          (3 : ZMod 842347039) ^ 21801 = (3 : ZMod 842347039) ^ (10900 + 10900 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = ((3 : ZMod 842347039) ^ 10900 * (3 : ZMod 842347039) ^ 10900) * (3 : ZMod 842347039) := by rw [pow_succ, pow_add]
          _ = 488096533 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 842347039) ^ 43602 = 654949179 := by
        calc
          (3 : ZMod 842347039) ^ 43602 = (3 : ZMod 842347039) ^ (21801 + 21801) :=
            congrArg (fun n : ℕ => (3 : ZMod 842347039) ^ n) (by norm_num)
          _ = (3 : ZMod 842347039) ^ 21801 * (3 : ZMod 842347039) ^ 21801 := by rw [pow_add]
          _ = 654949179 := by rw [factor_4_14]; decide
      change (3 : ZMod 842347039) ^ 43602 ≠ 1
      rw [factor_4_15]
      decide

#print axioms prime_lucas_842347039

end TotientTailPeriodKiller
end Erdos249257
