import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime16731745181

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_33463490363 : Nat.Prime 33463490363 := by
  apply lucas_primality 33463490363 (2 : ZMod 33463490363)
  ·
      have fermat_0 : (2 : ZMod 33463490363) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 33463490363) ^ 3 = 8 := by
        calc
          (2 : ZMod 33463490363) ^ 3 = (2 : ZMod 33463490363) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 1 * (2 : ZMod 33463490363) ^ 1) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 33463490363) ^ 7 = 128 := by
        calc
          (2 : ZMod 33463490363) ^ 7 = (2 : ZMod 33463490363) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 3 * (2 : ZMod 33463490363) ^ 3) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 33463490363) ^ 15 = 32768 := by
        calc
          (2 : ZMod 33463490363) ^ 15 = (2 : ZMod 33463490363) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 7 * (2 : ZMod 33463490363) ^ 7) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 33463490363) ^ 31 = 2147483648 := by
        calc
          (2 : ZMod 33463490363) ^ 31 = (2 : ZMod 33463490363) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 15 * (2 : ZMod 33463490363) ^ 15) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 2147483648 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 33463490363) ^ 62 = 24389084198 := by
        calc
          (2 : ZMod 33463490363) ^ 62 = (2 : ZMod 33463490363) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 31 * (2 : ZMod 33463490363) ^ 31 := by rw [pow_add]
          _ = 24389084198 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 33463490363) ^ 124 = 1723504012 := by
        calc
          (2 : ZMod 33463490363) ^ 124 = (2 : ZMod 33463490363) ^ (62 + 62) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 62 * (2 : ZMod 33463490363) ^ 62 := by rw [pow_add]
          _ = 1723504012 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 33463490363) ^ 249 = 30745500942 := by
        calc
          (2 : ZMod 33463490363) ^ 249 = (2 : ZMod 33463490363) ^ (124 + 124 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 124 * (2 : ZMod 33463490363) ^ 124) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 30745500942 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 33463490363) ^ 498 = 2030645412 := by
        calc
          (2 : ZMod 33463490363) ^ 498 = (2 : ZMod 33463490363) ^ (249 + 249) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 249 * (2 : ZMod 33463490363) ^ 249 := by rw [pow_add]
          _ = 2030645412 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 33463490363) ^ 997 = 17209186083 := by
        calc
          (2 : ZMod 33463490363) ^ 997 = (2 : ZMod 33463490363) ^ (498 + 498 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 498 * (2 : ZMod 33463490363) ^ 498) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 17209186083 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 33463490363) ^ 1994 = 6641247045 := by
        calc
          (2 : ZMod 33463490363) ^ 1994 = (2 : ZMod 33463490363) ^ (997 + 997) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 997 * (2 : ZMod 33463490363) ^ 997 := by rw [pow_add]
          _ = 6641247045 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 33463490363) ^ 3989 = 22479360627 := by
        calc
          (2 : ZMod 33463490363) ^ 3989 = (2 : ZMod 33463490363) ^ (1994 + 1994 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 1994 * (2 : ZMod 33463490363) ^ 1994) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 22479360627 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 33463490363) ^ 7978 = 20701513010 := by
        calc
          (2 : ZMod 33463490363) ^ 7978 = (2 : ZMod 33463490363) ^ (3989 + 3989) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 3989 * (2 : ZMod 33463490363) ^ 3989 := by rw [pow_add]
          _ = 20701513010 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 33463490363) ^ 15956 = 672276357 := by
        calc
          (2 : ZMod 33463490363) ^ 15956 = (2 : ZMod 33463490363) ^ (7978 + 7978) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 7978 * (2 : ZMod 33463490363) ^ 7978 := by rw [pow_add]
          _ = 672276357 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 33463490363) ^ 31913 = 17419639170 := by
        calc
          (2 : ZMod 33463490363) ^ 31913 = (2 : ZMod 33463490363) ^ (15956 + 15956 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 15956 * (2 : ZMod 33463490363) ^ 15956) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 17419639170 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 33463490363) ^ 63826 = 32626506459 := by
        calc
          (2 : ZMod 33463490363) ^ 63826 = (2 : ZMod 33463490363) ^ (31913 + 31913) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 31913 * (2 : ZMod 33463490363) ^ 31913 := by rw [pow_add]
          _ = 32626506459 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 33463490363) ^ 127653 = 28416062364 := by
        calc
          (2 : ZMod 33463490363) ^ 127653 = (2 : ZMod 33463490363) ^ (63826 + 63826 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 63826 * (2 : ZMod 33463490363) ^ 63826) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 28416062364 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 33463490363) ^ 255306 = 13887695996 := by
        calc
          (2 : ZMod 33463490363) ^ 255306 = (2 : ZMod 33463490363) ^ (127653 + 127653) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 127653 * (2 : ZMod 33463490363) ^ 127653 := by rw [pow_add]
          _ = 13887695996 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 33463490363) ^ 510612 = 17428639140 := by
        calc
          (2 : ZMod 33463490363) ^ 510612 = (2 : ZMod 33463490363) ^ (255306 + 255306) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 255306 * (2 : ZMod 33463490363) ^ 255306 := by rw [pow_add]
          _ = 17428639140 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 33463490363) ^ 1021224 = 7182053055 := by
        calc
          (2 : ZMod 33463490363) ^ 1021224 = (2 : ZMod 33463490363) ^ (510612 + 510612) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 510612 * (2 : ZMod 33463490363) ^ 510612 := by rw [pow_add]
          _ = 7182053055 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 33463490363) ^ 2042449 = 27925656049 := by
        calc
          (2 : ZMod 33463490363) ^ 2042449 = (2 : ZMod 33463490363) ^ (1021224 + 1021224 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 1021224 * (2 : ZMod 33463490363) ^ 1021224) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 27925656049 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 33463490363) ^ 4084898 = 6160025011 := by
        calc
          (2 : ZMod 33463490363) ^ 4084898 = (2 : ZMod 33463490363) ^ (2042449 + 2042449) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 2042449 * (2 : ZMod 33463490363) ^ 2042449 := by rw [pow_add]
          _ = 6160025011 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 33463490363) ^ 8169797 = 8460743968 := by
        calc
          (2 : ZMod 33463490363) ^ 8169797 = (2 : ZMod 33463490363) ^ (4084898 + 4084898 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 4084898 * (2 : ZMod 33463490363) ^ 4084898) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 8460743968 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 33463490363) ^ 16339594 = 14066187535 := by
        calc
          (2 : ZMod 33463490363) ^ 16339594 = (2 : ZMod 33463490363) ^ (8169797 + 8169797) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 8169797 * (2 : ZMod 33463490363) ^ 8169797 := by rw [pow_add]
          _ = 14066187535 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 33463490363) ^ 32679189 = 18944728554 := by
        calc
          (2 : ZMod 33463490363) ^ 32679189 = (2 : ZMod 33463490363) ^ (16339594 + 16339594 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 16339594 * (2 : ZMod 33463490363) ^ 16339594) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 18944728554 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 33463490363) ^ 65358379 = 6868827226 := by
        calc
          (2 : ZMod 33463490363) ^ 65358379 = (2 : ZMod 33463490363) ^ (32679189 + 32679189 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 32679189 * (2 : ZMod 33463490363) ^ 32679189) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 6868827226 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 33463490363) ^ 130716759 = 31943024352 := by
        calc
          (2 : ZMod 33463490363) ^ 130716759 = (2 : ZMod 33463490363) ^ (65358379 + 65358379 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 65358379 * (2 : ZMod 33463490363) ^ 65358379) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 31943024352 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 33463490363) ^ 261433518 = 24750987871 := by
        calc
          (2 : ZMod 33463490363) ^ 261433518 = (2 : ZMod 33463490363) ^ (130716759 + 130716759) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 130716759 * (2 : ZMod 33463490363) ^ 130716759 := by rw [pow_add]
          _ = 24750987871 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 33463490363) ^ 522867036 = 30502036566 := by
        calc
          (2 : ZMod 33463490363) ^ 522867036 = (2 : ZMod 33463490363) ^ (261433518 + 261433518) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 261433518 * (2 : ZMod 33463490363) ^ 261433518 := by rw [pow_add]
          _ = 30502036566 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 33463490363) ^ 1045734073 = 20080739381 := by
        calc
          (2 : ZMod 33463490363) ^ 1045734073 = (2 : ZMod 33463490363) ^ (522867036 + 522867036 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 522867036 * (2 : ZMod 33463490363) ^ 522867036) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 20080739381 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 33463490363) ^ 2091468147 = 7376277149 := by
        calc
          (2 : ZMod 33463490363) ^ 2091468147 = (2 : ZMod 33463490363) ^ (1045734073 + 1045734073 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 1045734073 * (2 : ZMod 33463490363) ^ 1045734073) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 7376277149 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 33463490363) ^ 4182936295 = 17019341659 := by
        calc
          (2 : ZMod 33463490363) ^ 4182936295 = (2 : ZMod 33463490363) ^ (2091468147 + 2091468147 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 2091468147 * (2 : ZMod 33463490363) ^ 2091468147) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 17019341659 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 33463490363) ^ 8365872590 = 33106053497 := by
        calc
          (2 : ZMod 33463490363) ^ 8365872590 = (2 : ZMod 33463490363) ^ (4182936295 + 4182936295) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 4182936295 * (2 : ZMod 33463490363) ^ 4182936295 := by rw [pow_add]
          _ = 33106053497 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 33463490363) ^ 16731745181 = 33463490362 := by
        calc
          (2 : ZMod 33463490363) ^ 16731745181 = (2 : ZMod 33463490363) ^ (8365872590 + 8365872590 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 8365872590 * (2 : ZMod 33463490363) ^ 8365872590) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 33463490362 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 33463490363) ^ 33463490362 = 1 := by
        calc
          (2 : ZMod 33463490363) ^ 33463490362 = (2 : ZMod 33463490363) ^ (16731745181 + 16731745181) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 16731745181 * (2 : ZMod 33463490363) ^ 16731745181 := by rw [pow_add]
          _ = 1 := by rw [fermat_33]; decide
      simpa using fermat_34
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (16731745181, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (16731745181, 1)] : List FactorBlock).map factorBlockValue).prod = 33463490363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_16731745181) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 33463490363) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 33463490363) ^ 3 = 8 := by
        calc
          (2 : ZMod 33463490363) ^ 3 = (2 : ZMod 33463490363) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 1 * (2 : ZMod 33463490363) ^ 1) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 33463490363) ^ 7 = 128 := by
        calc
          (2 : ZMod 33463490363) ^ 7 = (2 : ZMod 33463490363) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 3 * (2 : ZMod 33463490363) ^ 3) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 33463490363) ^ 15 = 32768 := by
        calc
          (2 : ZMod 33463490363) ^ 15 = (2 : ZMod 33463490363) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 7 * (2 : ZMod 33463490363) ^ 7) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 33463490363) ^ 31 = 2147483648 := by
        calc
          (2 : ZMod 33463490363) ^ 31 = (2 : ZMod 33463490363) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 15 * (2 : ZMod 33463490363) ^ 15) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 2147483648 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 33463490363) ^ 62 = 24389084198 := by
        calc
          (2 : ZMod 33463490363) ^ 62 = (2 : ZMod 33463490363) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 31 * (2 : ZMod 33463490363) ^ 31 := by rw [pow_add]
          _ = 24389084198 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 33463490363) ^ 124 = 1723504012 := by
        calc
          (2 : ZMod 33463490363) ^ 124 = (2 : ZMod 33463490363) ^ (62 + 62) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 62 * (2 : ZMod 33463490363) ^ 62 := by rw [pow_add]
          _ = 1723504012 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 33463490363) ^ 249 = 30745500942 := by
        calc
          (2 : ZMod 33463490363) ^ 249 = (2 : ZMod 33463490363) ^ (124 + 124 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 124 * (2 : ZMod 33463490363) ^ 124) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 30745500942 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 33463490363) ^ 498 = 2030645412 := by
        calc
          (2 : ZMod 33463490363) ^ 498 = (2 : ZMod 33463490363) ^ (249 + 249) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 249 * (2 : ZMod 33463490363) ^ 249 := by rw [pow_add]
          _ = 2030645412 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 33463490363) ^ 997 = 17209186083 := by
        calc
          (2 : ZMod 33463490363) ^ 997 = (2 : ZMod 33463490363) ^ (498 + 498 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 498 * (2 : ZMod 33463490363) ^ 498) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 17209186083 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 33463490363) ^ 1994 = 6641247045 := by
        calc
          (2 : ZMod 33463490363) ^ 1994 = (2 : ZMod 33463490363) ^ (997 + 997) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 997 * (2 : ZMod 33463490363) ^ 997 := by rw [pow_add]
          _ = 6641247045 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 33463490363) ^ 3989 = 22479360627 := by
        calc
          (2 : ZMod 33463490363) ^ 3989 = (2 : ZMod 33463490363) ^ (1994 + 1994 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 1994 * (2 : ZMod 33463490363) ^ 1994) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 22479360627 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 33463490363) ^ 7978 = 20701513010 := by
        calc
          (2 : ZMod 33463490363) ^ 7978 = (2 : ZMod 33463490363) ^ (3989 + 3989) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 3989 * (2 : ZMod 33463490363) ^ 3989 := by rw [pow_add]
          _ = 20701513010 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 33463490363) ^ 15956 = 672276357 := by
        calc
          (2 : ZMod 33463490363) ^ 15956 = (2 : ZMod 33463490363) ^ (7978 + 7978) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 7978 * (2 : ZMod 33463490363) ^ 7978 := by rw [pow_add]
          _ = 672276357 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 33463490363) ^ 31913 = 17419639170 := by
        calc
          (2 : ZMod 33463490363) ^ 31913 = (2 : ZMod 33463490363) ^ (15956 + 15956 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 15956 * (2 : ZMod 33463490363) ^ 15956) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 17419639170 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 33463490363) ^ 63826 = 32626506459 := by
        calc
          (2 : ZMod 33463490363) ^ 63826 = (2 : ZMod 33463490363) ^ (31913 + 31913) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 31913 * (2 : ZMod 33463490363) ^ 31913 := by rw [pow_add]
          _ = 32626506459 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 33463490363) ^ 127653 = 28416062364 := by
        calc
          (2 : ZMod 33463490363) ^ 127653 = (2 : ZMod 33463490363) ^ (63826 + 63826 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 63826 * (2 : ZMod 33463490363) ^ 63826) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 28416062364 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 33463490363) ^ 255306 = 13887695996 := by
        calc
          (2 : ZMod 33463490363) ^ 255306 = (2 : ZMod 33463490363) ^ (127653 + 127653) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 127653 * (2 : ZMod 33463490363) ^ 127653 := by rw [pow_add]
          _ = 13887695996 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 33463490363) ^ 510612 = 17428639140 := by
        calc
          (2 : ZMod 33463490363) ^ 510612 = (2 : ZMod 33463490363) ^ (255306 + 255306) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 255306 * (2 : ZMod 33463490363) ^ 255306 := by rw [pow_add]
          _ = 17428639140 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 33463490363) ^ 1021224 = 7182053055 := by
        calc
          (2 : ZMod 33463490363) ^ 1021224 = (2 : ZMod 33463490363) ^ (510612 + 510612) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 510612 * (2 : ZMod 33463490363) ^ 510612 := by rw [pow_add]
          _ = 7182053055 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 33463490363) ^ 2042449 = 27925656049 := by
        calc
          (2 : ZMod 33463490363) ^ 2042449 = (2 : ZMod 33463490363) ^ (1021224 + 1021224 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 1021224 * (2 : ZMod 33463490363) ^ 1021224) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 27925656049 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 33463490363) ^ 4084898 = 6160025011 := by
        calc
          (2 : ZMod 33463490363) ^ 4084898 = (2 : ZMod 33463490363) ^ (2042449 + 2042449) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 2042449 * (2 : ZMod 33463490363) ^ 2042449 := by rw [pow_add]
          _ = 6160025011 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 33463490363) ^ 8169797 = 8460743968 := by
        calc
          (2 : ZMod 33463490363) ^ 8169797 = (2 : ZMod 33463490363) ^ (4084898 + 4084898 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 4084898 * (2 : ZMod 33463490363) ^ 4084898) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 8460743968 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 33463490363) ^ 16339594 = 14066187535 := by
        calc
          (2 : ZMod 33463490363) ^ 16339594 = (2 : ZMod 33463490363) ^ (8169797 + 8169797) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 8169797 * (2 : ZMod 33463490363) ^ 8169797 := by rw [pow_add]
          _ = 14066187535 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 33463490363) ^ 32679189 = 18944728554 := by
        calc
          (2 : ZMod 33463490363) ^ 32679189 = (2 : ZMod 33463490363) ^ (16339594 + 16339594 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 16339594 * (2 : ZMod 33463490363) ^ 16339594) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 18944728554 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 33463490363) ^ 65358379 = 6868827226 := by
        calc
          (2 : ZMod 33463490363) ^ 65358379 = (2 : ZMod 33463490363) ^ (32679189 + 32679189 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 32679189 * (2 : ZMod 33463490363) ^ 32679189) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 6868827226 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 33463490363) ^ 130716759 = 31943024352 := by
        calc
          (2 : ZMod 33463490363) ^ 130716759 = (2 : ZMod 33463490363) ^ (65358379 + 65358379 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 65358379 * (2 : ZMod 33463490363) ^ 65358379) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 31943024352 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 33463490363) ^ 261433518 = 24750987871 := by
        calc
          (2 : ZMod 33463490363) ^ 261433518 = (2 : ZMod 33463490363) ^ (130716759 + 130716759) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 130716759 * (2 : ZMod 33463490363) ^ 130716759 := by rw [pow_add]
          _ = 24750987871 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 33463490363) ^ 522867036 = 30502036566 := by
        calc
          (2 : ZMod 33463490363) ^ 522867036 = (2 : ZMod 33463490363) ^ (261433518 + 261433518) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 261433518 * (2 : ZMod 33463490363) ^ 261433518 := by rw [pow_add]
          _ = 30502036566 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 33463490363) ^ 1045734073 = 20080739381 := by
        calc
          (2 : ZMod 33463490363) ^ 1045734073 = (2 : ZMod 33463490363) ^ (522867036 + 522867036 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 522867036 * (2 : ZMod 33463490363) ^ 522867036) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 20080739381 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 33463490363) ^ 2091468147 = 7376277149 := by
        calc
          (2 : ZMod 33463490363) ^ 2091468147 = (2 : ZMod 33463490363) ^ (1045734073 + 1045734073 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 1045734073 * (2 : ZMod 33463490363) ^ 1045734073) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 7376277149 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 33463490363) ^ 4182936295 = 17019341659 := by
        calc
          (2 : ZMod 33463490363) ^ 4182936295 = (2 : ZMod 33463490363) ^ (2091468147 + 2091468147 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 2091468147 * (2 : ZMod 33463490363) ^ 2091468147) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 17019341659 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 33463490363) ^ 8365872590 = 33106053497 := by
        calc
          (2 : ZMod 33463490363) ^ 8365872590 = (2 : ZMod 33463490363) ^ (4182936295 + 4182936295) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 4182936295 * (2 : ZMod 33463490363) ^ 4182936295 := by rw [pow_add]
          _ = 33106053497 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 33463490363) ^ 16731745181 = 33463490362 := by
        calc
          (2 : ZMod 33463490363) ^ 16731745181 = (2 : ZMod 33463490363) ^ (8365872590 + 8365872590 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = ((2 : ZMod 33463490363) ^ 8365872590 * (2 : ZMod 33463490363) ^ 8365872590) * (2 : ZMod 33463490363) := by rw [pow_succ, pow_add]
          _ = 33463490362 := by rw [factor_0_32]; decide
      change (2 : ZMod 33463490363) ^ 16731745181 ≠ 1
      rw [factor_0_33]
      decide
    ·
      have factor_1_0 : (2 : ZMod 33463490363) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 33463490363) ^ 2 = 4 := by
        calc
          (2 : ZMod 33463490363) ^ 2 = (2 : ZMod 33463490363) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 33463490363) ^ n) (by norm_num)
          _ = (2 : ZMod 33463490363) ^ 1 * (2 : ZMod 33463490363) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      change (2 : ZMod 33463490363) ^ 2 ≠ 1
      rw [factor_1_1]
      decide

#print axioms prime_lucas_33463490363

end TotientTailPeriodKiller
end Erdos249257
