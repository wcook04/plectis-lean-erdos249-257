import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime830406971

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_79719069217 : Nat.Prime 79719069217 := by
  apply lucas_primality 79719069217 (10 : ZMod 79719069217)
  ·
      have fermat_0 : (10 : ZMod 79719069217) ^ 1 = 10 := by norm_num
      have fermat_1 : (10 : ZMod 79719069217) ^ 2 = 100 := by
        calc
          (10 : ZMod 79719069217) ^ 2 = (10 : ZMod 79719069217) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 1 * (10 : ZMod 79719069217) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [fermat_0]; decide
      have fermat_2 : (10 : ZMod 79719069217) ^ 4 = 10000 := by
        calc
          (10 : ZMod 79719069217) ^ 4 = (10 : ZMod 79719069217) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 2 * (10 : ZMod 79719069217) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [fermat_1]; decide
      have fermat_3 : (10 : ZMod 79719069217) ^ 9 = 1000000000 := by
        calc
          (10 : ZMod 79719069217) ^ 9 = (10 : ZMod 79719069217) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 4 * (10 : ZMod 79719069217) ^ 4) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 1000000000 := by rw [fermat_2]; decide
      have fermat_4 : (10 : ZMod 79719069217) ^ 18 = 9788491150 := by
        calc
          (10 : ZMod 79719069217) ^ 18 = (10 : ZMod 79719069217) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 9 * (10 : ZMod 79719069217) ^ 9 := by rw [pow_add]
          _ = 9788491150 := by rw [fermat_3]; decide
      have fermat_5 : (10 : ZMod 79719069217) ^ 37 = 7044471815 := by
        calc
          (10 : ZMod 79719069217) ^ 37 = (10 : ZMod 79719069217) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 18 * (10 : ZMod 79719069217) ^ 18) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 7044471815 := by rw [fermat_4]; decide
      have fermat_6 : (10 : ZMod 79719069217) ^ 74 = 30711555239 := by
        calc
          (10 : ZMod 79719069217) ^ 74 = (10 : ZMod 79719069217) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 37 * (10 : ZMod 79719069217) ^ 37 := by rw [pow_add]
          _ = 30711555239 := by rw [fermat_5]; decide
      have fermat_7 : (10 : ZMod 79719069217) ^ 148 = 22304628963 := by
        calc
          (10 : ZMod 79719069217) ^ 148 = (10 : ZMod 79719069217) ^ (74 + 74) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 74 * (10 : ZMod 79719069217) ^ 74 := by rw [pow_add]
          _ = 22304628963 := by rw [fermat_6]; decide
      have fermat_8 : (10 : ZMod 79719069217) ^ 296 = 35350809554 := by
        calc
          (10 : ZMod 79719069217) ^ 296 = (10 : ZMod 79719069217) ^ (148 + 148) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 148 * (10 : ZMod 79719069217) ^ 148 := by rw [pow_add]
          _ = 35350809554 := by rw [fermat_7]; decide
      have fermat_9 : (10 : ZMod 79719069217) ^ 593 = 48450965519 := by
        calc
          (10 : ZMod 79719069217) ^ 593 = (10 : ZMod 79719069217) ^ (296 + 296 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 296 * (10 : ZMod 79719069217) ^ 296) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 48450965519 := by rw [fermat_8]; decide
      have fermat_10 : (10 : ZMod 79719069217) ^ 1187 = 12083543056 := by
        calc
          (10 : ZMod 79719069217) ^ 1187 = (10 : ZMod 79719069217) ^ (593 + 593 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 593 * (10 : ZMod 79719069217) ^ 593) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 12083543056 := by rw [fermat_9]; decide
      have fermat_11 : (10 : ZMod 79719069217) ^ 2375 = 15329475387 := by
        calc
          (10 : ZMod 79719069217) ^ 2375 = (10 : ZMod 79719069217) ^ (1187 + 1187 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 1187 * (10 : ZMod 79719069217) ^ 1187) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 15329475387 := by rw [fermat_10]; decide
      have fermat_12 : (10 : ZMod 79719069217) ^ 4751 = 72619318264 := by
        calc
          (10 : ZMod 79719069217) ^ 4751 = (10 : ZMod 79719069217) ^ (2375 + 2375 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 2375 * (10 : ZMod 79719069217) ^ 2375) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 72619318264 := by rw [fermat_11]; decide
      have fermat_13 : (10 : ZMod 79719069217) ^ 9503 = 34616463504 := by
        calc
          (10 : ZMod 79719069217) ^ 9503 = (10 : ZMod 79719069217) ^ (4751 + 4751 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 4751 * (10 : ZMod 79719069217) ^ 4751) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 34616463504 := by rw [fermat_12]; decide
      have fermat_14 : (10 : ZMod 79719069217) ^ 19006 = 13023334279 := by
        calc
          (10 : ZMod 79719069217) ^ 19006 = (10 : ZMod 79719069217) ^ (9503 + 9503) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 9503 * (10 : ZMod 79719069217) ^ 9503 := by rw [pow_add]
          _ = 13023334279 := by rw [fermat_13]; decide
      have fermat_15 : (10 : ZMod 79719069217) ^ 38013 = 33708935539 := by
        calc
          (10 : ZMod 79719069217) ^ 38013 = (10 : ZMod 79719069217) ^ (19006 + 19006 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 19006 * (10 : ZMod 79719069217) ^ 19006) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 33708935539 := by rw [fermat_14]; decide
      have fermat_16 : (10 : ZMod 79719069217) ^ 76026 = 43236169219 := by
        calc
          (10 : ZMod 79719069217) ^ 76026 = (10 : ZMod 79719069217) ^ (38013 + 38013) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 38013 * (10 : ZMod 79719069217) ^ 38013 := by rw [pow_add]
          _ = 43236169219 := by rw [fermat_15]; decide
      have fermat_17 : (10 : ZMod 79719069217) ^ 152052 = 39083036236 := by
        calc
          (10 : ZMod 79719069217) ^ 152052 = (10 : ZMod 79719069217) ^ (76026 + 76026) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 76026 * (10 : ZMod 79719069217) ^ 76026 := by rw [pow_add]
          _ = 39083036236 := by rw [fermat_16]; decide
      have fermat_18 : (10 : ZMod 79719069217) ^ 304104 = 23158377925 := by
        calc
          (10 : ZMod 79719069217) ^ 304104 = (10 : ZMod 79719069217) ^ (152052 + 152052) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 152052 * (10 : ZMod 79719069217) ^ 152052 := by rw [pow_add]
          _ = 23158377925 := by rw [fermat_17]; decide
      have fermat_19 : (10 : ZMod 79719069217) ^ 608208 = 34819518344 := by
        calc
          (10 : ZMod 79719069217) ^ 608208 = (10 : ZMod 79719069217) ^ (304104 + 304104) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 304104 * (10 : ZMod 79719069217) ^ 304104 := by rw [pow_add]
          _ = 34819518344 := by rw [fermat_18]; decide
      have fermat_20 : (10 : ZMod 79719069217) ^ 1216416 = 71839738873 := by
        calc
          (10 : ZMod 79719069217) ^ 1216416 = (10 : ZMod 79719069217) ^ (608208 + 608208) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 608208 * (10 : ZMod 79719069217) ^ 608208 := by rw [pow_add]
          _ = 71839738873 := by rw [fermat_19]; decide
      have fermat_21 : (10 : ZMod 79719069217) ^ 2432832 = 35268276508 := by
        calc
          (10 : ZMod 79719069217) ^ 2432832 = (10 : ZMod 79719069217) ^ (1216416 + 1216416) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 1216416 * (10 : ZMod 79719069217) ^ 1216416 := by rw [pow_add]
          _ = 35268276508 := by rw [fermat_20]; decide
      have fermat_22 : (10 : ZMod 79719069217) ^ 4865665 = 63811085951 := by
        calc
          (10 : ZMod 79719069217) ^ 4865665 = (10 : ZMod 79719069217) ^ (2432832 + 2432832 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 2432832 * (10 : ZMod 79719069217) ^ 2432832) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 63811085951 := by rw [fermat_21]; decide
      have fermat_23 : (10 : ZMod 79719069217) ^ 9731331 = 40929005203 := by
        calc
          (10 : ZMod 79719069217) ^ 9731331 = (10 : ZMod 79719069217) ^ (4865665 + 4865665 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 4865665 * (10 : ZMod 79719069217) ^ 4865665) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 40929005203 := by rw [fermat_22]; decide
      have fermat_24 : (10 : ZMod 79719069217) ^ 19462663 = 38719598161 := by
        calc
          (10 : ZMod 79719069217) ^ 19462663 = (10 : ZMod 79719069217) ^ (9731331 + 9731331 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 9731331 * (10 : ZMod 79719069217) ^ 9731331) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 38719598161 := by rw [fermat_23]; decide
      have fermat_25 : (10 : ZMod 79719069217) ^ 38925326 = 56691358859 := by
        calc
          (10 : ZMod 79719069217) ^ 38925326 = (10 : ZMod 79719069217) ^ (19462663 + 19462663) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 19462663 * (10 : ZMod 79719069217) ^ 19462663 := by rw [pow_add]
          _ = 56691358859 := by rw [fermat_24]; decide
      have fermat_26 : (10 : ZMod 79719069217) ^ 77850653 = 66310853715 := by
        calc
          (10 : ZMod 79719069217) ^ 77850653 = (10 : ZMod 79719069217) ^ (38925326 + 38925326 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 38925326 * (10 : ZMod 79719069217) ^ 38925326) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 66310853715 := by rw [fermat_25]; decide
      have fermat_27 : (10 : ZMod 79719069217) ^ 155701307 = 21931824478 := by
        calc
          (10 : ZMod 79719069217) ^ 155701307 = (10 : ZMod 79719069217) ^ (77850653 + 77850653 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 77850653 * (10 : ZMod 79719069217) ^ 77850653) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 21931824478 := by rw [fermat_26]; decide
      have fermat_28 : (10 : ZMod 79719069217) ^ 311402614 = 53981044005 := by
        calc
          (10 : ZMod 79719069217) ^ 311402614 = (10 : ZMod 79719069217) ^ (155701307 + 155701307) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 155701307 * (10 : ZMod 79719069217) ^ 155701307 := by rw [pow_add]
          _ = 53981044005 := by rw [fermat_27]; decide
      have fermat_29 : (10 : ZMod 79719069217) ^ 622805228 = 59486095895 := by
        calc
          (10 : ZMod 79719069217) ^ 622805228 = (10 : ZMod 79719069217) ^ (311402614 + 311402614) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 311402614 * (10 : ZMod 79719069217) ^ 311402614 := by rw [pow_add]
          _ = 59486095895 := by rw [fermat_28]; decide
      have fermat_30 : (10 : ZMod 79719069217) ^ 1245610456 = 20057735098 := by
        calc
          (10 : ZMod 79719069217) ^ 1245610456 = (10 : ZMod 79719069217) ^ (622805228 + 622805228) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 622805228 * (10 : ZMod 79719069217) ^ 622805228 := by rw [pow_add]
          _ = 20057735098 := by rw [fermat_29]; decide
      have fermat_31 : (10 : ZMod 79719069217) ^ 2491220913 = 35505691636 := by
        calc
          (10 : ZMod 79719069217) ^ 2491220913 = (10 : ZMod 79719069217) ^ (1245610456 + 1245610456 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 1245610456 * (10 : ZMod 79719069217) ^ 1245610456) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 35505691636 := by rw [fermat_30]; decide
      have fermat_32 : (10 : ZMod 79719069217) ^ 4982441826 = 38226199379 := by
        calc
          (10 : ZMod 79719069217) ^ 4982441826 = (10 : ZMod 79719069217) ^ (2491220913 + 2491220913) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 2491220913 * (10 : ZMod 79719069217) ^ 2491220913 := by rw [pow_add]
          _ = 38226199379 := by rw [fermat_31]; decide
      have fermat_33 : (10 : ZMod 79719069217) ^ 9964883652 = 48676950511 := by
        calc
          (10 : ZMod 79719069217) ^ 9964883652 = (10 : ZMod 79719069217) ^ (4982441826 + 4982441826) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 4982441826 * (10 : ZMod 79719069217) ^ 4982441826 := by rw [pow_add]
          _ = 48676950511 := by rw [fermat_32]; decide
      have fermat_34 : (10 : ZMod 79719069217) ^ 19929767304 = 66081518220 := by
        calc
          (10 : ZMod 79719069217) ^ 19929767304 = (10 : ZMod 79719069217) ^ (9964883652 + 9964883652) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 9964883652 * (10 : ZMod 79719069217) ^ 9964883652 := by rw [pow_add]
          _ = 66081518220 := by rw [fermat_33]; decide
      have fermat_35 : (10 : ZMod 79719069217) ^ 39859534608 = 79719069216 := by
        calc
          (10 : ZMod 79719069217) ^ 39859534608 = (10 : ZMod 79719069217) ^ (19929767304 + 19929767304) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 19929767304 * (10 : ZMod 79719069217) ^ 19929767304 := by rw [pow_add]
          _ = 79719069216 := by rw [fermat_34]; decide
      have fermat_36 : (10 : ZMod 79719069217) ^ 79719069216 = 1 := by
        calc
          (10 : ZMod 79719069217) ^ 79719069216 = (10 : ZMod 79719069217) ^ (39859534608 + 39859534608) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 39859534608 * (10 : ZMod 79719069217) ^ 39859534608 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (830406971, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (830406971, 1)] : List FactorBlock).map factorBlockValue).prod = 79719069217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_830406971) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (10 : ZMod 79719069217) ^ 1 = 10 := by norm_num
      have factor_0_1 : (10 : ZMod 79719069217) ^ 2 = 100 := by
        calc
          (10 : ZMod 79719069217) ^ 2 = (10 : ZMod 79719069217) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 1 * (10 : ZMod 79719069217) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_0_0]; decide
      have factor_0_2 : (10 : ZMod 79719069217) ^ 4 = 10000 := by
        calc
          (10 : ZMod 79719069217) ^ 4 = (10 : ZMod 79719069217) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 2 * (10 : ZMod 79719069217) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [factor_0_1]; decide
      have factor_0_3 : (10 : ZMod 79719069217) ^ 9 = 1000000000 := by
        calc
          (10 : ZMod 79719069217) ^ 9 = (10 : ZMod 79719069217) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 4 * (10 : ZMod 79719069217) ^ 4) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 1000000000 := by rw [factor_0_2]; decide
      have factor_0_4 : (10 : ZMod 79719069217) ^ 18 = 9788491150 := by
        calc
          (10 : ZMod 79719069217) ^ 18 = (10 : ZMod 79719069217) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 9 * (10 : ZMod 79719069217) ^ 9 := by rw [pow_add]
          _ = 9788491150 := by rw [factor_0_3]; decide
      have factor_0_5 : (10 : ZMod 79719069217) ^ 37 = 7044471815 := by
        calc
          (10 : ZMod 79719069217) ^ 37 = (10 : ZMod 79719069217) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 18 * (10 : ZMod 79719069217) ^ 18) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 7044471815 := by rw [factor_0_4]; decide
      have factor_0_6 : (10 : ZMod 79719069217) ^ 74 = 30711555239 := by
        calc
          (10 : ZMod 79719069217) ^ 74 = (10 : ZMod 79719069217) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 37 * (10 : ZMod 79719069217) ^ 37 := by rw [pow_add]
          _ = 30711555239 := by rw [factor_0_5]; decide
      have factor_0_7 : (10 : ZMod 79719069217) ^ 148 = 22304628963 := by
        calc
          (10 : ZMod 79719069217) ^ 148 = (10 : ZMod 79719069217) ^ (74 + 74) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 74 * (10 : ZMod 79719069217) ^ 74 := by rw [pow_add]
          _ = 22304628963 := by rw [factor_0_6]; decide
      have factor_0_8 : (10 : ZMod 79719069217) ^ 296 = 35350809554 := by
        calc
          (10 : ZMod 79719069217) ^ 296 = (10 : ZMod 79719069217) ^ (148 + 148) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 148 * (10 : ZMod 79719069217) ^ 148 := by rw [pow_add]
          _ = 35350809554 := by rw [factor_0_7]; decide
      have factor_0_9 : (10 : ZMod 79719069217) ^ 593 = 48450965519 := by
        calc
          (10 : ZMod 79719069217) ^ 593 = (10 : ZMod 79719069217) ^ (296 + 296 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 296 * (10 : ZMod 79719069217) ^ 296) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 48450965519 := by rw [factor_0_8]; decide
      have factor_0_10 : (10 : ZMod 79719069217) ^ 1187 = 12083543056 := by
        calc
          (10 : ZMod 79719069217) ^ 1187 = (10 : ZMod 79719069217) ^ (593 + 593 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 593 * (10 : ZMod 79719069217) ^ 593) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 12083543056 := by rw [factor_0_9]; decide
      have factor_0_11 : (10 : ZMod 79719069217) ^ 2375 = 15329475387 := by
        calc
          (10 : ZMod 79719069217) ^ 2375 = (10 : ZMod 79719069217) ^ (1187 + 1187 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 1187 * (10 : ZMod 79719069217) ^ 1187) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 15329475387 := by rw [factor_0_10]; decide
      have factor_0_12 : (10 : ZMod 79719069217) ^ 4751 = 72619318264 := by
        calc
          (10 : ZMod 79719069217) ^ 4751 = (10 : ZMod 79719069217) ^ (2375 + 2375 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 2375 * (10 : ZMod 79719069217) ^ 2375) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 72619318264 := by rw [factor_0_11]; decide
      have factor_0_13 : (10 : ZMod 79719069217) ^ 9503 = 34616463504 := by
        calc
          (10 : ZMod 79719069217) ^ 9503 = (10 : ZMod 79719069217) ^ (4751 + 4751 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 4751 * (10 : ZMod 79719069217) ^ 4751) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 34616463504 := by rw [factor_0_12]; decide
      have factor_0_14 : (10 : ZMod 79719069217) ^ 19006 = 13023334279 := by
        calc
          (10 : ZMod 79719069217) ^ 19006 = (10 : ZMod 79719069217) ^ (9503 + 9503) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 9503 * (10 : ZMod 79719069217) ^ 9503 := by rw [pow_add]
          _ = 13023334279 := by rw [factor_0_13]; decide
      have factor_0_15 : (10 : ZMod 79719069217) ^ 38013 = 33708935539 := by
        calc
          (10 : ZMod 79719069217) ^ 38013 = (10 : ZMod 79719069217) ^ (19006 + 19006 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 19006 * (10 : ZMod 79719069217) ^ 19006) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 33708935539 := by rw [factor_0_14]; decide
      have factor_0_16 : (10 : ZMod 79719069217) ^ 76026 = 43236169219 := by
        calc
          (10 : ZMod 79719069217) ^ 76026 = (10 : ZMod 79719069217) ^ (38013 + 38013) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 38013 * (10 : ZMod 79719069217) ^ 38013 := by rw [pow_add]
          _ = 43236169219 := by rw [factor_0_15]; decide
      have factor_0_17 : (10 : ZMod 79719069217) ^ 152052 = 39083036236 := by
        calc
          (10 : ZMod 79719069217) ^ 152052 = (10 : ZMod 79719069217) ^ (76026 + 76026) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 76026 * (10 : ZMod 79719069217) ^ 76026 := by rw [pow_add]
          _ = 39083036236 := by rw [factor_0_16]; decide
      have factor_0_18 : (10 : ZMod 79719069217) ^ 304104 = 23158377925 := by
        calc
          (10 : ZMod 79719069217) ^ 304104 = (10 : ZMod 79719069217) ^ (152052 + 152052) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 152052 * (10 : ZMod 79719069217) ^ 152052 := by rw [pow_add]
          _ = 23158377925 := by rw [factor_0_17]; decide
      have factor_0_19 : (10 : ZMod 79719069217) ^ 608208 = 34819518344 := by
        calc
          (10 : ZMod 79719069217) ^ 608208 = (10 : ZMod 79719069217) ^ (304104 + 304104) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 304104 * (10 : ZMod 79719069217) ^ 304104 := by rw [pow_add]
          _ = 34819518344 := by rw [factor_0_18]; decide
      have factor_0_20 : (10 : ZMod 79719069217) ^ 1216416 = 71839738873 := by
        calc
          (10 : ZMod 79719069217) ^ 1216416 = (10 : ZMod 79719069217) ^ (608208 + 608208) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 608208 * (10 : ZMod 79719069217) ^ 608208 := by rw [pow_add]
          _ = 71839738873 := by rw [factor_0_19]; decide
      have factor_0_21 : (10 : ZMod 79719069217) ^ 2432832 = 35268276508 := by
        calc
          (10 : ZMod 79719069217) ^ 2432832 = (10 : ZMod 79719069217) ^ (1216416 + 1216416) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 1216416 * (10 : ZMod 79719069217) ^ 1216416 := by rw [pow_add]
          _ = 35268276508 := by rw [factor_0_20]; decide
      have factor_0_22 : (10 : ZMod 79719069217) ^ 4865665 = 63811085951 := by
        calc
          (10 : ZMod 79719069217) ^ 4865665 = (10 : ZMod 79719069217) ^ (2432832 + 2432832 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 2432832 * (10 : ZMod 79719069217) ^ 2432832) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 63811085951 := by rw [factor_0_21]; decide
      have factor_0_23 : (10 : ZMod 79719069217) ^ 9731331 = 40929005203 := by
        calc
          (10 : ZMod 79719069217) ^ 9731331 = (10 : ZMod 79719069217) ^ (4865665 + 4865665 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 4865665 * (10 : ZMod 79719069217) ^ 4865665) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 40929005203 := by rw [factor_0_22]; decide
      have factor_0_24 : (10 : ZMod 79719069217) ^ 19462663 = 38719598161 := by
        calc
          (10 : ZMod 79719069217) ^ 19462663 = (10 : ZMod 79719069217) ^ (9731331 + 9731331 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 9731331 * (10 : ZMod 79719069217) ^ 9731331) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 38719598161 := by rw [factor_0_23]; decide
      have factor_0_25 : (10 : ZMod 79719069217) ^ 38925326 = 56691358859 := by
        calc
          (10 : ZMod 79719069217) ^ 38925326 = (10 : ZMod 79719069217) ^ (19462663 + 19462663) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 19462663 * (10 : ZMod 79719069217) ^ 19462663 := by rw [pow_add]
          _ = 56691358859 := by rw [factor_0_24]; decide
      have factor_0_26 : (10 : ZMod 79719069217) ^ 77850653 = 66310853715 := by
        calc
          (10 : ZMod 79719069217) ^ 77850653 = (10 : ZMod 79719069217) ^ (38925326 + 38925326 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 38925326 * (10 : ZMod 79719069217) ^ 38925326) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 66310853715 := by rw [factor_0_25]; decide
      have factor_0_27 : (10 : ZMod 79719069217) ^ 155701307 = 21931824478 := by
        calc
          (10 : ZMod 79719069217) ^ 155701307 = (10 : ZMod 79719069217) ^ (77850653 + 77850653 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 77850653 * (10 : ZMod 79719069217) ^ 77850653) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 21931824478 := by rw [factor_0_26]; decide
      have factor_0_28 : (10 : ZMod 79719069217) ^ 311402614 = 53981044005 := by
        calc
          (10 : ZMod 79719069217) ^ 311402614 = (10 : ZMod 79719069217) ^ (155701307 + 155701307) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 155701307 * (10 : ZMod 79719069217) ^ 155701307 := by rw [pow_add]
          _ = 53981044005 := by rw [factor_0_27]; decide
      have factor_0_29 : (10 : ZMod 79719069217) ^ 622805228 = 59486095895 := by
        calc
          (10 : ZMod 79719069217) ^ 622805228 = (10 : ZMod 79719069217) ^ (311402614 + 311402614) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 311402614 * (10 : ZMod 79719069217) ^ 311402614 := by rw [pow_add]
          _ = 59486095895 := by rw [factor_0_28]; decide
      have factor_0_30 : (10 : ZMod 79719069217) ^ 1245610456 = 20057735098 := by
        calc
          (10 : ZMod 79719069217) ^ 1245610456 = (10 : ZMod 79719069217) ^ (622805228 + 622805228) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 622805228 * (10 : ZMod 79719069217) ^ 622805228 := by rw [pow_add]
          _ = 20057735098 := by rw [factor_0_29]; decide
      have factor_0_31 : (10 : ZMod 79719069217) ^ 2491220913 = 35505691636 := by
        calc
          (10 : ZMod 79719069217) ^ 2491220913 = (10 : ZMod 79719069217) ^ (1245610456 + 1245610456 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 1245610456 * (10 : ZMod 79719069217) ^ 1245610456) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 35505691636 := by rw [factor_0_30]; decide
      have factor_0_32 : (10 : ZMod 79719069217) ^ 4982441826 = 38226199379 := by
        calc
          (10 : ZMod 79719069217) ^ 4982441826 = (10 : ZMod 79719069217) ^ (2491220913 + 2491220913) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 2491220913 * (10 : ZMod 79719069217) ^ 2491220913 := by rw [pow_add]
          _ = 38226199379 := by rw [factor_0_31]; decide
      have factor_0_33 : (10 : ZMod 79719069217) ^ 9964883652 = 48676950511 := by
        calc
          (10 : ZMod 79719069217) ^ 9964883652 = (10 : ZMod 79719069217) ^ (4982441826 + 4982441826) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 4982441826 * (10 : ZMod 79719069217) ^ 4982441826 := by rw [pow_add]
          _ = 48676950511 := by rw [factor_0_32]; decide
      have factor_0_34 : (10 : ZMod 79719069217) ^ 19929767304 = 66081518220 := by
        calc
          (10 : ZMod 79719069217) ^ 19929767304 = (10 : ZMod 79719069217) ^ (9964883652 + 9964883652) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 9964883652 * (10 : ZMod 79719069217) ^ 9964883652 := by rw [pow_add]
          _ = 66081518220 := by rw [factor_0_33]; decide
      have factor_0_35 : (10 : ZMod 79719069217) ^ 39859534608 = 79719069216 := by
        calc
          (10 : ZMod 79719069217) ^ 39859534608 = (10 : ZMod 79719069217) ^ (19929767304 + 19929767304) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 19929767304 * (10 : ZMod 79719069217) ^ 19929767304 := by rw [pow_add]
          _ = 79719069216 := by rw [factor_0_34]; decide
      change (10 : ZMod 79719069217) ^ 39859534608 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (10 : ZMod 79719069217) ^ 1 = 10 := by norm_num
      have factor_1_1 : (10 : ZMod 79719069217) ^ 3 = 1000 := by
        calc
          (10 : ZMod 79719069217) ^ 3 = (10 : ZMod 79719069217) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 1 * (10 : ZMod 79719069217) ^ 1) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_1_0]; decide
      have factor_1_2 : (10 : ZMod 79719069217) ^ 6 = 1000000 := by
        calc
          (10 : ZMod 79719069217) ^ 6 = (10 : ZMod 79719069217) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 3 * (10 : ZMod 79719069217) ^ 3 := by rw [pow_add]
          _ = 1000000 := by rw [factor_1_1]; decide
      have factor_1_3 : (10 : ZMod 79719069217) ^ 12 = 43371169396 := by
        calc
          (10 : ZMod 79719069217) ^ 12 = (10 : ZMod 79719069217) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 6 * (10 : ZMod 79719069217) ^ 6 := by rw [pow_add]
          _ = 43371169396 := by rw [factor_1_2]; decide
      have factor_1_4 : (10 : ZMod 79719069217) ^ 24 = 25798052221 := by
        calc
          (10 : ZMod 79719069217) ^ 24 = (10 : ZMod 79719069217) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 12 * (10 : ZMod 79719069217) ^ 12 := by rw [pow_add]
          _ = 25798052221 := by rw [factor_1_3]; decide
      have factor_1_5 : (10 : ZMod 79719069217) ^ 49 = 73548049905 := by
        calc
          (10 : ZMod 79719069217) ^ 49 = (10 : ZMod 79719069217) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 24 * (10 : ZMod 79719069217) ^ 24) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 73548049905 := by rw [factor_1_4]; decide
      have factor_1_6 : (10 : ZMod 79719069217) ^ 98 = 56178959599 := by
        calc
          (10 : ZMod 79719069217) ^ 98 = (10 : ZMod 79719069217) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 49 * (10 : ZMod 79719069217) ^ 49 := by rw [pow_add]
          _ = 56178959599 := by rw [factor_1_5]; decide
      have factor_1_7 : (10 : ZMod 79719069217) ^ 197 = 78619378598 := by
        calc
          (10 : ZMod 79719069217) ^ 197 = (10 : ZMod 79719069217) ^ (98 + 98 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 98 * (10 : ZMod 79719069217) ^ 98) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 78619378598 := by rw [factor_1_6]; decide
      have factor_1_8 : (10 : ZMod 79719069217) ^ 395 = 71388622164 := by
        calc
          (10 : ZMod 79719069217) ^ 395 = (10 : ZMod 79719069217) ^ (197 + 197 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 197 * (10 : ZMod 79719069217) ^ 197) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 71388622164 := by rw [factor_1_7]; decide
      have factor_1_9 : (10 : ZMod 79719069217) ^ 791 = 32187853577 := by
        calc
          (10 : ZMod 79719069217) ^ 791 = (10 : ZMod 79719069217) ^ (395 + 395 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 395 * (10 : ZMod 79719069217) ^ 395) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 32187853577 := by rw [factor_1_8]; decide
      have factor_1_10 : (10 : ZMod 79719069217) ^ 1583 = 62119479233 := by
        calc
          (10 : ZMod 79719069217) ^ 1583 = (10 : ZMod 79719069217) ^ (791 + 791 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 791 * (10 : ZMod 79719069217) ^ 791) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 62119479233 := by rw [factor_1_9]; decide
      have factor_1_11 : (10 : ZMod 79719069217) ^ 3167 = 37659027659 := by
        calc
          (10 : ZMod 79719069217) ^ 3167 = (10 : ZMod 79719069217) ^ (1583 + 1583 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 1583 * (10 : ZMod 79719069217) ^ 1583) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 37659027659 := by rw [factor_1_10]; decide
      have factor_1_12 : (10 : ZMod 79719069217) ^ 6335 = 38113568840 := by
        calc
          (10 : ZMod 79719069217) ^ 6335 = (10 : ZMod 79719069217) ^ (3167 + 3167 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 3167 * (10 : ZMod 79719069217) ^ 3167) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 38113568840 := by rw [factor_1_11]; decide
      have factor_1_13 : (10 : ZMod 79719069217) ^ 12671 = 78324124071 := by
        calc
          (10 : ZMod 79719069217) ^ 12671 = (10 : ZMod 79719069217) ^ (6335 + 6335 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 6335 * (10 : ZMod 79719069217) ^ 6335) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 78324124071 := by rw [factor_1_12]; decide
      have factor_1_14 : (10 : ZMod 79719069217) ^ 25342 = 32138248361 := by
        calc
          (10 : ZMod 79719069217) ^ 25342 = (10 : ZMod 79719069217) ^ (12671 + 12671) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 12671 * (10 : ZMod 79719069217) ^ 12671 := by rw [pow_add]
          _ = 32138248361 := by rw [factor_1_13]; decide
      have factor_1_15 : (10 : ZMod 79719069217) ^ 50684 = 74077913783 := by
        calc
          (10 : ZMod 79719069217) ^ 50684 = (10 : ZMod 79719069217) ^ (25342 + 25342) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 25342 * (10 : ZMod 79719069217) ^ 25342 := by rw [pow_add]
          _ = 74077913783 := by rw [factor_1_14]; decide
      have factor_1_16 : (10 : ZMod 79719069217) ^ 101368 = 67341756465 := by
        calc
          (10 : ZMod 79719069217) ^ 101368 = (10 : ZMod 79719069217) ^ (50684 + 50684) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 50684 * (10 : ZMod 79719069217) ^ 50684 := by rw [pow_add]
          _ = 67341756465 := by rw [factor_1_15]; decide
      have factor_1_17 : (10 : ZMod 79719069217) ^ 202736 = 2937920980 := by
        calc
          (10 : ZMod 79719069217) ^ 202736 = (10 : ZMod 79719069217) ^ (101368 + 101368) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 101368 * (10 : ZMod 79719069217) ^ 101368 := by rw [pow_add]
          _ = 2937920980 := by rw [factor_1_16]; decide
      have factor_1_18 : (10 : ZMod 79719069217) ^ 405472 = 31408365797 := by
        calc
          (10 : ZMod 79719069217) ^ 405472 = (10 : ZMod 79719069217) ^ (202736 + 202736) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 202736 * (10 : ZMod 79719069217) ^ 202736 := by rw [pow_add]
          _ = 31408365797 := by rw [factor_1_17]; decide
      have factor_1_19 : (10 : ZMod 79719069217) ^ 810944 = 26042721099 := by
        calc
          (10 : ZMod 79719069217) ^ 810944 = (10 : ZMod 79719069217) ^ (405472 + 405472) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 405472 * (10 : ZMod 79719069217) ^ 405472 := by rw [pow_add]
          _ = 26042721099 := by rw [factor_1_18]; decide
      have factor_1_20 : (10 : ZMod 79719069217) ^ 1621888 = 49876941285 := by
        calc
          (10 : ZMod 79719069217) ^ 1621888 = (10 : ZMod 79719069217) ^ (810944 + 810944) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 810944 * (10 : ZMod 79719069217) ^ 810944 := by rw [pow_add]
          _ = 49876941285 := by rw [factor_1_19]; decide
      have factor_1_21 : (10 : ZMod 79719069217) ^ 3243777 = 24044692156 := by
        calc
          (10 : ZMod 79719069217) ^ 3243777 = (10 : ZMod 79719069217) ^ (1621888 + 1621888 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 1621888 * (10 : ZMod 79719069217) ^ 1621888) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 24044692156 := by rw [factor_1_20]; decide
      have factor_1_22 : (10 : ZMod 79719069217) ^ 6487554 = 2301680747 := by
        calc
          (10 : ZMod 79719069217) ^ 6487554 = (10 : ZMod 79719069217) ^ (3243777 + 3243777) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 3243777 * (10 : ZMod 79719069217) ^ 3243777 := by rw [pow_add]
          _ = 2301680747 := by rw [factor_1_21]; decide
      have factor_1_23 : (10 : ZMod 79719069217) ^ 12975108 = 8655697461 := by
        calc
          (10 : ZMod 79719069217) ^ 12975108 = (10 : ZMod 79719069217) ^ (6487554 + 6487554) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 6487554 * (10 : ZMod 79719069217) ^ 6487554 := by rw [pow_add]
          _ = 8655697461 := by rw [factor_1_22]; decide
      have factor_1_24 : (10 : ZMod 79719069217) ^ 25950217 = 75263564226 := by
        calc
          (10 : ZMod 79719069217) ^ 25950217 = (10 : ZMod 79719069217) ^ (12975108 + 12975108 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 12975108 * (10 : ZMod 79719069217) ^ 12975108) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 75263564226 := by rw [factor_1_23]; decide
      have factor_1_25 : (10 : ZMod 79719069217) ^ 51900435 = 49400351023 := by
        calc
          (10 : ZMod 79719069217) ^ 51900435 = (10 : ZMod 79719069217) ^ (25950217 + 25950217 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 25950217 * (10 : ZMod 79719069217) ^ 25950217) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 49400351023 := by rw [factor_1_24]; decide
      have factor_1_26 : (10 : ZMod 79719069217) ^ 103800871 = 1126213639 := by
        calc
          (10 : ZMod 79719069217) ^ 103800871 = (10 : ZMod 79719069217) ^ (51900435 + 51900435 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 51900435 * (10 : ZMod 79719069217) ^ 51900435) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 1126213639 := by rw [factor_1_25]; decide
      have factor_1_27 : (10 : ZMod 79719069217) ^ 207601742 = 63538964626 := by
        calc
          (10 : ZMod 79719069217) ^ 207601742 = (10 : ZMod 79719069217) ^ (103800871 + 103800871) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 103800871 * (10 : ZMod 79719069217) ^ 103800871 := by rw [pow_add]
          _ = 63538964626 := by rw [factor_1_26]; decide
      have factor_1_28 : (10 : ZMod 79719069217) ^ 415203485 = 41457296198 := by
        calc
          (10 : ZMod 79719069217) ^ 415203485 = (10 : ZMod 79719069217) ^ (207601742 + 207601742 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 207601742 * (10 : ZMod 79719069217) ^ 207601742) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 41457296198 := by rw [factor_1_27]; decide
      have factor_1_29 : (10 : ZMod 79719069217) ^ 830406971 = 54881686847 := by
        calc
          (10 : ZMod 79719069217) ^ 830406971 = (10 : ZMod 79719069217) ^ (415203485 + 415203485 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 415203485 * (10 : ZMod 79719069217) ^ 415203485) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 54881686847 := by rw [factor_1_28]; decide
      have factor_1_30 : (10 : ZMod 79719069217) ^ 1660813942 = 57131295846 := by
        calc
          (10 : ZMod 79719069217) ^ 1660813942 = (10 : ZMod 79719069217) ^ (830406971 + 830406971) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 830406971 * (10 : ZMod 79719069217) ^ 830406971 := by rw [pow_add]
          _ = 57131295846 := by rw [factor_1_29]; decide
      have factor_1_31 : (10 : ZMod 79719069217) ^ 3321627884 = 41919539499 := by
        calc
          (10 : ZMod 79719069217) ^ 3321627884 = (10 : ZMod 79719069217) ^ (1660813942 + 1660813942) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 1660813942 * (10 : ZMod 79719069217) ^ 1660813942 := by rw [pow_add]
          _ = 41919539499 := by rw [factor_1_30]; decide
      have factor_1_32 : (10 : ZMod 79719069217) ^ 6643255768 = 47805138975 := by
        calc
          (10 : ZMod 79719069217) ^ 6643255768 = (10 : ZMod 79719069217) ^ (3321627884 + 3321627884) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 3321627884 * (10 : ZMod 79719069217) ^ 3321627884 := by rw [pow_add]
          _ = 47805138975 := by rw [factor_1_31]; decide
      have factor_1_33 : (10 : ZMod 79719069217) ^ 13286511536 = 12761095615 := by
        calc
          (10 : ZMod 79719069217) ^ 13286511536 = (10 : ZMod 79719069217) ^ (6643255768 + 6643255768) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 6643255768 * (10 : ZMod 79719069217) ^ 6643255768 := by rw [pow_add]
          _ = 12761095615 := by rw [factor_1_32]; decide
      have factor_1_34 : (10 : ZMod 79719069217) ^ 26573023072 = 12761095614 := by
        calc
          (10 : ZMod 79719069217) ^ 26573023072 = (10 : ZMod 79719069217) ^ (13286511536 + 13286511536) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 13286511536 * (10 : ZMod 79719069217) ^ 13286511536 := by rw [pow_add]
          _ = 12761095614 := by rw [factor_1_33]; decide
      change (10 : ZMod 79719069217) ^ 26573023072 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (10 : ZMod 79719069217) ^ 1 = 10 := by norm_num
      have factor_2_1 : (10 : ZMod 79719069217) ^ 3 = 1000 := by
        calc
          (10 : ZMod 79719069217) ^ 3 = (10 : ZMod 79719069217) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = ((10 : ZMod 79719069217) ^ 1 * (10 : ZMod 79719069217) ^ 1) * (10 : ZMod 79719069217) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_2_0]; decide
      have factor_2_2 : (10 : ZMod 79719069217) ^ 6 = 1000000 := by
        calc
          (10 : ZMod 79719069217) ^ 6 = (10 : ZMod 79719069217) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 3 * (10 : ZMod 79719069217) ^ 3 := by rw [pow_add]
          _ = 1000000 := by rw [factor_2_1]; decide
      have factor_2_3 : (10 : ZMod 79719069217) ^ 12 = 43371169396 := by
        calc
          (10 : ZMod 79719069217) ^ 12 = (10 : ZMod 79719069217) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 6 * (10 : ZMod 79719069217) ^ 6 := by rw [pow_add]
          _ = 43371169396 := by rw [factor_2_2]; decide
      have factor_2_4 : (10 : ZMod 79719069217) ^ 24 = 25798052221 := by
        calc
          (10 : ZMod 79719069217) ^ 24 = (10 : ZMod 79719069217) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 12 * (10 : ZMod 79719069217) ^ 12 := by rw [pow_add]
          _ = 25798052221 := by rw [factor_2_3]; decide
      have factor_2_5 : (10 : ZMod 79719069217) ^ 48 = 47214339599 := by
        calc
          (10 : ZMod 79719069217) ^ 48 = (10 : ZMod 79719069217) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 24 * (10 : ZMod 79719069217) ^ 24 := by rw [pow_add]
          _ = 47214339599 := by rw [factor_2_4]; decide
      have factor_2_6 : (10 : ZMod 79719069217) ^ 96 = 42812896281 := by
        calc
          (10 : ZMod 79719069217) ^ 96 = (10 : ZMod 79719069217) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (10 : ZMod 79719069217) ^ n) (by norm_num)
          _ = (10 : ZMod 79719069217) ^ 48 * (10 : ZMod 79719069217) ^ 48 := by rw [pow_add]
          _ = 42812896281 := by rw [factor_2_5]; decide
      change (10 : ZMod 79719069217) ^ 96 ≠ 1
      rw [factor_2_6]
      decide

#print axioms prime_lucas_79719069217

end TotientTailPeriodKiller
end Erdos249257
