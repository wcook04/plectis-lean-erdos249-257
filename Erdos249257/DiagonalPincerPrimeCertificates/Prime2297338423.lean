import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime382889737

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2297338423 : Nat.Prime 2297338423 := by
  apply lucas_primality 2297338423 (5 : ZMod 2297338423)
  ·
      have fermat_0 : (5 : ZMod 2297338423) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 2297338423) ^ 2 = 25 := by
        calc
          (5 : ZMod 2297338423) ^ 2 = (5 : ZMod 2297338423) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 1 * (5 : ZMod 2297338423) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 2297338423) ^ 4 = 625 := by
        calc
          (5 : ZMod 2297338423) ^ 4 = (5 : ZMod 2297338423) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 2 * (5 : ZMod 2297338423) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 2297338423) ^ 8 = 390625 := by
        calc
          (5 : ZMod 2297338423) ^ 8 = (5 : ZMod 2297338423) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 4 * (5 : ZMod 2297338423) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 2297338423) ^ 17 = 223096689 := by
        calc
          (5 : ZMod 2297338423) ^ 17 = (5 : ZMod 2297338423) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 8 * (5 : ZMod 2297338423) ^ 8) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 223096689 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 2297338423) ^ 34 = 1649149577 := by
        calc
          (5 : ZMod 2297338423) ^ 34 = (5 : ZMod 2297338423) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 17 * (5 : ZMod 2297338423) ^ 17 := by rw [pow_add]
          _ = 1649149577 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 2297338423) ^ 68 = 1236365102 := by
        calc
          (5 : ZMod 2297338423) ^ 68 = (5 : ZMod 2297338423) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 34 * (5 : ZMod 2297338423) ^ 34 := by rw [pow_add]
          _ = 1236365102 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 2297338423) ^ 136 = 1977426219 := by
        calc
          (5 : ZMod 2297338423) ^ 136 = (5 : ZMod 2297338423) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 68 * (5 : ZMod 2297338423) ^ 68 := by rw [pow_add]
          _ = 1977426219 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 2297338423) ^ 273 = 1905003874 := by
        calc
          (5 : ZMod 2297338423) ^ 273 = (5 : ZMod 2297338423) ^ (136 + 136 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 136 * (5 : ZMod 2297338423) ^ 136) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 1905003874 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 2297338423) ^ 547 = 1053840142 := by
        calc
          (5 : ZMod 2297338423) ^ 547 = (5 : ZMod 2297338423) ^ (273 + 273 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 273 * (5 : ZMod 2297338423) ^ 273) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 1053840142 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 2297338423) ^ 1095 = 1705545232 := by
        calc
          (5 : ZMod 2297338423) ^ 1095 = (5 : ZMod 2297338423) ^ (547 + 547 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 547 * (5 : ZMod 2297338423) ^ 547) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 1705545232 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 2297338423) ^ 2190 = 669905221 := by
        calc
          (5 : ZMod 2297338423) ^ 2190 = (5 : ZMod 2297338423) ^ (1095 + 1095) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 1095 * (5 : ZMod 2297338423) ^ 1095 := by rw [pow_add]
          _ = 669905221 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 2297338423) ^ 4381 = 812925302 := by
        calc
          (5 : ZMod 2297338423) ^ 4381 = (5 : ZMod 2297338423) ^ (2190 + 2190 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 2190 * (5 : ZMod 2297338423) ^ 2190) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 812925302 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 2297338423) ^ 8763 = 1411497520 := by
        calc
          (5 : ZMod 2297338423) ^ 8763 = (5 : ZMod 2297338423) ^ (4381 + 4381 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 4381 * (5 : ZMod 2297338423) ^ 4381) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 1411497520 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 2297338423) ^ 17527 = 1406028937 := by
        calc
          (5 : ZMod 2297338423) ^ 17527 = (5 : ZMod 2297338423) ^ (8763 + 8763 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 8763 * (5 : ZMod 2297338423) ^ 8763) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 1406028937 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 2297338423) ^ 35054 = 90109515 := by
        calc
          (5 : ZMod 2297338423) ^ 35054 = (5 : ZMod 2297338423) ^ (17527 + 17527) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 17527 * (5 : ZMod 2297338423) ^ 17527 := by rw [pow_add]
          _ = 90109515 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 2297338423) ^ 70109 = 1422959550 := by
        calc
          (5 : ZMod 2297338423) ^ 70109 = (5 : ZMod 2297338423) ^ (35054 + 35054 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 35054 * (5 : ZMod 2297338423) ^ 35054) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 1422959550 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 2297338423) ^ 140218 = 1252054061 := by
        calc
          (5 : ZMod 2297338423) ^ 140218 = (5 : ZMod 2297338423) ^ (70109 + 70109) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 70109 * (5 : ZMod 2297338423) ^ 70109 := by rw [pow_add]
          _ = 1252054061 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 2297338423) ^ 280436 = 936665758 := by
        calc
          (5 : ZMod 2297338423) ^ 280436 = (5 : ZMod 2297338423) ^ (140218 + 140218) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 140218 * (5 : ZMod 2297338423) ^ 140218 := by rw [pow_add]
          _ = 936665758 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 2297338423) ^ 560873 = 459059127 := by
        calc
          (5 : ZMod 2297338423) ^ 560873 = (5 : ZMod 2297338423) ^ (280436 + 280436 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 280436 * (5 : ZMod 2297338423) ^ 280436) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 459059127 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 2297338423) ^ 1121747 = 1581650409 := by
        calc
          (5 : ZMod 2297338423) ^ 1121747 = (5 : ZMod 2297338423) ^ (560873 + 560873 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 560873 * (5 : ZMod 2297338423) ^ 560873) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 1581650409 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 2297338423) ^ 2243494 = 1117465482 := by
        calc
          (5 : ZMod 2297338423) ^ 2243494 = (5 : ZMod 2297338423) ^ (1121747 + 1121747) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 1121747 * (5 : ZMod 2297338423) ^ 1121747 := by rw [pow_add]
          _ = 1117465482 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 2297338423) ^ 4486989 = 880871621 := by
        calc
          (5 : ZMod 2297338423) ^ 4486989 = (5 : ZMod 2297338423) ^ (2243494 + 2243494 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 2243494 * (5 : ZMod 2297338423) ^ 2243494) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 880871621 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 2297338423) ^ 8973978 = 563510742 := by
        calc
          (5 : ZMod 2297338423) ^ 8973978 = (5 : ZMod 2297338423) ^ (4486989 + 4486989) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 4486989 * (5 : ZMod 2297338423) ^ 4486989 := by rw [pow_add]
          _ = 563510742 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 2297338423) ^ 17947956 = 2248512119 := by
        calc
          (5 : ZMod 2297338423) ^ 17947956 = (5 : ZMod 2297338423) ^ (8973978 + 8973978) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 8973978 * (5 : ZMod 2297338423) ^ 8973978 := by rw [pow_add]
          _ = 2248512119 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 2297338423) ^ 35895912 = 149954318 := by
        calc
          (5 : ZMod 2297338423) ^ 35895912 = (5 : ZMod 2297338423) ^ (17947956 + 17947956) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 17947956 * (5 : ZMod 2297338423) ^ 17947956 := by rw [pow_add]
          _ = 149954318 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 2297338423) ^ 71791825 = 17170573 := by
        calc
          (5 : ZMod 2297338423) ^ 71791825 = (5 : ZMod 2297338423) ^ (35895912 + 35895912 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 35895912 * (5 : ZMod 2297338423) ^ 35895912) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 17170573 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 2297338423) ^ 143583651 = 550501543 := by
        calc
          (5 : ZMod 2297338423) ^ 143583651 = (5 : ZMod 2297338423) ^ (71791825 + 71791825 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 71791825 * (5 : ZMod 2297338423) ^ 71791825) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 550501543 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 2297338423) ^ 287167302 = 395880762 := by
        calc
          (5 : ZMod 2297338423) ^ 287167302 = (5 : ZMod 2297338423) ^ (143583651 + 143583651) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 143583651 * (5 : ZMod 2297338423) ^ 143583651 := by rw [pow_add]
          _ = 395880762 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 2297338423) ^ 574334605 = 616102666 := by
        calc
          (5 : ZMod 2297338423) ^ 574334605 = (5 : ZMod 2297338423) ^ (287167302 + 287167302 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 287167302 * (5 : ZMod 2297338423) ^ 287167302) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 616102666 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 2297338423) ^ 1148669211 = 2297338422 := by
        calc
          (5 : ZMod 2297338423) ^ 1148669211 = (5 : ZMod 2297338423) ^ (574334605 + 574334605 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 574334605 * (5 : ZMod 2297338423) ^ 574334605) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 2297338422 := by rw [fermat_29]; decide
      have fermat_31 : (5 : ZMod 2297338423) ^ 2297338422 = 1 := by
        calc
          (5 : ZMod 2297338423) ^ 2297338422 = (5 : ZMod 2297338423) ^ (1148669211 + 1148669211) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 1148669211 * (5 : ZMod 2297338423) ^ 1148669211 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (382889737, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (382889737, 1)] : List FactorBlock).map factorBlockValue).prod = 2297338423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_382889737) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 2297338423) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 2297338423) ^ 2 = 25 := by
        calc
          (5 : ZMod 2297338423) ^ 2 = (5 : ZMod 2297338423) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 1 * (5 : ZMod 2297338423) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 2297338423) ^ 4 = 625 := by
        calc
          (5 : ZMod 2297338423) ^ 4 = (5 : ZMod 2297338423) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 2 * (5 : ZMod 2297338423) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 2297338423) ^ 8 = 390625 := by
        calc
          (5 : ZMod 2297338423) ^ 8 = (5 : ZMod 2297338423) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 4 * (5 : ZMod 2297338423) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 2297338423) ^ 17 = 223096689 := by
        calc
          (5 : ZMod 2297338423) ^ 17 = (5 : ZMod 2297338423) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 8 * (5 : ZMod 2297338423) ^ 8) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 223096689 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 2297338423) ^ 34 = 1649149577 := by
        calc
          (5 : ZMod 2297338423) ^ 34 = (5 : ZMod 2297338423) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 17 * (5 : ZMod 2297338423) ^ 17 := by rw [pow_add]
          _ = 1649149577 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 2297338423) ^ 68 = 1236365102 := by
        calc
          (5 : ZMod 2297338423) ^ 68 = (5 : ZMod 2297338423) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 34 * (5 : ZMod 2297338423) ^ 34 := by rw [pow_add]
          _ = 1236365102 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 2297338423) ^ 136 = 1977426219 := by
        calc
          (5 : ZMod 2297338423) ^ 136 = (5 : ZMod 2297338423) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 68 * (5 : ZMod 2297338423) ^ 68 := by rw [pow_add]
          _ = 1977426219 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 2297338423) ^ 273 = 1905003874 := by
        calc
          (5 : ZMod 2297338423) ^ 273 = (5 : ZMod 2297338423) ^ (136 + 136 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 136 * (5 : ZMod 2297338423) ^ 136) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 1905003874 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 2297338423) ^ 547 = 1053840142 := by
        calc
          (5 : ZMod 2297338423) ^ 547 = (5 : ZMod 2297338423) ^ (273 + 273 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 273 * (5 : ZMod 2297338423) ^ 273) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 1053840142 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 2297338423) ^ 1095 = 1705545232 := by
        calc
          (5 : ZMod 2297338423) ^ 1095 = (5 : ZMod 2297338423) ^ (547 + 547 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 547 * (5 : ZMod 2297338423) ^ 547) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 1705545232 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 2297338423) ^ 2190 = 669905221 := by
        calc
          (5 : ZMod 2297338423) ^ 2190 = (5 : ZMod 2297338423) ^ (1095 + 1095) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 1095 * (5 : ZMod 2297338423) ^ 1095 := by rw [pow_add]
          _ = 669905221 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 2297338423) ^ 4381 = 812925302 := by
        calc
          (5 : ZMod 2297338423) ^ 4381 = (5 : ZMod 2297338423) ^ (2190 + 2190 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 2190 * (5 : ZMod 2297338423) ^ 2190) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 812925302 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 2297338423) ^ 8763 = 1411497520 := by
        calc
          (5 : ZMod 2297338423) ^ 8763 = (5 : ZMod 2297338423) ^ (4381 + 4381 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 4381 * (5 : ZMod 2297338423) ^ 4381) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 1411497520 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 2297338423) ^ 17527 = 1406028937 := by
        calc
          (5 : ZMod 2297338423) ^ 17527 = (5 : ZMod 2297338423) ^ (8763 + 8763 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 8763 * (5 : ZMod 2297338423) ^ 8763) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 1406028937 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 2297338423) ^ 35054 = 90109515 := by
        calc
          (5 : ZMod 2297338423) ^ 35054 = (5 : ZMod 2297338423) ^ (17527 + 17527) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 17527 * (5 : ZMod 2297338423) ^ 17527 := by rw [pow_add]
          _ = 90109515 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 2297338423) ^ 70109 = 1422959550 := by
        calc
          (5 : ZMod 2297338423) ^ 70109 = (5 : ZMod 2297338423) ^ (35054 + 35054 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 35054 * (5 : ZMod 2297338423) ^ 35054) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 1422959550 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 2297338423) ^ 140218 = 1252054061 := by
        calc
          (5 : ZMod 2297338423) ^ 140218 = (5 : ZMod 2297338423) ^ (70109 + 70109) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 70109 * (5 : ZMod 2297338423) ^ 70109 := by rw [pow_add]
          _ = 1252054061 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 2297338423) ^ 280436 = 936665758 := by
        calc
          (5 : ZMod 2297338423) ^ 280436 = (5 : ZMod 2297338423) ^ (140218 + 140218) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 140218 * (5 : ZMod 2297338423) ^ 140218 := by rw [pow_add]
          _ = 936665758 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 2297338423) ^ 560873 = 459059127 := by
        calc
          (5 : ZMod 2297338423) ^ 560873 = (5 : ZMod 2297338423) ^ (280436 + 280436 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 280436 * (5 : ZMod 2297338423) ^ 280436) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 459059127 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 2297338423) ^ 1121747 = 1581650409 := by
        calc
          (5 : ZMod 2297338423) ^ 1121747 = (5 : ZMod 2297338423) ^ (560873 + 560873 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 560873 * (5 : ZMod 2297338423) ^ 560873) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 1581650409 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 2297338423) ^ 2243494 = 1117465482 := by
        calc
          (5 : ZMod 2297338423) ^ 2243494 = (5 : ZMod 2297338423) ^ (1121747 + 1121747) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 1121747 * (5 : ZMod 2297338423) ^ 1121747 := by rw [pow_add]
          _ = 1117465482 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 2297338423) ^ 4486989 = 880871621 := by
        calc
          (5 : ZMod 2297338423) ^ 4486989 = (5 : ZMod 2297338423) ^ (2243494 + 2243494 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 2243494 * (5 : ZMod 2297338423) ^ 2243494) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 880871621 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 2297338423) ^ 8973978 = 563510742 := by
        calc
          (5 : ZMod 2297338423) ^ 8973978 = (5 : ZMod 2297338423) ^ (4486989 + 4486989) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 4486989 * (5 : ZMod 2297338423) ^ 4486989 := by rw [pow_add]
          _ = 563510742 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 2297338423) ^ 17947956 = 2248512119 := by
        calc
          (5 : ZMod 2297338423) ^ 17947956 = (5 : ZMod 2297338423) ^ (8973978 + 8973978) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 8973978 * (5 : ZMod 2297338423) ^ 8973978 := by rw [pow_add]
          _ = 2248512119 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 2297338423) ^ 35895912 = 149954318 := by
        calc
          (5 : ZMod 2297338423) ^ 35895912 = (5 : ZMod 2297338423) ^ (17947956 + 17947956) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 17947956 * (5 : ZMod 2297338423) ^ 17947956 := by rw [pow_add]
          _ = 149954318 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 2297338423) ^ 71791825 = 17170573 := by
        calc
          (5 : ZMod 2297338423) ^ 71791825 = (5 : ZMod 2297338423) ^ (35895912 + 35895912 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 35895912 * (5 : ZMod 2297338423) ^ 35895912) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 17170573 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 2297338423) ^ 143583651 = 550501543 := by
        calc
          (5 : ZMod 2297338423) ^ 143583651 = (5 : ZMod 2297338423) ^ (71791825 + 71791825 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 71791825 * (5 : ZMod 2297338423) ^ 71791825) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 550501543 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 2297338423) ^ 287167302 = 395880762 := by
        calc
          (5 : ZMod 2297338423) ^ 287167302 = (5 : ZMod 2297338423) ^ (143583651 + 143583651) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 143583651 * (5 : ZMod 2297338423) ^ 143583651 := by rw [pow_add]
          _ = 395880762 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 2297338423) ^ 574334605 = 616102666 := by
        calc
          (5 : ZMod 2297338423) ^ 574334605 = (5 : ZMod 2297338423) ^ (287167302 + 287167302 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 287167302 * (5 : ZMod 2297338423) ^ 287167302) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 616102666 := by rw [factor_0_28]; decide
      have factor_0_30 : (5 : ZMod 2297338423) ^ 1148669211 = 2297338422 := by
        calc
          (5 : ZMod 2297338423) ^ 1148669211 = (5 : ZMod 2297338423) ^ (574334605 + 574334605 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 574334605 * (5 : ZMod 2297338423) ^ 574334605) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 2297338422 := by rw [factor_0_29]; decide
      change (5 : ZMod 2297338423) ^ 1148669211 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (5 : ZMod 2297338423) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 2297338423) ^ 2 = 25 := by
        calc
          (5 : ZMod 2297338423) ^ 2 = (5 : ZMod 2297338423) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 1 * (5 : ZMod 2297338423) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 2297338423) ^ 5 = 3125 := by
        calc
          (5 : ZMod 2297338423) ^ 5 = (5 : ZMod 2297338423) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 2 * (5 : ZMod 2297338423) ^ 2) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 2297338423) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 2297338423) ^ 11 = (5 : ZMod 2297338423) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 5 * (5 : ZMod 2297338423) ^ 5) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 2297338423) ^ 22 = 1083610956 := by
        calc
          (5 : ZMod 2297338423) ^ 22 = (5 : ZMod 2297338423) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 11 * (5 : ZMod 2297338423) ^ 11 := by rw [pow_add]
          _ = 1083610956 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 2297338423) ^ 45 = 1933617808 := by
        calc
          (5 : ZMod 2297338423) ^ 45 = (5 : ZMod 2297338423) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 22 * (5 : ZMod 2297338423) ^ 22) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 1933617808 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 2297338423) ^ 91 = 559269470 := by
        calc
          (5 : ZMod 2297338423) ^ 91 = (5 : ZMod 2297338423) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 45 * (5 : ZMod 2297338423) ^ 45) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 559269470 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 2297338423) ^ 182 = 949933775 := by
        calc
          (5 : ZMod 2297338423) ^ 182 = (5 : ZMod 2297338423) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 91 * (5 : ZMod 2297338423) ^ 91 := by rw [pow_add]
          _ = 949933775 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 2297338423) ^ 365 = 640907294 := by
        calc
          (5 : ZMod 2297338423) ^ 365 = (5 : ZMod 2297338423) ^ (182 + 182 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 182 * (5 : ZMod 2297338423) ^ 182) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 640907294 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 2297338423) ^ 730 = 2207661986 := by
        calc
          (5 : ZMod 2297338423) ^ 730 = (5 : ZMod 2297338423) ^ (365 + 365) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 365 * (5 : ZMod 2297338423) ^ 365 := by rw [pow_add]
          _ = 2207661986 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 2297338423) ^ 1460 = 337903970 := by
        calc
          (5 : ZMod 2297338423) ^ 1460 = (5 : ZMod 2297338423) ^ (730 + 730) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 730 * (5 : ZMod 2297338423) ^ 730 := by rw [pow_add]
          _ = 337903970 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 2297338423) ^ 2921 = 2146096576 := by
        calc
          (5 : ZMod 2297338423) ^ 2921 = (5 : ZMod 2297338423) ^ (1460 + 1460 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 1460 * (5 : ZMod 2297338423) ^ 1460) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 2146096576 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 2297338423) ^ 5842 = 723275046 := by
        calc
          (5 : ZMod 2297338423) ^ 5842 = (5 : ZMod 2297338423) ^ (2921 + 2921) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 2921 * (5 : ZMod 2297338423) ^ 2921 := by rw [pow_add]
          _ = 723275046 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 2297338423) ^ 11684 = 2615919 := by
        calc
          (5 : ZMod 2297338423) ^ 11684 = (5 : ZMod 2297338423) ^ (5842 + 5842) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 5842 * (5 : ZMod 2297338423) ^ 5842 := by rw [pow_add]
          _ = 2615919 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 2297338423) ^ 23369 = 899939066 := by
        calc
          (5 : ZMod 2297338423) ^ 23369 = (5 : ZMod 2297338423) ^ (11684 + 11684 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 11684 * (5 : ZMod 2297338423) ^ 11684) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 899939066 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 2297338423) ^ 46739 = 1620048427 := by
        calc
          (5 : ZMod 2297338423) ^ 46739 = (5 : ZMod 2297338423) ^ (23369 + 23369 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 23369 * (5 : ZMod 2297338423) ^ 23369) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 1620048427 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 2297338423) ^ 93478 = 2164966539 := by
        calc
          (5 : ZMod 2297338423) ^ 93478 = (5 : ZMod 2297338423) ^ (46739 + 46739) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 46739 * (5 : ZMod 2297338423) ^ 46739 := by rw [pow_add]
          _ = 2164966539 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 2297338423) ^ 186957 = 2291070097 := by
        calc
          (5 : ZMod 2297338423) ^ 186957 = (5 : ZMod 2297338423) ^ (93478 + 93478 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 93478 * (5 : ZMod 2297338423) ^ 93478) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 2291070097 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 2297338423) ^ 373915 = 361630112 := by
        calc
          (5 : ZMod 2297338423) ^ 373915 = (5 : ZMod 2297338423) ^ (186957 + 186957 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 186957 * (5 : ZMod 2297338423) ^ 186957) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 361630112 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 2297338423) ^ 747831 = 1794101509 := by
        calc
          (5 : ZMod 2297338423) ^ 747831 = (5 : ZMod 2297338423) ^ (373915 + 373915 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 373915 * (5 : ZMod 2297338423) ^ 373915) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 1794101509 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 2297338423) ^ 1495663 = 846308644 := by
        calc
          (5 : ZMod 2297338423) ^ 1495663 = (5 : ZMod 2297338423) ^ (747831 + 747831 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 747831 * (5 : ZMod 2297338423) ^ 747831) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 846308644 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 2297338423) ^ 2991326 = 1632791178 := by
        calc
          (5 : ZMod 2297338423) ^ 2991326 = (5 : ZMod 2297338423) ^ (1495663 + 1495663) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 1495663 * (5 : ZMod 2297338423) ^ 1495663 := by rw [pow_add]
          _ = 1632791178 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 2297338423) ^ 5982652 = 1357895215 := by
        calc
          (5 : ZMod 2297338423) ^ 5982652 = (5 : ZMod 2297338423) ^ (2991326 + 2991326) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 2991326 * (5 : ZMod 2297338423) ^ 2991326 := by rw [pow_add]
          _ = 1357895215 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 2297338423) ^ 11965304 = 1658570263 := by
        calc
          (5 : ZMod 2297338423) ^ 11965304 = (5 : ZMod 2297338423) ^ (5982652 + 5982652) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 5982652 * (5 : ZMod 2297338423) ^ 5982652 := by rw [pow_add]
          _ = 1658570263 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 2297338423) ^ 23930608 = 830309223 := by
        calc
          (5 : ZMod 2297338423) ^ 23930608 = (5 : ZMod 2297338423) ^ (11965304 + 11965304) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 11965304 * (5 : ZMod 2297338423) ^ 11965304 := by rw [pow_add]
          _ = 830309223 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 2297338423) ^ 47861217 = 2151274848 := by
        calc
          (5 : ZMod 2297338423) ^ 47861217 = (5 : ZMod 2297338423) ^ (23930608 + 23930608 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 23930608 * (5 : ZMod 2297338423) ^ 23930608) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 2151274848 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 2297338423) ^ 95722434 = 1562519790 := by
        calc
          (5 : ZMod 2297338423) ^ 95722434 = (5 : ZMod 2297338423) ^ (47861217 + 47861217) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 47861217 * (5 : ZMod 2297338423) ^ 47861217 := by rw [pow_add]
          _ = 1562519790 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 2297338423) ^ 191444868 = 2091795998 := by
        calc
          (5 : ZMod 2297338423) ^ 191444868 = (5 : ZMod 2297338423) ^ (95722434 + 95722434) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 95722434 * (5 : ZMod 2297338423) ^ 95722434 := by rw [pow_add]
          _ = 2091795998 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 2297338423) ^ 382889737 = 763599410 := by
        calc
          (5 : ZMod 2297338423) ^ 382889737 = (5 : ZMod 2297338423) ^ (191444868 + 191444868 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 191444868 * (5 : ZMod 2297338423) ^ 191444868) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 763599410 := by rw [factor_1_27]; decide
      have factor_1_29 : (5 : ZMod 2297338423) ^ 765779474 = 763599409 := by
        calc
          (5 : ZMod 2297338423) ^ 765779474 = (5 : ZMod 2297338423) ^ (382889737 + 382889737) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 382889737 * (5 : ZMod 2297338423) ^ 382889737 := by rw [pow_add]
          _ = 763599409 := by rw [factor_1_28]; decide
      change (5 : ZMod 2297338423) ^ 765779474 ≠ 1
      rw [factor_1_29]
      decide
    ·
      have factor_2_0 : (5 : ZMod 2297338423) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 2297338423) ^ 3 = 125 := by
        calc
          (5 : ZMod 2297338423) ^ 3 = (5 : ZMod 2297338423) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = ((5 : ZMod 2297338423) ^ 1 * (5 : ZMod 2297338423) ^ 1) * (5 : ZMod 2297338423) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 2297338423) ^ 6 = 15625 := by
        calc
          (5 : ZMod 2297338423) ^ 6 = (5 : ZMod 2297338423) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 2297338423) ^ n) (by norm_num)
          _ = (5 : ZMod 2297338423) ^ 3 * (5 : ZMod 2297338423) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_2_1]; decide
      change (5 : ZMod 2297338423) ^ 6 ≠ 1
      rw [factor_2_2]
      decide

#print axioms prime_lucas_2297338423

end TotientTailPeriodKiller
end Erdos249257
