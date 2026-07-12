import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime95942699

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2302624777 : Nat.Prime 2302624777 := by
  apply lucas_primality 2302624777 (7 : ZMod 2302624777)
  ·
      have fermat_0 : (7 : ZMod 2302624777) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 2302624777) ^ 2 = 49 := by
        calc
          (7 : ZMod 2302624777) ^ 2 = (7 : ZMod 2302624777) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 1 * (7 : ZMod 2302624777) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 2302624777) ^ 4 = 2401 := by
        calc
          (7 : ZMod 2302624777) ^ 4 = (7 : ZMod 2302624777) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 2 * (7 : ZMod 2302624777) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 2302624777) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 2302624777) ^ 8 = (7 : ZMod 2302624777) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 4 * (7 : ZMod 2302624777) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 2302624777) ^ 17 = 938016451 := by
        calc
          (7 : ZMod 2302624777) ^ 17 = (7 : ZMod 2302624777) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 8 * (7 : ZMod 2302624777) ^ 8) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 938016451 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 2302624777) ^ 34 = 1955121454 := by
        calc
          (7 : ZMod 2302624777) ^ 34 = (7 : ZMod 2302624777) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 17 * (7 : ZMod 2302624777) ^ 17 := by rw [pow_add]
          _ = 1955121454 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 2302624777) ^ 68 = 427025785 := by
        calc
          (7 : ZMod 2302624777) ^ 68 = (7 : ZMod 2302624777) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 34 * (7 : ZMod 2302624777) ^ 34 := by rw [pow_add]
          _ = 427025785 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 2302624777) ^ 137 = 1258707818 := by
        calc
          (7 : ZMod 2302624777) ^ 137 = (7 : ZMod 2302624777) ^ (68 + 68 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 68 * (7 : ZMod 2302624777) ^ 68) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1258707818 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 2302624777) ^ 274 = 1575208363 := by
        calc
          (7 : ZMod 2302624777) ^ 274 = (7 : ZMod 2302624777) ^ (137 + 137) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 137 * (7 : ZMod 2302624777) ^ 137 := by rw [pow_add]
          _ = 1575208363 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 2302624777) ^ 548 = 1432067735 := by
        calc
          (7 : ZMod 2302624777) ^ 548 = (7 : ZMod 2302624777) ^ (274 + 274) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 274 * (7 : ZMod 2302624777) ^ 274 := by rw [pow_add]
          _ = 1432067735 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 2302624777) ^ 1097 = 1027230342 := by
        calc
          (7 : ZMod 2302624777) ^ 1097 = (7 : ZMod 2302624777) ^ (548 + 548 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 548 * (7 : ZMod 2302624777) ^ 548) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1027230342 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 2302624777) ^ 2195 = 1089205595 := by
        calc
          (7 : ZMod 2302624777) ^ 2195 = (7 : ZMod 2302624777) ^ (1097 + 1097 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 1097 * (7 : ZMod 2302624777) ^ 1097) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1089205595 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 2302624777) ^ 4391 = 1006784868 := by
        calc
          (7 : ZMod 2302624777) ^ 4391 = (7 : ZMod 2302624777) ^ (2195 + 2195 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 2195 * (7 : ZMod 2302624777) ^ 2195) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1006784868 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 2302624777) ^ 8783 = 1248374780 := by
        calc
          (7 : ZMod 2302624777) ^ 8783 = (7 : ZMod 2302624777) ^ (4391 + 4391 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 4391 * (7 : ZMod 2302624777) ^ 4391) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1248374780 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 2302624777) ^ 17567 = 1606827296 := by
        calc
          (7 : ZMod 2302624777) ^ 17567 = (7 : ZMod 2302624777) ^ (8783 + 8783 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 8783 * (7 : ZMod 2302624777) ^ 8783) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1606827296 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 2302624777) ^ 35135 = 1562299395 := by
        calc
          (7 : ZMod 2302624777) ^ 35135 = (7 : ZMod 2302624777) ^ (17567 + 17567 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 17567 * (7 : ZMod 2302624777) ^ 17567) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1562299395 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 2302624777) ^ 70270 = 462588613 := by
        calc
          (7 : ZMod 2302624777) ^ 70270 = (7 : ZMod 2302624777) ^ (35135 + 35135) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 35135 * (7 : ZMod 2302624777) ^ 35135 := by rw [pow_add]
          _ = 462588613 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 2302624777) ^ 140541 = 630047258 := by
        calc
          (7 : ZMod 2302624777) ^ 140541 = (7 : ZMod 2302624777) ^ (70270 + 70270 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 70270 * (7 : ZMod 2302624777) ^ 70270) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 630047258 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 2302624777) ^ 281082 = 1838637851 := by
        calc
          (7 : ZMod 2302624777) ^ 281082 = (7 : ZMod 2302624777) ^ (140541 + 140541) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 140541 * (7 : ZMod 2302624777) ^ 140541 := by rw [pow_add]
          _ = 1838637851 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 2302624777) ^ 562164 = 815310908 := by
        calc
          (7 : ZMod 2302624777) ^ 562164 = (7 : ZMod 2302624777) ^ (281082 + 281082) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 281082 * (7 : ZMod 2302624777) ^ 281082 := by rw [pow_add]
          _ = 815310908 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 2302624777) ^ 1124328 = 1504157894 := by
        calc
          (7 : ZMod 2302624777) ^ 1124328 = (7 : ZMod 2302624777) ^ (562164 + 562164) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 562164 * (7 : ZMod 2302624777) ^ 562164 := by rw [pow_add]
          _ = 1504157894 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 2302624777) ^ 2248657 = 1296765770 := by
        calc
          (7 : ZMod 2302624777) ^ 2248657 = (7 : ZMod 2302624777) ^ (1124328 + 1124328 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 1124328 * (7 : ZMod 2302624777) ^ 1124328) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1296765770 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 2302624777) ^ 4497314 = 1071443627 := by
        calc
          (7 : ZMod 2302624777) ^ 4497314 = (7 : ZMod 2302624777) ^ (2248657 + 2248657) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 2248657 * (7 : ZMod 2302624777) ^ 2248657 := by rw [pow_add]
          _ = 1071443627 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 2302624777) ^ 8994628 = 1805169940 := by
        calc
          (7 : ZMod 2302624777) ^ 8994628 = (7 : ZMod 2302624777) ^ (4497314 + 4497314) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 4497314 * (7 : ZMod 2302624777) ^ 4497314 := by rw [pow_add]
          _ = 1805169940 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 2302624777) ^ 17989256 = 788960082 := by
        calc
          (7 : ZMod 2302624777) ^ 17989256 = (7 : ZMod 2302624777) ^ (8994628 + 8994628) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 8994628 * (7 : ZMod 2302624777) ^ 8994628 := by rw [pow_add]
          _ = 788960082 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 2302624777) ^ 35978512 = 1044515384 := by
        calc
          (7 : ZMod 2302624777) ^ 35978512 = (7 : ZMod 2302624777) ^ (17989256 + 17989256) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 17989256 * (7 : ZMod 2302624777) ^ 17989256 := by rw [pow_add]
          _ = 1044515384 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 2302624777) ^ 71957024 = 1378728395 := by
        calc
          (7 : ZMod 2302624777) ^ 71957024 = (7 : ZMod 2302624777) ^ (35978512 + 35978512) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 35978512 * (7 : ZMod 2302624777) ^ 35978512 := by rw [pow_add]
          _ = 1378728395 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 2302624777) ^ 143914048 = 106437104 := by
        calc
          (7 : ZMod 2302624777) ^ 143914048 = (7 : ZMod 2302624777) ^ (71957024 + 71957024) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 71957024 * (7 : ZMod 2302624777) ^ 71957024 := by rw [pow_add]
          _ = 106437104 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 2302624777) ^ 287828097 = 789554133 := by
        calc
          (7 : ZMod 2302624777) ^ 287828097 = (7 : ZMod 2302624777) ^ (143914048 + 143914048 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 143914048 * (7 : ZMod 2302624777) ^ 143914048) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 789554133 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 2302624777) ^ 575656194 = 380889646 := by
        calc
          (7 : ZMod 2302624777) ^ 575656194 = (7 : ZMod 2302624777) ^ (287828097 + 287828097) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 287828097 * (7 : ZMod 2302624777) ^ 287828097 := by rw [pow_add]
          _ = 380889646 := by rw [fermat_28]; decide
      have fermat_30 : (7 : ZMod 2302624777) ^ 1151312388 = 2302624776 := by
        calc
          (7 : ZMod 2302624777) ^ 1151312388 = (7 : ZMod 2302624777) ^ (575656194 + 575656194) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 575656194 * (7 : ZMod 2302624777) ^ 575656194 := by rw [pow_add]
          _ = 2302624776 := by rw [fermat_29]; decide
      have fermat_31 : (7 : ZMod 2302624777) ^ 2302624776 = 1 := by
        calc
          (7 : ZMod 2302624777) ^ 2302624776 = (7 : ZMod 2302624777) ^ (1151312388 + 1151312388) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 1151312388 * (7 : ZMod 2302624777) ^ 1151312388 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (95942699, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (95942699, 1)] : List FactorBlock).map factorBlockValue).prod = 2302624777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_95942699) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 2302624777) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 2302624777) ^ 2 = 49 := by
        calc
          (7 : ZMod 2302624777) ^ 2 = (7 : ZMod 2302624777) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 1 * (7 : ZMod 2302624777) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 2302624777) ^ 4 = 2401 := by
        calc
          (7 : ZMod 2302624777) ^ 4 = (7 : ZMod 2302624777) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 2 * (7 : ZMod 2302624777) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 2302624777) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 2302624777) ^ 8 = (7 : ZMod 2302624777) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 4 * (7 : ZMod 2302624777) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 2302624777) ^ 17 = 938016451 := by
        calc
          (7 : ZMod 2302624777) ^ 17 = (7 : ZMod 2302624777) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 8 * (7 : ZMod 2302624777) ^ 8) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 938016451 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 2302624777) ^ 34 = 1955121454 := by
        calc
          (7 : ZMod 2302624777) ^ 34 = (7 : ZMod 2302624777) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 17 * (7 : ZMod 2302624777) ^ 17 := by rw [pow_add]
          _ = 1955121454 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 2302624777) ^ 68 = 427025785 := by
        calc
          (7 : ZMod 2302624777) ^ 68 = (7 : ZMod 2302624777) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 34 * (7 : ZMod 2302624777) ^ 34 := by rw [pow_add]
          _ = 427025785 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 2302624777) ^ 137 = 1258707818 := by
        calc
          (7 : ZMod 2302624777) ^ 137 = (7 : ZMod 2302624777) ^ (68 + 68 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 68 * (7 : ZMod 2302624777) ^ 68) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1258707818 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 2302624777) ^ 274 = 1575208363 := by
        calc
          (7 : ZMod 2302624777) ^ 274 = (7 : ZMod 2302624777) ^ (137 + 137) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 137 * (7 : ZMod 2302624777) ^ 137 := by rw [pow_add]
          _ = 1575208363 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 2302624777) ^ 548 = 1432067735 := by
        calc
          (7 : ZMod 2302624777) ^ 548 = (7 : ZMod 2302624777) ^ (274 + 274) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 274 * (7 : ZMod 2302624777) ^ 274 := by rw [pow_add]
          _ = 1432067735 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 2302624777) ^ 1097 = 1027230342 := by
        calc
          (7 : ZMod 2302624777) ^ 1097 = (7 : ZMod 2302624777) ^ (548 + 548 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 548 * (7 : ZMod 2302624777) ^ 548) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1027230342 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 2302624777) ^ 2195 = 1089205595 := by
        calc
          (7 : ZMod 2302624777) ^ 2195 = (7 : ZMod 2302624777) ^ (1097 + 1097 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 1097 * (7 : ZMod 2302624777) ^ 1097) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1089205595 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 2302624777) ^ 4391 = 1006784868 := by
        calc
          (7 : ZMod 2302624777) ^ 4391 = (7 : ZMod 2302624777) ^ (2195 + 2195 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 2195 * (7 : ZMod 2302624777) ^ 2195) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1006784868 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 2302624777) ^ 8783 = 1248374780 := by
        calc
          (7 : ZMod 2302624777) ^ 8783 = (7 : ZMod 2302624777) ^ (4391 + 4391 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 4391 * (7 : ZMod 2302624777) ^ 4391) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1248374780 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 2302624777) ^ 17567 = 1606827296 := by
        calc
          (7 : ZMod 2302624777) ^ 17567 = (7 : ZMod 2302624777) ^ (8783 + 8783 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 8783 * (7 : ZMod 2302624777) ^ 8783) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1606827296 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 2302624777) ^ 35135 = 1562299395 := by
        calc
          (7 : ZMod 2302624777) ^ 35135 = (7 : ZMod 2302624777) ^ (17567 + 17567 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 17567 * (7 : ZMod 2302624777) ^ 17567) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1562299395 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 2302624777) ^ 70270 = 462588613 := by
        calc
          (7 : ZMod 2302624777) ^ 70270 = (7 : ZMod 2302624777) ^ (35135 + 35135) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 35135 * (7 : ZMod 2302624777) ^ 35135 := by rw [pow_add]
          _ = 462588613 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 2302624777) ^ 140541 = 630047258 := by
        calc
          (7 : ZMod 2302624777) ^ 140541 = (7 : ZMod 2302624777) ^ (70270 + 70270 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 70270 * (7 : ZMod 2302624777) ^ 70270) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 630047258 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 2302624777) ^ 281082 = 1838637851 := by
        calc
          (7 : ZMod 2302624777) ^ 281082 = (7 : ZMod 2302624777) ^ (140541 + 140541) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 140541 * (7 : ZMod 2302624777) ^ 140541 := by rw [pow_add]
          _ = 1838637851 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 2302624777) ^ 562164 = 815310908 := by
        calc
          (7 : ZMod 2302624777) ^ 562164 = (7 : ZMod 2302624777) ^ (281082 + 281082) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 281082 * (7 : ZMod 2302624777) ^ 281082 := by rw [pow_add]
          _ = 815310908 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 2302624777) ^ 1124328 = 1504157894 := by
        calc
          (7 : ZMod 2302624777) ^ 1124328 = (7 : ZMod 2302624777) ^ (562164 + 562164) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 562164 * (7 : ZMod 2302624777) ^ 562164 := by rw [pow_add]
          _ = 1504157894 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 2302624777) ^ 2248657 = 1296765770 := by
        calc
          (7 : ZMod 2302624777) ^ 2248657 = (7 : ZMod 2302624777) ^ (1124328 + 1124328 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 1124328 * (7 : ZMod 2302624777) ^ 1124328) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1296765770 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 2302624777) ^ 4497314 = 1071443627 := by
        calc
          (7 : ZMod 2302624777) ^ 4497314 = (7 : ZMod 2302624777) ^ (2248657 + 2248657) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 2248657 * (7 : ZMod 2302624777) ^ 2248657 := by rw [pow_add]
          _ = 1071443627 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 2302624777) ^ 8994628 = 1805169940 := by
        calc
          (7 : ZMod 2302624777) ^ 8994628 = (7 : ZMod 2302624777) ^ (4497314 + 4497314) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 4497314 * (7 : ZMod 2302624777) ^ 4497314 := by rw [pow_add]
          _ = 1805169940 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 2302624777) ^ 17989256 = 788960082 := by
        calc
          (7 : ZMod 2302624777) ^ 17989256 = (7 : ZMod 2302624777) ^ (8994628 + 8994628) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 8994628 * (7 : ZMod 2302624777) ^ 8994628 := by rw [pow_add]
          _ = 788960082 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 2302624777) ^ 35978512 = 1044515384 := by
        calc
          (7 : ZMod 2302624777) ^ 35978512 = (7 : ZMod 2302624777) ^ (17989256 + 17989256) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 17989256 * (7 : ZMod 2302624777) ^ 17989256 := by rw [pow_add]
          _ = 1044515384 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 2302624777) ^ 71957024 = 1378728395 := by
        calc
          (7 : ZMod 2302624777) ^ 71957024 = (7 : ZMod 2302624777) ^ (35978512 + 35978512) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 35978512 * (7 : ZMod 2302624777) ^ 35978512 := by rw [pow_add]
          _ = 1378728395 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 2302624777) ^ 143914048 = 106437104 := by
        calc
          (7 : ZMod 2302624777) ^ 143914048 = (7 : ZMod 2302624777) ^ (71957024 + 71957024) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 71957024 * (7 : ZMod 2302624777) ^ 71957024 := by rw [pow_add]
          _ = 106437104 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 2302624777) ^ 287828097 = 789554133 := by
        calc
          (7 : ZMod 2302624777) ^ 287828097 = (7 : ZMod 2302624777) ^ (143914048 + 143914048 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 143914048 * (7 : ZMod 2302624777) ^ 143914048) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 789554133 := by rw [factor_0_27]; decide
      have factor_0_29 : (7 : ZMod 2302624777) ^ 575656194 = 380889646 := by
        calc
          (7 : ZMod 2302624777) ^ 575656194 = (7 : ZMod 2302624777) ^ (287828097 + 287828097) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 287828097 * (7 : ZMod 2302624777) ^ 287828097 := by rw [pow_add]
          _ = 380889646 := by rw [factor_0_28]; decide
      have factor_0_30 : (7 : ZMod 2302624777) ^ 1151312388 = 2302624776 := by
        calc
          (7 : ZMod 2302624777) ^ 1151312388 = (7 : ZMod 2302624777) ^ (575656194 + 575656194) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 575656194 * (7 : ZMod 2302624777) ^ 575656194 := by rw [pow_add]
          _ = 2302624776 := by rw [factor_0_29]; decide
      change (7 : ZMod 2302624777) ^ 1151312388 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (7 : ZMod 2302624777) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 2302624777) ^ 2 = 49 := by
        calc
          (7 : ZMod 2302624777) ^ 2 = (7 : ZMod 2302624777) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 1 * (7 : ZMod 2302624777) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 2302624777) ^ 5 = 16807 := by
        calc
          (7 : ZMod 2302624777) ^ 5 = (7 : ZMod 2302624777) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 2 * (7 : ZMod 2302624777) ^ 2) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 2302624777) ^ 11 = 1977326743 := by
        calc
          (7 : ZMod 2302624777) ^ 11 = (7 : ZMod 2302624777) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 5 * (7 : ZMod 2302624777) ^ 5) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1977326743 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 2302624777) ^ 22 = 1473268615 := by
        calc
          (7 : ZMod 2302624777) ^ 22 = (7 : ZMod 2302624777) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 11 * (7 : ZMod 2302624777) ^ 11 := by rw [pow_add]
          _ = 1473268615 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 2302624777) ^ 45 = 2101296664 := by
        calc
          (7 : ZMod 2302624777) ^ 45 = (7 : ZMod 2302624777) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 22 * (7 : ZMod 2302624777) ^ 22) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 2101296664 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 2302624777) ^ 91 = 1400828936 := by
        calc
          (7 : ZMod 2302624777) ^ 91 = (7 : ZMod 2302624777) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 45 * (7 : ZMod 2302624777) ^ 45) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1400828936 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 2302624777) ^ 182 = 22650942 := by
        calc
          (7 : ZMod 2302624777) ^ 182 = (7 : ZMod 2302624777) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 91 * (7 : ZMod 2302624777) ^ 91 := by rw [pow_add]
          _ = 22650942 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 2302624777) ^ 365 = 1691979554 := by
        calc
          (7 : ZMod 2302624777) ^ 365 = (7 : ZMod 2302624777) ^ (182 + 182 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 182 * (7 : ZMod 2302624777) ^ 182) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1691979554 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 2302624777) ^ 731 = 553113694 := by
        calc
          (7 : ZMod 2302624777) ^ 731 = (7 : ZMod 2302624777) ^ (365 + 365 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 365 * (7 : ZMod 2302624777) ^ 365) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 553113694 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 2302624777) ^ 1463 = 348058551 := by
        calc
          (7 : ZMod 2302624777) ^ 1463 = (7 : ZMod 2302624777) ^ (731 + 731 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 731 * (7 : ZMod 2302624777) ^ 731) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 348058551 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 2302624777) ^ 2927 = 1998481873 := by
        calc
          (7 : ZMod 2302624777) ^ 2927 = (7 : ZMod 2302624777) ^ (1463 + 1463 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 1463 * (7 : ZMod 2302624777) ^ 1463) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1998481873 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 2302624777) ^ 5855 = 214002807 := by
        calc
          (7 : ZMod 2302624777) ^ 5855 = (7 : ZMod 2302624777) ^ (2927 + 2927 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 2927 * (7 : ZMod 2302624777) ^ 2927) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 214002807 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 2302624777) ^ 11711 = 1228710112 := by
        calc
          (7 : ZMod 2302624777) ^ 11711 = (7 : ZMod 2302624777) ^ (5855 + 5855 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 5855 * (7 : ZMod 2302624777) ^ 5855) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1228710112 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 2302624777) ^ 23423 = 363437499 := by
        calc
          (7 : ZMod 2302624777) ^ 23423 = (7 : ZMod 2302624777) ^ (11711 + 11711 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 11711 * (7 : ZMod 2302624777) ^ 11711) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 363437499 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 2302624777) ^ 46847 = 1899558422 := by
        calc
          (7 : ZMod 2302624777) ^ 46847 = (7 : ZMod 2302624777) ^ (23423 + 23423 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 23423 * (7 : ZMod 2302624777) ^ 23423) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1899558422 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 2302624777) ^ 93694 = 986202960 := by
        calc
          (7 : ZMod 2302624777) ^ 93694 = (7 : ZMod 2302624777) ^ (46847 + 46847) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 46847 * (7 : ZMod 2302624777) ^ 46847 := by rw [pow_add]
          _ = 986202960 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 2302624777) ^ 187388 = 372696091 := by
        calc
          (7 : ZMod 2302624777) ^ 187388 = (7 : ZMod 2302624777) ^ (93694 + 93694) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 93694 * (7 : ZMod 2302624777) ^ 93694 := by rw [pow_add]
          _ = 372696091 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 2302624777) ^ 374776 = 2024444666 := by
        calc
          (7 : ZMod 2302624777) ^ 374776 = (7 : ZMod 2302624777) ^ (187388 + 187388) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 187388 * (7 : ZMod 2302624777) ^ 187388 := by rw [pow_add]
          _ = 2024444666 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 2302624777) ^ 749552 = 1432819941 := by
        calc
          (7 : ZMod 2302624777) ^ 749552 = (7 : ZMod 2302624777) ^ (374776 + 374776) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 374776 * (7 : ZMod 2302624777) ^ 374776 := by rw [pow_add]
          _ = 1432819941 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 2302624777) ^ 1499104 = 435465737 := by
        calc
          (7 : ZMod 2302624777) ^ 1499104 = (7 : ZMod 2302624777) ^ (749552 + 749552) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 749552 * (7 : ZMod 2302624777) ^ 749552 := by rw [pow_add]
          _ = 435465737 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 2302624777) ^ 2998209 = 1235923072 := by
        calc
          (7 : ZMod 2302624777) ^ 2998209 = (7 : ZMod 2302624777) ^ (1499104 + 1499104 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 1499104 * (7 : ZMod 2302624777) ^ 1499104) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1235923072 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 2302624777) ^ 5996418 = 834248236 := by
        calc
          (7 : ZMod 2302624777) ^ 5996418 = (7 : ZMod 2302624777) ^ (2998209 + 2998209) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 2998209 * (7 : ZMod 2302624777) ^ 2998209 := by rw [pow_add]
          _ = 834248236 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 2302624777) ^ 11992837 = 1140738748 := by
        calc
          (7 : ZMod 2302624777) ^ 11992837 = (7 : ZMod 2302624777) ^ (5996418 + 5996418 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 5996418 * (7 : ZMod 2302624777) ^ 5996418) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 1140738748 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 2302624777) ^ 23985674 = 1956969365 := by
        calc
          (7 : ZMod 2302624777) ^ 23985674 = (7 : ZMod 2302624777) ^ (11992837 + 11992837) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 11992837 * (7 : ZMod 2302624777) ^ 11992837 := by rw [pow_add]
          _ = 1956969365 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 2302624777) ^ 47971349 = 36890341 := by
        calc
          (7 : ZMod 2302624777) ^ 47971349 = (7 : ZMod 2302624777) ^ (23985674 + 23985674 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 23985674 * (7 : ZMod 2302624777) ^ 23985674) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 36890341 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 2302624777) ^ 95942699 = 2046380964 := by
        calc
          (7 : ZMod 2302624777) ^ 95942699 = (7 : ZMod 2302624777) ^ (47971349 + 47971349 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 47971349 * (7 : ZMod 2302624777) ^ 47971349) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 2046380964 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 2302624777) ^ 191885398 = 1123398602 := by
        calc
          (7 : ZMod 2302624777) ^ 191885398 = (7 : ZMod 2302624777) ^ (95942699 + 95942699) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 95942699 * (7 : ZMod 2302624777) ^ 95942699 := by rw [pow_add]
          _ = 1123398602 := by rw [factor_1_26]; decide
      have factor_1_28 : (7 : ZMod 2302624777) ^ 383770796 = 610696689 := by
        calc
          (7 : ZMod 2302624777) ^ 383770796 = (7 : ZMod 2302624777) ^ (191885398 + 191885398) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 191885398 * (7 : ZMod 2302624777) ^ 191885398 := by rw [pow_add]
          _ = 610696689 := by rw [factor_1_27]; decide
      have factor_1_29 : (7 : ZMod 2302624777) ^ 767541592 = 610696688 := by
        calc
          (7 : ZMod 2302624777) ^ 767541592 = (7 : ZMod 2302624777) ^ (383770796 + 383770796) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 383770796 * (7 : ZMod 2302624777) ^ 383770796 := by rw [pow_add]
          _ = 610696688 := by rw [factor_1_28]; decide
      change (7 : ZMod 2302624777) ^ 767541592 ≠ 1
      rw [factor_1_29]
      decide
    ·
      have factor_2_0 : (7 : ZMod 2302624777) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 2302624777) ^ 3 = 343 := by
        calc
          (7 : ZMod 2302624777) ^ 3 = (7 : ZMod 2302624777) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = ((7 : ZMod 2302624777) ^ 1 * (7 : ZMod 2302624777) ^ 1) * (7 : ZMod 2302624777) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 2302624777) ^ 6 = 117649 := by
        calc
          (7 : ZMod 2302624777) ^ 6 = (7 : ZMod 2302624777) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 3 * (7 : ZMod 2302624777) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 2302624777) ^ 12 = 25538539 := by
        calc
          (7 : ZMod 2302624777) ^ 12 = (7 : ZMod 2302624777) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 6 * (7 : ZMod 2302624777) ^ 6 := by rw [pow_add]
          _ = 25538539 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 2302624777) ^ 24 = 808794048 := by
        calc
          (7 : ZMod 2302624777) ^ 24 = (7 : ZMod 2302624777) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (7 : ZMod 2302624777) ^ n) (by norm_num)
          _ = (7 : ZMod 2302624777) ^ 12 * (7 : ZMod 2302624777) ^ 12 := by rw [pow_add]
          _ = 808794048 := by rw [factor_2_3]; decide
      change (7 : ZMod 2302624777) ^ 24 ≠ 1
      rw [factor_2_4]
      decide

#print axioms prime_lucas_2302624777

end TotientTailPeriodKiller
end Erdos249257
