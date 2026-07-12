import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime44544251

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_80179651801 : Nat.Prime 80179651801 := by
  apply lucas_primality 80179651801 (11 : ZMod 80179651801)
  ·
      have fermat_0 : (11 : ZMod 80179651801) ^ 1 = 11 := by norm_num
      have fermat_1 : (11 : ZMod 80179651801) ^ 2 = 121 := by
        calc
          (11 : ZMod 80179651801) ^ 2 = (11 : ZMod 80179651801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 1 * (11 : ZMod 80179651801) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [fermat_0]; decide
      have fermat_2 : (11 : ZMod 80179651801) ^ 4 = 14641 := by
        calc
          (11 : ZMod 80179651801) ^ 4 = (11 : ZMod 80179651801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 2 * (11 : ZMod 80179651801) ^ 2 := by rw [pow_add]
          _ = 14641 := by rw [fermat_1]; decide
      have fermat_3 : (11 : ZMod 80179651801) ^ 9 = 2357947691 := by
        calc
          (11 : ZMod 80179651801) ^ 9 = (11 : ZMod 80179651801) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 4 * (11 : ZMod 80179651801) ^ 4) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 2357947691 := by rw [fermat_2]; decide
      have fermat_4 : (11 : ZMod 80179651801) ^ 18 = 74640797236 := by
        calc
          (11 : ZMod 80179651801) ^ 18 = (11 : ZMod 80179651801) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 9 * (11 : ZMod 80179651801) ^ 9 := by rw [pow_add]
          _ = 74640797236 := by rw [fermat_3]; decide
      have fermat_5 : (11 : ZMod 80179651801) ^ 37 = 75391150468 := by
        calc
          (11 : ZMod 80179651801) ^ 37 = (11 : ZMod 80179651801) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 18 * (11 : ZMod 80179651801) ^ 18) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 75391150468 := by rw [fermat_4]; decide
      have fermat_6 : (11 : ZMod 80179651801) ^ 74 = 25414561886 := by
        calc
          (11 : ZMod 80179651801) ^ 74 = (11 : ZMod 80179651801) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 37 * (11 : ZMod 80179651801) ^ 37 := by rw [pow_add]
          _ = 25414561886 := by rw [fermat_5]; decide
      have fermat_7 : (11 : ZMod 80179651801) ^ 149 = 79832812110 := by
        calc
          (11 : ZMod 80179651801) ^ 149 = (11 : ZMod 80179651801) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 74 * (11 : ZMod 80179651801) ^ 74) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 79832812110 := by rw [fermat_6]; decide
      have fermat_8 : (11 : ZMod 80179651801) ^ 298 = 70314041529 := by
        calc
          (11 : ZMod 80179651801) ^ 298 = (11 : ZMod 80179651801) ^ (149 + 149) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 149 * (11 : ZMod 80179651801) ^ 149 := by rw [pow_add]
          _ = 70314041529 := by rw [fermat_7]; decide
      have fermat_9 : (11 : ZMod 80179651801) ^ 597 = 13377619408 := by
        calc
          (11 : ZMod 80179651801) ^ 597 = (11 : ZMod 80179651801) ^ (298 + 298 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 298 * (11 : ZMod 80179651801) ^ 298) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 13377619408 := by rw [fermat_8]; decide
      have fermat_10 : (11 : ZMod 80179651801) ^ 1194 = 36942350979 := by
        calc
          (11 : ZMod 80179651801) ^ 1194 = (11 : ZMod 80179651801) ^ (597 + 597) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 597 * (11 : ZMod 80179651801) ^ 597 := by rw [pow_add]
          _ = 36942350979 := by rw [fermat_9]; decide
      have fermat_11 : (11 : ZMod 80179651801) ^ 2389 = 38224279729 := by
        calc
          (11 : ZMod 80179651801) ^ 2389 = (11 : ZMod 80179651801) ^ (1194 + 1194 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 1194 * (11 : ZMod 80179651801) ^ 1194) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 38224279729 := by rw [fermat_10]; decide
      have fermat_12 : (11 : ZMod 80179651801) ^ 4779 = 72071846605 := by
        calc
          (11 : ZMod 80179651801) ^ 4779 = (11 : ZMod 80179651801) ^ (2389 + 2389 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 2389 * (11 : ZMod 80179651801) ^ 2389) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 72071846605 := by rw [fermat_11]; decide
      have fermat_13 : (11 : ZMod 80179651801) ^ 9558 = 39222150231 := by
        calc
          (11 : ZMod 80179651801) ^ 9558 = (11 : ZMod 80179651801) ^ (4779 + 4779) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 4779 * (11 : ZMod 80179651801) ^ 4779 := by rw [pow_add]
          _ = 39222150231 := by rw [fermat_12]; decide
      have fermat_14 : (11 : ZMod 80179651801) ^ 19116 = 15013502003 := by
        calc
          (11 : ZMod 80179651801) ^ 19116 = (11 : ZMod 80179651801) ^ (9558 + 9558) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 9558 * (11 : ZMod 80179651801) ^ 9558 := by rw [pow_add]
          _ = 15013502003 := by rw [fermat_13]; decide
      have fermat_15 : (11 : ZMod 80179651801) ^ 38232 = 68915804962 := by
        calc
          (11 : ZMod 80179651801) ^ 38232 = (11 : ZMod 80179651801) ^ (19116 + 19116) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 19116 * (11 : ZMod 80179651801) ^ 19116 := by rw [pow_add]
          _ = 68915804962 := by rw [fermat_14]; decide
      have fermat_16 : (11 : ZMod 80179651801) ^ 76465 = 74175374172 := by
        calc
          (11 : ZMod 80179651801) ^ 76465 = (11 : ZMod 80179651801) ^ (38232 + 38232 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 38232 * (11 : ZMod 80179651801) ^ 38232) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 74175374172 := by rw [fermat_15]; decide
      have fermat_17 : (11 : ZMod 80179651801) ^ 152930 = 59317296884 := by
        calc
          (11 : ZMod 80179651801) ^ 152930 = (11 : ZMod 80179651801) ^ (76465 + 76465) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 76465 * (11 : ZMod 80179651801) ^ 76465 := by rw [pow_add]
          _ = 59317296884 := by rw [fermat_16]; decide
      have fermat_18 : (11 : ZMod 80179651801) ^ 305861 = 69156852552 := by
        calc
          (11 : ZMod 80179651801) ^ 305861 = (11 : ZMod 80179651801) ^ (152930 + 152930 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 152930 * (11 : ZMod 80179651801) ^ 152930) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 69156852552 := by rw [fermat_17]; decide
      have fermat_19 : (11 : ZMod 80179651801) ^ 611722 = 61941257905 := by
        calc
          (11 : ZMod 80179651801) ^ 611722 = (11 : ZMod 80179651801) ^ (305861 + 305861) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 305861 * (11 : ZMod 80179651801) ^ 305861 := by rw [pow_add]
          _ = 61941257905 := by rw [fermat_18]; decide
      have fermat_20 : (11 : ZMod 80179651801) ^ 1223444 = 53711486621 := by
        calc
          (11 : ZMod 80179651801) ^ 1223444 = (11 : ZMod 80179651801) ^ (611722 + 611722) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 611722 * (11 : ZMod 80179651801) ^ 611722 := by rw [pow_add]
          _ = 53711486621 := by rw [fermat_19]; decide
      have fermat_21 : (11 : ZMod 80179651801) ^ 2446888 = 12952698679 := by
        calc
          (11 : ZMod 80179651801) ^ 2446888 = (11 : ZMod 80179651801) ^ (1223444 + 1223444) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 1223444 * (11 : ZMod 80179651801) ^ 1223444 := by rw [pow_add]
          _ = 12952698679 := by rw [fermat_20]; decide
      have fermat_22 : (11 : ZMod 80179651801) ^ 4893777 = 24543512937 := by
        calc
          (11 : ZMod 80179651801) ^ 4893777 = (11 : ZMod 80179651801) ^ (2446888 + 2446888 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 2446888 * (11 : ZMod 80179651801) ^ 2446888) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 24543512937 := by rw [fermat_21]; decide
      have fermat_23 : (11 : ZMod 80179651801) ^ 9787555 = 70755231000 := by
        calc
          (11 : ZMod 80179651801) ^ 9787555 = (11 : ZMod 80179651801) ^ (4893777 + 4893777 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 4893777 * (11 : ZMod 80179651801) ^ 4893777) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 70755231000 := by rw [fermat_22]; decide
      have fermat_24 : (11 : ZMod 80179651801) ^ 19575110 = 27535500294 := by
        calc
          (11 : ZMod 80179651801) ^ 19575110 = (11 : ZMod 80179651801) ^ (9787555 + 9787555) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 9787555 * (11 : ZMod 80179651801) ^ 9787555 := by rw [pow_add]
          _ = 27535500294 := by rw [fermat_23]; decide
      have fermat_25 : (11 : ZMod 80179651801) ^ 39150220 = 59978483174 := by
        calc
          (11 : ZMod 80179651801) ^ 39150220 = (11 : ZMod 80179651801) ^ (19575110 + 19575110) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 19575110 * (11 : ZMod 80179651801) ^ 19575110 := by rw [pow_add]
          _ = 59978483174 := by rw [fermat_24]; decide
      have fermat_26 : (11 : ZMod 80179651801) ^ 78300441 = 55185267929 := by
        calc
          (11 : ZMod 80179651801) ^ 78300441 = (11 : ZMod 80179651801) ^ (39150220 + 39150220 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 39150220 * (11 : ZMod 80179651801) ^ 39150220) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 55185267929 := by rw [fermat_25]; decide
      have fermat_27 : (11 : ZMod 80179651801) ^ 156600882 = 45212260218 := by
        calc
          (11 : ZMod 80179651801) ^ 156600882 = (11 : ZMod 80179651801) ^ (78300441 + 78300441) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 78300441 * (11 : ZMod 80179651801) ^ 78300441 := by rw [pow_add]
          _ = 45212260218 := by rw [fermat_26]; decide
      have fermat_28 : (11 : ZMod 80179651801) ^ 313201764 = 10194397693 := by
        calc
          (11 : ZMod 80179651801) ^ 313201764 = (11 : ZMod 80179651801) ^ (156600882 + 156600882) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 156600882 * (11 : ZMod 80179651801) ^ 156600882 := by rw [pow_add]
          _ = 10194397693 := by rw [fermat_27]; decide
      have fermat_29 : (11 : ZMod 80179651801) ^ 626403529 = 30883627625 := by
        calc
          (11 : ZMod 80179651801) ^ 626403529 = (11 : ZMod 80179651801) ^ (313201764 + 313201764 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 313201764 * (11 : ZMod 80179651801) ^ 313201764) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 30883627625 := by rw [fermat_28]; decide
      have fermat_30 : (11 : ZMod 80179651801) ^ 1252807059 = 69271430970 := by
        calc
          (11 : ZMod 80179651801) ^ 1252807059 = (11 : ZMod 80179651801) ^ (626403529 + 626403529 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 626403529 * (11 : ZMod 80179651801) ^ 626403529) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 69271430970 := by rw [fermat_29]; decide
      have fermat_31 : (11 : ZMod 80179651801) ^ 2505614118 = 23909918156 := by
        calc
          (11 : ZMod 80179651801) ^ 2505614118 = (11 : ZMod 80179651801) ^ (1252807059 + 1252807059) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 1252807059 * (11 : ZMod 80179651801) ^ 1252807059 := by rw [pow_add]
          _ = 23909918156 := by rw [fermat_30]; decide
      have fermat_32 : (11 : ZMod 80179651801) ^ 5011228237 = 53007560032 := by
        calc
          (11 : ZMod 80179651801) ^ 5011228237 = (11 : ZMod 80179651801) ^ (2505614118 + 2505614118 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 2505614118 * (11 : ZMod 80179651801) ^ 2505614118) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 53007560032 := by rw [fermat_31]; decide
      have fermat_33 : (11 : ZMod 80179651801) ^ 10022456475 = 9341233520 := by
        calc
          (11 : ZMod 80179651801) ^ 10022456475 = (11 : ZMod 80179651801) ^ (5011228237 + 5011228237 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 5011228237 * (11 : ZMod 80179651801) ^ 5011228237) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 9341233520 := by rw [fermat_32]; decide
      have fermat_34 : (11 : ZMod 80179651801) ^ 20044912950 = 12599063668 := by
        calc
          (11 : ZMod 80179651801) ^ 20044912950 = (11 : ZMod 80179651801) ^ (10022456475 + 10022456475) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 10022456475 * (11 : ZMod 80179651801) ^ 10022456475 := by rw [pow_add]
          _ = 12599063668 := by rw [fermat_33]; decide
      have fermat_35 : (11 : ZMod 80179651801) ^ 40089825900 = 80179651800 := by
        calc
          (11 : ZMod 80179651801) ^ 40089825900 = (11 : ZMod 80179651801) ^ (20044912950 + 20044912950) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 20044912950 * (11 : ZMod 80179651801) ^ 20044912950 := by rw [pow_add]
          _ = 80179651800 := by rw [fermat_34]; decide
      have fermat_36 : (11 : ZMod 80179651801) ^ 80179651800 = 1 := by
        calc
          (11 : ZMod 80179651801) ^ 80179651800 = (11 : ZMod 80179651801) ^ (40089825900 + 40089825900) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 40089825900 * (11 : ZMod 80179651801) ^ 40089825900 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (5, 2), (44544251, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (5, 2), (44544251, 1)] : List FactorBlock).map factorBlockValue).prod = 80179651801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_44544251) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (11 : ZMod 80179651801) ^ 1 = 11 := by norm_num
      have factor_0_1 : (11 : ZMod 80179651801) ^ 2 = 121 := by
        calc
          (11 : ZMod 80179651801) ^ 2 = (11 : ZMod 80179651801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 1 * (11 : ZMod 80179651801) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_0_0]; decide
      have factor_0_2 : (11 : ZMod 80179651801) ^ 4 = 14641 := by
        calc
          (11 : ZMod 80179651801) ^ 4 = (11 : ZMod 80179651801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 2 * (11 : ZMod 80179651801) ^ 2 := by rw [pow_add]
          _ = 14641 := by rw [factor_0_1]; decide
      have factor_0_3 : (11 : ZMod 80179651801) ^ 9 = 2357947691 := by
        calc
          (11 : ZMod 80179651801) ^ 9 = (11 : ZMod 80179651801) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 4 * (11 : ZMod 80179651801) ^ 4) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 2357947691 := by rw [factor_0_2]; decide
      have factor_0_4 : (11 : ZMod 80179651801) ^ 18 = 74640797236 := by
        calc
          (11 : ZMod 80179651801) ^ 18 = (11 : ZMod 80179651801) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 9 * (11 : ZMod 80179651801) ^ 9 := by rw [pow_add]
          _ = 74640797236 := by rw [factor_0_3]; decide
      have factor_0_5 : (11 : ZMod 80179651801) ^ 37 = 75391150468 := by
        calc
          (11 : ZMod 80179651801) ^ 37 = (11 : ZMod 80179651801) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 18 * (11 : ZMod 80179651801) ^ 18) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 75391150468 := by rw [factor_0_4]; decide
      have factor_0_6 : (11 : ZMod 80179651801) ^ 74 = 25414561886 := by
        calc
          (11 : ZMod 80179651801) ^ 74 = (11 : ZMod 80179651801) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 37 * (11 : ZMod 80179651801) ^ 37 := by rw [pow_add]
          _ = 25414561886 := by rw [factor_0_5]; decide
      have factor_0_7 : (11 : ZMod 80179651801) ^ 149 = 79832812110 := by
        calc
          (11 : ZMod 80179651801) ^ 149 = (11 : ZMod 80179651801) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 74 * (11 : ZMod 80179651801) ^ 74) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 79832812110 := by rw [factor_0_6]; decide
      have factor_0_8 : (11 : ZMod 80179651801) ^ 298 = 70314041529 := by
        calc
          (11 : ZMod 80179651801) ^ 298 = (11 : ZMod 80179651801) ^ (149 + 149) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 149 * (11 : ZMod 80179651801) ^ 149 := by rw [pow_add]
          _ = 70314041529 := by rw [factor_0_7]; decide
      have factor_0_9 : (11 : ZMod 80179651801) ^ 597 = 13377619408 := by
        calc
          (11 : ZMod 80179651801) ^ 597 = (11 : ZMod 80179651801) ^ (298 + 298 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 298 * (11 : ZMod 80179651801) ^ 298) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 13377619408 := by rw [factor_0_8]; decide
      have factor_0_10 : (11 : ZMod 80179651801) ^ 1194 = 36942350979 := by
        calc
          (11 : ZMod 80179651801) ^ 1194 = (11 : ZMod 80179651801) ^ (597 + 597) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 597 * (11 : ZMod 80179651801) ^ 597 := by rw [pow_add]
          _ = 36942350979 := by rw [factor_0_9]; decide
      have factor_0_11 : (11 : ZMod 80179651801) ^ 2389 = 38224279729 := by
        calc
          (11 : ZMod 80179651801) ^ 2389 = (11 : ZMod 80179651801) ^ (1194 + 1194 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 1194 * (11 : ZMod 80179651801) ^ 1194) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 38224279729 := by rw [factor_0_10]; decide
      have factor_0_12 : (11 : ZMod 80179651801) ^ 4779 = 72071846605 := by
        calc
          (11 : ZMod 80179651801) ^ 4779 = (11 : ZMod 80179651801) ^ (2389 + 2389 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 2389 * (11 : ZMod 80179651801) ^ 2389) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 72071846605 := by rw [factor_0_11]; decide
      have factor_0_13 : (11 : ZMod 80179651801) ^ 9558 = 39222150231 := by
        calc
          (11 : ZMod 80179651801) ^ 9558 = (11 : ZMod 80179651801) ^ (4779 + 4779) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 4779 * (11 : ZMod 80179651801) ^ 4779 := by rw [pow_add]
          _ = 39222150231 := by rw [factor_0_12]; decide
      have factor_0_14 : (11 : ZMod 80179651801) ^ 19116 = 15013502003 := by
        calc
          (11 : ZMod 80179651801) ^ 19116 = (11 : ZMod 80179651801) ^ (9558 + 9558) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 9558 * (11 : ZMod 80179651801) ^ 9558 := by rw [pow_add]
          _ = 15013502003 := by rw [factor_0_13]; decide
      have factor_0_15 : (11 : ZMod 80179651801) ^ 38232 = 68915804962 := by
        calc
          (11 : ZMod 80179651801) ^ 38232 = (11 : ZMod 80179651801) ^ (19116 + 19116) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 19116 * (11 : ZMod 80179651801) ^ 19116 := by rw [pow_add]
          _ = 68915804962 := by rw [factor_0_14]; decide
      have factor_0_16 : (11 : ZMod 80179651801) ^ 76465 = 74175374172 := by
        calc
          (11 : ZMod 80179651801) ^ 76465 = (11 : ZMod 80179651801) ^ (38232 + 38232 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 38232 * (11 : ZMod 80179651801) ^ 38232) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 74175374172 := by rw [factor_0_15]; decide
      have factor_0_17 : (11 : ZMod 80179651801) ^ 152930 = 59317296884 := by
        calc
          (11 : ZMod 80179651801) ^ 152930 = (11 : ZMod 80179651801) ^ (76465 + 76465) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 76465 * (11 : ZMod 80179651801) ^ 76465 := by rw [pow_add]
          _ = 59317296884 := by rw [factor_0_16]; decide
      have factor_0_18 : (11 : ZMod 80179651801) ^ 305861 = 69156852552 := by
        calc
          (11 : ZMod 80179651801) ^ 305861 = (11 : ZMod 80179651801) ^ (152930 + 152930 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 152930 * (11 : ZMod 80179651801) ^ 152930) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 69156852552 := by rw [factor_0_17]; decide
      have factor_0_19 : (11 : ZMod 80179651801) ^ 611722 = 61941257905 := by
        calc
          (11 : ZMod 80179651801) ^ 611722 = (11 : ZMod 80179651801) ^ (305861 + 305861) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 305861 * (11 : ZMod 80179651801) ^ 305861 := by rw [pow_add]
          _ = 61941257905 := by rw [factor_0_18]; decide
      have factor_0_20 : (11 : ZMod 80179651801) ^ 1223444 = 53711486621 := by
        calc
          (11 : ZMod 80179651801) ^ 1223444 = (11 : ZMod 80179651801) ^ (611722 + 611722) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 611722 * (11 : ZMod 80179651801) ^ 611722 := by rw [pow_add]
          _ = 53711486621 := by rw [factor_0_19]; decide
      have factor_0_21 : (11 : ZMod 80179651801) ^ 2446888 = 12952698679 := by
        calc
          (11 : ZMod 80179651801) ^ 2446888 = (11 : ZMod 80179651801) ^ (1223444 + 1223444) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 1223444 * (11 : ZMod 80179651801) ^ 1223444 := by rw [pow_add]
          _ = 12952698679 := by rw [factor_0_20]; decide
      have factor_0_22 : (11 : ZMod 80179651801) ^ 4893777 = 24543512937 := by
        calc
          (11 : ZMod 80179651801) ^ 4893777 = (11 : ZMod 80179651801) ^ (2446888 + 2446888 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 2446888 * (11 : ZMod 80179651801) ^ 2446888) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 24543512937 := by rw [factor_0_21]; decide
      have factor_0_23 : (11 : ZMod 80179651801) ^ 9787555 = 70755231000 := by
        calc
          (11 : ZMod 80179651801) ^ 9787555 = (11 : ZMod 80179651801) ^ (4893777 + 4893777 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 4893777 * (11 : ZMod 80179651801) ^ 4893777) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 70755231000 := by rw [factor_0_22]; decide
      have factor_0_24 : (11 : ZMod 80179651801) ^ 19575110 = 27535500294 := by
        calc
          (11 : ZMod 80179651801) ^ 19575110 = (11 : ZMod 80179651801) ^ (9787555 + 9787555) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 9787555 * (11 : ZMod 80179651801) ^ 9787555 := by rw [pow_add]
          _ = 27535500294 := by rw [factor_0_23]; decide
      have factor_0_25 : (11 : ZMod 80179651801) ^ 39150220 = 59978483174 := by
        calc
          (11 : ZMod 80179651801) ^ 39150220 = (11 : ZMod 80179651801) ^ (19575110 + 19575110) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 19575110 * (11 : ZMod 80179651801) ^ 19575110 := by rw [pow_add]
          _ = 59978483174 := by rw [factor_0_24]; decide
      have factor_0_26 : (11 : ZMod 80179651801) ^ 78300441 = 55185267929 := by
        calc
          (11 : ZMod 80179651801) ^ 78300441 = (11 : ZMod 80179651801) ^ (39150220 + 39150220 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 39150220 * (11 : ZMod 80179651801) ^ 39150220) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 55185267929 := by rw [factor_0_25]; decide
      have factor_0_27 : (11 : ZMod 80179651801) ^ 156600882 = 45212260218 := by
        calc
          (11 : ZMod 80179651801) ^ 156600882 = (11 : ZMod 80179651801) ^ (78300441 + 78300441) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 78300441 * (11 : ZMod 80179651801) ^ 78300441 := by rw [pow_add]
          _ = 45212260218 := by rw [factor_0_26]; decide
      have factor_0_28 : (11 : ZMod 80179651801) ^ 313201764 = 10194397693 := by
        calc
          (11 : ZMod 80179651801) ^ 313201764 = (11 : ZMod 80179651801) ^ (156600882 + 156600882) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 156600882 * (11 : ZMod 80179651801) ^ 156600882 := by rw [pow_add]
          _ = 10194397693 := by rw [factor_0_27]; decide
      have factor_0_29 : (11 : ZMod 80179651801) ^ 626403529 = 30883627625 := by
        calc
          (11 : ZMod 80179651801) ^ 626403529 = (11 : ZMod 80179651801) ^ (313201764 + 313201764 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 313201764 * (11 : ZMod 80179651801) ^ 313201764) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 30883627625 := by rw [factor_0_28]; decide
      have factor_0_30 : (11 : ZMod 80179651801) ^ 1252807059 = 69271430970 := by
        calc
          (11 : ZMod 80179651801) ^ 1252807059 = (11 : ZMod 80179651801) ^ (626403529 + 626403529 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 626403529 * (11 : ZMod 80179651801) ^ 626403529) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 69271430970 := by rw [factor_0_29]; decide
      have factor_0_31 : (11 : ZMod 80179651801) ^ 2505614118 = 23909918156 := by
        calc
          (11 : ZMod 80179651801) ^ 2505614118 = (11 : ZMod 80179651801) ^ (1252807059 + 1252807059) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 1252807059 * (11 : ZMod 80179651801) ^ 1252807059 := by rw [pow_add]
          _ = 23909918156 := by rw [factor_0_30]; decide
      have factor_0_32 : (11 : ZMod 80179651801) ^ 5011228237 = 53007560032 := by
        calc
          (11 : ZMod 80179651801) ^ 5011228237 = (11 : ZMod 80179651801) ^ (2505614118 + 2505614118 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 2505614118 * (11 : ZMod 80179651801) ^ 2505614118) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 53007560032 := by rw [factor_0_31]; decide
      have factor_0_33 : (11 : ZMod 80179651801) ^ 10022456475 = 9341233520 := by
        calc
          (11 : ZMod 80179651801) ^ 10022456475 = (11 : ZMod 80179651801) ^ (5011228237 + 5011228237 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 5011228237 * (11 : ZMod 80179651801) ^ 5011228237) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 9341233520 := by rw [factor_0_32]; decide
      have factor_0_34 : (11 : ZMod 80179651801) ^ 20044912950 = 12599063668 := by
        calc
          (11 : ZMod 80179651801) ^ 20044912950 = (11 : ZMod 80179651801) ^ (10022456475 + 10022456475) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 10022456475 * (11 : ZMod 80179651801) ^ 10022456475 := by rw [pow_add]
          _ = 12599063668 := by rw [factor_0_33]; decide
      have factor_0_35 : (11 : ZMod 80179651801) ^ 40089825900 = 80179651800 := by
        calc
          (11 : ZMod 80179651801) ^ 40089825900 = (11 : ZMod 80179651801) ^ (20044912950 + 20044912950) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 20044912950 * (11 : ZMod 80179651801) ^ 20044912950 := by rw [pow_add]
          _ = 80179651800 := by rw [factor_0_34]; decide
      change (11 : ZMod 80179651801) ^ 40089825900 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (11 : ZMod 80179651801) ^ 1 = 11 := by norm_num
      have factor_1_1 : (11 : ZMod 80179651801) ^ 3 = 1331 := by
        calc
          (11 : ZMod 80179651801) ^ 3 = (11 : ZMod 80179651801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 1 * (11 : ZMod 80179651801) ^ 1) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 1331 := by rw [factor_1_0]; decide
      have factor_1_2 : (11 : ZMod 80179651801) ^ 6 = 1771561 := by
        calc
          (11 : ZMod 80179651801) ^ 6 = (11 : ZMod 80179651801) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 3 * (11 : ZMod 80179651801) ^ 3 := by rw [pow_add]
          _ = 1771561 := by rw [factor_1_1]; decide
      have factor_1_3 : (11 : ZMod 80179651801) ^ 12 = 11421956482 := by
        calc
          (11 : ZMod 80179651801) ^ 12 = (11 : ZMod 80179651801) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 6 * (11 : ZMod 80179651801) ^ 6 := by rw [pow_add]
          _ = 11421956482 := by rw [factor_1_2]; decide
      have factor_1_4 : (11 : ZMod 80179651801) ^ 24 = 47235032216 := by
        calc
          (11 : ZMod 80179651801) ^ 24 = (11 : ZMod 80179651801) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 12 * (11 : ZMod 80179651801) ^ 12 := by rw [pow_add]
          _ = 47235032216 := by rw [factor_1_3]; decide
      have factor_1_5 : (11 : ZMod 80179651801) ^ 49 = 46099377513 := by
        calc
          (11 : ZMod 80179651801) ^ 49 = (11 : ZMod 80179651801) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 24 * (11 : ZMod 80179651801) ^ 24) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 46099377513 := by rw [factor_1_4]; decide
      have factor_1_6 : (11 : ZMod 80179651801) ^ 99 = 22372349553 := by
        calc
          (11 : ZMod 80179651801) ^ 99 = (11 : ZMod 80179651801) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 49 * (11 : ZMod 80179651801) ^ 49) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 22372349553 := by rw [factor_1_5]; decide
      have factor_1_7 : (11 : ZMod 80179651801) ^ 199 = 22470059097 := by
        calc
          (11 : ZMod 80179651801) ^ 199 = (11 : ZMod 80179651801) ^ (99 + 99 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 99 * (11 : ZMod 80179651801) ^ 99) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 22470059097 := by rw [factor_1_6]; decide
      have factor_1_8 : (11 : ZMod 80179651801) ^ 398 = 18160782348 := by
        calc
          (11 : ZMod 80179651801) ^ 398 = (11 : ZMod 80179651801) ^ (199 + 199) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 199 * (11 : ZMod 80179651801) ^ 199 := by rw [pow_add]
          _ = 18160782348 := by rw [factor_1_7]; decide
      have factor_1_9 : (11 : ZMod 80179651801) ^ 796 = 11218503642 := by
        calc
          (11 : ZMod 80179651801) ^ 796 = (11 : ZMod 80179651801) ^ (398 + 398) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 398 * (11 : ZMod 80179651801) ^ 398 := by rw [pow_add]
          _ = 11218503642 := by rw [factor_1_8]; decide
      have factor_1_10 : (11 : ZMod 80179651801) ^ 1593 = 54040659653 := by
        calc
          (11 : ZMod 80179651801) ^ 1593 = (11 : ZMod 80179651801) ^ (796 + 796 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 796 * (11 : ZMod 80179651801) ^ 796) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 54040659653 := by rw [factor_1_9]; decide
      have factor_1_11 : (11 : ZMod 80179651801) ^ 3186 = 76386281097 := by
        calc
          (11 : ZMod 80179651801) ^ 3186 = (11 : ZMod 80179651801) ^ (1593 + 1593) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 1593 * (11 : ZMod 80179651801) ^ 1593 := by rw [pow_add]
          _ = 76386281097 := by rw [factor_1_10]; decide
      have factor_1_12 : (11 : ZMod 80179651801) ^ 6372 = 74534448672 := by
        calc
          (11 : ZMod 80179651801) ^ 6372 = (11 : ZMod 80179651801) ^ (3186 + 3186) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 3186 * (11 : ZMod 80179651801) ^ 3186 := by rw [pow_add]
          _ = 74534448672 := by rw [factor_1_11]; decide
      have factor_1_13 : (11 : ZMod 80179651801) ^ 12744 = 27560721420 := by
        calc
          (11 : ZMod 80179651801) ^ 12744 = (11 : ZMod 80179651801) ^ (6372 + 6372) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 6372 * (11 : ZMod 80179651801) ^ 6372 := by rw [pow_add]
          _ = 27560721420 := by rw [factor_1_12]; decide
      have factor_1_14 : (11 : ZMod 80179651801) ^ 25488 = 75367190198 := by
        calc
          (11 : ZMod 80179651801) ^ 25488 = (11 : ZMod 80179651801) ^ (12744 + 12744) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 12744 * (11 : ZMod 80179651801) ^ 12744 := by rw [pow_add]
          _ = 75367190198 := by rw [factor_1_13]; decide
      have factor_1_15 : (11 : ZMod 80179651801) ^ 50976 = 14591205128 := by
        calc
          (11 : ZMod 80179651801) ^ 50976 = (11 : ZMod 80179651801) ^ (25488 + 25488) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 25488 * (11 : ZMod 80179651801) ^ 25488 := by rw [pow_add]
          _ = 14591205128 := by rw [factor_1_14]; decide
      have factor_1_16 : (11 : ZMod 80179651801) ^ 101953 = 71013074836 := by
        calc
          (11 : ZMod 80179651801) ^ 101953 = (11 : ZMod 80179651801) ^ (50976 + 50976 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 50976 * (11 : ZMod 80179651801) ^ 50976) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 71013074836 := by rw [factor_1_15]; decide
      have factor_1_17 : (11 : ZMod 80179651801) ^ 203907 = 75450884718 := by
        calc
          (11 : ZMod 80179651801) ^ 203907 = (11 : ZMod 80179651801) ^ (101953 + 101953 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 101953 * (11 : ZMod 80179651801) ^ 101953) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 75450884718 := by rw [factor_1_16]; decide
      have factor_1_18 : (11 : ZMod 80179651801) ^ 407814 = 60181049500 := by
        calc
          (11 : ZMod 80179651801) ^ 407814 = (11 : ZMod 80179651801) ^ (203907 + 203907) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 203907 * (11 : ZMod 80179651801) ^ 203907 := by rw [pow_add]
          _ = 60181049500 := by rw [factor_1_17]; decide
      have factor_1_19 : (11 : ZMod 80179651801) ^ 815629 = 44320951137 := by
        calc
          (11 : ZMod 80179651801) ^ 815629 = (11 : ZMod 80179651801) ^ (407814 + 407814 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 407814 * (11 : ZMod 80179651801) ^ 407814) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 44320951137 := by rw [factor_1_18]; decide
      have factor_1_20 : (11 : ZMod 80179651801) ^ 1631259 = 5754426611 := by
        calc
          (11 : ZMod 80179651801) ^ 1631259 = (11 : ZMod 80179651801) ^ (815629 + 815629 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 815629 * (11 : ZMod 80179651801) ^ 815629) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 5754426611 := by rw [factor_1_19]; decide
      have factor_1_21 : (11 : ZMod 80179651801) ^ 3262518 = 34205404732 := by
        calc
          (11 : ZMod 80179651801) ^ 3262518 = (11 : ZMod 80179651801) ^ (1631259 + 1631259) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 1631259 * (11 : ZMod 80179651801) ^ 1631259 := by rw [pow_add]
          _ = 34205404732 := by rw [factor_1_20]; decide
      have factor_1_22 : (11 : ZMod 80179651801) ^ 6525036 = 58767653893 := by
        calc
          (11 : ZMod 80179651801) ^ 6525036 = (11 : ZMod 80179651801) ^ (3262518 + 3262518) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 3262518 * (11 : ZMod 80179651801) ^ 3262518 := by rw [pow_add]
          _ = 58767653893 := by rw [factor_1_21]; decide
      have factor_1_23 : (11 : ZMod 80179651801) ^ 13050073 = 2069324533 := by
        calc
          (11 : ZMod 80179651801) ^ 13050073 = (11 : ZMod 80179651801) ^ (6525036 + 6525036 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 6525036 * (11 : ZMod 80179651801) ^ 6525036) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 2069324533 := by rw [factor_1_22]; decide
      have factor_1_24 : (11 : ZMod 80179651801) ^ 26100147 = 38756985327 := by
        calc
          (11 : ZMod 80179651801) ^ 26100147 = (11 : ZMod 80179651801) ^ (13050073 + 13050073 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 13050073 * (11 : ZMod 80179651801) ^ 13050073) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 38756985327 := by rw [factor_1_23]; decide
      have factor_1_25 : (11 : ZMod 80179651801) ^ 52200294 = 935608907 := by
        calc
          (11 : ZMod 80179651801) ^ 52200294 = (11 : ZMod 80179651801) ^ (26100147 + 26100147) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 26100147 * (11 : ZMod 80179651801) ^ 26100147 := by rw [pow_add]
          _ = 935608907 := by rw [factor_1_24]; decide
      have factor_1_26 : (11 : ZMod 80179651801) ^ 104400588 = 32391807716 := by
        calc
          (11 : ZMod 80179651801) ^ 104400588 = (11 : ZMod 80179651801) ^ (52200294 + 52200294) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 52200294 * (11 : ZMod 80179651801) ^ 52200294 := by rw [pow_add]
          _ = 32391807716 := by rw [factor_1_25]; decide
      have factor_1_27 : (11 : ZMod 80179651801) ^ 208801176 = 48237240663 := by
        calc
          (11 : ZMod 80179651801) ^ 208801176 = (11 : ZMod 80179651801) ^ (104400588 + 104400588) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 104400588 * (11 : ZMod 80179651801) ^ 104400588 := by rw [pow_add]
          _ = 48237240663 := by rw [factor_1_26]; decide
      have factor_1_28 : (11 : ZMod 80179651801) ^ 417602353 = 18666642888 := by
        calc
          (11 : ZMod 80179651801) ^ 417602353 = (11 : ZMod 80179651801) ^ (208801176 + 208801176 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 208801176 * (11 : ZMod 80179651801) ^ 208801176) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 18666642888 := by rw [factor_1_27]; decide
      have factor_1_29 : (11 : ZMod 80179651801) ^ 835204706 = 62156154388 := by
        calc
          (11 : ZMod 80179651801) ^ 835204706 = (11 : ZMod 80179651801) ^ (417602353 + 417602353) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 417602353 * (11 : ZMod 80179651801) ^ 417602353 := by rw [pow_add]
          _ = 62156154388 := by rw [factor_1_28]; decide
      have factor_1_30 : (11 : ZMod 80179651801) ^ 1670409412 = 62284897034 := by
        calc
          (11 : ZMod 80179651801) ^ 1670409412 = (11 : ZMod 80179651801) ^ (835204706 + 835204706) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 835204706 * (11 : ZMod 80179651801) ^ 835204706 := by rw [pow_add]
          _ = 62284897034 := by rw [factor_1_29]; decide
      have factor_1_31 : (11 : ZMod 80179651801) ^ 3340818825 = 47106718226 := by
        calc
          (11 : ZMod 80179651801) ^ 3340818825 = (11 : ZMod 80179651801) ^ (1670409412 + 1670409412 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 1670409412 * (11 : ZMod 80179651801) ^ 1670409412) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 47106718226 := by rw [factor_1_30]; decide
      have factor_1_32 : (11 : ZMod 80179651801) ^ 6681637650 = 61386419086 := by
        calc
          (11 : ZMod 80179651801) ^ 6681637650 = (11 : ZMod 80179651801) ^ (3340818825 + 3340818825) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 3340818825 * (11 : ZMod 80179651801) ^ 3340818825 := by rw [pow_add]
          _ = 61386419086 := by rw [factor_1_31]; decide
      have factor_1_33 : (11 : ZMod 80179651801) ^ 13363275300 = 65922085593 := by
        calc
          (11 : ZMod 80179651801) ^ 13363275300 = (11 : ZMod 80179651801) ^ (6681637650 + 6681637650) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 6681637650 * (11 : ZMod 80179651801) ^ 6681637650 := by rw [pow_add]
          _ = 65922085593 := by rw [factor_1_32]; decide
      have factor_1_34 : (11 : ZMod 80179651801) ^ 26726550600 = 65922085592 := by
        calc
          (11 : ZMod 80179651801) ^ 26726550600 = (11 : ZMod 80179651801) ^ (13363275300 + 13363275300) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 13363275300 * (11 : ZMod 80179651801) ^ 13363275300 := by rw [pow_add]
          _ = 65922085592 := by rw [factor_1_33]; decide
      change (11 : ZMod 80179651801) ^ 26726550600 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (11 : ZMod 80179651801) ^ 1 = 11 := by norm_num
      have factor_2_1 : (11 : ZMod 80179651801) ^ 3 = 1331 := by
        calc
          (11 : ZMod 80179651801) ^ 3 = (11 : ZMod 80179651801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 1 * (11 : ZMod 80179651801) ^ 1) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 1331 := by rw [factor_2_0]; decide
      have factor_2_2 : (11 : ZMod 80179651801) ^ 7 = 19487171 := by
        calc
          (11 : ZMod 80179651801) ^ 7 = (11 : ZMod 80179651801) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 3 * (11 : ZMod 80179651801) ^ 3) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 19487171 := by rw [factor_2_1]; decide
      have factor_2_3 : (11 : ZMod 80179651801) ^ 14 = 19002653705 := by
        calc
          (11 : ZMod 80179651801) ^ 14 = (11 : ZMod 80179651801) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 7 * (11 : ZMod 80179651801) ^ 7 := by rw [pow_add]
          _ = 19002653705 := by rw [factor_2_2]; decide
      have factor_2_4 : (11 : ZMod 80179651801) ^ 29 = 44349495539 := by
        calc
          (11 : ZMod 80179651801) ^ 29 = (11 : ZMod 80179651801) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 14 * (11 : ZMod 80179651801) ^ 14) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 44349495539 := by rw [factor_2_3]; decide
      have factor_2_5 : (11 : ZMod 80179651801) ^ 59 = 22902463789 := by
        calc
          (11 : ZMod 80179651801) ^ 59 = (11 : ZMod 80179651801) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 29 * (11 : ZMod 80179651801) ^ 29) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 22902463789 := by rw [factor_2_4]; decide
      have factor_2_6 : (11 : ZMod 80179651801) ^ 119 = 37260445641 := by
        calc
          (11 : ZMod 80179651801) ^ 119 = (11 : ZMod 80179651801) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 59 * (11 : ZMod 80179651801) ^ 59) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 37260445641 := by rw [factor_2_5]; decide
      have factor_2_7 : (11 : ZMod 80179651801) ^ 238 = 23004030195 := by
        calc
          (11 : ZMod 80179651801) ^ 238 = (11 : ZMod 80179651801) ^ (119 + 119) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 119 * (11 : ZMod 80179651801) ^ 119 := by rw [pow_add]
          _ = 23004030195 := by rw [factor_2_6]; decide
      have factor_2_8 : (11 : ZMod 80179651801) ^ 477 = 56776722577 := by
        calc
          (11 : ZMod 80179651801) ^ 477 = (11 : ZMod 80179651801) ^ (238 + 238 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 238 * (11 : ZMod 80179651801) ^ 238) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 56776722577 := by rw [factor_2_7]; decide
      have factor_2_9 : (11 : ZMod 80179651801) ^ 955 = 60598632087 := by
        calc
          (11 : ZMod 80179651801) ^ 955 = (11 : ZMod 80179651801) ^ (477 + 477 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 477 * (11 : ZMod 80179651801) ^ 477) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 60598632087 := by rw [factor_2_8]; decide
      have factor_2_10 : (11 : ZMod 80179651801) ^ 1911 = 35746021263 := by
        calc
          (11 : ZMod 80179651801) ^ 1911 = (11 : ZMod 80179651801) ^ (955 + 955 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 955 * (11 : ZMod 80179651801) ^ 955) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 35746021263 := by rw [factor_2_9]; decide
      have factor_2_11 : (11 : ZMod 80179651801) ^ 3823 = 69523523933 := by
        calc
          (11 : ZMod 80179651801) ^ 3823 = (11 : ZMod 80179651801) ^ (1911 + 1911 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 1911 * (11 : ZMod 80179651801) ^ 1911) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 69523523933 := by rw [factor_2_10]; decide
      have factor_2_12 : (11 : ZMod 80179651801) ^ 7646 = 27327165320 := by
        calc
          (11 : ZMod 80179651801) ^ 7646 = (11 : ZMod 80179651801) ^ (3823 + 3823) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 3823 * (11 : ZMod 80179651801) ^ 3823 := by rw [pow_add]
          _ = 27327165320 := by rw [factor_2_11]; decide
      have factor_2_13 : (11 : ZMod 80179651801) ^ 15293 = 22666297512 := by
        calc
          (11 : ZMod 80179651801) ^ 15293 = (11 : ZMod 80179651801) ^ (7646 + 7646 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 7646 * (11 : ZMod 80179651801) ^ 7646) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 22666297512 := by rw [factor_2_12]; decide
      have factor_2_14 : (11 : ZMod 80179651801) ^ 30586 = 71906828573 := by
        calc
          (11 : ZMod 80179651801) ^ 30586 = (11 : ZMod 80179651801) ^ (15293 + 15293) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 15293 * (11 : ZMod 80179651801) ^ 15293 := by rw [pow_add]
          _ = 71906828573 := by rw [factor_2_13]; decide
      have factor_2_15 : (11 : ZMod 80179651801) ^ 61172 = 17937572968 := by
        calc
          (11 : ZMod 80179651801) ^ 61172 = (11 : ZMod 80179651801) ^ (30586 + 30586) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 30586 * (11 : ZMod 80179651801) ^ 30586 := by rw [pow_add]
          _ = 17937572968 := by rw [factor_2_14]; decide
      have factor_2_16 : (11 : ZMod 80179651801) ^ 122344 = 5522082134 := by
        calc
          (11 : ZMod 80179651801) ^ 122344 = (11 : ZMod 80179651801) ^ (61172 + 61172) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 61172 * (11 : ZMod 80179651801) ^ 61172 := by rw [pow_add]
          _ = 5522082134 := by rw [factor_2_15]; decide
      have factor_2_17 : (11 : ZMod 80179651801) ^ 244688 = 78525972218 := by
        calc
          (11 : ZMod 80179651801) ^ 244688 = (11 : ZMod 80179651801) ^ (122344 + 122344) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 122344 * (11 : ZMod 80179651801) ^ 122344 := by rw [pow_add]
          _ = 78525972218 := by rw [factor_2_16]; decide
      have factor_2_18 : (11 : ZMod 80179651801) ^ 489377 = 61426131263 := by
        calc
          (11 : ZMod 80179651801) ^ 489377 = (11 : ZMod 80179651801) ^ (244688 + 244688 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 244688 * (11 : ZMod 80179651801) ^ 244688) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 61426131263 := by rw [factor_2_17]; decide
      have factor_2_19 : (11 : ZMod 80179651801) ^ 978755 = 44517655155 := by
        calc
          (11 : ZMod 80179651801) ^ 978755 = (11 : ZMod 80179651801) ^ (489377 + 489377 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 489377 * (11 : ZMod 80179651801) ^ 489377) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 44517655155 := by rw [factor_2_18]; decide
      have factor_2_20 : (11 : ZMod 80179651801) ^ 1957511 = 19378032743 := by
        calc
          (11 : ZMod 80179651801) ^ 1957511 = (11 : ZMod 80179651801) ^ (978755 + 978755 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 978755 * (11 : ZMod 80179651801) ^ 978755) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 19378032743 := by rw [factor_2_19]; decide
      have factor_2_21 : (11 : ZMod 80179651801) ^ 3915022 = 18531691856 := by
        calc
          (11 : ZMod 80179651801) ^ 3915022 = (11 : ZMod 80179651801) ^ (1957511 + 1957511) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 1957511 * (11 : ZMod 80179651801) ^ 1957511 := by rw [pow_add]
          _ = 18531691856 := by rw [factor_2_20]; decide
      have factor_2_22 : (11 : ZMod 80179651801) ^ 7830044 = 27582338803 := by
        calc
          (11 : ZMod 80179651801) ^ 7830044 = (11 : ZMod 80179651801) ^ (3915022 + 3915022) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 3915022 * (11 : ZMod 80179651801) ^ 3915022 := by rw [pow_add]
          _ = 27582338803 := by rw [factor_2_21]; decide
      have factor_2_23 : (11 : ZMod 80179651801) ^ 15660088 = 44791679785 := by
        calc
          (11 : ZMod 80179651801) ^ 15660088 = (11 : ZMod 80179651801) ^ (7830044 + 7830044) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 7830044 * (11 : ZMod 80179651801) ^ 7830044 := by rw [pow_add]
          _ = 44791679785 := by rw [factor_2_22]; decide
      have factor_2_24 : (11 : ZMod 80179651801) ^ 31320176 = 72757701695 := by
        calc
          (11 : ZMod 80179651801) ^ 31320176 = (11 : ZMod 80179651801) ^ (15660088 + 15660088) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 15660088 * (11 : ZMod 80179651801) ^ 15660088 := by rw [pow_add]
          _ = 72757701695 := by rw [factor_2_23]; decide
      have factor_2_25 : (11 : ZMod 80179651801) ^ 62640352 = 40975526858 := by
        calc
          (11 : ZMod 80179651801) ^ 62640352 = (11 : ZMod 80179651801) ^ (31320176 + 31320176) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 31320176 * (11 : ZMod 80179651801) ^ 31320176 := by rw [pow_add]
          _ = 40975526858 := by rw [factor_2_24]; decide
      have factor_2_26 : (11 : ZMod 80179651801) ^ 125280705 = 66103823001 := by
        calc
          (11 : ZMod 80179651801) ^ 125280705 = (11 : ZMod 80179651801) ^ (62640352 + 62640352 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 62640352 * (11 : ZMod 80179651801) ^ 62640352) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 66103823001 := by rw [factor_2_25]; decide
      have factor_2_27 : (11 : ZMod 80179651801) ^ 250561411 = 12011482791 := by
        calc
          (11 : ZMod 80179651801) ^ 250561411 = (11 : ZMod 80179651801) ^ (125280705 + 125280705 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 125280705 * (11 : ZMod 80179651801) ^ 125280705) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 12011482791 := by rw [factor_2_26]; decide
      have factor_2_28 : (11 : ZMod 80179651801) ^ 501122823 = 10945572490 := by
        calc
          (11 : ZMod 80179651801) ^ 501122823 = (11 : ZMod 80179651801) ^ (250561411 + 250561411 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 250561411 * (11 : ZMod 80179651801) ^ 250561411) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 10945572490 := by rw [factor_2_27]; decide
      have factor_2_29 : (11 : ZMod 80179651801) ^ 1002245647 = 61626320852 := by
        calc
          (11 : ZMod 80179651801) ^ 1002245647 = (11 : ZMod 80179651801) ^ (501122823 + 501122823 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 501122823 * (11 : ZMod 80179651801) ^ 501122823) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 61626320852 := by rw [factor_2_28]; decide
      have factor_2_30 : (11 : ZMod 80179651801) ^ 2004491295 = 36075472718 := by
        calc
          (11 : ZMod 80179651801) ^ 2004491295 = (11 : ZMod 80179651801) ^ (1002245647 + 1002245647 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 1002245647 * (11 : ZMod 80179651801) ^ 1002245647) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 36075472718 := by rw [factor_2_29]; decide
      have factor_2_31 : (11 : ZMod 80179651801) ^ 4008982590 = 18477992408 := by
        calc
          (11 : ZMod 80179651801) ^ 4008982590 = (11 : ZMod 80179651801) ^ (2004491295 + 2004491295) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 2004491295 * (11 : ZMod 80179651801) ^ 2004491295 := by rw [pow_add]
          _ = 18477992408 := by rw [factor_2_30]; decide
      have factor_2_32 : (11 : ZMod 80179651801) ^ 8017965180 = 51140788764 := by
        calc
          (11 : ZMod 80179651801) ^ 8017965180 = (11 : ZMod 80179651801) ^ (4008982590 + 4008982590) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 4008982590 * (11 : ZMod 80179651801) ^ 4008982590 := by rw [pow_add]
          _ = 51140788764 := by rw [factor_2_31]; decide
      have factor_2_33 : (11 : ZMod 80179651801) ^ 16035930360 = 29375857036 := by
        calc
          (11 : ZMod 80179651801) ^ 16035930360 = (11 : ZMod 80179651801) ^ (8017965180 + 8017965180) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 8017965180 * (11 : ZMod 80179651801) ^ 8017965180 := by rw [pow_add]
          _ = 29375857036 := by rw [factor_2_32]; decide
      change (11 : ZMod 80179651801) ^ 16035930360 ≠ 1
      rw [factor_2_33]
      decide
    ·
      have factor_3_0 : (11 : ZMod 80179651801) ^ 1 = 11 := by norm_num
      have factor_3_1 : (11 : ZMod 80179651801) ^ 3 = 1331 := by
        calc
          (11 : ZMod 80179651801) ^ 3 = (11 : ZMod 80179651801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 1 * (11 : ZMod 80179651801) ^ 1) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 1331 := by rw [factor_3_0]; decide
      have factor_3_2 : (11 : ZMod 80179651801) ^ 7 = 19487171 := by
        calc
          (11 : ZMod 80179651801) ^ 7 = (11 : ZMod 80179651801) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 3 * (11 : ZMod 80179651801) ^ 3) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 19487171 := by rw [factor_3_1]; decide
      have factor_3_3 : (11 : ZMod 80179651801) ^ 14 = 19002653705 := by
        calc
          (11 : ZMod 80179651801) ^ 14 = (11 : ZMod 80179651801) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 7 * (11 : ZMod 80179651801) ^ 7 := by rw [pow_add]
          _ = 19002653705 := by rw [factor_3_2]; decide
      have factor_3_4 : (11 : ZMod 80179651801) ^ 28 = 18609890831 := by
        calc
          (11 : ZMod 80179651801) ^ 28 = (11 : ZMod 80179651801) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 14 * (11 : ZMod 80179651801) ^ 14 := by rw [pow_add]
          _ = 18609890831 := by rw [factor_3_3]; decide
      have factor_3_5 : (11 : ZMod 80179651801) ^ 56 = 3270175553 := by
        calc
          (11 : ZMod 80179651801) ^ 56 = (11 : ZMod 80179651801) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 28 * (11 : ZMod 80179651801) ^ 28 := by rw [pow_add]
          _ = 3270175553 := by rw [factor_3_4]; decide
      have factor_3_6 : (11 : ZMod 80179651801) ^ 112 = 13378624923 := by
        calc
          (11 : ZMod 80179651801) ^ 112 = (11 : ZMod 80179651801) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 56 * (11 : ZMod 80179651801) ^ 56 := by rw [pow_add]
          _ = 13378624923 := by rw [factor_3_5]; decide
      have factor_3_7 : (11 : ZMod 80179651801) ^ 225 = 48747879695 := by
        calc
          (11 : ZMod 80179651801) ^ 225 = (11 : ZMod 80179651801) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = ((11 : ZMod 80179651801) ^ 112 * (11 : ZMod 80179651801) ^ 112) * (11 : ZMod 80179651801) := by rw [pow_succ, pow_add]
          _ = 48747879695 := by rw [factor_3_6]; decide
      have factor_3_8 : (11 : ZMod 80179651801) ^ 450 = 35136531697 := by
        calc
          (11 : ZMod 80179651801) ^ 450 = (11 : ZMod 80179651801) ^ (225 + 225) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 225 * (11 : ZMod 80179651801) ^ 225 := by rw [pow_add]
          _ = 35136531697 := by rw [factor_3_7]; decide
      have factor_3_9 : (11 : ZMod 80179651801) ^ 900 = 59326918592 := by
        calc
          (11 : ZMod 80179651801) ^ 900 = (11 : ZMod 80179651801) ^ (450 + 450) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 450 * (11 : ZMod 80179651801) ^ 450 := by rw [pow_add]
          _ = 59326918592 := by rw [factor_3_8]; decide
      have factor_3_10 : (11 : ZMod 80179651801) ^ 1800 = 38829744222 := by
        calc
          (11 : ZMod 80179651801) ^ 1800 = (11 : ZMod 80179651801) ^ (900 + 900) :=
            congrArg (fun n : ℕ => (11 : ZMod 80179651801) ^ n) (by norm_num)
          _ = (11 : ZMod 80179651801) ^ 900 * (11 : ZMod 80179651801) ^ 900 := by rw [pow_add]
          _ = 38829744222 := by rw [factor_3_9]; decide
      change (11 : ZMod 80179651801) ^ 1800 ≠ 1
      rw [factor_3_10]
      decide

#print axioms prime_lucas_80179651801

end TotientTailPeriodKiller
end Erdos249257
