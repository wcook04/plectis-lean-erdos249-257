import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime914622451

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_9146224511 : Nat.Prime 9146224511 := by
  apply lucas_primality 9146224511 (7 : ZMod 9146224511)
  ·
      have fermat_0 : (7 : ZMod 9146224511) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 9146224511) ^ 2 = 49 := by
        calc
          (7 : ZMod 9146224511) ^ 2 = (7 : ZMod 9146224511) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 1 * (7 : ZMod 9146224511) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 9146224511) ^ 4 = 2401 := by
        calc
          (7 : ZMod 9146224511) ^ 4 = (7 : ZMod 9146224511) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 2 * (7 : ZMod 9146224511) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 9146224511) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 9146224511) ^ 8 = (7 : ZMod 9146224511) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 4 * (7 : ZMod 9146224511) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 9146224511) ^ 17 = 5439774433 := by
        calc
          (7 : ZMod 9146224511) ^ 17 = (7 : ZMod 9146224511) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 8 * (7 : ZMod 9146224511) ^ 8) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 5439774433 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 9146224511) ^ 34 = 548874643 := by
        calc
          (7 : ZMod 9146224511) ^ 34 = (7 : ZMod 9146224511) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 17 * (7 : ZMod 9146224511) ^ 17 := by rw [pow_add]
          _ = 548874643 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 9146224511) ^ 68 = 361578399 := by
        calc
          (7 : ZMod 9146224511) ^ 68 = (7 : ZMod 9146224511) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 34 * (7 : ZMod 9146224511) ^ 34 := by rw [pow_add]
          _ = 361578399 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 9146224511) ^ 136 = 6718468835 := by
        calc
          (7 : ZMod 9146224511) ^ 136 = (7 : ZMod 9146224511) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 68 * (7 : ZMod 9146224511) ^ 68 := by rw [pow_add]
          _ = 6718468835 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 9146224511) ^ 272 = 6959584870 := by
        calc
          (7 : ZMod 9146224511) ^ 272 = (7 : ZMod 9146224511) ^ (136 + 136) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 136 * (7 : ZMod 9146224511) ^ 136 := by rw [pow_add]
          _ = 6959584870 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 9146224511) ^ 545 = 1950955764 := by
        calc
          (7 : ZMod 9146224511) ^ 545 = (7 : ZMod 9146224511) ^ (272 + 272 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 272 * (7 : ZMod 9146224511) ^ 272) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 1950955764 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 9146224511) ^ 1090 = 8300070158 := by
        calc
          (7 : ZMod 9146224511) ^ 1090 = (7 : ZMod 9146224511) ^ (545 + 545) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 545 * (7 : ZMod 9146224511) ^ 545 := by rw [pow_add]
          _ = 8300070158 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 9146224511) ^ 2180 = 5858417206 := by
        calc
          (7 : ZMod 9146224511) ^ 2180 = (7 : ZMod 9146224511) ^ (1090 + 1090) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 1090 * (7 : ZMod 9146224511) ^ 1090 := by rw [pow_add]
          _ = 5858417206 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 9146224511) ^ 4361 = 4205496644 := by
        calc
          (7 : ZMod 9146224511) ^ 4361 = (7 : ZMod 9146224511) ^ (2180 + 2180 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 2180 * (7 : ZMod 9146224511) ^ 2180) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 4205496644 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 9146224511) ^ 8722 = 1687383619 := by
        calc
          (7 : ZMod 9146224511) ^ 8722 = (7 : ZMod 9146224511) ^ (4361 + 4361) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 4361 * (7 : ZMod 9146224511) ^ 4361 := by rw [pow_add]
          _ = 1687383619 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 9146224511) ^ 17445 = 3490847495 := by
        calc
          (7 : ZMod 9146224511) ^ 17445 = (7 : ZMod 9146224511) ^ (8722 + 8722 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 8722 * (7 : ZMod 9146224511) ^ 8722) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 3490847495 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 9146224511) ^ 34890 = 3630802604 := by
        calc
          (7 : ZMod 9146224511) ^ 34890 = (7 : ZMod 9146224511) ^ (17445 + 17445) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 17445 * (7 : ZMod 9146224511) ^ 17445 := by rw [pow_add]
          _ = 3630802604 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 9146224511) ^ 69780 = 3429163591 := by
        calc
          (7 : ZMod 9146224511) ^ 69780 = (7 : ZMod 9146224511) ^ (34890 + 34890) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 34890 * (7 : ZMod 9146224511) ^ 34890 := by rw [pow_add]
          _ = 3429163591 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 9146224511) ^ 139560 = 5112941161 := by
        calc
          (7 : ZMod 9146224511) ^ 139560 = (7 : ZMod 9146224511) ^ (69780 + 69780) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 69780 * (7 : ZMod 9146224511) ^ 69780 := by rw [pow_add]
          _ = 5112941161 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 9146224511) ^ 279120 = 205508170 := by
        calc
          (7 : ZMod 9146224511) ^ 279120 = (7 : ZMod 9146224511) ^ (139560 + 139560) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 139560 * (7 : ZMod 9146224511) ^ 139560 := by rw [pow_add]
          _ = 205508170 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 9146224511) ^ 558241 = 2297062589 := by
        calc
          (7 : ZMod 9146224511) ^ 558241 = (7 : ZMod 9146224511) ^ (279120 + 279120 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 279120 * (7 : ZMod 9146224511) ^ 279120) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 2297062589 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 9146224511) ^ 1116482 = 5089125780 := by
        calc
          (7 : ZMod 9146224511) ^ 1116482 = (7 : ZMod 9146224511) ^ (558241 + 558241) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 558241 * (7 : ZMod 9146224511) ^ 558241 := by rw [pow_add]
          _ = 5089125780 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 9146224511) ^ 2232964 = 4780857134 := by
        calc
          (7 : ZMod 9146224511) ^ 2232964 = (7 : ZMod 9146224511) ^ (1116482 + 1116482) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 1116482 * (7 : ZMod 9146224511) ^ 1116482 := by rw [pow_add]
          _ = 4780857134 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 9146224511) ^ 4465929 = 86979300 := by
        calc
          (7 : ZMod 9146224511) ^ 4465929 = (7 : ZMod 9146224511) ^ (2232964 + 2232964 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 2232964 * (7 : ZMod 9146224511) ^ 2232964) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 86979300 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 9146224511) ^ 8931859 = 7202676125 := by
        calc
          (7 : ZMod 9146224511) ^ 8931859 = (7 : ZMod 9146224511) ^ (4465929 + 4465929 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 4465929 * (7 : ZMod 9146224511) ^ 4465929) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 7202676125 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 9146224511) ^ 17863719 = 7123644488 := by
        calc
          (7 : ZMod 9146224511) ^ 17863719 = (7 : ZMod 9146224511) ^ (8931859 + 8931859 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 8931859 * (7 : ZMod 9146224511) ^ 8931859) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 7123644488 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 9146224511) ^ 35727439 = 3120392098 := by
        calc
          (7 : ZMod 9146224511) ^ 35727439 = (7 : ZMod 9146224511) ^ (17863719 + 17863719 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 17863719 * (7 : ZMod 9146224511) ^ 17863719) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 3120392098 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 9146224511) ^ 71454878 = 2379127730 := by
        calc
          (7 : ZMod 9146224511) ^ 71454878 = (7 : ZMod 9146224511) ^ (35727439 + 35727439) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 35727439 * (7 : ZMod 9146224511) ^ 35727439 := by rw [pow_add]
          _ = 2379127730 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 9146224511) ^ 142909757 = 4409533460 := by
        calc
          (7 : ZMod 9146224511) ^ 142909757 = (7 : ZMod 9146224511) ^ (71454878 + 71454878 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 71454878 * (7 : ZMod 9146224511) ^ 71454878) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 4409533460 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 9146224511) ^ 285819515 = 370023866 := by
        calc
          (7 : ZMod 9146224511) ^ 285819515 = (7 : ZMod 9146224511) ^ (142909757 + 142909757 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 142909757 * (7 : ZMod 9146224511) ^ 142909757) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 370023866 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 9146224511) ^ 571639031 = 1046167802 := by
        calc
          (7 : ZMod 9146224511) ^ 571639031 = (7 : ZMod 9146224511) ^ (285819515 + 285819515 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 285819515 * (7 : ZMod 9146224511) ^ 285819515) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 1046167802 := by rw [fermat_28]; decide
      have fermat_30 : (7 : ZMod 9146224511) ^ 1143278063 = 5772702677 := by
        calc
          (7 : ZMod 9146224511) ^ 1143278063 = (7 : ZMod 9146224511) ^ (571639031 + 571639031 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 571639031 * (7 : ZMod 9146224511) ^ 571639031) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 5772702677 := by rw [fermat_29]; decide
      have fermat_31 : (7 : ZMod 9146224511) ^ 2286556127 = 9008864652 := by
        calc
          (7 : ZMod 9146224511) ^ 2286556127 = (7 : ZMod 9146224511) ^ (1143278063 + 1143278063 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 1143278063 * (7 : ZMod 9146224511) ^ 1143278063) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 9008864652 := by rw [fermat_30]; decide
      have fermat_32 : (7 : ZMod 9146224511) ^ 4573112255 = 9146224510 := by
        calc
          (7 : ZMod 9146224511) ^ 4573112255 = (7 : ZMod 9146224511) ^ (2286556127 + 2286556127 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 2286556127 * (7 : ZMod 9146224511) ^ 2286556127) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 9146224510 := by rw [fermat_31]; decide
      have fermat_33 : (7 : ZMod 9146224511) ^ 9146224510 = 1 := by
        calc
          (7 : ZMod 9146224511) ^ 9146224510 = (7 : ZMod 9146224511) ^ (4573112255 + 4573112255) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 4573112255 * (7 : ZMod 9146224511) ^ 4573112255 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (914622451, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (914622451, 1)] : List FactorBlock).map factorBlockValue).prod = 9146224511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_914622451) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 9146224511) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 9146224511) ^ 2 = 49 := by
        calc
          (7 : ZMod 9146224511) ^ 2 = (7 : ZMod 9146224511) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 1 * (7 : ZMod 9146224511) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 9146224511) ^ 4 = 2401 := by
        calc
          (7 : ZMod 9146224511) ^ 4 = (7 : ZMod 9146224511) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 2 * (7 : ZMod 9146224511) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 9146224511) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 9146224511) ^ 8 = (7 : ZMod 9146224511) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 4 * (7 : ZMod 9146224511) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 9146224511) ^ 17 = 5439774433 := by
        calc
          (7 : ZMod 9146224511) ^ 17 = (7 : ZMod 9146224511) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 8 * (7 : ZMod 9146224511) ^ 8) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 5439774433 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 9146224511) ^ 34 = 548874643 := by
        calc
          (7 : ZMod 9146224511) ^ 34 = (7 : ZMod 9146224511) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 17 * (7 : ZMod 9146224511) ^ 17 := by rw [pow_add]
          _ = 548874643 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 9146224511) ^ 68 = 361578399 := by
        calc
          (7 : ZMod 9146224511) ^ 68 = (7 : ZMod 9146224511) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 34 * (7 : ZMod 9146224511) ^ 34 := by rw [pow_add]
          _ = 361578399 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 9146224511) ^ 136 = 6718468835 := by
        calc
          (7 : ZMod 9146224511) ^ 136 = (7 : ZMod 9146224511) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 68 * (7 : ZMod 9146224511) ^ 68 := by rw [pow_add]
          _ = 6718468835 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 9146224511) ^ 272 = 6959584870 := by
        calc
          (7 : ZMod 9146224511) ^ 272 = (7 : ZMod 9146224511) ^ (136 + 136) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 136 * (7 : ZMod 9146224511) ^ 136 := by rw [pow_add]
          _ = 6959584870 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 9146224511) ^ 545 = 1950955764 := by
        calc
          (7 : ZMod 9146224511) ^ 545 = (7 : ZMod 9146224511) ^ (272 + 272 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 272 * (7 : ZMod 9146224511) ^ 272) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 1950955764 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 9146224511) ^ 1090 = 8300070158 := by
        calc
          (7 : ZMod 9146224511) ^ 1090 = (7 : ZMod 9146224511) ^ (545 + 545) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 545 * (7 : ZMod 9146224511) ^ 545 := by rw [pow_add]
          _ = 8300070158 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 9146224511) ^ 2180 = 5858417206 := by
        calc
          (7 : ZMod 9146224511) ^ 2180 = (7 : ZMod 9146224511) ^ (1090 + 1090) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 1090 * (7 : ZMod 9146224511) ^ 1090 := by rw [pow_add]
          _ = 5858417206 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 9146224511) ^ 4361 = 4205496644 := by
        calc
          (7 : ZMod 9146224511) ^ 4361 = (7 : ZMod 9146224511) ^ (2180 + 2180 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 2180 * (7 : ZMod 9146224511) ^ 2180) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 4205496644 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 9146224511) ^ 8722 = 1687383619 := by
        calc
          (7 : ZMod 9146224511) ^ 8722 = (7 : ZMod 9146224511) ^ (4361 + 4361) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 4361 * (7 : ZMod 9146224511) ^ 4361 := by rw [pow_add]
          _ = 1687383619 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 9146224511) ^ 17445 = 3490847495 := by
        calc
          (7 : ZMod 9146224511) ^ 17445 = (7 : ZMod 9146224511) ^ (8722 + 8722 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 8722 * (7 : ZMod 9146224511) ^ 8722) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 3490847495 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 9146224511) ^ 34890 = 3630802604 := by
        calc
          (7 : ZMod 9146224511) ^ 34890 = (7 : ZMod 9146224511) ^ (17445 + 17445) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 17445 * (7 : ZMod 9146224511) ^ 17445 := by rw [pow_add]
          _ = 3630802604 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 9146224511) ^ 69780 = 3429163591 := by
        calc
          (7 : ZMod 9146224511) ^ 69780 = (7 : ZMod 9146224511) ^ (34890 + 34890) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 34890 * (7 : ZMod 9146224511) ^ 34890 := by rw [pow_add]
          _ = 3429163591 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 9146224511) ^ 139560 = 5112941161 := by
        calc
          (7 : ZMod 9146224511) ^ 139560 = (7 : ZMod 9146224511) ^ (69780 + 69780) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 69780 * (7 : ZMod 9146224511) ^ 69780 := by rw [pow_add]
          _ = 5112941161 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 9146224511) ^ 279120 = 205508170 := by
        calc
          (7 : ZMod 9146224511) ^ 279120 = (7 : ZMod 9146224511) ^ (139560 + 139560) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 139560 * (7 : ZMod 9146224511) ^ 139560 := by rw [pow_add]
          _ = 205508170 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 9146224511) ^ 558241 = 2297062589 := by
        calc
          (7 : ZMod 9146224511) ^ 558241 = (7 : ZMod 9146224511) ^ (279120 + 279120 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 279120 * (7 : ZMod 9146224511) ^ 279120) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 2297062589 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 9146224511) ^ 1116482 = 5089125780 := by
        calc
          (7 : ZMod 9146224511) ^ 1116482 = (7 : ZMod 9146224511) ^ (558241 + 558241) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 558241 * (7 : ZMod 9146224511) ^ 558241 := by rw [pow_add]
          _ = 5089125780 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 9146224511) ^ 2232964 = 4780857134 := by
        calc
          (7 : ZMod 9146224511) ^ 2232964 = (7 : ZMod 9146224511) ^ (1116482 + 1116482) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 1116482 * (7 : ZMod 9146224511) ^ 1116482 := by rw [pow_add]
          _ = 4780857134 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 9146224511) ^ 4465929 = 86979300 := by
        calc
          (7 : ZMod 9146224511) ^ 4465929 = (7 : ZMod 9146224511) ^ (2232964 + 2232964 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 2232964 * (7 : ZMod 9146224511) ^ 2232964) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 86979300 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 9146224511) ^ 8931859 = 7202676125 := by
        calc
          (7 : ZMod 9146224511) ^ 8931859 = (7 : ZMod 9146224511) ^ (4465929 + 4465929 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 4465929 * (7 : ZMod 9146224511) ^ 4465929) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 7202676125 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 9146224511) ^ 17863719 = 7123644488 := by
        calc
          (7 : ZMod 9146224511) ^ 17863719 = (7 : ZMod 9146224511) ^ (8931859 + 8931859 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 8931859 * (7 : ZMod 9146224511) ^ 8931859) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 7123644488 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 9146224511) ^ 35727439 = 3120392098 := by
        calc
          (7 : ZMod 9146224511) ^ 35727439 = (7 : ZMod 9146224511) ^ (17863719 + 17863719 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 17863719 * (7 : ZMod 9146224511) ^ 17863719) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 3120392098 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 9146224511) ^ 71454878 = 2379127730 := by
        calc
          (7 : ZMod 9146224511) ^ 71454878 = (7 : ZMod 9146224511) ^ (35727439 + 35727439) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 35727439 * (7 : ZMod 9146224511) ^ 35727439 := by rw [pow_add]
          _ = 2379127730 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 9146224511) ^ 142909757 = 4409533460 := by
        calc
          (7 : ZMod 9146224511) ^ 142909757 = (7 : ZMod 9146224511) ^ (71454878 + 71454878 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 71454878 * (7 : ZMod 9146224511) ^ 71454878) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 4409533460 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 9146224511) ^ 285819515 = 370023866 := by
        calc
          (7 : ZMod 9146224511) ^ 285819515 = (7 : ZMod 9146224511) ^ (142909757 + 142909757 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 142909757 * (7 : ZMod 9146224511) ^ 142909757) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 370023866 := by rw [factor_0_27]; decide
      have factor_0_29 : (7 : ZMod 9146224511) ^ 571639031 = 1046167802 := by
        calc
          (7 : ZMod 9146224511) ^ 571639031 = (7 : ZMod 9146224511) ^ (285819515 + 285819515 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 285819515 * (7 : ZMod 9146224511) ^ 285819515) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 1046167802 := by rw [factor_0_28]; decide
      have factor_0_30 : (7 : ZMod 9146224511) ^ 1143278063 = 5772702677 := by
        calc
          (7 : ZMod 9146224511) ^ 1143278063 = (7 : ZMod 9146224511) ^ (571639031 + 571639031 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 571639031 * (7 : ZMod 9146224511) ^ 571639031) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 5772702677 := by rw [factor_0_29]; decide
      have factor_0_31 : (7 : ZMod 9146224511) ^ 2286556127 = 9008864652 := by
        calc
          (7 : ZMod 9146224511) ^ 2286556127 = (7 : ZMod 9146224511) ^ (1143278063 + 1143278063 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 1143278063 * (7 : ZMod 9146224511) ^ 1143278063) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 9008864652 := by rw [factor_0_30]; decide
      have factor_0_32 : (7 : ZMod 9146224511) ^ 4573112255 = 9146224510 := by
        calc
          (7 : ZMod 9146224511) ^ 4573112255 = (7 : ZMod 9146224511) ^ (2286556127 + 2286556127 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 2286556127 * (7 : ZMod 9146224511) ^ 2286556127) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 9146224510 := by rw [factor_0_31]; decide
      change (7 : ZMod 9146224511) ^ 4573112255 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (7 : ZMod 9146224511) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 9146224511) ^ 3 = 343 := by
        calc
          (7 : ZMod 9146224511) ^ 3 = (7 : ZMod 9146224511) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 1 * (7 : ZMod 9146224511) ^ 1) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 9146224511) ^ 6 = 117649 := by
        calc
          (7 : ZMod 9146224511) ^ 6 = (7 : ZMod 9146224511) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 3 * (7 : ZMod 9146224511) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 9146224511) ^ 13 = 5426765297 := by
        calc
          (7 : ZMod 9146224511) ^ 13 = (7 : ZMod 9146224511) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 6 * (7 : ZMod 9146224511) ^ 6) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 5426765297 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 9146224511) ^ 27 = 2393854120 := by
        calc
          (7 : ZMod 9146224511) ^ 27 = (7 : ZMod 9146224511) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 13 * (7 : ZMod 9146224511) ^ 13) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 2393854120 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 9146224511) ^ 54 = 3878176287 := by
        calc
          (7 : ZMod 9146224511) ^ 54 = (7 : ZMod 9146224511) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 27 * (7 : ZMod 9146224511) ^ 27 := by rw [pow_add]
          _ = 3878176287 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 9146224511) ^ 109 = 7392417634 := by
        calc
          (7 : ZMod 9146224511) ^ 109 = (7 : ZMod 9146224511) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 54 * (7 : ZMod 9146224511) ^ 54) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 7392417634 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 9146224511) ^ 218 = 8293278327 := by
        calc
          (7 : ZMod 9146224511) ^ 218 = (7 : ZMod 9146224511) ^ (109 + 109) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 109 * (7 : ZMod 9146224511) ^ 109 := by rw [pow_add]
          _ = 8293278327 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 9146224511) ^ 436 = 7729038000 := by
        calc
          (7 : ZMod 9146224511) ^ 436 = (7 : ZMod 9146224511) ^ (218 + 218) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 218 * (7 : ZMod 9146224511) ^ 218 := by rw [pow_add]
          _ = 7729038000 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 9146224511) ^ 872 = 4980989832 := by
        calc
          (7 : ZMod 9146224511) ^ 872 = (7 : ZMod 9146224511) ^ (436 + 436) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 436 * (7 : ZMod 9146224511) ^ 436 := by rw [pow_add]
          _ = 4980989832 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 9146224511) ^ 1744 = 3087074344 := by
        calc
          (7 : ZMod 9146224511) ^ 1744 = (7 : ZMod 9146224511) ^ (872 + 872) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 872 * (7 : ZMod 9146224511) ^ 872 := by rw [pow_add]
          _ = 3087074344 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 9146224511) ^ 3489 = 6516063859 := by
        calc
          (7 : ZMod 9146224511) ^ 3489 = (7 : ZMod 9146224511) ^ (1744 + 1744 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 1744 * (7 : ZMod 9146224511) ^ 1744) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 6516063859 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 9146224511) ^ 6978 = 3117790837 := by
        calc
          (7 : ZMod 9146224511) ^ 6978 = (7 : ZMod 9146224511) ^ (3489 + 3489) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 3489 * (7 : ZMod 9146224511) ^ 3489 := by rw [pow_add]
          _ = 3117790837 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 9146224511) ^ 13956 = 464617785 := by
        calc
          (7 : ZMod 9146224511) ^ 13956 = (7 : ZMod 9146224511) ^ (6978 + 6978) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 6978 * (7 : ZMod 9146224511) ^ 6978 := by rw [pow_add]
          _ = 464617785 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 9146224511) ^ 27912 = 1333560631 := by
        calc
          (7 : ZMod 9146224511) ^ 27912 = (7 : ZMod 9146224511) ^ (13956 + 13956) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 13956 * (7 : ZMod 9146224511) ^ 13956 := by rw [pow_add]
          _ = 1333560631 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 9146224511) ^ 55824 = 1557153709 := by
        calc
          (7 : ZMod 9146224511) ^ 55824 = (7 : ZMod 9146224511) ^ (27912 + 27912) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 27912 * (7 : ZMod 9146224511) ^ 27912 := by rw [pow_add]
          _ = 1557153709 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 9146224511) ^ 111648 = 7618454253 := by
        calc
          (7 : ZMod 9146224511) ^ 111648 = (7 : ZMod 9146224511) ^ (55824 + 55824) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 55824 * (7 : ZMod 9146224511) ^ 55824 := by rw [pow_add]
          _ = 7618454253 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 9146224511) ^ 223296 = 2165940100 := by
        calc
          (7 : ZMod 9146224511) ^ 223296 = (7 : ZMod 9146224511) ^ (111648 + 111648) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 111648 * (7 : ZMod 9146224511) ^ 111648 := by rw [pow_add]
          _ = 2165940100 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 9146224511) ^ 446592 = 4212793916 := by
        calc
          (7 : ZMod 9146224511) ^ 446592 = (7 : ZMod 9146224511) ^ (223296 + 223296) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 223296 * (7 : ZMod 9146224511) ^ 223296 := by rw [pow_add]
          _ = 4212793916 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 9146224511) ^ 893185 = 5980558579 := by
        calc
          (7 : ZMod 9146224511) ^ 893185 = (7 : ZMod 9146224511) ^ (446592 + 446592 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 446592 * (7 : ZMod 9146224511) ^ 446592) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 5980558579 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 9146224511) ^ 1786371 = 5745356519 := by
        calc
          (7 : ZMod 9146224511) ^ 1786371 = (7 : ZMod 9146224511) ^ (893185 + 893185 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 893185 * (7 : ZMod 9146224511) ^ 893185) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 5745356519 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 9146224511) ^ 3572743 = 247460999 := by
        calc
          (7 : ZMod 9146224511) ^ 3572743 = (7 : ZMod 9146224511) ^ (1786371 + 1786371 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 1786371 * (7 : ZMod 9146224511) ^ 1786371) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 247460999 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 9146224511) ^ 7145487 = 2813768482 := by
        calc
          (7 : ZMod 9146224511) ^ 7145487 = (7 : ZMod 9146224511) ^ (3572743 + 3572743 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 3572743 * (7 : ZMod 9146224511) ^ 3572743) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 2813768482 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 9146224511) ^ 14290975 = 3403250221 := by
        calc
          (7 : ZMod 9146224511) ^ 14290975 = (7 : ZMod 9146224511) ^ (7145487 + 7145487 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 7145487 * (7 : ZMod 9146224511) ^ 7145487) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 3403250221 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 9146224511) ^ 28581951 = 8713044307 := by
        calc
          (7 : ZMod 9146224511) ^ 28581951 = (7 : ZMod 9146224511) ^ (14290975 + 14290975 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 14290975 * (7 : ZMod 9146224511) ^ 14290975) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 8713044307 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 9146224511) ^ 57163903 = 8249743165 := by
        calc
          (7 : ZMod 9146224511) ^ 57163903 = (7 : ZMod 9146224511) ^ (28581951 + 28581951 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 28581951 * (7 : ZMod 9146224511) ^ 28581951) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 8249743165 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 9146224511) ^ 114327806 = 1067054650 := by
        calc
          (7 : ZMod 9146224511) ^ 114327806 = (7 : ZMod 9146224511) ^ (57163903 + 57163903) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 57163903 * (7 : ZMod 9146224511) ^ 57163903 := by rw [pow_add]
          _ = 1067054650 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 9146224511) ^ 228655612 = 2465311960 := by
        calc
          (7 : ZMod 9146224511) ^ 228655612 = (7 : ZMod 9146224511) ^ (114327806 + 114327806) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 114327806 * (7 : ZMod 9146224511) ^ 114327806 := by rw [pow_add]
          _ = 2465311960 := by rw [factor_1_26]; decide
      have factor_1_28 : (7 : ZMod 9146224511) ^ 457311225 = 6831545660 := by
        calc
          (7 : ZMod 9146224511) ^ 457311225 = (7 : ZMod 9146224511) ^ (228655612 + 228655612 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 228655612 * (7 : ZMod 9146224511) ^ 228655612) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 6831545660 := by rw [factor_1_27]; decide
      have factor_1_29 : (7 : ZMod 9146224511) ^ 914622451 = 2672825302 := by
        calc
          (7 : ZMod 9146224511) ^ 914622451 = (7 : ZMod 9146224511) ^ (457311225 + 457311225 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 457311225 * (7 : ZMod 9146224511) ^ 457311225) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 2672825302 := by rw [factor_1_28]; decide
      have factor_1_30 : (7 : ZMod 9146224511) ^ 1829244902 = 5972428580 := by
        calc
          (7 : ZMod 9146224511) ^ 1829244902 = (7 : ZMod 9146224511) ^ (914622451 + 914622451) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 914622451 * (7 : ZMod 9146224511) ^ 914622451 := by rw [pow_add]
          _ = 5972428580 := by rw [factor_1_29]; decide
      change (7 : ZMod 9146224511) ^ 1829244902 ≠ 1
      rw [factor_1_30]
      decide
    ·
      have factor_2_0 : (7 : ZMod 9146224511) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 9146224511) ^ 2 = 49 := by
        calc
          (7 : ZMod 9146224511) ^ 2 = (7 : ZMod 9146224511) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 1 * (7 : ZMod 9146224511) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 9146224511) ^ 5 = 16807 := by
        calc
          (7 : ZMod 9146224511) ^ 5 = (7 : ZMod 9146224511) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = ((7 : ZMod 9146224511) ^ 2 * (7 : ZMod 9146224511) ^ 2) * (7 : ZMod 9146224511) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 9146224511) ^ 10 = 282475249 := by
        calc
          (7 : ZMod 9146224511) ^ 10 = (7 : ZMod 9146224511) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 9146224511) ^ n) (by norm_num)
          _ = (7 : ZMod 9146224511) ^ 5 * (7 : ZMod 9146224511) ^ 5 := by rw [pow_add]
          _ = 282475249 := by rw [factor_2_2]; decide
      change (7 : ZMod 9146224511) ^ 10 ≠ 1
      rw [factor_2_3]
      decide

#print axioms prime_lucas_9146224511

end TotientTailPeriodKiller
end Erdos249257
