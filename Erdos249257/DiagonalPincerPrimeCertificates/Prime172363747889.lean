import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime10772734243

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_172363747889 : Nat.Prime 172363747889 := by
  apply lucas_primality 172363747889 (3 : ZMod 172363747889)
  ·
      have fermat_0 : (3 : ZMod 172363747889) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 172363747889) ^ 2 = 9 := by
        calc
          (3 : ZMod 172363747889) ^ 2 = (3 : ZMod 172363747889) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 1 * (3 : ZMod 172363747889) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 172363747889) ^ 5 = 243 := by
        calc
          (3 : ZMod 172363747889) ^ 5 = (3 : ZMod 172363747889) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 2 * (3 : ZMod 172363747889) ^ 2) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 172363747889) ^ 10 = 59049 := by
        calc
          (3 : ZMod 172363747889) ^ 10 = (3 : ZMod 172363747889) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 5 * (3 : ZMod 172363747889) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 172363747889) ^ 20 = 3486784401 := by
        calc
          (3 : ZMod 172363747889) ^ 20 = (3 : ZMod 172363747889) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 10 * (3 : ZMod 172363747889) ^ 10 := by rw [pow_add]
          _ = 3486784401 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 172363747889) ^ 40 = 50077422364 := by
        calc
          (3 : ZMod 172363747889) ^ 40 = (3 : ZMod 172363747889) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 20 * (3 : ZMod 172363747889) ^ 20 := by rw [pow_add]
          _ = 50077422364 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 172363747889) ^ 80 = 43592540406 := by
        calc
          (3 : ZMod 172363747889) ^ 80 = (3 : ZMod 172363747889) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 40 * (3 : ZMod 172363747889) ^ 40 := by rw [pow_add]
          _ = 43592540406 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 172363747889) ^ 160 = 81361063314 := by
        calc
          (3 : ZMod 172363747889) ^ 160 = (3 : ZMod 172363747889) ^ (80 + 80) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 80 * (3 : ZMod 172363747889) ^ 80 := by rw [pow_add]
          _ = 81361063314 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 172363747889) ^ 321 = 147006099546 := by
        calc
          (3 : ZMod 172363747889) ^ 321 = (3 : ZMod 172363747889) ^ (160 + 160 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 160 * (3 : ZMod 172363747889) ^ 160) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 147006099546 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 172363747889) ^ 642 = 126568882455 := by
        calc
          (3 : ZMod 172363747889) ^ 642 = (3 : ZMod 172363747889) ^ (321 + 321) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 321 * (3 : ZMod 172363747889) ^ 321 := by rw [pow_add]
          _ = 126568882455 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 172363747889) ^ 1284 = 8868454921 := by
        calc
          (3 : ZMod 172363747889) ^ 1284 = (3 : ZMod 172363747889) ^ (642 + 642) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 642 * (3 : ZMod 172363747889) ^ 642 := by rw [pow_add]
          _ = 8868454921 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 172363747889) ^ 2568 = 16477369185 := by
        calc
          (3 : ZMod 172363747889) ^ 2568 = (3 : ZMod 172363747889) ^ (1284 + 1284) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 1284 * (3 : ZMod 172363747889) ^ 1284 := by rw [pow_add]
          _ = 16477369185 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 172363747889) ^ 5136 = 67143438042 := by
        calc
          (3 : ZMod 172363747889) ^ 5136 = (3 : ZMod 172363747889) ^ (2568 + 2568) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 2568 * (3 : ZMod 172363747889) ^ 2568 := by rw [pow_add]
          _ = 67143438042 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 172363747889) ^ 10273 = 40918988414 := by
        calc
          (3 : ZMod 172363747889) ^ 10273 = (3 : ZMod 172363747889) ^ (5136 + 5136 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 5136 * (3 : ZMod 172363747889) ^ 5136) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 40918988414 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 172363747889) ^ 20547 = 77116373655 := by
        calc
          (3 : ZMod 172363747889) ^ 20547 = (3 : ZMod 172363747889) ^ (10273 + 10273 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 10273 * (3 : ZMod 172363747889) ^ 10273) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 77116373655 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 172363747889) ^ 41094 = 20735386559 := by
        calc
          (3 : ZMod 172363747889) ^ 41094 = (3 : ZMod 172363747889) ^ (20547 + 20547) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 20547 * (3 : ZMod 172363747889) ^ 20547 := by rw [pow_add]
          _ = 20735386559 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 172363747889) ^ 82189 = 127340454554 := by
        calc
          (3 : ZMod 172363747889) ^ 82189 = (3 : ZMod 172363747889) ^ (41094 + 41094 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 41094 * (3 : ZMod 172363747889) ^ 41094) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 127340454554 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 172363747889) ^ 164378 = 169858685123 := by
        calc
          (3 : ZMod 172363747889) ^ 164378 = (3 : ZMod 172363747889) ^ (82189 + 82189) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 82189 * (3 : ZMod 172363747889) ^ 82189 := by rw [pow_add]
          _ = 169858685123 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 172363747889) ^ 328757 = 143343889867 := by
        calc
          (3 : ZMod 172363747889) ^ 328757 = (3 : ZMod 172363747889) ^ (164378 + 164378 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 164378 * (3 : ZMod 172363747889) ^ 164378) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 143343889867 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 172363747889) ^ 657515 = 147005004546 := by
        calc
          (3 : ZMod 172363747889) ^ 657515 = (3 : ZMod 172363747889) ^ (328757 + 328757 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 328757 * (3 : ZMod 172363747889) ^ 328757) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 147005004546 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 172363747889) ^ 1315031 = 30233111967 := by
        calc
          (3 : ZMod 172363747889) ^ 1315031 = (3 : ZMod 172363747889) ^ (657515 + 657515 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 657515 * (3 : ZMod 172363747889) ^ 657515) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 30233111967 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 172363747889) ^ 2630062 = 91585144156 := by
        calc
          (3 : ZMod 172363747889) ^ 2630062 = (3 : ZMod 172363747889) ^ (1315031 + 1315031) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 1315031 * (3 : ZMod 172363747889) ^ 1315031 := by rw [pow_add]
          _ = 91585144156 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 172363747889) ^ 5260124 = 7904123863 := by
        calc
          (3 : ZMod 172363747889) ^ 5260124 = (3 : ZMod 172363747889) ^ (2630062 + 2630062) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 2630062 * (3 : ZMod 172363747889) ^ 2630062 := by rw [pow_add]
          _ = 7904123863 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 172363747889) ^ 10520248 = 42754173967 := by
        calc
          (3 : ZMod 172363747889) ^ 10520248 = (3 : ZMod 172363747889) ^ (5260124 + 5260124) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 5260124 * (3 : ZMod 172363747889) ^ 5260124 := by rw [pow_add]
          _ = 42754173967 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 172363747889) ^ 21040496 = 83734365344 := by
        calc
          (3 : ZMod 172363747889) ^ 21040496 = (3 : ZMod 172363747889) ^ (10520248 + 10520248) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 10520248 * (3 : ZMod 172363747889) ^ 10520248 := by rw [pow_add]
          _ = 83734365344 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 172363747889) ^ 42080993 = 119858772167 := by
        calc
          (3 : ZMod 172363747889) ^ 42080993 = (3 : ZMod 172363747889) ^ (21040496 + 21040496 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 21040496 * (3 : ZMod 172363747889) ^ 21040496) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 119858772167 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 172363747889) ^ 84161986 = 36117930974 := by
        calc
          (3 : ZMod 172363747889) ^ 84161986 = (3 : ZMod 172363747889) ^ (42080993 + 42080993) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 42080993 * (3 : ZMod 172363747889) ^ 42080993 := by rw [pow_add]
          _ = 36117930974 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 172363747889) ^ 168323972 = 105291088294 := by
        calc
          (3 : ZMod 172363747889) ^ 168323972 = (3 : ZMod 172363747889) ^ (84161986 + 84161986) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 84161986 * (3 : ZMod 172363747889) ^ 84161986 := by rw [pow_add]
          _ = 105291088294 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 172363747889) ^ 336647945 = 165209623103 := by
        calc
          (3 : ZMod 172363747889) ^ 336647945 = (3 : ZMod 172363747889) ^ (168323972 + 168323972 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 168323972 * (3 : ZMod 172363747889) ^ 168323972) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 165209623103 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 172363747889) ^ 673295890 = 100350059474 := by
        calc
          (3 : ZMod 172363747889) ^ 673295890 = (3 : ZMod 172363747889) ^ (336647945 + 336647945) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 336647945 * (3 : ZMod 172363747889) ^ 336647945 := by rw [pow_add]
          _ = 100350059474 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 172363747889) ^ 1346591780 = 101627939572 := by
        calc
          (3 : ZMod 172363747889) ^ 1346591780 = (3 : ZMod 172363747889) ^ (673295890 + 673295890) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 673295890 * (3 : ZMod 172363747889) ^ 673295890 := by rw [pow_add]
          _ = 101627939572 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 172363747889) ^ 2693183560 = 162290275757 := by
        calc
          (3 : ZMod 172363747889) ^ 2693183560 = (3 : ZMod 172363747889) ^ (1346591780 + 1346591780) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 1346591780 * (3 : ZMod 172363747889) ^ 1346591780 := by rw [pow_add]
          _ = 162290275757 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 172363747889) ^ 5386367121 = 121245804285 := by
        calc
          (3 : ZMod 172363747889) ^ 5386367121 = (3 : ZMod 172363747889) ^ (2693183560 + 2693183560 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 2693183560 * (3 : ZMod 172363747889) ^ 2693183560) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 121245804285 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 172363747889) ^ 10772734243 = 87273904278 := by
        calc
          (3 : ZMod 172363747889) ^ 10772734243 = (3 : ZMod 172363747889) ^ (5386367121 + 5386367121 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 5386367121 * (3 : ZMod 172363747889) ^ 5386367121) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 87273904278 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 172363747889) ^ 21545468486 = 73857274063 := by
        calc
          (3 : ZMod 172363747889) ^ 21545468486 = (3 : ZMod 172363747889) ^ (10772734243 + 10772734243) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 10772734243 * (3 : ZMod 172363747889) ^ 10772734243 := by rw [pow_add]
          _ = 73857274063 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 172363747889) ^ 43090936972 = 119207689824 := by
        calc
          (3 : ZMod 172363747889) ^ 43090936972 = (3 : ZMod 172363747889) ^ (21545468486 + 21545468486) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 21545468486 * (3 : ZMod 172363747889) ^ 21545468486 := by rw [pow_add]
          _ = 119207689824 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 172363747889) ^ 86181873944 = 172363747888 := by
        calc
          (3 : ZMod 172363747889) ^ 86181873944 = (3 : ZMod 172363747889) ^ (43090936972 + 43090936972) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 43090936972 * (3 : ZMod 172363747889) ^ 43090936972 := by rw [pow_add]
          _ = 172363747888 := by rw [fermat_35]; decide
      have fermat_37 : (3 : ZMod 172363747889) ^ 172363747888 = 1 := by
        calc
          (3 : ZMod 172363747889) ^ 172363747888 = (3 : ZMod 172363747889) ^ (86181873944 + 86181873944) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 86181873944 * (3 : ZMod 172363747889) ^ 86181873944 := by rw [pow_add]
          _ = 1 := by rw [fermat_36]; decide
      simpa using fermat_37
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (10772734243, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (10772734243, 1)] : List FactorBlock).map factorBlockValue).prod = 172363747889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_10772734243) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 172363747889) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 172363747889) ^ 2 = 9 := by
        calc
          (3 : ZMod 172363747889) ^ 2 = (3 : ZMod 172363747889) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 1 * (3 : ZMod 172363747889) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 172363747889) ^ 5 = 243 := by
        calc
          (3 : ZMod 172363747889) ^ 5 = (3 : ZMod 172363747889) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 2 * (3 : ZMod 172363747889) ^ 2) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 172363747889) ^ 10 = 59049 := by
        calc
          (3 : ZMod 172363747889) ^ 10 = (3 : ZMod 172363747889) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 5 * (3 : ZMod 172363747889) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 172363747889) ^ 20 = 3486784401 := by
        calc
          (3 : ZMod 172363747889) ^ 20 = (3 : ZMod 172363747889) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 10 * (3 : ZMod 172363747889) ^ 10 := by rw [pow_add]
          _ = 3486784401 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 172363747889) ^ 40 = 50077422364 := by
        calc
          (3 : ZMod 172363747889) ^ 40 = (3 : ZMod 172363747889) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 20 * (3 : ZMod 172363747889) ^ 20 := by rw [pow_add]
          _ = 50077422364 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 172363747889) ^ 80 = 43592540406 := by
        calc
          (3 : ZMod 172363747889) ^ 80 = (3 : ZMod 172363747889) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 40 * (3 : ZMod 172363747889) ^ 40 := by rw [pow_add]
          _ = 43592540406 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 172363747889) ^ 160 = 81361063314 := by
        calc
          (3 : ZMod 172363747889) ^ 160 = (3 : ZMod 172363747889) ^ (80 + 80) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 80 * (3 : ZMod 172363747889) ^ 80 := by rw [pow_add]
          _ = 81361063314 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 172363747889) ^ 321 = 147006099546 := by
        calc
          (3 : ZMod 172363747889) ^ 321 = (3 : ZMod 172363747889) ^ (160 + 160 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 160 * (3 : ZMod 172363747889) ^ 160) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 147006099546 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 172363747889) ^ 642 = 126568882455 := by
        calc
          (3 : ZMod 172363747889) ^ 642 = (3 : ZMod 172363747889) ^ (321 + 321) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 321 * (3 : ZMod 172363747889) ^ 321 := by rw [pow_add]
          _ = 126568882455 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 172363747889) ^ 1284 = 8868454921 := by
        calc
          (3 : ZMod 172363747889) ^ 1284 = (3 : ZMod 172363747889) ^ (642 + 642) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 642 * (3 : ZMod 172363747889) ^ 642 := by rw [pow_add]
          _ = 8868454921 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 172363747889) ^ 2568 = 16477369185 := by
        calc
          (3 : ZMod 172363747889) ^ 2568 = (3 : ZMod 172363747889) ^ (1284 + 1284) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 1284 * (3 : ZMod 172363747889) ^ 1284 := by rw [pow_add]
          _ = 16477369185 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 172363747889) ^ 5136 = 67143438042 := by
        calc
          (3 : ZMod 172363747889) ^ 5136 = (3 : ZMod 172363747889) ^ (2568 + 2568) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 2568 * (3 : ZMod 172363747889) ^ 2568 := by rw [pow_add]
          _ = 67143438042 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 172363747889) ^ 10273 = 40918988414 := by
        calc
          (3 : ZMod 172363747889) ^ 10273 = (3 : ZMod 172363747889) ^ (5136 + 5136 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 5136 * (3 : ZMod 172363747889) ^ 5136) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 40918988414 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 172363747889) ^ 20547 = 77116373655 := by
        calc
          (3 : ZMod 172363747889) ^ 20547 = (3 : ZMod 172363747889) ^ (10273 + 10273 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 10273 * (3 : ZMod 172363747889) ^ 10273) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 77116373655 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 172363747889) ^ 41094 = 20735386559 := by
        calc
          (3 : ZMod 172363747889) ^ 41094 = (3 : ZMod 172363747889) ^ (20547 + 20547) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 20547 * (3 : ZMod 172363747889) ^ 20547 := by rw [pow_add]
          _ = 20735386559 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 172363747889) ^ 82189 = 127340454554 := by
        calc
          (3 : ZMod 172363747889) ^ 82189 = (3 : ZMod 172363747889) ^ (41094 + 41094 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 41094 * (3 : ZMod 172363747889) ^ 41094) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 127340454554 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 172363747889) ^ 164378 = 169858685123 := by
        calc
          (3 : ZMod 172363747889) ^ 164378 = (3 : ZMod 172363747889) ^ (82189 + 82189) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 82189 * (3 : ZMod 172363747889) ^ 82189 := by rw [pow_add]
          _ = 169858685123 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 172363747889) ^ 328757 = 143343889867 := by
        calc
          (3 : ZMod 172363747889) ^ 328757 = (3 : ZMod 172363747889) ^ (164378 + 164378 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 164378 * (3 : ZMod 172363747889) ^ 164378) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 143343889867 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 172363747889) ^ 657515 = 147005004546 := by
        calc
          (3 : ZMod 172363747889) ^ 657515 = (3 : ZMod 172363747889) ^ (328757 + 328757 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 328757 * (3 : ZMod 172363747889) ^ 328757) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 147005004546 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 172363747889) ^ 1315031 = 30233111967 := by
        calc
          (3 : ZMod 172363747889) ^ 1315031 = (3 : ZMod 172363747889) ^ (657515 + 657515 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 657515 * (3 : ZMod 172363747889) ^ 657515) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 30233111967 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 172363747889) ^ 2630062 = 91585144156 := by
        calc
          (3 : ZMod 172363747889) ^ 2630062 = (3 : ZMod 172363747889) ^ (1315031 + 1315031) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 1315031 * (3 : ZMod 172363747889) ^ 1315031 := by rw [pow_add]
          _ = 91585144156 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 172363747889) ^ 5260124 = 7904123863 := by
        calc
          (3 : ZMod 172363747889) ^ 5260124 = (3 : ZMod 172363747889) ^ (2630062 + 2630062) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 2630062 * (3 : ZMod 172363747889) ^ 2630062 := by rw [pow_add]
          _ = 7904123863 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 172363747889) ^ 10520248 = 42754173967 := by
        calc
          (3 : ZMod 172363747889) ^ 10520248 = (3 : ZMod 172363747889) ^ (5260124 + 5260124) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 5260124 * (3 : ZMod 172363747889) ^ 5260124 := by rw [pow_add]
          _ = 42754173967 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 172363747889) ^ 21040496 = 83734365344 := by
        calc
          (3 : ZMod 172363747889) ^ 21040496 = (3 : ZMod 172363747889) ^ (10520248 + 10520248) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 10520248 * (3 : ZMod 172363747889) ^ 10520248 := by rw [pow_add]
          _ = 83734365344 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 172363747889) ^ 42080993 = 119858772167 := by
        calc
          (3 : ZMod 172363747889) ^ 42080993 = (3 : ZMod 172363747889) ^ (21040496 + 21040496 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 21040496 * (3 : ZMod 172363747889) ^ 21040496) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 119858772167 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 172363747889) ^ 84161986 = 36117930974 := by
        calc
          (3 : ZMod 172363747889) ^ 84161986 = (3 : ZMod 172363747889) ^ (42080993 + 42080993) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 42080993 * (3 : ZMod 172363747889) ^ 42080993 := by rw [pow_add]
          _ = 36117930974 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 172363747889) ^ 168323972 = 105291088294 := by
        calc
          (3 : ZMod 172363747889) ^ 168323972 = (3 : ZMod 172363747889) ^ (84161986 + 84161986) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 84161986 * (3 : ZMod 172363747889) ^ 84161986 := by rw [pow_add]
          _ = 105291088294 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 172363747889) ^ 336647945 = 165209623103 := by
        calc
          (3 : ZMod 172363747889) ^ 336647945 = (3 : ZMod 172363747889) ^ (168323972 + 168323972 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 168323972 * (3 : ZMod 172363747889) ^ 168323972) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 165209623103 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 172363747889) ^ 673295890 = 100350059474 := by
        calc
          (3 : ZMod 172363747889) ^ 673295890 = (3 : ZMod 172363747889) ^ (336647945 + 336647945) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 336647945 * (3 : ZMod 172363747889) ^ 336647945 := by rw [pow_add]
          _ = 100350059474 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 172363747889) ^ 1346591780 = 101627939572 := by
        calc
          (3 : ZMod 172363747889) ^ 1346591780 = (3 : ZMod 172363747889) ^ (673295890 + 673295890) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 673295890 * (3 : ZMod 172363747889) ^ 673295890 := by rw [pow_add]
          _ = 101627939572 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 172363747889) ^ 2693183560 = 162290275757 := by
        calc
          (3 : ZMod 172363747889) ^ 2693183560 = (3 : ZMod 172363747889) ^ (1346591780 + 1346591780) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 1346591780 * (3 : ZMod 172363747889) ^ 1346591780 := by rw [pow_add]
          _ = 162290275757 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 172363747889) ^ 5386367121 = 121245804285 := by
        calc
          (3 : ZMod 172363747889) ^ 5386367121 = (3 : ZMod 172363747889) ^ (2693183560 + 2693183560 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 2693183560 * (3 : ZMod 172363747889) ^ 2693183560) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 121245804285 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 172363747889) ^ 10772734243 = 87273904278 := by
        calc
          (3 : ZMod 172363747889) ^ 10772734243 = (3 : ZMod 172363747889) ^ (5386367121 + 5386367121 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = ((3 : ZMod 172363747889) ^ 5386367121 * (3 : ZMod 172363747889) ^ 5386367121) * (3 : ZMod 172363747889) := by rw [pow_succ, pow_add]
          _ = 87273904278 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 172363747889) ^ 21545468486 = 73857274063 := by
        calc
          (3 : ZMod 172363747889) ^ 21545468486 = (3 : ZMod 172363747889) ^ (10772734243 + 10772734243) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 10772734243 * (3 : ZMod 172363747889) ^ 10772734243 := by rw [pow_add]
          _ = 73857274063 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 172363747889) ^ 43090936972 = 119207689824 := by
        calc
          (3 : ZMod 172363747889) ^ 43090936972 = (3 : ZMod 172363747889) ^ (21545468486 + 21545468486) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 21545468486 * (3 : ZMod 172363747889) ^ 21545468486 := by rw [pow_add]
          _ = 119207689824 := by rw [factor_0_34]; decide
      have factor_0_36 : (3 : ZMod 172363747889) ^ 86181873944 = 172363747888 := by
        calc
          (3 : ZMod 172363747889) ^ 86181873944 = (3 : ZMod 172363747889) ^ (43090936972 + 43090936972) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 43090936972 * (3 : ZMod 172363747889) ^ 43090936972 := by rw [pow_add]
          _ = 172363747888 := by rw [factor_0_35]; decide
      change (3 : ZMod 172363747889) ^ 86181873944 ≠ 1
      rw [factor_0_36]
      decide
    ·
      have factor_1_0 : (3 : ZMod 172363747889) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 172363747889) ^ 2 = 9 := by
        calc
          (3 : ZMod 172363747889) ^ 2 = (3 : ZMod 172363747889) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 1 * (3 : ZMod 172363747889) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 172363747889) ^ 4 = 81 := by
        calc
          (3 : ZMod 172363747889) ^ 4 = (3 : ZMod 172363747889) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 2 * (3 : ZMod 172363747889) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 172363747889) ^ 8 = 6561 := by
        calc
          (3 : ZMod 172363747889) ^ 8 = (3 : ZMod 172363747889) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 4 * (3 : ZMod 172363747889) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 172363747889) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 172363747889) ^ 16 = (3 : ZMod 172363747889) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 172363747889) ^ n) (by norm_num)
          _ = (3 : ZMod 172363747889) ^ 8 * (3 : ZMod 172363747889) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_1_3]; decide
      change (3 : ZMod 172363747889) ^ 16 ≠ 1
      rw [factor_1_4]
      decide

#print axioms prime_lucas_172363747889

end TotientTailPeriodKiller
end Erdos249257
