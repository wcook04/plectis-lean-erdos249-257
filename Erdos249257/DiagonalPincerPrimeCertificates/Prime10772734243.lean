import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1795455707

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_10772734243 : Nat.Prime 10772734243 := by
  apply lucas_primality 10772734243 (2 : ZMod 10772734243)
  ·
      have fermat_0 : (2 : ZMod 10772734243) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 10772734243) ^ 2 = 4 := by
        calc
          (2 : ZMod 10772734243) ^ 2 = (2 : ZMod 10772734243) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 1 * (2 : ZMod 10772734243) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 10772734243) ^ 5 = 32 := by
        calc
          (2 : ZMod 10772734243) ^ 5 = (2 : ZMod 10772734243) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 2 * (2 : ZMod 10772734243) ^ 2) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 10772734243) ^ 10 = 1024 := by
        calc
          (2 : ZMod 10772734243) ^ 10 = (2 : ZMod 10772734243) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 5 * (2 : ZMod 10772734243) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 10772734243) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 10772734243) ^ 20 = (2 : ZMod 10772734243) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 10 * (2 : ZMod 10772734243) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 10772734243) ^ 40 = 692734990 := by
        calc
          (2 : ZMod 10772734243) ^ 40 = (2 : ZMod 10772734243) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 20 * (2 : ZMod 10772734243) ^ 20 := by rw [pow_add]
          _ = 692734990 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 10772734243) ^ 80 = 10009194549 := by
        calc
          (2 : ZMod 10772734243) ^ 80 = (2 : ZMod 10772734243) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 40 * (2 : ZMod 10772734243) ^ 40 := by rw [pow_add]
          _ = 10009194549 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 10772734243) ^ 160 = 645710258 := by
        calc
          (2 : ZMod 10772734243) ^ 160 = (2 : ZMod 10772734243) ^ (80 + 80) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 80 * (2 : ZMod 10772734243) ^ 80 := by rw [pow_add]
          _ = 645710258 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 10772734243) ^ 321 = 7844151606 := by
        calc
          (2 : ZMod 10772734243) ^ 321 = (2 : ZMod 10772734243) ^ (160 + 160 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 160 * (2 : ZMod 10772734243) ^ 160) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 7844151606 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 10772734243) ^ 642 = 2703094823 := by
        calc
          (2 : ZMod 10772734243) ^ 642 = (2 : ZMod 10772734243) ^ (321 + 321) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 321 * (2 : ZMod 10772734243) ^ 321 := by rw [pow_add]
          _ = 2703094823 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 10772734243) ^ 1284 = 10695040052 := by
        calc
          (2 : ZMod 10772734243) ^ 1284 = (2 : ZMod 10772734243) ^ (642 + 642) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 642 * (2 : ZMod 10772734243) ^ 642 := by rw [pow_add]
          _ = 10695040052 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 10772734243) ^ 2568 = 4182156104 := by
        calc
          (2 : ZMod 10772734243) ^ 2568 = (2 : ZMod 10772734243) ^ (1284 + 1284) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 1284 * (2 : ZMod 10772734243) ^ 1284 := by rw [pow_add]
          _ = 4182156104 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 10772734243) ^ 5136 = 361730039 := by
        calc
          (2 : ZMod 10772734243) ^ 5136 = (2 : ZMod 10772734243) ^ (2568 + 2568) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 2568 * (2 : ZMod 10772734243) ^ 2568 := by rw [pow_add]
          _ = 361730039 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 10772734243) ^ 10273 = 3131422177 := by
        calc
          (2 : ZMod 10772734243) ^ 10273 = (2 : ZMod 10772734243) ^ (5136 + 5136 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 5136 * (2 : ZMod 10772734243) ^ 5136) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 3131422177 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 10772734243) ^ 20547 = 6205057744 := by
        calc
          (2 : ZMod 10772734243) ^ 20547 = (2 : ZMod 10772734243) ^ (10273 + 10273 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 10273 * (2 : ZMod 10772734243) ^ 10273) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 6205057744 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 10772734243) ^ 41094 = 115821201 := by
        calc
          (2 : ZMod 10772734243) ^ 41094 = (2 : ZMod 10772734243) ^ (20547 + 20547) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 20547 * (2 : ZMod 10772734243) ^ 20547 := by rw [pow_add]
          _ = 115821201 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 10772734243) ^ 82189 = 5161140293 := by
        calc
          (2 : ZMod 10772734243) ^ 82189 = (2 : ZMod 10772734243) ^ (41094 + 41094 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 41094 * (2 : ZMod 10772734243) ^ 41094) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 5161140293 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 10772734243) ^ 164378 = 1965606881 := by
        calc
          (2 : ZMod 10772734243) ^ 164378 = (2 : ZMod 10772734243) ^ (82189 + 82189) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 82189 * (2 : ZMod 10772734243) ^ 82189 := by rw [pow_add]
          _ = 1965606881 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 10772734243) ^ 328757 = 7214052637 := by
        calc
          (2 : ZMod 10772734243) ^ 328757 = (2 : ZMod 10772734243) ^ (164378 + 164378 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 164378 * (2 : ZMod 10772734243) ^ 164378) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 7214052637 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 10772734243) ^ 657515 = 488614727 := by
        calc
          (2 : ZMod 10772734243) ^ 657515 = (2 : ZMod 10772734243) ^ (328757 + 328757 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 328757 * (2 : ZMod 10772734243) ^ 328757) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 488614727 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 10772734243) ^ 1315031 = 1706203527 := by
        calc
          (2 : ZMod 10772734243) ^ 1315031 = (2 : ZMod 10772734243) ^ (657515 + 657515 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 657515 * (2 : ZMod 10772734243) ^ 657515) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 1706203527 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 10772734243) ^ 2630062 = 961058651 := by
        calc
          (2 : ZMod 10772734243) ^ 2630062 = (2 : ZMod 10772734243) ^ (1315031 + 1315031) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 1315031 * (2 : ZMod 10772734243) ^ 1315031 := by rw [pow_add]
          _ = 961058651 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 10772734243) ^ 5260124 = 7953118473 := by
        calc
          (2 : ZMod 10772734243) ^ 5260124 = (2 : ZMod 10772734243) ^ (2630062 + 2630062) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 2630062 * (2 : ZMod 10772734243) ^ 2630062 := by rw [pow_add]
          _ = 7953118473 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 10772734243) ^ 10520248 = 1354941051 := by
        calc
          (2 : ZMod 10772734243) ^ 10520248 = (2 : ZMod 10772734243) ^ (5260124 + 5260124) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 5260124 * (2 : ZMod 10772734243) ^ 5260124 := by rw [pow_add]
          _ = 1354941051 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 10772734243) ^ 21040496 = 2144894678 := by
        calc
          (2 : ZMod 10772734243) ^ 21040496 = (2 : ZMod 10772734243) ^ (10520248 + 10520248) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 10520248 * (2 : ZMod 10772734243) ^ 10520248 := by rw [pow_add]
          _ = 2144894678 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 10772734243) ^ 42080993 = 3152206711 := by
        calc
          (2 : ZMod 10772734243) ^ 42080993 = (2 : ZMod 10772734243) ^ (21040496 + 21040496 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 21040496 * (2 : ZMod 10772734243) ^ 21040496) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 3152206711 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 10772734243) ^ 84161986 = 5774149948 := by
        calc
          (2 : ZMod 10772734243) ^ 84161986 = (2 : ZMod 10772734243) ^ (42080993 + 42080993) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 42080993 * (2 : ZMod 10772734243) ^ 42080993 := by rw [pow_add]
          _ = 5774149948 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 10772734243) ^ 168323972 = 3196899963 := by
        calc
          (2 : ZMod 10772734243) ^ 168323972 = (2 : ZMod 10772734243) ^ (84161986 + 84161986) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 84161986 * (2 : ZMod 10772734243) ^ 84161986 := by rw [pow_add]
          _ = 3196899963 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 10772734243) ^ 336647945 = 4500834269 := by
        calc
          (2 : ZMod 10772734243) ^ 336647945 = (2 : ZMod 10772734243) ^ (168323972 + 168323972 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 168323972 * (2 : ZMod 10772734243) ^ 168323972) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 4500834269 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 10772734243) ^ 673295890 = 6215618280 := by
        calc
          (2 : ZMod 10772734243) ^ 673295890 = (2 : ZMod 10772734243) ^ (336647945 + 336647945) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 336647945 * (2 : ZMod 10772734243) ^ 336647945 := by rw [pow_add]
          _ = 6215618280 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 10772734243) ^ 1346591780 = 1132359934 := by
        calc
          (2 : ZMod 10772734243) ^ 1346591780 = (2 : ZMod 10772734243) ^ (673295890 + 673295890) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 673295890 * (2 : ZMod 10772734243) ^ 673295890 := by rw [pow_add]
          _ = 1132359934 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 10772734243) ^ 2693183560 = 9891600409 := by
        calc
          (2 : ZMod 10772734243) ^ 2693183560 = (2 : ZMod 10772734243) ^ (1346591780 + 1346591780) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 1346591780 * (2 : ZMod 10772734243) ^ 1346591780 := by rw [pow_add]
          _ = 9891600409 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 10772734243) ^ 5386367121 = 10772734242 := by
        calc
          (2 : ZMod 10772734243) ^ 5386367121 = (2 : ZMod 10772734243) ^ (2693183560 + 2693183560 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 2693183560 * (2 : ZMod 10772734243) ^ 2693183560) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 10772734242 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 10772734243) ^ 10772734242 = 1 := by
        calc
          (2 : ZMod 10772734243) ^ 10772734242 = (2 : ZMod 10772734243) ^ (5386367121 + 5386367121) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 5386367121 * (2 : ZMod 10772734243) ^ 5386367121 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1795455707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1795455707, 1)] : List FactorBlock).map factorBlockValue).prod = 10772734243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_1795455707) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 10772734243) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 10772734243) ^ 2 = 4 := by
        calc
          (2 : ZMod 10772734243) ^ 2 = (2 : ZMod 10772734243) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 1 * (2 : ZMod 10772734243) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 10772734243) ^ 5 = 32 := by
        calc
          (2 : ZMod 10772734243) ^ 5 = (2 : ZMod 10772734243) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 2 * (2 : ZMod 10772734243) ^ 2) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 10772734243) ^ 10 = 1024 := by
        calc
          (2 : ZMod 10772734243) ^ 10 = (2 : ZMod 10772734243) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 5 * (2 : ZMod 10772734243) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 10772734243) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 10772734243) ^ 20 = (2 : ZMod 10772734243) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 10 * (2 : ZMod 10772734243) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 10772734243) ^ 40 = 692734990 := by
        calc
          (2 : ZMod 10772734243) ^ 40 = (2 : ZMod 10772734243) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 20 * (2 : ZMod 10772734243) ^ 20 := by rw [pow_add]
          _ = 692734990 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 10772734243) ^ 80 = 10009194549 := by
        calc
          (2 : ZMod 10772734243) ^ 80 = (2 : ZMod 10772734243) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 40 * (2 : ZMod 10772734243) ^ 40 := by rw [pow_add]
          _ = 10009194549 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 10772734243) ^ 160 = 645710258 := by
        calc
          (2 : ZMod 10772734243) ^ 160 = (2 : ZMod 10772734243) ^ (80 + 80) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 80 * (2 : ZMod 10772734243) ^ 80 := by rw [pow_add]
          _ = 645710258 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 10772734243) ^ 321 = 7844151606 := by
        calc
          (2 : ZMod 10772734243) ^ 321 = (2 : ZMod 10772734243) ^ (160 + 160 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 160 * (2 : ZMod 10772734243) ^ 160) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 7844151606 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 10772734243) ^ 642 = 2703094823 := by
        calc
          (2 : ZMod 10772734243) ^ 642 = (2 : ZMod 10772734243) ^ (321 + 321) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 321 * (2 : ZMod 10772734243) ^ 321 := by rw [pow_add]
          _ = 2703094823 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 10772734243) ^ 1284 = 10695040052 := by
        calc
          (2 : ZMod 10772734243) ^ 1284 = (2 : ZMod 10772734243) ^ (642 + 642) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 642 * (2 : ZMod 10772734243) ^ 642 := by rw [pow_add]
          _ = 10695040052 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 10772734243) ^ 2568 = 4182156104 := by
        calc
          (2 : ZMod 10772734243) ^ 2568 = (2 : ZMod 10772734243) ^ (1284 + 1284) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 1284 * (2 : ZMod 10772734243) ^ 1284 := by rw [pow_add]
          _ = 4182156104 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 10772734243) ^ 5136 = 361730039 := by
        calc
          (2 : ZMod 10772734243) ^ 5136 = (2 : ZMod 10772734243) ^ (2568 + 2568) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 2568 * (2 : ZMod 10772734243) ^ 2568 := by rw [pow_add]
          _ = 361730039 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 10772734243) ^ 10273 = 3131422177 := by
        calc
          (2 : ZMod 10772734243) ^ 10273 = (2 : ZMod 10772734243) ^ (5136 + 5136 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 5136 * (2 : ZMod 10772734243) ^ 5136) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 3131422177 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 10772734243) ^ 20547 = 6205057744 := by
        calc
          (2 : ZMod 10772734243) ^ 20547 = (2 : ZMod 10772734243) ^ (10273 + 10273 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 10273 * (2 : ZMod 10772734243) ^ 10273) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 6205057744 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 10772734243) ^ 41094 = 115821201 := by
        calc
          (2 : ZMod 10772734243) ^ 41094 = (2 : ZMod 10772734243) ^ (20547 + 20547) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 20547 * (2 : ZMod 10772734243) ^ 20547 := by rw [pow_add]
          _ = 115821201 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 10772734243) ^ 82189 = 5161140293 := by
        calc
          (2 : ZMod 10772734243) ^ 82189 = (2 : ZMod 10772734243) ^ (41094 + 41094 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 41094 * (2 : ZMod 10772734243) ^ 41094) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 5161140293 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 10772734243) ^ 164378 = 1965606881 := by
        calc
          (2 : ZMod 10772734243) ^ 164378 = (2 : ZMod 10772734243) ^ (82189 + 82189) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 82189 * (2 : ZMod 10772734243) ^ 82189 := by rw [pow_add]
          _ = 1965606881 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 10772734243) ^ 328757 = 7214052637 := by
        calc
          (2 : ZMod 10772734243) ^ 328757 = (2 : ZMod 10772734243) ^ (164378 + 164378 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 164378 * (2 : ZMod 10772734243) ^ 164378) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 7214052637 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 10772734243) ^ 657515 = 488614727 := by
        calc
          (2 : ZMod 10772734243) ^ 657515 = (2 : ZMod 10772734243) ^ (328757 + 328757 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 328757 * (2 : ZMod 10772734243) ^ 328757) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 488614727 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 10772734243) ^ 1315031 = 1706203527 := by
        calc
          (2 : ZMod 10772734243) ^ 1315031 = (2 : ZMod 10772734243) ^ (657515 + 657515 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 657515 * (2 : ZMod 10772734243) ^ 657515) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 1706203527 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 10772734243) ^ 2630062 = 961058651 := by
        calc
          (2 : ZMod 10772734243) ^ 2630062 = (2 : ZMod 10772734243) ^ (1315031 + 1315031) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 1315031 * (2 : ZMod 10772734243) ^ 1315031 := by rw [pow_add]
          _ = 961058651 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 10772734243) ^ 5260124 = 7953118473 := by
        calc
          (2 : ZMod 10772734243) ^ 5260124 = (2 : ZMod 10772734243) ^ (2630062 + 2630062) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 2630062 * (2 : ZMod 10772734243) ^ 2630062 := by rw [pow_add]
          _ = 7953118473 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 10772734243) ^ 10520248 = 1354941051 := by
        calc
          (2 : ZMod 10772734243) ^ 10520248 = (2 : ZMod 10772734243) ^ (5260124 + 5260124) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 5260124 * (2 : ZMod 10772734243) ^ 5260124 := by rw [pow_add]
          _ = 1354941051 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 10772734243) ^ 21040496 = 2144894678 := by
        calc
          (2 : ZMod 10772734243) ^ 21040496 = (2 : ZMod 10772734243) ^ (10520248 + 10520248) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 10520248 * (2 : ZMod 10772734243) ^ 10520248 := by rw [pow_add]
          _ = 2144894678 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 10772734243) ^ 42080993 = 3152206711 := by
        calc
          (2 : ZMod 10772734243) ^ 42080993 = (2 : ZMod 10772734243) ^ (21040496 + 21040496 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 21040496 * (2 : ZMod 10772734243) ^ 21040496) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 3152206711 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 10772734243) ^ 84161986 = 5774149948 := by
        calc
          (2 : ZMod 10772734243) ^ 84161986 = (2 : ZMod 10772734243) ^ (42080993 + 42080993) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 42080993 * (2 : ZMod 10772734243) ^ 42080993 := by rw [pow_add]
          _ = 5774149948 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 10772734243) ^ 168323972 = 3196899963 := by
        calc
          (2 : ZMod 10772734243) ^ 168323972 = (2 : ZMod 10772734243) ^ (84161986 + 84161986) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 84161986 * (2 : ZMod 10772734243) ^ 84161986 := by rw [pow_add]
          _ = 3196899963 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 10772734243) ^ 336647945 = 4500834269 := by
        calc
          (2 : ZMod 10772734243) ^ 336647945 = (2 : ZMod 10772734243) ^ (168323972 + 168323972 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 168323972 * (2 : ZMod 10772734243) ^ 168323972) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 4500834269 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 10772734243) ^ 673295890 = 6215618280 := by
        calc
          (2 : ZMod 10772734243) ^ 673295890 = (2 : ZMod 10772734243) ^ (336647945 + 336647945) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 336647945 * (2 : ZMod 10772734243) ^ 336647945 := by rw [pow_add]
          _ = 6215618280 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 10772734243) ^ 1346591780 = 1132359934 := by
        calc
          (2 : ZMod 10772734243) ^ 1346591780 = (2 : ZMod 10772734243) ^ (673295890 + 673295890) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 673295890 * (2 : ZMod 10772734243) ^ 673295890 := by rw [pow_add]
          _ = 1132359934 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 10772734243) ^ 2693183560 = 9891600409 := by
        calc
          (2 : ZMod 10772734243) ^ 2693183560 = (2 : ZMod 10772734243) ^ (1346591780 + 1346591780) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 1346591780 * (2 : ZMod 10772734243) ^ 1346591780 := by rw [pow_add]
          _ = 9891600409 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 10772734243) ^ 5386367121 = 10772734242 := by
        calc
          (2 : ZMod 10772734243) ^ 5386367121 = (2 : ZMod 10772734243) ^ (2693183560 + 2693183560 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 2693183560 * (2 : ZMod 10772734243) ^ 2693183560) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 10772734242 := by rw [factor_0_31]; decide
      change (2 : ZMod 10772734243) ^ 5386367121 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (2 : ZMod 10772734243) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 10772734243) ^ 3 = 8 := by
        calc
          (2 : ZMod 10772734243) ^ 3 = (2 : ZMod 10772734243) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 1 * (2 : ZMod 10772734243) ^ 1) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 10772734243) ^ 6 = 64 := by
        calc
          (2 : ZMod 10772734243) ^ 6 = (2 : ZMod 10772734243) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 3 * (2 : ZMod 10772734243) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 10772734243) ^ 13 = 8192 := by
        calc
          (2 : ZMod 10772734243) ^ 13 = (2 : ZMod 10772734243) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 6 * (2 : ZMod 10772734243) ^ 6) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 10772734243) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 10772734243) ^ 26 = (2 : ZMod 10772734243) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 13 * (2 : ZMod 10772734243) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 10772734243) ^ 53 = 8426826262 := by
        calc
          (2 : ZMod 10772734243) ^ 53 = (2 : ZMod 10772734243) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 26 * (2 : ZMod 10772734243) ^ 26) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 8426826262 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 10772734243) ^ 107 = 5432325562 := by
        calc
          (2 : ZMod 10772734243) ^ 107 = (2 : ZMod 10772734243) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 53 * (2 : ZMod 10772734243) ^ 53) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 5432325562 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 10772734243) ^ 214 = 3261553320 := by
        calc
          (2 : ZMod 10772734243) ^ 214 = (2 : ZMod 10772734243) ^ (107 + 107) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 107 * (2 : ZMod 10772734243) ^ 107 := by rw [pow_add]
          _ = 3261553320 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 10772734243) ^ 428 = 1827388718 := by
        calc
          (2 : ZMod 10772734243) ^ 428 = (2 : ZMod 10772734243) ^ (214 + 214) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 214 * (2 : ZMod 10772734243) ^ 214 := by rw [pow_add]
          _ = 1827388718 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 10772734243) ^ 856 = 380943808 := by
        calc
          (2 : ZMod 10772734243) ^ 856 = (2 : ZMod 10772734243) ^ (428 + 428) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 428 * (2 : ZMod 10772734243) ^ 428 := by rw [pow_add]
          _ = 380943808 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 10772734243) ^ 1712 = 6912399753 := by
        calc
          (2 : ZMod 10772734243) ^ 1712 = (2 : ZMod 10772734243) ^ (856 + 856) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 856 * (2 : ZMod 10772734243) ^ 856 := by rw [pow_add]
          _ = 6912399753 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 10772734243) ^ 3424 = 1310381707 := by
        calc
          (2 : ZMod 10772734243) ^ 3424 = (2 : ZMod 10772734243) ^ (1712 + 1712) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 1712 * (2 : ZMod 10772734243) ^ 1712 := by rw [pow_add]
          _ = 1310381707 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 10772734243) ^ 6849 = 1143701022 := by
        calc
          (2 : ZMod 10772734243) ^ 6849 = (2 : ZMod 10772734243) ^ (3424 + 3424 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 3424 * (2 : ZMod 10772734243) ^ 3424) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 1143701022 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 10772734243) ^ 13698 = 5739735788 := by
        calc
          (2 : ZMod 10772734243) ^ 13698 = (2 : ZMod 10772734243) ^ (6849 + 6849) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 6849 * (2 : ZMod 10772734243) ^ 6849 := by rw [pow_add]
          _ = 5739735788 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 10772734243) ^ 27396 = 4453935005 := by
        calc
          (2 : ZMod 10772734243) ^ 27396 = (2 : ZMod 10772734243) ^ (13698 + 13698) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 13698 * (2 : ZMod 10772734243) ^ 13698 := by rw [pow_add]
          _ = 4453935005 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 10772734243) ^ 54792 = 10709376362 := by
        calc
          (2 : ZMod 10772734243) ^ 54792 = (2 : ZMod 10772734243) ^ (27396 + 27396) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 27396 * (2 : ZMod 10772734243) ^ 27396 := by rw [pow_add]
          _ = 10709376362 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 10772734243) ^ 109585 = 8111353357 := by
        calc
          (2 : ZMod 10772734243) ^ 109585 = (2 : ZMod 10772734243) ^ (54792 + 54792 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 54792 * (2 : ZMod 10772734243) ^ 54792) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 8111353357 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 10772734243) ^ 219171 = 9121190881 := by
        calc
          (2 : ZMod 10772734243) ^ 219171 = (2 : ZMod 10772734243) ^ (109585 + 109585 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 109585 * (2 : ZMod 10772734243) ^ 109585) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 9121190881 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 10772734243) ^ 438343 = 10510600773 := by
        calc
          (2 : ZMod 10772734243) ^ 438343 = (2 : ZMod 10772734243) ^ (219171 + 219171 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 219171 * (2 : ZMod 10772734243) ^ 219171) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 10510600773 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 10772734243) ^ 876687 = 1404985641 := by
        calc
          (2 : ZMod 10772734243) ^ 876687 = (2 : ZMod 10772734243) ^ (438343 + 438343 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 438343 * (2 : ZMod 10772734243) ^ 438343) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 1404985641 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 10772734243) ^ 1753374 = 54270872 := by
        calc
          (2 : ZMod 10772734243) ^ 1753374 = (2 : ZMod 10772734243) ^ (876687 + 876687) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 876687 * (2 : ZMod 10772734243) ^ 876687 := by rw [pow_add]
          _ = 54270872 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 10772734243) ^ 3506749 = 5511131695 := by
        calc
          (2 : ZMod 10772734243) ^ 3506749 = (2 : ZMod 10772734243) ^ (1753374 + 1753374 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 1753374 * (2 : ZMod 10772734243) ^ 1753374) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 5511131695 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 10772734243) ^ 7013498 = 9876586697 := by
        calc
          (2 : ZMod 10772734243) ^ 7013498 = (2 : ZMod 10772734243) ^ (3506749 + 3506749) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 3506749 * (2 : ZMod 10772734243) ^ 3506749 := by rw [pow_add]
          _ = 9876586697 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 10772734243) ^ 14026997 = 4125356503 := by
        calc
          (2 : ZMod 10772734243) ^ 14026997 = (2 : ZMod 10772734243) ^ (7013498 + 7013498 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 7013498 * (2 : ZMod 10772734243) ^ 7013498) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 4125356503 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 10772734243) ^ 28053995 = 9127500532 := by
        calc
          (2 : ZMod 10772734243) ^ 28053995 = (2 : ZMod 10772734243) ^ (14026997 + 14026997 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 14026997 * (2 : ZMod 10772734243) ^ 14026997) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 9127500532 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 10772734243) ^ 56107990 = 1345414405 := by
        calc
          (2 : ZMod 10772734243) ^ 56107990 = (2 : ZMod 10772734243) ^ (28053995 + 28053995) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 28053995 * (2 : ZMod 10772734243) ^ 28053995 := by rw [pow_add]
          _ = 1345414405 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 10772734243) ^ 112215981 = 8209270148 := by
        calc
          (2 : ZMod 10772734243) ^ 112215981 = (2 : ZMod 10772734243) ^ (56107990 + 56107990 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 56107990 * (2 : ZMod 10772734243) ^ 56107990) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 8209270148 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 10772734243) ^ 224431963 = 6001135916 := by
        calc
          (2 : ZMod 10772734243) ^ 224431963 = (2 : ZMod 10772734243) ^ (112215981 + 112215981 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 112215981 * (2 : ZMod 10772734243) ^ 112215981) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 6001135916 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 10772734243) ^ 448863926 = 8436461080 := by
        calc
          (2 : ZMod 10772734243) ^ 448863926 = (2 : ZMod 10772734243) ^ (224431963 + 224431963) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 224431963 * (2 : ZMod 10772734243) ^ 224431963 := by rw [pow_add]
          _ = 8436461080 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 10772734243) ^ 897727853 = 1433432251 := by
        calc
          (2 : ZMod 10772734243) ^ 897727853 = (2 : ZMod 10772734243) ^ (448863926 + 448863926 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 448863926 * (2 : ZMod 10772734243) ^ 448863926) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 1433432251 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 10772734243) ^ 1795455707 = 112506224 := by
        calc
          (2 : ZMod 10772734243) ^ 1795455707 = (2 : ZMod 10772734243) ^ (897727853 + 897727853 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 897727853 * (2 : ZMod 10772734243) ^ 897727853) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 112506224 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 10772734243) ^ 3590911414 = 112506223 := by
        calc
          (2 : ZMod 10772734243) ^ 3590911414 = (2 : ZMod 10772734243) ^ (1795455707 + 1795455707) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 1795455707 * (2 : ZMod 10772734243) ^ 1795455707 := by rw [pow_add]
          _ = 112506223 := by rw [factor_1_30]; decide
      change (2 : ZMod 10772734243) ^ 3590911414 ≠ 1
      rw [factor_1_31]
      decide
    ·
      have factor_2_0 : (2 : ZMod 10772734243) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 10772734243) ^ 3 = 8 := by
        calc
          (2 : ZMod 10772734243) ^ 3 = (2 : ZMod 10772734243) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = ((2 : ZMod 10772734243) ^ 1 * (2 : ZMod 10772734243) ^ 1) * (2 : ZMod 10772734243) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 10772734243) ^ 6 = 64 := by
        calc
          (2 : ZMod 10772734243) ^ 6 = (2 : ZMod 10772734243) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 10772734243) ^ n) (by norm_num)
          _ = (2 : ZMod 10772734243) ^ 3 * (2 : ZMod 10772734243) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      change (2 : ZMod 10772734243) ^ 6 ≠ 1
      rw [factor_2_2]
      decide

#print axioms prime_lucas_10772734243

end TotientTailPeriodKiller
end Erdos249257
