import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime763698527

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_6109588217 : Nat.Prime 6109588217 := by
  apply lucas_primality 6109588217 (3 : ZMod 6109588217)
  ·
      have fermat_0 : (3 : ZMod 6109588217) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 6109588217) ^ 2 = 9 := by
        calc
          (3 : ZMod 6109588217) ^ 2 = (3 : ZMod 6109588217) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 1 * (3 : ZMod 6109588217) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 6109588217) ^ 5 = 243 := by
        calc
          (3 : ZMod 6109588217) ^ 5 = (3 : ZMod 6109588217) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 2 * (3 : ZMod 6109588217) ^ 2) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 6109588217) ^ 11 = 177147 := by
        calc
          (3 : ZMod 6109588217) ^ 11 = (3 : ZMod 6109588217) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 5 * (3 : ZMod 6109588217) ^ 5) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 6109588217) ^ 22 = 833118524 := by
        calc
          (3 : ZMod 6109588217) ^ 22 = (3 : ZMod 6109588217) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 11 * (3 : ZMod 6109588217) ^ 11 := by rw [pow_add]
          _ = 833118524 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 6109588217) ^ 45 = 4154550364 := by
        calc
          (3 : ZMod 6109588217) ^ 45 = (3 : ZMod 6109588217) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 22 * (3 : ZMod 6109588217) ^ 22) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 4154550364 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 6109588217) ^ 91 = 5808315418 := by
        calc
          (3 : ZMod 6109588217) ^ 91 = (3 : ZMod 6109588217) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 45 * (3 : ZMod 6109588217) ^ 45) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 5808315418 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 6109588217) ^ 182 = 4399957916 := by
        calc
          (3 : ZMod 6109588217) ^ 182 = (3 : ZMod 6109588217) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 91 * (3 : ZMod 6109588217) ^ 91 := by rw [pow_add]
          _ = 4399957916 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 6109588217) ^ 364 = 1935047423 := by
        calc
          (3 : ZMod 6109588217) ^ 364 = (3 : ZMod 6109588217) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 182 * (3 : ZMod 6109588217) ^ 182 := by rw [pow_add]
          _ = 1935047423 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 6109588217) ^ 728 = 2764344021 := by
        calc
          (3 : ZMod 6109588217) ^ 728 = (3 : ZMod 6109588217) ^ (364 + 364) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 364 * (3 : ZMod 6109588217) ^ 364 := by rw [pow_add]
          _ = 2764344021 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 6109588217) ^ 1456 = 2714730649 := by
        calc
          (3 : ZMod 6109588217) ^ 1456 = (3 : ZMod 6109588217) ^ (728 + 728) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 728 * (3 : ZMod 6109588217) ^ 728 := by rw [pow_add]
          _ = 2714730649 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 6109588217) ^ 2913 = 4880424816 := by
        calc
          (3 : ZMod 6109588217) ^ 2913 = (3 : ZMod 6109588217) ^ (1456 + 1456 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 1456 * (3 : ZMod 6109588217) ^ 1456) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 4880424816 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 6109588217) ^ 5826 = 5710552793 := by
        calc
          (3 : ZMod 6109588217) ^ 5826 = (3 : ZMod 6109588217) ^ (2913 + 2913) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 2913 * (3 : ZMod 6109588217) ^ 2913 := by rw [pow_add]
          _ = 5710552793 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 6109588217) ^ 11653 = 925051468 := by
        calc
          (3 : ZMod 6109588217) ^ 11653 = (3 : ZMod 6109588217) ^ (5826 + 5826 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 5826 * (3 : ZMod 6109588217) ^ 5826) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 925051468 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 6109588217) ^ 23306 = 2256910008 := by
        calc
          (3 : ZMod 6109588217) ^ 23306 = (3 : ZMod 6109588217) ^ (11653 + 11653) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 11653 * (3 : ZMod 6109588217) ^ 11653 := by rw [pow_add]
          _ = 2256910008 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 6109588217) ^ 46612 = 5187779216 := by
        calc
          (3 : ZMod 6109588217) ^ 46612 = (3 : ZMod 6109588217) ^ (23306 + 23306) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 23306 * (3 : ZMod 6109588217) ^ 23306 := by rw [pow_add]
          _ = 5187779216 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 6109588217) ^ 93224 = 4338524139 := by
        calc
          (3 : ZMod 6109588217) ^ 93224 = (3 : ZMod 6109588217) ^ (46612 + 46612) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 46612 * (3 : ZMod 6109588217) ^ 46612 := by rw [pow_add]
          _ = 4338524139 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 6109588217) ^ 186449 = 4009677372 := by
        calc
          (3 : ZMod 6109588217) ^ 186449 = (3 : ZMod 6109588217) ^ (93224 + 93224 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 93224 * (3 : ZMod 6109588217) ^ 93224) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 4009677372 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 6109588217) ^ 372899 = 1615275672 := by
        calc
          (3 : ZMod 6109588217) ^ 372899 = (3 : ZMod 6109588217) ^ (186449 + 186449 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 186449 * (3 : ZMod 6109588217) ^ 186449) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 1615275672 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 6109588217) ^ 745799 = 640100058 := by
        calc
          (3 : ZMod 6109588217) ^ 745799 = (3 : ZMod 6109588217) ^ (372899 + 372899 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 372899 * (3 : ZMod 6109588217) ^ 372899) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 640100058 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 6109588217) ^ 1491598 = 5956405239 := by
        calc
          (3 : ZMod 6109588217) ^ 1491598 = (3 : ZMod 6109588217) ^ (745799 + 745799) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 745799 * (3 : ZMod 6109588217) ^ 745799 := by rw [pow_add]
          _ = 5956405239 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 6109588217) ^ 2983197 = 1687337347 := by
        calc
          (3 : ZMod 6109588217) ^ 2983197 = (3 : ZMod 6109588217) ^ (1491598 + 1491598 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 1491598 * (3 : ZMod 6109588217) ^ 1491598) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 1687337347 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 6109588217) ^ 5966394 = 2121821703 := by
        calc
          (3 : ZMod 6109588217) ^ 5966394 = (3 : ZMod 6109588217) ^ (2983197 + 2983197) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 2983197 * (3 : ZMod 6109588217) ^ 2983197 := by rw [pow_add]
          _ = 2121821703 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 6109588217) ^ 11932789 = 1097895379 := by
        calc
          (3 : ZMod 6109588217) ^ 11932789 = (3 : ZMod 6109588217) ^ (5966394 + 5966394 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 5966394 * (3 : ZMod 6109588217) ^ 5966394) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 1097895379 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 6109588217) ^ 23865578 = 3954252599 := by
        calc
          (3 : ZMod 6109588217) ^ 23865578 = (3 : ZMod 6109588217) ^ (11932789 + 11932789) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 11932789 * (3 : ZMod 6109588217) ^ 11932789 := by rw [pow_add]
          _ = 3954252599 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 6109588217) ^ 47731157 = 837126306 := by
        calc
          (3 : ZMod 6109588217) ^ 47731157 = (3 : ZMod 6109588217) ^ (23865578 + 23865578 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 23865578 * (3 : ZMod 6109588217) ^ 23865578) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 837126306 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 6109588217) ^ 95462315 = 222130526 := by
        calc
          (3 : ZMod 6109588217) ^ 95462315 = (3 : ZMod 6109588217) ^ (47731157 + 47731157 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 47731157 * (3 : ZMod 6109588217) ^ 47731157) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 222130526 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 6109588217) ^ 190924631 = 4120642425 := by
        calc
          (3 : ZMod 6109588217) ^ 190924631 = (3 : ZMod 6109588217) ^ (95462315 + 95462315 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 95462315 * (3 : ZMod 6109588217) ^ 95462315) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 4120642425 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 6109588217) ^ 381849263 = 5492722085 := by
        calc
          (3 : ZMod 6109588217) ^ 381849263 = (3 : ZMod 6109588217) ^ (190924631 + 190924631 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 190924631 * (3 : ZMod 6109588217) ^ 190924631) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 5492722085 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 6109588217) ^ 763698527 = 5366459033 := by
        calc
          (3 : ZMod 6109588217) ^ 763698527 = (3 : ZMod 6109588217) ^ (381849263 + 381849263 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 381849263 * (3 : ZMod 6109588217) ^ 381849263) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 5366459033 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 6109588217) ^ 1527397054 = 3451214729 := by
        calc
          (3 : ZMod 6109588217) ^ 1527397054 = (3 : ZMod 6109588217) ^ (763698527 + 763698527) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 763698527 * (3 : ZMod 6109588217) ^ 763698527 := by rw [pow_add]
          _ = 3451214729 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 6109588217) ^ 3054794108 = 6109588216 := by
        calc
          (3 : ZMod 6109588217) ^ 3054794108 = (3 : ZMod 6109588217) ^ (1527397054 + 1527397054) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 1527397054 * (3 : ZMod 6109588217) ^ 1527397054 := by rw [pow_add]
          _ = 6109588216 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 6109588217) ^ 6109588216 = 1 := by
        calc
          (3 : ZMod 6109588217) ^ 6109588216 = (3 : ZMod 6109588217) ^ (3054794108 + 3054794108) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 3054794108 * (3 : ZMod 6109588217) ^ 3054794108 := by rw [pow_add]
          _ = 1 := by rw [fermat_31]; decide
      simpa using fermat_32
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (763698527, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (763698527, 1)] : List FactorBlock).map factorBlockValue).prod = 6109588217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_763698527) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 6109588217) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 6109588217) ^ 2 = 9 := by
        calc
          (3 : ZMod 6109588217) ^ 2 = (3 : ZMod 6109588217) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 1 * (3 : ZMod 6109588217) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 6109588217) ^ 5 = 243 := by
        calc
          (3 : ZMod 6109588217) ^ 5 = (3 : ZMod 6109588217) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 2 * (3 : ZMod 6109588217) ^ 2) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 6109588217) ^ 11 = 177147 := by
        calc
          (3 : ZMod 6109588217) ^ 11 = (3 : ZMod 6109588217) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 5 * (3 : ZMod 6109588217) ^ 5) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 6109588217) ^ 22 = 833118524 := by
        calc
          (3 : ZMod 6109588217) ^ 22 = (3 : ZMod 6109588217) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 11 * (3 : ZMod 6109588217) ^ 11 := by rw [pow_add]
          _ = 833118524 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 6109588217) ^ 45 = 4154550364 := by
        calc
          (3 : ZMod 6109588217) ^ 45 = (3 : ZMod 6109588217) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 22 * (3 : ZMod 6109588217) ^ 22) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 4154550364 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 6109588217) ^ 91 = 5808315418 := by
        calc
          (3 : ZMod 6109588217) ^ 91 = (3 : ZMod 6109588217) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 45 * (3 : ZMod 6109588217) ^ 45) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 5808315418 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 6109588217) ^ 182 = 4399957916 := by
        calc
          (3 : ZMod 6109588217) ^ 182 = (3 : ZMod 6109588217) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 91 * (3 : ZMod 6109588217) ^ 91 := by rw [pow_add]
          _ = 4399957916 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 6109588217) ^ 364 = 1935047423 := by
        calc
          (3 : ZMod 6109588217) ^ 364 = (3 : ZMod 6109588217) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 182 * (3 : ZMod 6109588217) ^ 182 := by rw [pow_add]
          _ = 1935047423 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 6109588217) ^ 728 = 2764344021 := by
        calc
          (3 : ZMod 6109588217) ^ 728 = (3 : ZMod 6109588217) ^ (364 + 364) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 364 * (3 : ZMod 6109588217) ^ 364 := by rw [pow_add]
          _ = 2764344021 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 6109588217) ^ 1456 = 2714730649 := by
        calc
          (3 : ZMod 6109588217) ^ 1456 = (3 : ZMod 6109588217) ^ (728 + 728) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 728 * (3 : ZMod 6109588217) ^ 728 := by rw [pow_add]
          _ = 2714730649 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 6109588217) ^ 2913 = 4880424816 := by
        calc
          (3 : ZMod 6109588217) ^ 2913 = (3 : ZMod 6109588217) ^ (1456 + 1456 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 1456 * (3 : ZMod 6109588217) ^ 1456) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 4880424816 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 6109588217) ^ 5826 = 5710552793 := by
        calc
          (3 : ZMod 6109588217) ^ 5826 = (3 : ZMod 6109588217) ^ (2913 + 2913) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 2913 * (3 : ZMod 6109588217) ^ 2913 := by rw [pow_add]
          _ = 5710552793 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 6109588217) ^ 11653 = 925051468 := by
        calc
          (3 : ZMod 6109588217) ^ 11653 = (3 : ZMod 6109588217) ^ (5826 + 5826 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 5826 * (3 : ZMod 6109588217) ^ 5826) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 925051468 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 6109588217) ^ 23306 = 2256910008 := by
        calc
          (3 : ZMod 6109588217) ^ 23306 = (3 : ZMod 6109588217) ^ (11653 + 11653) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 11653 * (3 : ZMod 6109588217) ^ 11653 := by rw [pow_add]
          _ = 2256910008 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 6109588217) ^ 46612 = 5187779216 := by
        calc
          (3 : ZMod 6109588217) ^ 46612 = (3 : ZMod 6109588217) ^ (23306 + 23306) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 23306 * (3 : ZMod 6109588217) ^ 23306 := by rw [pow_add]
          _ = 5187779216 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 6109588217) ^ 93224 = 4338524139 := by
        calc
          (3 : ZMod 6109588217) ^ 93224 = (3 : ZMod 6109588217) ^ (46612 + 46612) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 46612 * (3 : ZMod 6109588217) ^ 46612 := by rw [pow_add]
          _ = 4338524139 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 6109588217) ^ 186449 = 4009677372 := by
        calc
          (3 : ZMod 6109588217) ^ 186449 = (3 : ZMod 6109588217) ^ (93224 + 93224 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 93224 * (3 : ZMod 6109588217) ^ 93224) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 4009677372 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 6109588217) ^ 372899 = 1615275672 := by
        calc
          (3 : ZMod 6109588217) ^ 372899 = (3 : ZMod 6109588217) ^ (186449 + 186449 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 186449 * (3 : ZMod 6109588217) ^ 186449) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 1615275672 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 6109588217) ^ 745799 = 640100058 := by
        calc
          (3 : ZMod 6109588217) ^ 745799 = (3 : ZMod 6109588217) ^ (372899 + 372899 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 372899 * (3 : ZMod 6109588217) ^ 372899) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 640100058 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 6109588217) ^ 1491598 = 5956405239 := by
        calc
          (3 : ZMod 6109588217) ^ 1491598 = (3 : ZMod 6109588217) ^ (745799 + 745799) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 745799 * (3 : ZMod 6109588217) ^ 745799 := by rw [pow_add]
          _ = 5956405239 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 6109588217) ^ 2983197 = 1687337347 := by
        calc
          (3 : ZMod 6109588217) ^ 2983197 = (3 : ZMod 6109588217) ^ (1491598 + 1491598 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 1491598 * (3 : ZMod 6109588217) ^ 1491598) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 1687337347 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 6109588217) ^ 5966394 = 2121821703 := by
        calc
          (3 : ZMod 6109588217) ^ 5966394 = (3 : ZMod 6109588217) ^ (2983197 + 2983197) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 2983197 * (3 : ZMod 6109588217) ^ 2983197 := by rw [pow_add]
          _ = 2121821703 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 6109588217) ^ 11932789 = 1097895379 := by
        calc
          (3 : ZMod 6109588217) ^ 11932789 = (3 : ZMod 6109588217) ^ (5966394 + 5966394 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 5966394 * (3 : ZMod 6109588217) ^ 5966394) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 1097895379 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 6109588217) ^ 23865578 = 3954252599 := by
        calc
          (3 : ZMod 6109588217) ^ 23865578 = (3 : ZMod 6109588217) ^ (11932789 + 11932789) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 11932789 * (3 : ZMod 6109588217) ^ 11932789 := by rw [pow_add]
          _ = 3954252599 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 6109588217) ^ 47731157 = 837126306 := by
        calc
          (3 : ZMod 6109588217) ^ 47731157 = (3 : ZMod 6109588217) ^ (23865578 + 23865578 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 23865578 * (3 : ZMod 6109588217) ^ 23865578) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 837126306 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 6109588217) ^ 95462315 = 222130526 := by
        calc
          (3 : ZMod 6109588217) ^ 95462315 = (3 : ZMod 6109588217) ^ (47731157 + 47731157 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 47731157 * (3 : ZMod 6109588217) ^ 47731157) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 222130526 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 6109588217) ^ 190924631 = 4120642425 := by
        calc
          (3 : ZMod 6109588217) ^ 190924631 = (3 : ZMod 6109588217) ^ (95462315 + 95462315 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 95462315 * (3 : ZMod 6109588217) ^ 95462315) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 4120642425 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 6109588217) ^ 381849263 = 5492722085 := by
        calc
          (3 : ZMod 6109588217) ^ 381849263 = (3 : ZMod 6109588217) ^ (190924631 + 190924631 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 190924631 * (3 : ZMod 6109588217) ^ 190924631) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 5492722085 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 6109588217) ^ 763698527 = 5366459033 := by
        calc
          (3 : ZMod 6109588217) ^ 763698527 = (3 : ZMod 6109588217) ^ (381849263 + 381849263 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = ((3 : ZMod 6109588217) ^ 381849263 * (3 : ZMod 6109588217) ^ 381849263) * (3 : ZMod 6109588217) := by rw [pow_succ, pow_add]
          _ = 5366459033 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 6109588217) ^ 1527397054 = 3451214729 := by
        calc
          (3 : ZMod 6109588217) ^ 1527397054 = (3 : ZMod 6109588217) ^ (763698527 + 763698527) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 763698527 * (3 : ZMod 6109588217) ^ 763698527 := by rw [pow_add]
          _ = 3451214729 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 6109588217) ^ 3054794108 = 6109588216 := by
        calc
          (3 : ZMod 6109588217) ^ 3054794108 = (3 : ZMod 6109588217) ^ (1527397054 + 1527397054) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 1527397054 * (3 : ZMod 6109588217) ^ 1527397054 := by rw [pow_add]
          _ = 6109588216 := by rw [factor_0_30]; decide
      change (3 : ZMod 6109588217) ^ 3054794108 ≠ 1
      rw [factor_0_31]
      decide
    ·
      have factor_1_0 : (3 : ZMod 6109588217) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 6109588217) ^ 2 = 9 := by
        calc
          (3 : ZMod 6109588217) ^ 2 = (3 : ZMod 6109588217) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 1 * (3 : ZMod 6109588217) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 6109588217) ^ 4 = 81 := by
        calc
          (3 : ZMod 6109588217) ^ 4 = (3 : ZMod 6109588217) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 2 * (3 : ZMod 6109588217) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 6109588217) ^ 8 = 6561 := by
        calc
          (3 : ZMod 6109588217) ^ 8 = (3 : ZMod 6109588217) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 6109588217) ^ n) (by norm_num)
          _ = (3 : ZMod 6109588217) ^ 4 * (3 : ZMod 6109588217) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_1_2]; decide
      change (3 : ZMod 6109588217) ^ 8 ≠ 1
      rw [factor_1_3]
      decide

#print axioms prime_lucas_6109588217

end TotientTailPeriodKiller
end Erdos249257
