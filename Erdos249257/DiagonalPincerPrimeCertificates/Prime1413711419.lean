import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime100979387

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1413711419 : Nat.Prime 1413711419 := by
  apply lucas_primality 1413711419 (2 : ZMod 1413711419)
  ·
      have fermat_0 : (2 : ZMod 1413711419) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 1413711419) ^ 2 = 4 := by
        calc
          (2 : ZMod 1413711419) ^ 2 = (2 : ZMod 1413711419) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 1 * (2 : ZMod 1413711419) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 1413711419) ^ 5 = 32 := by
        calc
          (2 : ZMod 1413711419) ^ 5 = (2 : ZMod 1413711419) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 2 * (2 : ZMod 1413711419) ^ 2) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 1413711419) ^ 10 = 1024 := by
        calc
          (2 : ZMod 1413711419) ^ 10 = (2 : ZMod 1413711419) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 5 * (2 : ZMod 1413711419) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 1413711419) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 1413711419) ^ 21 = (2 : ZMod 1413711419) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 10 * (2 : ZMod 1413711419) ^ 10) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 1413711419) ^ 42 = 1403998014 := by
        calc
          (2 : ZMod 1413711419) ^ 42 = (2 : ZMod 1413711419) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 21 * (2 : ZMod 1413711419) ^ 21 := by rw [pow_add]
          _ = 1403998014 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 1413711419) ^ 84 = 550301384 := by
        calc
          (2 : ZMod 1413711419) ^ 84 = (2 : ZMod 1413711419) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 42 * (2 : ZMod 1413711419) ^ 42 := by rw [pow_add]
          _ = 550301384 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 1413711419) ^ 168 = 1024174482 := by
        calc
          (2 : ZMod 1413711419) ^ 168 = (2 : ZMod 1413711419) ^ (84 + 84) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 84 * (2 : ZMod 1413711419) ^ 84 := by rw [pow_add]
          _ = 1024174482 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 1413711419) ^ 337 = 441956767 := by
        calc
          (2 : ZMod 1413711419) ^ 337 = (2 : ZMod 1413711419) ^ (168 + 168 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 168 * (2 : ZMod 1413711419) ^ 168) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 441956767 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 1413711419) ^ 674 = 745371053 := by
        calc
          (2 : ZMod 1413711419) ^ 674 = (2 : ZMod 1413711419) ^ (337 + 337) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 337 * (2 : ZMod 1413711419) ^ 337 := by rw [pow_add]
          _ = 745371053 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 1413711419) ^ 1348 = 613300024 := by
        calc
          (2 : ZMod 1413711419) ^ 1348 = (2 : ZMod 1413711419) ^ (674 + 674) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 674 * (2 : ZMod 1413711419) ^ 674 := by rw [pow_add]
          _ = 613300024 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 1413711419) ^ 2696 = 373113473 := by
        calc
          (2 : ZMod 1413711419) ^ 2696 = (2 : ZMod 1413711419) ^ (1348 + 1348) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 1348 * (2 : ZMod 1413711419) ^ 1348 := by rw [pow_add]
          _ = 373113473 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 1413711419) ^ 5392 = 967771819 := by
        calc
          (2 : ZMod 1413711419) ^ 5392 = (2 : ZMod 1413711419) ^ (2696 + 2696) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 2696 * (2 : ZMod 1413711419) ^ 2696 := by rw [pow_add]
          _ = 967771819 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 1413711419) ^ 10785 = 846822629 := by
        calc
          (2 : ZMod 1413711419) ^ 10785 = (2 : ZMod 1413711419) ^ (5392 + 5392 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 5392 * (2 : ZMod 1413711419) ^ 5392) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 846822629 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 1413711419) ^ 21571 = 726852819 := by
        calc
          (2 : ZMod 1413711419) ^ 21571 = (2 : ZMod 1413711419) ^ (10785 + 10785 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 10785 * (2 : ZMod 1413711419) ^ 10785) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 726852819 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 1413711419) ^ 43143 = 418474753 := by
        calc
          (2 : ZMod 1413711419) ^ 43143 = (2 : ZMod 1413711419) ^ (21571 + 21571 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 21571 * (2 : ZMod 1413711419) ^ 21571) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 418474753 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 1413711419) ^ 86286 = 387238443 := by
        calc
          (2 : ZMod 1413711419) ^ 86286 = (2 : ZMod 1413711419) ^ (43143 + 43143) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 43143 * (2 : ZMod 1413711419) ^ 43143 := by rw [pow_add]
          _ = 387238443 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 1413711419) ^ 172572 = 285108367 := by
        calc
          (2 : ZMod 1413711419) ^ 172572 = (2 : ZMod 1413711419) ^ (86286 + 86286) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 86286 * (2 : ZMod 1413711419) ^ 86286 := by rw [pow_add]
          _ = 285108367 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 1413711419) ^ 345144 = 109038539 := by
        calc
          (2 : ZMod 1413711419) ^ 345144 = (2 : ZMod 1413711419) ^ (172572 + 172572) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 172572 * (2 : ZMod 1413711419) ^ 172572 := by rw [pow_add]
          _ = 109038539 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 1413711419) ^ 690288 = 889645124 := by
        calc
          (2 : ZMod 1413711419) ^ 690288 = (2 : ZMod 1413711419) ^ (345144 + 345144) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 345144 * (2 : ZMod 1413711419) ^ 345144 := by rw [pow_add]
          _ = 889645124 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 1413711419) ^ 1380577 = 358487875 := by
        calc
          (2 : ZMod 1413711419) ^ 1380577 = (2 : ZMod 1413711419) ^ (690288 + 690288 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 690288 * (2 : ZMod 1413711419) ^ 690288) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 358487875 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 1413711419) ^ 2761155 = 1038411439 := by
        calc
          (2 : ZMod 1413711419) ^ 2761155 = (2 : ZMod 1413711419) ^ (1380577 + 1380577 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 1380577 * (2 : ZMod 1413711419) ^ 1380577) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 1038411439 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 1413711419) ^ 5522310 = 256526839 := by
        calc
          (2 : ZMod 1413711419) ^ 5522310 = (2 : ZMod 1413711419) ^ (2761155 + 2761155) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 2761155 * (2 : ZMod 1413711419) ^ 2761155 := by rw [pow_add]
          _ = 256526839 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 1413711419) ^ 11044620 = 374038131 := by
        calc
          (2 : ZMod 1413711419) ^ 11044620 = (2 : ZMod 1413711419) ^ (5522310 + 5522310) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 5522310 * (2 : ZMod 1413711419) ^ 5522310 := by rw [pow_add]
          _ = 374038131 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 1413711419) ^ 22089240 = 1110829236 := by
        calc
          (2 : ZMod 1413711419) ^ 22089240 = (2 : ZMod 1413711419) ^ (11044620 + 11044620) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 11044620 * (2 : ZMod 1413711419) ^ 11044620 := by rw [pow_add]
          _ = 1110829236 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 1413711419) ^ 44178481 = 886362181 := by
        calc
          (2 : ZMod 1413711419) ^ 44178481 = (2 : ZMod 1413711419) ^ (22089240 + 22089240 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 22089240 * (2 : ZMod 1413711419) ^ 22089240) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 886362181 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 1413711419) ^ 88356963 = 1115326000 := by
        calc
          (2 : ZMod 1413711419) ^ 88356963 = (2 : ZMod 1413711419) ^ (44178481 + 44178481 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 44178481 * (2 : ZMod 1413711419) ^ 44178481) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 1115326000 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 1413711419) ^ 176713927 = 735528275 := by
        calc
          (2 : ZMod 1413711419) ^ 176713927 = (2 : ZMod 1413711419) ^ (88356963 + 88356963 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 88356963 * (2 : ZMod 1413711419) ^ 88356963) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 735528275 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 1413711419) ^ 353427854 = 764288575 := by
        calc
          (2 : ZMod 1413711419) ^ 353427854 = (2 : ZMod 1413711419) ^ (176713927 + 176713927) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 176713927 * (2 : ZMod 1413711419) ^ 176713927 := by rw [pow_add]
          _ = 764288575 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 1413711419) ^ 706855709 = 1413711418 := by
        calc
          (2 : ZMod 1413711419) ^ 706855709 = (2 : ZMod 1413711419) ^ (353427854 + 353427854 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 353427854 * (2 : ZMod 1413711419) ^ 353427854) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 1413711418 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 1413711419) ^ 1413711418 = 1 := by
        calc
          (2 : ZMod 1413711419) ^ 1413711418 = (2 : ZMod 1413711419) ^ (706855709 + 706855709) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 706855709 * (2 : ZMod 1413711419) ^ 706855709 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (100979387, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (100979387, 1)] : List FactorBlock).map factorBlockValue).prod = 1413711419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_100979387) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 1413711419) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 1413711419) ^ 2 = 4 := by
        calc
          (2 : ZMod 1413711419) ^ 2 = (2 : ZMod 1413711419) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 1 * (2 : ZMod 1413711419) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 1413711419) ^ 5 = 32 := by
        calc
          (2 : ZMod 1413711419) ^ 5 = (2 : ZMod 1413711419) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 2 * (2 : ZMod 1413711419) ^ 2) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 1413711419) ^ 10 = 1024 := by
        calc
          (2 : ZMod 1413711419) ^ 10 = (2 : ZMod 1413711419) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 5 * (2 : ZMod 1413711419) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 1413711419) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 1413711419) ^ 21 = (2 : ZMod 1413711419) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 10 * (2 : ZMod 1413711419) ^ 10) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 1413711419) ^ 42 = 1403998014 := by
        calc
          (2 : ZMod 1413711419) ^ 42 = (2 : ZMod 1413711419) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 21 * (2 : ZMod 1413711419) ^ 21 := by rw [pow_add]
          _ = 1403998014 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 1413711419) ^ 84 = 550301384 := by
        calc
          (2 : ZMod 1413711419) ^ 84 = (2 : ZMod 1413711419) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 42 * (2 : ZMod 1413711419) ^ 42 := by rw [pow_add]
          _ = 550301384 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 1413711419) ^ 168 = 1024174482 := by
        calc
          (2 : ZMod 1413711419) ^ 168 = (2 : ZMod 1413711419) ^ (84 + 84) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 84 * (2 : ZMod 1413711419) ^ 84 := by rw [pow_add]
          _ = 1024174482 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 1413711419) ^ 337 = 441956767 := by
        calc
          (2 : ZMod 1413711419) ^ 337 = (2 : ZMod 1413711419) ^ (168 + 168 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 168 * (2 : ZMod 1413711419) ^ 168) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 441956767 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 1413711419) ^ 674 = 745371053 := by
        calc
          (2 : ZMod 1413711419) ^ 674 = (2 : ZMod 1413711419) ^ (337 + 337) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 337 * (2 : ZMod 1413711419) ^ 337 := by rw [pow_add]
          _ = 745371053 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 1413711419) ^ 1348 = 613300024 := by
        calc
          (2 : ZMod 1413711419) ^ 1348 = (2 : ZMod 1413711419) ^ (674 + 674) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 674 * (2 : ZMod 1413711419) ^ 674 := by rw [pow_add]
          _ = 613300024 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 1413711419) ^ 2696 = 373113473 := by
        calc
          (2 : ZMod 1413711419) ^ 2696 = (2 : ZMod 1413711419) ^ (1348 + 1348) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 1348 * (2 : ZMod 1413711419) ^ 1348 := by rw [pow_add]
          _ = 373113473 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 1413711419) ^ 5392 = 967771819 := by
        calc
          (2 : ZMod 1413711419) ^ 5392 = (2 : ZMod 1413711419) ^ (2696 + 2696) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 2696 * (2 : ZMod 1413711419) ^ 2696 := by rw [pow_add]
          _ = 967771819 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 1413711419) ^ 10785 = 846822629 := by
        calc
          (2 : ZMod 1413711419) ^ 10785 = (2 : ZMod 1413711419) ^ (5392 + 5392 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 5392 * (2 : ZMod 1413711419) ^ 5392) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 846822629 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 1413711419) ^ 21571 = 726852819 := by
        calc
          (2 : ZMod 1413711419) ^ 21571 = (2 : ZMod 1413711419) ^ (10785 + 10785 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 10785 * (2 : ZMod 1413711419) ^ 10785) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 726852819 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 1413711419) ^ 43143 = 418474753 := by
        calc
          (2 : ZMod 1413711419) ^ 43143 = (2 : ZMod 1413711419) ^ (21571 + 21571 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 21571 * (2 : ZMod 1413711419) ^ 21571) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 418474753 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 1413711419) ^ 86286 = 387238443 := by
        calc
          (2 : ZMod 1413711419) ^ 86286 = (2 : ZMod 1413711419) ^ (43143 + 43143) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 43143 * (2 : ZMod 1413711419) ^ 43143 := by rw [pow_add]
          _ = 387238443 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 1413711419) ^ 172572 = 285108367 := by
        calc
          (2 : ZMod 1413711419) ^ 172572 = (2 : ZMod 1413711419) ^ (86286 + 86286) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 86286 * (2 : ZMod 1413711419) ^ 86286 := by rw [pow_add]
          _ = 285108367 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 1413711419) ^ 345144 = 109038539 := by
        calc
          (2 : ZMod 1413711419) ^ 345144 = (2 : ZMod 1413711419) ^ (172572 + 172572) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 172572 * (2 : ZMod 1413711419) ^ 172572 := by rw [pow_add]
          _ = 109038539 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 1413711419) ^ 690288 = 889645124 := by
        calc
          (2 : ZMod 1413711419) ^ 690288 = (2 : ZMod 1413711419) ^ (345144 + 345144) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 345144 * (2 : ZMod 1413711419) ^ 345144 := by rw [pow_add]
          _ = 889645124 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 1413711419) ^ 1380577 = 358487875 := by
        calc
          (2 : ZMod 1413711419) ^ 1380577 = (2 : ZMod 1413711419) ^ (690288 + 690288 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 690288 * (2 : ZMod 1413711419) ^ 690288) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 358487875 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 1413711419) ^ 2761155 = 1038411439 := by
        calc
          (2 : ZMod 1413711419) ^ 2761155 = (2 : ZMod 1413711419) ^ (1380577 + 1380577 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 1380577 * (2 : ZMod 1413711419) ^ 1380577) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 1038411439 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 1413711419) ^ 5522310 = 256526839 := by
        calc
          (2 : ZMod 1413711419) ^ 5522310 = (2 : ZMod 1413711419) ^ (2761155 + 2761155) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 2761155 * (2 : ZMod 1413711419) ^ 2761155 := by rw [pow_add]
          _ = 256526839 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 1413711419) ^ 11044620 = 374038131 := by
        calc
          (2 : ZMod 1413711419) ^ 11044620 = (2 : ZMod 1413711419) ^ (5522310 + 5522310) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 5522310 * (2 : ZMod 1413711419) ^ 5522310 := by rw [pow_add]
          _ = 374038131 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 1413711419) ^ 22089240 = 1110829236 := by
        calc
          (2 : ZMod 1413711419) ^ 22089240 = (2 : ZMod 1413711419) ^ (11044620 + 11044620) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 11044620 * (2 : ZMod 1413711419) ^ 11044620 := by rw [pow_add]
          _ = 1110829236 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 1413711419) ^ 44178481 = 886362181 := by
        calc
          (2 : ZMod 1413711419) ^ 44178481 = (2 : ZMod 1413711419) ^ (22089240 + 22089240 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 22089240 * (2 : ZMod 1413711419) ^ 22089240) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 886362181 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 1413711419) ^ 88356963 = 1115326000 := by
        calc
          (2 : ZMod 1413711419) ^ 88356963 = (2 : ZMod 1413711419) ^ (44178481 + 44178481 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 44178481 * (2 : ZMod 1413711419) ^ 44178481) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 1115326000 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 1413711419) ^ 176713927 = 735528275 := by
        calc
          (2 : ZMod 1413711419) ^ 176713927 = (2 : ZMod 1413711419) ^ (88356963 + 88356963 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 88356963 * (2 : ZMod 1413711419) ^ 88356963) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 735528275 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 1413711419) ^ 353427854 = 764288575 := by
        calc
          (2 : ZMod 1413711419) ^ 353427854 = (2 : ZMod 1413711419) ^ (176713927 + 176713927) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 176713927 * (2 : ZMod 1413711419) ^ 176713927 := by rw [pow_add]
          _ = 764288575 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 1413711419) ^ 706855709 = 1413711418 := by
        calc
          (2 : ZMod 1413711419) ^ 706855709 = (2 : ZMod 1413711419) ^ (353427854 + 353427854 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 353427854 * (2 : ZMod 1413711419) ^ 353427854) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 1413711418 := by rw [factor_0_28]; decide
      change (2 : ZMod 1413711419) ^ 706855709 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (2 : ZMod 1413711419) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 1413711419) ^ 3 = 8 := by
        calc
          (2 : ZMod 1413711419) ^ 3 = (2 : ZMod 1413711419) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 1 * (2 : ZMod 1413711419) ^ 1) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 1413711419) ^ 6 = 64 := by
        calc
          (2 : ZMod 1413711419) ^ 6 = (2 : ZMod 1413711419) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 3 * (2 : ZMod 1413711419) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 1413711419) ^ 12 = 4096 := by
        calc
          (2 : ZMod 1413711419) ^ 12 = (2 : ZMod 1413711419) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 6 * (2 : ZMod 1413711419) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 1413711419) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 1413711419) ^ 24 = (2 : ZMod 1413711419) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 12 * (2 : ZMod 1413711419) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 1413711419) ^ 48 = 792053499 := by
        calc
          (2 : ZMod 1413711419) ^ 48 = (2 : ZMod 1413711419) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 24 * (2 : ZMod 1413711419) ^ 24 := by rw [pow_add]
          _ = 792053499 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 1413711419) ^ 96 = 578466978 := by
        calc
          (2 : ZMod 1413711419) ^ 96 = (2 : ZMod 1413711419) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 48 * (2 : ZMod 1413711419) ^ 48 := by rw [pow_add]
          _ = 578466978 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 1413711419) ^ 192 = 813356959 := by
        calc
          (2 : ZMod 1413711419) ^ 192 = (2 : ZMod 1413711419) ^ (96 + 96) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 96 * (2 : ZMod 1413711419) ^ 96 := by rw [pow_add]
          _ = 813356959 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 1413711419) ^ 385 = 362102688 := by
        calc
          (2 : ZMod 1413711419) ^ 385 = (2 : ZMod 1413711419) ^ (192 + 192 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 192 * (2 : ZMod 1413711419) ^ 192) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 362102688 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 1413711419) ^ 770 = 1314866754 := by
        calc
          (2 : ZMod 1413711419) ^ 770 = (2 : ZMod 1413711419) ^ (385 + 385) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 385 * (2 : ZMod 1413711419) ^ 385 := by rw [pow_add]
          _ = 1314866754 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 1413711419) ^ 1540 = 740185381 := by
        calc
          (2 : ZMod 1413711419) ^ 1540 = (2 : ZMod 1413711419) ^ (770 + 770) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 770 * (2 : ZMod 1413711419) ^ 770 := by rw [pow_add]
          _ = 740185381 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 1413711419) ^ 3081 = 980096475 := by
        calc
          (2 : ZMod 1413711419) ^ 3081 = (2 : ZMod 1413711419) ^ (1540 + 1540 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 1540 * (2 : ZMod 1413711419) ^ 1540) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 980096475 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 1413711419) ^ 6163 = 428497548 := by
        calc
          (2 : ZMod 1413711419) ^ 6163 = (2 : ZMod 1413711419) ^ (3081 + 3081 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 3081 * (2 : ZMod 1413711419) ^ 3081) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 428497548 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 1413711419) ^ 12326 = 1248834080 := by
        calc
          (2 : ZMod 1413711419) ^ 12326 = (2 : ZMod 1413711419) ^ (6163 + 6163) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 6163 * (2 : ZMod 1413711419) ^ 6163 := by rw [pow_add]
          _ = 1248834080 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 1413711419) ^ 24653 = 249817918 := by
        calc
          (2 : ZMod 1413711419) ^ 24653 = (2 : ZMod 1413711419) ^ (12326 + 12326 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 12326 * (2 : ZMod 1413711419) ^ 12326) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 249817918 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 1413711419) ^ 49306 = 361235900 := by
        calc
          (2 : ZMod 1413711419) ^ 49306 = (2 : ZMod 1413711419) ^ (24653 + 24653) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 24653 * (2 : ZMod 1413711419) ^ 24653 := by rw [pow_add]
          _ = 361235900 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 1413711419) ^ 98612 = 1121177910 := by
        calc
          (2 : ZMod 1413711419) ^ 98612 = (2 : ZMod 1413711419) ^ (49306 + 49306) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 49306 * (2 : ZMod 1413711419) ^ 49306 := by rw [pow_add]
          _ = 1121177910 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 1413711419) ^ 197225 = 1118244701 := by
        calc
          (2 : ZMod 1413711419) ^ 197225 = (2 : ZMod 1413711419) ^ (98612 + 98612 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 98612 * (2 : ZMod 1413711419) ^ 98612) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 1118244701 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 1413711419) ^ 394450 = 892636503 := by
        calc
          (2 : ZMod 1413711419) ^ 394450 = (2 : ZMod 1413711419) ^ (197225 + 197225) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 197225 * (2 : ZMod 1413711419) ^ 197225 := by rw [pow_add]
          _ = 892636503 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 1413711419) ^ 788901 = 645236490 := by
        calc
          (2 : ZMod 1413711419) ^ 788901 = (2 : ZMod 1413711419) ^ (394450 + 394450 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 394450 * (2 : ZMod 1413711419) ^ 394450) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 645236490 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 1413711419) ^ 1577802 = 814315282 := by
        calc
          (2 : ZMod 1413711419) ^ 1577802 = (2 : ZMod 1413711419) ^ (788901 + 788901) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 788901 * (2 : ZMod 1413711419) ^ 788901 := by rw [pow_add]
          _ = 814315282 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 1413711419) ^ 3155605 = 934745018 := by
        calc
          (2 : ZMod 1413711419) ^ 3155605 = (2 : ZMod 1413711419) ^ (1577802 + 1577802 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 1577802 * (2 : ZMod 1413711419) ^ 1577802) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 934745018 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 1413711419) ^ 6311211 = 156439254 := by
        calc
          (2 : ZMod 1413711419) ^ 6311211 = (2 : ZMod 1413711419) ^ (3155605 + 3155605 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 3155605 * (2 : ZMod 1413711419) ^ 3155605) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 156439254 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 1413711419) ^ 12622423 = 898058693 := by
        calc
          (2 : ZMod 1413711419) ^ 12622423 = (2 : ZMod 1413711419) ^ (6311211 + 6311211 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 6311211 * (2 : ZMod 1413711419) ^ 6311211) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 898058693 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 1413711419) ^ 25244846 = 1129966289 := by
        calc
          (2 : ZMod 1413711419) ^ 25244846 = (2 : ZMod 1413711419) ^ (12622423 + 12622423) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 12622423 * (2 : ZMod 1413711419) ^ 12622423 := by rw [pow_add]
          _ = 1129966289 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 1413711419) ^ 50489693 = 368233953 := by
        calc
          (2 : ZMod 1413711419) ^ 50489693 = (2 : ZMod 1413711419) ^ (25244846 + 25244846 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 25244846 * (2 : ZMod 1413711419) ^ 25244846) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 368233953 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 1413711419) ^ 100979387 = 583415378 := by
        calc
          (2 : ZMod 1413711419) ^ 100979387 = (2 : ZMod 1413711419) ^ (50489693 + 50489693 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 50489693 * (2 : ZMod 1413711419) ^ 50489693) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 583415378 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 1413711419) ^ 201958774 = 1151070784 := by
        calc
          (2 : ZMod 1413711419) ^ 201958774 = (2 : ZMod 1413711419) ^ (100979387 + 100979387) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 100979387 * (2 : ZMod 1413711419) ^ 100979387 := by rw [pow_add]
          _ = 1151070784 := by rw [factor_1_26]; decide
      change (2 : ZMod 1413711419) ^ 201958774 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (2 : ZMod 1413711419) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 1413711419) ^ 3 = 8 := by
        calc
          (2 : ZMod 1413711419) ^ 3 = (2 : ZMod 1413711419) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 1 * (2 : ZMod 1413711419) ^ 1) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 1413711419) ^ 7 = 128 := by
        calc
          (2 : ZMod 1413711419) ^ 7 = (2 : ZMod 1413711419) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413711419) ^ 3 * (2 : ZMod 1413711419) ^ 3) * (2 : ZMod 1413711419) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 1413711419) ^ 14 = 16384 := by
        calc
          (2 : ZMod 1413711419) ^ 14 = (2 : ZMod 1413711419) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413711419) ^ n) (by norm_num)
          _ = (2 : ZMod 1413711419) ^ 7 * (2 : ZMod 1413711419) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_2_2]; decide
      change (2 : ZMod 1413711419) ^ 14 ≠ 1
      rw [factor_2_3]
      decide

#print axioms prime_lucas_1413711419

end TotientTailPeriodKiller
end Erdos249257
