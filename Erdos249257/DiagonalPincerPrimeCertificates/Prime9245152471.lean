import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime308171749

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_9245152471 : Nat.Prime 9245152471 := by
  apply lucas_primality 9245152471 (6 : ZMod 9245152471)
  ·
      have fermat_0 : (6 : ZMod 9245152471) ^ 1 = 6 := by norm_num
      have fermat_1 : (6 : ZMod 9245152471) ^ 2 = 36 := by
        calc
          (6 : ZMod 9245152471) ^ 2 = (6 : ZMod 9245152471) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 1 * (6 : ZMod 9245152471) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [fermat_0]; decide
      have fermat_2 : (6 : ZMod 9245152471) ^ 4 = 1296 := by
        calc
          (6 : ZMod 9245152471) ^ 4 = (6 : ZMod 9245152471) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 2 * (6 : ZMod 9245152471) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [fermat_1]; decide
      have fermat_3 : (6 : ZMod 9245152471) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 9245152471) ^ 8 = (6 : ZMod 9245152471) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 4 * (6 : ZMod 9245152471) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [fermat_2]; decide
      have fermat_4 : (6 : ZMod 9245152471) ^ 17 = 8030422806 := by
        calc
          (6 : ZMod 9245152471) ^ 17 = (6 : ZMod 9245152471) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 8 * (6 : ZMod 9245152471) ^ 8) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 8030422806 := by rw [fermat_3]; decide
      have fermat_5 : (6 : ZMod 9245152471) ^ 34 = 8834785892 := by
        calc
          (6 : ZMod 9245152471) ^ 34 = (6 : ZMod 9245152471) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 17 * (6 : ZMod 9245152471) ^ 17 := by rw [pow_add]
          _ = 8834785892 := by rw [fermat_4]; decide
      have fermat_6 : (6 : ZMod 9245152471) ^ 68 = 8791476582 := by
        calc
          (6 : ZMod 9245152471) ^ 68 = (6 : ZMod 9245152471) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 34 * (6 : ZMod 9245152471) ^ 34 := by rw [pow_add]
          _ = 8791476582 := by rw [fermat_5]; decide
      have fermat_7 : (6 : ZMod 9245152471) ^ 137 = 8042094615 := by
        calc
          (6 : ZMod 9245152471) ^ 137 = (6 : ZMod 9245152471) ^ (68 + 68 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 68 * (6 : ZMod 9245152471) ^ 68) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 8042094615 := by rw [fermat_6]; decide
      have fermat_8 : (6 : ZMod 9245152471) ^ 275 = 7401694006 := by
        calc
          (6 : ZMod 9245152471) ^ 275 = (6 : ZMod 9245152471) ^ (137 + 137 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 137 * (6 : ZMod 9245152471) ^ 137) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 7401694006 := by rw [fermat_7]; decide
      have fermat_9 : (6 : ZMod 9245152471) ^ 551 = 4109489638 := by
        calc
          (6 : ZMod 9245152471) ^ 551 = (6 : ZMod 9245152471) ^ (275 + 275 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 275 * (6 : ZMod 9245152471) ^ 275) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 4109489638 := by rw [fermat_8]; decide
      have fermat_10 : (6 : ZMod 9245152471) ^ 1102 = 6603469323 := by
        calc
          (6 : ZMod 9245152471) ^ 1102 = (6 : ZMod 9245152471) ^ (551 + 551) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 551 * (6 : ZMod 9245152471) ^ 551 := by rw [pow_add]
          _ = 6603469323 := by rw [fermat_9]; decide
      have fermat_11 : (6 : ZMod 9245152471) ^ 2204 = 753700236 := by
        calc
          (6 : ZMod 9245152471) ^ 2204 = (6 : ZMod 9245152471) ^ (1102 + 1102) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 1102 * (6 : ZMod 9245152471) ^ 1102 := by rw [pow_add]
          _ = 753700236 := by rw [fermat_10]; decide
      have fermat_12 : (6 : ZMod 9245152471) ^ 4408 = 6632674537 := by
        calc
          (6 : ZMod 9245152471) ^ 4408 = (6 : ZMod 9245152471) ^ (2204 + 2204) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 2204 * (6 : ZMod 9245152471) ^ 2204 := by rw [pow_add]
          _ = 6632674537 := by rw [fermat_11]; decide
      have fermat_13 : (6 : ZMod 9245152471) ^ 8816 = 7046855887 := by
        calc
          (6 : ZMod 9245152471) ^ 8816 = (6 : ZMod 9245152471) ^ (4408 + 4408) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 4408 * (6 : ZMod 9245152471) ^ 4408 := by rw [pow_add]
          _ = 7046855887 := by rw [fermat_12]; decide
      have fermat_14 : (6 : ZMod 9245152471) ^ 17633 = 813641695 := by
        calc
          (6 : ZMod 9245152471) ^ 17633 = (6 : ZMod 9245152471) ^ (8816 + 8816 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 8816 * (6 : ZMod 9245152471) ^ 8816) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 813641695 := by rw [fermat_13]; decide
      have fermat_15 : (6 : ZMod 9245152471) ^ 35267 = 4926995322 := by
        calc
          (6 : ZMod 9245152471) ^ 35267 = (6 : ZMod 9245152471) ^ (17633 + 17633 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 17633 * (6 : ZMod 9245152471) ^ 17633) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 4926995322 := by rw [fermat_14]; decide
      have fermat_16 : (6 : ZMod 9245152471) ^ 70534 = 5642578473 := by
        calc
          (6 : ZMod 9245152471) ^ 70534 = (6 : ZMod 9245152471) ^ (35267 + 35267) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 35267 * (6 : ZMod 9245152471) ^ 35267 := by rw [pow_add]
          _ = 5642578473 := by rw [fermat_15]; decide
      have fermat_17 : (6 : ZMod 9245152471) ^ 141069 = 3896969729 := by
        calc
          (6 : ZMod 9245152471) ^ 141069 = (6 : ZMod 9245152471) ^ (70534 + 70534 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 70534 * (6 : ZMod 9245152471) ^ 70534) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 3896969729 := by rw [fermat_16]; decide
      have fermat_18 : (6 : ZMod 9245152471) ^ 282139 = 823766202 := by
        calc
          (6 : ZMod 9245152471) ^ 282139 = (6 : ZMod 9245152471) ^ (141069 + 141069 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 141069 * (6 : ZMod 9245152471) ^ 141069) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 823766202 := by rw [fermat_17]; decide
      have fermat_19 : (6 : ZMod 9245152471) ^ 564279 = 1806639154 := by
        calc
          (6 : ZMod 9245152471) ^ 564279 = (6 : ZMod 9245152471) ^ (282139 + 282139 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 282139 * (6 : ZMod 9245152471) ^ 282139) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 1806639154 := by rw [fermat_18]; decide
      have fermat_20 : (6 : ZMod 9245152471) ^ 1128558 = 6238717389 := by
        calc
          (6 : ZMod 9245152471) ^ 1128558 = (6 : ZMod 9245152471) ^ (564279 + 564279) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 564279 * (6 : ZMod 9245152471) ^ 564279 := by rw [pow_add]
          _ = 6238717389 := by rw [fermat_19]; decide
      have fermat_21 : (6 : ZMod 9245152471) ^ 2257117 = 7579170452 := by
        calc
          (6 : ZMod 9245152471) ^ 2257117 = (6 : ZMod 9245152471) ^ (1128558 + 1128558 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 1128558 * (6 : ZMod 9245152471) ^ 1128558) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 7579170452 := by rw [fermat_20]; decide
      have fermat_22 : (6 : ZMod 9245152471) ^ 4514234 = 7456339143 := by
        calc
          (6 : ZMod 9245152471) ^ 4514234 = (6 : ZMod 9245152471) ^ (2257117 + 2257117) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 2257117 * (6 : ZMod 9245152471) ^ 2257117 := by rw [pow_add]
          _ = 7456339143 := by rw [fermat_21]; decide
      have fermat_23 : (6 : ZMod 9245152471) ^ 9028469 = 8309865688 := by
        calc
          (6 : ZMod 9245152471) ^ 9028469 = (6 : ZMod 9245152471) ^ (4514234 + 4514234 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 4514234 * (6 : ZMod 9245152471) ^ 4514234) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 8309865688 := by rw [fermat_22]; decide
      have fermat_24 : (6 : ZMod 9245152471) ^ 18056938 = 7550319638 := by
        calc
          (6 : ZMod 9245152471) ^ 18056938 = (6 : ZMod 9245152471) ^ (9028469 + 9028469) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 9028469 * (6 : ZMod 9245152471) ^ 9028469 := by rw [pow_add]
          _ = 7550319638 := by rw [fermat_23]; decide
      have fermat_25 : (6 : ZMod 9245152471) ^ 36113876 = 7794075300 := by
        calc
          (6 : ZMod 9245152471) ^ 36113876 = (6 : ZMod 9245152471) ^ (18056938 + 18056938) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 18056938 * (6 : ZMod 9245152471) ^ 18056938 := by rw [pow_add]
          _ = 7794075300 := by rw [fermat_24]; decide
      have fermat_26 : (6 : ZMod 9245152471) ^ 72227753 = 6058160126 := by
        calc
          (6 : ZMod 9245152471) ^ 72227753 = (6 : ZMod 9245152471) ^ (36113876 + 36113876 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 36113876 * (6 : ZMod 9245152471) ^ 36113876) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 6058160126 := by rw [fermat_25]; decide
      have fermat_27 : (6 : ZMod 9245152471) ^ 144455507 = 6362957382 := by
        calc
          (6 : ZMod 9245152471) ^ 144455507 = (6 : ZMod 9245152471) ^ (72227753 + 72227753 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 72227753 * (6 : ZMod 9245152471) ^ 72227753) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 6362957382 := by rw [fermat_26]; decide
      have fermat_28 : (6 : ZMod 9245152471) ^ 288911014 = 7915490670 := by
        calc
          (6 : ZMod 9245152471) ^ 288911014 = (6 : ZMod 9245152471) ^ (144455507 + 144455507) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 144455507 * (6 : ZMod 9245152471) ^ 144455507 := by rw [pow_add]
          _ = 7915490670 := by rw [fermat_27]; decide
      have fermat_29 : (6 : ZMod 9245152471) ^ 577822029 = 1348022598 := by
        calc
          (6 : ZMod 9245152471) ^ 577822029 = (6 : ZMod 9245152471) ^ (288911014 + 288911014 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 288911014 * (6 : ZMod 9245152471) ^ 288911014) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 1348022598 := by rw [fermat_28]; decide
      have fermat_30 : (6 : ZMod 9245152471) ^ 1155644058 = 2630496847 := by
        calc
          (6 : ZMod 9245152471) ^ 1155644058 = (6 : ZMod 9245152471) ^ (577822029 + 577822029) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 577822029 * (6 : ZMod 9245152471) ^ 577822029 := by rw [pow_add]
          _ = 2630496847 := by rw [fermat_29]; decide
      have fermat_31 : (6 : ZMod 9245152471) ^ 2311288117 = 7300853752 := by
        calc
          (6 : ZMod 9245152471) ^ 2311288117 = (6 : ZMod 9245152471) ^ (1155644058 + 1155644058 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 1155644058 * (6 : ZMod 9245152471) ^ 1155644058) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 7300853752 := by rw [fermat_30]; decide
      have fermat_32 : (6 : ZMod 9245152471) ^ 4622576235 = 9245152470 := by
        calc
          (6 : ZMod 9245152471) ^ 4622576235 = (6 : ZMod 9245152471) ^ (2311288117 + 2311288117 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 2311288117 * (6 : ZMod 9245152471) ^ 2311288117) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 9245152470 := by rw [fermat_31]; decide
      have fermat_33 : (6 : ZMod 9245152471) ^ 9245152470 = 1 := by
        calc
          (6 : ZMod 9245152471) ^ 9245152470 = (6 : ZMod 9245152471) ^ (4622576235 + 4622576235) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 4622576235 * (6 : ZMod 9245152471) ^ 4622576235 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (308171749, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (308171749, 1)] : List FactorBlock).map factorBlockValue).prod = 9245152471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_308171749) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (6 : ZMod 9245152471) ^ 1 = 6 := by norm_num
      have factor_0_1 : (6 : ZMod 9245152471) ^ 2 = 36 := by
        calc
          (6 : ZMod 9245152471) ^ 2 = (6 : ZMod 9245152471) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 1 * (6 : ZMod 9245152471) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_0_0]; decide
      have factor_0_2 : (6 : ZMod 9245152471) ^ 4 = 1296 := by
        calc
          (6 : ZMod 9245152471) ^ 4 = (6 : ZMod 9245152471) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 2 * (6 : ZMod 9245152471) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_0_1]; decide
      have factor_0_3 : (6 : ZMod 9245152471) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 9245152471) ^ 8 = (6 : ZMod 9245152471) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 4 * (6 : ZMod 9245152471) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_0_2]; decide
      have factor_0_4 : (6 : ZMod 9245152471) ^ 17 = 8030422806 := by
        calc
          (6 : ZMod 9245152471) ^ 17 = (6 : ZMod 9245152471) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 8 * (6 : ZMod 9245152471) ^ 8) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 8030422806 := by rw [factor_0_3]; decide
      have factor_0_5 : (6 : ZMod 9245152471) ^ 34 = 8834785892 := by
        calc
          (6 : ZMod 9245152471) ^ 34 = (6 : ZMod 9245152471) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 17 * (6 : ZMod 9245152471) ^ 17 := by rw [pow_add]
          _ = 8834785892 := by rw [factor_0_4]; decide
      have factor_0_6 : (6 : ZMod 9245152471) ^ 68 = 8791476582 := by
        calc
          (6 : ZMod 9245152471) ^ 68 = (6 : ZMod 9245152471) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 34 * (6 : ZMod 9245152471) ^ 34 := by rw [pow_add]
          _ = 8791476582 := by rw [factor_0_5]; decide
      have factor_0_7 : (6 : ZMod 9245152471) ^ 137 = 8042094615 := by
        calc
          (6 : ZMod 9245152471) ^ 137 = (6 : ZMod 9245152471) ^ (68 + 68 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 68 * (6 : ZMod 9245152471) ^ 68) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 8042094615 := by rw [factor_0_6]; decide
      have factor_0_8 : (6 : ZMod 9245152471) ^ 275 = 7401694006 := by
        calc
          (6 : ZMod 9245152471) ^ 275 = (6 : ZMod 9245152471) ^ (137 + 137 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 137 * (6 : ZMod 9245152471) ^ 137) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 7401694006 := by rw [factor_0_7]; decide
      have factor_0_9 : (6 : ZMod 9245152471) ^ 551 = 4109489638 := by
        calc
          (6 : ZMod 9245152471) ^ 551 = (6 : ZMod 9245152471) ^ (275 + 275 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 275 * (6 : ZMod 9245152471) ^ 275) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 4109489638 := by rw [factor_0_8]; decide
      have factor_0_10 : (6 : ZMod 9245152471) ^ 1102 = 6603469323 := by
        calc
          (6 : ZMod 9245152471) ^ 1102 = (6 : ZMod 9245152471) ^ (551 + 551) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 551 * (6 : ZMod 9245152471) ^ 551 := by rw [pow_add]
          _ = 6603469323 := by rw [factor_0_9]; decide
      have factor_0_11 : (6 : ZMod 9245152471) ^ 2204 = 753700236 := by
        calc
          (6 : ZMod 9245152471) ^ 2204 = (6 : ZMod 9245152471) ^ (1102 + 1102) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 1102 * (6 : ZMod 9245152471) ^ 1102 := by rw [pow_add]
          _ = 753700236 := by rw [factor_0_10]; decide
      have factor_0_12 : (6 : ZMod 9245152471) ^ 4408 = 6632674537 := by
        calc
          (6 : ZMod 9245152471) ^ 4408 = (6 : ZMod 9245152471) ^ (2204 + 2204) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 2204 * (6 : ZMod 9245152471) ^ 2204 := by rw [pow_add]
          _ = 6632674537 := by rw [factor_0_11]; decide
      have factor_0_13 : (6 : ZMod 9245152471) ^ 8816 = 7046855887 := by
        calc
          (6 : ZMod 9245152471) ^ 8816 = (6 : ZMod 9245152471) ^ (4408 + 4408) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 4408 * (6 : ZMod 9245152471) ^ 4408 := by rw [pow_add]
          _ = 7046855887 := by rw [factor_0_12]; decide
      have factor_0_14 : (6 : ZMod 9245152471) ^ 17633 = 813641695 := by
        calc
          (6 : ZMod 9245152471) ^ 17633 = (6 : ZMod 9245152471) ^ (8816 + 8816 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 8816 * (6 : ZMod 9245152471) ^ 8816) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 813641695 := by rw [factor_0_13]; decide
      have factor_0_15 : (6 : ZMod 9245152471) ^ 35267 = 4926995322 := by
        calc
          (6 : ZMod 9245152471) ^ 35267 = (6 : ZMod 9245152471) ^ (17633 + 17633 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 17633 * (6 : ZMod 9245152471) ^ 17633) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 4926995322 := by rw [factor_0_14]; decide
      have factor_0_16 : (6 : ZMod 9245152471) ^ 70534 = 5642578473 := by
        calc
          (6 : ZMod 9245152471) ^ 70534 = (6 : ZMod 9245152471) ^ (35267 + 35267) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 35267 * (6 : ZMod 9245152471) ^ 35267 := by rw [pow_add]
          _ = 5642578473 := by rw [factor_0_15]; decide
      have factor_0_17 : (6 : ZMod 9245152471) ^ 141069 = 3896969729 := by
        calc
          (6 : ZMod 9245152471) ^ 141069 = (6 : ZMod 9245152471) ^ (70534 + 70534 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 70534 * (6 : ZMod 9245152471) ^ 70534) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 3896969729 := by rw [factor_0_16]; decide
      have factor_0_18 : (6 : ZMod 9245152471) ^ 282139 = 823766202 := by
        calc
          (6 : ZMod 9245152471) ^ 282139 = (6 : ZMod 9245152471) ^ (141069 + 141069 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 141069 * (6 : ZMod 9245152471) ^ 141069) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 823766202 := by rw [factor_0_17]; decide
      have factor_0_19 : (6 : ZMod 9245152471) ^ 564279 = 1806639154 := by
        calc
          (6 : ZMod 9245152471) ^ 564279 = (6 : ZMod 9245152471) ^ (282139 + 282139 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 282139 * (6 : ZMod 9245152471) ^ 282139) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 1806639154 := by rw [factor_0_18]; decide
      have factor_0_20 : (6 : ZMod 9245152471) ^ 1128558 = 6238717389 := by
        calc
          (6 : ZMod 9245152471) ^ 1128558 = (6 : ZMod 9245152471) ^ (564279 + 564279) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 564279 * (6 : ZMod 9245152471) ^ 564279 := by rw [pow_add]
          _ = 6238717389 := by rw [factor_0_19]; decide
      have factor_0_21 : (6 : ZMod 9245152471) ^ 2257117 = 7579170452 := by
        calc
          (6 : ZMod 9245152471) ^ 2257117 = (6 : ZMod 9245152471) ^ (1128558 + 1128558 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 1128558 * (6 : ZMod 9245152471) ^ 1128558) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 7579170452 := by rw [factor_0_20]; decide
      have factor_0_22 : (6 : ZMod 9245152471) ^ 4514234 = 7456339143 := by
        calc
          (6 : ZMod 9245152471) ^ 4514234 = (6 : ZMod 9245152471) ^ (2257117 + 2257117) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 2257117 * (6 : ZMod 9245152471) ^ 2257117 := by rw [pow_add]
          _ = 7456339143 := by rw [factor_0_21]; decide
      have factor_0_23 : (6 : ZMod 9245152471) ^ 9028469 = 8309865688 := by
        calc
          (6 : ZMod 9245152471) ^ 9028469 = (6 : ZMod 9245152471) ^ (4514234 + 4514234 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 4514234 * (6 : ZMod 9245152471) ^ 4514234) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 8309865688 := by rw [factor_0_22]; decide
      have factor_0_24 : (6 : ZMod 9245152471) ^ 18056938 = 7550319638 := by
        calc
          (6 : ZMod 9245152471) ^ 18056938 = (6 : ZMod 9245152471) ^ (9028469 + 9028469) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 9028469 * (6 : ZMod 9245152471) ^ 9028469 := by rw [pow_add]
          _ = 7550319638 := by rw [factor_0_23]; decide
      have factor_0_25 : (6 : ZMod 9245152471) ^ 36113876 = 7794075300 := by
        calc
          (6 : ZMod 9245152471) ^ 36113876 = (6 : ZMod 9245152471) ^ (18056938 + 18056938) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 18056938 * (6 : ZMod 9245152471) ^ 18056938 := by rw [pow_add]
          _ = 7794075300 := by rw [factor_0_24]; decide
      have factor_0_26 : (6 : ZMod 9245152471) ^ 72227753 = 6058160126 := by
        calc
          (6 : ZMod 9245152471) ^ 72227753 = (6 : ZMod 9245152471) ^ (36113876 + 36113876 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 36113876 * (6 : ZMod 9245152471) ^ 36113876) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 6058160126 := by rw [factor_0_25]; decide
      have factor_0_27 : (6 : ZMod 9245152471) ^ 144455507 = 6362957382 := by
        calc
          (6 : ZMod 9245152471) ^ 144455507 = (6 : ZMod 9245152471) ^ (72227753 + 72227753 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 72227753 * (6 : ZMod 9245152471) ^ 72227753) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 6362957382 := by rw [factor_0_26]; decide
      have factor_0_28 : (6 : ZMod 9245152471) ^ 288911014 = 7915490670 := by
        calc
          (6 : ZMod 9245152471) ^ 288911014 = (6 : ZMod 9245152471) ^ (144455507 + 144455507) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 144455507 * (6 : ZMod 9245152471) ^ 144455507 := by rw [pow_add]
          _ = 7915490670 := by rw [factor_0_27]; decide
      have factor_0_29 : (6 : ZMod 9245152471) ^ 577822029 = 1348022598 := by
        calc
          (6 : ZMod 9245152471) ^ 577822029 = (6 : ZMod 9245152471) ^ (288911014 + 288911014 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 288911014 * (6 : ZMod 9245152471) ^ 288911014) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 1348022598 := by rw [factor_0_28]; decide
      have factor_0_30 : (6 : ZMod 9245152471) ^ 1155644058 = 2630496847 := by
        calc
          (6 : ZMod 9245152471) ^ 1155644058 = (6 : ZMod 9245152471) ^ (577822029 + 577822029) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 577822029 * (6 : ZMod 9245152471) ^ 577822029 := by rw [pow_add]
          _ = 2630496847 := by rw [factor_0_29]; decide
      have factor_0_31 : (6 : ZMod 9245152471) ^ 2311288117 = 7300853752 := by
        calc
          (6 : ZMod 9245152471) ^ 2311288117 = (6 : ZMod 9245152471) ^ (1155644058 + 1155644058 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 1155644058 * (6 : ZMod 9245152471) ^ 1155644058) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 7300853752 := by rw [factor_0_30]; decide
      have factor_0_32 : (6 : ZMod 9245152471) ^ 4622576235 = 9245152470 := by
        calc
          (6 : ZMod 9245152471) ^ 4622576235 = (6 : ZMod 9245152471) ^ (2311288117 + 2311288117 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 2311288117 * (6 : ZMod 9245152471) ^ 2311288117) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 9245152470 := by rw [factor_0_31]; decide
      change (6 : ZMod 9245152471) ^ 4622576235 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (6 : ZMod 9245152471) ^ 1 = 6 := by norm_num
      have factor_1_1 : (6 : ZMod 9245152471) ^ 2 = 36 := by
        calc
          (6 : ZMod 9245152471) ^ 2 = (6 : ZMod 9245152471) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 1 * (6 : ZMod 9245152471) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_1_0]; decide
      have factor_1_2 : (6 : ZMod 9245152471) ^ 5 = 7776 := by
        calc
          (6 : ZMod 9245152471) ^ 5 = (6 : ZMod 9245152471) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 2 * (6 : ZMod 9245152471) ^ 2) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_1_1]; decide
      have factor_1_3 : (6 : ZMod 9245152471) ^ 11 = 362797056 := by
        calc
          (6 : ZMod 9245152471) ^ 11 = (6 : ZMod 9245152471) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 5 * (6 : ZMod 9245152471) ^ 5) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 362797056 := by rw [factor_1_2]; decide
      have factor_1_4 : (6 : ZMod 9245152471) ^ 22 = 2807950322 := by
        calc
          (6 : ZMod 9245152471) ^ 22 = (6 : ZMod 9245152471) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 11 * (6 : ZMod 9245152471) ^ 11 := by rw [pow_add]
          _ = 2807950322 := by rw [factor_1_3]; decide
      have factor_1_5 : (6 : ZMod 9245152471) ^ 45 = 6822685568 := by
        calc
          (6 : ZMod 9245152471) ^ 45 = (6 : ZMod 9245152471) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 22 * (6 : ZMod 9245152471) ^ 22) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 6822685568 := by rw [factor_1_4]; decide
      have factor_1_6 : (6 : ZMod 9245152471) ^ 91 = 1437138012 := by
        calc
          (6 : ZMod 9245152471) ^ 91 = (6 : ZMod 9245152471) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 45 * (6 : ZMod 9245152471) ^ 45) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 1437138012 := by rw [factor_1_5]; decide
      have factor_1_7 : (6 : ZMod 9245152471) ^ 183 = 6436764061 := by
        calc
          (6 : ZMod 9245152471) ^ 183 = (6 : ZMod 9245152471) ^ (91 + 91 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 91 * (6 : ZMod 9245152471) ^ 91) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 6436764061 := by rw [factor_1_6]; decide
      have factor_1_8 : (6 : ZMod 9245152471) ^ 367 = 4745776909 := by
        calc
          (6 : ZMod 9245152471) ^ 367 = (6 : ZMod 9245152471) ^ (183 + 183 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 183 * (6 : ZMod 9245152471) ^ 183) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 4745776909 := by rw [factor_1_7]; decide
      have factor_1_9 : (6 : ZMod 9245152471) ^ 734 = 3534980521 := by
        calc
          (6 : ZMod 9245152471) ^ 734 = (6 : ZMod 9245152471) ^ (367 + 367) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 367 * (6 : ZMod 9245152471) ^ 367 := by rw [pow_add]
          _ = 3534980521 := by rw [factor_1_8]; decide
      have factor_1_10 : (6 : ZMod 9245152471) ^ 1469 = 5655175177 := by
        calc
          (6 : ZMod 9245152471) ^ 1469 = (6 : ZMod 9245152471) ^ (734 + 734 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 734 * (6 : ZMod 9245152471) ^ 734) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 5655175177 := by rw [factor_1_9]; decide
      have factor_1_11 : (6 : ZMod 9245152471) ^ 2938 = 1305097306 := by
        calc
          (6 : ZMod 9245152471) ^ 2938 = (6 : ZMod 9245152471) ^ (1469 + 1469) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 1469 * (6 : ZMod 9245152471) ^ 1469 := by rw [pow_add]
          _ = 1305097306 := by rw [factor_1_10]; decide
      have factor_1_12 : (6 : ZMod 9245152471) ^ 5877 = 8489744032 := by
        calc
          (6 : ZMod 9245152471) ^ 5877 = (6 : ZMod 9245152471) ^ (2938 + 2938 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 2938 * (6 : ZMod 9245152471) ^ 2938) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 8489744032 := by rw [factor_1_11]; decide
      have factor_1_13 : (6 : ZMod 9245152471) ^ 11755 = 301458133 := by
        calc
          (6 : ZMod 9245152471) ^ 11755 = (6 : ZMod 9245152471) ^ (5877 + 5877 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 5877 * (6 : ZMod 9245152471) ^ 5877) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 301458133 := by rw [factor_1_12]; decide
      have factor_1_14 : (6 : ZMod 9245152471) ^ 23511 = 277803129 := by
        calc
          (6 : ZMod 9245152471) ^ 23511 = (6 : ZMod 9245152471) ^ (11755 + 11755 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 11755 * (6 : ZMod 9245152471) ^ 11755) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 277803129 := by rw [factor_1_13]; decide
      have factor_1_15 : (6 : ZMod 9245152471) ^ 47023 = 6232088903 := by
        calc
          (6 : ZMod 9245152471) ^ 47023 = (6 : ZMod 9245152471) ^ (23511 + 23511 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 23511 * (6 : ZMod 9245152471) ^ 23511) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 6232088903 := by rw [factor_1_14]; decide
      have factor_1_16 : (6 : ZMod 9245152471) ^ 94046 = 5636899453 := by
        calc
          (6 : ZMod 9245152471) ^ 94046 = (6 : ZMod 9245152471) ^ (47023 + 47023) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 47023 * (6 : ZMod 9245152471) ^ 47023 := by rw [pow_add]
          _ = 5636899453 := by rw [factor_1_15]; decide
      have factor_1_17 : (6 : ZMod 9245152471) ^ 188093 = 5408837850 := by
        calc
          (6 : ZMod 9245152471) ^ 188093 = (6 : ZMod 9245152471) ^ (94046 + 94046 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 94046 * (6 : ZMod 9245152471) ^ 94046) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 5408837850 := by rw [factor_1_16]; decide
      have factor_1_18 : (6 : ZMod 9245152471) ^ 376186 = 4860896971 := by
        calc
          (6 : ZMod 9245152471) ^ 376186 = (6 : ZMod 9245152471) ^ (188093 + 188093) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 188093 * (6 : ZMod 9245152471) ^ 188093 := by rw [pow_add]
          _ = 4860896971 := by rw [factor_1_17]; decide
      have factor_1_19 : (6 : ZMod 9245152471) ^ 752372 = 3893530497 := by
        calc
          (6 : ZMod 9245152471) ^ 752372 = (6 : ZMod 9245152471) ^ (376186 + 376186) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 376186 * (6 : ZMod 9245152471) ^ 376186 := by rw [pow_add]
          _ = 3893530497 := by rw [factor_1_18]; decide
      have factor_1_20 : (6 : ZMod 9245152471) ^ 1504744 = 1859623151 := by
        calc
          (6 : ZMod 9245152471) ^ 1504744 = (6 : ZMod 9245152471) ^ (752372 + 752372) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 752372 * (6 : ZMod 9245152471) ^ 752372 := by rw [pow_add]
          _ = 1859623151 := by rw [factor_1_19]; decide
      have factor_1_21 : (6 : ZMod 9245152471) ^ 3009489 = 6838964658 := by
        calc
          (6 : ZMod 9245152471) ^ 3009489 = (6 : ZMod 9245152471) ^ (1504744 + 1504744 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 1504744 * (6 : ZMod 9245152471) ^ 1504744) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 6838964658 := by rw [factor_1_20]; decide
      have factor_1_22 : (6 : ZMod 9245152471) ^ 6018979 = 571482510 := by
        calc
          (6 : ZMod 9245152471) ^ 6018979 = (6 : ZMod 9245152471) ^ (3009489 + 3009489 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 3009489 * (6 : ZMod 9245152471) ^ 3009489) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 571482510 := by rw [factor_1_21]; decide
      have factor_1_23 : (6 : ZMod 9245152471) ^ 12037958 = 9243440307 := by
        calc
          (6 : ZMod 9245152471) ^ 12037958 = (6 : ZMod 9245152471) ^ (6018979 + 6018979) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 6018979 * (6 : ZMod 9245152471) ^ 6018979 := by rw [pow_add]
          _ = 9243440307 := by rw [factor_1_22]; decide
      have factor_1_24 : (6 : ZMod 9245152471) ^ 24075917 = 4753377534 := by
        calc
          (6 : ZMod 9245152471) ^ 24075917 = (6 : ZMod 9245152471) ^ (12037958 + 12037958 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 12037958 * (6 : ZMod 9245152471) ^ 12037958) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 4753377534 := by rw [factor_1_23]; decide
      have factor_1_25 : (6 : ZMod 9245152471) ^ 48151835 = 8716207864 := by
        calc
          (6 : ZMod 9245152471) ^ 48151835 = (6 : ZMod 9245152471) ^ (24075917 + 24075917 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 24075917 * (6 : ZMod 9245152471) ^ 24075917) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 8716207864 := by rw [factor_1_24]; decide
      have factor_1_26 : (6 : ZMod 9245152471) ^ 96303671 = 8523577435 := by
        calc
          (6 : ZMod 9245152471) ^ 96303671 = (6 : ZMod 9245152471) ^ (48151835 + 48151835 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 48151835 * (6 : ZMod 9245152471) ^ 48151835) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 8523577435 := by rw [factor_1_25]; decide
      have factor_1_27 : (6 : ZMod 9245152471) ^ 192607343 = 1453325585 := by
        calc
          (6 : ZMod 9245152471) ^ 192607343 = (6 : ZMod 9245152471) ^ (96303671 + 96303671 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 96303671 * (6 : ZMod 9245152471) ^ 96303671) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 1453325585 := by rw [factor_1_26]; decide
      have factor_1_28 : (6 : ZMod 9245152471) ^ 385214686 = 2788618940 := by
        calc
          (6 : ZMod 9245152471) ^ 385214686 = (6 : ZMod 9245152471) ^ (192607343 + 192607343) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 192607343 * (6 : ZMod 9245152471) ^ 192607343 := by rw [pow_add]
          _ = 2788618940 := by rw [factor_1_27]; decide
      have factor_1_29 : (6 : ZMod 9245152471) ^ 770429372 = 7336617864 := by
        calc
          (6 : ZMod 9245152471) ^ 770429372 = (6 : ZMod 9245152471) ^ (385214686 + 385214686) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 385214686 * (6 : ZMod 9245152471) ^ 385214686 := by rw [pow_add]
          _ = 7336617864 := by rw [factor_1_28]; decide
      have factor_1_30 : (6 : ZMod 9245152471) ^ 1540858745 = 7803895721 := by
        calc
          (6 : ZMod 9245152471) ^ 1540858745 = (6 : ZMod 9245152471) ^ (770429372 + 770429372 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 770429372 * (6 : ZMod 9245152471) ^ 770429372) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 7803895721 := by rw [factor_1_29]; decide
      have factor_1_31 : (6 : ZMod 9245152471) ^ 3081717490 = 7803895720 := by
        calc
          (6 : ZMod 9245152471) ^ 3081717490 = (6 : ZMod 9245152471) ^ (1540858745 + 1540858745) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 1540858745 * (6 : ZMod 9245152471) ^ 1540858745 := by rw [pow_add]
          _ = 7803895720 := by rw [factor_1_30]; decide
      change (6 : ZMod 9245152471) ^ 3081717490 ≠ 1
      rw [factor_1_31]
      decide
    ·
      have factor_2_0 : (6 : ZMod 9245152471) ^ 1 = 6 := by norm_num
      have factor_2_1 : (6 : ZMod 9245152471) ^ 3 = 216 := by
        calc
          (6 : ZMod 9245152471) ^ 3 = (6 : ZMod 9245152471) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 1 * (6 : ZMod 9245152471) ^ 1) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_2_0]; decide
      have factor_2_2 : (6 : ZMod 9245152471) ^ 6 = 46656 := by
        calc
          (6 : ZMod 9245152471) ^ 6 = (6 : ZMod 9245152471) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 3 * (6 : ZMod 9245152471) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [factor_2_1]; decide
      have factor_2_3 : (6 : ZMod 9245152471) ^ 13 = 3815541545 := by
        calc
          (6 : ZMod 9245152471) ^ 13 = (6 : ZMod 9245152471) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 6 * (6 : ZMod 9245152471) ^ 6) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 3815541545 := by rw [factor_2_2]; decide
      have factor_2_4 : (6 : ZMod 9245152471) ^ 27 = 6816719841 := by
        calc
          (6 : ZMod 9245152471) ^ 27 = (6 : ZMod 9245152471) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 13 * (6 : ZMod 9245152471) ^ 13) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 6816719841 := by rw [factor_2_3]; decide
      have factor_2_5 : (6 : ZMod 9245152471) ^ 55 = 1151980120 := by
        calc
          (6 : ZMod 9245152471) ^ 55 = (6 : ZMod 9245152471) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 27 * (6 : ZMod 9245152471) ^ 27) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 1151980120 := by rw [factor_2_4]; decide
      have factor_2_6 : (6 : ZMod 9245152471) ^ 110 = 6409367646 := by
        calc
          (6 : ZMod 9245152471) ^ 110 = (6 : ZMod 9245152471) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 55 * (6 : ZMod 9245152471) ^ 55 := by rw [pow_add]
          _ = 6409367646 := by rw [factor_2_5]; decide
      have factor_2_7 : (6 : ZMod 9245152471) ^ 220 = 8784314555 := by
        calc
          (6 : ZMod 9245152471) ^ 220 = (6 : ZMod 9245152471) ^ (110 + 110) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 110 * (6 : ZMod 9245152471) ^ 110 := by rw [pow_add]
          _ = 8784314555 := by rw [factor_2_6]; decide
      have factor_2_8 : (6 : ZMod 9245152471) ^ 440 = 4032365768 := by
        calc
          (6 : ZMod 9245152471) ^ 440 = (6 : ZMod 9245152471) ^ (220 + 220) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 220 * (6 : ZMod 9245152471) ^ 220 := by rw [pow_add]
          _ = 4032365768 := by rw [factor_2_7]; decide
      have factor_2_9 : (6 : ZMod 9245152471) ^ 881 = 5503859141 := by
        calc
          (6 : ZMod 9245152471) ^ 881 = (6 : ZMod 9245152471) ^ (440 + 440 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 440 * (6 : ZMod 9245152471) ^ 440) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 5503859141 := by rw [factor_2_8]; decide
      have factor_2_10 : (6 : ZMod 9245152471) ^ 1763 = 7147511626 := by
        calc
          (6 : ZMod 9245152471) ^ 1763 = (6 : ZMod 9245152471) ^ (881 + 881 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 881 * (6 : ZMod 9245152471) ^ 881) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 7147511626 := by rw [factor_2_9]; decide
      have factor_2_11 : (6 : ZMod 9245152471) ^ 3526 = 196666193 := by
        calc
          (6 : ZMod 9245152471) ^ 3526 = (6 : ZMod 9245152471) ^ (1763 + 1763) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 1763 * (6 : ZMod 9245152471) ^ 1763 := by rw [pow_add]
          _ = 196666193 := by rw [factor_2_10]; decide
      have factor_2_12 : (6 : ZMod 9245152471) ^ 7053 = 8946165303 := by
        calc
          (6 : ZMod 9245152471) ^ 7053 = (6 : ZMod 9245152471) ^ (3526 + 3526 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 3526 * (6 : ZMod 9245152471) ^ 3526) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 8946165303 := by rw [factor_2_11]; decide
      have factor_2_13 : (6 : ZMod 9245152471) ^ 14106 = 5904542314 := by
        calc
          (6 : ZMod 9245152471) ^ 14106 = (6 : ZMod 9245152471) ^ (7053 + 7053) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 7053 * (6 : ZMod 9245152471) ^ 7053 := by rw [pow_add]
          _ = 5904542314 := by rw [factor_2_12]; decide
      have factor_2_14 : (6 : ZMod 9245152471) ^ 28213 = 5853150088 := by
        calc
          (6 : ZMod 9245152471) ^ 28213 = (6 : ZMod 9245152471) ^ (14106 + 14106 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 14106 * (6 : ZMod 9245152471) ^ 14106) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 5853150088 := by rw [factor_2_13]; decide
      have factor_2_15 : (6 : ZMod 9245152471) ^ 56427 = 5289686758 := by
        calc
          (6 : ZMod 9245152471) ^ 56427 = (6 : ZMod 9245152471) ^ (28213 + 28213 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 28213 * (6 : ZMod 9245152471) ^ 28213) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 5289686758 := by rw [factor_2_14]; decide
      have factor_2_16 : (6 : ZMod 9245152471) ^ 112855 = 32870181 := by
        calc
          (6 : ZMod 9245152471) ^ 112855 = (6 : ZMod 9245152471) ^ (56427 + 56427 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 56427 * (6 : ZMod 9245152471) ^ 56427) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 32870181 := by rw [factor_2_15]; decide
      have factor_2_17 : (6 : ZMod 9245152471) ^ 225711 = 1126323837 := by
        calc
          (6 : ZMod 9245152471) ^ 225711 = (6 : ZMod 9245152471) ^ (112855 + 112855 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 112855 * (6 : ZMod 9245152471) ^ 112855) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 1126323837 := by rw [factor_2_16]; decide
      have factor_2_18 : (6 : ZMod 9245152471) ^ 451423 = 176196213 := by
        calc
          (6 : ZMod 9245152471) ^ 451423 = (6 : ZMod 9245152471) ^ (225711 + 225711 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 225711 * (6 : ZMod 9245152471) ^ 225711) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 176196213 := by rw [factor_2_17]; decide
      have factor_2_19 : (6 : ZMod 9245152471) ^ 902846 = 3664905492 := by
        calc
          (6 : ZMod 9245152471) ^ 902846 = (6 : ZMod 9245152471) ^ (451423 + 451423) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 451423 * (6 : ZMod 9245152471) ^ 451423 := by rw [pow_add]
          _ = 3664905492 := by rw [factor_2_18]; decide
      have factor_2_20 : (6 : ZMod 9245152471) ^ 1805693 = 2815426390 := by
        calc
          (6 : ZMod 9245152471) ^ 1805693 = (6 : ZMod 9245152471) ^ (902846 + 902846 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 902846 * (6 : ZMod 9245152471) ^ 902846) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 2815426390 := by rw [factor_2_19]; decide
      have factor_2_21 : (6 : ZMod 9245152471) ^ 3611387 = 5799361252 := by
        calc
          (6 : ZMod 9245152471) ^ 3611387 = (6 : ZMod 9245152471) ^ (1805693 + 1805693 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 1805693 * (6 : ZMod 9245152471) ^ 1805693) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 5799361252 := by rw [factor_2_20]; decide
      have factor_2_22 : (6 : ZMod 9245152471) ^ 7222775 = 1721959529 := by
        calc
          (6 : ZMod 9245152471) ^ 7222775 = (6 : ZMod 9245152471) ^ (3611387 + 3611387 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 3611387 * (6 : ZMod 9245152471) ^ 3611387) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 1721959529 := by rw [factor_2_21]; decide
      have factor_2_23 : (6 : ZMod 9245152471) ^ 14445550 = 8626475149 := by
        calc
          (6 : ZMod 9245152471) ^ 14445550 = (6 : ZMod 9245152471) ^ (7222775 + 7222775) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 7222775 * (6 : ZMod 9245152471) ^ 7222775 := by rw [pow_add]
          _ = 8626475149 := by rw [factor_2_22]; decide
      have factor_2_24 : (6 : ZMod 9245152471) ^ 28891101 = 2242449401 := by
        calc
          (6 : ZMod 9245152471) ^ 28891101 = (6 : ZMod 9245152471) ^ (14445550 + 14445550 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 14445550 * (6 : ZMod 9245152471) ^ 14445550) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 2242449401 := by rw [factor_2_23]; decide
      have factor_2_25 : (6 : ZMod 9245152471) ^ 57782202 = 189853232 := by
        calc
          (6 : ZMod 9245152471) ^ 57782202 = (6 : ZMod 9245152471) ^ (28891101 + 28891101) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 28891101 * (6 : ZMod 9245152471) ^ 28891101 := by rw [pow_add]
          _ = 189853232 := by rw [factor_2_24]; decide
      have factor_2_26 : (6 : ZMod 9245152471) ^ 115564405 = 7115871992 := by
        calc
          (6 : ZMod 9245152471) ^ 115564405 = (6 : ZMod 9245152471) ^ (57782202 + 57782202 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 57782202 * (6 : ZMod 9245152471) ^ 57782202) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 7115871992 := by rw [factor_2_25]; decide
      have factor_2_27 : (6 : ZMod 9245152471) ^ 231128811 = 4427033518 := by
        calc
          (6 : ZMod 9245152471) ^ 231128811 = (6 : ZMod 9245152471) ^ (115564405 + 115564405 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 115564405 * (6 : ZMod 9245152471) ^ 115564405) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 4427033518 := by rw [factor_2_26]; decide
      have factor_2_28 : (6 : ZMod 9245152471) ^ 462257623 = 8719597810 := by
        calc
          (6 : ZMod 9245152471) ^ 462257623 = (6 : ZMod 9245152471) ^ (231128811 + 231128811 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 231128811 * (6 : ZMod 9245152471) ^ 231128811) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 8719597810 := by rw [factor_2_27]; decide
      have factor_2_29 : (6 : ZMod 9245152471) ^ 924515247 = 6358334594 := by
        calc
          (6 : ZMod 9245152471) ^ 924515247 = (6 : ZMod 9245152471) ^ (462257623 + 462257623 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 462257623 * (6 : ZMod 9245152471) ^ 462257623) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 6358334594 := by rw [factor_2_28]; decide
      have factor_2_30 : (6 : ZMod 9245152471) ^ 1849030494 = 4447766909 := by
        calc
          (6 : ZMod 9245152471) ^ 1849030494 = (6 : ZMod 9245152471) ^ (924515247 + 924515247) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 924515247 * (6 : ZMod 9245152471) ^ 924515247 := by rw [pow_add]
          _ = 4447766909 := by rw [factor_2_29]; decide
      change (6 : ZMod 9245152471) ^ 1849030494 ≠ 1
      rw [factor_2_30]
      decide
    ·
      have factor_3_0 : (6 : ZMod 9245152471) ^ 1 = 6 := by norm_num
      have factor_3_1 : (6 : ZMod 9245152471) ^ 3 = 216 := by
        calc
          (6 : ZMod 9245152471) ^ 3 = (6 : ZMod 9245152471) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 1 * (6 : ZMod 9245152471) ^ 1) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_3_0]; decide
      have factor_3_2 : (6 : ZMod 9245152471) ^ 7 = 279936 := by
        calc
          (6 : ZMod 9245152471) ^ 7 = (6 : ZMod 9245152471) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 3 * (6 : ZMod 9245152471) ^ 3) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 279936 := by rw [factor_3_1]; decide
      have factor_3_3 : (6 : ZMod 9245152471) ^ 15 = 7927361026 := by
        calc
          (6 : ZMod 9245152471) ^ 15 = (6 : ZMod 9245152471) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = ((6 : ZMod 9245152471) ^ 7 * (6 : ZMod 9245152471) ^ 7) * (6 : ZMod 9245152471) := by rw [pow_succ, pow_add]
          _ = 7927361026 := by rw [factor_3_2]; decide
      have factor_3_4 : (6 : ZMod 9245152471) ^ 30 = 2432242767 := by
        calc
          (6 : ZMod 9245152471) ^ 30 = (6 : ZMod 9245152471) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (6 : ZMod 9245152471) ^ n) (by norm_num)
          _ = (6 : ZMod 9245152471) ^ 15 * (6 : ZMod 9245152471) ^ 15 := by rw [pow_add]
          _ = 2432242767 := by rw [factor_3_3]; decide
      change (6 : ZMod 9245152471) ^ 30 ≠ 1
      rw [factor_3_4]
      decide

#print axioms prime_lucas_9245152471

end TotientTailPeriodKiller
end Erdos249257
